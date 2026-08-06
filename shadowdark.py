"""
Eksportuje kompendia systemu Shadowdark do plików JSON zgodnych z Babele.

Skrypt obsługuje:
    - pobieranie najnowszego wydania Shadowdark z GitHub,
    - rozpakowane wydanie systemu,
    - katalog źródłowy repozytorium z paczkami data/packs/*.db,
    - paczki Foundry zapisane jako katalogi źródłowych plików JSON,
    - paczki Foundry zapisane jako bazy LevelDB,
    - dokumenty Item, Actor, JournalEntry, RollTable, Adventure i Macro,
    - dokumenty osadzone, między innymi przedmioty aktorów, strony dzienników,
      efekty aktywne i wyniki tabel,
    - dodatkowe tekstowe pola systemowe Shadowdark wykrywane w danych,
    - pobieranie i18n/en.yaml i zapisywanie go jako en.json,
    - pobieranie i eksport modułu Shadowdark Community Content,
    - dodanie form few oraz many do lokalizacji liczby mnogiej.

Wymagania:
    pip install requests PyYAML

Plyvel jest potrzebny tylko przy odczycie skompilowanych paczek LevelDB:
    pip install plyvel

Dla repozytorium źródłowego można użyć --source-dir bez instalowania plyvel.

Przykłady:
    python shadowdark1.py
    python shadowdark1.py --output shadowdark_export
    python shadowdark1.py --source-dir ./foundryvtt-shadowdark
    python shadowdark1.py --source-dir ./shadowdark-system --no-lang
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import shutil
import sys
import zipfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Any, Iterable, Iterator, Sequence

import requests

try:
    import plyvel
except ImportError:
    plyvel = None

try:
    import yaml
except ImportError:
    yaml = None


SYSTEM_ID = "shadowdark"
DEFAULT_MANIFEST_URL = (
    "https://github.com/Muttley/foundryvtt-shadowdark/"
    "releases/latest/download/system.json"
)
DEFAULT_DOWNLOAD_URL = (
    "https://github.com/Muttley/foundryvtt-shadowdark/"
    "releases/latest/download/shadowdark.zip"
)
DEFAULT_WORK_DIR = "pack_shadowdark"
DEFAULT_RAW_OUTPUT_DIR = "output"
DEFAULT_ZIP_NAME = "shadowdark.zip"
DEFAULT_LANGUAGE_URL = (
    "https://raw.githubusercontent.com/Muttley/foundryvtt-shadowdark/"
    "refs/heads/develop/i18n/en.yaml"
)
COMMUNITY_MODULE_ID = "shadowdark-community-content"
DEFAULT_COMMUNITY_MANIFEST_URL = (
    "https://github.com/PrototypeESBU/"
    "foundryvtt-shadowdark-community-content/"
    "releases/latest/download/module.json"
)
COMMUNITY_ZIP_NAME = "shadowdark-community-content.zip"

INTERNAL_LEVELDB_KEY = "__leveldb_key__"

TOP_LEVEL_COLLECTIONS = {
    "Item": "items",
    "Actor": "actors",
    "JournalEntry": "journal",
    "RollTable": "tables",
    "Adventure": "adventures",
    "Macro": "macros",
    "Scene": "scenes",
    "Cards": "cards",
}

# Końcowe nazwy pól, które mogą zawierać tekst przeznaczony do tłumaczenia.
# Lista jest celowo zachowawcza. Formuły, identyfikatory i konfiguracja mechaniki
# nie są eksportowane jako tekst.
TRANSLATABLE_SYSTEM_LEAVES = {
    "caption",
    "description",
    "effect",
    "label",
    "moveNote",
    "name",
    "notes",
    "special",
    "text",
    "title",
}

# Pola tytułów klasowych nie mają typowych nazw końcowych, ale zawierają tekst.
CLASS_TITLE_LEAVES = {"chaotic", "lawful", "neutral"}

EXCLUDED_SYSTEM_PREFIXES = (
    "system.source",
    "system.rollConfig",
    "system.roll-config",
    "system.configuration",
)

TECHNICAL_FILE_SUFFIXES = (
    ".avif",
    ".gif",
    ".jpeg",
    ".jpg",
    ".json",
    ".mp3",
    ".mp4",
    ".ogg",
    ".png",
    ".svg",
    ".webm",
    ".webp",
    ".wav",
)


@dataclass(frozen=True)
class PackMetadata:
    name: str
    label: str
    document_type: str
    relative_path: str


class ExportError(RuntimeError):
    """Błąd uniemożliwiający poprawne wykonanie eksportu."""


class RecordIndex:
    """Indeks rekordów paczki i dokumentów osadzonych."""

    def __init__(self, records: Sequence[dict[str, Any]]) -> None:
        self.records = list(records)
        self.by_id: dict[str, list[dict[str, Any]]] = defaultdict(list)
        self.by_key: dict[str, dict[str, Any]] = {}

        for record in self.records:
            record_id = clean_string(record.get("_id"))
            if record_id:
                self.by_id[record_id].append(record)

            storage_key = record_storage_key(record)
            if storage_key:
                self.by_key[storage_key] = record

    def resolve_id(
        self,
        record_id: str,
        parent: dict[str, Any] | None = None,
        collection: str | None = None,
    ) -> dict[str, Any] | None:
        if not record_id:
            return None

        candidates = self.by_id.get(record_id, [])
        if not candidates:
            return None

        if parent is not None and collection:
            for candidate in candidates:
                if record_belongs_to_parent(candidate, parent, collection):
                    return candidate

        if len(candidates) == 1:
            return candidates[0]

        for candidate in candidates:
            candidate_key = record_storage_key(candidate)
            if candidate_key and "." not in candidate_key:
                return candidate

        return candidates[0]

    def embedded(
        self,
        parent: dict[str, Any],
        collection: str,
    ) -> list[dict[str, Any]]:
        """Zwraca dokumenty osadzone niezależnie od sposobu ich zapisu."""
        output: list[dict[str, Any]] = []
        seen: set[str] = set()
        source_value = parent.get(collection)

        if isinstance(source_value, list):
            for value in source_value:
                resolved = None

                if isinstance(value, dict):
                    resolved = value
                elif isinstance(value, str):
                    resolved = self.resolve_id(value, parent, collection)

                if isinstance(resolved, dict):
                    identity = record_identity(resolved)
                    if identity not in seen:
                        seen.add(identity)
                        output.append(resolved)

        elif isinstance(source_value, dict):
            for value in source_value.values():
                if not isinstance(value, dict):
                    continue

                identity = record_identity(value)
                if identity not in seen:
                    seen.add(identity)
                    output.append(value)

        for record in self.by_key.values():
            if not record_belongs_to_parent(record, parent, collection):
                continue

            identity = record_identity(record)
            if identity not in seen:
                seen.add(identity)
                output.append(record)

        return output


def parse_yaml_mapping(text: str, source_name: str) -> dict[str, Any]:
    if yaml is None:
        raise ExportError(
            "Do konwersji i18n/en.yaml wymagany jest moduł PyYAML. "
            "Uruchom: pip install PyYAML"
        )

    try:
        data = yaml.safe_load(text)
    except yaml.YAMLError as error:
        raise ExportError(
            f"Nie można sparsować pliku YAML {source_name}: {error}"
        ) from error

    if not isinstance(data, dict):
        raise ExportError(
            f"Plik YAML {source_name} nie zawiera obiektu lokalizacji."
        )

    non_string_values = [
        key for key, value in data.items() if not isinstance(value, str)
    ]
    if non_string_values:
        examples = ", ".join(str(key) for key in non_string_values[:5])
        raise ExportError(
            "Plik YAML zawiera wartości lokalizacyjne, które nie są tekstem. "
            f"Przykładowe klucze: {examples}"
        )

    return data

def download_language_file(
    language_url: str,
    output_root: pathlib.Path,
) -> None:
    print(f"Pobieram plik językowy: {language_url}")
    response = requests.get(language_url, timeout=90)
    response.raise_for_status()
    data = parse_yaml_mapping(response.text, language_url)

    add_polish_plural_placeholders(data)
    destination = output_root / "en.json"
    destination.write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Zapisano plik językowy: {destination}")

def clean_string(value: Any) -> str:
    return value.strip() if isinstance(value, str) else ""


def get_path(data: Any, path: str) -> Any:
    current = data

    for part in path.split("."):
        if isinstance(current, dict):
            if part not in current:
                return None
            current = current[part]
        elif isinstance(current, list) and part.isdigit():
            index = int(part)
            if index >= len(current):
                return None
            current = current[index]
        else:
            return None

    return current


def has_path(data: Any, path: str) -> bool:
    sentinel = object()
    current = data

    for part in path.split("."):
        if isinstance(current, dict):
            current = current.get(part, sentinel)
        elif isinstance(current, list) and part.isdigit():
            index = int(part)
            current = current[index] if index < len(current) else sentinel
        else:
            return False

        if current is sentinel:
            return False

    return True


def records_have_path(
    records: Iterable[dict[str, Any]],
    path: str,
    expected_type: type | tuple[type, ...] | None = None,
) -> bool:
    for record in records:
        if not has_path(record, path):
            continue

        value = get_path(record, path)
        if expected_type is None or isinstance(value, expected_type):
            return True

    return False


def record_storage_key(record: dict[str, Any]) -> str:
    for key_name in (INTERNAL_LEVELDB_KEY, "_key"):
        value = record.get(key_name)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def record_identity(record: dict[str, Any]) -> str:
    storage_key = record_storage_key(record)
    if storage_key:
        return storage_key

    record_id = clean_string(record.get("_id"))
    if record_id:
        return record_id

    return f"object:{id(record)}"


def storage_collection_from_key(storage_key: str) -> str:
    match = re.match(r"^!([^. !]+)!", storage_key)
    return match.group(1) if match else ""


def record_belongs_to_parent(
    candidate: dict[str, Any],
    parent: dict[str, Any],
    collection: str,
) -> bool:
    """Rozpoznaje oba formaty kluczy dokumentów osadzonych Foundry."""
    candidate_key = record_storage_key(candidate)
    parent_key = record_storage_key(parent)
    parent_id = clean_string(parent.get("_id"))

    if not candidate_key or not parent_id:
        return False

    if parent_key and candidate_key.startswith(f"{parent_key}.{collection}!"):
        return True

    parent_collection = storage_collection_from_key(parent_key)
    if not parent_collection:
        return False

    source_prefixes = (
        f"!{parent_collection}.{collection}!{parent_id}.",
        f"!{parent_collection}.{collection}!{parent_id}!",
        f"!{parent_collection}!{parent_id}.{collection}!",
    )
    return candidate_key.startswith(source_prefixes)


def safe_extract_zip(zip_path: pathlib.Path, destination: pathlib.Path) -> None:
    destination = destination.resolve()

    with zipfile.ZipFile(zip_path, "r") as archive:
        for member in archive.infolist():
            target = (destination / member.filename).resolve()
            if destination != target and destination not in target.parents:
                raise ExportError(
                    f"Niebezpieczna ścieżka w archiwum: {member.filename}"
                )
        archive.extractall(destination)


def request_json(url: str, timeout: int = 90) -> dict[str, Any]:
    response = requests.get(url, timeout=timeout)
    response.raise_for_status()
    data = response.json()

    if not isinstance(data, dict):
        raise ExportError(f"Manifest pod adresem {url} nie jest obiektem JSON.")

    return data


def download_file(url: str, destination: pathlib.Path, timeout: int = 240) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)

    with requests.get(url, timeout=timeout, stream=True) as response:
        response.raise_for_status()
        with destination.open("wb") as output:
            for chunk in response.iter_content(chunk_size=1024 * 1024):
                if chunk:
                    output.write(chunk)


def recreate_directory(path: pathlib.Path) -> None:
    if path.exists():
        if not path.is_dir():
            raise ExportError(f"Ścieżka nie jest katalogiem: {path}")
        shutil.rmtree(path)

    path.mkdir(parents=True, exist_ok=True)


def find_system_root(extract_root: pathlib.Path) -> pathlib.Path:
    direct_manifest = extract_root / "system.json"
    if direct_manifest.is_file():
        return extract_root

    for candidate in extract_root.rglob("system.json"):
        try:
            data = json.loads(candidate.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue

        if isinstance(data, dict) and data.get("id") == SYSTEM_ID:
            return candidate.parent

    raise ExportError(
        "Nie znaleziono katalogu głównego systemu Shadowdark po rozpakowaniu."
    )


def find_module_root(
    extract_root: pathlib.Path,
    module_id: str,
) -> pathlib.Path:
    """Znajduje katalog główny rozpakowanego modułu Foundry."""
    direct_manifest = extract_root / "module.json"
    if direct_manifest.is_file():
        try:
            data = json.loads(direct_manifest.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            data = {}

        if not isinstance(data, dict) or data.get("id") in (None, module_id):
            return extract_root

    for candidate in extract_root.rglob("module.json"):
        try:
            data = json.loads(candidate.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue

        if isinstance(data, dict) and data.get("id") == module_id:
            return candidate.parent

    pack_roots = [
        candidate.parent
        for candidate in extract_root.rglob("packs")
        if candidate.is_dir()
    ]
    if pack_roots:
        return pack_roots[0]

    raise ExportError(
        f"Nie znaleziono katalogu głównego modułu {module_id} "
        "po rozpakowaniu."
    )


def normalize_source_root(source_dir: pathlib.Path) -> pathlib.Path:
    source_dir = source_dir.resolve()

    if not source_dir.exists() or not source_dir.is_dir():
        raise ExportError(f"Katalog źródłowy nie istnieje: {source_dir}")

    if (source_dir / "system.json").is_file():
        return source_dir

    nested_manifests = list(source_dir.glob("*/system.json"))
    for manifest_path in nested_manifests:
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue

        if isinstance(data, dict) and data.get("id") == SYSTEM_ID:
            return manifest_path.parent

    # Repozytorium źródłowe nie musi zawierać skompilowanego system.json.
    if (source_dir / "data" / "packs").is_dir():
        return source_dir

    return source_dir


def normalize_pack_metadata(manifest: dict[str, Any]) -> list[PackMetadata]:
    packs = manifest.get("packs")
    if not isinstance(packs, list):
        raise ExportError("Manifest nie zawiera listy packs.")

    output: list[PackMetadata] = []

    for pack in packs:
        if not isinstance(pack, dict):
            continue

        name = clean_string(pack.get("name"))
        relative_path = clean_string(pack.get("path"))
        document_type = clean_string(
            pack.get("type") or pack.get("documentName")
        )
        label = clean_string(pack.get("label")) or name

        if not name or not relative_path or not document_type:
            continue

        output.append(
            PackMetadata(
                name=name,
                label=label,
                document_type=document_type,
                relative_path=relative_path,
            )
        )

    return output


def resolve_pack_path(
    system_root: pathlib.Path,
    pack: PackMetadata,
) -> pathlib.Path:
    relative = pathlib.Path(pack.relative_path)
    candidates = [
        system_root / relative,
        system_root / "system" / relative,
        system_root / "data" / relative,
        system_root / "data" / "packs" / f"{pack.name}.db",
        system_root / "data" / "packs" / pack.name,
        system_root / "packs" / pack.name,
    ]

    if relative.parts and relative.parts[0] == "packs":
        pack_basename = relative.name
        candidates.extend(
            [
                system_root / "data" / "packs" / f"{pack_basename}.db",
                system_root / "data" / "packs" / pack_basename,
            ]
        )

    seen: set[pathlib.Path] = set()
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)

        if resolved.exists():
            return resolved

    candidate_text = "\n".join(f"  - {candidate}" for candidate in candidates)
    raise ExportError(
        f"Nie znaleziono paczki {pack.name}. Sprawdzono:\n{candidate_text}"
    )


def read_source_json_documents(source_dir: pathlib.Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    json_paths = sorted(source_dir.glob("*.json"), key=lambda path: path.name.casefold())

    for json_path in json_paths:
        try:
            data = json.loads(json_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            print(
                f"Ostrzeżenie: pomijam {json_path}: {error}",
                file=sys.stderr,
            )
            continue

        if isinstance(data, dict):
            records.append(data)
        elif isinstance(data, list):
            records.extend(value for value in data if isinstance(value, dict))

    return records


def write_raw_pack_json(
    records: Sequence[dict[str, Any]],
    destination: pathlib.Path,
) -> None:
    """Zapisuje wszystkie rekordy paczki w jednym prostym pliku JSON."""
    destination.parent.mkdir(parents=True, exist_ok=True)

    raw_records = [
        {
            key: value
            for key, value in record.items()
            if key != INTERNAL_LEVELDB_KEY
        }
        for record in records
    ]

    destination.write_text(
        json.dumps(raw_records, ensure_ascii=False, indent=4) + "\n",
        encoding="utf-8",
    )
    print(
        f"  zapisano surową paczkę: {destination} "
        f"({len(raw_records)} rekordów)"
    )


def read_leveldb_documents(
    database_path: pathlib.Path,
    raw_output_file: pathlib.Path | None = None,
) -> list[dict[str, Any]]:
    if plyvel is None:
        raise ExportError(
            "Paczka wymaga odczytu LevelDB, ale moduł plyvel nie jest "
            "zainstalowany. Uruchom: pip install plyvel"
        )

    records: list[dict[str, Any]] = []
    database = None

    try:
        database = plyvel.DB(str(database_path), create_if_missing=False)

        for key, value in database:
            try:
                decoded_key = key.decode("utf-8", errors="replace")
                decoded_value = value.decode("utf-8")
                data = json.loads(decoded_value)
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                print(
                    f"Ostrzeżenie: nie można odczytać rekordu {key!r}: {error}",
                    file=sys.stderr,
                )
                continue

            if isinstance(data, dict):
                data.setdefault(INTERNAL_LEVELDB_KEY, decoded_key)
                records.append(data)

    finally:
        if database is not None:
            database.close()

    if raw_output_file is not None:
        write_raw_pack_json(records, raw_output_file)

    return records


def read_pack_documents(
    pack_path: pathlib.Path,
    raw_output_file: pathlib.Path | None = None,
) -> list[dict[str, Any]]:
    source_dir = pack_path / "_source"
    if source_dir.is_dir():
        records = read_source_json_documents(source_dir)
        if records:
            if raw_output_file is not None:
                write_raw_pack_json(records, raw_output_file)
            return records

    if pack_path.is_dir():
        direct_json_files = list(pack_path.glob("*.json"))
        if direct_json_files:
            records = read_source_json_documents(pack_path)
            if records:
                if raw_output_file is not None:
                    write_raw_pack_json(records, raw_output_file)
                return records

    if not pack_path.exists():
        raise ExportError(f"Nie znaleziono paczki: {pack_path}")

    return read_leveldb_documents(
        pack_path,
        raw_output_file=raw_output_file,
    )

def is_folder_record(record: dict[str, Any]) -> bool:
    storage_key = record_storage_key(record)
    if "!folders!" in storage_key:
        return True

    if record.get("type") in {"Folder", "folder"}:
        return True

    if (
        clean_string(record.get("_id"))
        and clean_string(record.get("name"))
        and "folder" in record
        and "sorting" in record
        and not any(
            key in record
            for key in (
                "system",
                "prototypeToken",
                "pages",
                "results",
                "journal",
                "actors",
                "items",
                "scenes",
            )
        )
    ):
        return True

    return False


def top_level_from_storage_key(
    record: dict[str, Any],
    document_type: str,
) -> bool | None:
    storage_key = record_storage_key(record)
    collection = TOP_LEVEL_COLLECTIONS.get(document_type)

    if not storage_key or not collection:
        return None

    if re.fullmatch(rf"!{re.escape(collection)}![^.]+", storage_key):
        return True

    if storage_key.startswith(f"!{collection}!"):
        return False

    return None


def is_top_level_document(
    record: dict[str, Any],
    document_type: str,
) -> bool:
    if is_folder_record(record):
        return False

    storage_result = top_level_from_storage_key(record, document_type)
    if storage_result is not None:
        return storage_result

    name = clean_string(record.get("name"))
    if not name:
        return False

    if document_type == "Item":
        return isinstance(record.get("system"), dict)

    if document_type == "Actor":
        return isinstance(record.get("system"), dict) and (
            isinstance(record.get("prototypeToken"), dict)
            or "items" in record
        )

    if document_type == "JournalEntry":
        return "pages" in record

    if document_type == "RollTable":
        return "results" in record

    if document_type == "Adventure":
        return any(
            key in record
            for key in (
                "actors",
                "caption",
                "items",
                "journal",
                "scenes",
                "tables",
            )
        )

    if document_type == "Macro":
        return "command" in record or record.get("type") in {"chat", "script"}

    return True


def collect_folders(records: Sequence[dict[str, Any]]) -> dict[str, str]:
    names = {
        clean_string(record.get("name"))
        for record in records
        if is_folder_record(record) and clean_string(record.get("name"))
    }

    return {name: name for name in sorted(names, key=str.casefold)}


def iter_string_leaf_paths(
    value: Any,
    parts: list[str] | None = None,
) -> Iterator[tuple[str, str]]:
    current_parts = parts or []

    if isinstance(value, dict):
        for key, child in value.items():
            if key == INTERNAL_LEVELDB_KEY:
                continue
            yield from iter_string_leaf_paths(child, [*current_parts, str(key)])

    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from iter_string_leaf_paths(child, [*current_parts, str(index)])

    elif isinstance(value, str) and current_parts:
        yield ".".join(current_parts), value


def looks_like_technical_string(value: str) -> bool:
    text = value.strip()
    lower = text.casefold()

    if not text:
        return True

    if lower.endswith(TECHNICAL_FILE_SUFFIXES):
        return True

    if text.startswith(("@UUID[", "Compendium.", "Actor.", "Item.", "Scene.")):
        return True

    if re.fullmatch(r"[A-Za-z0-9_-]{16,}", text):
        return True

    if re.fullmatch(r"[a-z0-9_]+(?:-[a-z0-9_]+)+", text):
        return True

    if re.fullmatch(r"[\d\s+\-*/().@\[\]{}<>=,:]+", text):
        return True

    if re.fullmatch(r"[A-Z][A-Z0-9_]*(?:\.[A-Z0-9_]+)+", text):
        return True

    return False


def is_translatable_system_path(path: str, value: str) -> bool:
    if not path.startswith("system."):
        return False

    if any(path.startswith(prefix) for prefix in EXCLUDED_SYSTEM_PREFIXES):
        return False

    parts = path.split(".")
    leaf = parts[-1]

    # Tytuły klasowe są obsługiwane osobnym mapowaniem structured.
    # Nie należy eksportować ich jako niestabilnych ścieżek indeksowych.
    if path.startswith("system.titles."):
        return False

    if leaf not in TRANSLATABLE_SYSTEM_LEAVES:
        return False

    if looks_like_technical_string(value):
        return False

    return True

def class_titles_mapping() -> dict[str, Any]:
    return {
        "path": "system.titles",
        "converter": "structured",
        "cardinality": "many",
        "key": "from",
        "mapping": {
            title_type: title_type
            for title_type in sorted(CLASS_TITLE_LEAVES)
        },
    }


def custom_scalar_paths(
    records: Iterable[dict[str, Any]],
    reserved_paths: Iterable[str] = (),
) -> list[str]:
    reserved = set(reserved_paths)
    paths: set[str] = set()

    for record in records:
        system = record.get("system")
        if not isinstance(system, dict):
            continue

        for path, value in iter_string_leaf_paths(system, ["system"]):
            if path in reserved:
                continue

            if is_translatable_system_path(path, value):
                paths.add(path)

    return sorted(paths, key=str.casefold)


def custom_scalar_mapping(
    records: Iterable[dict[str, Any]],
    reserved_paths: Iterable[str] = (),
) -> dict[str, str]:
    return {
        path: path
        for path in custom_scalar_paths(records, reserved_paths=reserved_paths)
    }


def custom_scalar_values(
    record: dict[str, Any],
    paths: Iterable[str],
) -> dict[str, str]:
    output: dict[str, str] = {}

    for path in paths:
        value = get_path(record, path)
        if isinstance(value, str) and value.strip():
            output[path] = value

    return output


def detect_description_path(
    records: Iterable[dict[str, Any]],
    document_type: str,
) -> str | None:
    if document_type in {"Item", "Actor"}:
        candidates = (
            "system.description",
            "system.notes",
            "system.description.value",
            "system.details.biography.value",
            "system.details.biography",
            "description",
        )
    elif document_type == "JournalEntry":
        candidates = ("content", "description")
    else:
        candidates = (
            "description",
            "system.description",
            "system.description.value",
        )

    counts: Counter[str] = Counter()

    for record in records:
        for candidate in candidates:
            value = get_path(record, candidate)
            if isinstance(value, str) and value.strip():
                counts[candidate] += 1
                break

    if not counts:
        return None

    order = {candidate: index for index, candidate in enumerate(candidates)}
    return max(
        counts,
        key=lambda candidate: (counts[candidate], -order[candidate]),
    )


def merge_mapping(*mappings: dict[str, Any]) -> dict[str, Any]:
    output: dict[str, Any] = {}

    for mapping in mappings:
        output.update(mapping)

    return dict(sorted(output.items(), key=lambda item: item[0].casefold()))


def active_effect_mapping() -> dict[str, Any]:
    return {
        "name": "name",
        "description": "description",
    }


def item_mapping_for(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    mapping: dict[str, Any] = {"name": "name"}
    reserved_paths: set[str] = set()

    description_path = detect_description_path(records, "Item")
    if description_path:
        mapping["description"] = description_path
        reserved_paths.add(description_path)

    if any(record.get("effects") for record in records):
        mapping["effects"] = {
            "path": "effects",
            "converter": "document",
            "documentType": "ActiveEffect",
            "cardinality": "many",
            "mapping": active_effect_mapping(),
        }

    if records_have_path(records, "system.titles", list):
        mapping["titles"] = class_titles_mapping()

    return merge_mapping(
        mapping,
        custom_scalar_mapping(records, reserved_paths=reserved_paths),
    )

def extract_class_titles(item: dict[str, Any]) -> dict[str, Any]:
    titles = get_path(item, "system.titles")
    if not isinstance(titles, list):
        return {}

    output: dict[str, Any] = {}

    for index, title in enumerate(titles):
        if not isinstance(title, dict):
            continue

        entry = {
            title_type: value
            for title_type in sorted(CLASS_TITLE_LEAVES)
            if isinstance((value := title.get(title_type)), str)
            and value.strip()
        }
        if not entry:
            continue

        from_value = title.get("from")
        key = str(from_value) if from_value not in (None, "") else str(index)

        if key in output:
            key = f"{key}#{index}"

        output[key] = entry

    return output

def actor_mapping_for(
    actor_records: Sequence[dict[str, Any]],
    embedded_item_records: Sequence[dict[str, Any]],
) -> tuple[dict[str, Any], dict[str, Any]]:
    item_mapping = item_mapping_for(embedded_item_records)
    mapping: dict[str, Any] = {
        "name": "name",
        "tokenName": {
            "path": "prototypeToken.name",
            "converter": "name",
        },
        "items": {
            "path": "items",
            "converter": "document",
            "documentType": "Item",
            "cardinality": "many",
            "mapping": item_mapping,
        },
    }
    reserved_paths: set[str] = set()

    if any(record.get("effects") for record in actor_records):
        mapping["effects"] = {
            "path": "effects",
            "converter": "document",
            "documentType": "ActiveEffect",
            "cardinality": "many",
            "mapping": active_effect_mapping(),
        }

    description_path = detect_description_path(actor_records, "Actor")
    if description_path:
        mapping["description"] = description_path
        reserved_paths.add(description_path)

    return (
        merge_mapping(
            mapping,
            custom_scalar_mapping(actor_records, reserved_paths=reserved_paths),
        ),
        item_mapping,
    )


def journal_page_mapping(
    page_records: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    mapping: dict[str, Any] = {"name": "name"}

    if records_have_path(page_records, "text.content", str):
        mapping["text"] = "text.content"

    if records_have_path(page_records, "image.caption", str):
        mapping["caption"] = "image.caption"

    if records_have_path(page_records, "video.caption", str):
        mapping["videoCaption"] = "video.caption"

    description_path = detect_description_path(page_records, "JournalEntryPage")
    reserved_paths: set[str] = set()
    if description_path:
        mapping["description"] = description_path
        reserved_paths.add(description_path)

    return merge_mapping(
        mapping,
        custom_scalar_mapping(page_records, reserved_paths=reserved_paths),
    )


def journal_mapping_for(
    journal_records: Sequence[dict[str, Any]],
    page_records: Sequence[dict[str, Any]],
) -> tuple[dict[str, Any], dict[str, Any]]:
    page_mapping = journal_page_mapping(page_records)
    mapping: dict[str, Any] = {
        "name": "name",
        "pages": {
            "path": "pages",
            "converter": "document",
            "documentType": "JournalEntryPage",
            "cardinality": "many",
            "mapping": page_mapping,
        },
    }

    if any(record.get("categories") for record in journal_records):
        mapping["categories"] = {
            "path": "categories",
            "converter": "nameCollection",
        }

    description_path = detect_description_path(journal_records, "JournalEntry")
    reserved_paths: set[str] = set()
    if description_path:
        mapping["description"] = description_path
        reserved_paths.add(description_path)

    return (
        merge_mapping(
            mapping,
            custom_scalar_mapping(journal_records, reserved_paths=reserved_paths),
        ),
        page_mapping,
    )


def rolltable_mapping_for(
    table_records: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    mapping: dict[str, Any] = {
        "name": "name",
        "results": {
            "path": "results",
            "converter": "document",
            "documentType": "TableResult",
            "cardinality": "many",
            "mapping": table_result_mapping(),
        },
    }
    reserved_paths: set[str] = set()

    description_path = detect_description_path(table_records, "RollTable")
    if description_path:
        mapping["description"] = description_path
        reserved_paths.add(description_path)

    return merge_mapping(
        mapping,
        custom_scalar_mapping(table_records, reserved_paths=reserved_paths),
    )


def macro_mapping_for() -> dict[str, Any]:
    return {
        "name": "name",
        "command": "command",
    }


def primitive_mapping_items(
    mapping: dict[str, Any],
) -> Iterator[tuple[str, str]]:
    for field, definition in mapping.items():
        if isinstance(definition, str):
            yield field, definition


def extract_primitive_fields(
    record: dict[str, Any],
    mapping: dict[str, Any],
) -> dict[str, Any]:
    entry: dict[str, Any] = {}

    for field, path in primitive_mapping_items(mapping):
        if not has_path(record, path):
            continue

        value = get_path(record, path)
        if isinstance(value, str):
            if value.strip():
                entry[field] = value
        elif value not in (None, {}, []):
            entry[field] = value

    return entry


def export_key_for(
    record: dict[str, Any],
    duplicate_names: Counter[str],
) -> str:
    name = clean_string(record.get("name"))
    record_id = clean_string(record.get("_id"))

    if name and duplicate_names[name] == 1:
        return name
    if record_id:
        return record_id
    if name:
        return name

    return record_identity(record)


def nested_export_key(record: dict[str, Any], used: set[str]) -> str:
    name = clean_string(record.get("name"))
    record_id = clean_string(record.get("_id"))
    candidate = name or record_id or record_identity(record)

    if candidate in used and record_id:
        candidate = record_id

    base = candidate
    suffix = 2
    while candidate in used:
        candidate = f"{base} #{suffix}"
        suffix += 1

    used.add(candidate)
    return candidate


def extract_effect_entry(effect: dict[str, Any]) -> dict[str, Any]:
    entry: dict[str, Any] = {}
    name = clean_string(effect.get("name")) or clean_string(effect.get("label"))

    if name:
        entry["name"] = name

    description = effect.get("description")
    if isinstance(description, str) and description.strip():
        entry["description"] = description

    return entry


def extract_effects(
    parent: dict[str, Any],
    index: RecordIndex,
) -> dict[str, Any]:
    output: dict[str, Any] = {}
    used: set[str] = set()

    for effect in index.embedded(parent, "effects"):
        entry = extract_effect_entry(effect)
        if entry:
            output[nested_export_key(effect, used)] = entry

    return output


def custom_paths_from_mapping(mapping: dict[str, Any]) -> list[str]:
    return [
        field
        for field, path in primitive_mapping_items(mapping)
        if field == path and field.startswith("system.")
    ]


def extract_item_entry(
    item: dict[str, Any],
    item_mapping: dict[str, Any],
    index: RecordIndex,
) -> dict[str, Any]:
    entry = extract_primitive_fields(item, item_mapping)
    entry.update(
        custom_scalar_values(item, custom_paths_from_mapping(item_mapping))
    )

    effects = extract_effects(item, index)
    if effects:
        entry["effects"] = effects

    titles = extract_class_titles(item)
    if titles:
        entry["titles"] = titles

    return entry

def table_result_mapping() -> dict[str, Any]:
    return {
        "_identity": {
            "export": ["range", "_id"],
            "match": ["_id", "range"],
        },
        "name": {
            "path": "name",
            "converter": "referencedDocumentField",
            "uuidPath": "documentUuid",
            "referencedField": "name",
        },
        "description": "description",
    }

def extract_actor_entry(
    actor: dict[str, Any],
    actor_mapping: dict[str, Any],
    item_mapping: dict[str, Any],
    index: RecordIndex,
) -> dict[str, Any]:
    entry = extract_primitive_fields(actor, actor_mapping)
    entry.update(
        custom_scalar_values(actor, custom_paths_from_mapping(actor_mapping))
    )

    token_name = get_path(actor, "prototypeToken.name")
    if isinstance(token_name, str) and token_name.strip():
        entry["tokenName"] = token_name

    item_entries: dict[str, Any] = {}
    used: set[str] = set()

    for item in index.embedded(actor, "items"):
        item_entry = extract_item_entry(item, item_mapping, index)
        if item_entry:
            item_entries[nested_export_key(item, used)] = item_entry

    if item_entries:
        entry["items"] = item_entries

    effects = extract_effects(actor, index)
    if effects:
        entry["effects"] = effects

    return entry


def extract_page_entry(
    page: dict[str, Any],
    page_mapping: dict[str, Any],
) -> dict[str, Any]:
    entry = extract_primitive_fields(page, page_mapping)
    entry.update(
        custom_scalar_values(page, custom_paths_from_mapping(page_mapping))
    )
    return entry


def extract_name_collection(
    values: Any,
    parent: dict[str, Any],
    collection: str,
    index: RecordIndex,
) -> dict[str, str]:
    records: list[dict[str, Any]] = []

    if isinstance(values, list):
        for value in values:
            if isinstance(value, dict):
                records.append(value)
            elif isinstance(value, str):
                resolved = index.resolve_id(value, parent, collection)
                if resolved:
                    records.append(resolved)

    output: dict[str, str] = {}

    for record in records:
        name = clean_string(record.get("name"))
        if name:
            output[name] = name

    return output


def extract_journal_entry(
    journal: dict[str, Any],
    journal_mapping: dict[str, Any],
    page_mapping: dict[str, Any],
    index: RecordIndex,
) -> dict[str, Any]:
    entry = extract_primitive_fields(journal, journal_mapping)
    entry.update(
        custom_scalar_values(journal, custom_paths_from_mapping(journal_mapping))
    )

    page_entries: dict[str, Any] = {}
    used: set[str] = set()

    for page in index.embedded(journal, "pages"):
        page_entry = extract_page_entry(page, page_mapping)
        if page_entry:
            page_entries[nested_export_key(page, used)] = page_entry

    if page_entries:
        entry["pages"] = page_entries

    categories = extract_name_collection(
        journal.get("categories"),
        journal,
        "categories",
        index,
    )
    if categories:
        entry["categories"] = categories

    return entry


def table_result_key(result: dict[str, Any]) -> str:
    range_value = result.get("range")

    if isinstance(range_value, list) and len(range_value) >= 2:
        return f"{range_value[0]}-{range_value[1]}"

    return (
        clean_string(result.get("_id"))
        or clean_string(result.get("name"))
        or record_identity(result)
    )


def extract_table_results(
    table: dict[str, Any],
    index: RecordIndex,
) -> dict[str, dict[str, str]]:
    output: dict[str, dict[str, str]] = {}

    for result in index.embedded(table, "results"):
        entry: dict[str, str] = {}

        name = clean_string(result.get("name"))
        if name:
            entry["name"] = name

        description = (
            clean_string(result.get("description"))
            or clean_string(result.get("text"))
        )
        if description:
            entry["description"] = description

        if not entry:
            continue

        key = table_result_key(result)
        if key in output:
            key = clean_string(result.get("_id")) or key

        base_key = key
        suffix = 2
        while key in output:
            key = f"{base_key} #{suffix}"
            suffix += 1

        output[key] = entry

    return dict(
        sorted(output.items(), key=lambda item: natural_range_key(item[0]))
    )


def extract_rolltable_entry(
    table: dict[str, Any],
    table_mapping: dict[str, Any],
    index: RecordIndex,
) -> dict[str, Any]:
    entry = extract_primitive_fields(table, table_mapping)
    entry.update(
        custom_scalar_values(table, custom_paths_from_mapping(table_mapping))
    )

    results = extract_table_results(table, index)
    if results:
        entry["results"] = results

    return entry


def natural_range_key(value: str) -> tuple[Any, ...]:
    parts = re.split(r"(-?\d+)", value)
    return tuple(
        int(part) if re.fullmatch(r"-?\d+", part) else part.casefold()
        for part in parts
    )


def values_as_documents(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, list):
        return [item for item in value if isinstance(item, dict)]

    if isinstance(value, dict):
        return [item for item in value.values() if isinstance(item, dict)]

    return []


def scene_mapping() -> dict[str, Any]:
    return {
        "name": "name",
        "navName": "navName",
    }


def playlist_mapping() -> dict[str, Any]:
    return {
        "name": "name",
        "description": "description",
        "sounds": {
            "path": "sounds",
            "converter": "document",
            "documentType": "PlaylistSound",
            "cardinality": "many",
            "mapping": {
                "name": "name",
                "description": "description",
            },
        },
    }


def cards_mapping() -> dict[str, Any]:
    return {
        "name": "name",
        "description": "description",
        "cards": {
            "path": "cards",
            "converter": "document",
            "documentType": "Card",
            "cardinality": "many",
            "mapping": {
                "name": "name",
                "description": "description",
            },
        },
    }


def adventure_mapping_for(
    item_mapping: dict[str, Any],
    actor_mapping: dict[str, Any],
    journal_mapping: dict[str, Any],
    table_mapping: dict[str, Any],
) -> dict[str, Any]:
    return {
        "name": "name",
        "description": "description",
        "caption": "caption",
        "folders": {
            "path": "folders",
            "converter": "nameCollection",
        },
        "journals": {
            "path": "journal",
            "converter": "document",
            "documentType": "JournalEntry",
            "cardinality": "many",
            "mapping": journal_mapping,
        },
        "scenes": {
            "path": "scenes",
            "converter": "document",
            "documentType": "Scene",
            "cardinality": "many",
            "mapping": scene_mapping(),
        },
        "macros": {
            "path": "macros",
            "converter": "document",
            "documentType": "Macro",
            "cardinality": "many",
            "mapping": macro_mapping_for(),
        },
        "playlists": {
            "path": "playlists",
            "converter": "document",
            "documentType": "Playlist",
            "cardinality": "many",
            "mapping": playlist_mapping(),
        },
        "tables": {
            "path": "tables",
            "converter": "document",
            "documentType": "RollTable",
            "cardinality": "many",
            "mapping": table_mapping,
        },
        "items": {
            "path": "items",
            "converter": "document",
            "documentType": "Item",
            "cardinality": "many",
            "mapping": item_mapping,
        },
        "actors": {
            "path": "actors",
            "converter": "document",
            "documentType": "Actor",
            "cardinality": "many",
            "mapping": actor_mapping,
        },
        "cards": {
            "path": "cards",
            "converter": "document",
            "documentType": "Cards",
            "cardinality": "many",
            "mapping": cards_mapping(),
        },
    }


def extract_simple_document_collection(
    documents: Sequence[dict[str, Any]],
    mapping: dict[str, Any],
) -> dict[str, Any]:
    output: dict[str, Any] = {}
    used: set[str] = set()

    for document in documents:
        entry = extract_primitive_fields(document, mapping)
        if entry:
            output[nested_export_key(document, used)] = entry

    return output


def collect_adventure_documents(
    adventures: Sequence[dict[str, Any]],
) -> dict[str, list[dict[str, Any]]]:
    collections: dict[str, list[dict[str, Any]]] = defaultdict(list)

    for adventure in adventures:
        for collection in (
            "actors",
            "items",
            "journal",
            "scenes",
            "tables",
            "macros",
            "playlists",
            "cards",
            "folders",
        ):
            collections[collection].extend(
                values_as_documents(adventure.get(collection))
            )

    actor_items: list[dict[str, Any]] = []
    for actor in collections["actors"]:
        actor_items.extend(values_as_documents(actor.get("items")))
    collections["actor_items"] = actor_items

    pages: list[dict[str, Any]] = []
    for journal in collections["journal"]:
        pages.extend(values_as_documents(journal.get("pages")))
    collections["pages"] = pages

    return collections


def extract_adventure_entry(
    adventure: dict[str, Any],
    adventure_mapping: dict[str, Any],
    item_mapping: dict[str, Any],
    actor_mapping: dict[str, Any],
    journal_mapping: dict[str, Any],
    page_mapping: dict[str, Any],
    table_mapping: dict[str, Any],
) -> dict[str, Any]:
    local_records: list[dict[str, Any]] = []

    for collection in (
        "actors",
        "items",
        "journal",
        "scenes",
        "tables",
        "macros",
        "playlists",
        "cards",
        "folders",
    ):
        local_records.extend(values_as_documents(adventure.get(collection)))

    for actor in values_as_documents(adventure.get("actors")):
        local_records.extend(values_as_documents(actor.get("items")))
        local_records.extend(values_as_documents(actor.get("effects")))

    for item in values_as_documents(adventure.get("items")):
        local_records.extend(values_as_documents(item.get("effects")))

    for journal in values_as_documents(adventure.get("journal")):
        local_records.extend(values_as_documents(journal.get("pages")))

    for table in values_as_documents(adventure.get("tables")):
        local_records.extend(values_as_documents(table.get("results")))

    local_index = RecordIndex(local_records)
    entry = extract_primitive_fields(adventure, adventure_mapping)

    folder_names = {
        name: name
        for name in (
            clean_string(folder.get("name"))
            for folder in values_as_documents(adventure.get("folders"))
        )
        if name
    }
    if folder_names:
        entry["folders"] = folder_names

    item_entries: dict[str, Any] = {}
    used: set[str] = set()
    for item in values_as_documents(adventure.get("items")):
        item_entry = extract_item_entry(item, item_mapping, local_index)
        if item_entry:
            item_entries[nested_export_key(item, used)] = item_entry
    if item_entries:
        entry["items"] = item_entries

    actor_entries: dict[str, Any] = {}
    used = set()
    for actor in values_as_documents(adventure.get("actors")):
        actor_entry = extract_actor_entry(
            actor,
            actor_mapping,
            item_mapping,
            local_index,
        )
        if actor_entry:
            actor_entries[nested_export_key(actor, used)] = actor_entry
    if actor_entries:
        entry["actors"] = actor_entries

    journal_entries: dict[str, Any] = {}
    used = set()
    for journal in values_as_documents(adventure.get("journal")):
        journal_entry = extract_journal_entry(
            journal,
            journal_mapping,
            page_mapping,
            local_index,
        )
        if journal_entry:
            journal_entries[nested_export_key(journal, used)] = journal_entry
    if journal_entries:
        entry["journals"] = journal_entries

    table_entries: dict[str, Any] = {}
    used = set()
    for table in values_as_documents(adventure.get("tables")):
        table_entry = extract_rolltable_entry(
            table,
            table_mapping,
            local_index,
        )
        if table_entry:
            table_entries[nested_export_key(table, used)] = table_entry
    if table_entries:
        entry["tables"] = table_entries

    for source_key, target_key, mapping in (
        ("scenes", "scenes", scene_mapping()),
        ("macros", "macros", macro_mapping_for()),
        ("playlists", "playlists", playlist_mapping()),
        ("cards", "cards", cards_mapping()),
    ):
        collection = extract_simple_document_collection(
            values_as_documents(adventure.get(source_key)),
            mapping,
        )
        if collection:
            entry[target_key] = collection

    return entry

def ensure_directory(path: pathlib.Path) -> None:
    """Tworzy katalog bez usuwania jego istniejącej zawartości."""
    if path.exists() and not path.is_dir():
        raise ExportError(f"Ścieżka nie jest katalogiem: {path}")

    path.mkdir(parents=True, exist_ok=True)

def remove_empty(value: Any) -> Any:
    if isinstance(value, dict):
        cleaned = {
            key: remove_empty(child)
            for key, child in value.items()
            if key != INTERNAL_LEVELDB_KEY
        }
        return {
            key: child
            for key, child in cleaned.items()
            if child not in (None, "", {}, [])
        }

    if isinstance(value, list):
        return [
            child
            for child in (remove_empty(item) for item in value)
            if child not in (None, "", {}, [])
        ]

    return value


def build_pack_output(
    pack: PackMetadata,
    records: Sequence[dict[str, Any]],
    mapping: dict[str, Any],
    entries: dict[str, Any],
) -> dict[str, Any]:
    output: dict[str, Any] = {
        "label": pack.label,
        "mapping": mapping,
        "entries": dict(
            sorted(entries.items(), key=lambda item: item[0].casefold())
        ),
    }

    folders = collect_folders(records)
    if folders:
        output["folders"] = folders

    return remove_empty(output)


def process_item_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    items = [
        record
        for record in records
        if is_top_level_document(record, "Item")
    ]
    index = RecordIndex(records)
    mapping = item_mapping_for(items)
    duplicate_names = Counter(clean_string(item.get("name")) for item in items)
    entries: dict[str, Any] = {}

    for item in items:
        entry = extract_item_entry(item, mapping, index)
        if entry:
            entries[export_key_for(item, duplicate_names)] = entry

    return build_pack_output(pack, records, mapping, entries)


def process_actor_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    actors = [
        record
        for record in records
        if is_top_level_document(record, "Actor")
    ]
    index = RecordIndex(records)
    embedded_items: list[dict[str, Any]] = []

    for actor in actors:
        embedded_items.extend(index.embedded(actor, "items"))

    actor_mapping, item_mapping = actor_mapping_for(actors, embedded_items)
    duplicate_names = Counter(clean_string(actor.get("name")) for actor in actors)
    entries: dict[str, Any] = {}

    for actor in actors:
        entry = extract_actor_entry(
            actor,
            actor_mapping,
            item_mapping,
            index,
        )
        if entry:
            entries[export_key_for(actor, duplicate_names)] = entry

    return build_pack_output(pack, records, actor_mapping, entries)


def process_journal_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    journals = [
        record
        for record in records
        if is_top_level_document(record, "JournalEntry")
    ]
    index = RecordIndex(records)
    pages: list[dict[str, Any]] = []

    for journal in journals:
        pages.extend(index.embedded(journal, "pages"))

    journal_mapping, page_mapping = journal_mapping_for(journals, pages)
    duplicate_names = Counter(
        clean_string(journal.get("name")) for journal in journals
    )
    entries: dict[str, Any] = {}

    for journal in journals:
        entry = extract_journal_entry(
            journal,
            journal_mapping,
            page_mapping,
            index,
        )
        if entry:
            entries[export_key_for(journal, duplicate_names)] = entry

    return build_pack_output(pack, records, journal_mapping, entries)


def process_rolltable_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    tables = [
        record
        for record in records
        if is_top_level_document(record, "RollTable")
    ]
    index = RecordIndex(records)
    mapping = rolltable_mapping_for(tables)
    duplicate_names = Counter(clean_string(table.get("name")) for table in tables)
    entries: dict[str, Any] = {}

    for table in tables:
        entry = extract_rolltable_entry(table, mapping, index)
        if entry:
            entries[export_key_for(table, duplicate_names)] = entry

    return build_pack_output(pack, records, mapping, entries)


def process_macro_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    macros = [
        record
        for record in records
        if is_top_level_document(record, "Macro")
    ]
    mapping = macro_mapping_for()
    duplicate_names = Counter(clean_string(macro.get("name")) for macro in macros)
    entries: dict[str, Any] = {}

    for macro in macros:
        entry = extract_primitive_fields(macro, mapping)
        if entry:
            entries[export_key_for(macro, duplicate_names)] = entry

    return build_pack_output(pack, records, mapping, entries)


def process_adventure_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    adventures = [
        record
        for record in records
        if is_top_level_document(record, "Adventure")
    ]
    collections = collect_adventure_documents(adventures)

    all_items = [*collections["items"], *collections["actor_items"]]
    item_mapping = item_mapping_for(all_items)
    actor_mapping, _ = actor_mapping_for(
        collections["actors"],
        collections["actor_items"],
    )
    journal_mapping, page_mapping = journal_mapping_for(
        collections["journal"],
        collections["pages"],
    )
    table_mapping = rolltable_mapping_for(collections["tables"])
    mapping = adventure_mapping_for(
        item_mapping,
        actor_mapping,
        journal_mapping,
        table_mapping,
    )

    duplicate_names = Counter(
        clean_string(adventure.get("name")) for adventure in adventures
    )
    entries: dict[str, Any] = {}

    for adventure in adventures:
        entry = extract_adventure_entry(
            adventure,
            mapping,
            item_mapping,
            actor_mapping,
            journal_mapping,
            page_mapping,
            table_mapping,
        )
        if entry:
            entries[export_key_for(adventure, duplicate_names)] = entry

    return build_pack_output(pack, records, mapping, entries)


def process_scene_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    scenes = [
        record
        for record in records
        if is_top_level_document(record, "Scene")
    ]
    mapping = scene_mapping()
    duplicate_names = Counter(clean_string(scene.get("name")) for scene in scenes)
    entries: dict[str, Any] = {}

    for scene in scenes:
        entry = extract_primitive_fields(scene, mapping)
        if entry:
            entries[export_key_for(scene, duplicate_names)] = entry

    return build_pack_output(pack, records, mapping, entries)


def process_generic_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    documents = [
        record
        for record in records
        if is_top_level_document(record, pack.document_type)
    ]
    mapping: dict[str, Any] = {"name": "name"}
    description_path = detect_description_path(documents, pack.document_type)
    reserved_paths: set[str] = set()

    if description_path:
        mapping["description"] = description_path
        reserved_paths.add(description_path)

    mapping = merge_mapping(
        mapping,
        custom_scalar_mapping(documents, reserved_paths=reserved_paths),
    )
    duplicate_names = Counter(
        clean_string(document.get("name")) for document in documents
    )
    entries: dict[str, Any] = {}

    for document in documents:
        entry = extract_primitive_fields(document, mapping)
        entry.update(
            custom_scalar_values(document, custom_paths_from_mapping(mapping))
        )
        if entry:
            entries[export_key_for(document, duplicate_names)] = entry

    return build_pack_output(pack, records, mapping, entries)


def process_pack(
    records: Sequence[dict[str, Any]],
    pack: PackMetadata,
) -> dict[str, Any]:
    processors = {
        "Item": process_item_pack,
        "Actor": process_actor_pack,
        "JournalEntry": process_journal_pack,
        "RollTable": process_rolltable_pack,
        "Adventure": process_adventure_pack,
        "Macro": process_macro_pack,
        "Scene": process_scene_pack,
    }

    processor = processors.get(pack.document_type, process_generic_pack)
    return processor(records, pack)


def add_polish_plural_placeholders(data: Any) -> Any:
    if isinstance(data, dict):
        if "one" in data:
            source = data.get("other", data["one"])
            data.setdefault("few", source)
            data.setdefault("many", source)

        for value in data.values():
            add_polish_plural_placeholders(value)

    elif isinstance(data, list):
        for value in data:
            add_polish_plural_placeholders(value)

    return data

def collect_pack_folder_names(manifest: dict[str, Any]) -> list[str]:
    names: set[str] = set()

    def visit(folders: Any) -> None:
        if not isinstance(folders, list):
            return

        for folder in folders:
            if not isinstance(folder, dict):
                continue

            name = clean_string(folder.get("name"))
            if name:
                names.add(name)

            visit(folder.get("folders"))

    visit(manifest.get("packFolders"))
    return sorted(names, key=str.casefold)


def write_pack_folders_translation(
    manifest: dict[str, Any],
    compendium_root: pathlib.Path,
    package_id: str,
) -> None:
    names = collect_pack_folder_names(manifest)
    if not names:
        return

    destination = compendium_root / f"{package_id}._packs-folders.json"
    destination.write_text(
        json.dumps(
            {"entries": {name: name for name in names}},
            ensure_ascii=False,
            indent=4,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"  zapisano foldery paczek: {destination}")


def export_package(
    package_root: pathlib.Path,
    manifest: dict[str, Any],
    output_root: pathlib.Path,
    raw_output_root: pathlib.Path,
    package_id: str,
    raw_filename_prefix: str | None = None,
) -> None:
    """Eksportuje paczki systemu albo modułu do wspólnego katalogu Babele."""
    compendium_root = output_root / "compendium"
    compendium_root.mkdir(parents=True, exist_ok=True)

    packs = normalize_pack_metadata(manifest)
    if not packs:
        raise ExportError(
            f"Manifest pakietu {package_id} nie zawiera obsługiwanych paczek."
        )

    failures: list[str] = []

    for pack in packs:
        print(
            f"Przetwarzam {package_id}.{pack.name} "
            f"[{pack.document_type}]..."
        )

        try:
            pack_path = resolve_pack_path(package_root, pack)
            raw_stem = (
                f"{raw_filename_prefix}.{pack.name}"
                if raw_filename_prefix
                else pack.name
            )
            raw_output_file = raw_output_root / f"{raw_stem}.json"
            records = read_pack_documents(
                pack_path,
                raw_output_file=raw_output_file,
            )
            output = process_pack(records, pack)
        except Exception as error:
            failures.append(f"{pack.name}: {error}")
            print(f"  Błąd: {error}", file=sys.stderr)
            continue

        destination = compendium_root / f"{package_id}.{pack.name}.json"
        destination.write_text(
            json.dumps(output, ensure_ascii=False, indent=4) + "\n",
            encoding="utf-8",
        )
        print(
            f"  zapisano {destination} "
            f"({len(output.get('entries', {}))} wpisów, "
            f"{len(output.get('mapping', {}))} pól mapowania)"
        )

    write_pack_folders_translation(
        manifest=manifest,
        compendium_root=compendium_root,
        package_id=package_id,
    )

    if failures:
        details = "\n".join(f"  - {failure}" for failure in failures)
        raise ExportError(
            f"Nie udało się wyeksportować wszystkich paczek {package_id}:\n"
            + details
        )


def export_system(
    system_root: pathlib.Path,
    manifest: dict[str, Any],
    output_root: pathlib.Path,
    raw_output_root: pathlib.Path,
    copy_language: bool = True,
    language_url: str = DEFAULT_LANGUAGE_URL,
) -> None:
    export_package(
        package_root=system_root,
        manifest=manifest,
        output_root=output_root,
        raw_output_root=raw_output_root,
        package_id=SYSTEM_ID,
    )

    if copy_language:
        download_language_file(language_url, output_root)


def export_community_module(
    module_root: pathlib.Path,
    manifest: dict[str, Any],
    output_root: pathlib.Path,
    raw_output_root: pathlib.Path,
) -> None:
    module_id = clean_string(manifest.get("id")) or COMMUNITY_MODULE_ID
    export_package(
        package_root=module_root,
        manifest=manifest,
        output_root=output_root,
        raw_output_root=raw_output_root,
        package_id=module_id,
        raw_filename_prefix=module_id,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Eksport kompendiów Shadowdark do plików Babele."
    )
    parser.add_argument(
        "--manifest",
        default=DEFAULT_MANIFEST_URL,
        help="Adres manifestu system.json.",
    )
    parser.add_argument(
        "--source-dir",
        type=pathlib.Path,
        help=(
            "Rozpakowany system albo katalog repozytorium Shadowdark. "
            "Pomija pobieranie archiwum ZIP."
        ),
    )
    parser.add_argument(
        "--output",
        type=pathlib.Path,
        help=(
            "Katalog wynikowy z plikami Babele. Domyślnie "
            "shadowdark_<wersja>."
        ),
    )
    parser.add_argument(
        "--work-dir",
        type=pathlib.Path,
        default=pathlib.Path(DEFAULT_WORK_DIR),
        help=f"Katalog roboczy. Domyślnie {DEFAULT_WORK_DIR}.",
    )
    parser.add_argument(
        "--keep-work-dir",
        action="store_true",
        help="Nie usuwa pobranego archiwum i rozpakowanego systemu.",
    )
    parser.add_argument(
        "--no-lang",
        action="store_true",
        help="Nie pobiera i18n/en.yaml i nie tworzy pliku en.json.",
    )
    parser.add_argument(
        "--lang-url",
        default=DEFAULT_LANGUAGE_URL,
        help=(
            "Adres źródłowego pliku YAML lokalizacji. Domyślnie "
            "repozytorium Shadowdark, gałąź develop."
        ),
    )
    parser.add_argument(
        "--raw-output",
        type=pathlib.Path,
        default=pathlib.Path(DEFAULT_RAW_OUTPUT_DIR),
        help=(
            "Katalog prostych plików JSON, po jednym pliku na paczkę. "
            f"Domyślnie {DEFAULT_RAW_OUTPUT_DIR}."
        ),
    )
    parser.add_argument(
        "--community-manifest",
        default=DEFAULT_COMMUNITY_MANIFEST_URL,
        help="Adres manifestu module.json dla Shadowdark Community Content.",
    )
    parser.add_argument(
        "--community-source-dir",
        type=pathlib.Path,
        help=(
            "Rozpakowany moduł albo katalog repozytorium Shadowdark "
            "Community Content. Pomija pobieranie archiwum modułu."
        ),
    )
    parser.add_argument(
        "--no-community-content",
        action="store_true",
        help="Nie pobiera i nie eksportuje Shadowdark Community Content.",
    )
    return parser.parse_args()


def determine_output_root(
    args: argparse.Namespace,
    manifest: dict[str, Any],
) -> pathlib.Path:
    if args.output:
        return args.output.resolve()

    version = clean_string(manifest.get("version")) or "export"
    safe_version = re.sub(r"[^A-Za-z0-9._-]+", "_", version)
    return pathlib.Path(f"{SYSTEM_ID}_{safe_version}").resolve()

def determine_raw_output_root(args: argparse.Namespace) -> pathlib.Path:
    return args.raw_output.resolve()

def prepare_downloaded_system(
    args: argparse.Namespace,
    manifest: dict[str, Any],
) -> tuple[pathlib.Path, pathlib.Path]:
    work_root = args.work_dir.resolve()
    recreate_directory(work_root)

    zip_path = work_root / DEFAULT_ZIP_NAME
    extract_root = work_root / "system"
    download_url = clean_string(manifest.get("download")) or DEFAULT_DOWNLOAD_URL

    print(f"Pobieram system: {download_url}")
    download_file(download_url, zip_path)

    extract_root.mkdir(parents=True, exist_ok=True)
    safe_extract_zip(zip_path, extract_root)
    return find_system_root(extract_root), work_root


def prepare_downloaded_module(
    manifest: dict[str, Any],
    work_root: pathlib.Path,
) -> pathlib.Path:
    module_id = clean_string(manifest.get("id")) or COMMUNITY_MODULE_ID
    download_url = clean_string(manifest.get("download"))
    if not download_url:
        raise ExportError(
            f"Manifest modułu {module_id} nie zawiera pola download."
        )

    module_work_root = work_root / "modules" / module_id
    if module_work_root.exists():
        shutil.rmtree(module_work_root)
    module_work_root.mkdir(parents=True, exist_ok=True)

    zip_path = work_root / COMMUNITY_ZIP_NAME
    print(f"Pobieram moduł {module_id}: {download_url}")
    download_file(download_url, zip_path)
    safe_extract_zip(zip_path, module_work_root)
    return find_module_root(module_work_root, module_id)


def main() -> int:
    args = parse_args()
    work_root: pathlib.Path | None = None
    output_root: pathlib.Path | None = None
    raw_output_root: pathlib.Path | None = None

    try:
        manifest = request_json(args.manifest)
        output_root = determine_output_root(args, manifest)
        raw_output_root = determine_raw_output_root(args)

        if args.source_dir:
            system_root = normalize_source_root(args.source_dir)
        else:
            system_root, work_root = prepare_downloaded_system(args, manifest)

        community_manifest: dict[str, Any] | None = None
        community_root: pathlib.Path | None = None

        if not args.no_community_content:
            community_manifest = request_json(args.community_manifest)

            if args.community_source_dir:
                community_root = normalize_source_root(
                    args.community_source_dir
                )
            else:
                if work_root is None:
                    work_root = args.work_dir.resolve()
                    recreate_directory(work_root)

                community_root = prepare_downloaded_module(
                    manifest=community_manifest,
                    work_root=work_root,
                )

        # Surowe paczki są zapisywane jako pojedyncze pliki JSON.
        recreate_directory(raw_output_root)

        # Finalne pliki Babele pozostają w shadowdark_<wersja>.
        ensure_directory(output_root)

        print(f"Katalog surowych plików JSON: {raw_output_root}")
        print(f"Katalog wynikowy Babele: {output_root}")

        export_system(
            system_root=system_root,
            manifest=manifest,
            output_root=output_root,
            raw_output_root=raw_output_root,
            copy_language=not args.no_lang,
            language_url=args.lang_url,
        )

        if community_manifest is not None and community_root is not None:
            export_community_module(
                module_root=community_root,
                manifest=community_manifest,
                output_root=output_root,
                raw_output_root=raw_output_root,
            )

        print(f"Eksport zakończony: {output_root}")
        return 0

    except requests.RequestException as error:
        print(f"Błąd sieci: {error}", file=sys.stderr)
        return 1
    except (OSError, zipfile.BadZipFile, ExportError) as error:
        print(f"Błąd: {error}", file=sys.stderr)
        return 1
    finally:
        if work_root is not None and not args.keep_work_dir:
            protected_roots = [
                path
                for path in (output_root, raw_output_root)
                if path is not None
            ]
            protected_inside_work = any(
                path == work_root or work_root in path.parents
                for path in protected_roots
            )

            if protected_inside_work:
                print(
                    "Katalog roboczy nie został usunięty, ponieważ zawiera "
                    "katalog surowy lub katalog wynikowy."
                )
            else:
                shutil.rmtree(work_root, ignore_errors=True)

if __name__ == "__main__":
    raise SystemExit(main())
