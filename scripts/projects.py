"""Discover the independent Lean packages in Colombo_Lean (Python 3.11+)."""

import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def safe_path(root, relative):
    """Resolve a portable package-relative path without accepting traversal."""
    if not isinstance(relative, str) or not relative or "\\" in relative:
        raise ValueError(f"Invalid relative path: {relative!r}")
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts or ":" in relative:
        raise ValueError(f"Path must stay inside the package: {relative!r}")
    candidate = root / path
    if not candidate.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Path escapes the package: {relative!r}")
    return candidate


def load_metadata(directory):
    try:
        metadata = json.loads((directory / "project.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"{directory.name}: cannot read project.json") from error
    if not isinstance(metadata, dict) or metadata.get("schema_version") != 1:
        raise ValueError(f"{directory.name}: unsupported project.json schema")
    return metadata


def lake_directory(directory):
    return safe_path(directory, load_metadata(directory).get("lake_project", "."))


def discover(root=ROOT):
    projects = []
    for directory in sorted((root / "problems").iterdir()):
        if not directory.is_dir() or directory.name.startswith("."):
            continue
        if not re.fullmatch(r"(?:[a-z0-9]+(?:[-_][a-z0-9]+)*|[0-9]{4}\.[0-9]{4,5})", directory.name):
            raise ValueError(f"Invalid package name: {directory.name}")
        lake = lake_directory(directory)
        required = [directory / "README.md", directory / "proof/Audit.lean",
                    lake / "lean-toolchain", lake / "lake-manifest.json", lake / "lakefile.toml"]
        missing = [str(path.relative_to(directory)) for path in required if not path.is_file()]
        if missing:
            raise ValueError(f"{directory.name}: missing {', '.join(missing)}")
        projects.append({"name": directory.name, "path": directory.relative_to(root).as_posix(),
                         "lake_path": lake.relative_to(root).as_posix(), "artifact_name": directory.name})
    if not projects:
        raise ValueError("No Lean packages found under problems/")
    return projects


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Print a GitHub Actions matrix.")
    args = parser.parse_args()
    try:
        projects = discover()
    except (ValueError, OSError) as error:
        parser.exit(1, f"{error}\n")
    if args.json:
        # Start the largest source trees first so long builds do not sit behind
        # many small packages in a bounded-parallelism CI matrix.
        def source_bytes(project):
            package = ROOT / project["path"]
            return sum(safe_path(package, name).stat().st_size
                       for name in load_metadata(package)["production_files"])
        projects.sort(key=source_bytes, reverse=True)
        print(json.dumps({"include": projects}, separators=(",", ":")))
    else:
        for project in projects:
            print(f'{project["name"]}: {project["lake_path"]}')


if __name__ == "__main__":
    main()
