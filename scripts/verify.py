"""Verify current Lean sources, build every production module, and run axiom audits.

Static checks do not establish that a theorem compiles or matches a manuscript.
Full verification requires the package's pinned Lean toolchain and dependencies.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import tomllib

from projects import ROOT, discover, load_metadata, safe_path

FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by|extern|ofReduceBool)\b"
                       r"|\bdebug\.skipKernelTC\s+(?:true|1)\b")
CHAR_LITERAL = re.compile(r"'(?:\\.|[^\\'\n])'")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def code_only(text):
    """Blank nested comments and string literals, preserving line boundaries."""
    output = []
    index, depth, string = 0, 0, False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1; output.extend("  "); index += 2
            elif text.startswith("-/", index):
                depth -= 1; output.extend("  "); index += 2
            else:
                output.append("\n" if text[index] == "\n" else " "); index += 1
        elif string:
            if text[index] == "\\" and index + 1 < len(text):
                output.extend("  "); index += 2
            elif text[index] == '"':
                string = False; output.append(" "); index += 1
            else:
                output.append("\n" if text[index] == "\n" else " "); index += 1
        elif text.startswith("/-", index):
            depth = 1; output.extend("  "); index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end == -1 else end
            output.extend(" " * (end - index)); index = end
        elif text[index] == "'" and (literal := CHAR_LITERAL.match(text, index)):
            output.extend(" " * len(literal[0])); index += len(literal[0])
        elif text[index] == '"':
            string = True; output.append(" "); index += 1
        else:
            output.append(text[index]); index += 1
    require(depth == 0 and not string, "Unterminated Lean comment or string")
    return "".join(output)


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_inventory(package):
    paths = set()
    for directory, folders, files in os.walk(package, followlinks=False):
        folders[:] = [name for name in folders if name not in {".lake", ".git"}]
        for name in files:
            if name.endswith(".lean"):
                paths.add((Path(directory)/name).relative_to(package).as_posix())
    return paths


def validate_hashes(package, entries, label):
    require(isinstance(entries, dict) and entries, f"Empty or invalid {label}")
    for relative, expected in entries.items():
        path = safe_path(package, relative)
        require(path.is_file() and not path.is_symlink(), f"Missing or linked {label} file: {relative}")
        require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                f"Invalid SHA-256: {relative}")
        require(fingerprint(path) == expected, f"SHA-256 mismatch: {relative}")


def module_name(package, lake, config, relative):
    path = safe_path(package, relative)
    source_roots = {safe_path(lake, lib.get("srcDir", ".")) for lib in config.get("lean_lib", [])}
    matches = [root for root in source_roots if path.is_relative_to(root)]
    require(matches, f"Production source is outside Lake source directories: {relative}")
    root = max(matches, key=lambda p: len(p.parts))
    name = ".".join(path.relative_to(root).with_suffix("").parts)
    require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name),
            f"Unsupported Lean module path: {relative}")
    return name


def static_check(package):
    meta = load_metadata(package)
    lake = safe_path(package, meta.get("lake_project", "."))
    sources, configurations = meta.get("source_files"), meta.get("config_files")
    validate_hashes(package, sources, "source_files")
    validate_hashes(package, configurations, "config_files")
    actual = source_inventory(package)
    require(actual == set(sources), f"Lean source inventory changed: added={sorted(actual-set(sources))}, "
            f"missing={sorted(set(sources)-actual)}")
    required_configs = {(lake / name).relative_to(package).as_posix()
                        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")}
    require(required_configs.issubset(configurations), "Config fingerprint inventory is incomplete")
    config_text = (lake / "lakefile.toml").read_text(encoding="utf-8-sig")
    require(not re.search(r"debug\.skipKernelTC[=\s]+true", config_text), "Lake disables kernel checking")
    config = tomllib.loads(config_text)
    lock = json.loads((lake / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    require((lake / "lean-toolchain").read_text().strip() == meta.get("lean_toolchain"),
            "Lean toolchain differs from project.json")
    for dependency in lock.get("packages", []):
        require(dependency.get("type") == "git" and
                re.fullmatch(r"[0-9a-f]{40}", dependency.get("rev", "")),
                f"Dependency is not locked to a Git commit: {dependency.get('name')}")
    production, audits = meta.get("production_files"), meta.get("audit_files")
    require(isinstance(production, list) and production and len(production) == len(set(production)),
            "production_files must be a nonempty unique list")
    require(isinstance(audits, list) and audits and len(audits) == len(set(audits)),
            "audit_files must be a nonempty unique list")
    require("proof/Audit.lean" in audits, "The complete project audit must be scheduled")
    require(not (set(production) & set(audits)), "Production and audit inventories overlap")
    require(set(production) | set(audits) == set(sources), "Every Lean file must be compiled or audited")
    modules = {}
    for relative in production:
        module = module_name(package, lake, config, relative)
        require(module not in modules, f"Duplicate module name: {module}")
        code = code_only(safe_path(package, relative).read_text(encoding="utf-8-sig"))
        forbidden = FORBIDDEN.search(code)
        require(not forbidden, f"Trust escape in {relative}: {forbidden.group() if forbidden else ''}")
        modules[module] = relative
    # Audit drivers may quote axiom names to reject them, but must not admit proofs.
    for relative in audits:
        source = safe_path(package, relative).read_text(encoding="utf-8-sig")
        code = code_only(source)
        require(not re.search(r"\b(?:sorry|admit|native_decide)\b", code),
                f"Trust escape in audit: {relative}")
        # These drivers read literal JSON inventories relative to the Lake cwd.
        for filename in re.findall(r'IO\.FS\.read(?:Bin)?File\s+"([^"\n]+)"', source):
            data = (lake / filename).resolve()
            require(data.is_relative_to(package.resolve()), f"Audit input escapes package: {filename}")
            key = data.relative_to(package.resolve()).as_posix()
            require(key in configurations, f"Audit input is not fingerprinted: {key}")
    return meta, lake, config, modules


def run_logged(command, cwd, logfile, timeout):
    started = time.monotonic()
    with logfile.open("w", encoding="utf-8") as output:
        output.write("Command: " + json.dumps(command) + "\n"); output.flush()
        result = subprocess.run(command, cwd=cwd, stdout=output, stderr=subprocess.STDOUT,
                                timeout=timeout, encoding="utf-8", errors="replace")
    if result.returncode:
        tail = logfile.read_text(encoding="utf-8", errors="replace")[-5000:]
        raise ValueError(f"Command failed ({result.returncode}); {logfile}\n{tail}")
    return {"command": command, "seconds": round(time.monotonic()-started, 2), "exit_code": 0}


def verify(package, static=False, timeout=14400):
    proof = package / "proof"
    proof.mkdir(exist_ok=True)
    report_path = proof / ("static-verification.json" if static else "verification.json")
    report = {"project": package.name, "checked_at": datetime.now(timezone.utc).isoformat(),
              "mode": "static" if static else "build-and-audit", "status": "running",
              "manuscript_coverage_certified": False}
    try:
        meta, lake, config, modules = static_check(package)
        report.update(lean_sources=len(meta["source_files"]), production_modules=len(modules),
                      audit_inputs=len(meta["audit_files"]), toolchain=meta["lean_toolchain"])
        if not static:
            executable = shutil.which("lake")
            require(executable, "lake is not on PATH; install elan and the pinned toolchain")
            report["commands"] = []
            version = subprocess.check_output([executable, "env", "lean", "--version"], cwd=lake,
                                              text=True, timeout=timeout).strip()
            pinned = meta["lean_toolchain"].rsplit(":v", 1)[-1]
            require(re.search(r"\bversion " + re.escape(pinned) + r"(?:\s|,|$)", version),
                    f"Unexpected active Lean version: {version}")
            report["actual_lean_version"] = version
            targets = config.get("defaultTargets", [])
            require(targets, "No Lake default targets configured")
            report["commands"].append(run_logged([executable, "build", *targets], lake,
                                                 proof/"build.log", timeout))
            # Explicit module targets cover helpers omitted from an aggregate import.
            ordered = sorted(modules)
            for start in range(0, len(ordered), 40):
                report["commands"].append(run_logged(
                    [executable, "build", *["+"+module for module in ordered[start:start+40]]],
                    lake, proof/f"modules-{start//40:03d}.log", timeout))
            for index, relative in enumerate(meta["audit_files"]):
                report["commands"].append(run_logged(
                    [executable, "env", "lean", "-Ddebug.skipKernelTC=false",
                     str(safe_path(package, relative).resolve())],
                    lake, proof/f"audit-{index:03d}.log", timeout))
            static_check(package)
        report["status"] = "passed"
        return report
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        report_path.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", help="Verify one package name.")
    parser.add_argument("--static", action="store_true", help="Check source/configuration integrity without Lean.")
    parser.add_argument("--timeout", type=int, default=14400, help="Timeout in seconds for each build/audit command.")
    args = parser.parse_args()
    try:
        projects = discover()
        if args.project:
            projects = [project for project in projects if project["name"] == args.project]
            require(projects, f"Unknown package: {args.project}")
        require(args.timeout > 0, "Timeout must be positive")
    except (ValueError, OSError) as error:
        parser.exit(1, f"{error}\n")
    failed = []
    for project in projects:
        print(f'Verifying {project["name"]} ...', flush=True)
        try:
            report = verify(ROOT/project["path"], args.static, args.timeout)
            print(f'PASS: {report["production_modules"]} production modules, {report["audit_inputs"]} audit inputs', flush=True)
        except (ValueError, OSError, subprocess.SubprocessError) as error:
            failed.append(project["name"])
            print(str(error), file=sys.stderr, flush=True)
    if failed:
        print("Failed: " + ", ".join(failed), file=sys.stderr)
        return 1
    print(f'All {len(projects)} package(s) passed {"static checks" if args.static else "build and audits"}.')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
