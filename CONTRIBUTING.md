# Contributing to Colombo Lean

Keep mathematical statements, proof code, and documentation consistent. Read the project's README and Lean hypotheses before changing a result.

1. Use a separate `problems/<id>/` directory for an independent Lake project. Keep its Lean toolchain and portable Git dependency lock pinned.
2. Include every current `.lean` file in `project.json:source_files`, classified exactly once in `production_files` or `audit_files`. Record SHA-256 hashes of the actual file bytes. `config_files` pins the toolchain, Lake file, and lockfile.
3. Review changes to statements, assumptions, imported modules, and audits before refreshing hashes. A matching hash records identity, not correctness.
4. Build every production module and execute all audit files. Do not bypass the Lean kernel or introduce placeholders to make verification pass.
5. Rewrite scope documentation when assumptions or endpoints change. Conditional theorems must remain described as conditional; do not infer manuscript coverage from a successful build.

Run from the repository root:

```sh
python -m unittest discover -s tests -v
python scripts/verify.py --static
python scripts/verify.py --project <id>
```

Commit source and configuration changes with their reviewed inventory updates. Generated build artifacts, verification reports, and logs stay out of Git. Preserve third-party license and attribution notices.
