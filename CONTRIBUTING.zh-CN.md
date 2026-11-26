# Contributing to Colombo Lean

修改前阅读 project README 和 Lean hypotheses，确保 statement、proof code 与 documentation 一致。

1. 独立 Lake project 放在 `problems/<id>/`，固定 Lean toolchain 和可移植的 Git dependency lock。
2. 所有当前 `.lean` 文件列入 `project.json:source_files`，分别归入 `production_files` 或 `audit_files`，并记录实际文件 bytes 的 SHA-256。`config_files` 固定 toolchain、Lake file 和 lockfile。
3. 先 review statement、assumptions、imports 和 audits，再更新 hash。Hash 仅确认文件 identity，不证明 correctness。
4. Build 全部 production modules，执行全部 audit files；保留 Lean kernel verification。
5. 修改 endpoints 或 assumptions 后同步更新 scope。Conditional theorem 仍需标为 conditional；build 成功不代表 manuscript coverage。

```sh
python -m unittest discover -s tests -v
python scripts/verify.py --static
python scripts/verify.py --project <id>
```

提交 code、configuration 和经过 review 的 inventory 更新。Generated artifacts、logs 和 verification reports 不进入 Git。保留 third-party license 和 attribution。
