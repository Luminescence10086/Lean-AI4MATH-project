# 数竞屠宰场（Lean × AI 数学证明试验场）

> 与 AI 协作、用 Lean 4 形式化证明数学命题的试验场。**数学侧项目**。

## 目录
- `IMO组合预选题*.lean` —— 主要形式化工作（含零告警版、初等证明路线）
- `IMO组合预选题_*逻辑图.md`／`*评估.md` —— 证明逻辑图与路线评估
- `GPT-Bridge/` —— 与 AI 协作的桥接脚本与记录
- `explore/` —— 探索性草稿
- `lakefile.toml`／`lean-toolchain`／`lake-manifest.json` —— Lake 工程配置

## 复现
```bash
lake exe cache get    # 拉取 mathlib 缓存
lake build
```

> 构建产物（`.lake/`）不入库。
