# jixia 数据分析 | TODO

jixia 是一个为 Lean 4 设计的新静态分析工具，其旨在支持构建具有 Lean 感知能力的集成开发环境（IDE），并为机器学习提取有用的数据。该项目是北京大学数学科学学院（BICMR）人工智能与数学程序项目的一部分。"jixia" 这个名字来源于历史上的“稷下学宫”，位于现在的山东淄博。

**工具特点**：

- **非侵入性**：无需对目标文件进行任何修改，这有利于提高缓存利用率，特别是在 mathlib4 上。
- 单文件分析。
- 源码级信息：包含每个定义函数的源码范围、参数和返回类型等信息。
- 易于扩展：jixia 的基于插件的设计使得易于扩展，同时保持了上述所有优点。

## 使用方式

下载仓库并构建：

```bash
git clone https://github.com/frenzymath/jixia
cd jixia
lake update && lake build
```

查看帮助：

```bash
❯ lake exe jixia --help                                                                                          
jixia
A static analysis tool for Lean 4.

USAGE:
    jixia [FLAGS] <file>

FLAGS:
    -h, --help                  Prints this message.
    -m, --import : String       Import info
    -d, --declaration : String  Declaration info
    -s, --symbol : String       Symbol info
    -e, --elaboration : String  Elaboration info
    -l, --line : String         Line info
    -a, --ast : String          AST
    -i, --initializer           Execute initializers

ARGS:
    file : String  File to process
```

jixia 支持多个参数，包括：
- `Import`：导入模块列表。
- `Declaration`：每个声明（`def`、`theorem`、`inductive` 等）的源码级信息。
- `Symbol`：精细化后的符号信息（或 Lean 4 术语中的 _常数_），包括它们的类型和引用图。
- `Elaboration`：关于精细化过程的信息，包括策略信息。
- `Line`：每行开始时的证明状态，如在 VSCode 的 infoview 中显示。
- `AST`：解析命令的完整转储。


## 使用示例

新建 Lean 文件，比如 `test.lean`

```lean
import Init

example : ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  -- Here are some comments
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption
```

运行命令：

```bash
lake exe jixia -d test.decl.json -s test.sym.json -e test.elab.json -l test.lines.json test.lean
```

## 参数介绍

TODO。