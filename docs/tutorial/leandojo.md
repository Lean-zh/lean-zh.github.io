# LeanDojo | 为 Lean 定理证明器搭建桥梁

## 简介

LeanDojo 是一个为 Lean 定理证明器设计的 Python 库，支持 Lean 3 和 Lean 4 版本，其在解析 Lean 文件及与环境交互方面有很高的实用性。项目提供以下两大功能：

- **数据提取**：从 Lean 存储库中提取证明状态、策略、前提等关键信息。
- **环境交互**：允许用户以编程方式与 Lean 环境进行交互。

![LeanDojo 功能图示](https://qiniu.wzhecnu.cn/FileBed/source20240707042057.png)

LeanDojo 按照 `仓库=>文件=>定理` 的层次结构来解析文件，围绕 `LeanGitRepo` 对象进行操作：

![LeanGitRepo 示意图](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240606015531.png)

### 相关链接

- **项目文档**：[LeanDojo: Machine Learning for Theorem Proving in Lean](https://leandojo.readthedocs.io/en/latest/)
- **项目仓库**：[lean-dojo/LeanDojo](https://github.com/lean-dojo/LeanDojo)
- **社区帖子**：[Releasing LeanDojo](https://leanprover.zulipchat.com/#narrow/stream/219941-Machine-Learning-for-Theorem-Proving/topic/Releasing.20LeanDojo)

## 基本示例

### 准备工作

安装依赖，测试用 Python 3.10 版本：

```bash
pip install lean-dojo
```

使用官方示例仓库：[yangky11/lean4-example](https://github.com/yangky11/lean4-example)。这是一个简洁的 Lean 包，文件结构如下：

```bash
lean4-example/
├── lakefile.lean
├── lake-manifest.json
├── Lean4Example.lean
├── lean-toolchain
├── LICENSE
└── README.md
```

其中，`Lean4Example.lean` 文件的内容：

```lean
open Nat (add_assoc add_comm)

theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, ←add_assoc]

theorem foo (a : Nat) : a + 1 = Nat.succ a := by rfl
```

从 `Nat` 命名空间导入了 `add_assoc` 和 `add_comm` 两个引理，然后定义了两个定理。

### 设置环境变量

环境变量只在首次 `import lean_dojo` 时生效，因此先设置：

```python
import os

# 设置 GitHub token 以避免请求频率限制
os.environ['GITHUB_ACCESS_TOKEN'] = 'gho_xxx'
# 配置线程数以加快 `trace` 的运行速度
os.environ['NUM_PROCS'] = '64'
# 设置临时目录以便观察 `trace` 阶段生成的文件
os.environ['TMP_DIR'] = 'temp_dir'
# 取消远程缓存下载，在本地进行构建
os.environ['DISABLE_REMOTE_CACHE'] = 'true'
```

### 仓库对象

环境交互和数据提取都是围绕 `LeanGitRepo` 对象展开的。

首先导入 `LeanGitRepo` 类

```python
from lean_dojo import LeanGitRepo
```

初始化仓库对象，可使用 commit hash 或 main 分支：

```python
repo = LeanGitRepo("https://github.com/PatrickMassot/GlimpseOfLean", "8d73d32d90ec2315616ad8e720754eeacfb96af6")
```

查看仓库对象的基本属性：

```python
print("repo.url", repo.url)
print("repo.commit", repo.commit)
print("repo.repo", repo.repo)
print("repo.lean_version", repo.lean_version)
print(repo.get_config("lean-toolchain"))
```

输出结果：

```bash
repo.url https://github.com/PatrickMassot/GlimpseOfLean
repo.commit 8d73d32d90ec2315616ad8e720754eeacfb96af6
repo.repo Repository(full_name="PatrickMassot/GlimpseOfLean")
repo.lean_version 873ef2d894af80d8fc672e35f7e28bae314a1f6f
{'content': 'leanprover/lean4:v4.8.0-rc2\n'}
```

这里 `lean_version` 是一个 commit hash，而不是直观的版本字符串。

### Trace 操作

对仓库进行 trace 操作：

```python
from lean_dojo import trace

repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "04e29174a45eefaccb49b835a372aa762321194e")
trace(repo, dst_dir="traced_lean4-example")
```

`trace` 主要执行以下步骤：

1. 克隆仓库到 `TMP_DIR` 目录，并执行 `lake build` 进行构建。
2. 获取仓库的 Lean4 版本，将对应版本的 Lean4 文件复制到 `.lake/packages` 目录。
3. **数据提取**：将 `ExtractData.lean` 脚本拷贝到仓库，执行 `lake env lean --run ExtractData.lean` 命令，提取 AST 树、状态和定理等信息，随后删除 `ExtractData.lean` 文件。
4. **环境交互**：将 `Lean4Repl.lean` 脚本拷贝到仓库，并更新 `lakefile` 以包含依赖信息，执行 `lake build Lean4Repl` 命令进行构建。
5. 获取仓库信息，并更新 `.cache/leandojo` 目录下的缓存。

此外，**`ExtractData.lean` 和 `Lean4Repl.lean` 文件是整个项目的核心**。如果只关心环境交互问题，可以重点关注 `Lean4Repl.lean` 文件。

### 数据提取

提取的文件位于 `.lake/build` 目录：

```bash
.lake
├── build
│   ├── ir
│   │   ├── Lean4Example.ast.json
│   │   ├── Lean4Example.c
│   │   ├── Lean4Example.c.hash
│   │   ├── Lean4Example.dep_paths
│   │   └── Lean4Example.trace.xml
│   └── lib
│       ├── Lean4Example.ilean
│       ├── Lean4Example.ilean.hash
│       ├── Lean4Example.olean
│       ├── Lean4Example.olean.hash
│       └── Lean4Example.trace
├── lakefile.olean
├── lakefile.olean.trace
└── packages
    └── lean4
        ├── bin
        ├── include
        ├── lib
        ├── LICENSE
        ├── LICENSES
        ├── share
        └── src
```

这里有两类比较重要的文件：

- `.ast.json`：包含带有语义信息的注释，例如策略状态和名称。
- `.trace.xml`：结构化处理后的句法和语义信息。

项目按 `仓库 => 文件 => 定理` 的层次结构生成文件。示例中的例子比较简单，仅包含一个文件。


### 环境交互

示例仓库中包含两个定理。以 `hello_world` 定理为例，展示如何使用 `Dojo` 类进行环境交互。

```lean
theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, ←add_assoc]
```

首先导入 `Dojo` 类和 `Theorem` 类：

```python
from lean_dojo import Theorem, Dojo
```

获取定理对象，从 `Lean4Example.lean` 文件中提取 `hello_world` 定理：

```python
theorem = Theorem(repo, "Lean4Example.lean", "hello_world")
```

获取初始状态：

```python
dojo, state_0 = Dojo(theorem).__enter__()
print(state_0)
# TacticState(pp='a b c : Nat\n⊢ a + b + c = a + c + b', id=0, message=None)
print(state_0.pp)
# a b c : Nat
# ⊢ a + b + c = a + c + b
```

对初始状态 `state_0` 执行策略，并获取更新后的状态：

```python
state_1 = dojo.run_tac(state_0, "rw [add_assoc]")
print(state_1.pp)
# a b c : Nat
# ⊢ a + (b + c) = a + c + b
```

继续对状态 `state_1` 执行策略，并获取最终状态：

```python
print(dojo.run_tac(state_1, "sorry"))
# ProofGivenUp()
dojo.run_tac(state_1, "rw [add_comm b, ←add_assoc]")
# ProofFinished(tactic_state_id=4, message='')
```

## 小结

以上，演示了用 LeanDojo 进行数据提取和环境交互。如果对关键实现细节感兴趣，可以进一步阅读两个核心文件：

- [ExtractData.lean](https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean)
- [Lean4Repl.lean](https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/interaction/Lean4Repl.lean)
