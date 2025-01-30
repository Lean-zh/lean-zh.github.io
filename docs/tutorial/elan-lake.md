# Lean 工具链使用指南

[上篇](../install.md)安装 Lean4 提到了 Lean 项目开发的三件套：版本管理器 [elan](https://github.com/leanprover/elan) + 包管理器和构建工具 [lake](https://github.com/leanprover/lake) + 语言本身的核心组件 [lean](https://github.com/leanprover/lean4)。下边分别介绍这三个工具的基本用法。

> 这类设计与其他编程语言类似，如 Rust（rustup + cargo + rustc）或 Node.js（nvm + npm + node）。

## elan 常用功能

[elan](https://github.com/leanprover/elan) 是 Lean 版本管理器，用于安装、管理和切换不同版本的 Lean。

版本管理：

```bash
elan --version   # 输出版本号来测试安装是否成功
elan self update # 更新 elan
elan show        # 显示已安装的 Lean 版本

# 下载指定 Lean 版本，所有版本可见 https://github.com/leanprover/lean4/releases
elan install leanprover/lean4:v4.10.0

# 下载最新稳定版本 stable
elan default leanprover/lean4:stable 

# 切换默认的 Lean 版本
# 切换到 leanprover/lean4:v4.11.0-rc1 
elan default leanprover/lean4:v4.11.0-rc1 

# 设置在当前目录下使用的 Lean 版本
elan override set leanprover/lean4:stable
# info: info: override toolchain for 'xxx' set to 'leanprover/lean4:stable'
```

指定版本运行 `lake` 或 `lean` 命令：

```bash
lake --version # 使用 elan 默认版本
# 使用指定版本
elan run leanprover/lean4:v4.10.0 lake --version
elan run leanprover/lean4:v4.10.0 lean --version
# 创建指定版本的项目
elan run leanprover/lean4:v4.10.0 lake new package
```

elan 配置记录可以在 `~/.elan/settings.toml` 查看。

具体地，Windows 下的 elan 管理目录为 `%USERPROFILE%\.elan\bin`，Linux/Mac 下的管理目录为 `$HOME/.elan`，内容形如

```bash
❯ tree .elan -L 2
.elan
├── bin
│   ├── elan
│   ├── lake
│   ├── lean
│   ├── leanc
│   ├── leanchecker
│   ├── leanmake
│   └── leanpkg
├── env
├── settings.toml
├── tmp
├── toolchains
│   └── stable
└── update-hashes
    └── stable
```

文件说明：

- `toolchains` 存放下载的各个 Lean 版本
- `settings.toml` 是 elan 的配置文件。
- `bin` 存放常用的二进制文件，比如 `lake`。

## Lake 基本用法

[lake](https://github.com/leanprover/lake) 全称 Lean Make，是 Lean 4 的包管理器，用于创建 Lean 项目，构建 Lean 包和编译 Lean 可执行文件。

本节介绍 `lake` 的基本用法，[Lean 函数式编程](https://www.leanprover.cn/fp-lean-zh/hello-world/starting-a-project.html)也提供了创建 Lean 项目的例子，而更全面的参数介绍可参考 [lake 文档](../references/lake-doc.md)。

在终端中运行（`your_project_name` 替换为你自己起的名字）

```bash
lake new your_project_name

# 或者手动创建一个新文件夹并在原地建立项目
mkdir your_folder_name && cd your_folder_name && lake init your_project_name
```

以创建一个名为 `your_project_name` 的空白新项目。这个项目的内容形如

```bash
your_project_name
├── YourProjectName
│   └── Basic.lean
├── lakefile.lean
├── lean-toolchain
├── Main.lean
├── YourProjectName.lean
└── ...
```


其中 `lakefile.lean` 是当前项目的配置文件，`lean-toolchain` 是当前项目使用的 Lean 版本。

初次让 Lean Server 运行该项目时会添加

```bash
├── .lake
   ├── lakefile.olean.trace
   └── ...
├── lake-manifest.json
```

如果你想在这个现有的工程中引用 Mathlib4，你需要在 `lakefile.lean` 文件尾中加入

```bash
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
```

保存文件后 VS code 会提示 "Restart Lean"，点不点都没关系。

下面要下载 Mathlib，注意让终端路径在你的项目文件夹下。如果你的网络情况好，那么在终端中运行

```bash
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
```

保存运行缓存会让每次编译节省一两个小时，但它当然也不是必须的：

```bash
lake exe cache get
```

否则（会相当艰难），参考[这个解决方案](https://zhuanlan.zhihu.com/p/680690436)。（不保证该参考方案的可靠性）

如果你看到终端中显示了类似如下的提示：

```bash
Decompressing 1234 file(s)
unpacked in 12345 ms
```

同时你的项目文件夹中出现了 `.lake\packages` 文件夹，那么证明你安装 Mathlib 成功了，此时 "Restart Lean" 即可使用。**注意：你要在项目所在的目录中运行 VS code，才能让 Lean 使用Mathlib。**

这里提供一个实例来测试你的安装：

```bash
import Mathlib.Data.Real.Basic
example (a b : ℝ) : a * b = b * a := by
  rw [mul_comm a b]
```

如果你的 Lean infoview 没有任何报错，并且光标放在文件最后一行时会提示 "No goals"，证明你的 Mathlib 已经正确安装了。

如果你想更新 Mathlib，在终端中运行

```bash
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe cache get
```

*关于 Mathlib 的更多内容请参考 [Mathlib Wiki](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)*

lake 的其他常用功能：

```bash
# 构建项目可执行文件
lake build
# 运行
lake exec hello # Hello, world!
# 清理构建文件
lake clean
# 更新依赖
lake update
# 运行 lakefile.lean 的脚本
lake run <script>
```

## lean

[lean](https://github.com/leanprover/lean4) 是语言本身的核心组件，通常不需要直接与 `lean` 交互。

这里介绍常见的两个操作：运行 Lean 脚本，以及验证 Lean 代码。

执行 Lean 脚本，入口为 `main` 函数：

```lean
-- hello.lean
def main : IO Unit := IO.println s!"Version: {Lean.versionString}"
```

在终端中运行：

```bash
elan default leanprover/lean4:v4.11.0-rc1
lean --run hello.lean
# Version: 4.11.0-rc1
elan run leanprover/lean4:v4.10.0 lean --run hello.lean
# Version: 4.10.0
```

验证 Lean 代码：

```lean
-- proof.lean
theorem my_first_theorem : 1 + 1 = 2 := by
  simp

theorem my_false_theorem : 1 + 1 = 1 := by
  simp

theorem my_syntax_error_themore 1 + 1 = 2 := by
  simp
```

在终端中运行：`lean proof.lean`，返回错误信息：

```bash
hello.lean:5:40: error: unsolved goals
⊢ False
hello.lean:8:31: error: unexpected token; expected ':'
```
