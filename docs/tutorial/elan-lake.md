# elan 及 Lake 用法示例

## elan 常用功能

[elan](https://github.com/leanprover/elan) 是 Lean 环境版本管理器，用于安装、管理和切换不同版本的 Lean。

```bash
elan --version   # 输出版本号来测试安装是否成功
elan self update # 更新 elan
elan show        # 显示已安装的 Lean 版本

# 切换默认的 Lean 版本，例如 leanprover/lean4:v4.11.0-rc1 
# stable 是最新稳定版本，所有版本可见 https://github.com/leanprover/lean4/releases
elan default leanprover/lean4:stable 

# 也可设置，只在当前目录下使用的 Lean 版本
elan override set leanprover/lean4:stable
```

elan 在 Windows 下的管理目录为 `%USERPROFILE%\.elan\bin`，在 Linux 下的管理目录为 `$HOME/.elan`，内容形如

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

## 通过 Lake 创建 Lean 项目

对创建 Lean 项目的详细介绍参考[这个教程](https://www.leanprover.cn/fp-lean-zh/hello-world/starting-a-project.html)。此处演示最基本的用法。

[lake](https://github.com/leanprover/lake) 全称 Lean Make，是 Lean 4 的包管理器，用于创建 Lean 项目，构建 Lean 包和编译 Lean 可执行文件。

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

其中 `lakefile.lean` 是当前项目的配置文件，`lean-toolchain` 是当前项目使用的 Lean 版本。其他文件的功能以及更多细节请参考[这个教程](https://www.leanprover.cn/fp-lean-zh/hello-world/starting-a-project.html)。

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

关于 Lake 的更多用法可参考 [lake 文档](../references/lake-doc.md)。
