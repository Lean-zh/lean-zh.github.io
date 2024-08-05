# LEAN 4 安装和配置教程 

Lean 4 工作环境由以下几部分组成：

1. [elan](https://github.com/leanprover/elan)：Lean 环境版本管理器。它的功能类似于 Rust 的 `rustup` 或 Node.js 的 `nvm`，用于安装、管理和切换不同版本的 Lean。
2. [lake](https://github.com/leanprover/lake)：Lean 4 的包管理器，全称 Lean Make，已合并到 Lean 4 仓库，作为源码的一部分。它用于创建 Lean 项目，构建 Lean 包，配置 Mathlib 和编译 Lean 可执行文件。
3. （非必须）[Mathlib](https://leanprover-community.github.io/mathlib4_docs/)：Lean 的数学库。

为了使用 Lean，你需要先安装 [VS Code](https://code.visualstudio.com/) 和 Git，然后安装 elan，elan 会自动帮你安装 Lean 4 stable 以及 lake 包管理器，接下来就可以使用 lake 创建自己的 Lean 项目。

## Windows 安装 elan

你可以在这里下载安装 [VS Code](https://code.visualstudio.com/download) 和 [Git](https://gitforwindows.org/)。

安装 VS Code 后，需要安装 lean4 扩展（extension）。如果你的网络环境顺畅，可以在 lean4 扩展的欢迎页选择 Get Start 来完成安装，或者创建空的 Lean 文件时扩展会弹出提示提醒你安装 elan 和 Lean 4。
此外你还可以在 cmd 或 powershell 中运行命令

```
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

如果你遇到了 `"SSL connect error", "Timeout was reached","Failed to connect to github.com port 443"...` 等错误，就是说明你的网络环境不理想。如果这样可以通过[上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html)安装。下面演示在网络环境不理想的条件下的安装。

打开 cmd 或 Powershell，运行
```
curl -O --location https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/elan/releases/download/v3.1.1/elan-x86_64-pc-windows-msvc.zip
unzip -o elan-x86_64-pc-windows-msvc.zip
.\elan-init.exe
```
会在终端中开始安装程序。单击回车在默认位置 `~\.elan` 安装。

安装完成后可以删除刚刚下载的临时文件：

```
del elan-init.exe
del elan-x86_64-pc-windows-msvc.zip
```

添加 elan 的安装地址到 PATH 环境变量（如果是默认安装，那么是 `%USERPROFILE%\.elan\bin`）。

重启终端输入 `elan --version`，如果能正常输出版本号，那么你已经装好了 elan 和 Lean 4 stable 版本。

## Linux 安装 elan

以下内容在 Ubuntu 22.04 系统上测试通过。

如果没有网络问题，用一行命令安装：

```bash
wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile
```

该命令执行了一个脚本：[install_debian.sh](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh)，主要安装了 VsCode，Lean 插件，以及 elan。

如果访问 GitHub 存在问题，可以在安装 VS Code 和 Lean 插件后，手动安装 elan。

在 GitHub [release 页面](https://github.com/leanprover/elan/releases)根据系统版本下载新版 elan，比如 `linux-x86_64` 系统的 elan 安装器地址为：

```bash
https://github.com/leanprover/elan/releases/download/v3.1.1/elan-x86_64-unknown-linux-gnu.tar.gz
```

或者在[上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html)下载，查询你自己系统对应的 elan 版本。

如果不确定系统架构，执行 `uname -s` 和 `uname -m` 查看：

```bash
❯ uname -s
Linux
❯ uname -m
x86_64
```

下载文件并解压：

```bash
# 如果网络不行就本地下载再上传
curl https://github.com/leanprover/elan/releases/download/v3.1.1/elan-x86_64-unknown-linux-gnu.tar.gz -o elan.tar.gz
tar xf elan.tar.gz
```

解压得到 `elan-init` 文件，赋予可执行权限并执行：

```bash
chmod +x elan-init
./elan-init
```

完成后，在 `.bashrc` 或 `.zshrc` 中修改环境变量：

```bash
export PATH="$HOME/.elan/bin:$PATH"
```

重启终端，检查 `elan` 版本和默认安装的 Lean 版本：
```bash
❯ elan -V
elan 3.1.1 (71ddc6633 2024-02-22)
❯ elan show
stable (default)
Lean (version 4.7.0, x86_64-unknown-linux-gnu, commit 6fce8f7d5cd1, Release)
```

## Mac 安装 elan

Mac 系统类似，用脚本一键安装：

```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_macos.sh)" && source ~/.profile
```

或者在 GitHub [release 页面](https://github.com/leanprover/elan/releases) 或 [上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html) 手动下载运行安装程序。

不鼓励使用 homebrew 提供的 elan-init 包，因为用户经常发现这落后于官方版本的更新。

## elan 常用功能

```
elan --version   # 输出版本号来测试安装是否成功
elan self update # 更新 elan
elan show        # 显示已安装的 Lean 版本

# 切换默认的 Lean 版本，例如 leanprover/lean4:v4.11.0-rc1 
# stable 是最新稳定版本，所有版本可见 https://github.com/leanprover/lean4/releases
elan default leanprover/lean4:stable 

# 也可设置，只在当前目录下使用的 Lean 版本
elan override set leanprover/lean4:stable
```

elan 在 Windows 下的管理目录为 `%USERPROFILE%\.elan\bin`，在Linux下的管理目录为 `$HOME/.elan`，内容形如

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

下载的 Lean 版本在 `toolchains` 目录下，`settings.toml` 是 elan 的配置文件。

elan 的二进制文件中，`lake` 经常会用到。

## 通过 Lake 创建 Lean 项目

对创建 Lean 项目的详细介绍参考[这个教程](https://www.leanprover.cn/fp-lean-zh/hello-world/starting-a-project.html)。此处演示最基本的用法。

在终端中运行（`your_project_name` 替换为你自己起的名字）

```
lake new your_project_name

# 或者手动创建一个新文件夹并在原地建立项目
mkdir your_folder_name && cd your_folder_name && lake init your_project_name
```

以创建一个名为 `your_project_name` 的空白新项目。这个项目的内容形如

```
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

```
├── .lake
   ├── lakefile.olean.trace
   └── ...
├── lake-manifest.json
```

如果你想在这个现有的工程中引用 Mathlib4，你需要在 `lakefile.lean` 文件尾中加入

```
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
```

保存文件后 VS code 会提示 "Restart Lean"，点不点都没关系。

下面要下载 Mathlib，注意让终端路径在你的项目文件夹下。如果你的网络情况好，那么在终端中运行
```
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
```

保存运行缓存会让每次编译节省一两个小时，但它当然也不是必须的：

```
lake exe cache get
```

否则（会相当艰难），参考[这个解决方案](https://zhuanlan.zhihu.com/p/680690436)。（不保证该参考方案的可靠性）

如果你看到终端中显示了类似如下的提示：

```
Decompressing 1234 file(s)
unpacked in 12345 ms
```

同时你的项目文件夹中出现了 `.lake\packages` 文件夹，那么证明你安装 Mathlib 成功了，此时 "Restart Lean" 即可使用。**注意：你要在项目所在的目录中运行 VS code，才能让 Lean 使用Mathlib。**

这里提供一个实例来测试你的安装：
```
import Mathlib.Data.Real.Basic
example (a b : ℝ) : a * b = b * a := by
  rw [mul_comm a b]
```
如果你的 Lean infoview 没有任何报错，并且光标放在文件最后一行时会提示 "No goals"，证明你的 Mathlib 已经正确安装了。

如果你想更新 Mathlib，在终端中运行

```
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

关于 Lake 的更多用法可参考[ lake 文档](references/lake-doc.md)。
