# LEAN 4 安装教程

Lean 是一个开源的定理证明助手和函数式编程语言，由微软研究院开发。它既可以用于形式化数学证明，也可以用于通用程序设计。

## Lean 4 工具链

Lean 4 的完整开发环境由以下核心组件构成：

1. [elan](https://github.com/leanprover/elan)：Lean 的版本管理工具，用于安装、管理和切换不同版本的 Lean，类似于 Rust 的 `rustup` 或 Node.js 的 `nvm`。
2. [lake](https://github.com/leanprover/lake)（Lean Make）：Lean 的包管理器和构建器，已集成到 Lean 4 核心仓库中。用于创建 Lean 项目，构建 Lean 包,编译 Lean 可执行文件等。
3. [lean](https://github.com/leanprover/lean4)：语言本身的核心组件，负责实际的代码编译和语言服务器协议（LSP）支持，用户不需要直接与 `lean` 交互。

此外，还有 Lean 的标准数学库 [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)，包含大量数学定义和定理，以及实用的证明工具和策略。

为了使用 Lean，需要先安装 [VS Code](https://code.visualstudio.com/) 和 Git，然后安装 elan。再通过 elan 安装各个 Lean4 版本以及 lake 包管理器，接下来就可以使用 lake 创建自己的 Lean 项目。工具链的用法示例参见 [Lean 工具链](tutorial/elan-lake.md) 一节或 [lake 文档](references/lake-doc.md)。

> 如果希望快速了解和使用 Lean，除了在本地安装，也可以直接访问 [live.lean-lang.org](https://live.lean-lang.org) 或 [live.leanprover.cn](https://live.leanprover.cn) 在线体验。

## Linux 安装 elan

如果没有网络问题，用一行命令安装：

```bash
wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile
```

脚本内容包括：检查并安装 VsCode，Lean 插件，并安装 elan。

如果访问 GitHub 存在问题，可以在安装 vscode 后，手动安装 elan。

具体地，在 GitHub [release 页面](https://github.com/leanprover/elan/releases)或者 [上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html) ，根据系统版本下载 elan。

比如下载 `linux-x86_64` 系统的 elan 工具：

```bash
# 如果网络不行就本地下载再上传
curl -L https://github.com/leanprover/elan/releases/download/v3.1.1/elan-x86_64-unknown-linux-gnu.tar.gz -o elan.tar.gz
tar xf elan.tar.gz
```

解压得到 `elan-init` 文件，赋予可执行权限并执行安装：

```bash
chmod +x elan-init
./elan-init -y --default-toolchain none
```

默认安装最新版本的 Lean，也可以通过参数指定版本，或略过具体 Lean 版本的安装。

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

## Windows 安装 elan

先在这里下载安装 [VS Code](https://code.visualstudio.com/download) 和 [Git](https://gitforwindows.org/)。

安装 VS Code 后，需要安装 lean4 扩展（extension）。如果网络环境顺畅，可以在 lean4 扩展的欢迎页选择 Get Start 来完成安装，或者创建空的 Lean 文件时扩展会弹出提示提醒你安装 elan 和 Lean 4。
除了这种方式，也可以在 cmd 或 powershell 中运行命令

```
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

如果遇到了 `"SSL connect error", "Timeout was reached","Failed to connect to github.com port 443"...` 等错误，就是说明你的网络环境不理想。如果这样可以通过[上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/elan/releases/download/mirror_clone_list.html)下载安装。下面演示在网络环境不理想的条件下的安装。

打开 cmd 或 Powershell，运行
```
curl -O --location https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/elan/releases/download/v4.0.0-rc1/elan-x86_64-pc-windows-msvc.zip
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


## Mac 安装 elan

和 ubuntu 系统类似，用脚本一键安装：

```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_macos.sh)" && source ~/.profile
```

或者在 GitHub [release 页面](https://github.com/leanprover/elan/releases) 或 [上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html) 手动下载运行安装程序。

此外，不鼓励使用 homebrew 安装 elan-init 包，这可能会落后于官方版本的更新。
