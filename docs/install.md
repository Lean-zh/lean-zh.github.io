# LEAN 4 安装教程 

Lean 4 工作环境由以下几部分组成：

1. [elan](https://github.com/leanprover/elan)：Lean 环境版本管理器。功能类似于 Rust 的 `rustup` 或 Node.js 的 `nvm`，用于安装、管理和切换不同版本的 Lean。
2. [lake](https://github.com/leanprover/lake)：Lean 4 的包管理器，全称 Lean Make，已合并为 Lean 4 仓库源码的一部分。它用于创建 Lean 项目，构建 Lean 包，配置 Mathlib 和编译 Lean 可执行文件。
3. （非必须）[Mathlib](https://leanprover-community.github.io/mathlib4_docs/)：Lean 的数学库。

为了使用 Lean，你需要先安装 [VS Code](https://code.visualstudio.com/) 和 Git，然后安装 elan，elan 会自动帮你安装 Lean 4 stable 以及 lake 包管理器，接下来就可以使用 lake 创建自己的 Lean 项目。

> 如果希望快速了解和使用 Lean，除了在本地安装，也可以通过 [live.lean-lang.org](https://live.lean-lang.org) 或 [live.leanprover.cn](https://live.leanprover.cn) 在线体验。

## Windows 安装 elan

先在这里下载安装 [VS Code](https://code.visualstudio.com/download) 和 [Git](https://gitforwindows.org/)。

安装 VS Code 后，需要安装 lean4 扩展（extension）。如果网络环境顺畅，可以在 lean4 扩展的欢迎页选择 Get Start 来完成安装，或者创建空的 Lean 文件时扩展会弹出提示提醒你安装 elan 和 Lean 4。
除了这种方式，也可以在 cmd 或 powershell 中运行命令

```
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

如果遇到了 `"SSL connect error", "Timeout was reached","Failed to connect to github.com port 443"...` 等错误，就是说明你的网络环境不理想。如果这样可以通过[上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html)安装。下面演示在网络环境不理想的条件下的安装。

打开 cmd 或 Powershell，运行
```
curl -O --location https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/elan/releases/download/eager-resolution-v5/elan-x86_64-pc-windows-msvc.zip
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

通过执行脚本 [install_debian.sh](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh) 检查并安装 VsCode，Lean 插件以及 elan。

如果访问 GitHub 存在问题，可以手动完成这些过程。具体地，前往 GitHub [release 页面](https://github.com/leanprover/elan/releases)或者 [上交镜像源](https://s3.jcloud.sjtu.edu.cn/899a892efef34b1b944a19981040f55b-oss01/elan/mirror_clone_list.html) ，根据系统版本下载新版 elan。

比如下载并解压 `linux-x86_64` 系统的 elan 工具：

```bash
# 如果网络不行就本地下载再上传
curl -L https://github.com/leanprover/elan/releases/download/v3.1.1/elan-x86_64-unknown-linux-gnu.tar.gz -o elan.tar.gz
tar xf elan.tar.gz
```

解压得到 `elan-init` 文件，赋予可执行权限并执行安装：

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
