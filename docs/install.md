## LEAN4 安装教程 

Windows 可以参考 [子鱼的博客](https://subfish-zhou.github.io/theorem_proving_in_lean4_zh_CN/setup.html)，Mac 系统按[官网教程](https://leanprover-community.github.io/install/macos_details.html)使用 homebrew 来快速配置。当前教程针对 Ubuntu 系统，其他系统待实测后更新。

如果没有网络问题，用一行命令安装：

```bash
wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile
```

该命令执行了一个脚本：[install_debian.sh](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh)，主要安装了 VsCode，Lean 插件，以及 elan。

如果访问 GitHub 存在问题，可以在安装 VsCode 和 Lean 插件后，手动安装 elan。

### 安装 elan

elan 是一个用于管理 Lean 环境的工具。它的功能类似于 Rust 的 `rustup` 或 Node.js 的 `nvm`，用于安装、管理和切换不同版本的 Lean。

在 GitHub [release 页面](https://github.com/leanprover/elan/releases)根据系统版本下载新版 elan，比如 `linux-x86_64` 系统的 elan 安装器地址为：

```bash
https://github.com/leanprover/elan/releases/download/v3.1.1/elan-x86_64-unknown-linux-gnu.tar.gz
```

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

elan 的管理目录为 `$HOME/.elan`，内容形如

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

下载的 LEAN 版本在 `toolchains` 目录下，`settings.toml` 是 elan 的配置文件。

elan 的二进制文件中，`lake` 经常会用到。

### Lake 管理器

[lake](https://github.com/leanprover/lake) 全称 Lean Make，是 LEAN4 的包管理器，已合并到 LEAN4 仓库，作为源码的一部分。

下边用一个简单的例子演示 `lake` 的基本用法。

创建项目，目录为 `hello`

```bash
# 创建包
lake new hello
## 或者
mkdir hello && cd hello && lake init hello
# 构建包
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