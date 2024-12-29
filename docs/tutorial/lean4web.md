# Lean4web 在线编辑器

Lean4web 是 Lean 4 的一个网页版工具，允许用户在浏览器中编写和执行 Lean 代码。

官方的 Lean playground 托管在 [live.lean-lang.org](https://live.lean-lang.org)，但仅支持最新分支和最新发行版。由于 Mathlib 不向后兼容，旧版本的 Lean 代码可能无法在最新的 Lean playground 上运行。因此本篇将介绍如何在本地部署 Lean4web，以及如何添加旧版环境。

## 项目链接规则

Lean4web 使用 URL 参数来控制不同的功能和加载不同的项目。例如：

- `code=`: 纯文本代码
- `codez=`: 使用 [LZ-string](https://www.npmjs.com/package/lz-string) 压缩的代码
- `url=`: 从指定的 URL 加载内容，优先级高于上面的 `code` 和 `codez`
- `project=`: 用于服务器评估代码的 Lean 项目名称，该名称必须是服务器配置中定义的项目之一

这些规则允许通过 URL 直接加载 Lean 代码，方便用户分享和交流。

## 项目部署和启动方式

以下步骤部署在 Ubuntu Server 22.10 上时测可行：

1. 安装 NPM:
   ```bash
   curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
   source ~/.bashrc
   nvm install 20
   ```

2. 克隆 Lean4web 仓库:
   ```bash
   sudo apt-get install git
   git clone --recurse-submodules https://github.com/leanprover-community/lean4web.git
   ```

3. 安装 Bubblewrap 以增强安全性:
   ```bash
   sudo apt-get install bubblewrap
   ```

4. 回到仓库目录，安装依赖并编译:
   ```bash
   cd lean4web
   npm install
   npm run build
   ```

5. 启动服务器:
   ```bash
   PORT=8080 npm run production
   ```

通过这些步骤，Lean4web 服务器将会在指定的端口启动服务。

## 添加旧版带 mathlib 的方式

要创建包含特定版本 mathlib 的 Lean 项目，可以使用 `create_project.sh` 脚本：

```bash
cd lean4web
cd Projects
bash create_project.sh <version>
```

用具体的版本号替换 `<version>`。这会在 `Projects/` 目录下创建一个新项目，并配置相应的 mathlib 依赖和工具链版本。

配置后，在 `client/src/config/config.json` 中添加类似字段：

```json
{ "folder": "v4.13.0",
  "name": "Lean 4.13.0",
}
```

重新运行 `npm run build` 和 `npm run production` 即可。

## CDN 优化

网站存在较大的静态资源，首次访问速度可能较慢，比如字体文件和 JS 文件：

![live-cdn](https://qiniu.wzhecnu.cn/FileBed/source/live-cdn.png)

后续考虑部署 CDN 服务，优化加载速度。