
# Lean 中文文档

网站 https://www.leanprover.cn 的源代码。


## 文档修改指南

仓库开发者：

```bash
git clone git@github.com:Lean-zh/Lean-zh.github.io
cd Lean-zh.github.io
# 创建个人分支
git checkout -b mybranch
## 文档修改 
## git add/commit ##
git push -u origin mybranch
```

然后在 GitHub 上提交 Pull Request。

非仓库开发者，可以 fork 仓库，然后再 GitHub 上提交 Pull Request。

## 文档结构

| 目录 | 说明 |
| --- | --- |
| `docs/` | 部署网页的源码位置 |
| `docs/index.md` | 首页 |
| `docs/assets/` | 静态资源，如图片、样式等 |
| `mkdocs.yml` | 网站导航，配置等 |

## 本地预览

要在本地预览文档，请确保已安装 `mkdocs` 和 `mkdocs-material`：

```bash
pip install -r requirements.txt
mkdocs serve
```

## 贡献指南

我们欢迎任何形式的贡献！如果你有任何建议或发现了问题，请提交 Issue 或 Pull Request。

## 许可证

本项目采用 [MIT 许可证](LICENSE)。

