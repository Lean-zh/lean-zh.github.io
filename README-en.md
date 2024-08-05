# Lean-zh Documentation

Source code for the website https://www.leanprover.cn.

## Documentation Modification Guide

For repository members and organization members:

```bash
git clone git@github.com:Lean-zh/Lean-zh.github.io
cd Lean-zh.github.io
# Create a personal branch
git checkout -b mybranch
## Document modification
## git add/commit ##
git push -u origin mybranch
```

Then submit a Pull Request on GitHub.

For non-repository developers, you can fork the repository and then submit a Pull Request on GitHub.

## Document Structure

| Directory | Description |
| --- | --- |
| `docs/` | Source code location for the deployed webpage |
| `docs/index.md` | Homepage |
| `docs/assets/` | Static resources, such as images, styles, etc. |
| `mkdocs.yml` | Website navigation, configuration, etc. |

## Local Preview

To preview the documentation locally, ensure you have `mkdocs` and `mkdocs-material` installed:

```bash
pip install -r requirements.txt
mkdocs serve
```

## Contribution Guide

We welcome any form of contribution! If you have any suggestions or find any issues, please submit an Issue or Pull Request.

## License

This project is licensed under the [MIT License](LICENSE).