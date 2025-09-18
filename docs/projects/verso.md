# 使用 Verso 在 Lean 中编写文档

(WIP)

原文：[https://github.com/leanprover/verso](https://github.com/leanprover/verso)

作者：David Thrane Christiansen 译者：子鱼 subfishzhou@gmail.com

Verso 是用于撰写 Lean 文档的构建框架+具体工具。 你可以使用它来实现多种技术文档，包括但不限于：
- 参考手册
- 教程
- 网页
- 学术论文

它能够显示 Lean 代码、提供测试以避免文档年久失修、提供超链接等。它能够支持线性或链接错综的文档结构，提供交互，以及导出PDF。

Verso由以下组件构成：

**标记语言** 一种 Markdown 的简化变体，同时是 Lean 本身的另一种具体语法，因此 Verso 文档也是 Lean 文件。正如 TeX、Sphinx 和 Scribble 允许使用自己的编程语言扩展他们的语言一样，Verso 的标记语言是可扩展的。你可以在文件顶部定义一个 Lean 函数，随后在该文件的文本中使用它。

**可扩展的文档结构** 所有 Verso 文档都可以包含一组通用元素，例如段落、强调文本或图像。 它们还共享部分和子部分的分层结构。 这些类型可按各个体裁进行扩展。

阐述和渲染框架
Verso为作者提供的文本转换至可读输出建立了一套共享范式。不同体裁将生成不同的输出格式，但无需重复实现交叉引用解析功能，并能受益于共享库实现多格式输出。

【交叉引用管理】
Verso包含：用于表示文档化项目的通用范式，以及在HTML输出体裁间共享交叉引用数据库的格式。这使得链接与交叉引用能够自动插入和维护。

【Lean代码渲染】
Verso具备阐释和展示文档中Lean代码的功能。在HTML输出中，该代码呈现为可切换的证明状态、悬停提示和超链接形式。得益于精准的语法高亮（基于正则表达式的方法因Lean语法可扩展性而无法实现），代码显示更加清晰。

通过SubVerso辅助库，Verso文档可处理自Lean 4.0.0起任何版本的Lean代码。这使文档能够进行版本对比分析，并实现项目所用Lean版本与说明文档所用Lean版本的解耦升级。

【工具库】
Verso包含可供各体裁使用的工具库，提供诸如HTML内容全文检索等功能。这些库无需额外构建时依赖，避免了同时维护多个库生态系统带来的复杂性。

## 体裁

!!! def "" {data-label="def"}
    ```lean
    List.forM {u v w} {m : Type u → Type v} [Monad m]
    {a : Type w} (as : List a) (f : a → m PUnit) : m PUnit
    ```
    Applies the monadic action `f` to every element in the list, in order.

    参数说明：
    : **as** — 输入列表
    : **f**  — 作用在元素上的 monadic 函数

    参见：`List.mapM`（收集结果的变体）。

## Verso 标记语言

## 构建文档

## 扩展

## 输出格式

## 网页

## 手册和书

## 索引 依赖项 （请参考原文）