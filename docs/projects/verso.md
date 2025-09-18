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

**可扩展的文档结构** 所有 Verso 文档都可以包含一组通用元素，例如段落、强调文本或图像。 它们还共享部分和子部分的分层结构。 这些类型可按各个流派进行扩展。

阐述和渲染框架
Verso 提供了一种共享范例，用于将作者编写的文本转换为可读的输出。 不同的流派会产生不同的输出格式，但它们不需要重新发明轮子来解决交叉引用问题，并且它们可以从共享库中受益，以生成各种格式的输出。


## 流派

!!! note "def"
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