# 使用 Verso 在 Lean 中编写文档

原文：[https://github.com/leanprover/verso](https://github.com/leanprover/verso)

作者：David Thrane Christiansen 译者：子鱼和他的Cursor subfishzhou@gmail.com

Verso 是用于撰写 Lean 文档的构建框架+具体工具。 你可以使用它来实现多种技术文档，包括但不限于：

- 参考手册
- 教程
- 网页
- 学术论文

它能够显示 Lean 代码、提供测试以避免文档年久失修、提供超链接等。它能够支持线性或交叉引用错综的文档结构，提供交互，以及导出PDF。

Verso由以下组件构成：

**[标记语言](#verso-markup)** 一种 Markdown 的简化变体，同时是 Lean 本身的另一种具体语法，因此 Verso 文档也是 Lean 文件。正如 TeX、Sphinx 和 Scribble 允许使用自己的编程语言扩展他们的语言一样，Verso 的标记语言是可扩展的。你可以在文件顶部定义一个 Lean 函数，随后在该文件的文本中使用它。

**可扩展的文档结构** 所有 Verso 文档都可以包含一组通用元素，例如章节层级，例如段落、粗体字或图像。这些类型可按各个体裁进行扩展。

**阐释（Elaboration）和渲染框架** Verso为作者提供的文本转换至可读输出建立了一套共享范式。不同体裁将生成不同的输出格式，但无需重复实现交叉引用解析功能，并能受益于共享库实现多格式输出。

**交叉引用管理** Verso包含：用于表示文档化项目的通用范式，以及在HTML输出体裁间共享交叉引用数据库的格式。这使得链接与交叉引用能够自动插入和维护。

**Lean代码渲染** Verso具备阐释和展示文档中Lean代码的功能。在HTML输出中，该代码呈现为可切换的证明状态、悬停提示和超链接形式。得益于精准的语法高亮（基于正则表达式的方法因Lean语法可扩展性而无法实现），代码显示更加清晰。

通过 [SubVerso](https://github.com/leanprover/subverso) 辅助库，Verso文档可处理自Lean 4.0.0起任何版本的Lean代码。这使文档能够进行版本对比分析，并实现项目所用Lean版本与说明文档所用Lean版本的解耦升级。

**工具库** Verso包含可供各体裁使用的工具库，提供诸如HTML内容全文检索等功能。这些库无需额外构建时依赖，避免了同时维护多个库生态系统带来的复杂性。

## 1 体裁

没有什么系统可以完美支持所有文档体裁。软件手册作者的需求与教科书、论文、博主或者诗人的需求不同。因此 Verso 支持多种体裁，提供功能：

- 文档结构的全局视图，无论是带有小节的文档、相互链接的文档集合（如网站）还是单个文本文件
- 跨越整个文档的状态表示，例如对图表的交叉引用、索引条目和命名定理
- 文档结构的补充 —— 例如，博客体裁支持包含原始 HTML，而手册体裁支持将多个顶层区块组合成一个逻辑段落
- 处理交叉引用和将文档渲染为一个或多个输出格式的程序

所有体裁使用相同的标记语法，并且可以共享不依赖于不兼容结构扩展的标记语言扩展。混合不兼容的功能会导致普通的 Lean 类型错误。

## 2 Verso 标记语言 {#verso-markup}

Lean 的文档标记语言与 Markdown 密切相关，但并非完全相同。

### 2.1 设计原则

* **语法错误** 应该尽早失败（fail fast），而不是产生意外的输出或依赖复杂规则。
* **减少前瞻**  解析应尽可能局部地成功或失败。
* **可扩展性** 应该有专门的机制来组合式地添加新内容，而不是依赖一堆临时性的文本子格式。
* **默认支持 Unicode** Lean 用户已经习惯直接输入 Unicode，并且有良好的工具支持，因此没有必要支持其他替代文本语法来输入键盘上没有的字符（例如破折号或印刷引号）。
* **Markdown 兼容性** 在不违反上述原则的前提下，用户能够从已有的肌肉记忆和熟悉度中获益。

### 2.2 语法

与 Markdown 类似，Lean 的标记语法有三大主要类别：

* **文档结构** 标题、脚注定义和命名链接为文档提供更丰富的结构。它们不能嵌套在区块内。
* **区块元素** 书面文本的主要组织方式，包括段落、列表和引用。部分区块可以嵌套：例如，列表可以包含其他列表。
* **内联元素** 书面文本的普通内容，如正文、加粗或强调文本，以及超链接。

#### 2.2.1 文档结构

文档被组织为若干部分。一个部分是文档内容的逻辑划分，例如章节、小节或卷。部分可以附带元数据，例如作者、发布日期、用于交叉引用的内部标识符或期望的 URL；具体的元数据由文档体裁决定。

一个部分包含一系列块，接着是一系列子部分，两者都可以为空。

一个部分由标题引入。标题由行首一个或多个井号（`#`）加上一系列内联元素组成。井号的数量表示标题的层级，井号越多表示层级越低。低层级标题引入前一标题的子部分，而层级不低于前一标题的标题会结束该部分。换句话说，标题层级为文档引入一棵树形结构。

标题必须正确嵌套：文档中的第一个标题必须恰好有一个井号，之后的标题最多只能比前一个标题多一个井号。这是语法上的要求：无论 Verso 文件包含的是整本书、一章，还是仅一个小节，其最外层标题必须以单个井号引入。标题表示的是文档的逻辑层级结构，而不是文档渲染为 HTML 等输出格式时所选择的标题样式。

标题后可以跟随一个元数据块来为其附加元数据。元数据块以 `%%%` 开始和结束，内部可以包含任何在 Lean 结构初始化器中可接受的语法。


!!! blue "标题"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    # 顶级标题
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <h1>顶级标题</h1>
    ```
    </div>
    </div>

!!! blue "文本"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    a b c
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>a b c</p>
    ```
    </div>
    </div>

#### 2.2.2 块语法

段落是未修饰的：任何不是另一个块的内联序列都是段落。 段落一直持续到空白行（即仅包含空格的行）或另一个块开头：

!!! blue "段落"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    这是一段话。
    在下一行续写这一段。

    这是新的一段。
    * 这一段以列表结尾。
    * 在 Markdown 和 SGML 中, 列表不是段的一部分。
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
        这是一段话。
        在下一行续写这一段。
    </p>

    <p> 这是新的一段。 </p>

    <ul>
        <li>
            <p>
                * 这一段以列表结尾。
            </p>
        </li>
        <li>
            <p>
                在 Markdown 和 SGML 中, 列表不是段的一部分。
            </p>
        </li>
    </ul>
    ```
    </div>
    </div>

##### 2.2.2.1. 列表

有三种类型的列表：

**无序列表**
项的顺序不重要。对应于 HTML 中的 `<ul>` 或 LaTeX 中的 `\begin{itemize}`。

**有序列表**
项的顺序很重要。对应于 HTML 中的 `<ol>` 或 LaTeX 中的 `\begin{enumerate}`。

**描述列表**
描述列表将术语与更多信息相关联。对应于 HTML 中的 `<dl>` 或 LaTeX 中的 `\begin{description}`

以零个或多个空格开头，后跟 `*`、`-` 或 `+` 表示列表项的行。此些字符称为列表项指示符。相同的指示符加上相同的缩进表明它们是同一列表层级，更多的缩进表示某项下的子项；项可能包含多个块，甚至其他列表。

!!! blue "无序列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    * 含两个项目的列表
    * 都从第0列开头
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ul>
        <li>
            <p> 含两个项目的列表 </p>
        </li>
        <li>
            <p>
            都从第0列开头
            </p>
        </li>
    </ul>
    ```
    </div>
    </div>

!!! blue "列表指示符"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    * 两个列表
    + 带有不同的指示符
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ul>
        <li> <p> 两个列表 </p> </li>
    </ul>
    <ul>
        <li>
            <p>
                带有不同的指示符
            </p>
        </li>
    </ul>
    ```
    </div>
    </div>

!!! blue "列表对缩进敏感"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    * 一个含一个项目的列表
    * 另一个列表，因为用了不同的指示符
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ul>
        <li>
            <p>
                一个含一个项目的列表
            </p>
        </li>
    </ul>

    <ul>
        <li>
            <p>
                另一个列表，因为用了不同的指示符
            </p>
        </li>
    </ul>
    ```
    </div>
    </div>

!!! blue "子列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    * 单项列表
      也涵盖这一段

      * 这是子列表

      也涵盖这一段
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ul>
        <li>
            <p>
                单项列表   也涵盖这一段
            </p><ul>
            <li>
                <p>
                这是子列表
                </p>
            </li>
            </ul><p>
                也涵盖这一段
            </p>
        </li>
    </ul>
    ```
    </div>
    </div>

有序列表项由"零个或多个空格 + 一串数字 + 指示符（`.` 或 `)`）"起始。与无序列表相同，有序列表也对缩进与指示符敏感：相同缩进与相同指示符归为同一列表层级。

!!! blue "有序列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    1. 首先写一个数字
    2. 然后写指示符（`.` 或 `)`）
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ol>
        <li><p> 首先写一个数字 </p></li>
        <li>
            <p>
                然后写指示符
                ("." 或 ")")
            </p>
        </li>
    </ol>
    ```
    </div>
    </div>

!!! blue "有序列表与指示符"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    1. 两个列表
    2) 它们使用不同的指示符
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ol>
        <li> <p> 两个列表 </p> </li>
    </ol>

    <ol>
        <li>
            <p>
                它们使用不同的指示符
            </p>
        </li>
    </ol>
    ```
    </div>
    </div>

描述列表由若干"描述项"组成，具有相同缩进。一个描述项的第一行以"零个或多个空格 + 冒号 `:` + 一串行内元素"构成，随后必须有一行空行，然后跟随一个或多个缩进严格大于冒号位置的块。

!!! blue "描述列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    : 项目 1

      项目 1 的说明

    : 项目 2

      项目 2 的说明
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <dl>
      <dt>  项目 1 </dt>
      <dd><p> 项目 1 的说明 </p></dd>

      <dt>  项目 2 </dt>
      <dd><p> 项目 2 的说明 </p></dd>
    </dl>
    ```
    </div>
    </div>

##### 2.2.2.2. 引用（Quotes）

引用块表示一组块是由作者以外的人说的。其语法为：一行以"零个或多个空格 + 大于号 `>`"起始，随后必须跟随缩进严格大于该 `>` 的一个或多个块，这些块共同组成引用内容。

!!! blue "引用"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    常言道：
    > 引用超级棒。

      这一段也是引用部分。

     这里也是。

    这里就不是了。
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p> 常言道： </p>

    <blockquote>
      <p> 引用超级棒。 </p>
      <p>
        这一段也是引用部分。
      </p>
      <p> 这里也是。 </p>
    </blockquote>

    <p> 这里就不是了。 </p>
    ```
    </div>
    </div>

##### 2.2.2.3. 代码块（Code Blocks）

代码块以"行首三个或更多反引号"开始（之前可有空格），称为"围栏（fence）"。可在反引号后给出名称与参数。代码块持续到"同缩进、且仅包含相同数量反引号"的行。块内每行的实际字符串为移除围栏缩进后的结果。代码块不得包含长度不小于围栏的反引号序列；如需更多反引号，应增大围栏长度。

!!! blue "代码块"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ````markdown
    ```
    这是一个代码块
    包含两行内容
    ```
    ````
    </div>
    <div markdown>
    **结果**
    ```html
    <codeblock>
      1|这是一个代码块⏎
      2|包含两行内容⏎
    </codeblock>
    ```
    </div>
    </div>

!!! blue "作为扩展的代码块"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ````markdown
    ```lean
    -- 该代码块的名称为
    -- `lean`。调用时
    -- 未传入参数。
    def x := 5
    ```
    ````
    </div>
    <div markdown>
    **结果**
    ```html
    <lean>
      1|-- 该代码块的名称为⏎
      2|-- `lean`。调用时⏎
      3|-- 未传入参数。⏎
      4|def x := 5⏎
    </lean>
    ```
    </div>
    </div>

!!! blue "缩进的代码块"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
      ```lean
      -- 这是一个缩进的代码块
      -- 表示去除缩进后的
      -- 字符串
      def x := 5
      ```
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <lean>
      1|-- 这是一个缩进的代码块⏎
      2|-- 表示去除缩进后的⏎
      3|-- 字符串⏎
      4|def x := 5⏎
    </lean>
    ```
    </div>
    </div>

!!! blue "代码块与命名参数"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ````markdown
    ```lean (error := true)
    -- 该代码块的名称为
    -- `lean`，调用时传入了
    -- 命名参数 `error`
    -- 并将其设为 `true`。
    def x : String := 5
    ```
    ````
    </div>
    <div markdown>
    **结果**
    ```html
    <lean error="true">
      1|-- 该代码块的名称为⏎
      2|-- `lean`，调用时传入了⏎
      3|-- 命名参数 `error`⏎
      4|-- 并将其设为 `true`。⏎
      5|def x : String := 5⏎
    </lean>
    ```
    </div>
    </div>

当代码块带名称时，会在当前 Lean 命名空间解析该名称，并据此选择扩展实现（详见"扩展"一章）。

##### 2.2.2.4. 指令（Directives）

指令是一类无内建语义、由扩展解释的块，类似 LaTeX 的自定义环境或 HTML 的 `<div>`。以"行首三个或更多冒号 + 名称与参数"开始，在"同缩进、且仅包含相同数量冒号"的行结束。内容可包含任意数量的块，这些块的缩进至少与冒号对齐。嵌套指令的冒号数量必须严格少于其外层。

[扩展](#extension)一节更详细地描述了指令的处理。

这是空指令：

!!! blue "指令"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    :::nothing
    :::
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <nothing> </nothing>
    ```
    </div>
    </div>

!!! blue "嵌套指令"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    ::::outer
    :::inner
    你好
    :::
    这是一段
    ::::
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <outer>
      <inner> <p> 你好 </p> </inner>
      <p> 这是一段 </p>
    </outer>
    ```
    </div>
    </div>

##### 2.2.2.5. 命令（Commands）

仅由"花括号包裹的名称与零个或多个参数"构成的一行即为命令。名称将用于选择命令的实现，并在阐释阶段调用（详见[扩展](#extension)一章）。

!!! blue "命令"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    {include 0 MyChapter}
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <include 0 MyChapter/>
    ```
    </div>
    </div>

#### 2.2.3 行内语法（Inline Syntax）

强调（emphasis）使用下划线 `_`：

!!! blue "强调"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    一些 _强调_ 文本
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      一些
      <emph> 强调 </emph> 文本
    </p>
    ```
    </div>
    </div>

外层使用更多下划线可形成"嵌套强调"：

!!! blue "嵌套强调"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    Here's some __emphasized text
    with _extra_ emphasis__ inside
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      Here's some
      <emph>
        emphasized text with
        <emph> extra </emph> emphasis
      </emph>
      inside
    </p>
    ```
    </div>
    </div>

强强调（粗体，bold）使用星号 `*`：

!!! blue "加粗"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    一些 *粗体* 文本
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      一些 <bold>粗体</bold> 文本
    </p>
    ```
    </div>
    </div>

超链接由方括号包裹的链接文本，后接圆括号中的目标：

!!! blue "链接"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    [Lean](https://lean-lang.org)
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      <a href="https://lean-lang.org">Lean</a>
    </p>
    ```
    </div>
    </div>

链接目标也可以命名：

!!! blue "命名链接目标"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    The [Lean website][lean]

    [lean]: https://lean-lang.org
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      The <a href="(value of «lean»)">Lean website</a>
    </p>

    where «lean» := https://lean-lang.org
    ```
    </div>
    </div>

行内代码使用反引号。开启与关闭使用相同个数的反引号，且内容不得包含长度不小于分隔符的反引号序列：

!!! blue "行内代码"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    The definition of `main`
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p> The definition of <code>"main"</code> </p>
    ```
    </div>
    </div>

特殊规则：若行内代码首尾均有一个空格，则表示去掉一前一后的空格后得到的字符串，可用于表示以反引号开头/结尾的值：

!!! blue "代码中的空格"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    `` `quotedName ``
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p> <code>"`quotedName"</code> </p>
    ```
    </div>
    </div>

或带空格：

!!! blue "多个空格的代码"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    ``  one space  ``
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p> <code>" one space "</code> </p>
    ```
    </div>
    </div>

图片需要同时提供替代文本与图片地址，也支持命名地址：

!!! blue "图片"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    ![Alt text](image.png)
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      <img src="image.png" alt="Alt text"/>
    </p>
    ```
    </div>
    </div>

!!! blue "命名图片地址"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    ![Alternative text][image]

    [image]: image.png
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      <img src="value of «image»" alt="Alternative text"/>
    </p>

    where «image» := image.png
    ```
    </div>
    </div>

数学：单个或双个美元符包裹的 TeX 代码。`$...$` 为行内，`$$...$$` 为陈列（行间）模式：

!!! blue "数学"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    $`\sum_{i=0}^{10} i`$
    $$`\sum_{i=0}^{10} i`$$
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p> <span class="math inline">\sum_{i=0}^{10} i</span> </p>
    <p> <span class="math display">\sum_{i=0}^{10} i</span> </p>
    ```
    </div>
    </div>

角色（role）为后续行内赋予特殊语义。可用于代码阐释、技术术语定义/使用、旁注等。语法：一行内用花括号给出名称与参数，后面紧跟一个"自我定界"的行内元素，或用方括号包裹的若干行内元素。

!!! blue "带显式范围的角色"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    {ref "chapter-tag"}[the chapter on
    $`\frac{1}{2}`-powered syntax]
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      <ref "chapter-tag">
        the chapter on
        <math contents="\\frac{1}{2}"/>
        -powered syntax
      </ref>
    </p>
    ```
    </div>
    </div>

下例采用单个内联代码元素，不需要方括号：

!!! blue "单参数角色"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    {lean}`2 + f 4`
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      <lean>
        <code>"2 + f 4"</code>
      </lean>
    </p>
    ```
    </div>
    </div>

### 2.3 与 Markdown 的差异

Markdown用户的快速备忘录。

#### 2.3.1 语法错误
Markdown 允许一组优先级规则来解释不匹配的分隔符（例如 `what _is *bold_ or emph*?`），在 Lean 标记中这类情况是语法错误；同样，未闭合的分隔符（如 `*` 或 `_`）在 Markdown 中当作普通字符，而 Lean 标记中要求显式转义。长文技术写作更倾向于尽早发现此类错误。

#### 2.3.2 减少前瞻
在 Markdown 中，`[this][here]` 是否为链接取决于文档中是否定义了 `here`；在 Lean 标记中它总是链接，若缺失目标则报错。

#### 2.3.3 标题嵌套
Lean 标记认为每个文档都有标题，且强制使用 `#` 作为最外层标题、`##` 为下一层，依此类推。这样单文件既可代表节、章乃至整本书，而无需维护全局层级映射。

#### 2.3.4 体裁特定扩展
Markdown 没有标准方式表达特定工具/体裁的概念；Lean 标记提供标准语法以组合式扩展。

#### 2.3.5 移除少用特性
为减少意外并提升可预测性，Verso 移除了下列在实践中较少使用、或对多后端输出不友好的特性：

- 取消"[紧凑（tight）](https://spec.commonmark.org/0.31.2/#tight)/[宽松（loose）列表](https://spec.commonmark.org/0.31.2/#loose)"的区分；
- 使用[四个空格缩进创建代码块](https://spec.commonmark.org/0.31.2/#indented-code-blocks)（Verso 仅支持围栏代码块）；
- [Setext 风格标题](https://spec.commonmark.org/0.31.2/#setext-headings)（以下划线表示的标题），统一使用 `#` 形式；
- [硬换行语法](https://spec.commonmark.org/0.31.2/#hard-line-breaks)；
- [HTML 实体与字符引用](https://spec.commonmark.org/0.31.2/#entity-and-numeric-character-references)。

此外，一些特性对非 HTML 后端并不合适，可由具体体裁通过"代码块或指令"实现，因此也被移除：

- [HTML 区块](https://spec.commonmark.org/0.31.2/#html-blocks)、[原始 HTML](https://spec.commonmark.org/0.31.2/#raw-html)、[主题分隔线](https://spec.commonmark.org/0.31.2/#thematic-breaks)。

最后，还有少数作者偶尔使用、但不值得引入的复杂度，例如：[自动链接（autolinks）](https://spec.commonmark.org/0.31.2/#autolinks)。

## 3 构建文档

本节简述 Verso 文档从作者到读者的标准流程（不同体裁在细节上会作定制）：

1. 使用 [Verso 标记语言](#verso-markup)编写文本，解析为 Lean 的 `Syntax`。
2. 进行阐释（elaboration），转为对应体裁的 Lean 数据结构。
3. 将生成的 Lean 代码编译为可执行程序。
4. 运行该程序，执行"遍历（traversal）"步骤，解析交叉引用并计算全局元数据。
5. 生成目标输出（HTML/TeX 等）。

### 3.1 阐释（Elaboration）
阐释把[标记语言](#verso-markup)转换为内部归纳类型，并在遇到[扩展点](#elab-extension)时调用注册的实现。其他语法被转换为 Verso 数据的适当构造函数。

所有文档都以"体裁（genre）"为参数。

!!! green "structure"
    ```lean
    Verso.Doc.Genre : Type 1
    ```
    <hr>
    体裁主要由其对 Verso 框架的扩展来定义，在此类型中提供。此外，每种体裁会提供一个 `main` 函数负责遍历步骤的函数，并用于生成输出。

    **构造器**

    `Verso.Doc.Genre.mk`

    **域**

    `PartMetadata : Type`

    &nbsp;&nbsp;&nbsp;&nbsp;与每个 `Part` 联系的元数据（如作者，发表时间，交叉引用指示符）。

    `Block : Type`

    &nbsp;&nbsp;&nbsp;&nbsp;以体裁编写的文档的其他块级值。

    `Inline : Type`
    
    &nbsp;&nbsp;&nbsp;&nbsp;以该体裁编写的文档的其他内联级值。

    `TraverseContext : Type`
    
    &nbsp;&nbsp;&nbsp;&nbsp;体裁的遍历步骤中使用的阅读器样式数据。体裁中 `TraversePart` 和 `TraverseBlock` 的实例分别指定在遍历 Part 和 Block 时如何更新它。

    `TraverseState : Type`              
    
    &nbsp;&nbsp;&nbsp;&nbsp;该流派遍历步骤中使用的可变状态。

每个文档由一个 `Part` 组成，其标题即为整个文档的标题：

!!! green "def"
    ```lean
    Verso.Doc.Part (genre : Doc.Genre) : Type
    ```
    <hr>
    -- 文档的逻辑部分

`Part` 包含 `Block`：

!!! green "def"
    ```lean
    Verso.Doc.Block (genre : Doc.Genre) : Type
    ```
    <hr>
    -- 文档中的块级内容

`Block` 包含 `Inline`：

!!! green "def"
    ```lean
    Verso.Doc.Inline (genre : Doc.Genre) : Type
    ```
    <hr>
    -- 文本流中的行内内容

`Part` 的 `metadata` 字段通常从作者编写的元数据块获取值，但在遍历过程中可能被分配更多信息。`Block.other` 和 `Inline.other` 构造器通常来自阐释[扩展点](#elab-extension)的结果。

### 3.2 编译（Compilation）
阐释之后，文档被编译为可执行程序。各体裁提供 `main` 入口来完成遍历与输出；网站等非线性体裁会额外提供布局/配置方式。常见参数包括输出格式以及渲染自定义项。

### 3.3 遍历（Traversal） {#traversal}
Verso 文档是 Lean 值，遵循 Lean 程序的一般结构。特别地，Lean 不支持循环 import。但是技术写作中常见"循环引用"（例如两个小节相互引用、按引用数据库生成的参考文献等）。

"遍历"阶段发生在运行时、在生成输出之前。在遍历期间，文档会被从头到尾反复地遍历，并将元数据累积到一张表中。文档在遍历过程中也可以被改写；这允许，例如，将小节的标题插入到交叉引用处。遍历会重复，直到得到的文档与元数据表不再发生修改；如果连续执行了设定次数的遍历并且每次都产生了修改，则遍历失败。

Verso 为 `Part`、`Block` 与 `Inline` 提供了通用的遍历机制，体裁可以加以复用。
`Genre.TraverseState` 在遍历过程中保存体裁特定的累计信息，`Genre.TraverseContext` 提供跟踪周围文档上下文的手段。
要使用这一框架，各体裁应当定义 `Traverse` 的实例，它指定该体裁自定义元素的遍历方式。
此外，`TraversePart` 与 `TraverseBlock` 的实例指定了遍历如何跟踪文档中的当前位置。

!!! green "type class"
    ```lean
    Verso.Doc.Traverse (g : Doc.Genre) (m : outParam (Type → Type)) : Type 1
    ```
    <hr>
    ```
    特定体裁遍历。
    遍历步骤会反复应用"体裁特定的带状态的计算"，直到对"状态与文档"都到达一个固定点为止；遍历可以更新状态，也可以对文档进行重写。

    方法 `part`、`block` 与 `inline` 提供在遍历进入给定 AST 层级之前要执行的效果；
    其中 `part` 允许更新该 `Part` 的元数据。

    `genrePart` 在 `part` 之后执行，它允许基于体裁特定的元数据对整个 `Part` 做体裁特定的改写 —— 典型用法是构建目录或永久链接，但原则上它可以任意重写该 `Part`。`inPart` 用于局部地改造体裁的遍历上下文，其方式类似 `withReader`；它可以用来跟踪例如"当前在目录中的位置"。

    当遍历遇到 `Block.other` 与 `Inline.other`（体裁自定义值）时，会分别调用 `genreBlock` 与 `genreInline`；它们可以重写对应节点，或仅产生状态效果。

    **实例构造器**

    `Verso.Doc.Traverse.mk`

    **方法**
    `part   : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] → Doc.Part g   → m (Option g.PartMetadata)`

    &nbsp;&nbsp;&nbsp;&nbsp;在遍历 `Part` 前执行的效果。

    `block  : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] → Doc.Block g  → m Unit`

    &nbsp;&nbsp;&nbsp;&nbsp;在遍历 `Block` 前执行的效果。

    `inline : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] → Doc.Inline g → m Unit`

    &nbsp;&nbsp;&nbsp;&nbsp;在遍历 `Inline` 前执行的效果。

    `genrePart   : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] → g.PartMetadata → Doc.Part g → m (Option (Doc.Part g))`

    &nbsp;&nbsp;&nbsp;&nbsp;在Part具有元数据的情况下，对Part执行的操作。它允许根据特定体裁的元数据对整个部分进行特定体裁的重写。这通常用于构建目录或永久链接，但原则上可以任意重写Part。如果它返回none，则不执行重写。

    `genreBlock  : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] → g.Block → Array (Doc.Block g) → m (Option (Doc.Block g))`

    &nbsp;&nbsp;&nbsp;&nbsp;遍历特定类型的块值。如果返回空值，则不执行重写操作。

    `genreInline : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] → g.Inline → Array (Doc.Inline g) → m (Option (Doc.Inline g))`

    &nbsp;&nbsp;&nbsp;&nbsp;遍历特定类型的行内值。如果返回空值，则不执行重写操作。


!!! green "type class"
    ```lean
    Verso.Doc.TraversePart (g : Doc.Genre) : Type
    ```
    <hr>
    ```
    指定在遍历某个给定 Part 的内容时，如何修改遍历上下文。
    它在 `part` 与 `genrePart`（若适用）改写文本之后被应用；
    该规则同样用于 HTML 生成阶段。

    **实例构造器**

    `Verso.Doc.TraversePart.mk`

    **方法**
    `inPart : Doc.Part g → g.TraverseContext → g.TraverseContext`

    &nbsp;&nbsp;&nbsp;&nbsp;在进入给定 `Part` 的内容时，如何更新遍历上下文。
    ```

!!! green "type class"
    ```lean
    Verso.Doc.TraverseBlock (g : Doc.Genre) : Type
    ```
    <hr>
    ```
    指定在遍历某个给定 Block 的内容时，如何修改遍历上下文。
    该规则同样用于 HTML 生成阶段。

    **实例构造器**

    `Verso.Doc.TraverseBlock.mk`

    **方法**
    `inBlock : Doc.Block g → g.TraverseContext → g.TraverseContext`

    &nbsp;&nbsp;&nbsp;&nbsp;在进入给定 `Block` 的内容时，如何更新遍历上下文。
    ```

### 3.4 生成输出（Output Generation）

完成遍历后，文档的可读版本就会生成。该版本可以是任何格式；每种体裁都定义了其支持的格式。

此外，生成 HTML 格式的文档可能会生成其交叉引用数据库的序列化版本。这一功能可用于自动维护实现版本间交叉引用的链接：如果内容发生变动，只需重新构建链接文档即可修复链接。

## 4 扩展 {#extension}

Verso 的扩展机制允许体裁组合出新的块/行内元素、为阐释与遍历插入逻辑，以及为不同输出后端提供渲染实现。扩展由普通 Lean 代码定义，具备良好的类型约束与可组合性。

- 可定义自有数据（例如手册体裁的块、行内元素的数据结构），并注册阐释器将标记语法映射到这些数据。
- 在遍历（Traversal）中，扩展可读取/更新体裁状态，建立交叉引用、生成目录、注入永久链接等。
- 为 HTML/TeX 输出实现渲染器，并按需声明额外的静态资源（脚本/CSS/许可证信息）。

Verso 的标记语言提供四类扩展点：

- 角色（Roles）
- 指令（Directives）
- 代码块（Code blocks）
- 命令（Commands）

这些扩展点可用于为 Verso 增添新的文档功能。

### 4.1 语法

四类扩展点共享一套调用语法：按名称调用，并带有一串参数。参数既可定位（positional），也可命名（by name）；其取值可以是标识符、字符串字面量或数字。布尔开关可用 `-` 或 `+` 前缀传递，分别表示 `false` 或 `true`。

下例中，指令 `syntax` 以定位参数 `term` 与命名参数 `title := "Example"` 调用；标志 `check` 设为 `false`。其内容包含一段文字与一个名为 `grammar` 的代码块（调用时未带参数）：

````text
:::syntax term (title := example) -check
grammar示例:
```grammar
term ::= term "<+-+>" term
```
:::
````

形式化地说，扩展点的调用应满足如下语法：

```text
CALL := IDENT ARG*
ARG := VAL | "(" IDENT ":=" VAL ")" | "+" IDENT | "-" IDENT
VAL := IDENT | STRING | NUM
```

`CALL` 可出现在代码块的开围栏之后；它在指令的冒号之后、角色的花括号中，以及命令中都是必需的。

### 4.2 阐释扩展 {#elab-extension}

每一种扩展各自维护一张"名称 → 扩展器（expander）"的表。扩展器将 Verso 的语法转换为 Lean 项（terms）。当阐释器遇到代码块、角色、指令或命令的调用时，会解析名称并在表中查找扩展器；按顺序尝试扩展器，直到某个扩展器抛错或成功为止。扩展器运行在 `DocElabM` 单子中，它在 Lean 的 `TermElabM` 之上扩展了文档相关能力。扩展器首先会将参数[解析](#ArgParse)为合适的配置类型（通常借助 `FromArgs` 实例），随后返回 Lean 语法。

将扩展器与名称关联有两种方式：首选使用 `@[code_block]`、`@[role]`、`@[directive]` 与 `@[block_command]` 属性；或使用较低层级的 `@[code_block_expander]`、`@[role_expander]` 与 `@[directive_expander]` 属性。前一组属性会自动调用参数解析器，并使 Verso 能从 `FromArgs` 实例自动生成用法信息；后一组更底层，需要手工解析参数。

#### 4.2.1 参数解析 {#ArgParse}

上述调用语法相当受限，因此具体扩展需自行解析参数以提供足够灵活性。参数解析通过 `Verso.ArgParse.FromArgs` 实例完成：

!!! green "type class"
    ```lean
    Verso.ArgParse.FromArgs (α : Type) (m : Type → Type) : Type 1
    ```
    <hr>
    将一串 Verso 参数规范地转换为给定类型的方式。

    **实例构造器**

    `Verso.ArgParse.FromArgs.mk`

    **方法**
    `fromArgs : ArgParse m α`

    &nbsp;&nbsp;&nbsp;&nbsp;把一组参数转换成一个值。

`FromArgs.fromArgs` 的实现通常用 `Verso.ArgParse` 这一解析器 DSL 描述：

!!! green "inductive type"
    ```lean
    Verso.ArgParse (m : Type → Type) : Type → Type 1
    ```
    <hr>
    在底层单子 `m` 中进行参数解析的组合子。

    **构造器**

    `fail (stx? : Option Lean.Syntax) (message? : Option ArgParse.SigDoc) : ArgParse m α`

    &nbsp;&nbsp;&nbsp;&nbsp;携带给定错误信息的失败。

    `pure (val : α) : ArgParse m α`

    &nbsp;&nbsp;&nbsp;&nbsp;不消费任何参数直接返回值。

    `lift (desc : String) (act : m α) : ArgParse m α`

    &nbsp;&nbsp;&nbsp;&nbsp;从底层单子提升一个动作作为参数值。

    `positional (nameHint : Lean.Name) (val : ArgParse.ValDesc m α) (doc? : Option ArgParse.SigDoc := none) : ArgParse m α`

    &nbsp;&nbsp;&nbsp;&nbsp;匹配一个定位参数。

    `named (name : Lean.Name) (val : ArgParse.ValDesc m α) (optional : Bool) (doc? : Option ArgParse.SigDoc := none) : ArgParse m (if optional then Option α else α)`
    
    &nbsp;&nbsp;&nbsp;&nbsp;匹配一个具名参数，可指定是否可选。

    `anyNamed (name : Lean.Name) (val : ArgParse.ValDesc m α) (doc? : Option ArgParse.SigDoc := none) : ArgParse m (Lean.Ident × α)`
    
    &nbsp;&nbsp;&nbsp;&nbsp;匹配任意具名参数，返回键与值。

    `flag (name : Lean.Name) (default : Bool) (doc? : Option ArgParse.SigDoc := none) : ArgParse m Bool`
    
    &nbsp;&nbsp;&nbsp;&nbsp;匹配布尔开关标志。

    `flagM (name : Lean.Name) (default : m Bool) (doc? : Option ArgParse.SigDoc := none) : ArgParse m Bool`
    
    &nbsp;&nbsp;&nbsp;&nbsp;从底层单子派生默认值的布尔开关。

    `done : ArgParse m Unit`

    &nbsp;&nbsp;&nbsp;&nbsp;标记解析完成。

    `orElse (a b : ArgParse m α) : ArgParse m α`

    &nbsp;&nbsp;&nbsp;&nbsp;若 `a` 失败，则尝试 `b`。

    `seq (xs : Array (ArgParse m α)) : ArgParse m (Array α)`

    &nbsp;&nbsp;&nbsp;&nbsp;顺序运行一组解析器并收集结果。

    `many (p : ArgParse m α) : ArgParse m (Array α)`

    &nbsp;&nbsp;&nbsp;&nbsp;重复匹配零次或多次 `p`，直到失败为止。

    `remaining : ArgParse m (Array (Lean.Syntax × Arg))`

    &nbsp;&nbsp;&nbsp;&nbsp;返回尚未消费的所有原始参数（语法节点与值对）。

单个参数值通过 `ValDesc` 进行匹配：

!!! green "inductive type"
    ```lean
    Verso.ArgParse.ValDesc (m : Type → Type) (α : Type) : Type
    ```
    <hr>
    描述如何从一个参数值解析出类型的规范。

    **构造器**

    `Verso.ArgParse.ValDesc.mk`

    **域**

    `description : ArgParse.SigDoc`

    &nbsp;&nbsp;&nbsp;&nbsp;在自动生成的签名中，应该如何记录这一参数？

    `signature : ArgParse.CanMatch`

    &nbsp;&nbsp;&nbsp;&nbsp;在这三种值中，哪一种能够与这一参数相契合？

    `get : Doc.ArgVal → m α`

    &nbsp;&nbsp;&nbsp;&nbsp;如何把值转换伪给定类型。

对于 Lean 类型而言，其典范的值描述可以通过 `FromArgVal` 实例进行注册：

!!! green "type class"
    ```lean
    Verso.ArgParse.FromArgVal (α : Type) (m : Type → Type) : Type
    ```
    <hr>
    将一个 Verso 参数值转换为给定类型的规范方式。

    **实例构造器**

    `Verso.ArgParse.FromArgVal.mk`

    **方法**
    `fromArgVal : ArgParse.ValDesc m α`

    &nbsp;&nbsp;&nbsp;&nbsp;把一个参数值转换为目标类型的描述。

除了 `ArgParse` 的构造器之外，`Applicative` 和 `Functor` 的实例也是很重要的，此外还有以下的一些辅助函数：

!!! green "def"
    ```lean
    Verso.ArgParse.namedD {α m}
      (name : Lean.Name)
      (val  : ArgParse.ValDesc m α)
      (default : α) : ArgParse m α
    ```
    <hr>
    匹配一个具名参数；若缺失则返回给定的 `default`。

!!! green "def"
    ```lean
    Verso.ArgParse.positional' {α m}
      [ArgParse.FromArgVal α m]
      (nameHint : Lean.Name)
      (doc? : Option ArgParse.SigDoc := none)
      : ArgParse m α
    ```
    <hr>
    使用类型的 `FromArgVal` 实例匹配一个定位参数。

!!! green "def"
    ```lean
    Verso.ArgParse.named' {α m}
      [ArgParse.FromArgVal α m]
      (name : Lean.Name) (optional : Bool)
      (doc? : Option ArgParse.SigDoc := none)
      : ArgParse m (if optional then Option α else α)
    ```
    <hr>
    使用类型的 `FromArgVal` 实例匹配一个具名参数；可指定是否为可选参数。

!!! green "def"
    ```lean
    Verso.ArgParse.namedD' {α m}
      [ArgParse.FromArgVal α m]
      (name : Lean.Name)
      (default : α)
      (doc? : Option ArgParse.SigDoc := none)
      : ArgParse m α
    ```
    <hr>
    以 `FromArgVal` 实例为基础的具名参数解析器；若缺失则返回 `default`。

## 5 输出格式

本章介绍 Verso 的输出格式，当前提供两类主要输出：HTML 与 TeX。每一类都既包含在 Lean 中用于构建输出的类型与 API，也包含一个便于书写的内嵌 DSL 与示例。

### 5.1 HTML

Verso 的 HTML 输出使用 `Verso.Output.Html` 类型表示，用于将文档渲染到 Web。通常在打开 `Verso.Output.Html` 命名空间后，使用内嵌DSL来构造。

!!! green "inductive type"
    ```lean
    Verso.Output.Html : Type
    ```
    <hr>
    一个 HTML 的表示，用于把 Verso 渲染为网页。

    **构造器**

    `text (escape : Bool) (string : String) : Html`

    &nbsp;&nbsp;&nbsp;&nbsp;文本内容。若 `escape = true`，则在渲染时会将 `&` 等字符转义为实体（如 `&amp;`）。

    `tag (name : String) (attrs : Array (String × String)) (contents : Html) : Html`

    &nbsp;&nbsp;&nbsp;&nbsp;带有给定名称与属性的标签。

    `seq (contents : Array Html) : Html`

    &nbsp;&nbsp;&nbsp;&nbsp;将一组 HTML 值按顺序连接。

!!! green "def"
    ```lean
    Verso.Output.Html.empty : Html
    ```
    <hr>
    空的 HTML 文档。

!!! green "def"
    ```lean
    Verso.Output.Html.fromArray (htmls : Array Html) : Html
    ```
    <hr>
    将一个 HTML 数组追加为单个 HTML。等价于对同一内容使用 `Html.seq`，但可能得到更紧凑的表示。

!!! green "def"
    ```lean
    Verso.Output.Html.fromList (htmls : List Html) : Html
    ```
    <hr>
    将一个 HTML 列表追加为单个 HTML。等价于对相应数组使用 `Html.seq`，但可能更紧凑。

!!! green "def"
    ```lean
    Verso.Output.Html.append : Html → Html → Html
    ```
    <hr>
    追加两个 HTML 文档。

!!! green "opaque"
    ```lean
    Verso.Output.Html.visitM
      {m : Type → Type u} [Monad m]
      (text : Bool → String → m (Option Html) := fun _ _ => pure none)
      (tag  : String → Array (String × String) → Html → m (Option Html) := fun _ _ _ => pure none)
      (seq  : Array Html → m (Option Html) := fun _ => pure none)
      (html : Html) : m Html
    ```
    <hr>
    在某个 monad 中遍历整棵 HTML 树并应用改写。对节点处理返回 `none` 表示不改写。

!!! green "opaque"
    ```lean
    Verso.Output.Html.format : Html → Std.Format
    ```
    <hr>
    将 HTML 转换为 pretty-printer 文档，便于调试。注意其不保留预格式内容与脚本周围的空白。

!!! green "opaque"
    ```lean
    Verso.Output.Html.asString (html : Html) (indent : Nat := 0) (breakLines : Bool := true) : String
    ```
    <hr>
    将 HTML 转为既适合发送给浏览器、又便于阅读的字符串。

#### 在 Lean 中书写 HTML（内嵌 DSL）

HTML 文档用双花括号 `{{ ... }}` 书写，其语法与 HTML 十分类似，但有如下差异：

- **返回 Lean**：双花括号可在元素、属性值或整组属性处回到 Lean 表达式。
- **文本是字符串**：文本内容以 Lean 字符串字面量书写，便于精准控制空白。
- **字符串插值**：可在期望字符串的任意位置使用插值字符串 `s!`。

示例：定义一个生成 `<ul>` 列表的函数，并打印其字符串表示：

```lean
open Verso.Output.Html

def mkList (xs : List Html) : Html :=
  {{ <ul> {{ xs.map ({{ <li> {{ · }} </li> }}) }} </ul> }}

#eval mkList ["A", {{ <emph> "B" </emph> }}, "C"]
  |> Html.asString
  |> IO.println
```

可能的输出：

```html
<ul>
  <li>
    A</li>
  <li>
    <emph>B</emph></li>
  <li>
    C</li>
  </ul>
```

### 5.2 TeX

Verso 的 TeX 输出使用 `Verso.Output.TeX` 类型表示 LaTeX 文档。通常在打开命名空间 `Verso.Output.TeX` 后，使用内嵌 DSL 来构造。

!!! green "inductive type"
    ```lean
    Verso.Output.TeX : Type
    ```
    <hr>
    TeX 输出。

    **构造器**

    `text (string : String) : TeX`

    &nbsp;&nbsp;&nbsp;&nbsp;放入需要时会转义的文本。

    `raw (string : String) : TeX`

    &nbsp;&nbsp;&nbsp;&nbsp;原样包含的 TeX 代码（不转义）。

    `command (name : String) (optArgs args : Array TeX) : TeX`

    &nbsp;&nbsp;&nbsp;&nbsp;一个 LaTeX 命令，带可选与必选参数（分别用方括号与花括号）。

    `environment (name : String) (optArgs args content : Array TeX) : TeX`

    &nbsp;&nbsp;&nbsp;&nbsp;一个 LaTeX 环境，带可选与必选参数及内容。

    `paragraphBreak : TeX`

    &nbsp;&nbsp;&nbsp;&nbsp;段落分隔（渲染为一行空行）。

    `seq (contents : Array TeX) : TeX`

    &nbsp;&nbsp;&nbsp;&nbsp;TeX 内容拼接。

!!! green "def"
    ```lean
    Verso.Output.TeX.empty : TeX
    ```
    <hr>
    空的 TeX 文档。

!!! green "opaque"
    ```lean
    Verso.Output.TeX.asString (doc : TeX) : String
    ```
    <hr>
    将 TeX 文档转为可交给 LaTeX 处理的字符串。

#### 在 Lean 中书写 TeX（内嵌 DSL）

TeX 文档使用 `\TeX{ ... }` 书写，语法与 LaTeX 十分类似，但有如下差异：

- **返回 Lean**：`\Lean{ ... }` 返回到 Lean，且应产生一个 `TeX` 值。
- **文本是字符串**：文本内容以 Lean 字符串字面量书写，便于精准控制空白。
- **字符串插值**：可在期望字符串的任意位置使用插值字符串 `s!`。

示例：定义一个生成项目符号列表的函数，并打印其字符串表示：

```lean
open Verso.Output.TeX

def mkList (xs : List TeX) : TeX :=
  \TeX{
    \begin{itemize}
      \Lean{ xs.map (\TeX{\item " " \Lean{·} "\n"}) }
    \end{itemize}
  }

#eval mkList ["A", \TeX{\emph{"B"}}, "C"]
  |> TeX.asString
  |> IO.println
```

可能的输出：

```tex
\begin{itemize}
\item A
\item \emph{B}
\item C

\end{itemize}
```

## 6 网页

Verso 的"网站（website）"体裁是一个静态站点生成器。它包含两个 Verso `Genre`：`Page` 与 `Post`，二者除了元数据之外完全相同：

!!! green "def"
    ```lean
    Verso.Genre.Blog.Page : Genre
    ```
    <hr>
    一个普通的网页（不是博文）。

!!! green "def"
    ```lean
    Verso.Genre.Blog.Post : Genre
    ```
    <hr>
    一篇博文。

两者共享同一组扩展：

!!! green "inductive type"
    ```lean
    Verso.Genre.Blog.BlockExt : Type
    ```
    <hr>
    页面与博文中可用的"额外块（blocks）"。

    **构造器**

    - `highlightedCode (opts : Blog.CodeOpts) (highlighted : SubVerso.Highlighting.Highlighted) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;高亮显示的 Lean 代码。

    - `message (summarize : Bool) (msg : SubVerso.Highlighting.Highlighted.Message) (expandTraces : List Lean.Name) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;高亮显示的 Lean 消息。

    - `lexedText (content : Blog.LexedText) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;词法切分后的文本，以高亮语法进行展示。

    - `htmlDiv (classes : String) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;渲染时将内容包裹在带给定类名的 `<div>` 标签中。

    - `htmlWrapper (tag : String) (attributes : Array (String × String)) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;渲染时将内容包裹在指定标签（含给定属性）中。

    - `htmlDetails (classes : String) (summary : Output.Html) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;渲染时将内容包裹在 `<details>` 标签中，并使用给定 `summary` 作为摘要。

    - `blob (html : Output.Html) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;一段 HTML"原样块"。其内部内容在后续处理中会被丢弃。

    - `component (name : Lean.Name) (data : Lean.Json) : Blog.BlockExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;对某个"组件"的引用。

!!! green "inductive type"
    ```lean
    Verso.Genre.Blog.InlineExt : Type
    ```
    <hr>
    页面与博文中可用的"额外行内元素（inline elements）"。

    **构造器**

    - `highlightedCode (opts : Blog.CodeOpts) (highlighted : SubVerso.Highlighting.Highlighted) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;高亮显示的 Lean 代码。

    - `message (msg : SubVerso.Highlighting.Highlighted.Message) (expandTraces : List Lean.Name) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;高亮显示的 Lean 消息。

    - `lexedText (content : Blog.LexedText) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;词法切分后的文本，以高亮语法进行展示。

    - `customHighlight (highlighted : SubVerso.Highlighting.Highlighted) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;高亮代码，但不一定来自 Lean。

    - `label (name : Lean.Name) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;作为交叉引用目标的标签。

    - `ref (name : Lean.Name) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;对某个标签的引用。

    - `pageref (name : Lean.Name) (id? : Option String) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;引用某个页面/博文的"内部 Lean 名称"，以链接形式显示。若 `id? = some X`，则链接将追加 `#X` 作为片段标识。

    - `htmlSpan (classes : String) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;一个带给定类名的 HTML `<span>` 元素。

    - `blob (html : Output.Html) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;一段 HTML"原样行内块"。其内部内容在后续处理中会被丢弃。

    - `component (name : Lean.Name) (data : Lean.Json) : Blog.InlineExt`
      
      &nbsp;&nbsp;&nbsp;&nbsp;对某个"组件"的引用。

然而，页面与博文的"元数据（metadata）"是不同的：

!!! green "structure"
    ```lean
    Verso.Genre.Blog.Page.Meta : Type
    ```
    <hr>
    非博文页面使用的元数据。

    **构造器**

    `Verso.Genre.Blog.Page.Meta.mk`

    **域**

    `showInNav : Bool`
    
    &nbsp;&nbsp;&nbsp;&nbsp;是否在导航中显示该页面。

    `htmlId : Option String`
    
    &nbsp;&nbsp;&nbsp;&nbsp;分配给该页面标题的 HTML id。

!!! green "structure"
    ```lean
    Verso.Genre.Blog.Post.Meta : Type
    ```
    <hr>
    博文使用的元数据。

    **构造器**

    `Verso.Genre.Blog.Post.Meta.mk`

    **域**

    `date : Blog.Date`
    
    &nbsp;&nbsp;&nbsp;&nbsp;文章日期。默认情况下它也用于生成 URL，并显示在页面内容中。

    `authors : List String`
    
    &nbsp;&nbsp;&nbsp;&nbsp;作者列表。

    `categories : List Post.Category`
    
    &nbsp;&nbsp;&nbsp;&nbsp;该文章归属的分类。

    `draft : Bool`
    
    &nbsp;&nbsp;&nbsp;&nbsp;若为 `true`，默认不渲染该文章（草稿）。

    `htmlId : Option String`
    
    &nbsp;&nbsp;&nbsp;&nbsp;分配给该文章标题的 HTML id。

### 6.1 生成站点 {#blogMain}

博客项目通常应提供一个可执行程序，它对"合适的[站点与主题](#site-config)"调用 `blogMain`，并将命令行参数原样转发。`blogMain` 负责对站点执行[遍历](#traversal)并生成 HTML。

!!! green "def"
    ```lean
    Verso.Genre.Blog.blogMain
      (theme : Blog.Theme)
      (site : Blog.Site)
      (relativizeUrls : Bool := true)
      (linkTargets : Code.LinkTargets Blog.TraverseContext := {})
      (options : List String)
      (components : Blog.Components := by exact %registered_components)
      (header : String := Output.Html.doctype)
      : IO UInt32
    ```
    <hr>
    生成给定 `site` 的 HTML。

    **参数：**

    - `theme`：用于渲染内容的主题。
    - `site`：要生成的站点。
    - `options`：传入的命令行选项。

    **可选参数：**

    - `relativizeUrls`：将站点内部链接从绝对路径改写为相对路径，以便将博客托管在某个子目录下。默认 `true`。
    - `linkTargets`：指定如何把 Lean 代码中的超链接指向进一步的文档。默认不生成链接。
    - `components`：组件实现表；默认从已注册的表自动填充。
    - `header`：在每个 HTML 文档前输出的文本。默认输出 `<!doctype html>`，可以覆盖以便与其他静态站点生成器集成。

### 6.2 配置站点 {#site-config}

站点的 URL 与目录布局由 `Site` 指定：

!!! green "inductive type"
    ```lean
    Verso.Genre.Blog.Site : Type
    ```
    <hr>
    用于描述"整个站点"的布局。

    **构造器**

    - `page (id : Lean.Name) (text : Part Page) (contents : Array Blog.Dir) : Blog.Site`
      
      &nbsp;&nbsp;&nbsp;&nbsp;站点的根是一个"页面"。

    - `blog (id : Lean.Name) (text : Part Page) (contents : Array Blog.BlogPost) : Blog.Site`
      
      &nbsp;&nbsp;&nbsp;&nbsp;站点的根是一个"博客"，并带有其文章。

!!! green "inductive type"
    ```lean
    Verso.Genre.Blog.Dir : Type
    ```
    <hr>
    站点布局中的"目录"。

    **构造器**

    - `page (name : String) (id : Lean.Name) (text : Part Page) (contents : Array Blog.Dir) : Blog.Dir`
      
      &nbsp;&nbsp;&nbsp;&nbsp;该目录的根是给定的页面。

    - `blog (name : String) (id : Lean.Name) (text : Part Page) (contents : Array Blog.BlogPost) : Blog.Dir`
      
      &nbsp;&nbsp;&nbsp;&nbsp;该目录的根是一个博客。

    - `static (name : String) (files : System.FilePath) : Blog.Dir`
      
      &nbsp;&nbsp;&nbsp;&nbsp;该目录的根包含静态文件；生成站点时，从 `files` 路径拷贝到站点的静态文件目录。

通常，`Site` 会用一个"小型内嵌的配置语言"来构建。

博客通过"主题（theme）"进行渲染。主题是一组模板（templates）的集合。模板是"单子函数"，从一组"动态类型"的参数构造 `Html`：

!!! green "structure"
    ```lean
    Verso.Genre.Blog.Theme : Type
    ```
    <hr>
    站点如何渲染的规范。

    **域**

    `primaryTemplate : Blog.Template`
    
    &nbsp;&nbsp;&nbsp;&nbsp;用于渲染每一个页面的模板。它应当构造整个页面的 HTML（包括 `<html>` 元素）。
    
    &nbsp;&nbsp;&nbsp;&nbsp;在 `<head>` 元素中，它应调用 `builtinHeader`，以确保所需依赖已加载且执行 Verso 特定的初始化。
    
    &nbsp;&nbsp;&nbsp;&nbsp;在 `<body>` 中，它应检查 `"posts" : Html` 参数是否存在：若存在，则当前页面为"博客索引"，应把该参数值当作"文章列表"放置；若存在 `"categories" : Post.Categories`，则应将其渲染为"分类列表"。
    
    &nbsp;&nbsp;&nbsp;&nbsp;`"content" : Html` 参数包含页面主体，应当合适地插入到结果中。

    `pageTemplate : Blog.Template`
    
    &nbsp;&nbsp;&nbsp;&nbsp;用于渲染"普通页面"的模板。它应使用 `"title"` 与 `"content"` 两个参数构造页面内容；其结果通过 `"content"` 参数传给 `primaryTemplate`。

    `postTemplate : Blog.Template`
    
    &nbsp;&nbsp;&nbsp;&nbsp;用于渲染"博文"的模板。它应使用 `"title"` 与 `"content"` 两个参数构造文章内容；其结果通过 `"content"` 参数传给 `primaryTemplate`。
    
    &nbsp;&nbsp;&nbsp;&nbsp;此外，若存在 `"metadata" : Post.PartMetadata`，可用来渲染作者、日期与分类等信息。

    `archiveEntryTemplate : Blog.Template`
    
    &nbsp;&nbsp;&nbsp;&nbsp;用于在"文章归档"中摘要展示一篇文章的模板。接收 `"post"`（文章本身）与 `"summary"`（要展示的 HTML 摘要）两个参数。

    `categoryTemplate : Blog.Template`
    
    &nbsp;&nbsp;&nbsp;&nbsp;用于在"某分类的文章列表"页面顶部展示分类信息的模板。接收单个参数 `"category" : Post.Category`。

    `adHocTemplates : Array String → Option Blog.Template.Override`
    
    &nbsp;&nbsp;&nbsp;&nbsp;为给定路径自定义渲染：可以替换所用模板，并提供额外参数。

!!! green "def"
    ```lean
    Verso.Genre.Blog.Template : Type
    ```
    <hr>
    由参数生成 HTML 的过程。等价写法为 `TemplateM Html`。

!!! green "def"
    ```lean
    Verso.Genre.Blog.TemplateM (α : Type) : Type
    ```
    <hr>
    提供"以动态类型参数实例化模板"的单子。

!!! green "def"
    ```lean
    Verso.Genre.Blog.Template.param [TypeName α] (key : String) : Blog.TemplateM α
    ```
    <hr>
    读取给定模板参数 `key` 的值；若不存在或类型不匹配，则抛出异常。

!!! green "def"
    ```lean
    Verso.Genre.Blog.Template.param? [TypeName α] (key : String) : Blog.TemplateM (Option α)
    ```
    <hr>
    读取给定模板参数 `key` 的值；若存在但类型不匹配则抛出异常；否则返回 `none`。

!!! green "def"
    ```lean
    Verso.Genre.Blog.Template.builtinHeader : Blog.TemplateM Output.Html
    ```
    <hr>
    返回 `<head>` 中为确保站点正常工作所需包含的内容（依赖与 Verso 初始化等）。

## 7 手册和书

Verso 的 Manual 体裁可用于编写参考手册、教科书或其他类似书籍的文档。它支持通过 LaTeX 生成 HTML 和 PDF，但与 HTML 支持相比，PDF 支持相对不成熟且未经测试。

!!! green "def"
    ```lean
    Verso.Genre.Manual : Genre
    ```
    <hr>
    一种用于编写参考手册和其他类似书籍的文档的类型。

（太长了，请参考原文）

## 索引 依赖项 （请参考原文）
