# 使用 Verso 在 Lean 中编写文档

原文：[https://github.com/leanprover/verso](https://github.com/leanprover/verso)

作者：David Thrane Christiansen 译者：子鱼 subfishzhou@gmail.com

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

一个部分包含一系列区块，接着是一系列子部分，两者都可以为空。

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

#### 2.2.1 块语法

段落是未修饰的：任何不是另一个块的内联序列都是段落。 段落一直持续到空白行（即仅包含空格的行）或另一个块开头：

!!! blue "段落"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    This is one paragraph.
    Even though this sentence is on a
    new line, the paragraph continues.

    This is a new paragraph.
    * This list stopped the paragraph.
    * As in Markdown and SGML, lists
    are not part of paragraphs.
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
        This is one paragraph. Even
        though this sentence is on a new
        line, the paragraph continues.
    </p>

    <p> This is a new paragraph. </p>

    <ul>
        <li>
            <p>
                This list stopped the
                paragraph.
            </p>
        </li>
        <li>
            <p>
                As in Markdown and SGML,
                lists   are not part of
                paragraphs.
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

有序列表项由“零个或多个空格 + 一串数字 + 指示符（`.` 或 `)`）”起始。与无序列表相同，有序列表也对缩进与指示符敏感：相同缩进与相同指示符归为同一列表层级。

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

描述列表由若干“描述项”组成，具有相同缩进。一个描述项的第一行以“零个或多个空格 + 冒号 `:` + 一串行内元素”构成，随后必须有一行空行，然后跟随一个或多个缩进严格大于冒号位置的块。

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

引用块表示一组块是由作者以外的人说的。其语法为：一行以“零个或多个空格 + 大于号 `>`”起始，随后必须跟随缩进严格大于该 `>` 的一个或多个块，这些块共同组成引用内容。

!!! blue "引用"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    It is said that:
    > Quotations are excellent.

      This paragraph is part of the
      quotation.

     So is this one.

    But not this one.
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p> It is said that: </p>

    <blockquote>
      <p> Quotations are excellent. </p>
      <p>
        This paragraph is part of the
        quotation.
      </p>
      <p> So is this one. </p>
    </blockquote>

    <p> But not this one. </p>
    ```
    </div>
    </div>

### 2.2.3 行内语法（Inline Syntax）

强调（emphasis）使用下划线 `_`：

!!! blue "强调"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    Here's some _emphasized_ text
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      Here's some
      <emph> emphasized </emph> text
    </p>
    ```
    </div>
    </div>

外层使用更多下划线可形成“嵌套强调”：

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
    Here's some *bold* text
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      Here's some <bold>bold</bold> text
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

数学：单个或双个美元符包裹的 TeX 代码。`$...$` 为行内，`$$...$$` 为陈列模式：

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

角色（role）为后续行内赋予特殊语义。可用于代码阐释、技术术语定义/使用、旁注等。语法：一行内用花括号给出名称与参数，后面紧跟一个“自我定界”的行内元素，或用方括号包裹的若干行内元素。

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

## 2.3 与 Markdown 的差异

### 2.3.1 语法错误
Markdown 允许一组优先级规则来解释不匹配的分隔符（例如 `what _is *bold_ or emph*?`），在 Lean 标记中这类情况是语法错误；同样，未闭合的分隔符（如 `*` 或 `_`）在 Markdown 中当作普通字符，而 Lean 标记中要求显式转义。长文技术写作更倾向于尽早发现此类错误。

### 2.3.2 减少前瞻
在 Markdown 中，`[this][here]` 是否为链接取决于文档中是否定义了 `here`；在 Lean 标记中它总是链接，若缺失目标则报错。

### 2.3.3 标题嵌套
Lean 标记认为每个文档都有标题，且强制使用 `#` 作为最外层标题、`##` 为下一层，依此类推。这样单文件既可代表节、章乃至整本书，而无需维护全局层级映射。

### 2.3.4 体裁特定扩展
Markdown 没有标准方式表达特定工具/体裁的概念；Lean 标记提供标准语法以组合式扩展。

### 2.3.5 移除少用特性
为减少意外并提升可预测性，Verso 去除了少用特性，例如 CommonMark 所区分的“紧凑/宽松列表”等。

## 构建文档

本节简述 Verso 文档从作者到读者的标准流程（不同体裁在细节上会作定制）：

1) 使用 Verso 标记语言编写文本，解析为 Lean 的 `Syntax`。
2) 进行阐释（elaboration），转为对应体裁的 Lean 数据结构。
3) 将生成的 Lean 代码编译为可执行程序。
4) 运行该程序，执行“遍历（traversal）”步骤，解析交叉引用并计算全局元数据。
5) 生成目标输出（HTML/TeX 等）。

### 3.1 阐释（Elaboration）
阐释把标记语言转换为内部归纳类型，并在遇到扩展点时调用注册的实现。所有文档都以“体裁（genre）”为参数；体裁约定了该文档可用的元数据、块（Block）与行内（Inline）元素等。

!!! green "API（体裁定义要点）"
    ```lean
    structure Verso.Doc.Genre : Type where
      PartMetadata    : Type
      Block           : Type
      Inline          : Type
      TraverseContext : Type
      TraverseState   : Type
    -- 各体裁需定义：
    -- 1) 自定义块/行内元素类型
    -- 2) 遍历上下文与可变状态
    -- 3) main：组织遍历与输出
    ```

### 3.2 编译（Compilation）
阐释之后，文档被编译为可执行程序。各体裁提供 `main` 入口来完成遍历与输出；网站等非线性体裁会额外提供布局/配置方式。常见参数包括输出格式以及渲染自定义项。

!!! blue "最小工作流"
    - 编译：将阐释后的 Lean 值编译为可执行程序
    - 运行：传入命令行/代码参数（输出格式、主题、链接策略等）
    - 体裁 `main`：执行遍历与输出

### 3.3 遍历（Traversal）
遍历在运行期进行，按次序多次遍历文档并累计全局表，例如交叉引用、目录、引用文献等；在达成不再改变的“不动点”前会重复。体裁通过 `Traverse` 与相关实例说明如何在块/行内级别更新上下文与状态。

!!! green "API（遍历接口要点）"
    ```lean
    class Verso.Doc.Traverse (g : Doc.Genre) (m : outParam (Type → Type)) : Type :=
      part   : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] →
               Doc.Part g   → m Unit
      block  : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] →
               Doc.Block g  → m Unit
      inline : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] →
               Doc.Inline g → m Unit

      genrePart   : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] →
                    g.PartMetadata → Doc.Part g → m (Option (Doc.Part g))
      genreBlock  : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] →
                    g.Block → Array (Doc.Block g) → m (Option (Doc.Block g))
      genreInline : [MonadReader g.TraverseContext m] → [MonadState g.TraverseState m] →
                    g.Inline → Array (Doc.Inline g) → m (Option (Doc.Inline g))

    class Verso.Doc.TraversePart (g : Doc.Genre) : Type :=
      inPart  : Doc.Part g → g.TraverseContext → g.TraverseContext

    class Verso.Doc.TraverseBlock (g : Doc.Genre) : Type :=
      inBlock : Doc.Block g → g.TraverseContext → g.TraverseContext
    ```

!!! blue "遍历收敛（固定点）"
    - 从文档首到尾，反复遍历直至“文档与状态”均不再变化
    - 若连续若干次遍历仍有变化，视为失败（避免无限循环）

### 3.4 生成输出（Output Generation）
遍历完成后生成可读版本（各体裁决定支持哪些格式）。输出为 HTML 的体裁通常会序列化交叉引用数据库，供其他文档自动链接。

!!! green "API（输出对象）"
    ```lean
    inductive Verso.Output.Html : Type
    inductive Verso.Output.TeX  : Type
    -- 常用构造与工具：text / tag / seq / empty / append / asString ...
    -- HTML 体裁可选择输出交叉引用数据库（序列化），供其他文档复用
    ```

## 扩展

Verso 的扩展机制允许体裁组合出新的块/行内元素、为阐释与遍历插入逻辑，以及为不同输出后端提供渲染实现。扩展由普通 Lean 代码定义，具备良好的类型约束与可组合性。

- 可定义自有数据（例如手册体裁的块、行内元素的数据结构），并注册阐释器将标记语法映射到这些数据。
- 在遍历（Traversal）中，扩展可读取/更新体裁状态，建立交叉引用、生成目录、注入永久链接等。
- 为 HTML/TeX 输出实现渲染器，并按需声明额外的静态资源（脚本/CSS/许可证信息）。

!!! green "API（扩展的三个面向）"
```lean
-- 1) 数据与阐释：
structure Verso.Genre.Manual.Block    -- 体裁自定义块
structure Verso.Genre.Manual.Inline   -- 体裁自定义行内
-- 注册阐释器：将标记语法 → (Block/Inline) 数据

-- 2) 遍历：
class Verso.Doc.Traverse (g : Doc.Genre) (m : outParam (Type → Type))
-- 通过 part/block/inline 与 genrePart/genreBlock/genreInline 钩子
-- 读取 g.TraverseContext / 更新 g.TraverseState，执行重写

-- 3) 渲染：
structure Verso.Genre.Manual.BlockDescr where
  toHtml   : Option (InlineToHtml Manual (ReaderT ExtensionImpls IO))
  toTeX    : Option (InlineToTeX  Manual (ReaderT ExtensionImpls IO))
  extraJs  : List String
  extraJsFiles : List JsFile
  extraCss : List String
  extraCssFiles : List (String × String)
  licenseInfo  : List LicenseInfo
```

!!! blue "工作流要点"
- 扩展首先定义“数据（块/行内）+阐释”，让标记语法可产出强类型的文档值。
- 在遍历阶段填充交叉引用、目录、永久链接等全局信息；必要时对文档进行最小重写（直到收敛）。
- 渲染阶段面向不同后端（HTML/TeX）输出，按需注入静态资源与致谢信息。

!!! purple "资源与合规（许可证）"
- 通过 `BlockDescr.licenseInfo` / `InlineDescr.licenseInfo` 申报引入的前端依赖及许可证文本。
- 体裁提供统一命令（如 `licenseInfo`）汇总并渲染致谢页面，便于合规与复用。

## 输出格式

Verso 目前主要支持 HTML 与 TeX：

- HTML：使用 `Verso.Output.Html` 的嵌入式 DSL 构建页面结构；可在模板中安全插入文本、标签与属性，最终通过 `asString` 输出字符串。
- TeX：使用 `Verso.Output.TeX` 的 DSL 生成（La)TeX 源码，支持命令、环境与文本拼接等。

体裁为各自新增元素实现对应的 HTML/TeX 渲染器，以保证风格一致与依赖注入（内置头部、脚本、样式等）。

### 5.1 HTML
`Verso.Output.Html` 表示 HTML 文档，常配合命名空间 `Verso.Output.Html` 提供的 DSL 使用。

!!! green "API（Html）"
    ```lean
    inductive Verso.Output.Html : Type
    def Html.empty : Html
    def Html.append : Html → Html → Html
    def Html.seq    : Array Html → Html
    def Html.fromArray (xs : Array Html) : Html
    def Html.fromList  (xs : List  Html) : Html
    def Html.text  (escape : Bool) (s : String) : Html
    def Html.tag   (name : String) (attrs : Array (String × String)) (body : Html) : Html
    opaque Html.asString (doc : Html) : String
    ```

!!! blue "示例：构建一个无序列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```lean
    open Verso.Output.Html

    def mkList (xs : List Html) : Html :=
      {{ <ul> {{ xs.map ({{ <li> {{ · }} </li> }}) }} </ul> }}
    ```
    </div>
    <div markdown>
    **结果（asString）**
    ```html
    <ul>
      <li>A</li>
      <li><emph>B</emph></li>
      <li>C</li>
    </ul>
    ```
    </div>
    </div>

### 5.2 TeX
`Verso.Output.TeX` 表示（La）TeX 文档，常配合 `Verso.Output.TeX` 提供的 DSL 使用。

!!! green "API（TeX）"
    ```lean
    inductive Verso.Output.TeX : Type
    def TeX.empty : TeX
    def TeX.text  (s : String) : TeX
    def TeX.raw   (s : String) : TeX
    def TeX.command (name : String) (optArgs args : Array TeX) : TeX
    def TeX.environment (name : String) (optArgs args : Array TeX) : TeX
    def TeX.paragraphBreak : TeX
    def TeX.seq (xs : Array TeX) : TeX
    opaque TeX.asString (doc : TeX) : String
    ```

!!! blue "示例：itemize 列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```lean
    open Verso.Output.TeX

    def mkList (xs : List TeX) : TeX :=
      \TeX{
        \begin{itemize}
          \Lean{ xs.map (\TeX{\item " " \Lean{·} "\n"}) }
        \end{itemize}
      }
    ```
    </div>
    <div markdown>
    **结果（asString）**
    ```tex
    \begin{itemize}
    \item A
    \item \emph{B}
    \item C
    \end{itemize}
    ```
    </div>
    </div>

## 网页

“网站/博客”体裁通过站点（Site）与主题（Theme）描述网址结构与呈现模板：

- Site：用小型配置语言描述页面、文章、类别、静态文件与目录结构。
- Theme：提供模板（monadic 函数）以 `Html` 片段组合成完整页面，并可按路径覆写模板或注入额外参数。
- blogMain：体裁提供的可执行入口，负责遍历站点、应用主题并生成 HTML；可选择相对链接、代码交叉引用目标等参数。

### 6.1 生成站点（blogMain）
!!! green "API（blogMain）"
    ```lean
    def Verso.Genre.Blog.blogMain
      (theme : Blog.Theme) (site : Blog.Site)
      (relativizeUrls : Bool := true)
      (linkTargets : Code.LinkTargets Blog.TraverseContext := {})
      (options : List String)
      (components : Blog.Components := %registered_components)
      (header : String := Output.Html.doctype)
      : IO UInt32
    -- 说明：遍历站点并生成 HTML，可选择将绝对链接改为相对链接、指定 Lean 代码的交叉引用目标、注入组件与 HTML 头部等。
    ```

### 6.2 配置站点（Site/Dir/Page/Post）
!!! green "API（站点结构）"
    ```lean
    inductive Verso.Genre.Blog.Site : Type
    inductive Verso.Genre.Blog.Dir  : Type
    structure Verso.Genre.Blog.Page.Meta : Type -- 页面元信息
    structure Verso.Genre.Blog.Post.Meta : Type -- 博文元信息（日期、作者、分类、草稿等）
    ```

!!! blue "小贴士"
    - `Dir.static files`: 从指定目录拷贝静态资源至站点根
    - 页面/文章均可通过 `htmlId` 自定义标题的 HTML id，用于锚点

### 6.3 主题与模板（Theme/Template）
!!! green "API（主题）"
    ```lean
    structure Verso.Genre.Blog.Theme : Type where
      primaryTemplate       : Blog.Template
      pageTemplate          : Blog.Template
      postTemplate          : Blog.Template
      archiveEntryTemplate  : Blog.Template
      categoryTemplate      : Blog.Template
      adHocTemplates        : Array String → Option Blog.Template.Override
    -- 模板是从动态参数构造 Html 的过程（TemplateM Html），
    -- primaryTemplate 负责整页（含 <html>/<head>/<body>）。
    ```

!!! purple "约定"
    - 在 `<head>` 中调用 `builtinHeader` 以注入必要依赖与初始化脚本
    - `primaryTemplate` 读取参数 `"content"`/`"posts"`/`"categories"` 决定页类型与内容布局


## 手册和书

“手册/书籍”体裁侧重线性文本的结构与长期可维护性：

- 标签与引用：为章节与术语指定稳定 `tag`，可用于索引、快速跳转与跨文档链接。
- 段落指令：`paragraph` 指示一组块逻辑上构成段落（HTML/TeX 渲染会相应调整边距/空行）。
- Docstring/选项文档：可内嵌 Lean 常量的文档与系统选项说明，保持代码与文档一致。
- 术语表：`deftech` 定义术语，`tech` 在其他位置引用，键的标准化可配置。
- 开源许可证：块/行内元素可申报前端依赖的许可证，体裁汇总到致谢页面。

### 7.1 标签与引用（Tags & References）
!!! blue "要点"
    - 通过为章节/术语等指定 `tag`，可：
      - 加入快速跳转与索引
      - 生成稳定的永久链接（重构时链接不失效）
      - 跨文档自动链接

### 7.2 段落指令（paragraph）
!!! blue "段落合并"
    使用 `paragraph` 将多块合并为一个逻辑段落：HTML 渲染会减小内部边距；TeX 渲染会省略段落间空行。

### 7.3 Docstring 与选项文档
!!! blue "示例"
    ```text
    {docstring List.forM}
    {optionDocs pp.deepTerms.threshold}
    ```
    将从 Lean 源中提取常量/选项的文档，保持代码与文档同步。

### 7.4 术语（deftech/tech）
!!! green "API（术语）"
    ```lean
    def Verso.Genre.Manual.deftech : Elab.RoleExpanderOf TechArgs
    def Verso.Genre.Manual.tech    : Elab.RoleExpanderOf TechArgs
    -- deftech 定义术语，内部对关键字作规范化（小写、"ies"→"y"、合并空白/连字符），
    -- tech 在使用处引用；二者共享键的派生规则，可覆盖（normalize=false / 指定 key）。
    ```

### 7.5 开源许可证（OSS Licenses）
!!! green "API（许可证描述）"
    ```lean
    structure Verso.Genre.Manual.LicenseInfo : Type where
      identifier : String    -- SPDX 标识
      dependency : String    -- 依赖名称（用于排序与标题）
      howUsed    : Option String
      link       : Option String
      text       : Array (Option String × String) -- 按段落分节的纯文本许可证

    def Verso.Genre.Manual.licenseInfo : Elab.BlockCommandOf Unit
    -- 汇总文档中声明的所有前端依赖许可证并渲染致谢页面
    ```

## 索引 依赖项 （请参考原文）

## 附：标记示例（markup-example）

下列示例使用自定义蓝色块，左列是“Verso 语言”，右列是渲染“结果”。

!!! blue "有序列表"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    1. 第一项
    2. 第二项
    3. 第三项
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <ol>
      <li><p>第一项</p></li>
      <li><p>第二项</p></li>
      <li><p>第三项</p></li>
    </ol>
    ```
    </div>
    </div>

!!! blue "描述列表（术语–说明）"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    术语A: 说明文字A
    术语B: 说明文字B
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <dl>
      <dt>术语A</dt><dd><p>说明文字A</p></dd>
      <dt>术语B</dt><dd><p>说明文字B</p></dd>
    </dl>
    ```
    </div>
    </div>

!!! blue "行内样式与链接"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    *强调* 与 **加粗**，以及 `代码` 片段。
    还可以写链接：[可点击文本](#anchor)
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>
      <em>强调</em> 与 <strong>加粗</strong>，以及 <code>代码</code> 片段。
      还可以写链接：<a href="#anchor">可点击文本</a>
    </p>
    ```
    </div>
    </div>

!!! blue "代码块（围栏）"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    ```lean
    def hello : String := "hello"
    ```
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <pre><code class="language-lean">def hello : String := "hello"</code></pre>
    ```
    </div>
    </div>

!!! blue "脚注与脚注引用"
    <div class="grid grid-cols-2" markdown>
    <div markdown>
    **Verso 语言**
    ```markdown
    脚注示例[^note]。

    [^note]: 这里是脚注内容。
    ```
    </div>
    <div markdown>
    **结果**
    ```html
    <p>脚注示例<sup id="fnref-note"><a href="#fn-note">1</a></sup>。</p>
    <section class="footnotes">
      <ol>
        <li id="fn-note"><p>这里是脚注内容。</p></li>
      </ol>
    </section>
    ```
    </div>
    </div>

## 附：命名文档块（namedocs）摘要

以下以绿色“API”样式概括常用构件（保留关键签名与用途）。

!!! green "Verso.Doc.Genre"
    ```lean
    structure Verso.Doc.Genre : Type
    -- 关键字段：PartMetadata / Block / Inline / TraverseContext / TraverseState
    -- 说明：定义体裁扩展点与遍历所需上下文与状态。
    ```

!!! green "Verso.Doc.Part / Block / Inline"
    ```lean
    def   Verso.Doc.Part   (g : Doc.Genre) : Type
    def   Verso.Doc.Block  (g : Doc.Genre) : Type
    def   Verso.Doc.Inline (g : Doc.Genre) : Type
    -- 说明：文档的层级元素；Part 含 Block，Block 含 Inline。
    ```

!!! green "遍历接口（Traversal）"
    ```lean
    class Verso.Doc.Traverse      (g : Doc.Genre) (m : outParam (Type → Type)) : Type
    class Verso.Doc.TraversePart  (g : Doc.Genre) : Type
    class Verso.Doc.TraverseBlock (g : Doc.Genre) : Type
    -- 说明：提供遍历钩子与基于上下文/状态的重写。
    ```

!!! green "HTML 输出 DSL"
    ```lean
    inductive Verso.Output.Html : Type
    -- 构造：text / tag / seq；工具：empty / append / fromArray / fromList / asString
    ```

!!! green "TeX 输出 DSL"
    ```lean
    inductive Verso.Output.TeX : Type
    -- 构造：text / raw / command / environment / paragraphBreak / seq；工具：empty / asString
    ```

!!! blue "def"
    ```lean
    List.forM {u v w} {m : Type u → Type v} [Monad m]
    {a : Type w} (as : List a) (f : a → m PUnit) : m PUnit
    ```
    Applies the monadic action `f` to every element in the list, in order.

    参数说明：
    : **as** — 输入列表
    : **f**  — 作用在元素上的 monadic 函数

    参见：`List.mapM`（收集结果的变体）。

!!! purple "lemma"
    这里是一个引理块的示例。

!!! green "API"
    这里是 API 描述块的示例。