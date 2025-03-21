# Commands

Mathlib 版本：`e4cf8333e0be712392567e370eead57e05d636a7`

## \#adaptation_note
定义于：`adaptationNoteCmd`

适配注释（adaptation notes）是用于指示某段代码已因 Lean 核心变动而修改的注释。这类注释通常需要未来采取进一步的维护措施。

## \#aesop_rules
定义于：`Aesop.Frontend.Parser.showRules`


## \#aesop_stats
定义于：`Aesop.Frontend.Parser.showStats`


## \#allow_unused_tactic
定义于：`Mathlib.Linter.UnusedTactic.«command#allow_unused_tactic!___»`

`#allow_unused_tactic` 接受以空格分隔的标识符列表。这些标识符将被未使用策略检查器（unused tactic linter）允许：即使这些策略不修改目标，也不会触发警告。

注意：为此，这些标识符应为各策略的 `SyntaxNodeKind`。

例如，允许 `done` 和 `skip` 策略可使用：
```lean
#allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip
```

此变更仅作用于当前文件。若需**持久性**变更，请使用 `!` 标志：命令 `#allow_unused_tactic! ids` 将使检查器在导入该文件的文件中继续忽略这些策略。

命令 `#show_kind tac` 可辅助查找 `SyntaxNodeKind`。

## \#check
定义于：`Lean.Parser.Command.check`


## \#check_assertions
定义于：`Mathlib.AssertNotExist.«command#check_assertions!»`

`#check_assertions` 检索所有声明及声明不存在（包括间接导入文件中的）的导入项，并报告其当前状态：
* ✓ 表示声明或导入存在，
* × 表示声明或导入不存在。

这意味着预期所有检查在 `#check_assertions` 使用时（通常在构建完整 `Mathlib` 后）均**成功**。

若所有声明及导入在 `#check_assertions` 使用时均存在，则命令记录信息。否则，发出警告。

变体 `#check_assertions!` 仅打印环境中不存在的声明/导入项。特别地，若一切已导入，则静默，便于测试。

## \#check_failure
定义于：`Lean.Parser.Command.check_failure`


## \#check_simp
定义于：`Lean.Parser.checkSimp`

`#check_simp t ~> r` 检查 `simp` 是否将 `t` 规约为 `r`。

## \#check_simp
定义于：`Lean.Parser.checkSimpFailure`

`#check_simp t !~>` 检查 `simp` 是否规约 `t` 失败。

## \#check_tactic
定义于：`Lean.Parser.checkTactic`

`#check_tactic t ~> r by commands` 在目标为 `t` 时运行策略序列 `commands`，并验证结果表达式是否规约为 `r`。

## \#check_tactic_failure
定义于：`Lean.Parser.checkTacticFailure`

`#check_tactic_failure t by tac` 在目标为 `t` 时运行策略 `tac`，并验证其是否失败。

## \#conv
定义于：`Mathlib.Tactic.Conv.«command#conv_=>_»`

命令 `#conv tac => e` 将对 `e` 运行转换策略 `tac`，并显示结果表达式（舍弃证明）。例如，`#conv rw [true_and_iff] => True ∧ False` 显示 `False`。另有多个常用转换策略的简写命令：

* `#whnf e` 是 `#conv whnf => e` 的简写
* `#simp e` 是 `#conv simp => e` 的简写
* `#norm_num e` 是 `#conv norm_num => e` 的简写
* `#push_neg e` 是 `#conv push_neg => e` 的简写

## \#count_heartbeats
定义于：`Mathlib.CountHeartbeats.«command#count_heartbeatsApproximatelyIn__»`

`#count_heartbeats in cmd` 统计封闭命令 `cmd` 使用的心跳次数。使用 `#count_heartbeats` 统计后续所有声明的心跳次数。

此命令最适用于通过 `set_option maxHeartbeats` 为长运行声明设置充足但合理的限制。

若如此操作，请勿将限制设至最低。随着 `simp` 集及库其他功能的演进，其他贡献者可能发现其（可能无关的）变更导致声明超出限制。`count_heartbearts in` 将通过“Try this:”自动建议使用满足条件的最小 `2^k * 200000` 形式的 `set_option maxHeartbeats`。

注意，通过 `IO.getNumHeartbeats` 访问的内部心跳计数器粒度比 `set_option maxHeartbeats` 设置的限制精细 1000 倍。因本命令面向用户，故除以 1000。

可选关键字 `approximately` 将心跳次数向下舍入至最接近的千位。此功能有助于提升测试对心跳次数小变更的稳定性。使用 `#count_heartbeats approximately in cmd` 启用此功能。

## \#count_heartbeats
定义于：`Mathlib.Linter.CountHeartbeats.«command#count_heartbeatsApproximately»`

“countHeartbeats”检查器统计每个声明的心跳次数。

其效果类似于 `#count_heartbeats in xxx`，但应用于所有声明。

注意，检查器仅统计“顶层”声明的心跳次数：其查看 `set_option ... in` 内部，但不查看如 `mutual` 块内部。

便捷符号 `#count_heartbeats` 仅将检查器选项设为 true。

## \#count_heartbeats!
定义于：`Mathlib.CountHeartbeats.«command#count_heartbeats!_In__»`

`#count_heartbeats! in cmd` 运行命令 `10` 次，报告心跳次数范围及标准差。命令 `#count_heartbeats! n in cmd` 运行 `n` 次。

示例：
```lean
#count_heartbeats! in
def f := 37
```
显示信息 `Min: 7 Max: 8 StdDev: 14%`。

## \#discr_tree_key
定义于：`Lean.Parser.discrTreeKeyCmd`

`#discr_tree_key  t` 打印项 `t` 的歧视树键（若为单个标识符，则为该常量的类型）。使用默认键生成配置。

例如：
```
#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
-- bar _ (@OfNat.ofNat Nat _ _)

#discr_tree_simp_key Nat.add_assoc
-- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
```

`#discr_tree_simp_key` 类似 `#discr_tree_key`，但将底层类型视为 simp 引理，即转换为等式并生成左侧键。

## \#discr_tree_simp_key
定义于：`Lean.Parser.discrTreeSimpKeyCmd`

`#discr_tree_key  t` 打印项 `t` 的歧视树键（若为单个标识符，则为该常量的类型）。使用默认键生成配置。

例如：
```lean
#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
-- bar _ (@OfNat.ofNat Nat _ _)

#discr_tree_simp_key Nat.add_assoc
-- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
```

`#discr_tree_simp_key` 类似 `#discr_tree_key`，但将底层类型视为 simp 引理，即转换为等式并生成左侧键。

## \#eval!
定义于：`Lean.Parser.Command.evalBang`

`#eval e` 通过编译和求值来评估表达式 `e`。

* 该命令尝试使用 `ToExpr`、`Repr` 或 `ToString` 实例来打印结果。
* 如果 `e` 是类型为 `m ty` 的单子值，则命令会尝试将单子 `m` 适配到 `#eval` 支持的单子之一，包括 `IO`、`CoreM`、`MetaM`、`TermElabM` 和 `CommandElabM`。用户可通过定义 `MonadEval` 实例来扩展支持的单子列表。

由于不健全性，`#eval` 拒绝评估依赖于 `sorry` 的表达式（即使间接依赖），因为 `sorry` 的存在可能导致运行时不稳定和崩溃。可使用 `#eval! e` 命令覆盖此检查。

选项：
* 若 `eval.pp` 为 true（默认：true），则尝试使用 `ToExpr` 实例以利用常规的漂亮打印机。否则，仅尝试使用 `Repr` 和 `ToString` 实例。
* 若 `eval.type` 为 true（默认：false），则漂亮打印求值值的类型。
* 若 `eval.derive.repr` 为 true（默认：true），则当无其他方式打印结果时，尝试自动派生 `Repr` 实例。

另见：`#reduce e` 用于通过项归约进行求值。

## \#exit
定义于：`Lean.Parser.Command.exit`

## \#explode
定义于：`Mathlib.Explode.«command#explode_»`

`#explode expr` 以逐行格式显示证明项，类似于Fitch风格证明或Metamath证明风格。

例如，分解以下定理：

```lean
#explode iff_of_true
```

生成：

```lean
iff_of_true : ∀ {a b : Prop}, a → b → (a ↔ b)

0│         │ a         ├ Prop
1│         │ b         ├ Prop
2│         │ ha        ├ a
3│         │ hb        ├ b
4│         │ x✝        │ ┌ a
5│4,3      │ ∀I        │ a → b
6│         │ x✝        │ ┌ b
7│6,2      │ ∀I        │ b → a
8│5,7      │ Iff.intro │ a ↔ b
9│0,1,2,3,8│ ∀I        │ ∀ {a b : Prop}, a → b → (a ↔ b)
```

## 概述

`#explode` 命令将定理的主体分解为其组成部分，逐行显示每个表达式构造子。构造子在第三列以某种方式指示，其依赖关系记录在第二列。

主要构造子类型包括：

  - Lambda表达式（`Expr.lam`）。表达式 `fun (h : p) => s` 显示为：
    ```lean
     0│    │ h   │ ┌ p
     1│**  │ **  │ │ q
     2│1,2 │ ∀I  │ ∀ (h : p), q
    ```
    其中 `**` 为通配符，且步骤0到1之间可能有中间步骤。嵌套的lambda表达式可合并，`∀I` 可依赖一系列参数。

  - 应用（`Expr.app`）。表达式 `f a b c` 显示为：
     ```lean
     0│**      │ f  │ A → B → C → D
     1│**      │ a  │ A
     2│**      │ b  │ B
     3│**      │ c  │ C
     1│0,1,2,3 │ ∀E │ D
     ```
     各步骤间可能有中间步骤。特殊情况下，若 `f` 为常量，可省略，显示为：
     ```lean
     0│**    │ a │ A
     1│**    │ b │ B
     2│**    │ c │ C
     3│1,2,3 │ f │ D
     ```

  - Let表达式（`Expr.letE`）无特殊显示方式，但确保在 `let x := v; b` 中先处理 `v` 再处理 `b`，而非先进行zeta归约。这避免lambda合并和应用合并使含 `let` 的证明难以解释。

  - 其他内容（常量、fvars等）显示 `x : X` 为：
    ```lean
    0│  │ x │ X
    ```

## 详细说明

`#explode` 的输出为四列Fitch风格证明图，模仿Metamath的[此类显示](http://us.metamath.org/mpeuni/ru.html)。列头为“步骤”、“假设”、“引用”、“类型”（或Metamath中的“表达式”）：
* **步骤**：证明中每行的递增序号，用于假设字段。
* **假设**：当前步骤的直接子项。这些是当前步骤表达式的子表达式步骤号。对于定理应用，为定理参数；对于全称量词，为所有绑定变量及结论。
* **引用**：应用的定理名称。这在Metamath中明确，但Lean中某些特殊步骤可能因证明项结构不完全匹配而有长名称。
  * 若定理为 `foo (x y : Z) : A x -> B y -> C x y`：
    * 引用字段为 `foo`，
    * `x` 和 `y` 被抑制，因项构造不具趣味，
    * 假设字段引用证明 `A x` 和 `B y` 的步骤。对应证明项如 `@foo x y pA pB`，其中 `pA` 和 `pB` 为子证明。
    * 假设列中，被抑制项被省略，包括应被抑制但未被抑制的项（尤其是lambda参数）。
      TODO：实现配置选项以使用 `_` 而非步骤号表示被抑制项。
  * 若证明项头部为局部常量或lambda，则引用字段显示 `∀E`（全称消除）。例如，`h : A -> B` 和 `ha : A` 通过 `h ha` 证明 `b`，则重新解释为 `∀E h ha`，其中 `∀E` 为（n元）假言推理。
  * 若证明项为lambda，则使用 `∀I`（全称引入）引用lambda体。缩进级别增加，括号包围lambda体的证明，起始于标有lambda变量名及其类型的步骤，终止于 `∀I` 步骤。Metamath无此类步骤，但风格基于一阶逻辑的Fitch证明。

## \#find
定义于：`Mathlib.Tactic.Find.«command#find_»`

## \#find_home
定义于：`«command#find_home!_»`

尽可能在导入层次结构的高处找到命名声明可能存在的位置。
使用 `#find_home!` 将强制移除当前文件。注意，在含 `import Mathlib` 的文件中使用效果最佳。

即使使用 `#find_home! lemma`，当前文件仍可能为唯一建议。原因是 `#find_home!` 扫描当前文件下方的导入图，选择包含出现在 `lemma` 中的声明的文件（排除当前文件本身），并寻找这些文件的所有最小上界。

简单示例，若 `lemma` 在仅导入 `A.lean` 和 `B.lean` 的文件中，且各使用一个引理，则 `#find_home! lemma` 返回当前文件。

## \#find_syntax
定义于：`Mathlib.FindSyntax.«command#find_syntax_Approx»`

`#find_syntax` 命令接受字符串 `str`，并从环境中检索所有包含 `str` 的 `syntax` 项候选。

其还粗略尝试重新生成语法外观：仅为示意语法可能形式，不保证正确性。

可选尾随 `approx`（如 `#find_syntax "∘" approx`）仅意图使测试更稳定：不输出现有语法声明的精确总数，而是返回其向下取整至前一个100的倍数。

## \#guard
定义于: `Lean.Parser.Command.guardCmd`

用于检查表达式求值结果为 `true` 的命令。

`#guard e` 对 `e` 进行细部化，确保其类型为 `Bool` 后求值，并检查结果是否为 `true`。该表达式在细部化时*不会*包含使用 `variable` 声明的变量，因为这些变量无法被求值。

由于使用了强制转换，只要命题 `p` 是可判定的，即可直接书写 `#guard p` 而无需写成 `#guard decide p`。一个推论是，若存在可判定的等式，则可直接书写 `#guard a = b`。需注意这与直接检查 `a` 和 `b` 是否求值为相同对象并不完全相同，因为它使用了 `DecidableEq` 实例来进行求值。

注意：此命令使用非受信任的求值器，因此 `#guard` 通过*并不*代表表达式等于 `true` 的证明。

## \#guard_expr
定义于: `Lean.Parser.Command.guardExprCmd`

用于检查两个表达式相等性的命令。
* `#guard_expr e = e'` 检查 `e` 和 `e'` 在可约透明度下是否定义等价。
* `#guard_expr e =~ e'` 检查 `e` 和 `e'` 在默认透明度下是否定义等价。
* `#guard_expr e =ₛ e'` 检查 `e` 和 `e'` 是否语法等价。
* `#guard_expr e =ₐ e'` 检查 `e` 和 `e'` 是否 α 等价。

此为 `guard_expr` 策略的命令版本。

## \#guard_msgs
定义于: `Lean.guardMsgsCmd`

`/-- ... -/ #guard_msgs in cmd` 捕获命令 `cmd` 生成的消息并检查其是否与文档字符串内容匹配。

基础示例：
```lean
/--
error: 未知标识符 'x'
-/
#guard_msgs in
example : α := x
```
此示例检查是否存在该错误并消费该消息。

默认情况下，该命令捕获所有消息，但可调整过滤条件。例如，仅选择警告：
```lean
/--
warning: 声明使用了 'sorry'
-/
#guard_msgs(warning) in
example : α := sorry
```
或仅选择错误：
```lean
#guard_msgs(error) in
example : α := sorry
```
在前例中，由于未捕获警告，`sorry` 处会产生警告。若需完全丢弃警告，可使用：
```lean
#guard_msgs(error, drop warning) in
example : α := sorry
```

一般情况下，`#guard_msgs` 接受括号内的逗号分隔配置项列表：
```lean
#guard_msgs (configElt,*) in cmd
```
默认配置列表为 `(all, whitespace := normalized, ordering := exact)`。

消息过滤器（按从左到右顺序处理）：
- `info`、`warning`、`error`：捕获指定严重级别的消息。
- `all`：捕获所有消息（默认）。
- `drop info`、`drop warning`、`drop error`：丢弃指定严重级别的消息。
- `drop all`：丢弃所有消息。

空白处理（在修剪首尾空白后）：
- `whitespace := exact` 要求空白完全匹配。
- `whitespace := normalized` 在匹配前将所有换行符转换为空格（默认）。允许折行。
- `whitespace := lax` 在匹配前将空白合并为单个空格。

消息顺序：
- `ordering := exact` 使用消息的精确顺序（默认）。
- `ordering := sorted` 按字典序排序消息。适用于测试命令消息顺序不确定的情况。

例如，`#guard_msgs (error, drop all) in cmd` 表示检查错误并丢弃其他所有消息。

命令细部化器对 `#guard_msgs` 的静态检查有特殊支持。`#guard_msgs` 自身希望捕获静态检查警告，因此将其附加的命令视为顶层命令进行细部化。然而，命令细部化器会为*所有*顶层命令运行静态检查，包括 `#guard_msgs` 自身，这会导致重复或未捕获的静态检查警告。顶层命令细部化器仅在 `#guard_msgs` 不存在时运行静态检查。

## \#help
定义于: `Batteries.Tactic.«command#help_Term+____»`

命令 `#help term` 显示当前环境中定义的所有项语法。详见 `#help cat`。

## \#help
定义于: `Batteries.Tactic.«command#help_Cat+______»`

命令 `#help cat C` 显示当前环境中语法类别 `C` 定义的所有语法。
每个语法的格式如下：
```lean
## first
定义于: `Parser.tactic.first`

  `first | tac | ...` 依次运行每个 `tac` 直至成功，否则失败。
```
引号内为语法的前导标记（如适用），后跟语法的全名（可点击跳转至定义）及文档。

* `#help cat C id` 形式仅显示以 `id` 开头的语法。
* `#help cat+ C` 形式额外显示与所列语法相关联的 `macro` 和 `elab` 信息。

## \#help
定义于: `Batteries.Tactic.«command#help_Command+____»`

命令 `#help command` 显示当前环境中定义的所有命令。详见 `#help cat`。

## \#help
定义于: `Batteries.Tactic.«command#help_AttrAttribute___»`

命令 `#help attribute`（或简写 `#help attr`）显示当前环境中定义的所有属性。
每个属性的格式如下：
```lean
[inline]: 标记定义以始终内联
```
表示 `inline` 是可应用于定义的属性，如 `@[inline] def foo := 1`。（个别属性可能有应用位置限制，详见属性文档。）此处显示属性的 `descr` 字段及文档字符串。

`#help attr id` 形式仅显示以 `id` 开头的属性。

## \#help
定义于: `Batteries.Tactic.«command#help_Note___»`

`#help note "foo"` 搜索标签以 "foo" 开头的所有库注，并按标签字母顺序分组显示。该命令仅显示在导入文件或同一文件中该命令行上方声明的库注。

## \#help
定义于: `Batteries.Tactic.«command#help_Cats___»`

命令 `#help cats` 显示当前环境中定义的所有语法类别。
每个语法的格式如下：
```lean
category command [Lean.Parser.initFn✝]
```
此处语法类别名为 `command`，`Lean.Parser.initFn✝` 为引入该类别声明的名称（常为匿名声明，但可点击跳转至定义）。若存在文档字符串，亦会显示。

`#help cats id` 形式仅显示以 `id` 开头的语法类别。

## \#help
定义于: `Batteries.Tactic.«command#help_Tactic+____»`

命令 `#help tactic` 显示当前环境中定义的所有策略。详见 `#help cat`。

## \#help
定义于: `Batteries.Tactic.«command#help_Conv+____»`

命令 `#help conv` 显示当前环境中定义的所有转换策略。详见 `#help cat`。

## \#help
定义于: `Batteries.Tactic.«command#help_Option___»`

命令 `#help option` 显示当前环境中定义的所有选项。
每个选项的格式如下：
```lean
option pp.all : Bool := false
  （美观打印器）显示强制转换、隐式参数、证明项、全限定名、宇宙，并在美观打印时禁用 β 归约和记法
```
表示 `pp.all` 为可设置为 `Bool` 值的选项，默认值为 `false`。若选项已通过如 `set_option pp.all true` 修改默认值，将显示 `（当前值：true）` 的注释。

`#help option id` 形式仅显示以 `id` 开头的选项。

## \#html
定义于: `ProofWidgets.HtmlCommand.htmlCmd`

在信息视图中显示 `Html` 类型的值。

输入可为纯值或任何 Lean 元编程单子中的计算（如 `CommandElabM Html`）。

## \#import_bumps
定义于: `Mathlib.Linter.MinImports.«command#import_bumps»`

`minImports` 代码检查工具会逐步计算每个文件构建所需的最小导入集。每当检测到新命令需要增加其已计算的（传递）导入时，该工具会发出警告，指出更大的最小导入集。

与相关的 `#min_imports` 命令不同，此检查工具会考虑符号和策略信息。它以增量方式工作，提供更适合拆分文件等信息。

另一重要区别是，`minImports` *检查工具* 从设置选项为 `true` 的位置开始向下计算导入，而 `#min_imports` *命令* 则从命令所在位置向上查看所需的导入。

## \#info_trees
定义于: `Lean.infoTreesCmd`

格式化并打印指定命令的信息树。此功能主要用于调试信息树。

## \#instances
定义于: `Batteries.Tactic.Instances.instancesCmd`

`#instances 项` 打印给定类的所有实例。例如，`#instances Add _` 给出所有 `Add` 实例，`#instances Add Nat` 给出 `Nat` 实例。`项` 可以是出现在 `[...]` 绑定器中的任何类型。

末尾的下划线可省略，`#instances Add` 与 `#instances Add _` 等效；该命令会添加元变量，直至参数不再是函数。

`#instances` 命令与 `#synth` 密切相关，但 `#synth` 执行完整的实例合成算法，而 `#instances` 仅执行查找潜在实例的第一步。

## \#instances
定义于: `Batteries.Tactic.Instances.«command#instances__:_»`

`#instances 项` 打印给定类的所有实例。例如，`#instances Add _` 给出所有 `Add` 实例，`#instances Add Nat` 给出 `Nat` 实例。`项` 可以是出现在 `[...]` 绑定器中的任何类型。

末尾的下划线可省略，`#instances Add` 与 `#instances Add _` 等效；该命令会添加元变量，直至参数不再是函数。

`#instances` 命令与 `#synth` 密切相关，但 `#synth` 执行完整的实例合成算法，而 `#instances` 仅执行查找潜在实例的第一步。

## \#kerodon_tags
定义于: `Mathlib.StacksTag.kerodonTags`

`#kerodon_tags` 命令检索所有具有 `kerodon` 属性的声明。

对每个找到的声明，打印一行：
```
'declaration_name' 对应于标签 'declaration_tag'。
```
变体 `#kerodon_tags!` 还会在每个摘要行后添加定理陈述。

## \#leansearch
定义于: `LeanSearchClient.leansearch_search_cmd`

在 Lean 内搜索 [LeanSearch](https://leansearch.net/)。查询应为以 `.` 或 `?` 结尾的字符串。该命令可作为命令、术语或策略使用，如下例所示。在策略模式下，仅显示有效策略。

```lean
#leansearch "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"

example := #leansearch "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"

example : 3 ≤ 5 := by
  #leansearch "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"
  sorry
```

## \#lint
定义于: `Batteries.Tactic.Lint.«command#lint+-*Only___»`

命令 `#lint` 在当前文件运行代码检查工具（默认情况下）。

`#lint only 某检查工具` 可用于仅运行单个检查工具。

## \#list_linters
定义于: `Batteries.Tactic.Lint.«command#list_linters»`

命令 `#list_linters` 打印所有可用检查工具的列表。

## \#long_instances
定义于: `«command#long_instances_»`

列出所有以 `inst` 开头的长名称实例，按定义它们的模块分组。此功能有助于查找具有荒谬名称的自动命名实例。

使用方式为 `#long_names` 或 `#long_names 100` 指定长度。

## \#long_names
定义于: `«command#long_names_»`

列出所有具有长名称的声明，按定义它们的模块分组。使用方式为 `#long_names` 或 `#long_names 100` 指定长度。

## \#loogle
定义于: `LeanSearchClient.loogle_cmd`

在 Lean 内搜索 [Loogle](https://loogle.lean-lang.org/json)。该命令可作为命令、术语或策略使用，如下例所示。在策略模式下，仅显示有效策略。

```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry

```

## Loogle 使用方式

Loogle 通过多种方式查找定义和引理：

通过常量：
🔍 Real.sin
查找所有陈述中提及正弦函数的引理。

通过引理名称子串：
🔍 "differ"
查找所有名称中包含 "differ" 的引理。

通过子表达式：
🔍 _ * (_ ^ _)
查找所有陈述中某处包含乘积且第二个参数为某次幂的引理。

模式也可非线性，如：
🔍 Real.sqrt ?a * Real.sqrt ?a

若模式含有参数，则参数以任意顺序匹配。以下两者均会找到 List.map：
🔍 (?a -> ?b) -> List ?a -> List ?b
🔍 List ?a -> (?a -> ?b) -> List ?b

通过主要结论：
🔍 |- tsum _ = _ * tsum _
查找所有结论（所有 → 和 ∀ 右侧的子表达式）具有给定形状的引理。

如前所述，若模式含有参数，则参数以任意顺序匹配引理的假设；例如，
🔍 |- _ < _ → tsum _ < tsum _
将找到 tsum_lt_tsum，即使假设 f i < g i 并非最后。

若传递多个搜索过滤器（以逗号分隔），Loogle 将返回匹配所有过滤器的引理。搜索
🔍 Real.sin, "two", tsum, _ * _, _ ^ _, |- _ < _ → _
将查找所有提及常量 Real.sin 和 tsum、名称包含 "two" 子串、类型某处包含乘积和幂，并具有 _ < _ 形式假设的引理（若存在此类引理）。元变量（?a）在每个过滤器中独立分配。

## \#loogle
定义于: `LeanSearchClient.just_loogle_cmd`

在 Lean 内搜索 [Loogle](https://loogle.lean-lang.org/json)。该命令可作为命令、术语或策略使用，如下例所示。在策略模式下，仅显示有效策略。

```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry

```

## Loogle 使用方式

Loogle 通过多种方式查找定义和引理：

通过常量：
🔍 Real.sin
查找所有陈述中提及正弦函数的引理。

通过引理名称子串：
🔍 "differ"
查找所有名称中包含 "differ" 的引理。

通过子表达式：
🔍 _ * (_ ^ _)
查找所有陈述中某处包含乘积且第二个参数为某次幂的引理。

模式也可非线性，如：
🔍 Real.sqrt ?a * Real.sqrt ?a

若模式含有参数，则参数以任意顺序匹配。以下两者均会找到 List.map：
🔍 (?a -> ?b) -> List ?a -> List ?b
🔍 List ?a -> (?a -> ?b) -> List ?b

通过主要结论：
🔍 |- tsum _ = _ * tsum _
查找所有结论（所有 → 和 ∀ 右侧的子表达式）具有给定形状的引理。

如前所述，若模式含有参数，则参数以任意顺序匹配引理的假设；例如，
🔍 |- _ < _ → tsum _ < tsum _
将找到 tsum_lt_tsum，即使假设 f i < g i 并非最后。

若传递多个搜索过滤器（以逗号分隔），Loogle 将返回匹配所有过滤器的引理。搜索
🔍 Real.sin, "two", tsum, _ * _, _ ^ _, |- _ < _ → _
将查找所有提及常量 Real.sin 和 tsum、名称包含 "two" 子串、类型某处包含乘积和幂，并具有 _ < _ 形式假设的引理（若存在此类引理）。元变量（?a）在每个过滤器中独立分配。

## \#min_imports
定义于: `Mathlib.Command.MinImports.minImpsStx`

`#min_imports in cmd` 扫描语法 `cmd` 及其经详细阐述后得到的声明，以寻找一组足以使 `cmd` 正常工作的最小导入集合。

## \#min_imports
定义于: `Mathlib.Command.MinImports.«command#min_importsIn_»`

`#min_imports in cmd` 扫描语法 `cmd` 及其经详细阐述后得到的声明，以寻找一组足以使 `cmd` 正常工作的最小导入集合。

## \#min_imports
定义于: `«command#min_imports»`

尝试通过分析声明计算此文件所需的最小导入集合。

此命令需在文件末尾运行，且不感知语法与策略，因此结果可能仍需手动调整。

## \#minimize_imports
定义于: `«command#minimize_imports»`


## \#moogle
定义于: `LeanSearchClient.moogle_search_cmd`

在 Lean 内部搜索 [Moogle](https://www.moogle.ai/api/search)。  
查询应为以 `.` 或 `?` 结尾的字符串。该命令可作为命令、项或策略使用，如下例所示。在策略模式下，仅显示有效策略。

```lean
#moogle "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"

example := #moogle "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"

example : 3 ≤ 5 := by
  #moogle "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"
  sorry
```

## \#norm_num
定义于: `Mathlib.Tactic.normNumCmd`

基础用法为 `#norm_num e`，其中 `e` 为表达式，将打印 `e` 的 `norm_num` 形式。

语法：`#norm_num` (`only`)? (`[` 化简引理列表 `]`)? `:`? 表达式

此命令接受与 `#simp` 相同的选项。例如可使用 `#norm_num [f, g] : e` 指定额外化简引理（冒号可选但有助于解析）。`only` 限制 `norm_num` 仅使用提供的引理，因此 `#norm_num only : e` 行为类似于 `norm_num1`。

与 `norm_num` 不同，此命令在未进行任何化简时不会失败。

`#norm_num` 理解局部变量，因此可利用其引入参数。

## \#parse
定义于: `Mathlib.GuardExceptions.parseCmd`

`#parse parserFnId => str` 允许捕获解析异常。  
`parserFnId` 为 `ParserFn` 的标识符，`str` 为 `parserFnId` 应解析的字符串。

若解析成功，则输出被记录；若解析失败，则输出被捕获为异常。

无论结果如何，均可使用 `#guard_msgs` 捕获解析错误。

例如，`#parse` 可如下使用：
```lean
/-- error: <input>:1:3: Stacks 标签必须为 4 个字符 -/
#guard_msgs in #parse Mathlib.Stacks.stacksTagFn => "A05"
```

## \#print
定义于: `Batteries.Tactic.printPrefix`

命令 `#print prefix foo` 将打印所有以命名空间 `foo` 开头的定义。

例如，以下命令将打印 `List` 命名空间中的定义：

```lean
#print prefix List
```

`#print prefix` 可通过 `PrintPrefixConfig` 中的标志进行控制，这些标志提供筛选名称与格式化的选项。例如，默认排除内部名称，但可通过配置调整：
```lean
#print prefix (config := {internals := true}) List
```

默认情况下，`#print prefix` 在每个名称后打印类型。可通过设置 `showTypes` 为 `false` 关闭：
```lean
#print prefix (config := {showTypes := false}) List
```

完整标志集可查阅 `Lean.Elab.Command.PrintPrefixConfig` 文档。

## \#print
定义于: `Lean.Parser.Command.printAxioms`


## \#print
定义于: `Lean.Parser.Command.printTacTags`

显示所有可用策略标签及其文档。

## \#print
定义于: `Batteries.Tactic.«command#printOpaques_»`

命令 `#print opaques X` 打印 `X` 依赖的所有不透明定义。

不透明定义包括部分定义与公理。仅列出计算相关上下文中出现的依赖项，证明项内的出现被忽略。此命令有助于判断定义是否可能依赖平台、可能部分或可能不可计算。

例如，`#print opaques Std.HashMap.insert` 显示 `Std.HashMap.insert` 依赖于不透明定义 `System.Platform.getNumBits` 与 `UInt64.toUSize`。因此 `Std.HashMap.insert` 在 32 位或 64 位平台编译时可能有不同行为。

`#print opaques Stream.forIn` 显示 `Stream.forIn` 可能部分，因其依赖部分定义 `Stream.forIn.visit`。若输入流无界，`Stream.forIn` 可能不终止。

`#print opaques Classical.choice` 显示 `Classical.choice` 自身为不透明定义（公理）。而 `#print opaques Classical.axiomOfChoice` 无输出，因其为命题故计算无关（`#print axioms` 显示 `Classical.axiomOfChoice` 依赖 `Classical.choice` 公理）。

## \#print
定义于: `Lean.Parser.Command.printEqns`


## \#print
定义于: `Batteries.Tactic.«command#printDependents___»`

命令 `#print dependents X Y` 打印文件中所有传递依赖于 `X` 或 `Y` 的声明列表。每个声明后显示其体中直接引用且同样依赖 `X` 或 `Y` 的声明列表。

例如，下方 `#print axioms bar'` 显示 `bar'` 依赖 `Classical.choice`，但未说明原因。`#print dependents Classical.choice` 指出 `bar'` 依赖 `Classical.choice` 因其使用 `foo`，而 `foo` 使用 `Classical.em`。`bar` 未被列出因其证明未使用 `Classical.choice`。
```
import Batteries.Tactic.PrintDependents

theorem foo : x = y ∨ x ≠ y := Classical.em _
theorem bar : 1 = 1 ∨ 1 ≠ 1 := by simp
theorem bar' : 1 = 1 ∨ 1 ≠ 1 := foo

#print axioms bar'
-- 'bar'' 依赖公理: [Classical.choice, Quot.sound, propext]

#print dependents Classical.choice
-- foo: Classical.em
-- bar': foo
```

## \#print
定义于: `Lean.Parser.Command.print`


## \#print_fun_prop_theorems
定义于: `Mathlib.Meta.FunProp.«command#print_fun_prop_theorems__»`

打印附加于某函数的所有函数属性的命令。

例如：
```
#print_fun_prop_theorems HAdd.hAdd
```
可能输出：
```
Continuous
  continuous_add, 参数: [4,5], 优先级: 1000
  continuous_add_left, 参数: [5], 优先级: 1000
  continuous_add_right, 参数 [4], 优先级: 1000
  ...
Diferentiable
  Differentiable.add, 参数: [4,5], 优先级: 1000
  Differentiable.add_const, 参数: [4], 优先级: 1000
  Differentiable.const_add, 参数: [5], 优先级: 1000
  ...
```

也可仅查看特定函数属性的定理：
```
#print_fun_prop_theorems HAdd.hAdd Continuous
```

## \#push_neg
定义于: `Mathlib.Tactic.PushNeg.pushNeg`

语法为 `#push_neg e`，其中 `e` 为表达式，将打印 `e` 的 `push_neg` 形式。

`#push_neg` 理解局部变量，因此可利用其引入参数。

## \#reduce
定义于: `Lean.reduceCmd`

`#reduce <表达式>` 将表达式 `<表达式>` 规约至其正规形式。此过程涉及应用规约规则直至无法继续规约。

默认情况下，表达式中的证明与类型不被规约。使用修饰符 `(proofs := true)` 与 `(types := true)` 可规约之。注意命题在 Lean 中为类型。

**警告：** 此操作可能计算量较大，尤其对于复杂表达式。

建议对简单表达式使用 `#eval <表达式>` 进行求值/执行。

## \#reset_min_imports
定义于: `Mathlib.Linter.«command#reset_min_imports»`

`#reset_min_imports` 将当前累积的导入列表设置为空。

## \#sample
定义于: `Plausible.«command#sample_»`

`#sample type`，其中 `type` 具有 `SampleableExt` 的实例，使用递增的大小参数打印十次 `type` 类型的随机值。

```lean
#sample Nat
-- 输出
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- 或其他数字序列

#sample List Int
-- 输出
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- 或其他内容
```

## \#search
定义于: `LeanSearchClient.search_cmd`

根据选项 `leansearchclient.backend` 的设置，在 Lean 中搜索 [Moogle](https://www.moogle.ai/api/search) 或 [LeanSearch](https://leansearch.net/)。查询应为以 `.` 或 `?` 结尾的字符串。该命令可作为命令、项和策略使用，如下例所示。在策略模式下，仅显示有效的策略。

```lean
#search "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"

example := #search "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"

example : 3 ≤ 5 := by
  #search "若自然数 n 小于 m，则 n 的后继小于 m 的后继。"
  sorry
```
在策略模式下，若未提供查询字符串，则基于目标状态查询 [LeanStateSearch](https://premise-search.com)。

## \#show_kind
定义于: `Mathlib.Linter.UnusedTactic.«command#show_kind_»`

`#show_kind tac` 接受一个策略的语法作为输入，并返回该策略语法树头部的 `SyntaxNodeKind`。

输入的语法需要可解析，但可以*极其*简略。例如，要查看 `refine` 策略的 `SyntaxNodeKind`，可以使用：
```lean
#show_kind refine _
```
尾随的下划线 `_` 使语法有效，因为 `refine` 预期有其他内容。

## \#show_unused
定义于: `Batteries.Tactic.ShowUnused.«command#show_unused___»`

`#show_unused decl1 decl2 ..` 将高亮当前文件中未参与声明 `decl1`、`decl2` 等定义的所有定理或定义。结果既显示在 `#show_unused` 的消息中，也显示在声明本身上。
```lean
def foo := 1
def baz := 2
def bar := foo
#show_unused bar -- 高亮 `baz`
```

## \#simp
定义于: `Mathlib.Tactic.Conv.«command#simpOnly_=>__»`

* `#simp => e` 对表达式 `e` 运行 `simp`，并显示简化后的结果表达式。
* `#simp only [lems] => e` 对 `e` 运行 `simp only [lems]`。
* `=>` 是可选的，因此 `#simp e` 和 `#simp only [lems] e` 行为相同。主要用于消除表达式 `e` 与引理之间的歧义。

## \#stacks_tags
定义于: `Mathlib.StacksTag.stacksTags`

`#stacks_tags` 检索所有具有 `stacks` 属性的声明。

对于每个找到的声明，打印一行：
```
'declaration_name' 对应于标签 'declaration_tag'。
```
变体 `#stacks_tags!` 在每个摘要行后添加定理陈述。

## \#string_diagram
定义于: `Mathlib.Tactic.Widget.stringDiagram`

显示给定项的弦图。

示例用法：
```lean
/- 等式定理的弦图。 -/
#string_diagram MonoidalCategory.whisker_exchange

/- 态射的弦图。 -/
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) in
#string_diagram f
```

## \#synth
定义于: `Lean.Parser.Command.synth`


## \#test
定义于: `Plausible.«command#test_»`


## \#time
定义于: `Lean.Parser.timeCmd`

计时命令的详细阐述，并打印结果（以毫秒为单位）。

示例用法：
```lean
set_option maxRecDepth 100000 in
#time example : (List.range 500).length = 500 := rfl
```

## \#trans_imports
定义于: `transImportsStx`

`#trans_imports` 报告当前模块有多少个传递性导入。该命令接受可选的字符串输入：`#trans_imports str` 还显示名称以 `str` 开头的传递性导入模块。

主要用于测试，该命令还接受可选的 `at_most x` 输入：若导入数量不超过 `x`，则消息涉及 `x`，而非实际可能变化的导入数量。

## \#unfold?
定义于: `Mathlib.Tactic.InteractiveUnfold.unfoldCommand`

`#unfold? e` 显示 `e` 的所有展开。在策略模式下，请使用 `unfold?`。

## \#version
定义于: `Lean.Parser.Command.version`

显示当前 Lean 版本。打印 `Lean.versionString`。

## \#where
定义于: `Lean.Parser.Command.where`

`#where` 描述当前作用域的状态。包括当前命名空间、`open` 的命名空间、`universe` 和 `variable` 命令，以及通过 `set_option` 设置的选项。

## \#whnf
定义于: `Mathlib.Tactic.Conv.«command#whnf_»`

命令 `#whnf e` 将 `e` 求值至弱头范式（WHNF），即表达式的“头”被约简至原语——lambda 或 forall，或公理或归纳类型。类似于 `#reduce e`，但不会完全约简表达式，仅暴露第一个构造子。例如：
```lean
open Nat List
set_option pp.notation false
#whnf [1, 2, 3].map succ
-- cons (succ 1) (map succ (cons 2 (cons 3 nil)))
#reduce [1, 2, 3].map succ
-- cons 2 (cons 3 (cons 4 nil))
```
该表达式的头为 `List.cons` 构造子，因此可看出列表非空，但子项 `Nat.succ 1` 和 `List.map Nat.succ (List.cons 2 (List.cons 3 List.nil))` 仍未被求值。`#reduce` 等效于对所有子项使用 `#whnf`。

## \#whnfR
定义于: `Mathlib.Tactic.Conv.«command#whnfR_»`

命令 `#whnfR e` 以可约透明性将 `e` 求值至弱头范式，即使用 `whnf` 但仅展开可约定义。

## \#widget
定义于: `Lean.Widget.widgetCmd`

使用 `#widget <widget>` 显示面板小部件，使用 `#widget <widget> with <props>` 显示带有给定属性（props）的小部件。用于调试小部件。

`<widget>` 的类型必须实现 `Widget.ToModule`，`<props>` 的类型必须实现 `Server.RpcEncodable`。特别是，`<props> : Json` 有效。

## %reset_grind_attrs
定义于: `Lean.Parser.resetGrindAttrs`

重置所有 `grind` 属性。此命令仅供测试使用，不应用于应用程序。

## /-!
定义于: `Lean.Parser.Command.moduleDoc`

`/-! <text> -/` 定义可被文档生成工具显示的*模块文档字符串*。该字符串与文件中的对应位置关联。可在同一文件中多次使用。

## add_aesop_rules
定义于: `Aesop.Frontend.Parser.addRules`


## add_decl_doc
定义于: `Lean.Parser.Command.addDocString`

向现有声明添加文档字符串，替换任何现有文档字符串。提供的文档字符串应作为 `add_decl_doc` 命令的文档字符串编写，如：
```
/-- 我的新文档字符串 -/
add_decl_doc oldDeclaration
```

这适用于自动生成的声明，其源代码中无处编写文档字符串。

结构中的父投影即为一例：
```lean
structure Triple (α β γ : Type) extends Prod α β where
  thrd : γ

/-- 提取三元组的前两个投影。 -/
add_decl_doc Triple.toProd
```

文档仅可添加至同一模块中的声明。

## alias
定义于: `Batteries.Tactic.Alias.alias`

命令 `alias name := target` 创建 `target` 的同义词，使用给定名称。

命令 `alias ⟨fwd, rev⟩ := target` 为 iff 定理的正向和反向创建同义词。若仅需一个方向，使用 `_`。

这些命令接受所有与`def`和`theorem`相同的修饰符和属性。

## alias
定义于：`Batteries.Tactic.Alias.aliasLR`

命令`alias name := target`创建`target`的同义词`name`。

命令`alias ⟨fwd, rev⟩ := target`为iff定理的正向和反向创建同义词。如果只需要一个方向，使用`_`。

这些命令接受所有与`def`和`theorem`相同的修饰符和属性。

## assert_exists
定义于：`commandAssert_exists_`

`assert_exists n`是一个用户命令，用于断言当前导入作用域中存在名为`n`的声明。

注意使用名称（如`Rat`）而非符号（如`ℚ`）。

## assert_no_sorry
定义于：`commandAssert_no_sorry_`

如果给定标识符使用了`sorryAx`，则抛出错误。

## assert_not_exists
定义于：`commandAssert_not_exists_`

`assert_not_exists d₁ d₂ ... dₙ`是一个用户命令，用于断言当前导入作用域中*不存在*名为`d₁ d₂ ... dₙ`的声明。

注意使用名称（如`Rat`）而非符号（如`ℚ`）。

在mathlib中可能（谨慎地！）用于强制执行某些文件相互独立的计划。

如果在开发mathlib时遇到`assert_not_exists`命令的错误，可能是因为您向文件引入了新的导入依赖项。

在这种情况下，您应重构您的工作（例如通过创建新文件而非向现有文件添加导入）。您*不应*未经事先仔细讨论就删除`assert_not_exists`语句。

`assert_not_exists`语句通常应位于文件顶部，模块文档之后。

## assert_not_imported
定义于：`commandAssert_not_imported_`

`assert_not_imported m₁ m₂ ... mₙ`检查模块`m₁ m₂ ... mₙ`中的每一个都不在当前文件的传递导入中。

该命令当前不检查模块`m₁ m₂ ... mₙ`是否实际存在。

## attribute
定义于：`Lean.Parser.Command.attribute`


## binder_predicate
定义于：`Lean.Parser.Command.binderPredicate`

声明一个绑定器谓词。例如：
```lean
binder_predicate x " > " y:term => `($x > $y)
```

## builtin_dsimproc
定义于：`Lean.Parser.«command__Builtin_dsimproc__[_]_(_):=_»`

一个内置的defeq简化过程。

## builtin_dsimproc_decl
定义于：`Lean.Parser.«command_Builtin_dsimproc_decl_(_):=_»`

一个内置的defeq简化过程声明。

## builtin_grind_propagator
定义于：`Lean.Parser.«command_Builtin_grind_propagator____:=_»`

一个为`grind`策略设计的内置传播器。

## builtin_simproc
定义于：`Lean.Parser.«command__Builtin_simproc__[_]_(_):=_»`

一个内置的简化过程。

## builtin_simproc_decl
定义于：`Lean.Parser.«command_Builtin_simproc_decl_(_):=_»`

一个内置的简化过程声明。

## builtin_simproc_pattern%
定义于：`Lean.Parser.simprocPatternBuiltin`

将模式与内置简化过程关联的辅助命令。

## class
定义于：`Lean.Parser.Command.classAbbrev`

将
```
class abbrev C <params> := D_1, ..., D_n
```
扩展为
```
class C <params> extends D_1, ..., D_n
attribute [instance] C.mk
```

## compile_def%
定义于：`Mathlib.Util.«commandCompile_def%_»`

`compile_def% Foo.foo`为定义`Foo.foo`添加编译代码。这可用于类型类投影或像`List._sizeOf_1`这样的定义，默认情况下Lean不会为这些生成编译代码（因为99%的时间不会使用它们）。

## compile_inductive%
定义于：`Mathlib.Util.«commandCompile_inductive%_»`

`compile_inductive% Foo`为递归器`Foo.rec`创建编译代码，以便在定义中使用`Foo.rec`而无需将定义标记为`noncomputable`。

## count_heartbeats
定义于：`Mathlib.CountHeartbeats.commandCount_heartbeats`

`count_heartbeats`自"2025-01-12"起已弃用，推荐使用`#count_heartbeats`

## declare_aesop_rule_sets
定义于：`Aesop.Frontend.Parser.declareRuleSets`


## declare_bitwise_int_theorems
定义于：`commandDeclare_bitwise_int_theorems__`


## declare_bitwise_uint_theorems
定义于：`commandDeclare_bitwise_uint_theorems__`


## declare_command_config_elab
定义于：`Lean.Elab.Tactic.commandConfigElab`


## declare_config_elab
定义于：`Lean.Elab.Tactic.configElab`


## declare_int_theorems
定义于：`commandDeclare_int_theorems__`


## declare_simp_like_tactic
定义于：`Lean.Parser.Tactic.declareSimpLikeTactic`


## declare_syntax_cat
定义于：`Lean.Parser.Command.syntaxCat`


## declare_uint_simprocs
定义于：`commandDeclare_uint_simprocs_`


## declare_uint_theorems
定义于：`commandDeclare_uint_theorems__`


## deprecate
定义于：`Mathlib.Tactic.DeprecateTo.commandDeprecateTo______`

编写
```lean
deprecate to new_name new_name₂ ... new_nameₙ
theorem old_name : True := .intro
```
其中`new_name new_name₂ ... new_nameₙ`是一系列标识符，生成`Try this`建议：
```lean
theorem new_name : True := .intro

@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name

@[deprecated (since := "YYYY-MM-DD")] alias old_name₂ := new_name₂
...

@[deprecated (since := "YYYY-MM-DD")] alias old_nameₙ := new_nameₙ
```
其中`old_name old_name₂ ... old_nameₙ`是初始命令生成的未黑名单声明。

"YYYY-MM-DD"条目是今天的日期，自动填充。

`deprecate to`努力将`old_name`（“可见”名称）与用户生成的第一个标识符`new_name`匹配。旧的自动生成声明`old_name₂ ... old_nameₙ`按字母顺序检索。在初始声明最多生成一个非黑名单声明的情况下，字母排序无关紧要。

技术上，该命令还接受一个可选的`String`参数来填充`since`中的日期。但主要用于调试目的，因为变量日期会导致测试时间依赖。

## deriving
定义于：`Lean.Parser.Command.deriving`


## dsimproc
定义于：`Lean.Parser.«command__Dsimproc__[_]_(_):=_»`

类似于`simproc`，但结果表达式必须与输入表达式在定义上相等。

## dsimproc_decl
定义于：`Lean.Parser.«command_Dsimproc_decl_(_):=_»`

用户定义的defeq简化过程声明。要在`simp`策略中激活此过程，必须将其作为参数提供，或使用`attribute`命令设置其`[simproc]`属性。

## elab
定义于：`Lean.Parser.Command.elab`


## elab_rules
定义于：`Lean.Parser.Command.elab_rules`


## elab_stx_quot
定义于：`Lean.Elab.Term.Quotation.commandElab_stx_quot_`


## end
定义于：`Lean.Parser.Command.end`

`end`关闭`section`或`namespace`作用域。如果作用域名为`<id>`，则必须使用`end <id>`关闭。文件末尾的`end`命令是可选的。

## erase_aesop_rules
定义于：`Aesop.Frontend.Parser.eraseRules`


## export
定义于：`Lean.Parser.Command.export`

将其他命名空间的名称添加到当前命名空间。

命令`export Some.Namespace (name₁ name₂)`使`name₁`和`name₂`：

- 在当前命名空间中无需前缀`Some.Namespace`即可见，类似`open`，且
- 从当前命名空间`N`外部可见为`N.name₁`和`N.name₂`。

示例：

```lean
namespace Morning.Sky
  def star := "venus"
end Morning.Sky

namespace Evening.Sky
  export Morning.Sky (star)
  -- `star`现在在作用域内
  #check star
end Evening.Sky

-- `star`在`Evening.Sky`中可见
#check Evening.Sky.star
```

## export
定义于：`Lean.Elab.Command.exportPrivate`

命令`export private a b c in foo bar`类似于`open private`，但不会在当前作用域内打开它们，而是创建指向私有定义的公共别名。该定义将存在于原始位置和名称，如同最初未使用`private`关键字。

它还会在提供的短名称下打开新创建的别名定义，例如
`open private`。
也可以指定模块，例如
`export private a b c from Other.Module`。

## extend_docs
定义于：`Mathlib.Tactic.ExtendDocs.commandExtend_docs__Before__After_`

`extend_docs <declName> before <prefix_string> after <suffix_string>` 通过添加 `<prefix_string>` 在前和 `<suffix_string>` 在后，扩展 `<declName>` 的文档。

## gen_injective_theorems%
定义于：`Lean.Parser.Command.genInjectiveTheorems`

这是一个用于为在 `Prelude.lean` 中定义的归纳类型生成构造函数可逆性定理的辅助命令。仅用于引导目的。

## grind_pattern
定义于：`Lean.Parser.Command.grindPattern`


## grind_propagator
定义于：`Lean.Parser.«command_Grind_propagator___(_):=_»`

用户为 `grind` 策略定义的自定义传播器。

## guard_min_heartbeats
定义于：`Mathlib.CountHeartbeats.commandGuard_min_heartbeats_In__`

守护在封闭命令中使用的最小心跳数。

这在调试和最小化慢速声明示例的上下文中最为有用。通过守护慢速声明中使用的心跳数，如果最小化步骤消除了慢速行为，将生成错误消息。

默认的最小心跳数是 `maxHeartbeats` 的值（通常为 200000）。或者，可以使用语法 `guard_min_heartbeats n in cmd` 指定要守护的心跳数。

## import
定义于：`Lean.Parser.Command.import`


## in
定义于：`Lean.Parser.Command.in`


## include
定义于：`Lean.Parser.Command.include`

`include eeny meeny` 指示 Lean 在当前节剩余的所有定理中包含节 `variable`s `eeny` 和 `meeny`，与默认根据定理头中的使用情况有条件包含变量的行为不同。其他命令不受影响。`include` 通常后跟 `in theorem ...` 以将包含限制在后续声明中。

## init_grind_norm
定义于：`Lean.Parser.Command.initGrindNorm`


## init_quot
定义于：`Lean.Parser.Command.init_quot`


## initialize_simps_projections
定义于：`Lean.Parser.Command.initialize_simps_projections`

此命令允许自定义由 `simps` 生成的引理。

默认情况下，用 `@[simps]` 标记结构 `MyStruct` 的元素 `myObj` 的定义会为 `MyStruct` 的每个投影 `myProj` 生成一个 `@[simp]` 引理 `myObj_myProj`。此一般规则有一些例外：
* 对于代数结构，如果可用，我们将自动使用符号（如 `Mul`）作为投影。
* 默认情况下，对父结构的投影不是默认投影，但所有携带数据的字段都是（包括父结构中的字段）。

此默认行为可通过以下方式自定义：
* 通过运行 `initialize_simps_projections MulEquiv (-invFun)` 默认禁用投影。这将确保不为该投影生成简化引理，除非用户显式指定此投影（如 `@[simps invFun] def myEquiv : MulEquiv _ _ := _`）。
* 反之，通过运行 `initialize_simps_projections MulEquiv (+toEquiv)` 默认启用投影。
* 可以通过例如 `initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)` 指定自定义名称。
* 如果希望将投影名称作为生成引理名称的前缀，可以使用 `as_prefix fieldName`：
  `initialize_simps_projections MulEquiv (toFun → coe, as_prefix coe)`
  请注意，这不影响投影名称的解析：如果有一个声明 `foo`，并且希望按顺序应用投影 `snd`、`coe`（作为前缀）和 `fst`，可以运行 `@[simps snd_coe_fst] def foo ...`，这将生成一个名为 `coe_foo_snd_fst` 的引理。

以下是一些额外信息：
  * 运行 `initialize_simps_projections?`（或 `set_option trace.simps.verbose true`）查看生成的投影。
* 不带参数运行 `initialize_simps_projections MyStruct` 不是必需的，如果在声明结构后添加 `@[simps]`，则效果相同。
* 建议在与结构声明相同的文件中调用 `@[simps]` 或 `initialize_simps_projections`。否则，投影可能在不同文件中多次生成。

一些常见用途：
* 如果定义了一个新的类似同态的结构（如 `MulHom`），只需在定义 `DFunLike` 实例（或暗示 `DFunLike` 实例的实例）后运行 `initialize_simps_projections`。
  ```
    instance {mM : Mul M} {mN : Mul N} : FunLike (MulHom M N) M N := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  这将为每个声明 `foo` 生成 `foo_apply` 引理。
* 如果更喜欢表示函数间等式的 `coe_foo` 引理，请使用
  `initialize_simps_projections MulHom (toFun → coe, as_prefix coe)`
  在这种情况下，每当调用 `@[simps]` 时，必须使用 `@[simps -fullyApplied]`。
* 也可以初始化为同时使用两者，此时必须通过以下方式之一选择默认使用的：
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -apply)
  ```
  在第一种情况下，可以使用 `@[simps, simps -fullyApplied coe]` 获取两个引理，在第二种情况下，可以使用 `@[simps -fullyApplied, simps apply]` 获取两个引理。
* 如果声明了一个新的类似同态的结构（如 `RelEmbedding`），则 `initialize_simps_projections` 将自动找到任何将用作 `toFun` 字段默认投影的 `DFunLike` 强制转换。
  ```
    initialize_simps_projections relEmbedding (toFun → apply)
  ```
* 如果有一个类似同构的结构（如 `Equiv`），通常希望为逆定义自定义投影：
  ```
    def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)
  ```

## initialize_simps_projections?
定义于：`Lean.Parser.Command.commandInitialize_simps_projections?_`

此命令允许自定义由 `simps` 生成的引理。

默认情况下，用 `@[simps]` 标记结构 `MyStruct` 的元素 `myObj` 的定义会为 `MyStruct` 的每个投影 `myProj` 生成一个 `@[simp]` 引理 `myObj_myProj`。此一般规则有一些例外：
* 对于代数结构，如果可用，我们将自动使用符号（如 `Mul`）作为投影。
* 默认情况下，对父结构的投影不是默认投影，但所有携带数据的字段都是（包括父结构中的字段）。

此默认行为可通过以下方式自定义：
* 通过运行 `initialize_simps_projections MulEquiv (-invFun)` 默认禁用投影。这将确保不为该投影生成简化引理，除非用户显式指定此投影（如 `@[simps invFun] def myEquiv : MulEquiv _ _ := _`）。
* 反之，通过运行 `initialize_simps_projections MulEquiv (+toEquiv)` 默认启用投影。
* 可以通过例如 `initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)` 指定自定义名称。
* 如果希望将投影名称作为生成引理名称的前缀，可以使用 `as_prefix fieldName`：
  `initialize_simps_projections MulEquiv (toFun → coe, as_prefix coe)`
  请注意，这不影响投影名称的解析：如果有一个声明 `foo`，并且希望按顺序应用投影 `snd`、`coe`（作为前缀）和 `fst`，可以运行 `@[simps snd_coe_fst] def foo ...`，这将生成一个名为 `coe_foo_snd_fst` 的引理。

## irreducible_def
定义于：`Lean.Elab.Command.command_Irreducible_def____`

引入一个不可约定义。`irreducible_def foo := 42` 生成一个常量 `foo : Nat` 以及一个定理 `foo_def : foo = 42`。

## library_note
定义于：`Batteries.Util.LibraryNote.commandLibrary_note___`

```
library_note "some tag" /--
... 一些说明 ...
-/
```
创建一个新的“库注记”，之后可以在文档注释中通过
```
-- 参见注记 [some tag]
```
进行交叉引用。使用 `#help note "some tag"` 在信息视图中显示所有带有标签 `"some tag"` 的注记。该命令可从 `Batteries.Tactic.HelpCmd` 导入。

## lrat_proof
定义于：`Mathlib.Tactic.Sat.commandLrat_proof_Example____`

一个用于从 CNF / LRAT 文件生成 SAT 证明的宏。这些文件在 SAT 社区中常用于编写证明。

`lrat_proof` 命令的输入是要定义的定理名称，以及陈述（以 CNF 格式书写）和证明（以 LRAT 格式书写）。例如：
```lean
lrat_proof foo
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
```
将生成定理：
```lean
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* 悬停在 `foo` 上可查看定理陈述。
* 可使用 `example` 关键字替代 `foo` 以避免生成定理。
* 可使用 `include_str` 宏代替字符串以从磁盘加载 CNF / LRAT 文件。

## macro
定义于：`Lean.Parser.Command.macro`


## macro_rules
定义于：`Lean.Parser.Command.macro_rules`


## mk_iff_of_inductive_prop
定义于：`Mathlib.Tactic.MkIff.mkIffOfInductiveProp`

`mk_iff_of_inductive_prop i r` 为归纳定义的命题 `i` 创建 `iff` 规则。新规则 `r` 的形如 `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`，其中 `ps` 是类型参数，`is` 是索引，`j` 遍历所有可能的构造子，`cs` 是各构造子的参数，`is = cs` 是各构造子对索引的实例化。

在每种情况下，当对应的等式仅为某个索引 `i` 的 `c = i` 时，我们移除构造子参数（即 `cs`）。

例如，对 `List.Chain` 使用 `mk_iff_of_inductive_prop` 生成：
```lean
∀ { α : Type*} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃(b : α) (l' : List α), R a b ∧ Chain R b l ∧ l = b :: l'
```

另见用户属性 `mk_iff`。

## mutual
定义于：`Lean.Parser.Command.mutual`


## namespace
定义于：`Lean.Parser.Command.namespace`

`namespace <id>` 打开一个带有标签 `<id>` 的区段，该区段会影响区段内的命名和名称解析：
* 声明名称会被前缀化：在命名空间 `Nat` 内部的 `def seventeen : ℕ := 17` 会被赋予全名 `Nat.seventeen`。
* 由 `export` 声明引入的名称也会被标识符前缀化。
* 所有以 `<id>.` 开头的名称在命名空间内无需前缀即可使用。这些名称优先于由外部命名空间或 `open` 引入的名称。
* 在命名空间内部，声明可以是 `protected` 的，这会排除它们在打开命名空间时的影响。

与 `section` 类似，命名空间可嵌套，其作用域由对应的 `end <id>` 或文件末尾终止。

`namespace` 也像 `section` 一样界定 `variable`、`open` 及其他作用域命令的范围。

## noncomputable
定义于：`Lean.Parser.Command.noncomputableSection`


## norm_cast_add_elim
定义于：`Lean.Parser.Tactic.normCastAddElim`

`norm_cast_add_elim foo` 将 `foo` 注册为 `norm_cast` 中的消除引理。

## notation
定义于：`Lean.Parser.Command.notation`


## notation3
定义于：`Mathlib.Notation3.notation3`

`notation3` 使用 Lean-3 风格的语法声明记法。

示例：
```lean
notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r
notation3 "MyList[" (x", "* => foldr (a b => MyList.cons a b) MyList.nil) "]" => x
```
默认情况下，记法无法提及使用 `variable` 定义的任何变量，但 `local notation3` 可使用此类局部变量。

使用 `notation3 (prettyPrint := false)` 阻止命令为记法生成美化打印器。

该命令可用于 mathlib4，但其未来不确定，主要为向后兼容而创建。

## omit
定义于：`Lean.Parser.Command.omit`

`omit` 指示 Lean 不包含先前 `include` 的变量。除变量名外，还可通过类型使用语法 `omit [TypeOfInst]` 引用类型类实例变量，此时将省略所有与给定类型统一的实例变量。`omit` 通常应与 `in` 结合使用以保持区段结构简单。

## open
定义于：`Lean.Elab.Command.openPrivate`

命令 `open private a b c in foo bar` 将在声明 `foo` 和 `bar` 中查找名为 `a`、`b`、`c` 的私有定义，并在当前作用域中打开它们。这不会使定义公开，而是让它们通过短名称 `a` 在当前区段内可访问，而非无法直接输入的内部名称（如 `_private.Other.Module.0.Other.Namespace.foo.a`）。

也可通过 `open private a b c from Other.Module` 指定模块。

## open
定义于：`Lean.Parser.Command.open`

使其他命名空间的名称无需前缀即可见。

通过 `open` 可用的名称在当前 `section` 或 `namespace` 块内可见。这简化了对（类型）定义和定理的引用，但需注意，也可能使来自其他命名空间的[作用域实例]、记法和属性可用。

`open` 命令有几种不同的使用方式：

* `open Some.Namespace.Path1 Some.Namespace.Path2` 使得 `Some.Namespace.Path1` 和 `Some.Namespace.Path2` 中的所有非受保护名称无需前缀即可使用，因此 `Some.Namespace.Path1.x` 和 `Some.Namespace.Path2.y` 可以直接通过 `x` 和 `y` 来引用。

* `open Some.Namespace.Path hiding def1 def2` 打开 `Some.Namespace.Path` 中除 `def1` 和 `def2` 外的所有非受保护名称。

* `open Some.Namespace.Path (def1 def2)` 仅使 `Some.Namespace.Path.def1` 和 `Some.Namespace.Path.def2` 无需完整前缀即可使用，而 `Some.Namespace.Path.def3` 不会受到影响。

  即使 `def1` 和 `def2` 是 `protected` 的，此方法仍有效。

* `open Some.Namespace.Path renaming def1 → def1', def2 → def2'` 与 `open Some.Namespace.Path (def1 def2)` 类似，但将 `def1`/`def2` 的名称更改为 `def1'`/`def2'`。

  即使 `def1` 和 `def2` 是 `protected` 的，此方法仍有效。

* `open scoped Some.Namespace.Path1 Some.Namespace.Path2` **仅** 打开来自 `Namespace1` 和 `Namespace2` 的[作用域实例]、符号和属性；**不** 提供其他任何名称。

* `open <上述任意 open 形式> in` 使得 `open` 的名称仅在下一个命令或表达式中可见。

[作用域实例]: https://lean-lang.org/theorem_proving_in_lean4/type_classes.html#scoped-instances
(定理证明中的作用域实例)


示例：

```lean
/-- SKI组合子 https://zh.wikipedia.org/wiki/SKI组合子演算 -/
namespace Combinator.Calculus
  def I (a : α) : α := a
  def K (a : α) : β → α := fun _ => a
  def S (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
end Combinator.Calculus

section
  -- 打开 `Combinator.Calculus` 下的所有内容，即 `I`、`K` 和 `S`，直到该 section 结束
  open Combinator.Calculus

  theorem SKx_eq_K : S K x = I := rfl
end

-- 仅对下一个命令（此处为下一个 `theorem`）打开 `Combinator.Calculus` 下的所有内容
open Combinator.Calculus in
theorem SKx_eq_K' : S K x = I := rfl

section
  -- 仅打开 `Combinator.Calculus` 下的 `S` 和 `K`
  open Combinator.Calculus (S K)

  theorem SKxy_eq_y : S K x y = y := rfl

  -- `I` 不在作用域中，必须使用其完整路径
  theorem SKxy_eq_Iy : S K x y = Combinator.Calculus.I y := rfl
end

section
  open Combinator.Calculus
    renaming
      I → identity,
      K → konstant

  #check identity
  #check konstant
end

section
  open Combinator.Calculus
    hiding S

  #check I
  #check K
end

section
  namespace Demo
    inductive MyType
    | val

    namespace N1
      scoped infix:68 " ≋ " => BEq.beq

      scoped instance : BEq MyType where
        beq _ _ := true

      def Alias := MyType
    end N1
  end Demo

  -- 将 `≋` 和实例引入作用域，但不引入 `Alias`
  open scoped Demo.N1

  #check Demo.MyType.val == Demo.MyType.val
  #check Demo.MyType.val ≋ Demo.MyType.val
  -- #check Alias -- 未知标识符 'Alias'
end
```

## proof_wanted
定义于：`«proof_wanted»`

此证明将是对库的一个欢迎贡献！

`proof_wanted` 声明的语法与 `theorem` 类似，但不包含 `:=` 或证明。Lean 会检查 `proof_wanted` 声明是否格式正确（例如确保所有提到的名称都在作用域内，且定理陈述是有效的命题），但它们随后会被丢弃。这意味着它们不能作为公理使用。

典型用法：
```lean
@[simp] proof_wanted empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none
```

## recall
定义于：`Mathlib.Tactic.Recall.recall`

`recall` 命令重新声明先前的定义以作说明之用。
这对于以说明性方式呈现某些理论的 Lean 文件非常有用。

该命令的语法与 `def` 相同，因此所有常规功能均可使用。
```lean
recall List.cons_append (a : α) (as bs : List α) : (a :: as) ++ bs = a :: (as ++ bs) := rfl
```
此外，可以省略主体。
```lean
recall Nat.add_comm (n m : Nat) : n + m = m + n
```

该命令验证新定义是否类型检查，以及提供的类型和值是否与原始声明在定义上相等。然而，这不会捕获某些细节（如绑定器），因此以下内容不会报错。
```lean
recall Nat.add_comm {n m : Nat} : n + m = m + n
```

## recommended_spelling
定义于：`Lean.Parser.Command.recommended_spelling`

记录标识符中符号的推荐拼写。

定理通常应根据其陈述系统命名，而非创造性命名。非标识符符号应始终通过其推荐拼写一致引用。

```
/-- 一些额外信息 -/
recommended_spelling "and" for "∧" in [And, «term_∧_»]
```

将执行以下操作：
* 在 `And` 和 `∧` 的文档字符串末尾添加句子“`∧` 在标识符中的推荐拼写为 `and`（一些额外信息）”。如果额外信息超过一行，它将放置在句子下方而非括号内。
* 将此信息注册到环境扩展中，以便后续生成包含所有推荐拼写的表格。

您可以将推荐拼写附加到任意多个声明。建议将推荐拼写附加到所有相关解析器以及解析器所指的声明（如果存在此类声明）。注意 `inherit_doc` 属性*不会*复制推荐拼写，因此即使 `∧` 的解析器使用 `@[inherit_doc And]`，我们也必须将推荐拼写附加到 `And` 和 `«term_∧_»` 两者。

`syntax`、`macro`、`elab` 和 `notation` 命令接受 `(name := parserName)` 选项以将名称分配给创建的解析器，从而无需猜测自动生成的名称。`syntax`、`macro` 和 `elab` 命令可悬停以查看解析器名称。

对于包含标识符的复杂符号，约定是使用示例标识符而非其他占位符。以下是遵循此约定的示例：
```lean
recommended_spelling "singleton" for "[a]" in [List.cons, «term[_]»]
```
使用 `[·]` 或 `[⋯]` 或 `[…]` 代替 `[a]` 将违反约定。当将推荐拼写附加到已有示例的符号文档时，尽量重用文档中选择的标识符名称以保持一致性。

## register_builtin_option
定义于：`Lean.Option.registerBuiltinOption`


## register_hint
定义于：`Mathlib.Tactic.Hint.registerHintStx`

注册一个与 `hint` 策略一起使用的策略，例如 `register_hint simp_all`。

## register_label_attr
定义于：`Lean.Parser.Command.registerLabelAttr`

初始化新的“标签”属性。
使用 `Lean.labelled` 可检索标记有此属性的声明。

## register_option
定义于：`Lean.Option.registerOption`


## register_simp_attr
定义于：`Lean.Parser.Command.registerSimpAttr`


## register_tactic_tag
定义于：`Lean.Parser.Command.register_tactic_tag`

注册策略标签，保存其面向用户的名称和文档字符串。

文档生成工具可使用策略标签对相关策略进行分类。

## run_cmd
定义于：`Lean.runCmd`

`run_cmd doSeq` 命令在 `CommandElabM Unit` 中执行代码。
这与 `#eval show CommandElabM Unit from discard do doSeq` 相同。

## run_elab
定义于：`Lean.runElab`

`run_elab doSeq` 命令在 `TermElabM Unit` 中执行代码。
这与 `#eval show TermElabM Unit from discard do doSeq` 相同。

## run_meta
定义于：`Lean.runMeta`

`run_meta doSeq` 命令在 `MetaM Unit` 中执行代码。
这与 `#eval show MetaM Unit from do discard doSeq` 相同。

（这实际上是 `run_elab` 的同义词，因为 `MetaM` 可提升至 `TermElabM`。）

## scoped
定义于：`Mathlib.Tactic.scopedNS`

`scoped[NS]` 类似于属性和符号上的 `scoped` 修饰符，但它在指定命名空间中作用语法，而非当前命名空间。
```lean
scoped[Matrix] postfix:1024 "ᵀ" => Matrix.transpose
-- 声明 `ᵀ` 作为矩阵转置的符号
-- 仅在 `open Matrix` 或 `open scoped Matrix` 时可访问。

namespace Nat

scoped[Nat.Count] attribute [instance] CountSet.fintype
-- 将定义 Nat.CountSet.fintype 设为实例，
-- 但仅在 `Nat.Count` 打开时生效
```

## seal
Defined in: `Lean.Parser.commandSeal__`

`seal foo` 命令确保 `foo` 的定义被密封，即标记为 `[irreducible]`。
此命令在需要防止证明过程中对 `foo` 进行规约的上下文中尤为有用。

在功能上，`seal foo` 等同于 `attribute [local irreducible] foo`。
该属性指定 `foo` 仅在局部作用域内被视为不可规约，
这有助于在保持所需抽象层级的同时不影响全局设置。

## section
Defined in: `Lean.Parser.Command.section`

`section`/`end` 对用于界定 `variable`、`include`、`open`、`set_option` 和 `local`
命令的作用域。节（section）可嵌套。`section <id>` 为节提供标签，需与匹配的 `end` 一起出现。
无论是否使用标签，`end` 均可省略，此时节将在文件末尾关闭。

## set_option
Defined in: `Lean.Parser.Command.set_option`

`set_option <id> <value>` 将选项 `<id>` 设为 `<value>`。根据选项类型的不同，
值可为 `true`、`false`、字符串或数字。选项用于配置 Lean 及用户定义扩展的行为。
该设置将保持有效直至当前 `section` 或 `namespace` 结束，或文件结束。
输入 `<id>` 时可使用自动补全以列出可用选项。

`set_option <id> <value> in <command>` 将选项设为仅对单个命令生效：
```lean
set_option pp.all true in
#check 1 + 1
```
类似地，`set_option <id> <value> in` 也可在项和策略内部使用，以仅对单个项或策略设置选项。

## set_premise_selector
Defined in: `Lean.setPremiseSelectorCmd`

指定前提选择引擎。
注意 Lean 未内置默认前提选择引擎，
因此此命令需结合提供引擎的下游包使用。

## show_panel_widgets
Defined in: `Lean.Widget.showPanelWidgetsCmd`

使用 `show_panel_widgets [<widget>]` 标记应始终显示 `<widget>`，
包括在下游模块中。

`<widget>` 的类型必须实现 `Widget.ToModule`，
且 `<props>` 的类型必须实现 `Server.RpcEncodable`。
特别地，`<props> : Json` 适用。

使用 `show_panel_widgets [<widget> with <props>]`
指定应传递给 widget 的参数 `<props>`。

使用 `show_panel_widgets [local <widget> (with <props>)?]` 标记仅在当前节、命名空间或文件中显示。

使用 `show_panel_widgets [scoped <widget> (with <props>)?]` 标记仅当当前命名空间打开时显示。

使用 `show_panel_widgets [-<widget>]` 临时隐藏先前显示的 widget，
仅在当前节、命名空间或文件内有效。
注意无法永久移除，即 `-<widget>` 对下游模块无影响。

## simproc
Defined in: `Lean.Parser.«command__Simproc__[_]_(_):=_»`

用户定义的简化过程，供 `simp` 策略及其变体使用。示例如下：
```lean
theorem and_false_eq {p : Prop} (q : Prop) (h : p = False) : (p ∧ q) = False := by simp [*]

open Lean Meta Simp
simproc ↓ shortCircuitAnd (And _ _) := fun e => do
  let_expr And p q := e | return .continue
  let r ← simp p
  let_expr False := r.expr | return .continue
  let proof ← mkAppM ``and_false_eq #[q, (← r.getProof)]
  return .done { expr := r.expr, proof? := some proof }
```
当 `simp` 策略发现形如 `And _ _` 的项时，会调用 `shortCircuitAnd`。
简化过程存储于（不完美的）判别树中。
过程**不应**假设项 `e` 完美匹配给定模式。
简化过程主体必须具有 `Simproc` 类型，即 `Expr → SimpM Step` 的别名。
使用修饰符 `↓` 在过程名前可指示简化器在子表达式简化前应用该过程。
简化过程亦可设为作用域或局部。

## simproc_decl
Defined in: `Lean.Parser.«command_Simproc_decl_(_):=_»`

用户定义的简化过程声明。需通过提供该过程作为参数或使用 `attribute` 命令设置其 `[simproc]` 属性，
方可在 `simp` 策略中激活。

## simproc_pattern%
Defined in: `Lean.Parser.simprocPattern`

用于将模式与简化过程关联的辅助命令。

## sudo
Defined in: `commandSudoSet_option___`

命令 `sudo set_option name val` 类似 `set_option name val`，
但允许设置未声明的选项。

## suppress_compilation
Defined in: `commandSuppress_compilation`

将 `def` 和 `instance` 替换为 `noncomputable def` 和 `noncomputable instance`，
用于在特定文件或节中禁用编译器。
此为应对 https://github.com/leanprover-community/mathlib4/issues/7103 的临时方案。
注意其不适用于 `notation3`。若 `suppress_compilation` 处于激活状态，
需在声明此类记号前使用 `unsuppress_compilation`。

## syntax
Defined in: `Lean.Parser.Command.syntax`


## syntax
Defined in: `Lean.Parser.Command.syntaxAbbrev`


## tactic_extension
Defined in: `Lean.Parser.Command.tactic_extension`

扩展指定策略的文档。

扩展文档置于命令的文档字符串中，以项目符号列表形式显示，应保持简洁。

## test_extern
Defined in: `testExternCmd`


## unif_hint
Defined in: `Lean.«command__Unif_hint____Where_|_-⊢_»`


## universe
Defined in: `Lean.Parser.Command.universe`

声明一个或多个宇宙变量。

`universe u v`

`Prop`、`Type`、`Type u` 和 `Sort u` 是分类其他类型的类型，亦称*宇宙*。
在 `Type u` 和 `Sort u` 中，变量 `u` 代表宇宙的*层级*，层级为 `u` 的宇宙仅能分类层级低于 `u` 的宇宙。
有关类型宇宙的更多细节，请参阅 [Theorem Proving in Lean 相关章节][tpil universes]。

正如类型参数允许多态定义用于多种类型，宇宙参数（由宇宙变量表示）允许定义用于任意所需层级。
虽然 Lean 主要自动处理宇宙层级，但显式声明可在编写签名时提供更多控制。
`universe` 关键字允许在定义集合中使用声明的宇宙变量，Lean 将确保这些定义一致使用它们。

[tpil universes]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects
(Theorem Proving in Lean 中的类型宇宙)

```lean
/- 显式类型宇宙参数 -/
def id₁.{u} (α : Type u) (a : α) := a

/- 隐式类型宇宙参数，等价于 `id₁`。需启用选项 `autoImplicit true`（默认启用） -/
def id₂ (α : Type u) (a : α) := a

/- 显式独立宇宙变量声明，等价于 `id₁` 和 `id₂` -/
universe u
def id₃ (α : Type u) (a : α) := a
```

技术细节：若宇宙变量仅用于定义的右侧且未预先声明，将引发错误。

```lean
def L₁.{u} := List (Type u)

-- def L₂ := List (Type u) -- 错误：`未知宇宙层级 'u'`

universe u
def L₃ := List (Type u)
```

示例：

```lean
universe u v w

structure Pair (α : Type u) (β : Type v) : Type (max u v) where
  a : α
  b : β

#check Pair.{v, w}
-- Pair : Type v → Type w → Type (max v w)
```

## unseal
Defined in: `Lean.Parser.commandUnseal__`

`unseal foo` 命令确保 `foo` 的定义未密封，即标记为 `[semireducible]`（默认可规约设置）。
此命令在需要允许证明中对 `foo` 进行一定程度的规约时有用。

在功能上，`unseal foo` 等同于 `attribute [local semireducible] foo`。应用此属性会使 `foo` 仅在局部作用域内半可约。

## unset_option
定义于：`Lean.Elab.Command.unsetOption`

取消设置用户选项

## unsuppress_compilation
定义于：`commandUnsuppress_compilationIn_`

命令 `unsuppress_compilation in def foo : ...` 确保即使 `suppress_compilation` 处于激活状态，该定义仍会被编译为可执行代码。

## variable
定义于：`Lean.Parser.Command.variable`

声明一个或多个类型化变量，或修改已声明变量的隐式性。

引入可在同一 `namespace` 或 `section` 块内定义中使用的变量。当定义中提及变量时，Lean 会将其作为该定义的参数添加。这在编写许多具有共同参数的定义时特别有用（参见下面的示例）。

变量声明具有与常规函数参数相同的灵活性。特别是它们可以是[显式、隐式][binder docs]，或[实例隐式][tpil classes]（此时它们可以是匿名的）。例如，可以通过 `variable {x}` 将显式变量 `x` 转换为隐式。注意，当前应避免同时更改变量绑定方式和声明新变量；有关此主题的更多信息，请参见[问题 2789]。

在*定理体*（即证明）中，变量不会基于使用情况被包含，以确保对证明的更改不会影响整体定理的陈述。相反，变量仅在定理头部或 `include` 命令中提及过，或者作为实例隐式且仅依赖于此类变量时，才对证明可用。

有关更详细的讨论，请参阅 [*定理证明中的变量与节*][tpil vars]。

[tpil vars]:
https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#variables-and-sections
（定理证明中的变量与节）[tpil classes]:
https://lean-lang.org/theorem_proving_in_lean4/type_classes.html （定理证明中的类型类）[binder docs]:
https://leanprover-community.github.io/mathlib4_docs/Lean/Expr.html#Lean.BinderInfo （BinderInfo 类型的文档）[issue 2789]: https://github.com/leanprover/lean4/issues/2789 （GitHub 上的问题 2789）

示例：

```lean
section
  variable
    {α : Type u}      -- 隐式
    (a : α)           -- 显式
    [instBEq : BEq α] -- 实例隐式，具名
    [Hashable α]      -- 实例隐式，匿名

  def isEqual (b : α) : Bool :=
    a == b

  #check isEqual
  -- isEqual.{u} {α : Type u} (a : α) [instBEq : BEq α] (b : α) : Bool

  variable
    {a} -- 现在 `a` 是隐式的

  def eqComm {b : α} := a == b ↔ b == a

  #check eqComm
  -- eqComm.{u} {α : Type u} {a : α} [instBEq : BEq α] {b : α} : Prop
end
```

以下展示了使用 `variable` 提取定义参数的典型用法：

```lean
variable (Src : Type)

structure Logger where
  trace : List (Src × String)
#check Logger
-- Logger (Src : Type) : Type

namespace Logger
  -- 将 `Src : Type` 切换为隐式，直到 `end Logger`
  variable {Src}

  def empty : Logger Src where
    trace := []
  #check empty
  -- Logger.empty {Src : Type} : Logger Src

  variable (log : Logger Src)

  def len :=
    log.trace.length
  #check len
  -- Logger.len {Src : Type} (log : Logger Src) : Nat

  variable (src : Src) [BEq Src]

  -- 此时所有 `log`、`src`、`Src` 及 `BEq` 实例均可成为参数

  def filterSrc :=
    log.trace.filterMap
      fun (src', str') => if src' == src then some str' else none
  #check filterSrc
  -- Logger.filterSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : List String

  def lenSrc :=
    log.filterSrc src |>.length
  #check lenSrc
  -- Logger.lenSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : Nat
end Logger
```

以下示例展示了变量在证明中的可用性：
```lean
variable
  {α : Type}    -- 在证明中可用，因通过 `a` 间接提及
  [ToString α]  -- 在证明中可用，因 `α` 被包含
  (a : α)       -- 在证明中可用，因在头部提及
  {β : Type}    -- 在证明中不可用
  [ToString β]  -- 在证明中不可用

theorem ex : a = a := rfl
```
在证明精化后，将生成以下警告以突出未使用的假设：
```lean
包含的节变量 '[ToString α]' 在 'ex' 中未使用，请考虑排除它
```
在此类情况下，应将有问题的变量声明下移或放入节中，仅让依赖它的定理跟随至节结束。

## variable?
定义于：`Mathlib.Command.Variable.variable?`

`variable?` 命令与 `variable` 语法相同，但会自动插入所需但缺失的实例参数。它不会添加可从当前上下文中其他变量推导出的变量。默认情况下，该命令检查变量是否未被之前的变量隐含，但*不*检查之前的变量是否未被之后的变量隐含。与 `variable` 不同，`variable?` 不支持更改变量绑定类型。

`variable?` 命令会建议将其自身替换为形如 `variable? ...binders... => ...binders...` 的命令。`=>` 后的绑定器是完整的绑定器列表。当存在此 `=>` 子句时，命令验证扩展后的绑定器是否与 `=>` 后的绑定器匹配。此举旨在帮助使用 `variable?` 的代码对类型类层次结构的变化保持弹性，至少此附加信息可用于调试可能出现的问题。也可将 `variable? ...binders... =>` 替换为 `variable`。

核心算法是尝试逐一精化绑定器，每当出现类型类实例推断失败时，合成绑定器语法并将其添加到绑定器列表并重试，递归进行。此过程不保证给出“正确”的绑定器列表。

标有 `variable_alias` 属性的结构可作为一系列类型类的别名。例如，给定
```lean
@[variable_alias]
structure VectorSpace (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
```
则 `variable? [VectorSpace k V]` 等同于 `variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]`，假设当前作用域中 `k` 和 `V` 没有预先存在的实例。注意，这不是简单替换：它仅添加无法从当前作用域中其他变量推断出的实例。

警告：核心算法依赖美观打印，因此若绑定器中的项无法往返，此算法可能失败。但该算法支持如 `[∀ i, F i]` 的量化绑定器。

## variables
定义于：`Mathlib.Tactic.variables`

`variables` 命令的语法：此命令仅为存根，仅提示在 Lean 4 中已更名为 `variable`。

## whatsnew
定义于：`Mathlib.WhatsNew.commandWhatsnewIn__`

`whatsnew in $command` 执行命令并打印添加到环境中的声明。

## with_weak_namespace
定义于：`Lean.Elab.Command.commandWith_weak_namespace__`

更改当前命名空间，但不会导致作用域内事物退出作用域

语法 ... [Batteries.Tactic.Lemma.lemmaCmd]
不支持 `lemma`，请改用 `theorem`

语法 ... [Lean.Parser.Command.declaration]

语法 ... [Lean.Parser.Command.initialize]

语法 ... [Lean.Parser.Command.mixfix]

语法 ... [«lemma»]
`lemma` 与 `theorem` 含义相同，用于表示“次要”定理