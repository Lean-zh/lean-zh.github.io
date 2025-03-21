# 策略

Mathlib 版本：`e4cf8333e0be712392567e370eead57e05d636a7`

## \#adaptation_note
定义于：`«tactic#adaptation_note_»`

适配注释（Adaptation notes）是用于标记某段代码因 Lean 核心变更而进行调整的注释。通常需要未来进一步的维护操作。

## \#check
定义于：`Mathlib.Tactic.«tactic#check__»`

`#check t` 策略会对项 `t` 进行详细阐述，随后以 `e : ty` 的形式美观打印其类型。

若 `t` 为标识符，则改为打印全局常量 `t` 的类型声明形式。使用 `#check (t)` 可将其作为详细阐述后的表达式打印。

与 `#check` 命令类似，`#check` 策略允许存在未解决的类型类实例问题，这些将作为元变量出现在输出中。

## \#count_heartbeats
定义于：`Mathlib.CountHeartbeats.«tactic#count_heartbeats_»`

统计策略使用的心拍数，例如：`#count_heartbeats simp`。

## \#count_heartbeats!
定义于：`Mathlib.CountHeartbeats.«tactic#count_heartbeats!_In__»`

`#count_heartbeats! in tac` 将运行策略 `tac` 10 次，统计使用的心拍数，并记录范围和标准差。`#count_heartbeats! n in tac` 则会运行 `n` 次。

## \#find
定义于：`Mathlib.Tactic.Find.«tactic#find_»`

## \#leansearch
定义于：`LeanSearchClient.leansearch_search_tactic`

在 Lean 内搜索 [LeanSearch](https://leansearch.net/)。查询应为以 `.` 或 `?` 结尾的字符串。可作为命令、项或策略使用。在策略模式下，仅显示有效策略。

```lean
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

## \#loogle
定义于：`LeanSearchClient.loogle_tactic`

在 Lean 内搜索 [Loogle](https://loogle.lean-lang.org/json)。可作为命令、项或策略使用。在策略模式下，仅显示有效策略。

```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry
```

### Loogle 使用指南

Loogle 通过多种方式查找定义和引理：

按常量：
🔍 Real.sin
查找所有陈述中提及正弦函数的引理。

按引理名称子串：
🔍 "differ"
查找所有名称中包含 "differ" 的引理。

按子表达式：
🔍 _ * (_ ^ _)
查找所有陈述中包含乘积且第二个参数为某次幂的引理。

模式可非线性，如：
🔍 Real.sqrt ?a * Real.sqrt ?a

若模式含参数，将以任意顺序匹配。以下两者均能找到 List.map：
🔍 (?a -> ?b) -> List ?a -> List ?b
🔍 List ?a -> (?a -> ?b) -> List ?b

按主要结论：
🔍 |- tsum _ = _ * tsum _
查找所有结论（所有 → 和 ∀ 右侧的子表达式）具有给定形状的引理。

如前所述，若模式含参数，将按任意顺序匹配引理的假设。例如：
🔍 |- _ < _ → tsum _ < tsum _
将找到 tsum_lt_tsum，尽管假设 f i < g i 并非最后。

若传递多个搜索过滤器（以逗号分隔），Loogle 将返回匹配所有过滤器的引理。例如：
🔍 Real.sin, "two", tsum, _ * _, _ ^ _, |- _ < _ → _
将查找提及常量 Real.sin 和 tsum、引理名包含 "two"、类型中某处含乘积和幂、且具有 _ < _ 形式假设的引理（若有）。元变量（?a）在各过滤器中独立分配。

## \#loogle
定义于：`LeanSearchClient.just_loogle_tactic`

## \#moogle
定义于：`LeanSearchClient.moogle_search_tactic`

在 Lean 内搜索 [Moogle](https://www.moogle.ai/api/search)。查询应为以 `.` 或 `?` 结尾的字符串。可作为命令、项或策略使用。在策略模式下，仅显示有效策略。

```lean
#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

## \#search
定义于：`LeanSearchClient.search_tactic`

根据选项 `leansearchclient.backend`，在 Lean 内搜索 [Moogle](https://www.moogle.ai/api/search) 或 [LeanSearch](https://leansearch.net/)。查询应为以 `.` 或 `?` 结尾的字符串。可作为命令、项或策略使用。在策略模式下，仅显示有效策略。

```lean
#search "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

在策略模式下，若未提供查询字符串，则基于当前目标状态查询 [LeanStateSearch](https://premise-search.com)。


## \#statesearch
定义于：`LeanSearchClient.statesearch_search_tactic`

在 Lean 内搜索 [LeanStateSearch](https://premise-search.com)。当前主目标将作为查询发送。可通过 `statesearch.revision` 选项设置搜索版本，通过 `statesearch.queries` 选项设置结果数量。

提示：若需修改查询，需使用网页界面。

```lean
set_option statesearch.queries 1
set_option statesearch.revision "v4.16.0"

example : 0 ≤ 1 := by
  #statesearch
  sorry
```

## (
定义于：`Lean.Parser.Tactic.paren`

`(tacs)` 依次执行一系列策略，无需像 `· tacs` 那样在最后关闭目标。类似 `by` 本身，策略可通过换行或 `;` 分隔。

## <;>
定义于：`Batteries.Tactic.seq_focus`

`t <;> [t1; t2; ...; tn]` 聚焦于首个目标并应用 `t`，应生成 `n` 个子目标。随后对每个目标应用对应的 `ti` 并收集生成的子目标。

## <;>
定义于：`Lean.Parser.Tactic.«tactic_<;>_»`

`tac <;> tac'` 在主目标上运行 `tac`，随后在每个生成的目标上运行 `tac'`，合并所有 `tac'` 生成的子目标。

## _
定义于：`Batteries.Tactic.tactic_`

策略位置的 `_` 类似 `done` 策略：若存在任何目标则失败并列出目标列表。在开始策略块（如 `by _`）后作为占位符使用，可保证语法正确并显示当前目标。

## abel
定义于：`Mathlib.Tactic.Abel.abel`

用于在*加法*交换幺半群和群的语言中评估方程的策略。

`abel` 及其变体既可作为策略，也可作为转换策略使用。

* `abel1` 若目标非由交换幺半群/群公理可证的等式，则失败。
* `abel_nf` 将所有群表达式重写为规范形式。
  * 在策略模式下，`abel_nf at h` 可用于在假设中重写。
  * `abel_nf (config := cfg)` 允许额外配置：
    * `red`: 可约性设置（被 `!` 覆盖）
    * `zetaDelta`: 若为真，可展开局部 let 变量（被 `!` 覆盖）
    * `recursive`: 若为真，`abel_nf` 将递归处理原子
* `abel!`, `abel1!`, `abel_nf!` 将使用更激进的可约性设置识别原子。

例如：

```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

### 未来工作

* 在 mathlib 3 中，`abel` 接受额外的可选参数：
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  是否应最终恢复这些功能尚未决定。

## abel!
定义于：`Mathlib.Tactic.Abel.tacticAbel!`

用于在*加法*交换幺半群和群的公理体系中验证等式的策略。

`abel` 及其变体既可作为普通策略，也可作为转换策略使用。

* `abel1` 若目标不是可被交换幺半群/群公理证明的等式，则会失败。
* `abel_nf` 将所有群表达式重写为标准形式。
  * 在策略模式中，`abel_nf at h` 可用于在假设中重写。
  * `abel_nf (config := cfg)` 允许额外配置：
    * `red`：可约性设置（被 `!` 覆盖）
    * `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
    * `recursive`：若为真，`abel_nf` 将递归进入原子
* `abel!`、`abel1!`、`abel_nf!` 将使用更激进的可约性设置来识别原子。

例如：

```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

### 未来工作

* 在 mathlib 3 中，`abel` 接受额外的可选参数：
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  是否应最终恢复这些功能尚未决定。

## abel1
定义于：`Mathlib.Tactic.Abel.abel1`

用于在*加法*交换幺半群和群的公理体系中验证等式的策略。

`abel` 及其变体既可作为普通策略，也可作为转换策略使用。

* `abel1` 若目标不是可被交换幺半群/群公理证明的等式，则会失败。
* `abel_nf` 将所有群表达式重写为标准形式。
  * 在策略模式中，`abel_nf at h` 可用于在假设中重写。
  * `abel_nf (config := cfg)` 允许额外配置：
    * `red`：可约性设置（被 `!` 覆盖）
    * `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
    * `recursive`：若为真，`abel_nf` 将递归进入原子
* `abel!`、`abel1!`、`abel_nf!` 将使用更激进的可约性设置来识别原子。

例如：

```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

### 未来工作

* 在 mathlib 3 中，`abel` 接受额外的可选参数：
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  是否应最终恢复这些功能尚未决定。

## abel1!
定义于：`Mathlib.Tactic.Abel.abel1!`

用于在*加法*交换幺半群和群的公理体系中验证等式的策略。

`abel` 及其变体既可作为普通策略，也可作为转换策略使用。

* `abel1` 若目标不是可被交换幺半群/群公理证明的等式，则会失败。
* `abel_nf` 将所有群表达式重写为标准形式。
  * 在策略模式中，`abel_nf at h` 可用于在假设中重写。
  * `abel_nf (config := cfg)` 允许额外配置：
    * `red`：可约性设置（被 `!` 覆盖）
    * `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
    * `recursive`：若为真，`abel_nf` 将递归进入原子
* `abel!`、`abel1!`、`abel_nf!` 将使用更激进的可约性设置来识别原子。

例如：

```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

### 未来工作

* 在 mathlib 3 中，`abel` 接受额外的可选参数：
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  是否应最终恢复这些功能尚未决定。

## abel_nf
定义于：`Mathlib.Tactic.Abel.abelNF`

用于在*加法*交换幺半群和群的公理体系中验证等式的策略。

`abel` 及其变体既可作为普通策略，也可作为转换策略使用。

* `abel1` 若目标不是可被交换幺半群/群公理证明的等式，则会失败。
* `abel_nf` 将所有群表达式重写为标准形式。
  * 在策略模式中，`abel_nf at h` 可用于在假设中重写。
  * `abel_nf (config := cfg)` 允许额外配置：
    * `red`：可约性设置（被 `!` 覆盖）
    * `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
    * `recursive`：若为真，`abel_nf` 将递归进入原子
* `abel!`、`abel1!`、`abel_nf!` 将使用更激进的可约性设置来识别原子。

例如：

```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

### 未来工作

* 在 mathlib 3 中，`abel` 接受额外的可选参数：
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  是否应最终恢复这些功能尚未决定。

## abel_nf!
定义于：`Mathlib.Tactic.Abel.tacticAbel_nf!__`

用于在*加法*交换幺半群和群的公理体系中验证等式的策略。

`abel` 及其变体既可作为普通策略，也可作为转换策略使用。

* `abel1` 若目标不是可被交换幺半群/群公理证明的等式，则会失败。
* `abel_nf` 将所有群表达式重写为标准形式。
  * 在策略模式中，`abel_nf at h` 可用于在假设中重写。
  * `abel_nf (config := cfg)` 允许额外配置：
    * `red`：可约性设置（被 `!` 覆盖）
    * `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
    * `recursive`：若为真，`abel_nf` 将递归进入原子
* `abel!`、`abel1!`、`abel_nf!` 将使用更激进的可约性设置来识别原子。

例如：

```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

### 未来工作

* 在 mathlib 3 中，`abel` 接受额外的可选参数：
  ```
  syntax "abel" (&" raw" <|> &" term")? (location)? : tactic
  ```
  是否应最终恢复这些功能尚未决定。

## absurd
定义于：`Batteries.Tactic.tacticAbsurd_`

给定一个证明 `h` 证明 `p`，`absurd h` 将目标更改为 `⊢ ¬ p`。若 `p` 是否定式 `¬q`，则目标将更改为 `⊢ q`。

## ac_change
定义于：`Mathlib.Tactic.acChange`

`ac_change g using n` 是 `convert_to g using n` 后接 `ac_rfl`。它对于重新排列/重新结合例如和式很有用：
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N := by
  ac_change a + d + e + f + c + g + b ≤ _
  -- ⊢ a + d + e + f + c + g + b ≤ N
```

## ac_nf
定义于：`Lean.Parser.Tactic.tacticAc_nf_`

`ac_nf` 将等式规范化至结合交换运算符的应用。
- `ac_nf` 规范化所有假设和当前目标的目标。
- `ac_nf at l` 在位置 `l` 处规范化，其中 `l` 是 `*` 或局部上下文中的假设列表。后者中，可使用转向符 `⊢` 或 `|-` 表示当前目标的目标。
```lean
instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by
 ac_nf
 -- 目标：a + (b + (c + d)) = a + (b + (c + d))
```

## ac_nf0
定义于：`Lean.Parser.Tactic.acNf0`

`ac_nf` 的实现（完整的 `ac_nf` 之后会调用 `trivial`）。

## ac_rfl
定义于：`Lean.Parser.Tactic.acRfl`

`ac_rfl` 证明等式至结合交换运算符的应用。
```lean
instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```

## admit
定义于：`Lean.Parser.Tactic.tacticAdmit`

`admit` 是 `sorry` 的同义词。

## aesop
定义于：`Aesop.Frontend.Parser.aesopTactic`

`aesop <clause>*` 尝试通过应用一组使用 `@[aesop]` 属性注册的规则来解决当前目标。参考[其 README](https://github.com/JLimperg/aesop#readme)获取教程和参考。

变体 `aesop?` 会打印找到的证明作为 `Try this` 建议。

子句可用于自定义 Aesop 调用的行为。可用的子句包括：

- `(add <phase> <priority> <builder> <rule>)` 添加一条规则。`<phase>` 为 `unsafe`、`safe` 或 `norm`。`<priority>` 对于不安全规则是百分比，对于安全和规范规则是整数。`<rule>` 是声明或局部假设的名称。`<builder>` 是将 `<rule>` 转换为 Aesop 规则的构建器。例如：`(add unsafe 50% apply Or.inl)`。
- `(erase <rule>)` 禁用全局注册的 Aesop 规则。例如：`(erase Aesop.BuiltinRules.assumption)`。
- `(rule_sets := [<ruleset>,*])` 为此 Aesop 调用启用或禁用命名的规则集。例如：`(rule_sets := [-builtin, MyRuleSet])`。
- `(config { <opt> := <value> })` 调整 Aesop 的搜索选项。参考 `Aesop.Options`。
- `(simp_config { <opt> := <value> })` 调整 Aesop 内置 `simp` 规则的选项。给定的选项直接传递给 `simp`。例如：`(simp_config := { zeta := false })` 使 Aesop 使用 `simp (config := { zeta := false })`。

## aesop?
定义于：`Aesop.Frontend.Parser.aesopTactic?`

`aesop <clause>*` 尝试通过应用一组使用 `@[aesop]` 属性注册的规则来解决当前目标。参考[其 README](https://github.com/JLimperg/aesop#readme)获取教程和参考。

变体 `aesop?` 会打印找到的证明作为 `Try this` 建议。

子句可用于自定义 Aesop 调用的行为。可用的子句包括：

- `(add <phase> <priority> <builder> <rule>)` 添加一条规则。`<phase>` 为 `unsafe`、`safe` 或 `norm`。`<priority>` 对于不安全规则是百分比，对于安全和规范规则是整数。`<rule>` 是声明或局部假设的名称。`<builder>` 是将 `<rule>` 转换为 Aesop 规则的构建器。例如：`(add unsafe 50% apply Or.inl)`。
- `(erase <rule>)` 禁用全局注册的 Aesop 规则。例如：`(erase Aesop.BuiltinRules.assumption)`。
- `(rule_sets := [<ruleset>,*])` 为此 Aesop 调用启用或禁用命名的规则集。例如：`(rule_sets := [-builtin, MyRuleSet])`。
- `(config { <opt> := <value> })` 调整 Aesop 的搜索选项。参考 `Aesop.Options`。
- `(simp_config { <opt> := <value> })` 调整 Aesop 内置 `simp` 规则的选项。给定的选项直接传递给 `simp`。例如：`(simp_config := { zeta := false })` 使 Aesop 使用 `simp (config := { zeta := false })`。

## aesop_cat
定义于：`CategoryTheory.aesop_cat`

`aesop_cat` 是 `aesop` 的轻量级包装，添加了 `CategoryTheory` 规则集，并允许 `aesop` 在调用 `intros` 时查看半透明定义。当无法解决目标时，此策略会失败，适用于在自动参数中使用。

## aesop_cat?
定义于：`CategoryTheory.aesop_cat?`

我们还使用 `aesop_cat?` 在使用 `aesop_cat` 时传递 `Try this` 建议。

## aesop_cat_nonterminal
定义于：`CategoryTheory.aesop_cat_nonterminal`

`aesop_cat_nonterminal` 是 `aesop_cat` 的变体，当无法解决目标时不会失败。仅用于探索！非终止的 `aesop` 比非终止的 `simp` 更糟糕。

## aesop_graph
定义于：`aesop_graph`

用于图库的 `aesop` 策略变体。相对于标准 `aesop` 的更改：

- 除默认规则集外，还使用 `SimpleGraph` 规则集。
- 指示 Aesop 的 `intro` 规则使用 `default` 透明度展开。
- 指示 Aesop 如果无法完全解决目标则失败。这允许我们将 `aesop_graph` 用于自动参数。

## aesop_graph?
定义于：`aesop_graph?`

使用 `aesop_graph?` 在使用 `aesop_graph` 时传递 `Try this` 建议。

## aesop_graph_nonterminal
定义于：`aesop_graph_nonterminal`

`aesop_graph_nonterminal` 是 `aesop_graph` 的变体，当无法解决目标时不会失败。仅用于探索！非终止的 Aesop 比非终止的 `simp` 更糟糕。

## aesop_mat
定义于：`Matroid.aesop_mat`

`aesop_mat` 策略尝试证明一个集合包含在拟阵的基集中。它使用 `[Matroid]` 规则集，并允许失败。

## aesop_unfold
定义于：`Aesop.tacticAesop_unfold_`

## aesop_unfold
定义于：`Aesop.tacticAesop_unfold_At_`

## algebraize
定义于：`Mathlib.Tactic.tacticAlgebraize__`

给定 `RingHom` 时，`algebraize` 策略会添加相应的 `Algebra` 实例（如果可能）和 `IsScalarTower` 实例，以及将 `RingHom` 属性转换为可用假设的 `Algebra` 属性。

例如：给定 `f : A →+* B` 和 `g : B →+* C`，以及 `hf : f.FiniteType`，`algebraize [f, g]` 将添加实例 `Algebra A B`、`Algebra B C` 和 `Algebra.FiniteType A B`。

参考 `algebraize` 标签以获取可添加属性的说明。

该策略还提供配置选项 `properties`。若设置为 `true`（默认），策略会在局部上下文中搜索可转换为 `Algebra` 属性的 `RingHom` 属性。宏 `algebraize_only` 调用 `algebraize (config := {properties := false})`，即仅添加 `Algebra` 和 `IsScalarTower` 实例。

## algebraize_only
定义于：`Mathlib.Tactic.tacticAlgebraize_only__`

`algebraize_only` 是 `algebraize` 的版本，仅添加 `Algebra` 实例和 `IsScalarTower` 实例，不尝试添加任何关于带有 `@[algebraize]` 标签的属性（如 `Finite` 或 `IsIntegral`）的实例。

## all_goals
定义于：`Lean.Parser.Tactic.allGoals`

`all_goals tac` 在每个目标上运行 `tac`，合并结果目标。若策略在任何目标上失败，整个 `all_goals` 策略失败。

另见 `any_goals tac`。

## and_intros
定义于：`Lean.Parser.Tactic.tacticAnd_intros`

`and_intros` 应用 `And.intro` 直到不再有进展。

## any_goals
定义于：`Lean.Parser.Tactic.anyGoals`

`any_goals tac` 将策略 `tac` 应用于每个目标，合并成功应用的结果目标。若策略在所有目标上失败，整个 `any_goals` 策略失败。

此策略类似于 `all_goals try tac`，但若所有 `tac` 应用均失败，则失败。

## apply
定义于：`Mathlib.Tactic.tacticApply_At_`

`apply t at i` 将在假设 `i` 处使用 `t` 进行前向推理。明确地说，若 `t : α₁ → ⋯ → αᵢ → ⋯ → αₙ` 且 `i` 的类型为 `αᵢ`，则此策略将为 `j = 1, …, i-1` 的任意 `αⱼ` 添加元变量/目标，然后通过应用这些元变量和原始 `i`，将 `i` 的类型替换为 `αᵢ₊₁ → ⋯ → αₙ`。

## apply
定义于：`Lean.Parser.Tactic.apply`

`apply e` 尝试将当前目标与 `e` 类型的结论匹配。若成功，则返回与未被类型推断或类型类解析固定的前提数量相同的子目标。非依赖前提在依赖前提之前添加。

`apply` 策略使用高阶模式匹配、类型类解析和依赖类型的一阶统一。

## apply
定义于：`Mathlib.Tactic.applyWith`

`apply (config := cfg) e` 类似于 `apply e`，但允许提供传递到底层 `apply` 操作的配置 `cfg : ApplyConfig`。

## apply?
定义于：`Lean.Parser.Tactic.apply?`

在环境中搜索可使用 `apply` 通过 `solve_by_elim` 解决条件来优化目标的定义或定理。

可选的 `using` 子句提供必须用于关闭目标的局部上下文中的标识符。

## apply_assumption
定义于：`Lean.Parser.Tactic.applyAssumption`

`apply_assumption` 会寻找形式为 `... → ∀ _, ... → head` 的假设，其中 `head` 与当前目标匹配。

您可以通过 `apply_assumption [...]` 指定额外的应用规则。默认情况下，`apply_assumption` 还会尝试使用 `rfl`、`trivial`、`congrFun` 和 `congrArg`。若您不希望使用这些规则，或不想使用所有假设，请使用 `apply_assumption only [...]`。您可以使用 `apply_assumption [-h]` 来忽略某个局部假设。通过 `apply_assumption using [a₁, ...]` 可以使用所有标有属性 `aᵢ` 的引理（这些属性必须通过 `register_label_attr` 创建）。

`apply_assumption` 会使用通过 `symm` 获得的局部假设的推论。

若 `apply_assumption` 失败，它将调用 `exfalso` 并重试。因此，若存在形式为 `P → ¬ Q` 的假设，新的策略状态将包含两个目标：`P` 和 `Q`。

您可以通过语法 `apply_rules (config := {...}) lemmas` 传递进一步的配置。支持的选项与 `solve_by_elim` 相同（包括所有 `apply` 的选项）。

## apply_ext_theorem
定义于：`Lean.Elab.Tactic.Ext.applyExtTheorem`

将单个扩展性定理应用于当前目标。

## apply_fun
定义于：`Mathlib.Tactic.applyFun`

将函数应用于等式或不等式中的局部假设或目标。

* 若存在 `h : a = b`，则 `apply_fun f at h` 将替换为 `h : f a = f b`。
* 若存在 `h : a ≤ b`，则 `apply_fun f at h` 将替换为 `h : f a ≤ f b`，并创建辅助目标 `Monotone f`。`apply_fun` 会自动尝试使用 `mono` 解决此辅助目标，或通过 `apply_fun f at h using P` 显式提供解决方案，其中 `P : Monotone f`。
* 若存在 `h : a < b`，则 `apply_fun f at h` 将替换为 `h : f a < f b`，并创建辅助目标 `StrictMono f`，行为与上一条类似。
* 若存在 `h : a ≠ b`，则 `apply_fun f at h` 将替换为 `h : f a ≠ f b`，并创建辅助目标 `Injective f`，行为与上述情况类似。
* 若目标为 `a ≠ b`，`apply_fun f` 将替换为 `f a ≠ f b`。
* 若目标为 `a = b`，`apply_fun f` 将替换为 `f a = f b`，并创建辅助目标 `injective f`。`apply_fun` 会自动尝试使用局部假设解决此辅助目标，若 `f` 实际为 `Equiv`，或通过 `apply_fun f using P` 显式提供解决方案，其中 `P : Injective f`。
* 若目标为 `a ≤ b`（或类似 `a < b`），且 `f` 实际为 `OrderIso`，`apply_fun f` 将替换目标为 `f a ≤ f b`。若 `f` 为其他类型（例如普通函数或 `Equiv`），`apply_fun` 将失败。

典型用法如下：
```lean
open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Injective <| g ∘ f) :
    Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h
```

函数 `f` 的处理方式与 `refine` 类似，`f` 可包含占位符。命名占位符（如 `?a` 或 `?_`）将生成新目标。

## apply_gmonoid_gnpowRec_succ_tac
定义于：`GradedMonoid.tacticApply_gmonoid_gnpowRec_succ_tac`

作为 `GMonoid.gnpow_succ'` 可选值的策略。

## apply_gmonoid_gnpowRec_zero_tac
定义于：`GradedMonoid.tacticApply_gmonoid_gnpowRec_zero_tac`

作为 `GMonoid.gnpow_zero'` 可选值的策略。

## apply_mod_cast
定义于：`Lean.Parser.Tactic.tacticApply_mod_cast_`

规范化目标及给定表达式中的强制转换，随后将表达式 `apply` 到目标。

## apply_rfl
定义于：`Lean.Parser.Tactic.applyRfl`

与 `rfl` 相同，但不在最后尝试 `eq_refl`。

## apply_rules
定义于：`Lean.Parser.Tactic.applyRules`

`apply_rules [l₁, l₂, ...]` 尝试通过迭代应用引理列表 `[l₁, l₂, ...]` 或局部假设来解决主要目标。若 `apply` 生成新目标，`apply_rules` 会迭代尝试解决这些目标。您可使用 `apply_rules [-h]` 忽略局部假设。

`apply_rules` 还会使用 `rfl`、`trivial`、`congrFun` 和 `congrArg`。通过 `apply_rules only [...]` 可禁用这些规则及局部假设。

通过 `apply_rules using [a₁, ...]` 可使用所有标有属性 `aᵢ` 的引理（这些属性必须通过 `register_label_attr` 创建）。

您可通过语法 `apply_rules (config := {...})` 传递进一步配置。支持的选项与 `solve_by_elim` 相同（包括所有 `apply` 的选项）。

`apply_rules` 会在需要时对假设调用 `symm` 并对目标调用 `exfalso`。通过 `apply_rules (config := {symm := false, exfalso := false})` 可禁用此行为。

使用语法 `apply_rules (config := {maxDepth := n})` 可限制迭代深度。

与 `solve_by_elim` 不同，`apply_rules` 不执行回溯，并贪婪应用列表中的引理直至陷入停滞。

## arith_mult
定义于：`ArithmeticFunction.arith_mult`

`arith_mult` 通过应用标有用户属性 `arith_mult` 的引理，解决形如 `IsMultiplicative f`（其中 `f : ArithmeticFunction R`）的目标。

## arith_mult?
定义于：`ArithmeticFunction.arith_mult?`

`arith_mult` 通过应用标有用户属性 `arith_mult` 的引理，解决形如 `IsMultiplicative f`（其中 `f : ArithmeticFunction R`）的目标，并打印生成的证明项。

## array_get_dec
定义于：`Array.tacticArray_get_dec`

此策略被添加到 `decreasing_trivial` 工具箱中，用于证明 `sizeOf arr[i] < sizeOf arr`，这对于嵌套归纳类型（如 `inductive T | mk : Array T → T`）的良基递归非常有用。

## array_mem_dec
定义于：`Array.tacticArray_mem_dec`

此策略被添加到 `decreasing_trivial` 工具箱中，用于在 `a ∈ arr` 时证明 `sizeOf a < sizeOf arr`，这对于嵌套归纳类型（如 `inductive T | mk : Array T → T`）的良基递归非常有用。

## as_aux_lemma
定义于：`Lean.Parser.Tactic.as_aux_lemma`

`as_aux_lemma => tac` 执行与 `tac` 相同的操作，但会将结果表达式包装到辅助引理中。在某些情况下，这能显著减小表达式的大小，因为证明项不会被重复。

## assumption
定义于：`Lean.Parser.Tactic.assumption`

`assumption` 尝试使用类型兼容的假设解决主要目标，否则失败。另请注意术语符号 `‹t›`，它是 `show t by assumption` 的简写。

## assumption'
定义于：`Mathlib.Tactic.tacticAssumption'`

尝试在所有目标上调用 `assumption`；若至少关闭一个目标，则成功。

## assumption_mod_cast
定义于：`Lean.Parser.Tactic.tacticAssumption_mod_cast_`

`assumption_mod_cast` 是 `assumption` 的变体，使用假设解决目标。与 `assumption` 不同，它首先预处理目标及各假设，将强制转换尽可能外移，从而适用于更多情况。

具体而言，它对目标运行 `norm_cast`。对于每个局部假设 `h`，它还会使用 `norm_cast` 规范化 `h`，并尝试用其关闭目标。

## attempt_all
定义于：`Lean.Parser.Tactic.attemptAll`

实现 `try?` 策略的辅助内部策略。

## aux_group₁
定义于：`Mathlib.Tactic.Group.aux_group₁`

`group` 策略的辅助策略。仅调用简化器。

## aux_group₂
定义于：`Mathlib.Tactic.Group.aux_group₂`

`group` 策略的辅助策略。调用 `ring_nf` 规范化指数。

## bddDefault
定义于：`tacticBddDefault`

在完全格中，集合自动有界或共界。为了在完全格和条件完全格中使用相同陈述，但让自动化在完全格中自动填充有界性证明，我们在陈述中使用 `bddDefault` 策略，形式为 `(hA : BddAbove A := by bddDefault)`。

## beta_reduce
定义于：`Mathlib.Tactic.betaReduceStx`

`beta_reduce at loc` 完全贝塔归约给定位置。这也作为 `conv` 模式策略存在。

这意味着每当有一个应用的lambda表达式如 `(fun x => f x) y` 时，参数会被代入lambda表达式，生成如 `f y` 的表达式。

## bicategory
定义于：`Mathlib.Tactic.Bicategory.tacticBicategory`

使用双范畴的相干定理来解双范畴中的方程，其中两边仅通过用不同但具有相同源和目标的双范畴结构态射（即结合子、单位子和恒等态射）替换结构态射字符串而不同。

即，`bicategory` 可处理形如 `a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'` 的目标，其中 `a = a'`、`b = b'` 和 `c = c'` 可通过 `bicategory_coherence` 证明。

## bicategory_coherence
定义于：`Mathlib.Tactic.BicategoryCoherence.tacticBicategory_coherence`

双范畴的相干策略。请改用 `pure_coherence`，这是本策略的前端。

## bicategory_coherence
定义于：`Mathlib.Tactic.Bicategory.tacticBicategory_coherence`

关闭形如 `η = θ` 的目标，其中 `η` 和 `θ` 是仅由结合子、单位子和恒等态射构成的2-同构。
```lean
示例 {B : Type} [Bicategory B] {a : B} :
  (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  bicategory_coherence
```

## bicategory_nf
定义于：`Mathlib.Tactic.Bicategory.tacticBicategory_nf`

规范化等式两边。

## bitwise_assoc_tac
定义于：`Nat.tacticBitwise_assoc_tac`

证明位运算的结合性通常需要进行大量的案例分析，因此使用此策略比在一般情况下证明更为简便。

## borelize
定义于：`Mathlib.Tactic.Borelize.tacticBorelize___`

`borelize α` 的行为取决于关于 `α` 的现有假设：

- 若 `α` 是具有实例 `[MeasurableSpace α] [BorelSpace α]` 的拓扑空间，则 `borelize α` 将前者实例替换为 `borel α`；
- 否则，`borelize α` 添加实例 `borel α : MeasurableSpace α` 和 `⟨rfl⟩ : BorelSpace α`。

最后，`borelize α β γ` 执行 `borelize α; borelize β; borelize γ`。

## bound
定义于：`«tacticBound[_]»`

`bound` 策略通过直接递归表达式结构来证明不等式。

一个使用示例如下：

```
-- 计算示例：`z ↦ z^2 + c` 的弱下界
lemma le_sqr_add (c z : ℝ) (cz : ‖c‖ ≤ ‖z‖) (z3 : 3 ≤ ‖z‖) :
    2 * ‖z‖ ≤ ‖z^2 + c‖ := by
  calc ‖z^2 + c‖
    _ ≥ ‖z^2‖ - ‖c‖ := by bound
    _ ≥ ‖z^2‖ - ‖z‖ := by bound
    _ ≥ (‖z‖ - 1) * ‖z‖ := by
      rw [mul_comm, mul_sub_one, ← pow_two, ← norm_pow]
    _ ≥ 2 * ‖z‖ := by bound
```

`bound` 构建于 `aesop` 之上，使用：
1. 应用通过 `@[bound]` 属性注册的引理
2. 前向通过 `@[bound_forward]` 属性注册的引理
3. 上下文中的局部假设
4. 可选：作为 `bound [h₀, h₁]` 提供的额外假设。这些假设会被添加到上下文中，如同通过 `have := hᵢ` 添加。

`bound` 的功能与 `positivity` 和 `gcongr` 有所重叠，但可以在 `0 ≤ x` 和 `x ≤ y` 型不等式之间来回跳跃。例如，`bound` 通过将目标转化为 `b * c ≤ a * c`，然后使用 `mul_le_mul_of_nonneg_right` 来证明 `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`。`bound` 还包含处理形如 `1 ≤ x`、`1 < x`、`x ≤ 1`、`x < 1` 的目标的引理。相反，`gcongr` 可证明更多类型关系的不等式，支持所有 `positivity` 功能，并且可能更快，因为它更专门（非基于 `aesop`）。

## bv_check
定义于：`Lean.Parser.Tactic.bvCheck`

此策略与 `bv_decide` 类似，但通过使用已存储在磁盘上的证明来跳过调用SAT求解器。调用时需指定与当前Lean文件同目录下的LRAT文件名：
```lean
bv_check "proof.lrat"
```

## bv_decide
定义于：`Lean.Parser.Tactic.bvDecide`

通过从外部SAT求解器获取证明并在Lean内部验证，关闭固定宽度的 `BitVec` 和 `Bool` 目标。当前可解决的目标限于：
- Lean中等效于 [`QF_BV`](https://smt-lib.org/logics-all.shtml#QF_BV) 的目标
- 自动拆解包含 `BitVec` 或 `Bool` 信息的结构
```lean
example: ∀ (a b : BitVec 64), (a &&& b) + (a ^^^ b) = a ||| b := by
  intros
  bv_decide
```

若 `bv_decide` 遇到未知定义，则会将其视为无约束的 `BitVec` 变量。有时这可以在不理解定义的情况下解决问题，因为定义的精确属性在特定证明中无关紧要。

若 `bv_decide` 未能关闭目标，则会提供反例，包含所有被视为变量的项的赋值。

为避免每次调用SAT求解器，可通过 `bv_decide?` 缓存证明。

若解决问题依赖于结合性或交换性，请启用 `bv.ac_nf` 选项。

注意：`bv_decide` 使用 `ofReduceBool`，因此信任代码生成器的正确性。

注意：需包含 `import Std.Tactic.BVDecide`

## bv_decide?
定义于：`Lean.Parser.Tactic.bvTraceMacro`

为 `bv_decide` 策略调用建议证明脚本。用于缓存LRAT证明。

注意：需包含 `import Std.Tactic.BVDecide`

## bv_normalize
定义于：`Lean.Parser.Tactic.bvNormalize`

仅运行 `bv_decide` 的规范化过程。有时这足以解决基本的 `BitVec` 目标。

注意：需包含 `import Std.Tactic.BVDecide`

## bv_omega
定义于：`Lean.Parser.Tactic.tacticBv_omega`

`bv_omega` 是带有预处理器的 `omega`，将关于 `BitVec` 的陈述转化为关于 `Nat` 的陈述。当前预处理器实现为 `try simp only [bitvec_to_nat] at *`。`bitvec_to_nat` 是您可（谨慎）添加更多定理的 `@[simp]` 属性。

## by_cases
定义于：`«tacticBy_cases_:_»`

`by_cases (h :)? p` 将主目标拆分为两种情况，在第一个分支中假设 `h : p`，在第二个分支中假设 `h : ¬ p`。

## by_contra
定义于：`Batteries.Tactic.byContra`

`by_contra h` 通过反证法证明 `⊢ p`，引入假设 `h : ¬p` 并证明 `False`。
* 若 `p` 是否定式 `¬q`，则会引入 `h : q` 而非 `¬¬q`。
* 若 `p` 可判定，则使用 `Decidable.byContradiction` 替代 `Classical.byContradiction`。
* 若省略 `h`，则引入的变量 `_: ¬p` 将为匿名。## by_contra!
定义于：`byContra!`

若主目标的目标类型为命题 `p`，`by_contra!` 会将目标转换为在额外假设 `this : ¬ p` 下证明 `False`。  
`by_contra! h` 可用于为假设命名 `h : ¬ p`。  
假设 `¬ p` 将使用 `push_neg` 进行否定规范化。例如，`¬ a < b` 将被更改为 `b ≤ a`。  
`by_contra! h : q` 会对 `¬ p` 进行否定规范化，对 `q` 进行否定规范化，然后检查两个规范化形式是否相等。生成的假设为规范化前的形式 `q`。  
若未显式提供名称 `h`，则默认使用 `this` 作为名称。  
此策略使用经典推理。  
它是策略 `by_contra` 的一个变体。  
示例：  
```lean
example : 1 < 2 := by
  by_contra! h
  -- h : 2 ≤ 1 ⊢ False

example : 1 < 2 := by
  by_contra! h : ¬ 1 < 2
  -- h : ¬ 1 < 2 ⊢ False
```

## calc
定义于：`Lean.calcTactic`

基于传递关系的逐步推理。  
```lean
calc
  a = b := pab
  b = c := pbc
  ...
  y = z := pyz
```  
通过逐步证明 `a = b`、`b = c` 等，最终证明 `a = z`。`=` 可替换为任何实现了 `Trans` 类型类的关系。为避免重复右侧表达式，后续左侧可用 `_` 替代。  
```lean
calc
  a = b := pab
  _ = c := pbc
  ...
  _ = z := pyz
```  
首行也可写作 `<lhs>\n  _ = <rhs> := <proof>`，便于对齐长标识符的关系符号：  
```lean
calc abc
  _ = bce := pabce
  _ = cef := pbcef
  ...
  _ = xyz := pwxyz
```  

`calc` 可作为项、策略或 `conv` 策略使用。  
详见 [Lean 4 定理证明][tpil4]。  

[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#calculational-proofs

## calc?
定义于：`Lean.Elab.Tactic.tacticCalc?`

生成 `calc` 证明。

## cancel_denoms
定义于：`tacticCancel_denoms_`

## cancel_denoms
定义于：`cancelDenoms`

`cancel_denoms` 尝试从分数分母中去除数值。适用于有序域不等式命题。  

```lean
variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```

## case
定义于：`Batteries.Tactic.casePatt`

* `case _ : t => tac` 寻找首个与 `t` 统一的目标，使用 `tac` 解决之，否则失败。类似 `show`，将目标类型更改为 `t`。  
  `_` 可为案例标签，此时仅匹配符合 `case` 规则的目标（精确匹配标签，或以标签为后缀/前缀的目标）。  

* `case _ n₁ ... nₘ : t => tac` 额外将最近 `m` 个不可访问名称的假设重命名为指定名称。重命名在匹配 `t` 前进行。  
  `_` 可为案例标签。  

* `case _ : t := e` 是 `case _ : t => exact e` 的简写。  

* `case _ : t₁ | _ : t₂ | ... => tac` 等价于依次对每个模式执行 `case`，但所有匹配基于原始目标列表——每个目标被匹配后即被消耗，故模式可重复或重叠。  

* `case _ : t` 将使匹配目标成为首个目标。  
  `case _ : t₁ | _ : t₂ | ...` 按顺序使匹配目标成为首个目标。  

* `case _ : t := _` 和 `case _ : t := ?m` 等同于 `case _ : t`，但在 `?m` 情况下目标标签更改为 `m`，目标变为元变量 `?m`。  

## case
定义于：`Lean.Parser.Tactic.case`

* `case tag => tac` 聚焦于案例名为 `tag` 的目标，使用 `tac` 解决之，否则失败。  
* `case tag x₁ ... xₙ => tac` 额外将最近 `n` 个假设重命名为指定名称。  
* `case tag₁ | tag₂ => tac` 等价于依次执行 `(case tag₁ => tac); (case tag₂ => tac)`。  

## case'
定义于：`Lean.Parser.Tactic.case'`

`case'` 类似 `case tag => tac`，但不确保 `tac` 后目标已解决，且在 `tac` 失败时不会承认目标。注意：`case` 在 `tac` 失败时使用 `sorry` 关闭目标，且不中断策略执行。  

## case'
定义于：`Batteries.Tactic.casePatt'`

`case' _ : t => tac` 类似 `case _ : t => tac`，但不确保 `tac` 后目标已解决，且在 `tac` 失败时不会承认目标。注意：`case` 在 `tac` 失败时使用 `sorry` 关闭目标，且不中断策略执行。  

## cases
定义于：`Lean.Parser.Tactic.cases`

假设局部上下文中变量 `x` 具有归纳类型，`cases x` 将主目标拆分，为每个构造子生成一个目标，其中目标被替换为该构造子的通用实例。若局部上下文中的元素类型依赖于 `x`，则该元素会被恢复并重新引入，确保案例拆分影响该假设。`cases` 自动检测并关闭不可达案例。  

例如，给定 `n : Nat` 及目标假设 `h : P n` 和目标 `Q n`，`cases n` 生成两个目标：假设 `h : P 0` 和目标 `Q 0`，以及假设 `h : P (Nat.succ a)` 和目标 `Q (Nat.succ a)`。此处名称 `a` 自动生成且不可访问。可使用 `with` 为各构造子指定变量名。  
- `cases e`（`e` 为表达式而非变量）将 `e` 在目标中泛化，然后对结果变量进行案例拆分。  
- 给定 `as : List α`，`cases as with | nil => tac₁ | cons a as' => tac₂` 对 `nil` 案例使用 `tac₁`，对 `cons` 案例使用 `tac₂`，其中 `a` 和 `as'` 为新引入变量名。  
- `cases h : e`（`e` 为变量或表达式）对 `e` 进行案例拆分，并为每个案例添加假设 `h : e = ...`，其中 `...` 为该案例的构造子实例。  

## cases'
定义于：`Mathlib.Tactic.cases'`

`cases'` 策略类似 Lean 4 核心的 `cases`，但命名语法不同：  

```lean
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```  

推荐优先使用 `cases` 或 `rcases`，因其支持结构化证明。  

## cases_first_enat
定义于：`Mathlib.Tactic.ENatToNat.tacticCases_first_enat`

在上下文中查找首个 `ENat` 并对其应用 `cases` 策略，随后使用 `enat_to_nat_top` 简化集简化含 `⊤` 的表达式。  

## cases_type
定义于：`Mathlib.Tactic.casesType`

* `cases_type I` 对假设 `h : (I ...)` 应用 `cases` 策略。  
* `cases_type I_1 ... I_n` 对假设 `h : (I_1 ...)` 或 ... 或 `h : (I_n ...)` 应用 `cases` 策略。  
* `cases_type* I` 为 `· repeat cases_type I` 的简写。  
* `cases_type! I` 仅在生成子目标数 ≤ 1 时应用 `cases`。  

示例：以下策略解构当前目标中所有合取与析取。  
```lean
cases_type* Or And
```  

## cases_type!
定义于：`Mathlib.Tactic.casesType!`

* `cases_type I` 对假设 `h : (I ...)` 应用 `cases` 策略。  
* `cases_type I_1 ... I_n` 对假设 `h : (I_1 ...)` 或 ... 或 `h : (I_n ...)` 应用 `cases` 策略。  
* `cases_type* I` 为 `· repeat cases_type I` 的简写。  
* `cases_type! I` 仅在生成子目标数 ≤ 1 时应用 `cases`。  

示例：以下策略解构当前目标中所有合取与析取。  
```lean
cases_type* Or And
```  

## casesm
定义于：`Mathlib.Tactic.casesM`

`casesm` 允许使用模式匹配语法指定多个目标进行案例拆分。例如：  
```lean
casesm _ ∨ _  -- 拆分所有析取假设
casesm _ ∧ _  -- 拆分所有合取假设
```

* `casesm p` 对假设 `h : type` 应用 `cases` 策略，前提是 `type` 匹配模式 `p`。
* `casesm p_1, ..., p_n` 对假设 `h : type` 应用 `cases` 策略，前提是 `type` 匹配任一给定模式。
* `casesm* p` 是 `· repeat casesm p` 的更高效简洁版本，由于模式只需编译一次，因此效率更高。
* `casesm! p` 仅在生成的子目标数 ≤ 1 时应用 `cases`。

示例：以下策略在当前上下文中解构所有合取与析取。
```lean
casesm* _ ∨ _, _ ∧ _
```

## casesm!
定义于：`Mathlib.Tactic.casesm!`

* `casesm p` 对假设 `h : type` 应用 `cases` 策略，前提是 `type` 匹配模式 `p`。
* `casesm p_1, ..., p_n` 对假设 `h : type` 应用 `cases` 策略，前提是 `type` 匹配任一给定模式。
* `casesm* p` 是 `· repeat casesm p` 的更高效简洁版本，由于模式只需编译一次，因此效率更高。
* `casesm! p` 仅在生成的子目标数 ≤ 1 时应用 `cases`。

示例：以下策略在当前上下文中解构所有合取与析取。
```lean
casesm* _ ∨ _, _ ∧ _
```

## cc
定义于：`Mathlib.Tactic.cc`

同余闭包策略 `cc` 试图通过链式应用上下文中的等式及同余（即若 `a = b`，则 `f a = f b`）来解决目标。它是终结策略，旨在关闭当前目标而非取得不确定的进展。一个简单的示例如下：

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by
  cc
```

需要手动推导的示例如下：

```lean
example (f : ℕ → ℕ) (x : ℕ)
    (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
    f x = x := by
  cc
```

## cfc_cont_tac
定义于：`cfcContTac`

用于自动解除与连续函数演算相关目标的策略，特别涉及函数的连续性。

## cfc_tac
定义于：`cfcTac`

用于自动解除与连续函数演算相关目标的策略，特别是元素是否满足谓词。

## cfc_zero_tac
定义于：`cfcZeroTac`

用于自动解除与非单位连续函数演算相关目标的策略，特别是验证 `f 0 = 0`。

## change
定义于：`Lean.Parser.Tactic.change`

* `change tgt'` 将目标从 `tgt` 更改为 `tgt'`，假设二者定义等价。
* `change t' at h` 将假设 `h : t` 的类型更改为 `t'`，假设 `t` 和 `t'` 定义等价。

## change
定义于：`Lean.Parser.Tactic.changeWith`

* `change a with b` 将目标中的 `a` 更改为 `b`，假设二者定义等价。
* `change a with b at h` 类似地更改假设 `h` 类型中的 `a` 为 `b`。

## change?
定义于：`change?`

`change? term` 将 `term` 与当前目标统一，然后建议使用统一后的 `term` 的显式 `change` 语法。

若 `term` 未提供，`change?` 将建议当前目标本身。这在需要删除维持定义等价的先前策略（如 `dsimp`）时有用。

```lean
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- `Try this: change 0 = 1`
```

## check_compositions
定义于：`Mathlib.Tactic.CheckCompositions.tacticCheck_compositions`

对于目标中的每个组合 `f ≫ g`（内部表示为 `CategoryStruct.comp C inst X Y Z f g`），推断 `f` 和 `g` 的类型，并在“实例与可约简”透明级别检查其来源和目标是否与 `X`、`Y` 和 `Z` 一致，报告任何差异。

示例：

```
example (j : J) :
    colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv =
      H.map (G.map (colimit.ι F j)) := by

  -- 已知想使用的引理，甚至是simp引理，但`rw`不允许应用
  fail_if_success rw [ι_preservesColimitIso_inv]
  fail_if_success rw [ι_preservesColimitIso_inv (G ⋙ H)]
  fail_if_success simp only [ι_preservesColimitIso_inv]

  -- 这会有效：
  -- erw [ι_preservesColimitIso_inv (G ⋙ H)]

  -- `check_compositions`检查是否存在滥用定义的组合，并提示定义性结合性问题。

  check_compositions

  -- 此处可通过重新结合目标来“修复”，但通常应回溯检查问题根源。
  dsimp only [Functor.assoc]

  -- 此时可应用`rw`，但`simp`同样有效。
  -- rw [ι_preservesColimitIso_inv]

  simp
```

## choose
定义于：`Mathlib.Tactic.Choose.choose`

* `choose a b h h' using hyp` 接受形如 `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b` 的假设 `hyp`，输出函数 `a : X → Y → A`、`b : X → Y → B` 及假设 `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` 和 `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`。支持依赖版本。

* `choose! a b h h' using hyp` 类似，但尽可能移除函数对命题参数的依赖。例如若 `Y` 为命题且 `A`、`B` 非空，则得到 `a : X → A`、`b : X → B` 及假设 `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` 和 `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`。

可省略 `using hyp`，此时 `choose` 会以 `intro hyp` 开始。

示例：

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```

## choose!
定义于：`Mathlib.Tactic.Choose.tacticChoose!___Using_`

* `choose a b h h' using hyp` 接受形如 `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b` 的假设 `hyp`，输出函数 `a : X → Y → A`、`b : X → Y → B` 及假设 `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` 和 `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`。支持依赖版本。

* `choose! a b h h' using hyp` 类似，但尽可能移除函数对命题参数的依赖。例如若 `Y` 为命题且 `A`、`B` 非空，则得到 `a : X → A`、`b : X → B` 及假设 `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` 和 `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`。

可省略 `using hyp`，此时 `choose` 会以 `intro hyp` 开始。

示例：

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```

## classical
定义于：`Lean.Parser.Tactic.classical`

`classical tacs` 在 `Classical.propDecidable` 作为低优先级局部实例的范围内运行 `tacs`。

注意，`classical` 是一个作用域策略：它仅在策略的作用域内添加该实例。

## clean
定义于：`Mathlib.Tactic.tacticClean_`

（已弃用）`clean t` 是 `exact clean% t` 的宏。

## clean_wf
定义于：`tacticClean_wf`

此策略由 Lean 内部在通过 `decreasing_by` 向用户展示良基定义产生的证明义务之前使用。无需手动使用此策略。

## clear
定义于：`Lean.Elab.Tactic.clearExcept`

清除所有可清除的假设，除了减号后提供的那些。示例：
```lean
  clear * - h₁ h₂
```

## clear
定义于：`Lean.Parser.Tactic.clear`

`clear x...` 移除给定假设，若假设仍被引用则失败。

## clear!
定义于：`Mathlib.Tactic.clear!`

`clear` 的变体，不仅清除给定假设，还清除依赖它们的其他假设。

## clear_
定义于：`Mathlib.Tactic.clear_`

清除所有以下划线开头的假设，如 `_match` 和 `_let_match`。

## clear_aux_decl
定义于：`Mathlib.Tactic.clearAuxDecl`

此策略清除上下文中的所有辅助声明。

## clear_value
定义于：`Mathlib.Tactic.clearValue`

`clear_value n₁ n₂ ...` 清除局部定义 `n₁, n₂ ...` 的主体，将其变为普通假设。假设 `n : α := t` 将变为 `n : α`。

`n₁ n₂ ...` 的顺序无关紧要，值将按其在上下文中出现的逆序清除。

## coherence
定义于：`Mathlib.Tactic.Coherence.coherence`

使用幺半范畴的连贯定理解决幺半方程，其中两边仅通过用具有相同源和目标的幺半结构态射（即结合子、单位子和恒等态射）的不同字符串替换来区分。

即，`coherence` 可处理形式为 `a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'` 的目标，其中 `a = a'`、`b = b'` 和 `c = c'` 可使用 `pure_coherence` 证明。

（若 `coherence` 在处理大方程时意外失败，可能需要增加类型类搜索深度，如使用 `set_option synthInstance.maxSize 500`。）

## compareOfLessAndEq_rfl
定义于：`tacticCompareOfLessAndEq_rfl`

此策略尝试通过引入参数并按以下顺序应用方法，证明给定的 `compare` 实例等于 `compareOfLessAndEq`：

1. 检查 `rfl` 是否有效。
2. 检查当前的 `compare` 是否本质上是 `compareOfLessAndEq`，但因隐式参数需要展开定义并拆分 `compareOfLessAndEq` 中的 `if`。
3. 若无法拆分参数，则尝试通过案例分析参数，让定义自行解决（适用于 `compare` 通过 `match` 语句定义的情况，如 `Bool`）。

## compute_degree
定义于：`Mathlib.Tactic.ComputeDegree.computeDegree`

`compute_degree` 是解决以下形式目标的策略：
* `natDegree f = d`
* `degree f = d`
* `natDegree f ≤ d`
* `degree f ≤ d`
* `coeff f d = r`（若 `d` 为 `f` 的次数）

该策略可能留下形式为 `d' = d`、`d' ≤ d` 或 `r ≠ 0` 的子目标，其中 `d'` 为策略猜测的次数（`ℕ` 或 `WithBot ℕ`），`r` 为猜测的 `f` 的首项系数。

`compute_degree` 对所有子目标的左侧应用 `norm_num`，尝试关闭它们。

变体 `compute_degree!` 首先应用 `compute_degree`，然后在剩余目标上使用 `norm_num` 并尝试 `assumption`。

## compute_degree!
定义于：`Mathlib.Tactic.ComputeDegree.tacticCompute_degree!`

`compute_degree` 是解决以下形式目标的策略：
* `natDegree f = d`
* `degree f = d`
* `natDegree f ≤ d`
* `degree f ≤ d`
* `coeff f d = r`（若 `d` 为 `f` 的次数）

该策略可能留下形式为 `d' = d`、`d' ≤ d` 或 `r ≠ 0` 的子目标，其中 `d'` 为策略猜测的次数（`ℕ` 或 `WithBot ℕ`），`r` 为猜测的 `f` 的首项系数。

`compute_degree` 对所有子目标的左侧应用 `norm_num`，尝试关闭它们。

变体 `compute_degree!` 首先应用 `compute_degree`，然后在剩余目标上使用 `norm_num` 并尝试 `assumption`。

## congr
定义于：`Lean.Parser.Tactic.congr`

对形如 `⊢ f as = f bs` 和 `⊢ HEq (f as) (f bs)` 的目标应用同余（递归）。可选参数为递归应用的深度。当 `congr` 分解目标过于激进时，此参数有用。例如，给定 `⊢ f (g (x + y)) = f (g (y + x))`，`congr` 产生目标 `⊢ x = y` 和 `⊢ y = x`，而 `congr 2` 产生预期的 `⊢ x + y = y + x`。

## congr
定义于：`Batteries.Tactic.congrConfigWith`

对形如 `⊢ f as = f bs` 和 `⊢ HEq (f as) (f bs)` 的目标应用同余（递归）。
* `congr n` 控制递归应用的深度。当 `congr` 分解目标过于激进时，此参数有用。例如，给定 `⊢ f (g (x + y)) = f (g (y + x))`，`congr` 产生目标 `⊢ x = y` 和 `⊢ y = x`，而 `congr 2` 产生预期的 `⊢ x + y = y + x`。
* 若在任何时候子目标匹配假设，则该子目标将被关闭。
* 可使用 `congr with p (: n)?` 调用 `ext p (: n)?` 到所有由 `congr` 生成的子目标。例如，若目标为 `⊢ f '' s = g '' s`，则 `congr with x` 生成目标 `x : α ⊢ f x = g x`。

## congr
定义于：`Batteries.Tactic.congrConfig`

对形如 `⊢ f as = f bs` 和 `⊢ HEq (f as) (f bs)` 的目标应用同余（递归）。可选参数为递归应用的深度。当 `congr` 分解目标过于激进时，此参数有用。例如，给定 `⊢ f (g (x + y)) = f (g (y + x))`，`congr` 产生目标 `⊢ x = y` 和 `⊢ y = x`，而 `congr 2` 产生预期的 `⊢ x + y = y + x`。

## congr!
定义于：`Congr!.congr!`

通过递归应用同余引理，将目标的左侧部分等同于右侧对应部分。例如，对于 `⊢ f as = g bs`，可能得到两个目标 `⊢ f = g` 和 `⊢ as = bs`。

语法：
```lean
congr!
congr! n
congr! with x y z
congr! n with x y z
```
其中，`n` 为自然数，`x`、`y`、`z` 为 `rintro` 模式（如 `h`、`rfl`、`⟨x, y⟩`、`_`、`-`、`(h | h)` 等）。

`congr!` 策略类似于 `congr`，但在尝试将目标左侧等同于右侧时更为坚持。以下是其可能尝试的方法：

- 若目标 `⊢ R x y` 中的 `R` 为自反关系，则在可能的情况下将目标转换为 `⊢ x = y`。自反关系列表通过 `@[refl]` 属性维护。作为特例，`⊢ p ↔ q` 在同余处理期间转换为 `⊢ p = q`，并在最后恢复为 `⊢ p ↔ q`。

- 若有用户同余引理与目标关联（例如，应用 `@[congr]` 标记的引理至 `⊢ List.map f xs = List.map g ys`），则使用该引理。

- 使用至少与 `congr` 和 `simp` 同等的同余引理生成器。若有子表达式可通过 `simp` 重写，则 `congr!` 应能为其生成等式。

- 可使用如 `implies_congr` 和 `pi_congr` 的引理进行 Pi 类型的同余。

- 在应用同余前，自动运行 `intros` 策略。引入的变量可通过 `with` 子句命名，有助于同余引理在假设中提供额外条件时使用。

- 当函数间存在等式时，只要至少有一个明显为 lambda，应用 `funext` 或 `Function.hfunext`，允许 lambda 体的同余。

- 尝试通过几种策略关闭目标，包括检查定义等式、应用 `Subsingleton.elim` 或 `proof_irrel_heq`，以及使用 `assumption` 策略。

可选参数是递归应用的深度。这在`congr!`过于激进地分解目标时非常有用。例如，给定`⊢ f (g (x + y)) = f (g (y + x))`，`congr!`会生成目标`⊢ x = y`和`⊢ y = x`，而`congr! 2`则生成预期的`⊢ x + y = y + x`。

`congr!`策略还接受配置选项，例如：
```lean
congr! (config := {transparency := .default}) 2
```
这会覆盖默认设置，即在可约透明度下应用协变引理。

`congr!`策略在等式两边非常积极。有一个预定义配置使用不同的策略：
尝试
```lean
congr! (config := .unfoldSameFun)
```
这仅允许在定义上相等的函数应用之间进行协变，并在默认透明度（而非仅可约透明度）下应用协变引理。这类似于`congr`。

有关所有选项，请参见`Congr!.Config`。

## congrm

定义于：`Mathlib.Tactic.congrM`

`congrm e`是用于证明形如`lhs = rhs`、`lhs ↔ rhs`、`HEq lhs rhs`或当`R`是自反关系时的`R lhs rhs`目标的策略。表达式`e`是一个包含占位符`?_`的模式，此模式会同时与`lhs`和`rhs`匹配。这些占位符生成新的目标，声明`lhs`和`rhs`中的对应子表达式相等。如果占位符有名称（如`?m`），则新目标将带有这些名称的标签。

示例：
```lean
example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ ?h1) * (?h2 + ?h3)
  /- 剩余目标：
  case h1 ⊢ a = b
  case h2 ⊢ d = b
  case h3 ⊢ c + a.pred = c + d.pred
  -/
  sorry
  sorry
  sorry

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm fun x => ∀ w, ?_ + a = w
  -- ⊢ a = b
  exact h
```

`congrm`命令是`congr(...)`协变引用的便捷前端。如果目标是等式，`congrm e`等价于`refine congr(e')`，其中`e'`通过将每个占位符`?m`替换为`$(?m)`构建而成。模式`e`允许包含`$(...)`表达式，以便像协变引用一样立即将等式证明代入协变。

## congrm?

定义于：`tacticCongrm?`

显示一个小部件面板，允许通过选择目标中的子表达式生成带有指定孔的`congrm`调用。

## constructor

定义于：`Lean.Parser.Tactic.constructor`

如果主目标的目标类型是归纳类型，`constructor`使用第一个匹配的构造函数解决它，否则失败。

## constructorm

定义于：`Mathlib.Tactic.constructorM`

* `constructorm p_1, ..., p_n`将`constructor`策略应用于主目标，如果`type`匹配任一给定模式。
* `constructorm* p`是`· repeat constructorm p`的更高效紧凑版本。由于模式仅编译一次，因此更高效。

示例：以下策略证明了任何由和/或/真构成的定理，如`True ∧ (True ∨ True)`：
```lean
constructorm* _ ∨ _, _ ∧ _, True
```

## continuity

定义于：`tacticContinuity`

`continuity`策略通过应用带有`continuity`用户属性的引理来解决形如`Continuous f`的目标。

## continuity?

定义于：`tacticContinuity?`

`continuity`策略通过应用带有`continuity`用户属性的引理来解决形如`Continuous f`的目标。

## contradiction

定义于：`Lean.Parser.Tactic.contradiction`

如果假设“显然矛盾”，`contradiction`将关闭主目标。

- 无适用构造函数的归纳类型/族
  ```lean
  example (h : False) : p := by contradiction
  ```
- 构造函数的注入性
  ```lean
  example (h : none = some true) : p := by contradiction  --
  ```
- 可判定的假命题
  ```lean
  example (h : 2 + 2 = 3) : p := by contradiction
  ```
- 矛盾的假设
  ```lean
  example (h : p) (h' : ¬ p) : q := by contradiction
  ```
- 其他简单矛盾，如
  ```lean
  example (x : Nat) (h : x ≠ x) : p := by contradiction
  ```

## contrapose

定义于：`Mathlib.Tactic.Contrapose.contrapose`

将目标转换为其逆否命题。
* `contrapose`     将目标`P → Q`转换为`¬ Q → ¬ P`
* `contrapose h`   首先还原局部假设`h`，然后使用`contrapose`和`intro h`
* `contrapose h with new_h`使用名称`new_h`引入假设

## contrapose!

定义于：`Mathlib.Tactic.Contrapose.contrapose!`

将目标转换为其逆否命题，并将否定推入`P`和`Q`内部。用法与`contrapose`相同。

## conv

定义于：`Lean.Parser.Tactic.Conv.conv`

`conv => ...`允许用户通过聚焦特定子表达式，在目标或假设上执行针对性重写。

详见<https://lean-lang.org/theorem_proving_in_lean4/conv.html>。

基本形式：
* `conv => cs`将用转换策略`cs`重写目标。
* `conv at h => cs`将重写假设`h`。
* `conv in pat => cs`将重写第一个匹配`pat`的子表达式（参见`pattern`）。

## conv'

定义于：`Lean.Parser.Tactic.Conv.convTactic`

执行给定的转换块，而不将常规目标转换为`conv`目标。

## conv?

定义于：`tacticConv?`

显示一个小部件面板，允许生成聚焦到目标中选定子表达式的`conv`调用。

## conv_lhs

定义于：`Mathlib.Tactic.Conv.convLHS`

## conv_rhs

定义于：`Mathlib.Tactic.Conv.convRHS`

## convert

定义于：`Mathlib.Tactic.convert`

`exact e`和`refine e`策略需要类型与目标定义上相等的项`e`。`convert e`类似于`refine e`，但`e`的类型不需要完全匹配目标。相反，使用与`congr!`策略相同的策略为`e`的类型与目标之间的差异创建新目标。例如，在证明状态

```lean
n : ℕ,
e : Prime (2 * n + 1)
⊢ Prime (n + n + 1)
```

中，策略`convert e using 2`将目标更改为

```lean
⊢ n + n = 2 * n
```

在此示例中，新目标可使用`ring`解决。

`using 2`表示应迭代协变算法最多两次，而`convert e`将使用无限制的迭代次数，导致两个不可能的目标：`⊢ HAdd.hAdd = HMul.hMul`和`⊢ n = 2`。

一种变体配置是`convert (config := .unfoldSameFun) e`，它仅对同一函数的函数应用等式化（同时在更高的`default`透明度下进行）。这在不需要`using 2`的情况下给出相同目标`⊢ n + n = 2 * n`。

`convert`策略在简化之前急切地应用协变引理，因此在`exact`成功的情况下可能失败：
```lean
def p (n : ℕ) := True
example (h : p 0) : p 1 := by exact h -- 成功
example (h : p 0) : p 1 := by convert h -- 失败，剩余目标`1 = 0`
```
限制递归深度可以帮助解决此问题。例如，在此情况下`convert h using 1`将有效。

语法`convert ← e`将反转新目标的方向（在此示例中生成`⊢ 2 * n = n + n`）。

内部上，`convert e`通过创建一个断言目标等于`e`类型的新目标，然后使用`congr!`简化它。语法`convert e using n`可用于控制匹配深度（如`congr! n`）。在示例中，`convert e using 1`将生成新目标`⊢ n + n + 1 = 2 * n + 1`。

有关协变操作，请参考`congr!`策略。其众多功能之一是，如果`x y : t`且作用域中有实例`Subsingleton t`，则任何形如`x = y`的目标将自动解决。

与`congr!`类似，`convert`接受可选的`with`子句（`rintro`模式），例如`convert e using n with x y z`。

`convert`策略还接受配置选项，例如
```lean
convert (config := {transparency := .default}) h
```
这些选项传递给`congr!`。有关选项，请参见`Congr!.Config`。

## convert_to
定义于：`Mathlib.Tactic.convertTo`

`convert_to` 策略用于改变目标或局部假设的类型，但与`change`策略不同，它会通过`congr!`生成等式证明义务来解决差异。

* `convert_to ty` 将目标改为`ty`
* `convert_to ty using n` 使用`congr! n`而非`congr! 1`
* `convert_to ty at h` 将局部假设`h`的类型改为`ty`。剩余的`congr!`目标会优先处理。

作用于目标时，策略`convert_to ty using n`等同于`convert (?_ : ty) using n`。区别在于`convert_to`接受类型而`convert`接受证明项。

除了能够操作局部假设外，`convert_to`的语法与`convert`相同，并具有如`convert_to ← g`和`convert_to (config := {transparency := .default}) g`等变体。

注意，`convert_to ty at h`可能会保留`h`的副本，如果后续的局部假设或目标依赖于它，这与`rw`或`simp`中的情况类似。

## count_heartbeats
定义于：`Mathlib.CountHeartbeats.tacticCount_heartbeats`

自“2025-01-12”起，`count_heartbeats`已弃用，推荐使用`#count_heartbeats`

## dbg_trace
定义于：`Lean.Parser.Tactic.dbgTrace`

`dbg_trace "foo"`在代码被详细阐述时打印`foo`。对调试策略控制流很有用：
```lean
example : False ∨ True := by
  first
  | apply Or.inl; trivial; dbg_trace "left"
  | apply Or.inr; trivial; dbg_trace "right"
```

## decide
定义于：`Lean.Parser.Tactic.decide`

`decide`尝试通过合成一个`Decidable p`的实例并缩减该实例以评估`p`的真值来证明主目标（目标类型为`p`）。若缩减为`isTrue h`，则`h`即为关闭目标的`p`的证明。

目标中不允许包含局部变量或元变量。若存在局部变量，可先使用`revert`策略将这些局部变量移至目标中，或使用`+revert`选项（见下文）。

选项：
- `decide +revert`首先还原目标依赖的局部变量，并清理无关变量的局部上下文。若变量出现在目标中、相关变量中，或作为涉及相关变量的命题，则视为*相关*。
- `decide +kernel`使用内核而非详细阐述器进行缩减。其关键特性为：(1) 因使用内核，故忽略透明度并可展开所有内容；(2) 仅缩减`Decidable`实例一次而非两次。
- `decide +native`使用原生代码编译器（`#eval`）评估`Decidable`实例，通过`Lean.ofReduceBool`公理接受结果。此方式可能比缩减更高效，但代价是增大可信代码库规模。即，其依赖于Lean编译器及所有带`@[implemented_by]`属性的定义的正确性。与`+kernel`类似，`Decidable`实例仅评估一次。

限制：在默认模式或`+kernel`模式下，由于`decide`使用缩减评估项，基于良基递归定义的`Decidable`实例可能无效，因其评估需要缩减证明。缩减也可能在处理含`Eq.rec`项的`Decidable`实例时卡住。这些项可能出现在使用策略（如`rw`和`simp`）定义的实例中。为避免此问题，请使用如`decidable_of_iff`等定义来创建此类实例。

示例：

证明不等式：
```lean
example : 2 + 2 ≠ 5 := by decide
```

尝试证明错误命题：
```lean
example : 1 ≠ 1 := by decide
/-
策略 'decide' 证明命题
  1 ≠ 1
为假
-/
```

尝试证明`Decidable`实例未能缩减的命题：
```lean
opaque unknownProp : Prop

open scoped Classical in
example : unknownProp := by decide
/-
策略 'decide' 对命题
  unknownProp
失败，因其 'Decidable' 实例缩减为
  Classical.choice ⋯
而非 'isTrue' 构造子。
-/
```

## 性质与关系

对于具有可判定相等性的类型的等式目标，通常可用`rfl`替代`decide`。
```lean
example : 1 + 1 = 2 := by decide
example : 1 + 1 = 2 := by rfl
```

## decreasing_tactic
定义于：`tacticDecreasing_tactic`

默认情况下，`decreasing_tactic`在良基递归中被调用，以合成递归调用沿选定良基关系递减的证明。可通过在递归定义中使用`decreasing_by tac`局部覆盖，或通过添加更多`decreasing_tactic`（或调用此策略的`decreasing_trivial`）的定义全局扩展。

## decreasing_trivial
定义于：`tacticDecreasing_trivial`

可扩展的`decreasing_tactic`辅助策略。此策略处理应用字典序引理后的“基本情况”推理。可通过添加更多宏定义进行扩展，例如：
```lean
macro_rules | `(tactic| decreasing_trivial) => `(tactic| linarith)
```

## decreasing_trivial_pre_omega
定义于：`tacticDecreasing_trivial_pre_omega`

`decreasing_trivial`的变体，不使用`omega`，旨在核心模块中`omega`不可用时使用。

## decreasing_with
定义于：`tacticDecreasing_with_`

通过简化后应用字典序引理，最后使用`ts`解决基本情况，构造沿良基关系递减的证明。若失败，则打印信息以帮助用户诊断非良基递归定义。

## delta
定义于：`Lean.Parser.Tactic.delta`

`delta id1 id2 ...`对定义`id1`, `id2`, ...进行delta展开。此为底层策略，将暴露Lean如何编译递归定义。

## discrete_cases
定义于：`CategoryTheory.Discrete.tacticDiscrete_cases`

对任何`Discrete α`假设执行`cases`的简单策略。

## done
定义于：`Lean.Parser.Tactic.done`

`done`在无剩余目标时成功。

## dsimp
定义于：`Lean.Parser.Tactic.dsimp`

`dsimp`策略为定义简化器。其类似于`simp`但仅应用通过自反性成立的定理。因此，结果保证与输入定义相等。

## dsimp!
定义于：`Lean.Parser.Tactic.dsimpAutoUnfold`

`dsimp!`为`dsimp`的简写，设置`autoUnfold := true`。这将用所有等式引理重写，可用于部分评估许多定义。

## dsimp?
定义于：`Lean.Parser.Tactic.dsimpTrace`

`simp?`接受与`simp`相同的参数，但报告足以关闭目标的等效`simp only`调用。此有助于减少局部调用中的simp集大小以加速处理。
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- 输出 "Try this: simp only [ite_true]"
```

此命令也可用于`simp_all`和`dsimp`。

## dsimp?!
定义于：`Lean.Parser.Tactic.tacticDsimp?!_`

`simp?`接受与`simp`相同的参数，但报告足以关闭目标的等效`simp only`调用。此有助于减少局部调用中的simp集大小以加速处理。
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- 输出 "Try this: simp only [ite_true]"
```

此命令也可用于`simp_all`和`dsimp`。

## eapply
定义于：`Batteries.Tactic.tacticEapply_`

`eapply e`类似于`apply e`，但不会为出现在其他目标类型中的变量添加子目标。注意，这可能导致无剩余目标但项中仍有元变量的失败：
```lean
example (h : ∀ x : Nat, x = x → True) : True := by
  eapply h
  rfl
  -- 无目标
-- (内核) 声明存在元变量 '_example'
```

## econstructor
定义于：`tacticEconstructor`

`econstructor`应用构造函数，但不会为出现在其他目标中的元变量添加新目标。此策略对存在量词目标特别有用。
```lean
example : ∃ x : Nat, x = x := by
  econstructor
  exact 0
  rfl
```

`econstructor` 类似于 `constructor`
（它使用归纳数据类型的第一个匹配构造器调用 `apply`）
但仅将非依赖前提作为新目标添加。

## elementwise
定义于：`Tactic.Elementwise.tacticElementwise___`


## elementwise!
定义于：`Tactic.Elementwise.tacticElementwise!___`


## else
定义于：`Lean.Parser.Tactic.tacDepIfThenElse`

在策略模式中，`if h : t then tac1 else tac2` 可作为以下语法的替代：
```lean
by_cases h : t
· tac1
· tac2
```
它根据 `h : t` 或 `h : ¬t` 进行情况分析，`tac1` 和 `tac2` 为子证明。

可使用 `?_` 或 `_` 延迟任一子证明至策略之后，但如果为 `tac1` 或 `tac2` 提供了策略序列，则要求该块结束时目标必须闭合。

## else
定义于：`Lean.Parser.Tactic.tacIfThenElse`

在策略模式中，`if t then tac1 else tac2` 是以下语法的替代：
```lean
by_cases t
· tac1
· tac2
```
它根据匿名假设 `h† : t` 或 `h† : ¬t` 进行情况分析，`tac1` 和 `tac2` 为子证明。（实际上未使用非依赖 `if`，因这不会向上下文中添加任何内容，故对定理证明无用。要实际插入 `ite` 应用，请使用 `refine if t then ?_ else ?_`。）

## enat_to_nat
定义于：`Mathlib.Tactic.ENatToNat.tacticEnat_to_nat`

`enat_to_nat` 将上下文中的所有 `ENat` 转换为 `Nat`，并重写相关命题。典型用例为 `enat_to_nat; omega`。

## eq_refl
定义于：`Lean.Parser.Tactic.eqRefl`

`eq_refl` 等效于 `exact rfl`，但进行了一些优化。

## erw
定义于：`Lean.Parser.Tactic.tacticErw___`

`erw [rules]` 是 `rw (transparency := .default) [rules]` 的简写。此操作通过常规定义展开进行重写（相比常规 `rw` 仅展开 `@[reducible]` 定义）。

## erw?
定义于：`Mathlib.Tactic.Erw?.erw?`

`erw? [r]` 调用 `erw [r]`（注意仅允许单步操作），随后尝试识别可能阻碍使用 `rw` 的子表达式。通过识别在可约透明度下定义等价但非完全等价的子表达式实现。

## eta_expand
定义于：`Mathlib.Tactic.etaExpandStx`

`eta_expand at loc` 对给定位置的所有子表达式进行 eta 展开。同时 beta 归约任何 eta 展开项的应用，故将其置于 eta 展开的“正规形式”。此策略亦存在于 `conv` 模式。

例如，若 `f` 接受两个参数，则 `f` 变为 `fun x y => f x y`，而 `f x` 变为 `fun y => f x y`。

此操作可用于将例如原始 `HAdd.hAdd` 转换为 `fun x y => x + y`。

## eta_reduce
定义于：`Mathlib.Tactic.etaReduceStx`

`eta_reduce at loc` 对给定位置的所有子表达式进行 eta 归约。此策略亦存在于 `conv` 模式。

例如，`fun x y => f x y` 经 eta 归约后变为 `f`。

## eta_struct
定义于：`Mathlib.Tactic.etaStructStx`

`eta_struct at loc` 将结构构造器应用如 `S.mk x.1 ... x.n`（例如漂亮打印为 `{a := x.a, b := x.b, ...}`）转换为 `x`。此策略亦存在于 `conv` 模式。

此转换称为结构的 eta 归约，生成定义相等的表达式。

例如，给定 `x : α × β`，则 `(x.1, x.2)` 经此转换后变为 `x`。

## exact
定义于：`Lean.Parser.Tactic.exact`

`exact e` 在主目标类型与 `e` 的类型匹配时闭合该目标。

## exact?
定义于：`Lean.Parser.Tactic.exact?`

在环境中搜索可通过 `exact` 结合 `solve_by_elim` 解决条件来闭合目标的定义或定理。

可选 `using` 子句提供局部上下文中必须被 `exact?` 用于闭合目标的标识符。这在存在多种闭合目标方式且需指导使用特定引理时尤为有用。

## exact_mod_cast
定义于：`Lean.Parser.Tactic.tacticExact_mod_cast_`

规范化目标及给定表达式中的强制转换，随后使用 `exact` 闭合目标。

## exacts
定义于：`Batteries.Tactic.exacts`

类似 `exact`，但接受一系列项并检查所有目标在策略后均已闭合。

## exfalso
定义于：`Lean.Parser.Tactic.tacticExfalso`

`exfalso` 通过应用 `False.elim` 将目标 `⊢ tgt` 转换为 `⊢ False`。

## exists
定义于：`Lean.Parser.Tactic.«tacticExists_,,»`

`exists e₁, e₂, ...` 是 `refine ⟨e₁, e₂, ...⟩; try trivial` 的简写，适用于存在目标。

## existsi
定义于：`Mathlib.Tactic.«tacticExistsi_,,»`

`existsi e₁, e₂, ⋯` 应用策略 `refine ⟨e₁, e₂, ⋯, ?_⟩`，其目的在于实例化存在量词。

示例：

```lean
example : ∃ x : Nat, x = x := by
  existsi 42
  rfl

example : ∃ x : Nat, ∃ y : Nat, x = y := by
  existsi 42, 42
  rfl
```

## expose_names
定义于：`Lean.Parser.Tactic.exposeNames`

`expose_names` 将所有不可访问变量重命名为可访问名称，使其在生成策略中可引用。但此重命名引入的机器生成名称不完全受用户控制。`expose_names` 主要用作自动生成终局策略脚本的前导。其亦可作为 `set_option tactic.hygienic false` 的替代。若需在策略脚本中间显式控制重命名，可考虑使用带用户定义名称的结构化策略脚本，如 `match .. with`、`induction .. with` 或带显式名称的 `intro`，以及 `next`、`case` 和 `rename_i` 等策略。

## ext
定义于：`Lean.Elab.Tactic.Ext.ext`

应用通过 `@[ext]` 属性注册的外延性引理。
* `ext pat*` 尽可能应用外延性定理，使用模式 `pat*` 通过 `rintro` 引入外延性定理中的变量。例如，模式用于命名由 `funext` 等引理引入的变量。
* 无模式时，`ext` 尽可能应用外延性引理，但必要时引入匿名假设。
* `ext pat* : n` 仅应用外延性定理至深度 `n`。

`ext1 pat*` 策略类似 `ext pat*`，但仅应用单一外延性定理而非递归应用尽可能多。

未使用的模式将生成警告。不匹配变量的模式通常导致匿名假设的引入。

## ext1
定义于：`Lean.Elab.Tactic.Ext.tacticExt1___`

`ext1 pat*` 类似 `ext pat*`，但仅应用单一外延性定理而非递归应用尽可能多。

`pat*` 模式通过 `rintro` 策略处理。若未提供模式，则通过 `intros` 策略匿名引入变量。

## extract_goal
定义于：`Mathlib.Tactic.ExtractGoal.extractGoal`

- `extract_goal` 将当前目标格式化为独立定理或定义，清理局部上下文中的无关变量。变量*相关*若满足以下条件：(1) 出现于目标类型，(2) 存在依赖其的相关变量，或 (3) 变量类型为依赖相关变量的命题。

  若目标为 `False`，则出于便利 `extract_goal` 包含所有变量。
- `extract_goal *` 格式化当前目标但不清理局部上下文。
- `extract_goal a b c ...` 格式化当前目标，移除给定变量 `a`、`b`、`c`、... 不依赖的所有内容。
- `extract_goal ... using name` 使用名称 `name` 而非自动生成名称命名定理或定义。

此策略尝试生成可复制粘贴且直接可用的输出，但其成功取决于表达式是否适合无歧义漂亮打印。

策略响应漂亮打印选项。例如，`set_option pp.all true in extract_goal` 提供 `pp.all` 形式。

## extract_lets
定义于：`Mathlib.extractLets`

`extract_lets at h` 策略接受一个形式为 `h : let x := v; b` 的局部假设，并引入一个新的局部定义 `x := v`，同时将 `h` 修改为 `h : b`。可以将其视为针对 `let` 表达式的 `cases` 策略，或类似于针对 `let` 表达式的 `intros at h`。

例如，若 `h : let x := 1; x = x`，则执行 `extract_lets x at h` 会引入 `x : Nat := 1` 并将 `h` 修改为 `h : x = x`。

与 `intros` 类似，`extract_lets` 策略要么接受一个名称列表（此时指定必须提取的 `let` 绑定数量），要么不指定名称（此时提取所有 `let` 绑定）。

不带 `at` 的 `extract_lets` 策略或 `extract_lets at h ⊢` 可视为对目标执行较弱的 `intros`，仅引入明显的 `let` 绑定。

## fail
定义于：`Lean.Parser.Tactic.fail`

`fail msg` 是一个始终失败的策略，并使用给定消息生成错误。

## fail_if_no_progress
定义于：`Mathlib.Tactic.failIfNoProgress`

`fail_if_no_progress tacs` 执行 `tacs`，若在主目标或可约透明度的局部上下文中未取得进展则失败。

## fail_if_success
定义于：`Lean.Parser.Tactic.failIfSuccess`

`fail_if_success t` 在策略 `t` 成功时失败。

## false_or_by_contra
定义于：`Lean.Parser.Tactic.falseOrByContra`

将目标更改为 `False`，尽可能保留信息：

* 若目标为 `False`，则不做任何操作。
* 若目标为蕴含或函数类型，则引入参数并重新开始。（特别地，若目标为 `x ≠ y`，则引入 `x = y`。）
* 否则，对于命题目标 `P`，将其替换为 `¬ ¬ P`（尝试寻找 `Decidable` 实例，否则退化为经典方式处理）并引入 `¬ P`。
* 对于非命题目标，使用 `False.elim`。

## fapply
定义于：`Batteries.Tactic.tacticFapply_`

`fapply e` 类似于 `apply e`，但按出现顺序添加目标，而非将依赖目标置于首位。

## fconstructor
定义于：`tacticFconstructor`

`fconstructor` 类似于 `constructor`（它调用第一个匹配的归纳数据类型构造子的 `apply`），不同之处在于它不会重新排序目标。

## field_simp
定义于：`Mathlib.Tactic.FieldSimp.fieldSimp`

`field_simp` 的目标是通过使用名为 `field_simps` 的精心设计的简化集，将域中的表达式简化为形式 `n / d`，其中 `n` 和 `d` 均不含任何除法符号。其迭代步骤如下：

- 将逆元写为除法
- 在任何乘积中将除法移至右侧
- 若乘积中有多个除法，则将其分组至末尾并写为单一除法
- 将和式化为公分母

若目标为等式，此简化集还将清除分母，从而通常可通过应用 `ring` 完成证明。

`field_simp [hx, hy]` 是以下形式的简写：
`simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, hx, hy, field_simps]`

注意此简单算法不会尝试检测分母中的公因子以降低结果表达式的复杂度，而是依赖 `ring` 在后续步骤中处理复杂表达式。

与简化器一贯行为相同，仅当前提条件可验证时才会应用归约步骤。这意味着应包含分母非零的证明。乘积非零当且仅当其因子均非零，以及非零数的幂非零等事实已包含在简化集中，但更复杂的断言（尤其涉及和式）需显式给出。若表达式未被完全简化，请检查结果表达式的分母并提供非零证明以继续。

为验证分母非零，`field_simp` 将查找上下文中的事实，并尝试应用 `norm_num` 以闭合数值目标。

`field_simp` 调用会从简化集中移除 `one_div` 引理，因该引理与上述算法冲突。同时移除 `mul_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0`（因 `norm_num` 无法处理析取以闭合形如 `24 ≠ 0` 的目标），并以 `mul_ne_zero : x ≠ 0 → y ≠ 0 → x * y ≠ 0` 替代，从而创建两个目标而非析取。

例如：
```lean
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring
```

此外，`field_simp` 策略还可处理一般（交换）幺半群/环中的单位逆及偏除法 `/ₚ`，参见 `Algebra.Group.Units` 定义。类似地，移除 `one_divp` 引理以避免与算法冲突。若存在具有 `IsUnit x` 实例的对象如 `(x : R) (hx : IsUnit x)`，应在使用 `field_simp` 前通过 `lift x to Rˣ using id hx; rw [IsUnit.unit_of_val_units] clear hx` 提升。

另见 `cancel_denoms` 策略，其尝试对含数值分母的表达式进行类似简化。两者无关联：`cancel_denoms` 仅处理数值分母，并通过乘以因子尝试完全移除（数值）除法。

## field_simp_discharge
定义于：`Mathlib.Tactic.FieldSimp.tacticField_simp_discharge`

`field_simp` 策略的放电策略。

## filter_upwards
定义于：`Mathlib.Tactic.filterUpwards`

`filter_upwards [h₁, ⋯, hₙ]` 将形如 `s ∈ f` 的目标及项 `h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` 替换为 `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`。列表为可选参数，默认值为 `[]`。

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` 是 `{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }` 的简写。

`filter_upwards [h₁, ⋯, hₙ] using e` 是 `{ filter_upwards [h1, ⋯, hn], exact e }` 的简写。

组合两种简写可写作 `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`。注意此时 `aᵢ` 可在 `e` 中使用。

## fin_cases
定义于：`Lean.Elab.Tactic.finCases`

`fin_cases h` 对假设 `h : A`（其中 `[Fintype A]` 可用）或 `h : a ∈ A`（其中 `A : Finset X`、`A : Multiset X` 或 `A : List X`）执行案例分析。

例如：
```lean
example (f : ℕ → Prop) (p : Fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val := by
  fin_cases p; simp
  all_goals assumption
```
执行 `fin_cases p; simp` 后，将生成三个目标：`f 0`、`f 1` 和 `f 2`。

## fin_omega
定义于：`Fin.tacticFin_omega`

`omega` 的前处理器，用于处理 `Fin` 中的不等式。注意此过程涉及大量情况分割，可能较慢。

## find
定义于：`Mathlib.Tactic.Find.tacticFind`


## finiteness
定义于：`finiteness`

解决扩展非负实数（`ℝ≥0∞`）中形如 `*** < ∞` 或等效的 `*** ≠ ∞` 目标的策略。

## finiteness?
定义于：`finiteness?`

解决扩展非负实数（`ℝ≥0∞`）中形如 `*** < ∞` 或等效的 `*** ≠ ∞` 目标的策略。

## finiteness_nonterminal
定义于：`finiteness_nonterminal`

解决扩展非负实数（`ℝ≥0∞`）中形如 `*** < ∞` 或等效的 `*** ≠ ∞` 目标的策略。

## first
定义于：`Lean.Parser.Tactic.first`

`first | tac | ...` 依次运行每个 `tac` 直到其中一个成功，否则失败。

## focus
定义于：`Lean.Parser.Tactic.focus`

`focus tac` 聚焦于主目标，抑制所有其他目标，并对其运行 `tac`。通常更推荐使用 `· tac`，其强制 `tac` 闭合目标。

## forward
定义于：`Aesop.Frontend.tacticForward___`


## forward?
定义于：`Aesop.Frontend.tacticForward?___`

## frac_tac
定义于：`RatFunc.tacticFrac_tac`

通过操作 `FractionRing K[X]` 来求解 `RatFunc K` 的方程。

## fun_cases
定义于：`Lean.Parser.Tactic.funCases`

`fun_cases` 策略是使用函数式案例分析原理时 `cases` 策略的便捷包装。

策略调用
```
fun_cases f x ... y ...
```
等价于
```
cases y, ... using f.fun_cases x ...
```
其中 `f` 的参数被用作 `f.fun_cases` 的参数或案例分析的目标，视情况而定。

形式
```
fun_cases f
```
（无参数传递给 `f`）会在目标中寻找 `f` 的唯一的合格应用，并使用这些参数。当应用是饱和的且将成为目标的参数是自由变量时，该应用是合格的。

形式 `fun_cases f x y with | case1 => tac₁ | case2 x' ih => tac₂` 的工作方式与 `cases` 相同。

## fun_induction
定义于：`Lean.Parser.Tactic.funInduction`

`fun_induction` 策略是使用函数式归纳原理时 `induction` 策略的便捷包装。

策略调用
```
fun_induction f x₁ ... xₙ y₁ ... yₘ
```
其中 `f` 是通过非互结构或良基递归定义的函数，等价于
```
induction y₁, ... yₘ using f.induct x₁ ... xₙ
```
其中 `f` 的参数被用作 `f.induct` 的参数或归纳的目标，视情况而定。

形式
```
fun_induction f
```
（无参数传递给 `f`）会在目标中寻找 `f` 的唯一的合格应用，并使用这些参数。当应用是饱和的且将成为目标的参数是自由变量时，该应用是合格的。

形式 `fun_induction f x y generalizing z₁ ... zₙ` 和 `fun_induction f x y with | case1 => tac₁ | case2 x' ih => tac₂` 的工作方式与 `induction` 相同。

## fun_prop
定义于：`Mathlib.Meta.FunProp.funPropTacStx`

用于证明函数属性的策略

## funext
定义于：`tacticFunext___`

应用函数外延性并引入新假设。
策略 `funext` 将持续应用 `funext` 引理，直到目标不再可简化为
```
  |-  ((fun x => ...) = (fun x => ...))
```
变体 `funext h₁ ... hₙ` 应用 `funext` `n` 次，并使用给定的标识符命名新假设。
可以像在 `intro` 策略中一样使用模式。例如，给定目标
```
  |-  ((fun x : Nat × Bool => ...) = (fun x => ...))
```
`funext (a, b)` 应用一次 `funext` 并对新引入的对进行模式匹配。

## gcongr
定义于：`Mathlib.Tactic.GCongr.tacticGcongr__With__`

`gcongr` 策略应用“广义同余”规则，将匹配同一模式的 LHS 和 RHS 之间的关系目标简化为不同输入之间的子关系目标。例如，
```lean
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · linarith
```
该示例的目标是证明模式
```
x ^ 2 * ?_ + ?_
```
的 LHS 和 RHS 之间的 `≤` 关系（左侧输入为 `a` 和 `c`，右侧为 `b` 和 `d`）；使用 `gcongr` 后，我们得到更简单的目标 `a ≤ b` 和 `c ≤ d`。

可以显式提供模式；这在需要非最大匹配时很有用：
```lean
example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  linarith
```

所使用的“广义同余”规则是带有 `@[gcongr]` 属性的库引理。例如，第一个示例使用广义同余引理 `add_le_add` 和 `mul_le_mul_of_nonneg_left` 构建证明项
```
add_le_add (mul_le_mul_of_nonneg_left _ (pow_bit0_nonneg x 1)) _
```

策略尝试使用 `gcongr_discharger` 策略（封装了 `positivity` 但也可扩展）来消除这些“广义同余”引理的次要目标（如上述 `mul_le_mul_of_nonneg_left` 应用中的次要目标 `0 ≤ x ^ 2`）。无法以此方式消除的次要目标将留给用户处理。

## gcongr?
定义于：`tacticGcongr?`

显示一个部件面板，允许通过选择目标中的子表达式生成带有孔的 `gcongr` 调用。

## gcongr_discharger
定义于：`Mathlib.Tactic.GCongr.tacticGcongr_discharger`


## generalize
定义于：`Lean.Parser.Tactic.generalize`

* `generalize ([h :] e = x),+` 用新假设 `x` 替换主目标中所有 `e` 的出现。如果给出 `h`，则引入 `h : e = x`。
* `generalize e = x at h₁ ... hₙ` 也泛化 `h₁`, ..., `hₙ` 中的 `e` 出现。
* `generalize e = x at *` 将泛化所有位置的 `e` 出现。

## generalize'
定义于：`«tacticGeneralize'_:_=_»`

`generalize` 的向后兼容垫片。

## generalize_proofs
定义于：`Mathlib.Tactic.generalizeProofsElab`

`generalize_proofs ids* [at locs]?` 泛化当前目标中的证明，将其转换为新的局部假设。

- `generalize_proofs` 泛化目标中的证明。
- `generalize_proofs at h₁ h₂` 泛化假设 `h₁` 和 `h₂` 中的证明。
- `generalize_proofs at *` 泛化整个局部上下文中的证明。
- `generalize_proofs pf₁ pf₂ pf₃` 使用名称 `pf₁`、`pf₂` 和 `pf₃` 命名泛化的证明。可以使用 `_` 来不命名证明。

如果证明已存在于局部上下文中，则使用该证明而不是创建新的局部假设。

当执行 `generalize_proofs at h` 时，如果 `h` 是一个 let 绑定，则其值被清除，且如果 `h` 重复了前面的局部假设，则被消除。

该策略能够从绑定器下抽象证明，在局部上下文中创建全称量化的证明。要禁用此功能，使用 `generalize_proofs (config := { abstract := false })`。该策略还设置为从泛化证明的类型中递归抽象证明。可以通过 `maxDepth` 配置选项控制，`generalize_proofs (config := { maxDepth := 0 })` 关闭此功能。

例如：
```lean
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```

## get_elem_tactic
定义于：`tacticGet_elem_tactic`

`get_elem_tactic` 是符号 `arr[i]` 自动调用的策略，用于证明构造项时出现的任何次要条件（例如索引在数组边界内）。它只是委托给 `get_elem_tactic_trivial` 并在其他情况下给出诊断错误消息；鼓励用户扩展 `get_elem_tactic_trivial` 而不是此策略。

## get_elem_tactic_trivial
定义于：`tacticGet_elem_tactic_trivial`

`get_elem_tactic_trivial` 是一个可扩展的策略，由符号 `arr[i]` 自动调用，用于证明构造项时出现的任何次要条件（例如索引在数组边界内）。默认行为是尝试 `trivial`（处理上下文中存在 `i < arr.size` 的情况）、`simp +arith` 和 `omega`（用于进行索引的线性算术）。

## ghost_calc
定义于：`WittVector.Tactic.ghostCalc`

`ghost_calc` 是用于证明多项式函数间恒等式的策略。通常，当面对像
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
这样的目标时，你可以：
1. 调用 `ghost_calc`
2. 进行少量手动工作——可能无需操作，可能需要 `rintro` 等
3. 调用 `ghost_simp`

这将关闭目标。

`ghost_calc` 无法检测你处理的是单变量还是多变量多项式函数。你必须提供参数来确定这一点。如果要证明像上面这样的全称量化目标，调用 `ghost_calc _ _`。如果变量已引入，调用 `ghost_calc x y`。在单变量情况下，使用 `ghost_calc _` 或 `ghost_calc x`。

`ghost_calc` 是围绕类型类推断的轻量包装。它所做的只是应用适当的外延性引理并尝试推断结果目标。由于涉及高阶统一，Lean 的 elaborator 不喜欢这种操作，因此在策略脚本中使用它更容易（且更美观）。

## ghost_fun_tac
定义于：`WittVector.«tacticGhost_fun_tac_,_»`

用于证明`ghostFun`保持环运算的辅助策略。

## ghost_simp
定义于：`WittVector.Tactic.ghostSimp`

在通过幽灵分量方程进行重写时常用的简化宏。

## grind
定义于：`Lean.Parser.Tactic.grind`


## grind?
定义于：`Lean.Parser.Tactic.grindTrace`


## group
定义于：`Mathlib.Tactic.Group.group`

用于在乘法群中规范化表达式的策略，不假设交换性，仅使用群公理而不涉及具体群的信息。

（对于加法交换群，请使用`abel`策略。）

示例：
```lean
example {G : Type} [Group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a := by
  group at h -- 规范化`h`，使其变为`h : c = d`
  rw [h]     -- 目标现在为`a*d*d⁻¹ = a`
  group      -- 再次规范化并闭合目标
```

## guard_expr
定义于：`Lean.Parser.Tactic.guardExpr`

检查两个表达式是否相等的策略。
* `guard_expr e = e'` 检查`e`和`e'`在可约透明度下是否定义等价。
* `guard_expr e =~ e'` 检查`e`和`e'`在默认透明度下是否定义等价。
* `guard_expr e =ₛ e'` 检查`e`和`e'`是否句法等价。
* `guard_expr e =ₐ e'` 检查`e`和`e'`是否α等价。

在检查相等性前，`e`和`e'`会被实例化其元变量。它们的类型会在处理合成元变量前通过`isDefEqGuarded`进行统一，以处理默认实例。

## guard_goal_nums
定义于：`guardGoalNums`

`guard_goal_nums n` 在当前目标数为`n`时成功，否则失败。

## guard_hyp
定义于：`Lean.Parser.Tactic.guardHyp`

检查指定假设是否具有给定类型和/或值的策略。

* `guard_hyp h : t` 检查类型是否在可约定义等价下匹配。
* `guard_hyp h :~ t` 检查类型是否在默认定义等价下匹配。
* `guard_hyp h :ₛ t` 检查类型是否句法等价。
* `guard_hyp h :ₐ t` 检查类型是否α等价。
* `guard_hyp h := v` 检查值是否在可约定义等价下匹配。
* `guard_hyp h :=~ v` 检查值是否在默认定义等价下匹配。
* `guard_hyp h :=ₛ v` 检查值是否句法等价。
* `guard_hyp h :=ₐ v` 检查值是否α等价。

值`v`会以假设`h`的类型作为预期类型进行推导。

## guard_hyp_nums
定义于：`guardHypNums`

`guard_hyp_nums n` 在当前假设数为`n`时成功，否则失败。

注意：根据设置选项的不同，某些假设可能不会显示在目标视图中。此策略计算总假设数，而非可见假设数。

## guard_target
定义于：`Lean.Parser.Tactic.guardTarget`

检查目标是否与给定表达式一致的策略。
* `guard_target = e` 检查目标在可约透明度下是否与`e`定义等价。
* `guard_target =~ e` 检查目标在默认透明度下是否与`e`定义等价。
* `guard_target =ₛ e` 检查目标是否与`e`句法等价。
* `guard_target =ₐ e` 检查目标是否与`e`α等价。

`e`会以目标的类型作为预期类型进行推导，这在`conv`模式中尤为有用。

## have
定义于：`Lean.Parser.Tactic.tacticHave_`

`have`策略用于向主目标的本地上下文中添加假设。
* `have h : t := e` 若`e`是类型`t`的项，则添加假设`h : t`。
* `have h := e` 使用`e`的类型作为`t`。
* `have : t := e` 和 `have := e` 使用`this`作为假设名称。
* `have pat := e` 对于模式`pat`等同于`match e with | pat => _`，
  其中`_`代表后续策略。适用于仅有一个适用构造器的类型。
  例如，给定`h : p ∧ q ∧ r`，`have ⟨h₁, h₂, h₃⟩ := h` 生成假设`h₁ : p`、`h₂ : q`和`h₃ : r`。

## have
定义于：`Mathlib.Tactic.tacticHave_`


## have!?
定义于：`Mathlib.Tactic.Propose.«tacticHave!?:_Using__»`

* `have? using a, b, c` 尝试查找使用本地假设`a, b, c`的引理，
  并通过追踪消息报告结果。
* `have? : h using a, b, c` 仅返回类型匹配`h`（可含`_`）的引理。
* `have?! using a, b, c` 还会调用`have`将结果添加至本地目标状态。

注意：`have?`（与`apply?`不同）不会检查目标，仅检查`using`子句中引理的类型。

`have?`不应留在最终证明中；它是类似于`apply?`的搜索工具。

建议以`have := f a b c`形式打印。

## have'
定义于：`Lean.Parser.Tactic.tacticHave'_`

类似于`have`，但使用`refine'`

## have'
定义于：`Lean.Parser.Tactic.«tacticHave'_:=_»`

类似于`have`，但使用`refine'`

## have?
定义于：`Mathlib.Tactic.Propose.propose'`

* `have? using a, b, c` 尝试查找使用本地假设`a, b, c`的引理，
  并通过追踪消息报告结果。
* `have? : h using a, b, c` 仅返回类型匹配`h`（可含`_`）的引理。
* `have?! using a, b, c` 还会调用`have`将结果添加至本地目标状态。

注意：`have?`（与`apply?`不同）不会检查目标，仅检查`using`子句中引理的类型。

`have?`不应留在最终证明中；它是类似于`apply?`的搜索工具。

建议以`have := f a b c`形式打印。

## have?!
定义于：`Mathlib.Tactic.Propose.«tacticHave?!:_Using__»`

* `have? using a, b, c` 尝试查找使用本地假设`a, b, c`的引理，
  并通过追踪消息报告结果。
* `have? : h using a, b, c` 仅返回类型匹配`h`（可含`_`）的引理。
* `have?! using a, b, c` 还会调用`have`将结果添加至本地目标状态。

注意：`have?`（与`apply?`不同）不会检查目标，仅检查`using`子句中引理的类型。

`have?`不应留在最终证明中；它是类似于`apply?`的搜索工具。

建议以`have := f a b c`形式打印。

## haveI
定义于：`Lean.Parser.Tactic.tacticHaveI_`

`haveI`行为类似`have`，但会内联值而非生成`let_fun`项。

## hint
定义于：`Mathlib.Tactic.Hint.hintStx`

`hint`策略尝试所有通过`register_hint tac`注册的策略，并报告所有成功执行的策略。

## induction
定义于：`Lean.Parser.Tactic.induction`

假设本地上下文中变量`x`具有归纳类型，`induction x`对主目标应用归纳法，为归纳类型的每个构造器生成一个子目标，其中目标被替换为该构造器的一般实例，并为每个递归参数添加归纳假设。若本地上下文中的某个元素类型依赖于`x`，该元素会被临时移除并在之后重新引入，以确保归纳假设包含该元素。

例如，给定`n : Nat`及目标假设`h : P n`和目标`Q n`，`induction n`生成一个假设`h : P 0`和目标`Q 0`的子目标，以及一个假设`h : P (Nat.succ a)`和归纳假设`ih₁ : P a → Q a`，目标为`Q (Nat.succ a)`。此处`a`和`ih₁`自动命名且不可访问。可通过`with`为每个构造器指定变量名。
- `induction e`（`e`为表达式而非变量）在目标中泛化`e`后对结果变量应用归纳。
- `induction e using r`允许用户指定应使用的归纳原则。`r`的类型需为`C t`形式，
  其中`C`为绑定变量，`t`为（可能为空的）绑定变量序列。
- `induction e generalizing z₁ ... zₙ`在应用归纳前泛化本地上下文中的变量`z₁ ... zₙ`，
  之后在每个子目标中重新引入。净效应为每个归纳假设被泛化。
- 给定`x : Nat`，`induction x with | zero => tac₁ | succ x' ih => tac₂`
  对`zero`情况使用策略`tac₁`，对`succ`情况使用`tac₂`。
  
## induction'
定义于：`Mathlib.Tactic.induction'`

`induction'` 策略与 Lean 4 核心中的 `induction` 策略类似，但语法略有不同（例如，无需为构造函数命名）。

```lean
open Nat

example (n : ℕ) : 0 < factorial n := by
  induction' n with n ih
  · rw [factorial_zero]
    simp
  · rw [factorial_succ]
    apply mul_pos (succ_pos n) ih

example (n : ℕ) : 0 < factorial n := by
  induction n
  case zero =>
    rw [factorial_zero]
    simp
  case succ n ih =>
    rw [factorial_succ]
    apply mul_pos (succ_pos n) ih
```

## infer_instance
定义于：`Lean.Parser.Tactic.tacticInfer_instance`

`infer_instance` 是 `exact inferInstance` 的缩写。它通过类型类推断合成目标类型的值。

## infer_param
定义于：`Mathlib.Tactic.inferOptParam`

通过使用 `a` 来关闭形如 `optParam α a` 或 `autoParam α stx` 的目标。

## inhabit
定义于：`Lean.Elab.Tactic.inhabit`

`inhabit α` 尝试推导 `Nonempty α` 实例，然后利用该实例创建 `Inhabited α` 实例。若目标是 `Prop`，则以构造性方式完成；否则使用 `Classical.choice`。

## init_ring
定义于：`WittVector.initRing`

`init_ring` 是一个辅助策略，用于通过环运算分解 `init` 的目标。

## injection（单射分解）
定义于：`Lean.Parser.Tactic.injection`

`injection` 策略基于归纳数据类型构造函数的单射性。即若 `c` 是归纳数据类型的构造函数，且 `(c t₁)` 与 `(c t₂)` 相等，则 `t₁` 与 `t₂` 也相等。若 `q` 是证明 `t₁ = t₂` 的命题，则 `injection` 应用单射性推导所有位于相同位置的参数的相等性。例如，从 `(a::b) = (c::d)` 可推导出 `a=c` 和 `b=d`。使用此策略时，`t₁` 和 `t₂` 应为同一构造函数的应用。给定 `h : a::b = c::d`，策略 `injection h` 会在主目标中添加两个新假设，类型分别为 `a = c` 和 `b = d`。策略 `injection h with h₁ h₂` 使用 `h₁` 和 `h₂` 命名新假设。

## injections
定义于：`Lean.Parser.Tactic.injections`

`injections` 递归地对所有假设应用 `injection`（因 `injection` 可能生成新假设）。适用于解构嵌套的构造函数等式，如 `(a::b::c) = (d::e::f)`。

## interval_cases
定义于：`Mathlib.Tactic.intervalCases`

`interval_cases n` 搜索变量 `n` 的上下限，若找到边界，则分割为 `n` 的每个可能值的独立案例。

例如：
```lean
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  all_goals simp
```
执行 `interval_cases n` 后，目标变为 `3 = 3 ∨ 3 = 4` 和 `4 = 3 ∨ 4 = 4`。

也可显式指定上下限，如 `interval_cases using hl, hu`。假设应形如 `hl : a ≤ n` 和 `hu : n < b`，此时 `interval_cases` 会对结果 `n ∈ Set.Ico a b` 调用 `fin_cases`。

可指定新假设的名称 `h`，如 `interval_cases h : n` 或 `interval_cases h : n using hl, hu`。

## intro
定义于：`Batteries.Tactic.introDot`

语法 `intro.` 已弃用，建议使用 `nofun`。

## intro
定义于：`Lean.Parser.Tactic.intro`

引入一个或多个假设，可选命名或模式匹配。对于每个待引入的假设，剩余主目标的目标类型必须是 `let` 或函数类型。

* 单独使用 `intro` 会引入一个匿名假设，可通过如 `assumption` 访问。
* `intro x y` 引入两个假设并命名。单个假设可通过 `_` 匿名，
  或进行模式匹配：
  ```lean
  -- ... ⊢ α × β → ...
  intro (a, b)
  -- ..., a : α, b : β ⊢ ...
  ```
* 此外，`intro` 可结合模式匹配，类似 `fun`：
  ```lean
  intro
  | n + 1, 0 => tac
  | ...
  ```

## intro
定义于：`Lean.Parser.Tactic.introMatch`

策略
```
intro
| pat1 => tac1
| pat2 => tac2
```
等同于：
```lean
intro x
match x with
| pat1 => tac1
| pat2 => tac2
```
即 `intro` 后可跟匹配分支，在引入值时进行模式匹配。这与项模式中的 `fun` 带匹配分支类似。

## intros
定义于：`Lean.Parser.Tactic.intros`

引入零或多个假设，可选命名。

- `intros` 等效于重复应用 `intro`，直至目标不再是 `intro` 的明显候选，即只要目标是 `let` 或 Pi 类型（如蕴含、函数或全称量词），`intros` 会引入匿名假设。此策略不展开定义。

- `intros x y ...` 等效于 `intro x y ...`，为每个提供的参数引入假设，并按需展开定义。
  参数可为标识符或 `_`。标识符表示对应引入假设的名称，`_` 表示匿名引入假设。

示例：

基础属性：
```lean
def AllEven (f : Nat → Nat) := ∀ n, f n % 2 = 0

-- 自动引入两个明显假设
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros
  /- 策略状态
     f✝ : Nat → Nat
     a✝ : AllEven f✝
     ⊢ AllEven fun k => f✝ (k + 1) -/
  sorry

-- 精确引入两个假设，仅命名第一个
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros g _
  /- 策略状态
     g : Nat → Nat
     a✝ : AllEven g
     ⊢ AllEven fun k => g (k + 1) -/
  sorry

-- 精确引入三个假设，需展开 `AllEven`
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros f h n
  /- 策略状态
     f : Nat → Nat
     h : AllEven f
     n : Nat
     ⊢ (fun k => f (k + 1)) n % 2 = 0 -/
  apply h
```

蕴含：
```lean
example (p q : Prop) : p → q → p := by
  intros
  /- 策略状态
     a✝¹ : p
     a✝ : q
     ⊢ p      -/
  assumption
```

Let 绑定：
```lean
example : let n := 1; let k := 2; n + k = 3 := by
  intros
  /- n✝ : Nat := 1
     k✝ : Nat := 2
     ⊢ n✝ + k✝ = 3 -/
  rfl
```

## introv
定义于：`Mathlib.Tactic.introv`

策略 `introv` 允许用户自动引入定理的变量，并显式命名非依赖假设。依赖假设使用默认名称。

示例：
```lean
example : ∀ a b : Nat, a = b → b = a := by
  introv h,
  exact h.symm
```
执行 `introv h` 后的状态为：
```
a b : ℕ,
h : a = b
⊢ b = a
```

```
example : ∀ a b : Nat, a = b → ∀ c, b = c → a = c := by
  introv h₁ h₂,
  exact h₁.trans h₂
```
执行 `introv h₁ h₂` 后的状态为：
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```

## isBoundedDefault
定义于：`Filter.tacticIsBoundedDefault`

在完全格中，滤波器自动有界或共界。为了在完全格和条件完全格中使用相同语句，但让自动化在完全格中自动填充有界性证明，我们在语句中使用策略 `isBoundedDefault`，形式为 `(hf : f.IsBounded (≥) := by isBoundedDefault)`。

## itauto
定义于：`Mathlib.Tactic.ITauto.itauto`

直觉主义命题逻辑的决策过程。与 `finish` 和 `tauto!` 不同，此策略不使用排中律（不带 `!` 选项时），且证明搜索针对此用例优化。（`itauto!` 可作为经典 SAT 求解器，但算法在此情况下效果不佳。）

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]` 会额外尝试对 `a` 和 `b` 进行案例分析，前提是能推导出 `Decidable a` 和 `Decidable b`。`itauto *` 会对所有可判定的命题原子进行案例分析，`itauto! *` 会对所有命题原子进行案例分析。
*警告：* 可能导致证明搜索爆炸，需谨慎使用。

## itauto!
定义于：`Mathlib.Tactic.ITauto.itauto!`

针对直觉主义命题逻辑的决策过程。与`finish`和`tauto!`不同，此策略在无`!`选项时绝不使用排中律，且其证明搜索专为此用例优化。（`itauto!`可作为经典SAT求解器使用，但在此情境下算法效率不高。）

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]`将额外尝试对`a`和`b`进行案例分析，前提是能推导出`Decidable a`和`Decidable b`。`itauto *`将对所有可判定的原子命题进行案例分析，而`itauto! *`则对所有命题原子进行分析。
*警告：*此操作可能导致证明搜索爆炸，故应谨慎使用。

## iterate
定义于：`Lean.Parser.Tactic.tacticIterate____`

`iterate n tac`精确运行`tac`策略`n`次。`iterate tac`反复运行`tac`直至失败。

`iterate`的参数为策略序列，因此可通过`iterate n (tac₁; tac₂; ⋯)`或以下方式运行多个策略：
```lean
iterate n
  tac₁
  tac₂
  ⋯
```

## left
定义于：`Lean.Parser.Tactic.left`

当目标为恰好两个构造函数的归纳类型时，应用第一个构造函数，否则失败。
```lean
example : True ∨ False := by
  left
  trivial
```

## let
定义于：`Lean.Parser.Tactic.letrec`

`let rec f : t := e`向当前目标添加递归定义`f`。语法与项模式下的`let rec`相同。

## let
定义于：`Mathlib.Tactic.tacticLet_`

## let
定义于：`Lean.Parser.Tactic.tacticLet_`

`let`策略用于向主目标的局部上下文中添加定义。
* `let x : t := e`若`e`为类型`t`的项，则添加定义`x : t := e`。
* `let x := e`使用`e`的类型作为`t`。
* `let : t := e`和`let := e`使用`this`作为假设名称。
* 对模式`pat`的`let pat := e`等价于`match e with | pat => _`，其中`_`代表后续策略。此语法适用于仅有一个适用构造函数的情况。例如，给定`p : α × β × γ`，`let ⟨x, y, z⟩ := p`将生成局部变量`x : α`、`y : β`和`z : γ`。

## let'
定义于：`Lean.Parser.Tactic.tacticLet'_`

类似`let`，但使用`refine'`

## letI
定义于：`Lean.Parser.Tactic.tacticLetI_`

`letI`行为类似`let`，但内联值而非生成`let_fun`项。

## lift
定义于：`Mathlib.Tactic.lift`

将表达式提升至另一类型。
* 用法：`'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`。
* 若`n : ℤ`且`hn : n ≥ 0`，则策略`lift n to ℕ using hn`将创建名为`n`的`ℕ`类型新常量，并将旧变量`(n : ℤ)`的所有出现替换为`↑n`（新变量`n`）。同时从上下文中移除`n`和`hn`。
  + 例如，策略`lift n to ℕ using hn`将目标`n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3`转换为`n : ℕ, h : P ↑n ⊢ ↑n = 3`（此处`P`为`ℤ → Prop`类型项）。
* 参数`using hn`可选，策略`lift n to ℕ`效果相同，但会新增子目标`n ≥ 0`（`n`为旧变量）。此子目标将置于目标列表顶端。
  + 例如，策略`lift n to ℕ`将目标`n : ℤ, h : P n ⊢ n = 3`转换为两个目标：`n : ℤ, h : P n ⊢ n ≥ 0`和`n : ℕ, h : P ↑n ⊢ ↑n = 3`。
* 也可使用`lift n to ℕ using e`，其中`e`为`n ≥ 0`类型的任意表达式。
* 使用`lift n to ℕ with k`指定新变量名称。
* 使用`lift n to ℕ with k hk`同时指定等式`↑k = n`的名称。此时`n`仍保留于上下文中。可使用`rfl`作为`hk`名称以消除`n`（即默认行为）。
* 也可对`e : ℤ`类型的任意表达式使用`lift e to ℕ with k hk`。此时`hk`始终保留于上下文中，但用于重写所有假设及目标中的`e`。
  + 例如，策略`lift n + 3 to ℕ using hn with k hk`将目标`n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n`转换为`n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`。
* 策略`lift n to ℕ using h`将从上下文中移除`h`。若需保留，可在`with`的第三个参数中再次指定，如`lift n to ℕ using h with n rfl h`。
* 更一般地，此策略可将表达式从`α`提升至`β`，前提是存在`CanLift α β`实例。此时证明义务由`CanLift.prf`指定。
* 给定实例`CanLift β γ`，亦可提升`α → β`至`α → γ`；更一般地，给定`β : Π a : α, Type*`、`γ : Π a : α, Type*`及`[Π a : α, CanLift (β a) (γ a)]`，自动生成实例`CanLift (Π a, β a) (Π a, γ a)`。

`lift`在某种意义上与`zify`策略互为补充。`lift (z : ℤ) to ℕ`将在超类型`ℤ`中整数`z`提升至子类型`ℕ`，前提是证明`z ≥ 0`；涉及`z`的命题仍位于`ℤ`。`zify`则将子类型`ℕ`的命题转换为超类型`ℤ`的命题，且不改变任何变量类型。

## lift_lets
定义于：`Mathlib.Tactic.lift_lets`

将表达式类型中的所有`let`绑定尽可能外提。

应用于主目标时，此策略允许`intro`内嵌的`let`表达式。例如：
```lean
example : (let x := 1; x) = 1 := by
  lift_lets
  -- ⊢ let x := 1; x = 1
  intro x
  sorry
```

在提升过程中，类型和值相同的`let`绑定将被合并。

## liftable_prefixes
定义于：`Mathlib.Tactic.Coherence.liftable_prefixes`

`coherence`内部使用的策略。

将等式`f = g`重写为`f₀ ≫ f₁ = g₀ ≫ g₁`，其中`f₀`和`g₀`为`f`和`g`（可能经重新结合后的）的最大可提升前缀（即能表示为单一化子和结合子的组合）。

## linarith
定义于：`linarith`

`linarith`尝试在线性（不）等式假设间寻找矛盾。等价地，通过假设其否定并证明`False`，可证明线性不等式。

理论上，`linarith`应能证明所有在线性算术有理数理论中成立的目标。尽管对`Nat`和`Int`等非密集序有特殊处理，此策略对这类理论并不完备，无法证明所有真命题。它将解决任意实例化`LinearOrderedCommRing`类型的目标。

示例：
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith
```

`linarith`将使用所有适用假设及目标的否定（若适用）。不等性假设需分情况讨论，通常不予考虑（参见`splitNe`选项）。

`linarith [t1, t2, t3]`将额外使用证明项`t1, t2, t3`。

`linarith only [h1, h2, h3, t1, t2, t3]`仅使用目标（若相关）、局部假设`h1, h2, h3`及证明`t1, t2, t3`，忽略其余上下文。

`linarith!`将使用更强的可约简性设置以识别原子。例如：
```lean
example (x : ℚ) : id x ≥ x := by
  linarith
```
将失败，因`linarith`无法识别`x`与`id x`。`linarith!`则能成功。此操作有时较为耗时。

`linarith (config := { .. })`接受包含五个可选参数的配置对象：
* `discharger`指定用于在证明阶段简化代数方程的策略，默认为`ring`。其他选项包括基础问题的`simp`。
* `transparency`控制`linarith`尝试匹配原子的力度，默认仅展开`reducible`定义。
* 若`splitHypotheses`为`true`，`linarith`将拆分上下文中的合取为独立假设。
* 若`splitNe`为`true`，`linarith`将对不等性假设进行情况拆分。对每个`x ≠ y`假设，分别以`x < y`和`x > y`运行`linarith`，导致随不等性假设数量指数级增长的运行次数（默认`false`）。
* 若`exfalso`为`false`，当目标非不等式或`False`时，`linarith`将失败（默认`true`）。
* `restrict_type`（尚未在mathlib4中实现）仅使用`tp`上的不等式假设，适用于局部上下文中同时存在整数和有理数不等式的情况，避免混淆。

## linarith!
定义于：`tacticLinarith!_`

`linarith` 尝试在线性（不）等式假设中寻找矛盾。等价地，它可以通过假设目标的否定并证明 `False` 来证明一个线性不等式。

理论上，`linarith` 应能证明任何在有理数线性算术理论中成立的命题。尽管对于非稠密序如 `Nat` 和 `Int` 有特殊处理，此策略对这些理论并不完备，无法证明所有真命题。它能够解决实例化了 `LinearOrderedCommRing`（线性有序交换环）的任意类型上的目标。

示例：
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith
```

`linarith` 将使用所有适用的假设及目标的否定（若适用）。不等式假设需要进行情况拆分，通常不被考虑（参见下方的 `splitNe` 选项）。

`linarith [t1, t2, t3]` 将额外使用证明项 `t1, t2, t3`。

`linarith only [h1, h2, h3, t1, t2, t3]` 将仅使用目标（若相关）、局部假设 `h1`、`h2`、`h3` 及证明 `t1`、`t2`、`t3`，忽略其余局部上下文。

`linarith!` 将使用更强的可约简性设置以尝试识别原子。例如：
```lean
example (x : ℚ) : id x ≥ x := by
  linarith
```
将失败，因为 `linarith` 无法识别 `x` 与 `id x`。而 `linarith!` 可以。此操作有时可能较为耗时。

`linarith (config := { .. })` 接受一个配置对象，包含五个可选参数：
* `discharger` 指定用于在证明阶段化简代数方程的策略，默认为 `ring`。其他选项包括处理基础问题的 `simp`。
* `transparency` 控制 `linarith` 尝试匹配原子的努力程度，默认仅展开 `reducible` 定义。
* 若 `splitHypotheses` 为真，`linarith` 将上下文中的合取式拆分为独立假设。
* 若 `splitNe` 为 `true`，`linarith` 将对不等式假设进行情况拆分。对于给定的 `x ≠ y` 假设，`linarith` 将分别在 `x < y` 和 `x > y` 下运行，这会随不等式假设数量呈指数级增加运行次数（默认为 `false`）。
* 若 `exfalso` 为 `false`，当目标既非不等式也非 `False` 时，`linarith` 将失败（默认为 `true`）。
* `restrict_type`（mathlib4 中尚未实现）将仅使用类型为 `tp` 的不等式假设。这在局部上下文中同时存在整型与有理型不等式时尤为有用，避免混淆策略。

其变体 `nlinarith` 通过基础预处理处理部分非线性目标。

选项 `set_option trace.linarith true` 将追踪 `linarith` 例程的特定中间阶段。

## linear_combination
定义于：`Mathlib.Tactic.LinearCombination.linearCombination`

`linear_combination` 策略尝试通过将目标展示为指定的（不）等式假设或其它（不）等式证明项的线性组合来证明（不）等式目标，模（A）项在（不）等式左右侧的移动，及（B）默认使用环归一化的归一化策略。

示例用法：
```lean
example {a b : ℚ} (h1 : a = 1) (h2 : b = 3) : (a + b) / 2 = 2 := by
  linear_combination (h1 + h2) / 2

example {a b : ℚ} (h1 : a ≤ 1) (h2 : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination (h1 + h2) / 2

example {a b : ℚ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  linear_combination sq_nonneg (a - b)

example {x y z w : ℤ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) :
    z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

example {x : ℚ} (h : x ≥ 5) : x ^ 2 > 2 * x + 11 := by
  linear_combination (x + 3) * h

example {R : Type*} [CommRing R] {a b : R} (h : a = b) : a ^ 2 = b ^ 2 := by
  linear_combination (a + b) * h

example {A : Type*} [AddCommGroup A]
    {x y z : A} (h1 : x + y = 10 • z) (h2 : x - y = 6 • z) :
    2 • x = 2 • (8 • z) := by
  linear_combination (norm := abel) h1 + h2

example (x y : ℤ) (h1 : x * y + 2 * x = 1) (h2 : x = y) :
    x * y = -2 * y + 1 := by
  linear_combination (norm := ring_nf) -2 * h2
  -- 留下目标 `⊢ x * y + x * 2 - 1 = 0`
```

输入 `e` 于 `linear_combination e` 中是（不）等式证明的线性组合，表现为系数乘以表达式的和/差。系数可为任意表达式（不等式时需非负）。表达式可为任意证明（不）等式的证明项，通常为假设名 `h1`、`h2` 等。

所有（不）等式的左右侧应具相同类型 `α`，系数亦应具类型 `α`。完整功能下，`α` 应为交换环——严格而言，是具有“可消去”加法的交换半环（半环情形下，负与减将形式化处理为在包络环中的操作）。若使用非标准归一化（如 `abel` 或 `skip`），策略可工作于代数结构较弱的类型 `α`：对于等式，最低要求为实例 `[Add α] [IsRightCancelAdd α]` 及策略调用中使用操作的实例。

变体 `linear_combination (norm := tac) e` 显式指定归一化策略 `tac` 在构建线性组合后作用于子目标。
* 默认归一化策略为 `ring1`（等式）或 `Mathlib.Tactic.Ring.prove{LE,LT}`（不等式）。这些为终结策略：成功闭合目标或失败。
* 当工作于交换环外的代数范畴（如域、交换群、模）时，使用适配这些范畴的归一化策略（`field_simp`、`abel`、`module`）有时有效。
* 跳过归一化，使用 `skip` 作为归一化策略。
* `linear_combination` 通过从左至右相加提供的（不）等式构建线性组合，故若 `tac` 对加法表达式交换不变，输入假设的顺序可能影响结果。

变体 `linear_combination (exp := n) e` 将在减去组合 `e` 前将目标提升至 `n` 次方。即，若目标为 `t1 = t2`，`linear_combination (exp := n) e` 将目标变为 `(t1 - t2)^n = 0` 后继续处理。此变体仅实现于等式线性组合（即不适用于不等式）。

## linear_combination'
定义于：`Mathlib.Tactic.LinearCombination'.linearCombination'`

`linear_combination'` 尝试通过创建等式列表的线性组合并将其从目标中减去以简化目标。策略通过从左至右相加等式构建线性组合，故输入假设的顺序会影响结果。若策略的 `norm` 字段设为 `skip`，则策略将直接设置用户以使用线性组合证明目标，而非归约减法。

注：另有类似策略 `linear_combination`（无撇号）；此版本为向后兼容提供。相比此策略，`linear_combination`：
* 舍弃 `←` 语法反转等式，转而使用 `-` 语法提供此操作
* 不支持两假设相乘（`h1 * h2`）、假设相除（`3 / h`）或假设取逆（`h⁻¹`）
* 在用户对假设加减常数（`h + 3`）时产生冗长输出

注：所有等式的左右侧应具相同类型，系数亦然。需有该类型的 `Mul` 和 `AddGroup` 实例。

## linear_combination'

定义于：`Mathlib.Tactic.LinearCombination'.tacticLinear_combination2____`

`linear_combination'` 尝试通过创建一系列等式的线性组合并将其从目标中减去来简化目标。该策略会从左到右将等式相加以形成线性组合，因此输入假设的顺序会影响结果。若将策略的 `norm` 参数设为 `skip`，则该策略将仅设置用户通过线性组合来证明目标，而不会对减法进行归一化处理。

注意：另有一个类似的策略 `linear_combination`（无撇号），此版本为向后兼容而保留。相比本策略，`linear_combination`：
* 移除了使用 `←` 语法反转等式的功能，转而通过 `-` 语法实现此操作
* 不支持两个假设相乘（`h1 * h2`）、除以假设（`3 / h`）或对假设取逆（`h⁻¹`）
* 当用户对假设进行加减常数（如 `h + 3`）时会产生冗余输出

注意：所有等式的左右两侧应具有相同类型，系数也需与此类型一致。必须存在该类型的 `Mul` 和 `AddGroup` 实例。

* `linear_combination' e` 中的输入 `e` 是等式证明的线性组合，表示为系数与表达式相乘后的和/差。系数可为任意表达式，表达式则为证明等式的任意证明项，通常为假设名称 `h1, h2, ...`。
* `linear_combination' (norm := tac) e` 在构建线性组合后，对子目标运行“归一化策略” `tac`。
  * 默认的归一化策略为 `ring1`，其将闭合目标或失败。
  * 若目标无法立即证明，可使用 `ring_nf` 作为归一化策略以获取子目标。
  * 若需完全跳过归一化，可使用 `skip` 作为归一化策略。
* `linear_combination' (exp := n) e` 将在减去组合 `e` 前将目标提升至第 `n` 次幂。即，若目标为 `t1 = t2`，则 `linear_combination' (exp := n) e` 将目标更改为 `(t1 - t2)^n = 0` 后再进行后续处理。此特性不适用于 `linear_combination2`。
* `linear_combination2 e` 与 `linear_combination' e` 类似，但生成两个子目标而非一个：不证明 `(a - b) - (a' - b') = 0`（其中 `a' = b'` 来自 `e` 的线性组合，`a = b` 为目标），而是尝试证明 `a = a'` 和 `b = b'`。由于不使用减法，此形式也适用于半环。
  * 注意，可通过 `linear_combination' e` 证明的目标可能无法通过 `linear_combination2 e` 证明；通常需向 `e` 添加系数以使两侧匹配，如 `linear_combination2 e + c`。
  * 可使用 `← h` 反转等式，例如若 `h₁ : a = b`，则 `2 * (← h)` 为 `2 * b = 2 * a` 的证明。

示例用法：
```lean
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' (norm := ring_nf) -2*h2
  /- 目标：x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination' ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination' x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination' (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination' 3 * h a b + hqc
```

## map_fun_tac

定义于：`WittVector.mapFun.tacticMap_fun_tac`

用于展示 `mapFun` 遵守环运算的辅助策略。

## map_tacs

定义于：`Batteries.Tactic.«tacticMap_tacs[_;]»`

假设存在 `n` 个目标，`map_tacs [t1; t2; ...; tn]` 将各个 `ti` 应用于对应的目标，并保留生成的子目标。

## match

定义于：`Lean.Parser.Tactic.match`

`match` 对一个或多个表达式进行模式匹配分析。参见[归纳与递归][tpil4]。`match` 策略的语法与项模式 `match` 相同，但匹配分支为策略而非表达式。
```lean
example (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | i+1 => simp
```

[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html

## match

定义于：`Batteries.Tactic.«tacticMatch_,,With.»`

语法 `match ⋯ with.` 已弃用，建议改用 `nomatch ⋯`。两者现均支持多个判别式。

## match_scalars

定义于：`Mathlib.Tactic.Module.tacticMatch_scalars`

当目标为类型 `M`（`M` 为 `AddCommMonoid`）中的等式时，将目标的左侧和右侧解析为某半环 `R` 上 `M` 原子的线性组合，并将目标简化为各原子对应的 `R` 系数间的等式。

例如，以下代码生成目标 `⊢ a * 1 + b * 1 = (b + a) * 1`：
```lean
example [AddCommMonoid M] [Semiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (b + a) • x := by
  match_scalars
```

以下代码生成两个目标：来自原子 `x` 的 `⊢ a * (a * 1) + b * (b * 1) = 1` 和来自原子 `y` 的 `⊢ a * -(b * 1) + b * (a * 1) = 0`：
```lean
example [AddCommGroup M] [Ring R] [Module R M] (a b : R) (x : M) :
    a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  match_scalars
```

以下代码生成目标 `⊢ -2 * (a * 1) = a * (-2 * 1)`：
```lean
example [AddCommGroup M] [Ring R] [Module R M] (a : R) (x : M) :
    -(2:R) • a • x = a • (-2:ℤ) • x  := by
  match_scalars
```

`match_scalars` 策略生成的目标的标量类型是遇到的最大标量类型。例如，若 `ℕ`、`ℚ` 和特征零域 `K` 同时作为标量出现，则生成的目标为 `K` 中的等式。策略内部使用 `push_cast` 的变体将其他类型的标量解释为此最大类型。

若遇到的标量类型集合非全序（即对于所有遇到的环 `R` 和 `S`，不存在 `Algebra R S` 或 `Algebra S R`），则 `match_scalars` 策略失败。


## match_target

定义于：`Mathlib.Tactic.tacticMatch_target_`


## measurability

定义于：`tacticMeasurability`

`measurability` 策略用于解决形如 `Measurable f`、`AEMeasurable f`、`StronglyMeasurable f`、`AEStronglyMeasurable f μ` 或 `MeasurableSet s` 的目标，通过应用带有 `measurability` 用户属性的引理。


## measurability!

定义于：`measurability!`

## measurability!?

定义于：`measurability!?`

## measurability?

定义于：`tacticMeasurability?`

`measurability?` 策略用于解决形如 `Measurable f`、`AEMeasurable f`、`StronglyMeasurable f`、`AEStronglyMeasurable f μ` 或 `MeasurableSet s` 的目标，通过应用带有 `measurability` 用户属性的引理，并在成功时建议可替换当前策略调用的更快证明脚本。


## mem_tac

定义于：`AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.tacticMem_tac`

## mem_tac_aux

定义于：`AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.tacticMem_tac_aux`

## mfld_set_tac

定义于：`Tactic.MfldSetTac.mfldSetTac`

一个基础的策略，用于证明流形中出现的集合相等或包含关系。


## mod_cases

定义于：`Mathlib.Tactic.ModCases.«tacticMod_cases_:_%_»`

* 策略 `mod_cases h : e % 3` 将对 `e` 进行情况分析。若 `e : ℤ`，则生成包含假设 `h : e ≡ 0 [ZMOD 3]`、`h : e ≡ 1 [ZMOD 3]`、`h : e ≡ 2 [ZMOD 3]` 的子目标。若 `e : ℕ`，则类似处理，但使用 `[MOD 3]` 替代 `[ZMOD 3]`。
* 通常，当 `n` 为正数且 `e` 为 `ℕ` 或 `ℤ` 类型表达式时，`mod_cases h : e % n` 有效。
* 若省略 `h`，如 `mod_cases e % n`，将默认命名为 `H`。


## module

定义于：`Mathlib.Tactic.Module.tacticModule`

对于目标为 `M` 类型等式（`M` 为加法交换幺半群）的情况，将目标的左侧和右侧解析为交换半环 `R` 上 `M` 原子的线性组合，并通过检查每个原子的左右系数在 `R` 中环归一化后相同来证明目标。

（若系数相等性证明需要比环归一化更复杂的推理，请使用 `match_scalars` 策略，并手动证明系数相等性。）

`module` 策略示例：
```lean
example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (b + a) • x := by
  module

example [AddCommMonoid M] [Field K] [CharZero K] [Module K M] (x : M) :
    (2:K)⁻¹ • x + (3:K)⁻¹ • x + (6:K)⁻¹ • x = x := by
  module

example [AddCommGroup M] [CommRing R] [Module R M] (a : R) (v w : M) :
    (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by
  module

example [AddCommGroup M] [CommRing R] [Module R M] (a b μ ν : R) (x y : M) :
    (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by
  module
```


## monicity

定义于：`Mathlib.Tactic.ComputeDegree.monicityMacro`

`monicity` 尝试解决形如 `Monic f` 的目标。它将目标转换为 `natDegree f ≤ n` 和 `f.coeff n = 1`，并在这些子目标上调用 `compute_degree`。

变体 `monicity!` 类似 `monicity`，但调用 `compute_degree!` 处理子目标。


## monicity!

定义于：`Mathlib.Tactic.ComputeDegree.tacticMonicity!`


## mono

定义于：`Mathlib.Tactic.Monotonicity.mono`

`mono` 重复应用单调性规则和局部假设。例如：
```lean
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  mono
```


## monoidal

定义于：`Mathlib.Tactic.Monoidal.tacticMonoidal`

利用幺半范畴的连贯定理解决幺半范畴中的方程，其中两边仅通过用不同但同源同目标的幺半结构态射（结合子、单位子、恒等态射）替换字符串而不同。

例如，`monoidal` 可处理形如 `a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'` 的目标，其中 `a = a'`、`b = b'` 和 `c = c'` 可通过 `monoidal_coherence` 证明。

## monoidal_coherence

定义于：`Mathlib.Tactic.Monoidal.tacticMonoidal_coherence`

关闭形如 `η = θ` 的目标，其中 `η` 和 `θ` 为由结合子、单位子和恒等态射组成的2-同构。
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence
```

## monoidal_nf

定义于：`Mathlib.Tactic.Monoidal.tacticMonoidal_nf`

将等式的两边规范化。

## monoidal_simps

定义于：`Mathlib.Tactic.Coherence.monoidal_simps`

用于将幺半范畴中的态射重写为范式的简化规则。

## move_add

定义于：`Mathlib.MoveAdd.tacticMove_add_`

`move_add` 策略重新排列表达式中的加数。调用 `move_add [a, ← b, ...]` 将 `a, b,...` 与主目标中的加数匹配，并将 `a` 移至每个加法的最右端，`b` 移至最左端。箭头 `←` 决定移动方向。

输入 `a, b,...` 可为任意项，含占位符。策略使用与每个输入项统一的首个“新”加数。

乘法变体为 `move_mul`。

通用二元结合交换操作策略为 `move_oper`，需提供操作符首符号的项。例如，`move_oper HAdd.hAdd [...]` 等效于 `move_add`，而 `move_oper Max.max [...]` 重新排列 `max`。

## move_mul

定义于：`Mathlib.MoveAdd.tacticMove_mul_`

`move_mul` 策略重新排列表达式中的乘数，操作方式与 `move_add` 类似，但针对乘法项。

存在一个称为 `move_mul` 的乘法变体。

还有一种针对“二元结合交换运算”的通用策略：`move_oper`。在这种情况下，语法要求首先提供一个头符号为该运算的项。例如，`move_oper HAdd.hAdd [...]` 与 `move_add` 相同，而 `move_oper Max.max [...]`则会重新排列 `max`。

## move_oper
定义于：`Mathlib.MoveAdd.moveOperTac`

策略 `move_add` 用于重新排列表达式中的加数。调用 `move_add [a, ← b, ...]` 会将 `a, b, ...` 与主目标中的加数进行匹配。然后将每个加法中出现的 `a` 移动到最右侧，`b` 移动到最左侧。加数移动的方向由箭头 `←` 的存在与否决定。

输入 `a, b, ...` 可以是任何项，也可以包含下划线。该策略使用第一个与每个给定输入项统一的新加数。

存在一个乘法变体，称为 `move_mul`。

还有一种针对“二元结合交换运算”的通用策略：`move_oper`。在这种情况下，语法要求首先提供一个头符号为该运算的项。例如，`move_oper HAdd.hAdd [...]` 与 `move_add` 相同，而 `move_oper Max.max [...]`则会重新排列 `max`。

## mv_bisim
定义于：`Mathlib.Tactic.MvBisim.tacticMv_bisim___With___`

通过双模拟进行证明的策略

## native_decide
定义于：`Lean.Parser.Tactic.nativeDecide`

`native_decide` 是 `decide +native` 的同义词。它将尝试通过合成一个 `Decidable p` 的实例并评估为 `isTrue ..` 来证明类型为 `p` 的目标。与 `decide` 不同，此方法使用 `#eval` 来评估可判定性实例。

由于此方法将整个 Lean 编译器添加到可信部分，并且定理使用此方法或间接依赖它们的定理在 `#print axioms` 中会显示 `Lean.ofReduceBool` 公理，因此需谨慎使用。然而，由于它是编译的，因此在处理非常大的计算时，这可能比使用 `decide` 更高效，这也是信任外部程序运行结果的一种方式。
```lean
example : (List.range 1000).length = 1000 := by native_decide
```

## next
定义于：`Lean.Parser.Tactic.«tacticNext_=>_»`

`next => tac` 聚焦于下一个目标并使用 `tac` 解决它，否则失败。
`next x₁ ... xₙ => tac` 还会将最近 `n` 个具有不可访问名称的假设重命名为给定名称。

## nlinarith
定义于：`nlinarith`

`linarith` 的扩展，通过一些预处理使其能够解决某些非线性算术问题。（基于 Coq 的 `nra` 策略。）有关选项的可用语法，请参见 `linarith`，这些选项由 `nlinarith` 继承；即 `nlinarith!` 和 `nlinarith only [h1, h2]` 均与 `linarith` 中相同。预处理如下：

* 对于假设或目标中的每个子项 `a ^ 2` 或 `a * a`，将假设 `0 ≤ a ^ 2` 或 `0 ≤ a * a` 添加到上下文中。
* 对于上下文中的每对假设 `a1 R1 b1` 和 `a2 R2 b2`，其中 `R1, R2 ∈ {<, ≤, =}`，将假设 `0 R' (b1 - a1) * (b2 - a2)` 添加到上下文中（非递归地），其中 `R ∈ {<, ≤, =}` 是从 `R1, R2` 派生的适当比较。

## nlinarith!
定义于：`tacticNlinarith!_`

`linarith` 的扩展，通过一些预处理使其能够解决某些非线性算术问题。（基于 Coq 的 `nra` 策略。）有关选项的可用语法，请参见 `linarith`，这些选项由 `nlinarith` 继承；即 `nlinarith!` 和 `nlinarith only [h1, h2]` 均与 `linarith` 中相同。预处理如下：

* 对于假设或目标中的每个子项 `a ^ 2` 或 `a * a`，将假设 `0 ≤ a ^ 2` 或 `0 ≤ a * a` 添加到上下文中。
* 对于上下文中的每对假设 `a1 R1 b1` 和 `a2 R2 b2`，其中 `R1, R2 ∈ {<, ≤, =}`，将假设 `0 R' (b1 - a1) * (b2 - a2)` 添加到上下文中（非递归地），其中 `R ∈ {<, ≤, =}` 是从 `R1, R2` 派生的适当比较。

## nofun
定义于：`Lean.Parser.Tactic.tacticNofun_

策略 `nofun` 是 `exact nofun` 的简写：它引入假设，然后执行空模式匹配，如果引入的模式不可能，则关闭目标。

## nomatch
定义于：`Lean.Parser.Tactic.«tacticNomatch_,,»`

策略 `nomatch h` 是 `exact nomatch h` 的简写。

## noncomm_ring
定义于：`Mathlib.Tactic.NoncommRing.noncomm_ring`

用于简化非交换环中等式的策略。

示例：
```lean
example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2 * a * c := by
  noncomm_ring
```

您可以使用 `noncomm_ring [h]` 来同时利用 `h` 进行简化。

## nontriviality
定义于：`Mathlib.Tactic.Nontriviality.nontriviality`

尝试生成 `Nontrivial α` 假设。

该策略首先检查是否已存在 `Nontrivial α` 实例，然后再尝试使用其他技术合成一个。

如果目标是一个（不）等式，则类型 `α` 从目标中推断得出。否则，需要在策略调用中指定类型，如 `nontriviality α`。

`nontriviality` 策略首先查找假设中的严格不等式，并使用这些直接推导 `Nontrivial` 实例。

否则，它将执行 `Subsingleton α ∨ Nontrivial α` 的情况分割，并尝试使用 `simp [h₁, h₂, ..., hₙ, nontriviality]` 解除 `Subsingleton` 目标，其中 `[h₁, h₂, ..., hₙ]` 是可以传递给 `nontriviality` 的附加 `simp` 引理列表，使用语法 `nontriviality α using h₁, h₂, ..., hₙ`。

```lean
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality -- 现在有一个 `Nontrivial R` 假设可用。
  assumption
```

```lean
example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality -- 现在有一个 `Nontrivial R` 假设可用。
  apply mul_comm
```

```lean
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 := by
  nontriviality R -- 现在有一个 `Nontrivial R` 假设可用。
  dec_trivial
```

```lean
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b := by
  success_if_fail nontriviality α -- 失败
  nontriviality α using myeq -- 现在有一个 `Nontrivial α` 假设可用
  assumption
```

## norm_cast
定义于：`Lean.Parser.Tactic.tacticNorm_cast__`

`norm_cast` 系列策略用于规范化表达式中的某些强制转换（*casts*）。
- `norm_cast` 规范化目标中的强制转换。
- `norm_cast at h` 规范化假设 `h` 中的强制转换。

该策略基本上是 `simp` 的一个版本，使用一组特定的引理将强制转换向上移动到表达式中。因此，即使在通常不鼓励使用非终止 `simp` 调用的情况下（由于脆弱性），`norm_cast` 也被认为是安全的。它还对数字有特殊处理。

例如，给定假设
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```
编写 `norm_cast at h` 将 `h` 转换为
```lean
h : a + b < 10
```

还有一些基本策略的变体，它们在操作过程中使用 `norm_cast` 规范化表达式，使其更灵活地接受表达式（我们称其为*模* `norm_cast` 效果的策略）：
- `exact_mod_cast` 对应 `exact`，`apply_mod_cast` 对应 `apply`。编写 `exact_mod_cast h` 和 `apply_mod_cast h` 将在使用 `exact h` 或 `apply h` 之前规范化目标和 `h` 中的强制转换。
- `rw_mod_cast` 对应 `rw`。它在重写之间应用 `norm_cast`。
- `assumption_mod_cast` 对应 `assumption`。这实际上是 `norm_cast at *; assumption`，但更高效。它规范化目标中的强制转换，并对上下文中的每个假设 `h`，尝试规范化 `h` 中的强制转换并使用 `exact h`。

另请参见 `push_cast`，它将强制转换向内移动而非向外提升。

## norm_num
定义于：`Mathlib.Tactic.normNum`

规范化数值表达式。支持在`ℕ`、`ℤ`、`ℚ`、`ℝ`、`ℂ`等数值类型及部分通用代数类型上进行`+`、`-`、`*`、`/`、`⁻¹`、`^`和`%`运算，并能证明形如`A = B`、`A ≠ B`、`A < B`及`A ≤ B`的目标（其中`A`和`B`为数值表达式）。此外，还包含一个相对简单的质数证明器。

## norm_num1
定义于：`Mathlib.Tactic.normNum1`

`norm_num`的基础版本，不调用`simp`。

## nth_rewrite
定义于：`Mathlib.Tactic.nthRewriteSeq`

`nth_rewrite`是`rewrite`的变体，仅修改表达式第`n₁, ..., nₖ`次出现的匹配项。`nth_rewrite n₁ ... nₖ [eq₁, eq₂,..., eqₘ]`会按顺序对每个等式`eqᵢ`的第`n₁, ..., nₖ`次_出现_进行重写。计数从`1`开始，按优先顺序排列。

例如：
```lean
example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rewrite 2 3 [h]
/-
a: ℕ
h: a = 1
⊢ a + 1 + 1 + a + a = 5
-/
```
可见左侧第二和第三个`a`被`nth_rewrite`重写。

理解优先顺序的重要性，参考下例：
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] -- ⊢ (b + a) + c = (b + a) + c
```
此处尽管出现参数为`2`，`(a + b)`仍被重写为`(b + a)`。这是因为在优先顺序中，第一个`_ + _`出现是将`a + b`与`c`相加，而`a + b`中的出现计为第二次。

若通过`eqᵢ`重写引入新项`t`，则此`t`的实例在后续使用`eqⱼ`（`j > i`）重写时将被计为`t`的出现。如下例所示：
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rewrite 3 [h, h]
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b + b) + a + a = 0
-/
```
第一次使用`h`重写后，目标变为：
```lean
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b) + a + a = 0
-/
```
新引入的`a`恰好成为第三次出现，因此后续的`nth_rewrite`会重写该`a`。

## nth_rw
定义于：`Mathlib.Tactic.nthRwSeq`

`nth_rw`是`rw`的变体，仅修改表达式第`n₁, ..., nₖ`次出现的匹配项。类似`rw`，但不同于`nth_rewrite`，它会在重写后尝试使用`rfl`闭合目标。`nth_rw n₁ ... nₖ [eq₁, eq₂,..., eqₘ]`会按顺序对每个等式`eqᵢ`的第`n₁, ..., nₖ`次_出现_进行重写。计数从`1`开始，按优先顺序排列。例如：
```lean
example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rw 2 3 [h]
/-
a: ℕ
h: a = 1
⊢ a + 1 + 1 + a + a = 5
-/
```
可见左侧第二和第三个`a`被`nth_rw`重写。

理解优先顺序的重要性，参考下例：
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] -- ⊢ (b + a) + c = (b + a) + c
```
此处尽管出现参数为`2`，`(a + b)`仍被重写为`(b + a)`。这是因为在优先顺序中，第一个`_ + _`出现是将`a + b`与`c`相加，而`a + b`中的出现计为第二次。

若通过`eqᵢ`重写引入新项`t`，则此`t`的实例在后续使用`eqⱼ`（`j > i`）重写时将被计为`t`的出现。如下例所示：
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rw 3 [h, h]
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b + b) + a + a = 0
-/
```
第一次使用`h`重写后，目标变为：
```lean
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b) + a + a = 0
-/
```
新引入的`a`恰好成为第三次出现，因此后续的`nth_rw`会重写该`a`。

此外，`nth_rw`会在可能时使用`rfl`闭合剩余目标。

## observe
定义于：`Mathlib.Tactic.LibrarySearch.observe`

`observe hp : p`断言命题`p`，并尝试使用`exact?`进行证明。若未找到证明，则策略失败。等效于`have hp : p := by exact?`。

若省略`hp`，则使用占位符`this`。

变体`observe? hp : p`会输出形如`have hp : p := proof_term`的追踪信息，有助于加速证明过程。

## observe?
定义于：`Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_Using__,,»`

`observe hp : p`断言命题`p`，并尝试使用`exact?`进行证明。若未找到证明，则策略失败。等效于`have hp : p := by exact?`。

若省略`hp`，则使用占位符`this`。

变体`observe? hp : p`会输出形如`have hp : p := proof_term`的追踪信息，有助于加速证明过程。

## observe?
定义于：`Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_»`

`observe hp : p`断言命题`p`，并尝试使用`exact?`进行证明。若未找到证明，则策略失败。等效于`have hp : p := by exact?`。

若省略`hp`，则使用占位符`this`。

变体`observe? hp : p`会输出形如`have hp : p := proof_term`的追踪信息，有助于加速证明过程。

## obtain
定义于：`Lean.Parser.Tactic.obtain`

`obtain`策略结合了`have`和`rcases`。关于模式支持的描述，请参考`rcases`。

```lean
obtain ⟨patt⟩ : type := proof
```
等效于：
```lean
have h : type := proof
rcases h with ⟨patt⟩
```

若省略`⟨patt⟩`，`rcases`将尝试推断模式。

若省略`type`，则必须提供`:= proof`。

## omega
定义于：`Lean.Parser.Tactic.omega`

`omega`策略用于解决整数和自然数的线性算术问题。

目前尚未成为完整的决策过程（无“dark”或“grey” shadows），但对许多问题有效。

我们处理形如`x = y`、`x < y`、`x ≤ y`及`k ∣ x`（`x`和`y`属于`Nat`或`Int`，`k`为字面量）的假设，以及这些陈述的否定形式。

我们将不等式两侧分解为原子的线性组合。

遇到字面整数`k`的`x / k`或`x % k`时，引入新的辅助变量及相关不等式。

首次处理时，不执行自然数减法的分情况。若`omega`失败，则递归地对假设中的自然数减法进行分情况处理，并重试。

选项：
```
omega +splitDisjunctions +splitNatSub +splitNatAbs +splitMinMax
```
用于：
* `splitDisjunctions`：若问题无法通过其他方式解决，拆分上下文中的任何析取。
* `splitNatSub`：对每个`((a - b : Nat) : Int)`的出现，必要时拆分`a ≤ b`。
* `splitNatAbs`：对每个`Int.natAbs a`的出现，必要时拆分`0 ≤ a`。
* `splitMinMax`：对每个`min a b`的出现，拆分`min a b = a ∨ min a b = b`。
当前所有选项默认启用。

## on_goal
定义于：`Batteries.Tactic.«tacticOn_goal-_=>_»`

`on_goal n => tacSeq`为第`n`个目标创建块作用域，并尝试在该目标上应用策略序列`tacSeq`。

`on_goal -n => tacSeq`类似，但第`n`个目标从底部开始计数。

不要求目标必须被解决，任何生成的子目标将重新插入目标列表，替换原目标。

## open
定义于：`Lean.Parser.Tactic.open`

策略`open Foo in tacs`类似于命令级的`open Foo`，但仅在策略`tacs`中打开命名空间。

## order
定义于: `Mathlib.Tactic.Order.tacticOrder`

用于在任意`Preorder`、`PartialOrder`或`LinearOrder`中解决目标的收尾策略。

## peel
定义于: `Mathlib.Tactic.Peel.peel`

剥离给定项和目标中的匹配量词，并引入相关变量。

- `peel e` 剥离所有可还原透明度的量词，使用`this`作为剥离假设的名称。
- `peel e with h` 类似`peel e`，但将剥离的假设命名为`h`。若`h`为`_`，则使用`this`作为名称。
- `peel n e` 剥离`n`个量词（默认透明度）。
- `peel n e with x y z ... h` 剥离`n`个量词，命名剥离的假设为`h`，并使用`x`、`y`、`z`等命名引入的变量；这些名称可为`_`。若`h`为`_`，则使用`this`作为名称。变量列表的长度无需与`n`相等。
- `peel e with x₁ ... xₙ h` 等同于`peel n e with x₁ ... xₙ h`。

另有适用于目标中iff的变体：
- `peel n` 剥离iff中的`n`个量词。
- `peel with x₁ ... xₙ` 剥离iff中的`n`个量词并命名。

给定`p q : ℕ → Prop`、`h : ∀ x, p x`及目标`⊢ : ∀ x, q x`，策略`peel h with x h'`将引入`x : ℕ`和`h' : p x`至上下文中，新目标为`⊢ q x`。此策略适用于`∃`、`∀ᶠ`及`∃ᶠ`，并可应用于一系列量词。注意，此设置逻辑上较弱，故使用此策略并非总可行。

更复杂示例，给定假设及目标：
```lean
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
⊢ ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ ε
```
（仅在`<`/`≤`上不同），应用`peel h with ε hε N n hn h_peel`将得到策略状态：
```lean
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
ε : ℝ
hε : 0 < ε
N n : ℕ
hn : N ≤ n
h_peel : 1 / (n + 1 : ℝ) < ε
⊢ 1 / (n + 1 : ℝ) ≤ ε
```
目标可通过`exact h_peel.le`关闭。注意在此例中，`h`与目标逻辑等价，但`peel`无法直接用于证明目标蕴含`h`。

此外，`peel`支持形如`(∀ x, p x) ↔ ∀ x, q x`的目标，或其它量词类似形式。此时无需提供假设或项，语法相同。因此，对此类目标，语法为`peel 1`或`peel with x`，应用后目标变为`p x ↔ q x`。`congr!`策略亦可使用`congr! 1 with x`应用于此类目标。尽管`congr!`通常应用同余引理，`peel`则专门用于最外层量词。

用户可通过`... using e`提供项`e`以立即关闭目标。例如，`peel h using e`等价于`peel h; exact e`。`using`语法可与`peel`的其它特性结合使用。

此策略通过反复应用如`forall_imp`、`Exists.imp`、`Filter.Eventually.mp`、`Filter.Frequently.mp`及`Filter.Eventually.of_forall`等引理实现。

## pgame_wf_tac
定义于: `SetTheory.PGame.tacticPgame_wf_tac`

处理在使用`PGame`上的良基递归定义时产生的`⊢ Subsequent ..`形式的证明义务。

## pi_lower_bound
定义于: `Real.«tacticPi_lower_bound[_,,]»`

为固定有理数`a`创建`a < π`的证明，给定见证为满足`√(2 + r i) ≤ r(i+1)`（其中`r 0 = 0`）及`√(2 - r n) ≥ a/2^(n+1)`的有理数序列`√2 < r 1 < r 2 < ... < r n < 2`。

## pi_upper_bound
定义于: `Real.«tacticPi_upper_bound[_,,]»`

为固定有理数`a`创建`π < a`的证明，给定见证为满足`√(2 + r i) ≥ r(i+1)`（其中`r 0 = 0`）及`√(2 - r n) ≤ (a - 1/4^n) / 2^(n+1)`的有理数序列`√2 < r 1 < r 2 < ... < r n < 2`。

## pick_goal
定义于: `Batteries.Tactic.«tacticPick_goal-_»`

`pick_goal n`将第`n`个目标移至前端。

`pick_goal -n`将倒数第`n`个目标移至前端。

另见`Tactic.rotate_goals`，该策略将目标从前移至后或反之。

## plausible
定义于: `plausibleSyntax`

`plausible`考虑证明目标并尝试生成反驳陈述的示例。

考虑以下证明目标：

```lean
xs : List Nat,
h : ∃ (x : Nat) (H : x ∈ xs), x < 3
⊢ ∀ (y : Nat), y ∈ xs → y < 5
```

局部常量将被还原，并找到`Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`的实例。`Testable`实例由`Sampleable (List Nat)`、`Decidable (x < 3)`及`Decidable (y < 5)`的实例支持。

示例将按大小升序创建（大致如此）。

找到的首个反例将被打印并导致错误：

```
===================
Found problems!
xs := [1, 28]
x := 1
y := 28
-------------------
```

若`plausible`成功测试100个示例，其行为类似`admit`。若放弃或找到反例，则报告错误。

有关编写自定义`Sampleable`及`Testable`实例的更多信息，请参阅`Testing.Plausible.Testable`。

可选参数通过`plausible (config : { ... })`提供：
* `numInst`（默认100）：测试属性所用的示例数量
* `maxSize`（默认100）：最终大小参数

选项：
* `set_option trace.plausible.decoration true`：打印带量词注解的命题
* `set_option trace.plausible.discarded true`：打印因不满足假设而被丢弃的示例
* `set_option trace.plausible.shrink.steps true`：追踪反例的收缩步骤
* `set_option trace.plausible.shrink.candidates true`：打印收缩每个变量时考虑的候选列表
* `set_option trace.plausible.instance true`：打印用于测试命题的`testable`实例
* `set_option trace.plausible.success true`：打印满足属性的已测试样本

## pnat_positivity
定义于: `Mathlib.Tactic.PNatToNat.tacticPnat_positivity`

为上下文中的每个`x : PNat`添加假设`0 < (↑x : ℕ)`。

## pnat_to_nat
定义于: `Mathlib.Tactic.PNatToNat.tacticPnat_to_nat`

`pnat_to_nat`将上下文中的所有`PNat`转换为`Nat`，重写相关命题。典型用例为`pnat_to_nat; omega`。

## polyrith
定义于: `Mathlib.Tactic.Polyrith.«tacticPolyrithOnly[_]»`

尝试通过假设（及用户指定的额外证明项）的多项式算术证明多项式等式目标。通过生成对`linear_combination`策略的适当调用来证明目标。若调用成功，则向用户建议此调用。

* `polyrith`将使用本地上下文中所有相关假设。
* `polyrith [t1, t2, t3]`将添加证明项t1、t2、t3至本地上下文。
* `polyrith only [h1, h2, h3, t1, t2, t3]`将仅使用本地假设`h1`、`h2`、`h3`及证明项`t1`、`t2`、`t3`，忽略其余本地上下文。

注：
* 此策略需网络连接，因其通过<https://sagecell.sagemath.org/>调用Sage的SageCell网络API。衷心感谢Sage团队及组织允许此使用。
* 此策略假设用户路径中可用`curl`。

示例：

```lean
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
    x*y = -2*y + 1 := by
  polyrith
-- 建议尝试：linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
  polyrith
-- 建议尝试：linear_combination (2 * y + x) * hzw

axiom scary : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 := by
  polyrith only [scary c d, h]
-- 建议尝试：linear_combination scary c d + h
```## positivity
定义于：`Mathlib.Tactic.Positivity.positivity`

用于解决形如 `0 ≤ x`、`0 < x` 和 `x ≠ 0` 目标的策略。该策略根据表达式 `x` 的语法递归工作，如果组成表达式的所有原子都能通过 `norm_num` 证明具有正数/非负/非零的数值下界。此策略要么关闭目标，要么失败。

示例：
```lean
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by
  positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by
  positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by
  positivity
```

## pure_coherence
定义于：`Mathlib.Tactic.Coherence.pure_coherence`

`pure_coherence` 利用幺半范畴的连贯性定理来证明目标。它可以证明仅由结合子、单位子和恒等态射组成的任何等式。
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  pure_coherence
```

用户通常只需使用 `coherence` 策略，该策略还能处理形如 `a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'` 的恒等式，其中 `a = a'`、`b = b'` 和 `c = c'` 可使用 `pure_coherence` 证明。

## push_cast
定义于：`Lean.Parser.Tactic.pushCast`

`push_cast` 重写目标以将某些强制转换（*casts*）向叶节点方向内移。这使用 `norm_cast` 引理的前向方向。例如，`↑(a + b)` 将被重写为 `↑a + ↑b`。
- `push_cast` 将目标中的强制转换内移。
- `push_cast at h` 将假设 `h` 中的强制转换内移。
可结合额外简化引理使用，例如 `push_cast [Int.add_zero]`。

示例：
```lean
example (a b : Nat)
    (h1 : ((a + b : Nat) : Int) = 10)
    (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  /-
  h1 : ↑(a + b) = 10
  h2 : ↑(a + b + 0) = 10
  ⊢ ↑(a + b) = 10
  -/
  push_cast
  /- 现在
  ⊢ ↑a + ↑b = 10
  -/
  push_cast at h1
  push_cast [Int.add_zero] at h2
  /- 现在
  h1 h2 : ↑a + ↑b = 10
  -/
  exact h1
```

另见 `norm_cast`。

## push_neg
定义于：`Mathlib.Tactic.PushNeg.tacticPush_neg_`

将否定推入假设的结论中。例如，假设 `h : ¬ ∀ x, ∃ y, x ≤ y` 将被 `push_neg at h` 转换为 `h : ∃ x, ∀ y, y < x`。变量名称保持不变。
此策略将否定推入表达式内部。例如，给定假设
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε
```
执行 `push_neg at h` 会将 `h` 转换为
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|)
```
（漂亮的打印器不使用缩写 `∀ δ > 0` 和 `∃ ε > 0`，但此问题与 `push_neg` 无关）。

注意，与此策略相比，使用相关引理的 `simp` 不会保留名称。可以使用 `push_neg` 在目标处应用此策略，或在所有假设和目标处使用 `push_neg at *`，或在选定的假设和目标处使用如 `push_neg at h h' ⊢`。

此策略有两种模式：标准模式下，它将 `¬(p ∧ q)` 转换为 `p → ¬q`；分配模式下，它生成 `¬p ∨ ¬q`。要使用分配模式，请设置 `set_option push_neg.use_distrib true`。

## qify
定义于：`Mathlib.Tactic.Qify.qify`

`qify` 策略用于将命题从 `ℕ` 或 `ℤ` 转移到 `ℚ`。这通常很有用，因为 `ℚ` 具有良好的除法行为。
```lean
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
  sorry
```
`qify` 可以接受额外的引理用于简化。这在存在自然数减法时特别有用：传递 `≤` 参数将允许 `push_cast` 完成更多工作。
```lean
example (a b c : ℤ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b := by
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h
```
`qify` 利用 `@[zify_simps]` 和 `@[qify_simps]` 属性来转移命题，并使用 `push_cast` 策略简化 `ℚ` 值表达式。

## rcases
定义于：`Lean.Parser.Tactic.rcases`

`rcases` 是一个根据模式递归执行 `cases` 的策略。它用于解构由归纳类型组成的假设或表达式，如 `h1 : a ∧ b ∧ c ∨ d` 或 `h2 : ∃ x y, trans_rel R x y`。常见用法如 `rcases h1 with ⟨ha, hb, hc⟩ | hd` 或 `rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩`。

`rcases` 模式的每个元素与特定的局部假设（其中大部分在 `rcases` 执行期间生成，表示从输入表达式解构出的单个元素）匹配。`rcases` 模式的语法如下：

* 名称如 `x`，将活动假设命名为 `x`。
* 空白 `_`，不执行任何操作（让 `cases` 使用的自动命名系统命名假设）。
* 连字符 `-`，清除活动假设及其依赖项。
* 关键字 `rfl`，期望假设为 `h : a = b`，并对假设调用 `subst`（效果为在所有地方用 `a` 替换 `b` 或反之）。
* 类型归属 `p : ty`，将假设的类型设置为 `ty` 然后将其与 `p` 匹配（当然，`ty` 必须与 `h` 的实际类型统一）。
* 元组模式 `⟨p1, p2, p3⟩`，匹配具有多个参数的构造函数，或一系列嵌套的合取或存在。例如，如果活动假设为 `a ∧ b ∧ c`，则将解构合取，`p1` 匹配 `a`，`p2` 匹配 `b` 等。
* 在元组模式前加 `@` 如 `@⟨p1, p2, p3⟩` 将绑定构造函数中的所有参数，而省略 `@` 将仅在显式参数上使用模式。
* 交替模式 `p1 | p2 | p3`，匹配具有多个构造函数的归纳类型，或嵌套的析取如 `a ∨ b ∨ c`。

像 `⟨a, b, c⟩ | ⟨d, e⟩` 这样的模式将对归纳数据类型进行拆分，将第一个构造器的前三个参数命名为 `a,b,c`，第二个构造器的前两个参数命名为 `d,e`。如果列表长度与构造器的参数数量或构造器数量不符，剩余变量将自动命名。如果有嵌套括号如 `⟨⟨a⟩, b | c⟩ | d`，这些将根据需要引起更多的案例分析。如果参数过多，如对 `∃ x, ∃ y, p x` 使用 `⟨a, b, c⟩`，则将被视为 `⟨a, ⟨b, c⟩⟩`，必要时拆分最后一个参数。

`rcases` 对商类型有特殊支持：商归纳到 Prop 的工作方式类似于匹配构造器 `quot.mk`。

`rcases h : e with PAT` 将执行与 `rcases e with PAT` 相同的操作，但会在上下文中添加假设 `h : e = PAT`。

## rcongr
定义于：`Batteries.Tactic.rcongr`

重复应用 `congr` 和 `ext`，使用给定模式作为 `ext` 的参数。

此策略在以下两种情况下停止：
* `congr` 失败（未取得进展），在已应用 `ext` 后。
* `congr` 取消了上一次 `ext` 的使用。此时，状态将恢复到应用 `congr` 之前。

例如，当目标为
```
⊢ (fun x => f x + 3) '' s = (fun x => g x + 3) '' s
```
时，`rcongr x` 将生成目标
```
x : α ⊢ f x = g x
```
这与 `congr; ext x; congr` 产生的结果相同。

相比之下，`congr` 将生成
```
⊢ (fun x => f x + 3) = (fun x => g x + 3)
```
而 `congr with x`（或 `congr; ext x`）将生成
```
x : α ⊢ f x + 3 = g x + 3
```

## recover
定义于：`Mathlib.Tactic.tacticRecover_`

修饰符 `recover` 用于调试目标被错误关闭的情况的策略（序列）。策略 `recover tacs` 对策略（序列）`tacs` 应用这些策略，然后添加未关闭的目标，从原始目标开始。

## reduce
定义于：`Mathlib.Tactic.tacticReduce__`

`reduce at loc` 完全规约给定位置。这也作为 `conv` 模式的策略存在。

## reduce_mod_char
定义于：`Tactic.ReduceModChar.reduce_mod_char`

策略`reduce_mod_char`寻找特征为`p`的数值表达式，并将这些数值缩减至`0`到`p`之间。

例如：
```lean
example:  (5 : ZMod 4) = 1 := by reduce_mod_char
example:  (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

该策略还处理取反操作，将其转换为乘以`p - 1`，减法操作同理。

为提高性能，此策略通过子表达式的类型来判断其是否处于正特征环境中，而非尝试合成`CharP`实例。变体`reduce_mod_char!`会尝试使用上下文中的`CharP R n`假设（由于类型类系统的限制，若`n`尚未知，策略无法搜索`CharP R n`实例；此时可使用`have : CharP R n := inferInstance; reduce_mod_char!`作为临时解决方案）。

## reduce_mod_char!
定义于：`Tactic.ReduceModChar.reduce_mod_char!`

策略`reduce_mod_char!`寻找特征为`p`的数值表达式，并将这些数值缩减至`0`到`p`之间。

例如：
```lean
example:  (5 : ZMod 4) = 1 := by reduce_mod_char
example:  (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

该策略还处理取反操作，将其转换为乘以`p - 1`，减法操作同理。

为提高性能，此策略通过子表达式的类型来判断其是否处于正特征环境中，而非尝试合成`CharP`实例。变体`reduce_mod_char!`会尝试使用上下文中的`CharP R n`假设（由于类型类系统的限制，若`n`尚未知，策略无法搜索`CharP R n`实例；此时可使用`have : CharP R n := inferInstance; reduce_mod_char!`作为临时解决方案）。

## refine
定义于：`Lean.Parser.Tactic.refine`

`refine e`的行为类似于`exact e`，不同之处在于，若主目标的目标类型无法通过统一解决`e`中的命名（`?x`）或未命名（`?_`）孔洞，则这些孔洞将被转换为新目标，并使用孔洞名称（如有）作为目标案例名称。

## refine'
定义于：`Lean.Parser.Tactic.refine'`

`refine' e`的行为类似于`refine e`，不同之处在于未解决的占位符（`_`）和隐式参数也会被转换为新目标。

## refine_lift
定义于：`Lean.Parser.Tactic.tacticRefine_lift_`

用于提升`have`/`suffices`/`let`等的辅助宏。确保在精炼后，“?_”成为主目标。

## refine_lift'
定义于：`Lean.Parser.Tactic.tacticRefine_lift'_`

类似于`refine_lift`，但使用`refine'`

## refold_let
定义于：`Mathlib.Tactic.refoldLetStx`

`refold_let x y z at loc`在指定位置查找本地定义`x`、`y`和`z`的实体，并将其替换回`x`、`y`或`z`。此为zeta规约的逆操作。此策略也可作为`conv`模式策略使用。

## rel
定义于：`Mathlib.Tactic.GCongr.«tacticRel[_]»`

`rel`策略应用“广义同余”规则，通过“替换”解决关系型目标。例如：
```lean
示例 {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) : x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]
```
在此示例中，我们将假设`a ≤ b`和`c ≤ d`“替换”到目标的左端`x ^ 2 * a + c`，得到右端`x ^ 2 * b + d`，从而证明目标。

所使用的“广义同余”规则为标有`@[gcongr]`属性的库引理。例如，上述示例构造了证明项：
```lean
add_le_add (mul_le_mul_of_nonneg_left h1 (pow_bit0_nonneg x 1)) h2
```
使用的广义同余引理为`add_le_add`和`mul_le_mul_of_nonneg_left`。若无适用的广义同余引理，策略将失败。

此策略尝试通过`gcongr_discharger`解决这些广义同余引理的边目标（如上述`mul_le_mul_of_nonneg_left`应用中的边目标`0 ≤ x ^ 2`），该工具包装了`positivity`但可扩展。若边目标无法以此方式解决，策略将失败。

## rename
定义于：`Lean.Parser.Tactic.rename`

`rename t => x`将类型匹配`t`（可含占位符）的最新假设重命名为`x`，若无此类假设则失败。

## rename'
定义于：`Mathlib.Tactic.rename'`

`rename' h => hnew`将名为`h`的假设重命名为`hnew`。重命名多个假设时，使用`rename' h₁ => h₁new, h₂ => h₂new`。可通过`rename' a => b, b => a`交换两个变量。

## rename_bvar
定义于：`Mathlib.Tactic.«tacticRename_bvar_→__»`

* `rename_bvar old → new`将目标中所有名为`old`的绑定变量重命名为`new`。
* `rename_bvar old → new at h`在假设`h`中执行相同操作。

```lean
示例 (P : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m := by
  rename_bvar n → q at h -- h现为∀ (q : ℕ), ∃ (m : ℕ), P q m
  rename_bvar m → n -- 目标现为∀ (l : ℕ), ∃ (n : ℕ), P k n
  exact h -- Lean不关心这些绑定变量名称
```
注意：名称冲突将自动解决。

## rename_i
定义于：`Lean.Parser.Tactic.renameI`

`rename_i x_1 ... x_n`使用给定名称重命名最后的`n`个不可访问名称。

## repeat
定义于：`Lean.Parser.Tactic.tacticRepeat_`

`repeat tac`重复应用`tac`直至其失败。`tac`可为策略序列，若`tac`在执行过程中失败，`repeat`将撤销`tac`对策略状态的部分更改。

`tac`应最终失败，否则`repeat tac`将无限运行。

另见：
* `try tac`类似于`repeat tac`但最多应用一次`tac`。
* `repeat' tac`递归应用`tac`至各子目标。
* `first | tac1 | tac2`实现`repeat`的回溯机制。

## repeat'
定义于：`Lean.Parser.Tactic.repeat'`

`repeat' tac`递归应用`tac`至所有子目标直至其失败。即若`tac`生成多个子目标，`repeat' tac`将分别应用于每个子目标。

另见：
* `repeat tac`仅简单重复应用`tac`。
* `repeat1' tac`为`repeat' tac`但要求`tac`至少成功应用于某个目标一次。

## repeat1
定义于：`Mathlib.Tactic.tacticRepeat1_`

`repeat1 tac`至少对主目标应用一次`tac`。若应用成功，则递归应用于生成的子目标直至最终失败。

## repeat1'
定义于：`Lean.Parser.Tactic.repeat1'`

`repeat1' tac`递归应用`tac`至所有子目标直至其失败，但若`tac`未成功应用于任何初始目标，`repeat1' tac`将失败。

另见：
* `repeat tac`仅简单重复应用`tac`。
* `repeat' tac`类似于`repeat1' tac`但不要求`tac`至少成功一次。

## replace
定义于：`Mathlib.Tactic.replace'`

行为类似于`have`，但会移除同名假设（若存在）。例如，若当前状态为：
```lean
f : α → β
h : α
⊢ goal
```
执行`replace h : β`后状态为：
```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h : β
⊢ goal
```
而`have h : β`将导致：
```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h✝ : α
h : β
⊢ goal
```

## replace
定义于：`Lean.Parser.Tactic.replace`

行为类似于`have`，但会移除同名假设（若存在）。例如，若当前状态为：
```lean
f : α → β
h : α
⊢ goal
```
执行`replace h := f h`后状态为：
```lean
f : α → β
h : β
⊢ goal
```
而`have h := f h`将导致：
```lean
f : α → β
h† : α
h : β
⊢ goal
```
此策略可用于模拟Coq的`specialize`和`apply at`策略。

## restrict_tac
定义于：`TopCat.Presheaf.restrict_tac`

`restrict_tac`解决子集间的关系（复制自`aesop cat`）

## restrict_tac?
定义于：`TopCat.Presheaf.restrict_tac?`

`restrict_tac?`传递来自`aesop`的`Try this`

## revert
定义于：`Lean.Parser.Tactic.revert`

`revert x...` 是 `intro x...` 的逆操作：它将给定的假设移回主目标的目标类型中。

## rewrite
定义于：`Lean.Parser.Tactic.rewriteSeq`

`rewrite [e]` 将恒等式 `e` 作为重写规则应用于主目标的目标。若 `e` 前有左箭头（`←` 或 `<-`），则反向应用重写。若 `e` 是已定义的常量，则使用与 `e` 相关的等式定理。这为展开 `e` 提供了一种便捷方式。
- `rewrite [e₁, ..., eₙ]` 依次应用给定的规则。
- `rewrite [e] at l` 在位置 `l` 处重写 `e`，其中 `l` 为 `*` 或局部上下文中的假设列表。后者中也可使用转折符 `⊢` 或 `|-` 表示目标的目标。

使用 `rw (occs := .pos L) [e]`（其中 `L : List Nat`）可控制重写哪些“出现项”。（此选项适用于每条规则，因此通常仅与单一规则配合使用。）出现项从 `1` 开始计数。在每个允许的出现项处，重写规则 `e` 的参数可能被实例化，从而限制后续可找到的重写项。（不允许的出现项不会导致实例化。）`(occs := .neg L)` 允许跳过指定出现项。

## rfl
定义于：`Lean.Parser.Tactic.tacticRfl`

此策略适用于目标形式为 `x ~ x` 的情况，其中 `~` 为等式、异构等式或任何带有 `@[refl]` 属性标记的自反性引理的关系。

## rfl'
定义于：`Lean.Parser.Tactic.tacticRfl'`

`rfl'` 类似于 `rfl`，但禁用智能展开并展开所有类型的定义（包括通过良基递归定义的声明）。

## rify
定义于：`Mathlib.Tactic.Rify.rify`

`rify` 策略用于将命题从 `ℕ`、`ℤ` 或 `ℚ` 转换到 `ℝ`。尽管不如其同类 `zify` 和 `qify` 实用，但当目标或上下文中已涉及实数时，它可能有用。

以下示例中，假设 `hn` 关于自然数，`hk` 关于整数并涉及自然数到 `ℤ` 的转换，结论关于实数。证明使用 `rify` 将两个假设提升至 `ℝ` 后调用 `linarith`：
```
example {n : ℕ} {k : ℤ} (hn : 8 ≤ n) (hk : 2 * k ≤ n + 2) :
    (0 : ℝ) < n - k - 1 := by
  rify at hn hk /- 现有 hn : 8 ≤ (n : ℝ)   hk : 2 * (k : ℝ) ≤ (n : ℝ) + 2 -/
  linarith
```

`rify` 利用 `@[zify_simps]`、`@[qify_simps]` 和 `@[rify_simps]` 属性迁移命题，并使用 `push_cast` 策略简化 `ℝ` 值的表达式。

`rify` 可接收额外引理以用于简化。这在存在自然数减法时尤为有用：传递 `≤` 参数可让 `push_cast` 完成更多工作。
```lean
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : a < b + c := by
  rify [hab] at h ⊢
  linarith
```
注意，上述示例中 `zify` 或 `qify` 同样有效（且 `zify` 是自然选择，因其足以消除病态的 `ℕ` 减法）。

## right
定义于：`Lean.Parser.Tactic.right`

当目标为恰好有两个构造函数的归纳类型时，应用第二个构造函数，否则失败。
```lean
example {p q : Prop} (h : q) : p ∨ q := by
  right
  exact h
```

## ring
定义于：`Mathlib.Tactic.RingNF.ring`

用于在*交换*（半）环中评估表达式的策略，允许指数中含有变量。若目标不适合 `ring`（如非等式），将建议使用 `ring_nf`。
- `ring!` 使用更具侵略性的可约性设置以判定原子项的相等性。
- `ring1` 在目标非等式时失败。

例如：
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- 建议使用 ring_nf
```

## ring!
定义于：`Mathlib.Tactic.RingNF.tacticRing!`

用于在*交换*（半）环中评估表达式的策略，允许指数中含有变量。若目标不适合 `ring`（如非等式），将建议使用 `ring_nf`。
- `ring!` 使用更具侵略性的可约性设置以判定原子项的相等性。
- `ring1` 在目标非等式时失败。

例如：
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- 建议使用 ring_nf
```

## ring1
定义于：`Mathlib.Tactic.Ring.ring1`

用于解*交换*（半）环方程的策略，允许指数中含有变量。
- 此版本 `ring` 在目标非等式时失败。
- 变体 `ring1!` 使用更具侵略性的可约性设置以判定原子项的相等性。

## ring1!
定义于：`Mathlib.Tactic.Ring.tacticRing1!`

用于解*交换*（半）环方程的策略，允许指数中含有变量。
- 此版本 `ring` 在目标非等式时失败。
- 变体 `ring1!` 使用更具侵略性的可约性设置以判定原子项的相等性。

## ring1_nf
定义于：`Mathlib.Tactic.RingNF.ring1NF`

用于解*交换*（半）环方程的策略，允许指数中含有变量。
- 此版本 `ring1` 使用 `ring_nf` 简化原子项。
- 变体 `ring1_nf!` 使用更具侵略性的可约性设置以判定原子项的相等性。

## ring1_nf!
定义于：`Mathlib.Tactic.RingNF.tacticRing1_nf!_`

用于解*交换*（半）环方程的策略，允许指数中含有变量。
- 此版本 `ring1` 使用 `ring_nf` 简化原子项。
- 变体 `ring1_nf!` 使用更具侵略性的可约性设置以判定原子项的相等性。

## ring_nf
定义于：`Mathlib.Tactic.RingNF.ringNF`

用于在交换（半）环语言中表达式简化的策略，将所有环表达式重写为正规形式。
- `ring_nf!` 使用更具侵略性的可约性设置以识别原子项。
- `ring_nf (config := cfg)` 允许额外配置：
  - `red`：可约性设置（被 `!` 覆盖）
  - `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
  - `recursive`：若为真，`ring_nf` 将递归进入原子项
- `ring_nf` 可作为策略或转换策略使用。在策略模式中，`ring_nf at h` 可用于在假设中重写。

此策略可用于非终止性地将目标中的环表达式规范化，如 `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`，并能证明某些 `ring` 无法处理的方程，因其涉及子项内的环推理，如 `sin (x + y) + sin (y + x) = 2 * sin (x + y)`。

## ring_nf!
定义于：`Mathlib.Tactic.RingNF.tacticRing_nf!__`

用于在交换（半）环语言中表达式简化的策略，将所有环表达式重写为正规形式。
- `ring_nf!` 使用更具侵略性的可约性设置以识别原子项。
- `ring_nf (config := cfg)` 允许额外配置：
  - `red`：可约性设置（被 `!` 覆盖）
  - `zetaDelta`：若为真，局部 let 变量可展开（被 `!` 覆盖）
  - `recursive`：若为真，`ring_nf` 将递归进入原子项
- `ring_nf` 可作为策略或转换策略使用。在策略模式中，`ring_nf at h` 可用于在假设中重写。

此策略可用于非终止性地将目标中的环表达式规范化，如 `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`，并能证明某些 `ring` 无法处理的方程，因其涉及子项内的环推理，如 `sin (x + y) + sin (y + x) = 2 * sin (x + y)`。

## rintro
定义于：`Lean.Parser.Tactic.rintro`

`rintro` 策略结合了 `intros` 策略和 `rcases` 的功能，允许在引入变量时进行解构模式。关于支持的模式描述，请参见 `rcases`。例如，`rintro (a | ⟨b, c⟩) ⟨d, e⟩` 将引入两个变量，然后对它们进行分支处理，生成两个子目标：一个带有变量 `a d e`，另一个带有 `b c d e`。

与 `rcases` 不同，`rintro` 还支持 `(x y : ty)` 形式的语法，用于同时引入多个变量并进行类型标注，类似于绑定器。

## rotate_left
定义于：`Lean.Parser.Tactic.rotateLeft`

`rotate_left n` 将目标向左轮换 `n` 次。即，`rotate_left 1` 将主目标移动到子目标列表的末尾。如果未指定 `n`，默认值为 `1`。

## rotate_right
定义于：`Lean.Parser.Tactic.rotateRight`

`rotate_right n` 将目标向右轮换 `n` 次。即，将末尾的目标移动到前端 `n` 次。如果未指定 `n`，默认值为 `1`。

## rsuffices
定义于：`Mathlib.Tactic.rsuffices`

`rsuffices` 是 `suffices` 的替代版本，允许使用在 `obtain` 块中有效的任何语法。此策略通过调用 `obtain` 处理表达式，然后执行 `rotate_left`。

## run_tac
定义于：`Lean.Parser.Tactic.runTac`

`run_tac doSeq` 策略用于执行 `TacticM Unit` 中的代码。

## rw
定义于：`Lean.Parser.Tactic.rwSeq`

`rw` 类似于 `rewrite`，但在之后会尝试通过“廉价”（可还原的）`rfl` 闭合目标。

## rw?
定义于：`Lean.Parser.Tactic.rewrites?`

`rw?` 尝试查找可用于重写目标的引理。

`rw?` 不应留在最终证明中；它类似于 `apply?`，是一个搜索工具。

建议会以 `rw [h]` 或 `rw [← h]` 的形式打印。

可通过 `rw? [-my_lemma, -my_theorem]` 防止 `rw?` 使用指定名称的引理。

## rw_mod_cast
定义于：`Lean.Parser.Tactic.tacticRw_mod_cast___`

根据给定规则进行重写，每次重写前规范化类型转换。

## rw_search
定义于：`Mathlib.Tactic.RewriteSearch.tacticRw_search_`

`rw_search` 尝试通过反复重写库中的引理来解决等式目标。若未找到解，则返回在 `maxHeartbeats` 超时前找到的最佳重写序列。

搜索采用最佳优先策略，最小化等式两侧美化打印表达式的 Levenshtein 编辑距离。（字符串以空格、分隔符 `(`, `)`, `[`, `]`, `,` 进行分词。）

可通过 `rw_search [-my_lemma, -my_theorem]` 阻止 `rw_search` 使用指定名称的定理。

## rwa
定义于：`Lean.Parser.Tactic.tacticRwa__`

`rwa` 是 `rw; assumption` 的简写形式。

## saturate
定义于：`Aesop.Frontend.tacticSaturate_____`


## saturate?
定义于：`Aesop.Frontend.tacticSaturate?_____`


## says
定义于：`Mathlib.Tactic.Says.says`

若书写 `X says`（其中 `X` 是会产生“Try this: Y”消息的策略），则会生成“Try this: X says Y”消息。点击替换 `X says` 为 `X says Y` 后，`X says Y` 将仅执行 `Y`。

典型用法为：
```lean
simp? [X] says simp only [X, Y, Z]
```

若设置 `set_option says.verify true`（在 CI 中自动设置），则 `X says Y` 会执行 `X` 并验证其仍输出“Try this: Y”。

## set
定义于：`Mathlib.Tactic.setTactic`


## set!
定义于：`Mathlib.Tactic.tacticSet!_`


## set_option
定义于：`Lean.Parser.Tactic.set_option`

`set_option opt val in tacs`（作为策略）类似于命令层的 `set_option opt val`，但仅在策略 `tacs` 内设置选项。

## show
定义于：`Lean.Parser.Tactic.tacticShow_`

`show t` 查找首个目标其目标可与 `t` 统一。将其设为主目标，执行统一，并将目标替换为统一后的 `t` 版本。

## show_term
定义于：`Lean.Parser.Tactic.showTerm`

`show_term tac` 运行 `tac`，随后以“exact X Y Z”或“refine X ?_ Z”形式打印生成的项（若存在剩余子目标）。

（部分策略的打印项可能不易于人类阅读。）

## simp
定义于：`Lean.Parser.Tactic.simp`

`simp` 策略使用标记为 `[simp]` 属性的引理和假设来简化主目标或非依赖假设。其变体包括：
- `simp`：使用 `[simp]` 引理简化主目标。
- `simp [h₁, h₂, ..., hₙ]`：使用 `[simp]` 引理及给定 `hᵢ` 简化主目标。若 `hᵢ` 为已定义常量 `f`，则展开 `f`。
- `simp [*]`：使用 `[simp]` 引理及所有假设简化主目标。
- `simp only [h₁, h₂, ..., hₙ]`：类似 `simp [h₁, h₂, ..., hₙ]`，但不使用 `[simp]` 引理。
- `simp [-id₁, ..., -idₙ]`：使用 `[simp]` 引理简化主目标，但排除指定名称的引理。
- `simp at h₁ h₂ ... hₙ`：在假设 `h₁ : T₁` ... `hₙ : Tₙ` 上应用简化。若目标或其他假设依赖 `hᵢ`，则引入新的简化假设，但旧假设仍保留在上下文中。
- `simp at *`：简化所有假设及目标。
- `simp [*] at *`：使用其他假设简化目标及所有命题性假设。

## simp!
定义于：`Lean.Parser.Tactic.simpAutoUnfold`

`simp!` 是 `simp` 的简写形式，启用 `autoUnfold := true`。这将使用所有等式引理进行重写，可部分求值多项定义。

## simp?
定义于：`Lean.Parser.Tactic.simpTrace`

`simp?` 接受与 `simp` 相同的参数，但报告等效的 `simp only` 调用，以闭合目标。有助于减少本地调用中的简化集以加速处理。
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- 输出 "Try this: simp only [ite_true]"
```

此命令也可用于 `simp_all` 和 `dsimp`。

## simp?!
定义于：`Lean.Parser.Tactic.tacticSimp?!_`

`simp?` 接受与 `simp` 相同的参数，但报告等效的 `simp only` 调用，以闭合目标。有助于减少本地调用中的简化集以加速处理。
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- 输出 "Try this: simp only [ite_true]"
```

此命令也可用于 `simp_all` 和 `dsimp`。

## simp_all
定义于：`Lean.Parser.Tactic.simpAll`

`simp_all` 是 `simp [*] at *` 的强化版本，持续简化假设及目标直至无适用简化。仅考虑非依赖命题性假设。

## simp_all!
定义于：`Lean.Parser.Tactic.simpAllAutoUnfold`

`simp_all!` 是 `simp_all` 的简写形式，启用 `autoUnfold := true`。这将使用所有等式引理进行重写，可部分求值多项定义。

## simp_all?
定义于：`Lean.Parser.Tactic.simpAllTrace`

`simp?` 接受与 `simp` 相同的参数，但报告等效的 `simp only` 调用，以闭合目标。有助于减少本地调用中的简化集以加速处理。
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- 输出 "Try this: simp only [ite_true]"
```

此命令也可用于 `simp_all` 和 `dsimp`。

## simp_all?!
定义于：`Lean.Parser.Tactic.tacticSimp_all?!_`

`simp?` 接受与 `simp` 相同的参数，但报告等效的 `simp only` 调用，以闭合目标。有助于减少本地调用中的简化集以加速处理。
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- 输出 "Try this: simp only [ite_true]"
```

此命令也可用于 `simp_all` 和 `dsimp`。

## simp_all_arith
定义于：`Lean.Parser.Tactic.simpAllArith`

`simp_all_arith` 已被弃用。它曾是 `simp_all +arith +decide` 的简写形式。注意，由于 Lean 已添加了简化过程（simprocs），`+decide` 不再需要用于简化算术表达式。

## simp_all_arith!
定义于：`Lean.Parser.Tactic.simpAllArithBang`

`simp_all_arith!` 已被弃用。它曾是 `simp_all! +arith +decide` 的简写形式。注意，由于 Lean 已添加了简化过程（simprocs），`+decide` 不再需要用于简化算术表达式。

## simp_arith
定义于：`Lean.Parser.Tactic.simpArith`

`simp_arith` 已被弃用。它曾是 `simp +arith +decide` 的简写形式。注意，由于 Lean 已添加了简化过程（simprocs），`+decide` 不再需要用于简化算术表达式。

## simp_arith!
定义于：`Lean.Parser.Tactic.simpArithBang`

`simp_arith!` 已被弃用。它曾是 `simp! +arith +decide` 的简写形式。注意，由于 Lean 已添加了简化过程（simprocs），`+decide` 不再需要用于简化算术表达式。

## simp_intro
定义于：`Mathlib.Tactic.«tacticSimp_intro_____..Only_»`

`simp_intro` 是 `simp` 和 `intro` 的结合策略：它在引入变量的同时简化变量的类型，并利用新变量简化后续参数及目标。
* `simp_intro x y z` 引入名为 `x y z` 的变量
* `simp_intro x y z ..` 引入名为 `x y z` 的变量后，继续引入 `_` 匿名绑定器
* `simp_intro (config := cfg) (discharger := tac) x y .. only [h₁, h₂]`：
  `simp_intro` 接受与 `simp` 相同的配置选项（参见 `simp`）

示例：
```lean
example : x + 0 = y → x = z := by
  simp_intro h
  -- h: x = y ⊢ y = z
  sorry
```

## simp_rw
定义于：`Mathlib.Tactic.tacticSimp_rw___`

`simp_rw` 结合了 `simp` 和 `rw` 的功能。类似于 `rw`，它按顺序应用每条重写规则，但像 `simp` 一样反复应用这些规则，并处理如 `∀ x, ...`、`∃ x, ...` 和 `fun x ↦...` 等绑定器下的表达式。

用法：
- `simp_rw [lemma_1, ..., lemma_n]` 将按顺序应用这些引理来重写目标。以 `←` 开头的引理将反向应用。
- `simp_rw [lemma_1, ..., lemma_n] at h₁ ... hₙ` 对指定假设进行重写。
- `simp_rw [...] at *` 在整个上下文中重写：所有假设及目标。

传递给 `simp_rw` 的引理必须是 `simp` 的有效参数。例如，以下示例中 `simp` 和 `rw` 均无法解决，但 `simp_rw` 可以：

```lean
example {a : ℕ}
    (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
    (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
    (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 := by
  simp_rw [h1, h2]
```

## simp_wf
定义于：`tacticSimp_wf`

展开常用于良基关系定义的表达式。

自 Lean 4.12 起，Lean 在向用户展示目标前会自动展开这些定义，因此本策略不再必要。可移除 `simp_wf` 调用，或替换为普通 `simp` 调用。

## simpa
定义于：`Lean.Parser.Tactic.simpa`

这是 `simp` 的“终结”策略变体，有两种形式：
* `simpa [rules, ⋯] using e` 会使用 `rules` 简化目标及 `e` 的类型，然后尝试用 `e` 闭合目标。
  简化 `e` 的类型使其更可能匹配目标（目标也已被简化）。此构造在 simp 引理集变更时更具鲁棒性。
* `simpa [rules, ⋯]` 会简化目标及上下文中的 `this` 假设（若存在）的类型，然后尝试用 `assumption` 策略闭合目标。

## simpa!
定义于：`Lean.Parser.Tactic.tacticSimpa!_`

这是 `simp` 的“终结”策略变体，有两种形式：
* `simpa [rules, ⋯] using e` 会使用 `rules` 简化目标及 `e` 的类型，然后尝试用 `e` 闭合目标。
  简化 `e` 的类型使其更可能匹配目标（目标也已被简化）。此构造在 simp 引理集变更时更具鲁棒性。
* `simpa [rules, ⋯]` 会简化目标及上下文中的 `this` 假设（若存在）的类型，然后尝试用 `assumption` 策略闭合目标。

## simpa?
定义于：`Lean.Parser.Tactic.tacticSimpa?_`

这是 `simp` 的“终结”策略变体，有两种形式：
* `simpa [rules, ⋯] using e` 会使用 `rules` 简化目标及 `e` 的类型，然后尝试用 `e` 闭合目标。
  简化 `e` 的类型使其更可能匹配目标（目标也已被简化）。此构造在 simp 引理集变更时更具鲁棒性。
* `simpa [rules, ⋯]` 会简化目标及上下文中的 `this` 假设（若存在）的类型，然后尝试用 `assumption` 策略闭合目标。

## simpa?!
定义于：`Lean.Parser.Tactic.tacticSimpa?!_`

这是 `simp` 的“终结”策略变体，有两种形式：
* `simpa [rules, ⋯] using e` 会使用 `rules` 简化目标及 `e` 的类型，然后尝试用 `e` 闭合目标。
  简化 `e` 的类型使其更可能匹配目标（目标也已被简化）。此构造在 simp 引理集变更时更具鲁棒性。
* `simpa [rules, ⋯]` 会简化目标及上下文中的 `this` 假设（若存在）的类型，然后尝试用 `assumption` 策略闭合目标。

## sizeOf_list_dec
定义于：`List.tacticSizeOf_list_dec`

此策略已添加至 `decreasing_trivial` 工具箱，当 `a ∈ as` 时证明 `sizeOf a < sizeOf as`，对于嵌套归纳类型如 `inductive T | mk : List T → T` 的良基递归十分有用。

## skip
定义于：`Lean.Parser.Tactic.skip`

`skip` 无任何操作。

## sleep
定义于：`Lean.Parser.Tactic.sleep`

策略 `sleep ms` 暂停 `ms` 毫秒且不执行任何操作，仅用于调试目的。

## sleep_heartbeats
定义于：`tacticSleep_heartbeats_`

暂停至少 n 次心跳周期，无任何操作。

## slice_lhs
定义于：`sliceLHS`

`slice_lhs a b => tac` 聚焦左侧，根据需要使用范畴组合的结合律，聚焦第 `a` 至 `b` 个态射，并调用 `tac`。

## slice_rhs
定义于：`sliceRHS`

`slice_rhs a b => tac` 聚焦右侧，根据需要使用范畴组合的结合律，聚焦第 `a` 至 `b` 个态射，并调用 `tac`。

## smul_tac
定义于：`RatFunc.tacticSmul_tac`

通过应用 `RatFunc.induction_on` 解决 `RatFunc K` 的方程。

## solve
定义于：`Lean.solveTactic`

类似于 `first`，但仅当给定策略之一解决当前目标时成功。

## solve_by_elim
定义于：`Lean.Parser.Tactic.solveByElim`

`solve_by_elim` 对主目标调用 `apply` 寻找头部匹配的假设，随后在生成的子目标上反复调用 `apply` 直至无子目标残留，最多执行 `maxDepth`（默认 6）次递归步骤。

`solve_by_elim` 解决当前目标或失败。

若子目标无法解决，`solve_by_elim` 将进行回溯。

默认情况下，传递给 `apply` 的假设为局部上下文、`rfl`、`trivial`、`congrFun` 和 `congrArg`。

假设可通过类似 `simp` 的语法调整：
* `solve_by_elim [h₁, h₂, ..., hᵣ]` 同时应用给定表达式。
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` 不包含局部上下文、`rfl`、`trivial`、`congrFun` 或 `congrArg`，除非显式包含。
* `solve_by_elim [-h₁, ... -hₙ]` 移除给定局部假设。
* `solve_by_elim using [a₁, ...]` 使用所有标记有属性 `aᵢ` 的引理（这些属性需通过 `register_label_attr` 创建）。

`solve_by_elim*` 尝试同时解决所有目标，若某目标的解决方案导致其他目标无法解决则进行回溯。
（起始时存在多个目标时，添加或移除局部假设可能表现不稳定。）

通过配置参数传递的可选参数 `solve_by_elim (config := { ... })`
- `maxDepth`: 用于解除生成子目标的最大尝试次数。
- `symm`: 添加所有通过 `symm` 派生的假设（默认为 `true`）。
- `exfalso`: 允许在 `solve_by_elim` 失败时调用 `exfalso` 并重试（默认为 `true`）。
- `transparency`: 调用 `apply` 时更改透明模式。默认为 `.default`，但通常更改为 `.reducible`，以便在尝试应用引理时不会展开半可约定义。

另请参阅 `Lean.Meta.Tactic.Backtrack.BacktrackConfig` 的文档注释，了解允许进一步自定义 `solve_by_elim` 的 `proc`、`suspend` 和 `discharge` 选项。`apply_assumption` 和 `apply_rules` 均通过这些钩子实现。

## sorry
定义于：`Lean.Parser.Tactic.tacticSorry`

`sorry` 策略是用于不完整策略证明的临时占位符，使用 `exact sorry` 关闭主目标。

此策略旨在为证明的不完整部分占位，同时保持语法正确的证明框架。每当证明使用 `sorry` 时，Lean 会发出警告，因此不太可能遗漏。但可以通过查看 `#print axioms my_thm` 命令输出中的 `sorryAx` 来确认定理是否依赖 `sorry`，即 `sorry` 实现所使用的公理。

## sorry_if_sorry
定义于：`CategoryTheory.sorryIfSorry`

如果主目标的类型包含 `sorry`，则使用 `sorry` 关闭主目标，否则失败。

## specialize
定义于：`Lean.Parser.Tactic.specialize`

策略 `specialize h a₁ ... aₙ` 作用于局部假设 `h`。该假设的前提（无论是全称量化还是非依赖蕴含）通过具体项 `a₁ ... aₙ` 实例化。该策略添加一个同名新假设 `h := h a₁ ... aₙ`，并尝试清除之前的假设。

## specialize_all
定义于：`Mathlib.Tactic.TautoSet.specialize_all`

`specialize_all x` 对所有假设 `h` 运行 `specialize h x`，只要该策略成功。

## split
定义于：`Lean.Parser.Tactic.split`

`split` 策略用于将嵌套的 if-then-else 和 `match` 表达式拆分为单独的情况。对于有 `n` 个情况的 `match` 表达式，`split` 最多生成 `n` 个子目标。

例如，给定 `n : Nat` 和目标 `if n = 0 then Q else R`，`split` 将生成一个具有假设 `n = 0` 和目标 `Q` 的子目标，以及第二个具有假设 `¬n = 0` 和目标 `R` 的子目标。注意引入的假设未命名，通常使用 `case` 或 `next` 策略重命名。

- `split` 将拆分目标（主目标）。
- `split at h` 将拆分假设 `h`。

## split_ands
定义于：`Batteries.Tactic.tacticSplit_ands`

`split_ands` 应用 `And.intro` 直到不再进展。

## split_ifs
定义于：`Mathlib.Tactic.splitIfs`

将所有 if-then-else 表达式拆分为多个目标。给定形式为 `g (if p then x else y)` 的目标，`split_ifs` 将生成两个目标：`p ⊢ g x` 和 `¬p ⊢ g y`。若存在多个 ite 表达式，`split_ifs` 将拆分所有，从顶层开始，其条件不包含其他 ite 表达式。`split_ifs at *` 拆分所有假设中的 ite 表达式及目标。`split_ifs with h₁ h₂ h₃` 覆盖默认假设名称。

## squeeze_scope
定义于：`Batteries.Tactic.squeezeScope`

`squeeze_scope` 策略允许聚合来自同一语法但在不同执行分支的多个 `simp` 调用，例如 `cases x <;> simp`。报告的 `simp` 调用涵盖该语法使用的所有 simp 引理。

```lean
@[simp] def bar (z : Nat) := 1 + z
@[simp] def baz (z : Nat) := 1 + z

@[simp] def foo : Nat → Nat → Nat
  | 0, z => bar z
  | _+1, z => baz z

example : foo x y = 1 + y := by
  cases x <;> simp? -- 两次输出：
  -- "Try this: simp only [foo, bar]"
  -- "Try this: simp only [foo, baz]"

example : foo x y = 1 + y := by
  squeeze_scope
    cases x <;> simp -- 仅一次输出："Try this: simp only [foo, baz, bar]"
```

## stop
定义于：`Lean.Parser.Tactic.tacticStop_`

`stop` 是用于“丢弃”剩余证明的辅助策略：定义为 `repeat sorry`。在处理复杂证明的中间部分时非常有用，比注释剩余证明更整洁。

## subsingleton
定义于：`Mathlib.Tactic.subsingletonStx`

`subsingleton` 策略尝试使用所涉及类型为 **子单一类型**（恰好有零或一个项的类型）的事实来证明形式为 `x = y` 或 `HEq x y` 的目标。近似地说，它执行 `apply Subsingleton.elim`。作为优化，`subsingleton` 首先运行 `intros` 策略。

- 若目标是等式，则要么关闭目标，要么失败。
- `subsingleton [inst1, inst2, ...]` 可用于向局部上下文添加额外的 `Subsingleton` 实例。这比 `have := inst1; have := inst2; ...; subsingleton` 更灵活，因为该策略不要求所有占位符都被解决。

`subsingleton` 策略可应用的技术：
- 证明无关性
- 异质证明无关性（通过 `proof_irrel_heq`）
- 使用 `Subsingleton`（通过 `Subsingleton.elim`）
- 若 `BEq` 实例均为合法，则证明它们相等（通过 `lawful_beq_subsingleton`）

### 特性

该策略谨慎避免意外将 `Sort _` 特化为 `Prop`，防止 `apply Subsingleton.elim` 的以下意外行为：

```lean
example (α : Sort _) (x y : α) : x = y := by apply Subsingleton.elim
```
此 `example` 通过的原因在于应用了 `∀ (p : Prop), Subsingleton p` 实例，将 `Sort _` 的宇宙级别元变量特化为 `0`。

## subst
定义于：`Lean.Parser.Tactic.subst`

`subst x...` 在目标中用 `e` 替换每个 `x`，前提是有类型为 `x = e` 或 `e = x` 的假设。若 `x` 本身是类型为 `y = e` 或 `e = y` 的假设，则替换 `y`。

## subst_eqs
定义于：`Lean.Parser.Tactic.substEqs`

`subst_eq` 根据上下文中的等式证明假设反复替换，将等式的左侧替换为右侧，直到无法进一步进展。

## subst_hom_lift
定义于：`CategoryTheory.tacticSubst_hom_lift___`

`subst_hom_lift p f φ` 尝试通过使用 `p.IsHomLift f φ` 将 `f` 替换为 `p(φ)`。

## subst_vars
定义于：`Lean.Parser.Tactic.substVars`

对形式为 `h : x = t` 或 `h : t = x` 的所有假设应用 `subst`。

## substs
定义于：`Mathlib.Tactic.Substs.substs`

从左到右对所有给定假设应用 `subst` 策略。

## success_if_fail_with_msg
定义于：`Mathlib.Tactic.successIfFailWithMsg`

`success_if_fail_with_msg msg tacs` 运行 `tacs` 且仅在其因消息 `msg` 失败时成功。

`msg` 可以是任何评估为显式 `String` 的项。

## suffices
定义于：`Lean.Parser.Tactic.tacticSuffices_`

给定主目标 `ctx ⊢ t`，`suffices h : t' from e` 将主目标替换为 `ctx ⊢ t'`，`e` 必须在上下文 `ctx, h : t'` 中具有类型 `t`。

变体 `suffices h : t' by tac` 是 `suffices h : t' from by tac` 的简写。若省略 `h :`，则使用名称 `this`。

## suffices
定义于：`Mathlib.Tactic.tacticSuffices_`

## suggest_premises
定义于：`Lean.Parser.Tactic.suggestPremises`

`#suggest_premises` 将建议当前目标的前提，使用当前注册的前提选择器。

建议按置信度从高到低排序。

## swap
定义于：`Batteries.Tactic.tacticSwap`

`swap` 是 `pick_goal 2` 的快捷方式，交换第一个和第二个目标。

## swap_var
定义于：`Mathlib.Tactic.«tacticSwap_var__,,»`

`swap_var swap_rule₁, swap_rule₂, ⋯` 依次应用 `swap_rule₁` 然后 `swap_rule₂` 然后 `⋯`。

*交换规则* 的形式为 `x y` 或 `x ↔ y`，“应用”它意味着在所有假设和目标上将变量名 `x` 和 `y` 互换。

```lean
example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩
```

## symm
定义于：`Lean.Parser.Tactic.symm`

* `symm` 应用于目标形式为 `t ~ u` 的情况，其中 `~` 是一个对称关系，即具有标记为属性 [symm] 的对称性引理的关系。它将目标替换为 `u ~ t`。
* `symm at h` 将重写假设 `h : t ~ u` 为 `h : u ~ t`。

## symm_saturate
定义于：`Lean.Parser.Tactic.symmSaturate`

对于每个假设 `h : a ~ b`（其中存在可用的 `@[symm]` 引理），添加一个假设 `h_symm : b ~ a`。

## tauto
定义于：`Mathlib.Tactic.Tauto.tauto`

`tauto` 分解形如 `_ ∧ _`、`_ ∨ _`、`_ ↔ _` 和 `∃ _, _` 的假设，并将形如 `_ ∧ _`、`_ ↔ _` 或 `∃ _, _` 的目标拆分，直到可以通过 `reflexivity` 或 `solve_by_elim` 完成。这是一个终结策略：它要么闭合目标，要么抛出错误。

Lean 3 版本的此策略默认尽量避免使用经典推理。而 Lean 4 版本不再进行此类尝试。`itauto` 策略专为此目的设计。

## tauto_set
定义于：`Mathlib.Tactic.TautoSet.tacticTauto_set`

`tauto_set` 尝试证明涉及形如 `X ⊆ Y` 或 `X = Y` 的假设和目标的同义反复，其中 `X`、`Y` 是使用 ∪、∩、\ 和 ᶜ 从有限多个 `Set α` 类型的变量构建的表达式。它还会展开形如 `Disjoint A B` 和 `symmDiff A B` 的表达式。

示例：
```lean
example {α} (A B C D : Set α) (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by
  tauto_set

example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by
  tauto_set
```

## tfae_finish
定义于：`Mathlib.Tactic.TFAE.tfaeFinish`

`tfae_finish` 用于闭合形如 `TFAE [P₁, P₂, ...]` 的目标，一旦向局部上下文中引入了足够多的形如 `Pᵢ → Pⱼ` 或 `Pᵢ ↔ Pⱼ` 的假设。

`tfae_have` 可方便地引入这些假设；参见 `tfae_have`。

示例：
```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- 证明 P → Q -/
  tfae_have 2 → 1 := sorry /- 证明 Q → P -/
  tfae_have 2 ↔ 3 := sorry /- 证明 Q ↔ R -/
  tfae_finish
```

## tfae_have
定义于：`Mathlib.Tactic.TFAE.tfaeHave`

`tfae_have` 引入用于证明形如 `TFAE [P₁, P₂, ...]` 目标的假设。具体来说，`tfae_have i <箭头> j := ...` 向局部上下文中引入一个类型为 `Pᵢ <箭头> Pⱼ` 的假设，其中 `<箭头>` 可以是 `→`、`←` 或 `↔`。注意 `i` 和 `j` 是自然数索引（从 1 开始），用于指定目标中出现的命题 `P₁, P₂, ...`。

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  ...
```
现在上下文中包含 `tfae_1_to_3 : P → R`。

一旦通过 `tfae_have` 引入了足够的假设，即可使用 `tfae_finish` 闭合目标。例如：

```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- 证明 P → Q -/
  tfae_have 2 → 1 := sorry /- 证明 Q → P -/
  tfae_have 2 ↔ 3 := sorry /- 证明 Q ↔ R -/
  tfae_finish
```

`tfae_have` 支持 `have` 的所有功能，包括命名、匹配、解构和目标创建。以下示例展示了这些功能：

```lean
example : TFAE [P, Q] := by
  -- 断言 `tfae_1_to_2 : P → Q`：
  tfae_have 1 → 2 := sorry

  -- 断言 `hpq : P → Q`：
  tfae_have hpq : 1 → 2 := sorry

  -- 匹配 `p : P` 并通过 `f p` 证明 `Q`：
  tfae_have 1 → 2
  | p => f p

  -- 断言 `pq : P → Q`，`qp : Q → P`：
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry

  -- 断言 `h : P → Q`；`?a` 是一个新目标：
  tfae_have h : 1 → 2 := f ?a
  ...
```

## tfae_have
定义于：`Mathlib.Tactic.TFAE.tfaeHave'`

“目标式” `tfae_have` 语法已弃用。现在，`tfae_have ...` 后应跟随 `:= ...`；有关新行为，请参见下文。可通过 `set_option Mathlib.Tactic.TFAE.useDeprecated true` 关闭此警告。

***

`tfae_have` 引入用于证明形如 `TFAE [P₁, P₂, ...]` 目标的假设。具体来说，`tfae_have i <箭头> j := ...` 向局部上下文中引入一个类型为 `Pᵢ <箭头> Pⱼ` 的假设，其中 `<箭头>` 可以是 `→`、`←` 或 `↔`。注意 `i` 和 `j` 是自然数索引（从 1 开始），用于指定目标中出现的命题 `P₁, P₂, ...`。

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  ...
```
现在上下文中包含 `tfae_1_to_3 : P → R`。

一旦通过 `tfae_have` 引入了足够的假设，即可使用 `tfae_finish` 闭合目标。例如：

```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- 证明 P → Q -/
  tfae_have 2 → 1 := sorry /- 证明 Q → P -/
  tfae_have 2 ↔ 3 := sorry /- 证明 Q ↔ R -/
  tfae_finish
```

`tfae_have` 支持 `have` 的所有功能，包括命名、匹配、解构和目标创建。以下示例展示了这些功能：

```lean
example : TFAE [P, Q] := by
  -- 断言 `tfae_1_to_2 : P → Q`：
  tfae_have 1 → 2 := sorry

  -- 断言 `hpq : P → Q`：
  tfae_have hpq : 1 → 2 := sorry

  -- 匹配 `p : P` 并通过 `f p` 证明 `Q`：
  tfae_have 1 → 2
  | p => f p

  -- 断言 `pq : P → Q`，`qp : Q → P`：
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry

  -- 断言 `h : P → Q`；`?a` 是一个新目标：
  tfae_have h : 1 → 2 := f ?a
  ...
```

## toFinite_tac
定义于：`Set.tacticToFinite_tac`

一种（用于默认参数中的）策略，应用 `Set.toFinite` 来合成 `Set.Finite` 项。

## to_encard_tac
定义于：`Set.tacticTo_encard_tac`

一种有助于将 `encard` 的证明转移到其对应的 `card` 陈述中的策略

## trace
定义于：`Lean.Parser.Tactic.trace`

将术语求值为字符串（可能时），并作为跟踪消息打印。

## trace
定义于：`Lean.Parser.Tactic.traceMessage`

`trace msg` 在信息视图中显示 `msg`。

## trace_state
定义于：`Lean.Parser.Tactic.traceState`

`trace_state` 在信息视图中显示当前状态。

## trans
定义于：`Batteries.Tactic.tacticTrans___`

`trans` 应用于目标形式为 `t ~ u` 的情况，其中 `~` 是一个传递关系，即具有标记为属性 [trans] 的传递性引理的关系。

* `trans s` 将目标替换为两个子目标 `t ~ s` 和 `s ~ u`。
* 若省略 `s`，则使用一个元变量代替。

此外，`trans` 也应用于目标形式为 `t → u` 的情况，此时它将目标替换为 `t → s` 和 `s → u`。

## transitivity
定义于：`Batteries.Tactic.tacticTransitivity___`

`trans` 策略的同义词。

## triv
定义于：`Batteries.Tactic.triv`

已弃用的 `trivial` 变体。

## trivial
定义于：`Lean.Parser.Tactic.tacticTrivial`

`trivial` 尝试不同的简单策略（如 `rfl`、`contradiction` 等）以闭合当前目标。您可以使用 `macro_rules` 命令扩展所使用的策略集合。例如：
```lean
macro_rules | `(tactic| trivial) => `(tactic| simp)
```

## try
定义于：`Lean.Parser.Tactic.tacticTry_`

`try tac` 运行 `tac` 并在 `tac` 失败时仍视为成功。

## try?
定义于：`Lean.Parser.Tactic.tryTrace`


## try_suggestions
定义于：`Lean.Parser.Tactic.tryResult`

用于在 `try?` 中实现 `evalSuggest` 的内部辅助策略

## try_this
定义于：`Mathlib.Tactic.tacticTry_this__`

生成文本 `Try this: <tac>` 并执行给定的策略。

## type_check
定义于：`tacticType_check_`

对给定表达式进行类型检查，并追踪其类型。

## unfold
定义于：`Lean.Parser.Tactic.unfold`

* `unfold id` 展开目标中定义 `id` 的所有出现。
* `unfold id1 id2 ...` 等效于 `unfold id1; unfold id2; ...`。
* `unfold id at h` 在假设 `h` 处展开。

定义可以是全局或局部定义。

对于非递归的全局定义，此策略与 `delta` 相同。对于递归的全局定义，它使用由用户给出的递归定义生成的“展开引理” `id.eq_def` 来展开。仅执行一级展开，与 `simp only [id]` 不同，后者递归展开定义 `id`。

## unfold?
定义于：`Mathlib.Tactic.InteractiveUnfold.tacticUnfold?`

将选定的表达式替换为定义展开。
- 每次展开后，我们应用`whnfCore`来简化表达式。
- 显式的自然数表达式会被求值。
- 标记有`@[default_instance]`的类投影实例的展开不会被显示。这对于如`+`这样的符号类型类很重要：我们不希望将`Add.add a b`作为`a + b`的展开建议。类似地，`OfNat n : Nat`展开为`n : Nat`。

使用`unfold?`时，按住Shift键点击策略状态中的表达式。这将为选定的表达式提供重写建议列表。点击建议将用执行该重写的策略替换`unfold?`。

## unfold_let
定义于：`Mathlib.Tactic.unfoldLetStx`

此策略已被`unfold`策略取代。

`unfold_let x y z at loc`在给定位置展开局部定义`x`、`y`和`z`，这被称为“zeta约简”。此策略也可作为`conv`模式策略使用。

若未指定局部定义，则展开所有局部定义。此变体也可作为`conv`模式策略`zeta`使用。

## unfold_projs
定义于：`Mathlib.Tactic.unfoldProjsStx`

`unfold_projs at loc`在给定位置展开类实例的投影。此策略也可作为`conv`模式策略使用。

## unhygienic
定义于：`Lean.Parser.Tactic.tacticUnhygienic_`

`unhygienic tacs`运行`tacs`时禁用名称卫生机制。这意味着通常会生成不可访问名称的策略将生成常规变量。**警告**：策略可能随时更改其变量命名策略，因此依赖自动生成名称的代码较为脆弱。用户应尽可能避免使用`unhygienic`。

```lean
example : ∀ x : Nat, x = x := by unhygienic
  intro            -- x通常会被引入为不可访问
  exact Eq.refl x  -- 引用x
```

## uniqueDiffWithinAt_Ici_Iic_univ
定义于：`intervalIntegral.tacticUniqueDiffWithinAt_Ici_Iic_univ`

一个辅助策略，用于关闭目标`UniqueDiffWithinAt ℝ s a`，其中`s ∈ {Iic a, Ici a, univ}`。

## unit_interval
定义于：`Tactic.Interactive.tacticUnit_interval`

一个解决`0 ≤ ↑x`、`0 ≤ 1 - ↑x`、`↑x ≤ 1`和`1 - ↑x ≤ 1`对于`x : I`的策略。

## unreachable!
定义于：`Batteries.Tactic.unreachable`

此策略在运行时（编译时）引发恐慌。（这与`exact unreachable!`不同，后者插入在运行时恐慌的代码。）

它用于测试中，以断言某个策略永远不会被执行，否则这是不寻常的做法（而`unreachableTactic`检查器会对此发出警告）。

`unreachableTactic`检查器对`unreachable!`的使用有特殊例外。

```lean
example : True := by trivial <;> unreachable!
```

## use
定义于：`Mathlib.Tactic.useSyntax`

`use e₁, e₂, ⋯`类似于`exists`，但与`exists`不同，它等效于应用策略`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩`，带有任意数量的占位符（而非仅一个），然后尝试用可配置的解除器关闭与占位符关联的目标（而非仅`try trivial`）。

示例：

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯`类似，但它会在所有地方应用构造函数，而不仅仅针对构造器最后一个参数对应的目标。这产生了一种效果，即嵌套的构造函数被展开，提供的值被用于构造函数树的叶子和节点。使用`use!`可以逐个输入每个`42`：

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

第二行利用了`use!`在应用构造函数前尝试用参数进行精炼的事实。还需注意，`use`/`use!`默认使用称为`use_discharger`的策略来关闭目标，因此在此示例中`use! 42`将关闭目标，因为`use_discharger`应用`rfl`，从而解决另一个`Nat`元变量。

这些策略接受一个可选的解除器来处理剩余的显式`Prop`构造器参数。默认情况下为`use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`。要关闭解除器并保留所有目标，使用`(discharger := skip)`。要允许“重度反身”，使用`(discharger := try use_discharger)`。

## use!
定义于：`Mathlib.Tactic.«tacticUse!___,,»`

`use e₁, e₂, ⋯`类似于`exists`，但与`exists`不同，它等效于应用策略`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩`，带有任意数量的占位符（而非仅一个），然后尝试用可配置的解除器关闭与占位符关联的目标（而非仅`try trivial`）。

示例：

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯`类似，但它会在所有地方应用构造函数，而不仅仅针对构造器最后一个参数对应的目标。这产生了一种效果，即嵌套的构造函数被展开，提供的值被用于构造函数树的叶子和节点。使用`use!`可以逐个输入每个`42`：

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

第二行利用了`use!`在应用构造函数前尝试用参数进行精炼的事实。还需注意，`use`/`use!`默认使用称为`use_discharger`的策略来关闭目标，因此在此示例中`use! 42`将关闭目标，因为`use_discharger`应用`rfl`，从而解决另一个`Nat`元变量。

这些策略接受一个可选的解除器来处理剩余的显式`Prop`构造器参数。默认情况下为`use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`。要关闭解除器并保留所有目标，使用`(discharger := skip)`。要允许“重度反身”，使用`(discharger := try use_discharger)`。

## use_discharger
定义于：`Mathlib.Tactic.tacticUse_discharger`

用于`use`和`use!`策略的默认解除器。此策略类似于`trivial`，但不执行`contradiction`或`decide`等操作。

## use_finite_instance
定义于：`tacticUse_finite_instance`


## valid
定义于：`CategoryTheory.ComposableArrows.tacticValid`

`omega`的包装器，前置一些快速且有用的尝试

## volume_tac
定义于：`MeasureTheory.tacticVolume_tac`

策略`exact volume`，用于可选（`autoParam`）参数。

## wait_for_unblock_async
定义于：`Lean.Server.Test.Cancel.tacticWait_for_unblock_async`

生成一个`logSnapshotTask`，等待`unblock`被调用，预计在后续不使此策略失效的文档版本中发生。如果在取消令牌设置前未解除阻塞（即如果策略在之后被失效），则会抱怨。

## whisker_simps
定义于：`Mathlib.Tactic.BicategoryCoherence.whisker_simps`

用于将2-态重写为正常形式的Simp引理。

## whnf
定义于：`Mathlib.Tactic.tacticWhnf__`

`whnf at loc`将给定位置置于弱头正规形式。此策略也可作为`conv`模式策略使用。

弱头正规形式是指最外层表达式已完全约简，但可能包含未约简的子表达式。

## with_panel_widgets
定义于：`ProofWidgets.withPanelWidgetsTacticStx`

在嵌套的策略脚本中显示选定的面板小部件。例如，假设我们编写了一个`GeometryDisplay`组件，

```lean
by with_panel_widgets [GeometryDisplay]
  simp
  rfl
```

将在整个证明过程中显示几何显示与通常的策略状态。

## with_reducible
定义于：`Lean.Parser.Tactic.withReducible`

`with_reducible tacs` 使用可约简的透明度设置执行 `tacs`。在此设置下，仅展开被标记为 `[reducible]` 的定义。

## with_reducible_and_instances
定义于：`Lean.Parser.Tactic.withReducibleAndInstances`

`with_reducible_and_instances tacs` 使用 `.instances` 透明度设置执行 `tacs`。在此设置下，展开被标记为 `[reducible]` 的定义或类型类实例。

## with_unfolding_all
定义于：`Lean.Parser.Tactic.withUnfoldingAll`

`with_unfolding_all tacs` 使用 `.all` 透明度设置执行 `tacs`。在此设置下，展开所有非不透明的定义。

## witt_truncateFun_tac
定义于：`witt_truncateFun_tac`

用于证明 `truncateFun` 尊重环操作的宏策略。

## wlog
定义于：`Mathlib.Tactic.wlog`

`wlog h : P` 将在主目标中添加假设 `h : P`，并添加一个需证明当 `h : ¬ P` 时的情况可简化为 `P` 成立的边目标（通常通过对称性）。

边目标将位于目标栈顶部。在此边目标中，将有两个额外假设：
- `h : ¬ P`：假设 `P` 不成立
- `this`：表示在原上下文中 `P` 足以证明目标。默认使用名称 `this`，但可通过添加 `with H` 指定名称：`wlog h : P with H`。

通常，结合 `wlog h : P generalizing x y` 使用以在创建新目标前恢复上下文的某些部分，便于 `wlog` 声明 `this` 以不同顺序应用于 `x` 和 `y`（利用对称性，典型用例）。

默认恢复整个上下文。

## zify
定义于：`Mathlib.Tactic.Zify.zify`

`zify` 策略用于将命题从 `Nat` 转换到 `Int`。由于 `Int` 具有良好减法特性，此举常有益。
```lean
example (a b c x y z : Nat) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
`zify` 可接受额外引理以辅助化简。这在存在自然数减法时尤为有用：传递 `≤` 参数将使 `push_cast` 完成更多工作。
```lean
example (a b c : Nat) (h : a - b < c) (hab : b ≤ a) : false := by
  zify [hab] at h
  /- h : ↑a - ↑b < ↑c -/
```
`zify` 利用 `@[zify_simps]` 属性转移命题，并通过 `push_cast` 策略简化 `Int` 表达式。某种意义上，`zify` 与 `lift` 策略互为对偶。`lift (z : Int) to Nat` 将整数 `z`（超类型）的类型更改为 `Nat`（子类型），需证明 `z ≥ 0`；关于 `z` 的命题仍处于 `Int` 层面。`zify` 则将关于 `Nat`（子类型）的命题转换为关于 `Int`（超类型）的命题，且不改变任何变量的类型。

语法 ... [Lean.Parser.Tactic.nestedTactic]

语法 ... [Lean.Parser.Tactic.unknown]

语法 ... [Lean.cdot]
`· tac` 聚焦主目标并尝试用 `tac` 解决，否则失败。