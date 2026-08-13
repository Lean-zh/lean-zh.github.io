# 使用 `mvcgen` 验证命令式程序

- 原文：[官方教程页面](https://lean-lang.org/doc/tutorials/4.34.0-rc1/mvcgen/)；[Verso 源文件](https://github.com/leanprover/reference-manual/blob/v4.34.0-rc1/Tutorial/VCGen.lean)
- 作者：Sebastian Graf
- 译者：Lean 中文社区
- 对应版本：Lean `v4.34.0-rc1`
- 上游版权：Copyright © 2025 Lean FRO LLC，以 [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0) 发布
- 配套源码：[下载完整工程压缩包](../assets/files/mvcgen/mvcgen-4.34.0-rc1.zip)；[直接查看 `MVCGenTutorial.lean`](../assets/files/mvcgen/MVCGenTutorial.lean)

本教程自上而下介绍 `mvcgen` 的主要概念，展示怎样方便而组合式地证明单子程序的性质。完整的策略说明见 Lean 4 参考手册的 [`mvcgen` 策略参考](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)。运行示例需要导入 `Std.Tactic.Do` 并打开 `Std.Do`。配套源码还导入了示例所用的哈希表和哈希集合：

```lean
import Std.Data.HashMap
import Std.Data.HashSet

import Std.Tactic.Do

set_option mvcgen.warning false

open Std.Do
```

## 前置条件与后置条件

程序规格的一种写法是给出[前置条件](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)，记作 $P$，要求程序 $\mathit{prog}$ 的调用方保证它成立；再给出后置条件 $Q$，要求 $\mathit{prog}$ 保证它成立。如果在 $P$ 成立时运行程序总会得到满足 $Q$ 的结果，那么 $\mathit{prog}$ 满足这份规格。

一般来说，为了保证同一个后置条件，可能有许多不同的前置条件。毕竟，只要把前置条件 $P_1$ 换成 $P_1 \wedge P_2$，就能生成新的前置条件。程序 $\mathit{prog}$ 对后置条件 $Q$ 的[最弱前置条件](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen) $\textbf{wp}⟦\mathit{prog}⟧(Q)$ 满足两项要求：$\mathit{prog}$ 在该条件下保证 $Q$，而且任何能保证 $Q$ 的其他前置条件都蕴含它。

证明程序结果性质的一种方法，是先找出保证该结果的最弱前置条件，再证明这个最弱前置条件就是 `True`。这说明后置条件无条件成立。

## 循环与不变量

第一个 `mvcgen` 示例用[局部可变状态](https://lean-lang.org/doc/reference/4.34.0-rc1/Functors___-Monads-and--do--Notation/Syntax/#let-mut)和 `for` 循环计算数组元素之和：

```lean
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out
```

如果 `mySum` 正确，它就应当等于 `Array.sum`。`mySum` 中的 `do` 只是内部实现细节，函数签名没有提到任何单子。因此，证明先用引理 `Id.of_wp_run_eq` 把目标改写成适合 `mvcgen` 处理的形式。该引理说明：若 `Id` 单子中的计算正常终止，想证明其运行结果的性质，只需证明保证该性质的最弱前置条件为真。`Id` 计算从不抛出异常。随后，`mvcgen` 把最弱前置条件形式的目标替换为一组[验证条件](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)。

`mvcgen` 大体上是自动的，但循环不变量必须由用户给出。[循环不变量](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)是循环体既可以假设、又必须保证的命题。只要循环开始时它成立，循环结束时它也成立。

```lean
theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- 聚焦含有 `do` 块的程序部分，即 `Id.run ...`
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- 分解为验证条件
  mvcgen
  -- 指定整个循环期间都应成立的不变量
  -- * `out` 指 `let mut` 变量的当前值
  -- * `xs` 是 `List.Cursor`，表示一个被拆成 `xs.prefix` 与
  --   `xs.suffix` 的列表，用来记录循环已经执行到哪里
  -- 不变量断言 `out` 保存前缀之和
  -- 记法 ⌜p⌝ 把 `p : Prop` 嵌入断言语言
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- 指定不变量后，可以“离开证明模式”来进一步简化目标
  -- `mleave` 就是在稳定的 simp 子集上执行 `simp only [...] at *`
  all_goals mleave
  -- 证明每一步循环都保持不变量
  case vc1 ih =>
    -- 此处目标提到 `pref`，它绑定传给不变量的游标的 `prefix` 字段
    -- 拆开这个依赖类型游标后，`grind` 更容易处理目标
    grind
  -- 证明不变量在循环开始时成立
  case vc2 =>
    grind
  -- 证明循环结束时的不变量蕴含所需性质
  case vc3 h =>
    grind
```

这些分支标签其实都是完整标签的唯一前缀。引用分支时只应写这个前缀，后缀只是提示该验证条件来自哪里。例如：

- `vc1.step` 表示这个验证条件证明循环的归纳步骤。
- `vc2.a.pre` 用来证明目标的假设蕴含某个规格的前置条件，这里是 `forIn` 的规格。
- `vc3.a.post.success` 用来证明某个规格的后置条件蕴含所需性质，这里仍是 `forIn` 的规格。

给出循环不变量后，证明可以缩成 `all_goals mleave; grind`。其中 `mleave` 离开有状态证明模式并清理证明状态。

```lean
theorem mySum_correct_short (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  all_goals mleave; grind
```

这种写法很常见，因此 `mvcgen` 提供了专用语法：

```lean
theorem mySum_correct_shorter (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  with grind
```

`mvcgen invariants ... with ...` 是上面这串策略的缩写：`mvcgen; case inv1 => ...; all_goals mleave; grind`。下文都采用这种形式。

可以把 `mySum_correct_shorter` 与传统的正确性证明比较：

```lean
theorem mySum_correct_vanilla (l : Array Nat) : mySum l = l.sum := by
  -- 把数组变成列表
  cases l with | mk l =>
  -- 展开 `mySum`，并把 `forIn` 改写为 `foldl`
  simp [mySum]
  -- 推广归纳假设
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- 交给 `grind`
  induction l with grind
```

这个证明与使用 `mvcgen` 的 `mySum_correct_shorter` 一样简短。不过，传统方法依赖程序的几个重要性质：

- `for` 循环没有用 `break` 或提前 `return`，否则不能把 `forIn` 改写成 `foldl`。
- 循环体 `(· + ·)` 足够小，可以在证明中重复写出。
- 循环体没有在底层单子中执行任何作用，也就是说，作用只来自 `do` 记法引入的结构。`Id` 单子没有作用，它的全部计算都是纯的。虽然仍可把 `forIn` 改写成 `foldlM`，但 `grind` 很难直接推理单子式循环体。

后续各节用更多示例介绍 `mvcgen` 及其支持库，也会看到传统证明在什么地方变得困难。常见原因有两类：

- `do` 块使用 `for` 循环、`break` 和提前 `return` 等控制流构造。
- 程序使用非 `Id` 单子中的作用，隐式单子上下文里的状态或异常会变化，循环不变量必须反映这些变化。

处理这些情况时，`mvcgen` 所需的额外工作仍然有限。

## 控制流

下面的示例把 `for` 循环与提前返回组合起来。`List.Nodup` 断言给定列表没有重复元素，函数 `nodup` 判定该命题：

```lean
def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true
```

如果 `nodup` 对每个满足 `List.Nodup` 的列表返回 `true`，并对每个不满足它的列表返回 `false`，那么该函数就是正确的。与 `mySum` 一样，`do` 记法和 `Id` 单子只是 `nodup` 的内部实现细节。因此，证明先用 `Id.of_wp_run_eq` 把证明状态变成 `mvcgen` 可以处理的形式：

```lean
theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun xs seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  with grind
```

这个证明和最初的 `mySum` 示例一样简短，因为具体命题仍交给 `grind` 及其已有的 `List.Nodup` 自动化处理。两者唯一的区别是循环不变量。

循环中有[提前返回](https://lean-lang.org/doc/reference/4.34.0-rc1/Functors___-Monads-and--do--Notation/Syntax/#early-return)，所以这里用辅助函数 `Invariant.withEarlyReturnNewDo` 构造不变量。该函数支持[可扩展的 `do` 记法精译器（elaborator）](https://lean-lang.org/doc/reference/4.34.0-rc1/Functors___-Monads-and--do--Notation/Syntax/)，并允许把不变量分成三部分：

- `onReturn ret seen` 在循环通过提前返回值 `ret` 退出后成立。对 `nodup` 而言，唯一可能提前返回的值是 `false`，此时 `nodup` 已判定列表中确有重复元素。
- `onContinue xs seen` 是通常的归纳步骤，证明每次迭代都保持不变量。游标 `xs` 捕获迭代状态。这里断言集合 `seen` 含有之前各轮迭代见过的所有元素，而且到目前为止没有重复元素。
- `onExcept` 必须在循环抛出异常时成立。`Id` 中没有异常，因此不指定它并采用默认值。后文会讨论异常。

不必背下指定不变量的完整语法。`mvcgen invariants?` 会建议一个初始不变量：

```lean
example (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants? <;> sorry
```

策略给出的起点如下：

```lean
Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => ⌜(r = true ↔ l.Nodup) ∧ l.Nodup⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = ∅ ∨ xs.suffix = [] ∧ l.Nodup⌝)
```

这个起点不足以让证明成功。要是系统能直接推断出不变量，也就不必要求用户指定了。不过，它会提醒用户当前单子中的断言应采用什么语法。

上面的 `invariants?` 调用是故意保留的待完成示例，官方配套源码中也含有这里的 `sorry`。它用于展示策略建议，不是一个零 `sorry` 的成品证明。

再看一个不使用 `mvcgen` 的直接证明。它刻意压缩得很短：

```lean
theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]
```

有几点值得注意：

- 它甚至比 `mvcgen` 版本更短。
- 用 `generalize` 推广累加器时，证明依赖代码里恰好只有一个可推广的 `(∅ : Std.HashSet Int)`。如果不满足这个条件，就得把部分程序复制进证明。对较大的函数，这种做法不可取。
- 给出合适引理后，`grind` 会沿函数的控制流拆分，并推理 `Id`。这对 `Id.run_pure` 和 `Id.run_bind` 有效，但例如 `Id.run_seq` 就不行，因为该引理不能用于 [E-matching](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#grind)。一旦 `grind` 失败，就只能手工拆分控制流并推理单子，直到 `grind` 能继续接手。

证明中避免复制定义控制流的通常办法，是使用 `fun_cases` 或 `fun_induction`。遗憾的是，`fun_cases` 无法帮助处理 `forIn` 应用内部的控制流。`mvcgen` 则自带许多 `forIn` 实现的支持，也能通过 `@[spec]` 标注轻松扩展到自定义 `forIn` 实现。更重要的是，由 `mvcgen` 驱动的证明不需要复制原程序的任何部分。

## 用 Hoare 三元组组合式推理带作用程序

前面的示例都推理形如 `Id.run do <prog>` 的函数，以便在 `<prog>` 中使用局部可变状态和提前返回。实际程序则常用 `do` 记法和单子 `M`，把状态与失败条件隐藏成隐式的“作用”。这类函数通常不写 `M.run`，而是返回 `M α`，并与具有同类返回值的其他函数组合。换句话说，单子是函数接口的一部分，不只是实现细节。

下面是有状态函数 `mkFresh`。它返回自动递增的计数器值：

```lean
structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList
```

`mkFreshN n` 返回 `n` 个“新鲜”数字，并通过 `mkFresh` 修改内部的 `Supply` 状态。这里的“新鲜”是指先前生成的所有数字都不同于下一个生成的数字。可以用 `List.Nodup` 表述并证明正确性定理 `mkFreshN_correct`：返回的数字列表不含重复元素。此处 `StateM.of_wp_run'_eq` 的作用与前面示例中的 `Id.of_wp_run_eq` 相同。

```lean
theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- 聚焦 `(mkFreshN n).run' s`
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- 证明单子程序 `mkFresh n` 的性质
  -- 把 `mkFreshN` 和 `mkFresh` 传给 `mvcgen`，会将它们加入内部
  -- `simp` 集合，使 `mvcgen` 展开这些定义
  mvcgen [mkFreshN, mkFresh]
  invariants
  -- 不变量：计数器大于每个已累积数字，且这些数字彼此不同
  -- 不变量可通过函数参数 `state : Supply` 引用状态
  -- 下一个要累积的数字就是计数器，所以它不同于所有已累积数字
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```

### Hoare 三元组

[Hoare 三元组](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)由前置条件、语句和后置条件组成。它断言：若前置条件成立，则运行语句后，后置条件成立。Lean 语法写作 `⦃ P ⦄ prog ⦃ Q ⦄`，其中 `P` 是前置条件，`prog : m α` 是语句，`Q` 是后置条件。

`P` 和 `Q` 写在由具体单子 `m` 决定的断言语言中。具体来说，该单子的 `WP` 类型类实例规定断言可以用什么方式引用单子状态或它可能抛出的异常。

Hoare 三元组规格具有组合性，因为可以顺序组合语句。给定 `⦃P⦄ stmt1 ⦃Q⦄` 和 `⦃P'⦄ stmt2 ⦃Q'⦄`，如果 `Q` 蕴含 `P'`，就有 `⦃P⦄ (do stmt1; stmt2) ⦃Q'⦄`。普通函数的证明可以使用被调用函数的引理；同样，单子程序的证明可以使用以 Hoare 三元组表述的引理。

把 `mkFreshN_correct` 改写为 Hoare 三元组，可得到一份合适的 `mkFreshN` 规格：

```lean
⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄
```

`⌜·⌝` 记法把命题嵌入单子断言语言，所以 `⌜p⌝` 是对命题 `p` 的断言。前置条件 `⌜True⌝` 断言 `True` 成立，这个平凡前置条件表示规格对调用时的状态没有要求。后置条件则说明结果是不含重复元素的列表。

单步函数 `mkFresh` 的规格还要描述它对单子状态的作用：

```lean
∀ (c : Nat),
⦃fun state => ⌜state.counter = c⌝⦄
mkFresh
⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄
```

使用状态单子时，前置条件可以参数化于运行代码之前的状态值。这里全称量化的 `Nat` 用来关联初始状态与最终状态，前置条件把它连接到初始状态。同样，后置条件也可以接收最终状态作为参数。这个 Hoare 三元组表示：

> 如果 `c` 指 `Supply` 前状态的 `Supply.counter` 字段，那么运行 `mkFresh` 会返回 `c`，并把后状态中的 `Supply.counter` 修改为大于 `c` 的值。

注意，这份规格有意丢失了一些信息。即使 `mkFresh` 把状态增加任意正数，它仍满足该规格。这是合理的，因为规格可以抽象掉无关实现细节，使证明更短，也不易受实现变更影响。

Hoare 三元组定义在有状态谓词逻辑和最弱前置条件语义 `wp⟦prog⟧` 之上，后者把单子程序翻译到该逻辑中。最弱前置条件语义把程序解释为从后置条件到最弱前置条件的映射。按这种解释，程序是[谓词变换器](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)，这也称为谓词变换器语义。Hoare 三元组语法是 `Std.Do.Triple` 的记法：

```lean
-- 这是 Std.Do.Triple 的定义：
def Triple [WP m ps] {α : Type u} (prog : m α)
    (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦prog⟧ Q
```

`WP` 类型类把单子 `m` 映射到它的 `PostShape ps`，而这个 `PostShape` 决定 `Std.Do.Triple` 的确切形状。`StateT`、`ReaderT` 和 `ExceptT` 等标准单子变换器都有规范的 `WP` 实例。例如，`StateT σ` 的 `WP` 实例会给每个 `Assertion` 增加一个 `σ` 参数。有状态蕴含 `⊢ₛ` 会经过这些新增的 `σ` 参数做 eta 展开。对 `StateM` 程序，下列类型在定义上等价于 `Std.Do.Triple`：

```lean
def StateMTriple {α σ : Type u} (prog : StateM σ α)
    (P : σ → ULift Prop) (Q : (α → σ → ULift Prop) × PUnit) : Prop :=
  ∀ s, (P s).down → let (a, s') := prog.run s; (Q.1 a s').down
```

常见的后置条件记法 `⇓ r => ...` 把类型为 `α → Assertion ps` 的断言注入 `PostCond α ps`。这里的 `⇓` 可以像 `fun` 一样读。对 `StateM` 而言，这通过附加空元组 `PUnit.unit` 实现。异常出现后，后置条件的形状会更复杂。

记法 `⌜p⌝` 把纯假设 `p` 嵌入有状态断言。反过来，如果有状态假设 `P` 等价于某个 `⌜p⌝`，就称 `P` 为纯的。纯的有状态假设可以自由移入普通 Lean 上下文，再移回有状态上下文。手工操作可使用 `mpure` 策略。

### 组合规格

像 `mvcgen [mkFreshN, mkFresh]` 那样嵌套展开定义，做法直接而有效，适合小程序。更具组合性的办法，是为每个单子函数分别建立[规格引理](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#mvcgen)。规格引理是一个 Hoare 三元组，在生成验证条件时会被自动使用，以取得 `do` 块中每条语句的前置条件和后置条件。如果系统不能自动证明一条语句的后置条件蕴含下一条语句的前置条件，缺失的推理步骤就会成为验证条件。

规格引理可以作为参数传给 `mvcgen`，也可以用 `@[spec]` 属性注册到全局、`scoped` 或 `local` 规格数据库：

```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- 展开 `mkFresh`，然后交给自动化处理
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- 如果 `mkFresh_spec` 没有用 `@[spec]` 注册，这里应写
  -- `mvcgen [mkFreshN, mkFresh_spec]`
  mvcgen [mkFreshN]
  invariants
  -- 与之前相同
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```

现在只用一次 `mvcgen` 就能证明原来的正确性定理：

```lean
theorem mkFreshN_correct_compositional (n : Nat) :
    ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  mvcgen
```

`mvcgen` 会自动使用规格引理 `mkFreshN_spec`。

### 关于纯前置条件与框架规则的高级说明

本小节稍微偏离主线，初读时可以跳过。

假设有一个受 [`Aeneas`](https://github.com/AeneasVerif/aeneas) 启发的单子式加法函数 `x +? y : M UInt8`。上游草图把它的无溢出条件写成 `h : x.toNat + y.toNat ≤ UInt8.size`：

```lean
axiom M : Type → Type
variable {x y : UInt8} [Monad M] [WP M .pure]
def addQ (x y : UInt8) : M UInt8 := pure (x + y)
local infix:1023 " +? " => addQ
```

这个要求应该写成规格的普通 Lean 假设 `add_spec_hyp`，还是通过 `⌜·⌝` 写成 Hoare 三元组的纯前置条件 `add_spec_pre`？

```lean
theorem add_spec_hyp (x y : UInt8)
    (h : x.toNat + y.toNat ≤ UInt8.size) :
    ⦃⌜True⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := …

theorem add_spec_pre (x y : UInt8) :
    ⦃⌜x.toNat + y.toNat ≤ UInt8.size⌝⦄
    x +? y
    ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := …
```

上面两个定理只是在文档中展示规格形状的草图，其中的 `…` 不是 Lean 代码；它们不属于配套可执行源码。

!!! note "上游边界条件"
    这里原样保留上游的 `≤ UInt8.size`。若要保证 `UInt8` 加法不回绕，边界条件应为 `< UInt8.size`；和恰好等于 `UInt8.size` 时已经溢出。这个边界问题不影响本小节比较“普通 Lean 假设”与“纯前置条件”两种规格写法的目的。

推荐第一种写法，尽管实践中两者应当没有区别。验证条件生成器会把纯假设从有状态上下文移入普通 Lean 上下文，所以第二种形式实际上会变成第一种。这称为对假设做“框定”（framing hypotheses），可参见 `mpure` 与 `mframe` 策略。Lean 上下文中的假设属于有状态逻辑里不可变的“框架”（frame），因为它们与有状态假设不同，在使用后果规则后仍然保留。这是一种类似框架规则的机制。

## 单子变换器与提升

实际程序常用多个[单子变换器](https://lean-lang.org/doc/reference/4.34.0-rc1/Functors___-Monads-and--do--Notation/Varieties-of-Monads/#StateT)构成单子，并频繁把操作从一个单子[提升](https://lean-lang.org/doc/reference/4.34.0-rc1/Functors___-Monads-and--do--Notation/Lifting-Monads/#lifting-monads)到另一个单子。验证这类程序时必须考虑这些结构。下面调整前一个示例来说明。

现在应用中有两个不同的单子，它们都由变换器构成：

```lean
namespace Transformers

abbrev CounterM := StateT Supply (ReaderM String)

abbrev AppM := StateT Bool CounterM
```

`mkFresh` 不再使用 `StateM Supply`，而是使用 `CounterM`：

```lean
def mkFresh : CounterM Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n
```

`mkFreshN` 用 `AppM` 定义，其中包含多个状态和一个读取器作用。定义会把 `mkFresh` 提升到 `AppM`：

```lean
def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← mkFresh
    acc := acc.push n
  return acc.toList
```

基于 `mvcgen` 的证明不需要改动：

```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- 此处 `liftCounterM` 确保展开
  mvcgen [mkFreshN]
  invariants
  · ⇓⟨xs, acc⟩ _ state =>
      ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  with grind

end Transformers
```

`WPMonad` 类型类断言 `wp⟦prog⟧` 与 `pure`、`bind` 相容，因而表现为单子态射。这个证明表面上与只涉及一个单子时差别不大，但在用户看不到的地方，它依赖一连串 `MonadLift` 实例的规格。

## 异常

如果说 `let mut` 是 `do` 语言中与 `StateT` 对应的结构，那么提前 `return` 就与 `ExceptT` 对应。前面已经看到 `mvcgen` 如何处理 `StateT`，本节说明程序逻辑如何支持 `ExceptT`。

异常正是后置条件类型 `PostCond α ps` 不能只是一个成功分支条件 `α → Assertion ps` 的原因。假设后置条件只有这一种形状，而程序 `prog` 在满足前置条件 `P` 的前状态中抛出异常。此时能否证明 `⦃P⦄ prog ⦃⇓ r => Q' r⦄`？请记住，`⇓` 在语法上类似 `fun`。异常路径上根本没有结果 `r`，因此这份证明对 `Q'` 有何意义并不清楚。

传统程序逻辑对不终止的处理给出了两种合理解释：

- [**完全正确性解释**](https://lean-lang.org/doc/reference/4.34.0-rc1/The--mvcgen--tactic/Predicate-Transformers/#--tech-term-total-correctness-interpretation)：`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 断言，只要 `P` 成立，`prog` 就会正常返回，而且返回值满足 `Q'`。
- [**部分正确性解释**](https://lean-lang.org/doc/reference/4.34.0-rc1/The--mvcgen--tactic/Predicate-Transformers/#--tech-term-partial-correctness-interpretation)：`⦃P⦄ prog ⦃⇓? r => Q' r⦄` 断言，只要 `P` 成立，那么如果 `prog` 正常返回，其返回值就满足 `Q'`。

记法 `⇓ r => Q' r` 采用完全正确性解释，`⇓? r => Q' r` 采用部分正确性解释。在当前假设中，`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 不可证明，而 `⦃P⦄ prog ⦃⇓? r => Q' r⦄` 平凡可证。不过，这个二元选择也表明，实际可表达的是一系列处在两端之间的正确性性质。`Std.Do` 的后置条件概念 `PostCond` 支持这一整套选择。

例如，假设新鲜数字的 `Supply` 有上限，并希望在供给耗尽时抛出异常。`mkFreshN` 只有在供给确实耗尽时才应抛出异常。实现如下：

```lean
namespace Exceptions

structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set { supply with counter := n + 1, property := by grind }
    pure n
```

下列正确性性质表达了这个要求：

```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝,
          fun _ state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh] with grind
```

这里的后置条件有两个分支：第一个覆盖成功终止，第二个覆盖抛出异常。单子的 `WP` 实例同时决定后置条件可以有多少分支，以及每个分支有多少参数。每一层 `PostShape.except ε` 增加一个以异常值 `ε` 为参数的异常后置条件分支，每一层状态则增加一个参数。

在这个新单子里，除了类型签名，`mkFreshN` 的实现不变：

```lean
def mkFreshN (n : Nat) : EStateM String Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList
```

不过，规格引理必须在后置条件和循环不变量中同时处理成功终止与抛出异常：

```lean
@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN n
    ⦃post⟨fun r => ⌜r.Nodup⌝,
          fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN]
  invariants
  · post⟨fun ⟨xs, acc⟩ state =>
           ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
         fun _msg state => ⌜state.counter = state.limit⌝⟩
  with grind
```

最终证明和之前一样，只需使用规格引理与 `mvcgen`：

```lean
theorem mkFreshN_correct (n : Nat) :
    match (mkFreshN n).run s with
    | .ok    l _  => l.Nodup
    | .error _ s' => s'.counter = s'.limit := by
  generalize h : (mkFreshN n).run s = x
  apply EStateM.of_wp_run_eq h
  mvcgen

end Exceptions
```

每个类似 `StateT σ` 的单子变换器都会在 `WP` 所映射到的 `ps` 中产生一层 `PostShape.arg σ`。同理，每个类似 `ExceptT ε` 的层都会产生一层 `PostShape.except ε`。

每个 `PostShape.arg σ` 都给 `Assertion` 语言增加一层 `σ → ...`。每个 `PostShape.except ε` 不改变 `Assertion` 语言，但会给后置条件增加一个异常条件。因此，`EStateM ε σ` 的 `WP` 实例映射到 `PostShape.except ε (.arg σ .pure)`，与 `ExceptT ε (StateM σ)` 相同。

## 扩展 `mvcgen` 以支持自定义单子

`mvcgen` 框架按可扩展方式设计。前文出现的单子没有任何一个被硬编码进 `mvcgen`。相反，`mvcgen` 依靠 `WP`、`WPMonad` 类型类实例和用户提供的规格来生成验证条件。

`WP` 实例定义单子 `m` 到谓词变换器 `PredTrans ps` 的最弱前置条件解释；对应的 `WPMonad` 实例则断言该翻译与 `pure`、`bind` 相容。

假设要用 `mvcgen` 为 [`Aeneas`](https://github.com/AeneasVerif/aeneas) 生成的程序产生验证条件。`Aeneas` 把 Rust 程序翻译成下列 `Result` 单子中的 Lean 程序：

```lean
inductive Error where
  | integerOverflow: Error
  -- ... 更多错误种类 ...

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
```

配套可执行源码还给出了 `Monad Result` 与 `LawfulMonad Result` 实例：

```lean
instance Result.instMonad : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance Result.instLawfulMonad : LawfulMonad Result := by
  apply LawfulMonad.mk' _
  all_goals (dsimp [Functor.map, bind, pure]; grind)
```

让 `mvcgen` 支持这个单子需要两步：

1. 为 `Result` 添加 `WP` 和 `WPMonad` 实例。
2. 为加法等 Rust 基本原语的翻译注册规格引理。

`Result` 没有类似状态的作用，但有一个类型为 `Error` 的异常，因此其 `WP` 实例指定后置条件形状 `.except Error .pure`。该实例把 `Result α` 中的程序翻译为 `PredTrans ps α` 中的谓词变换器，也就是函数 `PostCond α ps → Assertion ps`，它把后置条件映射到最弱前置条件。

`WP.wp` 的实现与 `Except Error` 类似。`Result` 的每个构造器都由已有谓词变换器实现：

- `Result.ok` 使用 `PredTrans.pure`。
- `Result.fail` 使用 `PredTrans.throw`。
- `Result.div` 使用 `PredTrans.const ⌜False⌝`。该分支的最弱前置条件为假，因此任何具有可满足前置条件的完全正确性规格都不能覆盖它；证明必须排除发散。

```lean
instance : WP Result (.except Error .pure) where
  wp
    | .ok v => PredTrans.pure v
    | .fail e => PredTrans.throw e
    | .div => PredTrans.const ⌜False⌝
```

`WP.wp` 的实现应当与基本单子运算相容。下面分别为 `pure` 和 `bind` 证明这一点。处理 `bind` 时，需要同时展开 `wp` 和 `bind` 的定义，暴露嵌套的 `match` 结构，`grind` 很快就能处理它。

只要谓词变换器应用到后置条件上，关于谓词变换器的 `simp` 和 `grind` 理论就会触发。为了把 `WPMonad.wp_pure` 与 `WPMonad.wp_bind` 的目标变成这种形式，这里使用 `ext`：

```lean
theorem Result.apply_wp_pure {α} {a : α} {Q} :
  wp⟦pure (f := Result) a⟧ Q = Q.1 a := by rfl

theorem Result.apply_wp_bind {α β} {x} {f : α → Result β} {Q} :
  wp⟦do let a ← x; f a⟧ Q = wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) := by
  simp only [wp, bind]
  grind

instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure _ := by ext Q : 1; apply Result.apply_wp_pure
  wp_bind x f := by ext Q : 1; apply Result.apply_wp_bind
```

最后，还要证明一个与 `Except.of_wp_eq` 类似的充分性引理：

```lean
theorem Result.of_wp_eq {α} {x prog : Result α}
    (h : prog = x) (P : Result α → Prop)
    (hspec : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝,
                              fun e => ⌜P (.fail e)⌝⟩) :
      P x := by
  subst h
  match prog with
  | .ok a   => simpa [wp] using hspec
  | .fail e => simpa [wp] using hspec
  | .div    => simp [wp] at hspec
```

`WP` 实例的定义决定能通过 `Result.of_wp_eq` 从已证规格推出哪些性质。这个引理也定义了这里的“最弱前置条件”究竟意味着什么。

为了说明第二步，下面在 `Result` 中定义一个模拟整数溢出的 `UInt32` 加法：

```lean
instance : MonadExcept Error Result where
  throw e := .fail e
  tryCatch x h := match x with
  | .ok v => pure v
  | .fail e => h e
  | .div => .div

def addOp (x y : UInt32) : Result UInt32 :=
  if x.toNat + y.toNat ≥ UInt32.size then
    throw .integerOverflow
  else
    pure (x + y)
```

需要注册两个相关的规格引理：

```lean
@[spec]
theorem Result.throw_spec {α Q} (e : Error) :
    ⦃Q.2.1 e⦄ throw (m := Result) (α := α) e ⦃Q⦄ := id

@[spec]
theorem addOp_ok_spec {x y} (h : x.toNat + y.toNat < UInt32.size) :
    ⦃⌜True⌝⦄
    addOp x y
    ⦃⇓ r => ⌜r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⌝⦄ := by
  mvcgen [addOp] with (simp_all; try grind)
```

这些规格已经足以证明下例：

```lean
example :
  ⦃⌜True⌝⦄
  do let mut x ← addOp 1 3
     for _ in [:4] do
        x ← addOp x 5
     return x
  ⦃⇓ r => ⌜r.toNat = 24⌝⦄ := by
  mvcgen
  invariants
  · ⇓⟨xs, x⟩ => ⌜x.toNat = 4 + 5 * xs.prefix.length⌝
  with (simp_all [UInt32.size]; try grind)
```

## 有状态目标的证明模式

`mvcgen` 的设计重点之一，是把单子程序分解成容易理解的验证条件。例如，单子为单态而且所有循环不变量都已实例化时，执行 `all_goals mleave` 应当能消去所有 `Std.Do.SPred` 专用构造，留下人和 `grind` 都容易理解的目标。循环不变量实例化后，`mvcgen` 会自动执行这一步。

但有时 `mleave` 无法消去全部 `Std.Do.SPred` 构造，于是会留下形如 `H ⊢ₛ T` 的验证条件。断言语言 `Assertion` 按如下方式翻译成 `Std.Do.SPred`：

```lean
abbrev PostShape.args : PostShape.{u} → List (Type u)
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

abbrev Assertion (ps : PostShape.{u}) : Type u :=
  SPred (PostShape.args ps)
```

留下 `H ⊢ₛ T` 形式验证条件的一种常见情况，是基础单子 `m` 为多态。此时证明依赖 `WP m ps` 实例，它控制如何翻译到 `Assertion` 语言，但与 `σs : List (Type u)` 的确切对应关系还未知。

为了成功解决这种验证条件，`mvcgen` 提供了一整套证明模式，其设计受 Iris 并发分离逻辑的证明模式启发。事实上，这套证明模式很大一部分改编自 Iris 的 Lean 克隆 [`iris-lean`](https://github.com/leanprover-community/iris-lean)。全部证明模式策略见 Lean 4 参考手册的 [`SPred` 策略参考](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#stateful-proof-mode)。
