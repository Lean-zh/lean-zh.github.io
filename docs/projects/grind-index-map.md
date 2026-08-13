# 使用 `grind` 实现有序映射

- 原文：[官方教程页面](https://lean-lang.org/doc/tutorials/4.34.0-rc1/grind-index-map/)；[Verso 源文件](https://github.com/leanprover/reference-manual/blob/v4.34.0-rc1/Tutorial/Grind/IndexMap.lean)
- 作者：Leo de Moura、Kim Morrison
- 译者：Lean 中文社区
- 对应版本：Lean `v4.34.0-rc1`
- 上游版权：Copyright © 2025 Lean FRO LLC，以 [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0) 发布
- 配套源码：[下载完整工程压缩包](../assets/files/grind-index-map/grind-index-map-4.34.0-rc1.zip)；[直接查看 `IndexMap.lean`](../assets/files/grind-index-map/IndexMap.lean)

本节构造一种新的数据结构及其基本 API，以此说明 [`grind`](https://lean-lang.org/doc/reference/4.34.0-rc1/Tactic-Proofs/Tactic-Reference/#grind) 的用法。示例取材于 Rust 的 [`indexmap`](https://docs.rs/indexmap/latest/indexmap/) 数据结构。

教程展示如何让 `grind` 自动完成一种新数据结构中几乎所有的证明，使 API 兼顾安全性和使用便利。上游 Verso 源在生成本页时设置 `maxHeartbeats 1000000` 和 `maxRecDepth 20000`，分别供 `IndexMap` 示例精译和编译使用；它还启用 `pp.rawOnError true`，以生成后文展示的原始诊断信息。

`IndexMap` 旨在替代 `HashMap`。它同样支持快速的哈希查找，同时允许用户控制元素顺序。这里不会给出完整 API，只建立一些基本函数以及关于它们的定理。

当前要实现的两个主要函数是 `insert` 和 `eraseSwap`：

- `insert k v` 检查映射中是否已有 `k`。如果有，就用 `v` 替换其值，并保持 `k` 在原顺序中的位置；如果没有，就把 `(k, v)` 添加到映射末尾。
- `eraseSwap k` 删除键为 `k` 的元素，再把原来的最后一个元素移入被删元素留下的槽位；如果 `k` 原本就在末尾，则直接弹出末项；如果映射中没有 `k`，则不做任何操作。这个行为可能出人意料。该函数适用于不关心其余元素顺序、只求高效删除的场合。另一种这里未实现的函数可以保留其余元素的顺序，但运行时间会与被删元素之后的元素数量成正比。

目标如下：

- 完全封装：`IndexMap` 的实现对用户隐藏，关于实现细节的定理也设为私有。
- 尽可能使用 `grind`：只要可行，就优先添加私有定理，并为它作适当的本地 `grind` 标注，而不是手写较长的证明。
- 尽可能使用自动参数：理想情况下，证明甚至不会出现在眼前，绝大部分工作由 `grind` 在幕后处理。

第一步是导入所需的数据结构：

```lean
import Std.Data.HashMap
```

## 实现骨架

先写出预期实现的骨架，并大量使用 `sorry` 占位所有证明。特别要注意，这个版本完全没有使用 `grind`。

**实现骨架：**

```lean
import Std.Data.HashMap

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  indices : HashMap α Nat
  keys : Array α
  values : Array β
  size_keys : keys.size = values.size
  WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i

namespace IndexMap

variable {α : Type u} {β : Type v}
  [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
  size_keys := sorry
  WF := sorry

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]'(by sorry)
  getElem? m a :=
    m.indices[a]?.bind (m.values[·]?)
  getElem! m a :=
    m.indices[a]?.bind (m.values[·]?) |>.getD default

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := sorry
  getElem!_def := sorry

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a sorry
      values := m.values.set i b sorry
      size_keys := sorry
      WF := sorry }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b
      size_keys := sorry
      WF := sorry }

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

/--
删除具有给定键的键值对，并把最后一个键值对
移动到被删除键值对原来的顺序位置。
如果该键不存在，映射保持不变。
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop
        size_keys := sorry
        WF := sorry }
    else
      let lastKey := m.keys.back sorry
      let lastValue := m.values.back sorry
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey sorry
        values := m.values.pop.set i lastValue sorry
        size_keys := sorry
        WF := sorry }
  | none => m

/-! ### 验证定理 -/

theorem getIdx_findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m) :
    m.getIdx (m.findIdx a h) sorry = m[a] :=
  sorry

theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  sorry

theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β)
    (h : a' ∈ m.insert a b) :
    (m.insert a b)[a']'h =
      if h' : a' == a then b else m[a']'sorry := by
  sorry

theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a sorry =
      if h : a ∈ m then m.findIdx a h else m.size := by
  sorry

end IndexMap
```

## 用 `grind` 填充实现骨架

现在正式着手实现。目标是完全不手写证明。第一步是在 `size_keys'` 和 `WF` 字段上安装自动参数；只要 `grind` 能证明它们，构造值时就可以省略这些字段。既然正在修改 `IndexMap` 的定义本身，而且目标是完全封装，也把所有字段都设为私有。

```lean
open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind
```

本教程余下部分都在以下命名空间和变量声明下进行：

```lean
namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}
```

### 大小与基本构造

让 `grind` 可以使用 `size` 的定义和私有字段 `size_keys'`：

```lean
@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'

@[local grind =] private theorem size_values : m.values.size = m.size := rfl
```

草稿版构造 `emptyWithCapacity` 时，最先遇到的 `sorry` 是 `size_keys'` 和 `WF` 字段。这两项显然很简单，`grind` 可以解决，因此直接删去这两个字段：

```lean
def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
```

还需要定义包含关系。上游将这段标记为 `codeOnly`：网页正文隐藏它，但下载源码和编译上下文需要这些定义。

```lean
@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))
```

### `GetElem?` 与良构性

下一个任务是处理草稿版 `GetElem?` 实例中的 `sorry`：

```lean
instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]'(by sorry)
  getElem? m a :=
    m.indices[a]?.bind (m.values[·]?)
  getElem! m a :=
    m.indices[a]?.bind (m.values[·]?) |>.getD default
```

这个 `sorry` 处的目标是：

```text
m : IndexMap α β
a : α
h : a ∈ m
⊢ m.indices[a] < m.values.size
```

> 上游维护备注：上述目标展示需要与前一个代码块中的 `sorry` 保持同步。解决办法是为 SubVerso 提取机制添加项级目标支持，做法可仿照现有的普通目标保存功能。

先把它写成独立定理，尝试用 `grind` 证明，看看 `grind` 会卡在哪里。由于已经为 `size` 和 `size_keys` 添加了 `grind` 标注，可以把目标安全地改写为：

```lean
theorem getElem_indices_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.indices[a] < m.size := by
  grind
```

**预期失败。** 这个证明会失败。从 `grind` 消息的 `Goal diagnostics` 一节看，它几乎没有取得进展：

```text
`grind` failed
case grind
α : Type u
β : Type v
inst : BEq α
inst_1 : Hashable α
m : IndexMap α β
a : α
h : a ∈ m
h_1 : m.size ≤ m.indices[a]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a ∈ m
    [prop] m.size ≤ m.indices[a]
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
```

这里立刻能看出一个问题：`grind` 还不知道 `a ∈ m` 与 `a ∈ m.indices` 是同一回事。添加这一事实：

```lean
@[local grind _=_] private theorem mem_indices
    {m : IndexMap α β} {a : α} :
    a ∈ m.indices ↔ a ∈ m := Iff.rfl
```

以下变量声明是上游展示区段的上下文：

```lean
variable {α : Type u} [BEq α] [Hashable α]
```

不论最终证明采用什么方式，已经知道以下几点：

- 它必须使用映射的良构性条件。
- 它必须关联 `m.indices[a]` 和 `m.indices[a]?`，因为后者出现在良构性条件中。
- 除非映射 `m.indices` 满足 `LawfulGetElem`，预期的对应关系根本不成立。为此，需要 `LawfulBEq α` 和 `LawfulHashable α` 的[类型类实例](https://lean-lang.org/doc/reference/4.34.0-rc1/Type-Classes/#--tech-term-instances)。

> 上游待办：这里希望能链接到 `HashMap` 的 `LawfulGetElem` 实例，以便读者直接看到这些要求。

把这些实例和良构性条件配置给 `grind`：

```lean
variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF
```

再给 `grind` 一条手工提示，关联 `m.indices[a]` 与 `m.indices[a]?`：

```lean
private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind
```

定理证明完成后，还要让 `grind` 能使用它。可以在定理陈述前添加 `@[local grind]`，也可以在陈述后写 `attribute [local grind] getElem_indices_lt`。两种写法都会使用 `grind` 的内置启发式方法，决定用什么模式匹配这条定理。

这里先查看 `grind` 属性生成了哪些模式：

```lean
attribute [local grind] getElem_indices_lt
```

**信息输出：**

```text
Try these:
  [apply] [grind
    .] for pattern: [@LE.le `[Nat] `[instLENat] ((@getElem (HashMap #8 `[Nat] #6 #5) _ `[Nat] _ _ (@indices _ #7 _ _ #4) #3 #0) + 1) (@size _ _ _ _ #4)]
  [apply] [grind →] for pattern: [LawfulBEq #8 #6, LawfulHashable _ _ #5, @Membership.mem _ (IndexMap _ #7 _ _) _ #4 #3]
```

这些模式没有用。第一个匹配定理的整个结论，而且是规范化后的版本，其中 `x < y` 已被替换为 `x + 1 ≤ y`。第二个过于宽泛：它会匹配任何包含该定理各项假设的项，而完全忽略结论。

所需模式应比整个结论更一般，但又不能忽略结论。希望每当 `grind` 看到 `m.indices[a]` 时就触发这条定理，因此不用属性自动选取模式，而是编写自定义模式：

```lean
grind_pattern getElem_indices_lt => m.indices[a]
```

Lean 标准库把 `get_elem_tactic` 用作 `xs[i]` 记法的自动参数。该记法展开为 `GetElem.getElem xs i h`，证明 `h` 由 `get_elem_tactic` 生成。这里不只希望 `grind` 填入这些证明，还希望可以完全省略证明。为此添加：

```lean
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)
```

在之后的 Lean 版本中，这可能会成为内置行为的一部分。

现在可以回到 `GetElem?` 实例的构造。为了使用良构性条件，`grind` 必须能展开 `size`：

```lean
attribute [local grind] size
```

其中 `local` 修饰符把这种展开限制在当前文件。配置完成后，可以直接写成：

```lean
instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default
```

这里既没有 `sorry`，也没有显式写出的证明。

接下来需要把这些定义的展开等式暴露给本文件内的 `grind`，但不把实现细节加入公开 API：

```lean
@[local grind =] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind =] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind =] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl
```

这里再次采用 `@[local grind =] private theorem` 模式：对外隐藏实现细节，同时允许 `grind` 在本文件内看到这些事实。

然后证明 `LawfulGetElem` 实例，并让 `grind` 填入证明：

```lean
instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind
```

成功。

### `insert`

继续尝试在不写任何证明的情况下定义 `insert`：

```lean
@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys    := m.keys.set i a
      values  := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys    := m.keys.push a
      values  := m.values.push b }
```

两个分支中，`grind` 都自动证明了 `size_keys'` 和 `WF` 字段。另请注意，第一个分支中的 `m.keys.set i a` 和 `m.values.set i b` 调用，其“索引在界内”义务也由 `grind` 通过 `get_elem_tactic` 自动参数填入。

### `eraseSwap` 的失败诊断与修复

接着尝试 `eraseSwap`：

```lean
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m
```

**预期失败：**

```text
could not synthesize default value for field 'WF' of 'IndexMap' using tactics
```

**预期失败的详细诊断：**

```text
`grind` failed
case grind.1.1.2.2.1.1.1
α : Type u
β : Type v
inst : BEq α
inst_1 : Hashable α
m_1 : IndexMap α β
a_1 : α
b : β
i_1 : Nat
inst_2 : LawfulBEq α
inst_3 : LawfulHashable α
m : IndexMap α β
a : α
i : Nat
h : m.indices[a]? = some i
w : ¬i = m.size - 1
lastKey : α := m.keys.back ⋯
lastValue : β := m.values.back ⋯
i_2 : Nat
a_2 : α
h_1 : ((m.keys.pop.set i (m.keys.back ⋯) ⋯)[i_2]? = some a_2) =
  ¬((m.indices.erase a).insert (m.keys.back ⋯) i)[a_2]? = some i_2
h_2 : -1 * ↑(m.keys.set i (m.keys.back ⋯) ⋯).size + 1 ≤ 0
left : (m.keys.pop.set i (m.keys.back ⋯) ⋯)[i_2]? = some a_2
right : ¬((m.indices.erase a).insert (m.keys.back ⋯) i)[a_2]? = some i_2
h_4 : ¬i = i_2
left_1 : ¬m.keys[i_2]? = some a
right_1 : ¬m.indices[a]? = some i_2
h_6 : (m.keys.back ⋯ == a_2) = true
h_7 : i + 1 ≤ m.keys.pop.size
left_2 : (m.indices.erase a).contains a_2 = true
right_2 : a_2 ∈ m.indices.erase a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Rings

[grind] Diagnostics
```

失败发生在证明第二个分支的 `WF` 字段时。与往常一样，`grind` 给出了失败状态的详细信息，只是信息多得几乎难以利用。查看 `cutsat` 生成的模型，判断问题所在：

```text
[cutsat] Assignment satisfying linear constraints
  [assign] i_1 := 4
  [assign] i := 0
  [assign] i_2 := 1
  [assign] m.keys.pop.size := 2
  [assign] m.keys.size := 3
  [assign] m.size := 3
  [assign] (m.keys.pop.set i (m.keys.back ⋯) ⋯).size := 2
  [assign] m.values.size := 3
  [assign] m.indices[a] := 0
  [assign] ((m.indices.erase a).insert (m.keys.back ⋯) i)[a_2] := 0
  [assign] (m.keys.set i (m.keys.back ⋯) ⋯).pop.size := 2
  [assign] (m.keys.set i (m.keys.back ⋯) ⋯).size := 3
  [assign] m.indices[a] := 0
  [assign] m.indices[a_2] := 1
  [assign] m.indices[m.keys[i_2]] := 1
  [assign] m.indices[m.keys[i_2]] := 1
```

上游对该输出的备注：

```text
FIXME（@kim-em / @leodemoura）：这里有一些重复输出。
```

这不是一个合法 `IndexMap` 的反例，而是 `cutsat` 在当前线性抽象下允许的一组赋值。它表现得像一个大小为 `3`、键为 `a`、`a_2` 和未单独命名的 `m.keys.back ⋯` 的映射，用来指出当前规则还没有向线性算术求解器传递哪些事实。

赋值中最可疑的是下面这一行：

```text
((m.indices.erase a).insert (m.keys.back ⋯) i)[a_2] := 0
```

如果把原 `IndexMap` 的良构性和由此推出的键单射性充分传递进来，这三个位置对应的键互异，因而应当有：

```text
((m.indices.erase a).insert (m.keys.back ⋯) i)[a_2] =
  (m.indices.erase a)[a_2] =
  m.indices[a_2] =
  1
```

发现可疑之处后，可以检查 `grind` 找到的等价类。未来会提供检查等价类的搜索工具；目前只能手工通读。许多等价类中包括：

```text
{a_2,
  m.keys.back ⋯,
  ..
  m.keys[m.keys.size - 1],
  ..
  m.keys[i_2], ...}
```

根据 `keys` 的单射性，这应当推出 `i_2 = m.keys.size - 1`。但这组 `cutsat` 赋值并未反映该等式，说明 `grind` 尚未把由 `WF` 推出的单射性传递给线性算术求解器。

回看良构性条件的表达方式：`∀ (i : Nat) (a : α), keys[i]? = some a ↔ indices[a]? = some i`，出现这种情况或许并不意外。它以 `keys[i]?` 和 `indices[a]?` 表述。添加一个改用 `GetElem.getElem` 而非 `GetElem?.getElem?` 的良构性条件变体：

```lean
@[local grind .]
private theorem WF' (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind
```

有了这个变体，可以验证 `grind` 现在能够证明：

```lean
example {m : IndexMap α β} {a : α} {h : a ∈ m} :
  m.keys[m.indices[a]'h] = a := by grind
```

再次尝试 `eraseSwap`，现在所有内容都顺利通过，不需要手工证明：

```lean
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m
```

以下是索引查找和值读取函数。上游同样将这段标记为 `codeOnly`：网页正文隐藏它，但后续证明和下载源码需要这些定义。

```lean
@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m := by get_elem_tactic) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]
```

### 验证定理与完整原型

最后证明基本操作的验证定理，关联 `getIdx`、`findIdx`、`insert` 和 `eraseSwap`。所有证明都能直接使用带 `+locals` 修饰符的 `grind` 完成；该修饰符把当前文件中的定义加入 `grind` 可用的规则集合，使这些本文件定义的方程能够参与证明：

```lean
/-! ### 验证定理（并未穷尽） -/

@[grind =]
theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind +locals

@[grind =]
theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind +locals

theorem findIdx_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.findIdx a h < m.size := by
  grind +locals

grind_pattern findIdx_lt => m.findIdx a h

@[grind =]
theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind +locals

@[grind =]
theorem findIdx?_eq (m : IndexMap α β) (a : α) :
    m.findIdx? a = if h : a ∈ m then some (m.findIdx a h) else none := by
  grind +locals

@[grind =]
theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind +locals

omit [LawfulBEq α] [LawfulHashable α] in
@[grind =]
theorem getIdx?_eq (m : IndexMap α β) (i : Nat) :
    m.getIdx? i = if h : i < m.size then some (m.getIdx i h) else none := by
  grind +locals

private theorem getElem_keys_mem {m : IndexMap α β} {i : Nat} (h : i < m.size) :
    m.keys[i] ∈ m := by
  have : m.indices[m.keys[i]]? = some i := by grind
  grind

local grind_pattern getElem_keys_mem => m.keys[i]

theorem getElem?_eraseSwap (m : IndexMap α β) (a a' : α) :
    (m.eraseSwap a)[a']? = if a' == a then none else m[a']? := by
  grind +locals

@[grind =]
theorem mem_eraseSwap (m : IndexMap α β) (a a' : α) :
    a' ∈ m.eraseSwap a ↔ a' ≠ a ∧ a' ∈ m := by
  grind +locals

theorem getElem_eraseSwap (m : IndexMap α β) (a a' : α) (h : a' ∈ m.eraseSwap a) :
    (m.eraseSwap a)[a'] = m[a'] := by
  grind +locals
```

其中，希望供模块外的 `grind` 自动使用的 API 定理，需要通过 `@[grind]` 或 `grind_pattern` 注册；普通公开定理不必全部注册。这样，即使用户无法使用本文件内部的 `local grind` 规则，选定的公开事实仍能参与 `grind` 证明。

汇总以上代码，原型 API 得到如下实现。

> 上游待办：应当通过注解从源模块生成这个版本，并丢弃不需要的内容，从而使展示代码与源码保持同步。

```lean
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'

@[local grind =] private theorem size_values : m.values.size = m.size := rfl

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β) (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind _=_] private theorem mem_indices
    {m : IndexMap α β} {a : α} :
    a ∈ m.indices ↔ a ∈ m := Iff.rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m := by get_elem_tactic) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF

private theorem getElem_indices_lt
    {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind

grind_pattern getElem_indices_lt => m.indices[a]

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind =] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind =] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind =] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys    := m.keys.set i a
      values  := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys    := m.keys.push a
      values  := m.values.push b }

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

@[local grind .]
private theorem WF' (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind

/--
删除具有给定键的键值对，并把最后一个键值对
移动到被删除键值对原来的顺序位置。
如果该键不存在，映射保持不变。
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m

/-! ### 验证定理（并未穷尽） -/

@[grind =]
theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind +locals

@[grind =]
theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind +locals

theorem findIdx_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.findIdx a h < m.size := by
  grind +locals

grind_pattern findIdx_lt => m.findIdx a h

@[grind =]
theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind +locals

@[grind =]
theorem findIdx?_eq (m : IndexMap α β) (a : α) :
    m.findIdx? a = if h : a ∈ m then some (m.findIdx a h) else none := by
  grind +locals

@[grind =]
theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind +locals

omit [LawfulBEq α] [LawfulHashable α] in
@[grind =]
theorem getIdx?_eq (m : IndexMap α β) (i : Nat) :
    m.getIdx? i = if h : i < m.size then some (m.getIdx i h) else none := by
  grind +locals

end IndexMap
```

现在还为 `eraseSwap` 操作添加了验证定理。有兴趣的读者可以继续扩充，甚至发布一个完整的 `IndexMap` 库。

以上封装设计遵循这些原则：

- `IndexMap` 的所有字段都是私有的，因为它们属于实现细节。
- 关于这些字段的定理也都是私有的，并标注 `@[local grind]` 而不是 `@[grind]`，因为 API 建立之后不再需要它们。
- 希望模块外的 `grind` 自动使用的验证定理，通过 `@[grind]` 或 `grind_pattern` 注册；这些定理本身由 `grind` 证明。离开当前模块后，`@[local grind]` 定理不再可用，因此必须把所需的公开事实另行注册。未供自动匹配使用的公开定理不必标注 `@[grind]`。
