# LeanSearchClient

LeanSearchClient 提供了在 Lean 内使用 [leansearch API](https://leansearch.net/)、[Moogle API](https://www.moogle.ai/api/search) 和 [LeanStateSearch](https://premise-search.com) API 进行搜索的语法。它允许你使用自然语言搜索 Lean 的策略和定理，同时也支持在 Lean 内对 [Loogle](https://loogle.lean-lang.org/json) 进行搜索。

我们提供了用于发起查询的语法，并生成 `TryThis` 选项，方便你点击或使用代码操作来利用搜索结果。查询共有四种形式：

* `command` 语法：以命令形式使用 `#search "search query"`。
* `Term` 语法：以项的形式使用 `#search "search query"`。
* `Tactic` 语法：以策略形式使用 `#search "search query"`。
* 基于状态的 `Tactic` 语法：直接使用 `#search`。

在所有情况下，结果都会显示在 Lean 信息视图中，点击结果会替换原查询文本。而在策略查询中，只会显示有效的策略。

所使用的后端由 `leansearchclient.backend` 选项决定。

## 示例

以下是使用 leansearch API 的示例。当查询语句以句号或问号结束时，搜索将会被触发。

### 查询 command

适用于所有后端的通用命令：

```lean
#search "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

我们还为特定后端提供了命令。例如，对于 `leansearch`：

```lean
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

对于 `moogle`：

```lean
#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
```


### 查询 Term

通用命令：

```lean
example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

对于 `leansearch`：

```lean
example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
```

对于 `moogle`：

```lean
example := #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
```


### 查询 Tactic

请注意，只会显示有效的策略。

通用命令有两种变体。一种是带字符串的形式，调用 LeanSearch 或 Moogle：

```lean
example : 3 ≤ 5 := by
  #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

另一种是不带字符串的形式，调用 LeanStateSearch：

```lean
example : 3 ≤ 5 := by
  #search
  sorry
```

不同后端也有各自的特定命令。

对于 `leansearch`：

```lean
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

对于 `moogle`：

```lean
example : 3 ≤ 5 := by
  #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

对于 LeanStateSearch：

```lean
example : 3 ≤ 5 := by
  #statesearch
  sorry
```


## Loogle 搜索

`#loogle` 命令也可以在所有三种模式下使用。其语法为 `#loogle <search query>`，例如：

```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry
```