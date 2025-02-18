# Lean4 REPL

## 项目概要

REPL (Read-Eval-Print Loop) 是一个交互式编程环境，允许用户输入命令，执行并查看结果。Lean 4 REPL 基于 JSON 通信，支持三种工作模式。

### 命令模式 (Command Mode)

在命令模式下，可以发送完整的 Lean 命令（如声明、定义等）到 REPL，比如：

```json
{ "cmd": "def f := 2" }
```

### 文件模式 (File Mode)

文件模式是命令模式的简单封装，允许直接读取和执行整个 Lean 文件的内容。例如：

```json
{ "path": "test/file.lean", "allTactics": true }
```

### 策略模式 (Tactic Mode)

策略模式允许使用 Lean 的证明策略（tactics）来交互式地构建证明。这个模式通常从一个包含 `sorry` 的命令开始，然后逐步完成证明。

## 安装与基本使用

### 安装

首先，克隆并构建 REPL 项目：

```bash
git clone https://github.com/leanprover-community/repl
cd repl
lake update -R && lake build
```

**特别注意**，REPL 的版本需要与目标 Lean 代码的版本保持一致。

### 基本使用

进入仓库，通过 `lake exe repl` 启动交互式终端，输入 JSON 块，获取相应的输出。

此外，也可以通过标准输入输出流进行通信，比如：

```bash
echo '{ "cmd": "def f := 2" }' | lake exe repl
```

## REPL 命令模式

下边，我们详细介绍 REPL 的三种模式，以及 Pickle 特性。先从最基础的 **命令模式** 开始。

### 状态跟踪

REPL 的命令模式通过 `env` 字段跟踪环境状态，每次执行 `cmd` 命令后会返回一个新的环境编号。这种机制有很多好处：

1. **状态追踪**：允许在一个交互终端中启用多个环境，比如 `import` 不同的模块，每个命令执行后都会生成新的环境编号
2. **环境选择**：允许通过指定 `env` 值回溯到之前的状态，在该环境的基础上执行新命令
3. **环境隔离**：不同环境的变量相互独立

### 示例解析

我们通过一个具体示例来理解命令模式的工作方式：

```bash
# 命令序列
{"cmd": "def f1 := 37"}                 # 命令 1
{"cmd": "def f2 := 37", "env":0}        # 命令 2
{"cmd": "def f3 := f1 + f2", "env": 1 } # 命令 3
{"cmd": "def f3 := f1 + f2", "env": 1 } # 命令 4
{"cmd": "def f3 := f1 + f2", "env": 2 } # 命令 5
```

**环境变化过程**：

1. 定义 `f1 := 37`，创建新环境 env 0
2. 基于 env 0 添加定义 `f2 := 37`，并创建新环境 env 1
3. 基于 env 1 添加定义 `f3 := f1 + f2`，并创建新环境 env 2
4. 基于 env 1 执行相同操作，并创建新环境 env 3
5. 基于 env 2 重新定义 `f3`，报错：`'f3' has already been declared`，并创建新环境 env 4


## REPL 策略模式

策略模式（Tactic Mode）是 REPL 的核心功能，用于交互式证明构建。

策略模式有以下特性：

1. **状态创建**：使用 `sorry` 创建证明占位符，
2. **状态追踪**：通过 `proofState` 标识状态索引，每个 `sorry` 按顺序生成 `proofState`，策略作用也会产生新的证明状态
3. **多目标处理**：支持 pick 指定目标来进行下一步证明
4. **灵活性**：支持各种证明策略，包括 `have, calc` 等，且允许分步构建复杂证明

### 示例解析

为展示方便，我们将输出结果拼接到对应输入行后边：

```python
# 步骤1：创建定理
{"cmd" : "def f (x : Unit) : Nat := by sorry"}
# 返回 proofState 0，并得到 env 0
{"sorries":
 [{"proofState": 0,
   "pos": {"line": 1, "column": 29},
   "goal": "x : Unit\n⊢ Nat",
   "endPos": {"line": 1, "column": 34}}],
 "messages":
 [{"severity": "warning",
   "pos": {"line": 1, "column": 4},
   "endPos": {"line": 1, "column": 5},
   "data": "declaration uses 'sorry'"}],
 "env": 0}

# 步骤2：应用第一个策略
{"tactic": "apply Int.natAbs", "proofState": 0}
# 生成新的证明状态 proofState 1
{"proofState": 1, "goals": ["x : Unit\n⊢ Int"]}

# 步骤3：完成证明
{"tactic": "exact 0", "proofState": 1}
# 空目标列表表示证明完成
{"proofState": 2, "goals": []}
```

### 复杂示例：使用 have 策略

```python
# 创建带有中间步骤的定理
{"cmd": "theorem foo (x : Int) : x = x := by\n  have h : x = 1 := by sorry"}

# 结果：
# 1. 抛出错误：只放了一处 sorry，存在未解决的目标
# 2. 返回 proofState 0，由 have 的 sorry 产生
{"sorries":
 [{"proofState": 0,
   "pos": {"line": 2, "column": 23},
   "goal": "x : Int\n⊢ x = 1",
   "endPos": {"line": 2, "column": 28}}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 33},
   "endPos": {"line": 2, "column": 28},
   "data": "unsolved goals\nx : Int\nh : x = 1\n⊢ x = x"}],
 "env": 0}

# 使用 have 策略
{"proofState" : 0, "tactic": "have h : x = 1 := by sorry"}
# 结果：
# 1. have 引入了新的目标 proofState 1
# 2. proofState 0 在执行 have 后变为 proofState 2
{"sorries": [{"proofState": 1, "goal": "x : Int\n⊢ x = 1"}],
 "proofState": 2,
 "goals": ["x : Int\nh : x = 1\n⊢ x = 1"]}
```


## REPL 文件模式

文件模式是 REPL 提供的一个简单但实用的功能，它允许直接读取和执行 Lean 源文件。

### 用法示例

假设 `test/file.lean` 包含以下内容：

```lean
def f : Nat := 37
def g := 2
theorem h : f + g = 39 := by exact rfl
```

将 `allTactics` 参数设置为 `true`，获取更详细的证明过程和状态：

```bash
echo '{"path": "/path/to/file.lean", "allTactics": true}' | lake exe repl
```

执行后会得到类似的输出：

```json
{"tactics":
 [{"tactic": "exact rfl",
   "proofState": 0,
   "pos": {"line": 3, "column": 29},
   "goals": "⊢ f + g = 39",
   "endPos": {"line": 3, "column": 38}}],
 "env": 0}
```

效果等同于将文件内容通过 `cmd` 命令执行，即：

```bash
echo '{"cmd" : "def f : Nat := 37\\ndef g := 2\\ntheorem h : f + g = 39 := by exact rfl", "allTactics": true}' | lake exe repl
```

## Pickle 特性

Pickle 特性允许我们将环境状态（env）或证明状态（proofState）保存到文件中，并在需要时重新加载。

**使用场景**：REPL 是以 Json 数据形式交互的，如果我们想还原当前的证明状态或环境，需要重新执行所有命令。对于复杂的证明过程，重复执行会很耗时。此外，在多机协作时，我们也需要共享证明状态。

### Pickle 的基本操作

Pickle 的基本操作：

1. **保存环境/状态**（pickleTo）
2. **加载状态**（unpickleProofStateFrom）
3. **加载环境**（unpickleEnvFrom）

### 示例分析

看一个实际的例子：

```python
# 1. 导入基础库
{"cmd" : "import Mathlib"}

# 2. 创建定理
{"cmd": "theorem simple \n  (a : ℝ):\n  a^((1:ℝ)/2 * 2) = a := by sorry", "env":0}

# 3. 保存证明状态
{"pickleTo": "test.olean", "proofState": 0}

# 4. 加载证明状态
{"unpickleProofStateFrom": "test.olean"}

# 5. 继续证明
{"tactic": "ring_nf", "proofState": 1}
{"tactic": "simp", "proofState": 2}
```

## 配置 Mathlib 依赖

REPL 本身不依赖 Mathlib，但我们可能需要处理包含 Mathlib 依赖的项目。以 Lean 4.14.0 版本为例，有两种解决方式：

**方式一：直接添加 Mathlib 依赖**

1. 在 REPL 项目的 `lakefile.toml` 中添加依赖：

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84"
```

2. 更新并构建：

```bash
lake update -R && lake exe cache get && lake build
```

3. 使用示例：

```bash
echo '{ "cmd": "import Mathlib" }' | lake exe repl
```

**方式二：使用 lake env**

在包含 Mathlib 依赖的项目中，使用 `lake env` 指向 REPL 可执行文件：

```bash
echo '{ "cmd": "import Mathlib" }' | lake env /path/to/repl/.lake/build/bin/repl
```

## 更多示例

最后，附上 REPL 提供的测试示例，以下内容由模型结合测试代码生成。

### 基础示例：检查变量定义

```python
# 输入命令和对应输出
{"cmd": "def f := 2"}                 # 定义 f
{"env": 0}

{"cmd": "#check f", "env": 0}         # 检查 f 的类型
{"messages": [{"data": "f : Nat"}...]} # f 的类型是 Nat

{"cmd": "#check g", "env": 1}         # 检查未定义的 g
{"messages": [{"data": "unknown identifier 'g'"}...]} # 报错：未知标识符
```

使用 `#check` 命令检查变量的类型，以及处理未定义变量的错误情况。

### 策略示例：使用 by_cases 分类讨论

```python
# 定义带有 sorry 的定理
{"cmd": "theorem foo (x : Int) : x = x := by sorry"}
{"sorries": [{"proofState": 0, "goal": "x : Int\n⊢ x = x"}...]}

# 使用 by_cases 策略分类讨论
{"proofState" : 0, "tactic": "by_cases h : x < 0"}
{"proofState": 1, "goals": [
  "case pos\nx : Int\nh : x < 0\n⊢ x = x",
  "case neg\nx : Int\nh : ¬x < 0\n⊢ x = x"]}

# 处理正例
{"proofState" : 1, "tactic": "case pos => rfl"}
{"proofState": 2, "goals": ["case neg..."]}

# 使用 sorry 完成所有剩余目标
{"proofState" : 1, "tactic": "all_goals sorry"}
{"proofState": 5, "goals": []}
```

使用 `by_cases` 策略进行分类讨论，并通过 `all_goals sorry` 处理剩余证明目标。

### 变量声明与复杂定理

```python
# 声明变量
{"cmd": "variable (x y : Nat)"}
{"cmd": "variable (f : Nat → Nat)", "env": 0}

# 定义复杂定理
{"cmd": "theorem problem (h0 : f 5 = 3) (h1 : f (4 * x * y) = 2 * y * (f (x + y) + f (x - y))) :
    ∃ (k : Nat), f 2015 = k := by\n  sorry", "env": 1}
```

声明变量和函数变量，并构建包含这些变量的复杂定理。注意到这个例子中的错误提示表明需要正确处理变量作用域。

### 策略示例：使用各种策略组合

```python
# 设置 simp 追踪并定义示例
{"cmd": "set_option trace.Meta.Tactic.simp true\nexample {x : Int} (h0 : x > 0) : False := by sorry"}

# 尝试不同策略
{"tactic": "have h : x > 0 := by sorry", "proofState": 0}  # 引入新假设
{"tactic": "exact h0", "proofState": 1}                    # 使用 exact
{"tactic": "assumption", "proofState": 1}                  # 使用 assumption
{"tactic": "simp only [of_eq_true (eq_true h0)]", "proofState": 1}  # simp 带配置
{"tactic": "{ simp [h0] }", "proofState": 1}              # 局部 simp
# ... 其他策略尝试
```

多种证明策略的使用方式，包括 `have`、`exact`、`assumption` 和带不同配置的 `simp`。

注：为简洁起见，省略了部分输出信息。

### 策略示例：使用 have 引入中间变量

```python
# 使用 have 引入中间变量并完成定义
{"cmd": "def f : Nat := by have t := 37; exact t", "allTactics": true}
{"proofState": 0, "goals": ["t : Nat\n⊢ Nat"]}  # 引入 t 后的状态
{"proofState": 1, "goals": []}                   # exact t 完成证明
```

使用 `have` 引入中间变量，并用 `exact` 完成定义，`allTactics` 参数允许追踪策略执行过程。

### 包管理示例：导入 Lake

```python
# 导入 Lake 包并打开 DSL 命名空间
{"cmd": "import Lake open Lake DSL\npackage REPL"}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}
```

导入和使用 Lake 包管理系统，这是 Lean 4 的标准包管理器。

### 简单示例：基础定义中的 sorry

```python
# 使用 sorry 定义函数
{"cmd": "def f : Nat := by sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ ◾"}...]}
```

最基本的 sorry 占位符使用方式，其中 `⊢ ◾` 表示需要证明一个值（而不是命题）。

### 策略示例：构造函数应用

```python
# 简单构造函数应用
{"cmd": "def f : Nat := by apply Nat.succ"}
{"messages": [{"data": "unused variable `h`"...}]}

# 使用 by_cases 的条件分支
{"cmd": "def f (x : Bool) : Nat := by\n  by_cases x\n  { apply Nat.succ }"}
```

使用 `apply` 策略应用构造函数，以及在 `by_cases` 分支中使用构造函数。

### 策略示例：have 引入中间命题

```python
# 创建带有多个 sorry 的示例
{"cmd" : "example : True := by\n  have h : set Nat := by sorry\n  sorry"}
{"sorries": [
  {"proofState": 0, "goal": "x : Int\n⊢ x = x"}...],  # 第一个 sorry
  "messages": [{"data": "declaration uses 'sorry'"}...]}

# have 语句产生新的证明状态
{"sorries": [{"proofState": 1, "goal": "x : Int\n⊢ x = 1"}],
 "proofState": 2,
 "goals": ["x : Int\nh : x = 1\n⊢ x = x"]}
```

使用 `have` 策略引入中间命题，这会产生两个证明目标：一个用于证明引入的命题，另一个用于完成主要证明。

### 基础示例：使用 rfl 检查相等性

```python
# 定义数值
{"cmd": "def f := 37"}
{"env": 0}

# 使用 rfl 检查相等性
{"cmd": "#check (rfl : f = 37)", "env": 0}
# 命令执行成功，无输出表示类型检查通过
```

使用 `rfl`（reflexivity）证明简单的相等性，并通过 `#check` 验证。

### 示例：使用下划线占位符

```python
# 使用下划线作为占位符定义函数
{"cmd": "def f : Nat := _"}
{"messages": [{"data": "constructor List.cons..."}...]}
```

使用下划线（`_`）作为占位符来定义函数，REPL 会显示可能的构造器信息。

### 基础示例：定义数值类型

```python
# 使用 sorry 定义自然数
{"cmd": "def f : Nat := sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}
```

使用 `sorry` 为自然数类型创建一个占位定义。

### 打印示例：查看定义和设置选项

```python
# 打印 List.cons 定义
{"cmd": "#print List.cons"}
{"env": 0}

# 启用打印universe层级
{"cmd": "set_option pp.universes true"}
{"env": 1}

# 再次打印 List.cons，这次会显示universe信息
{"cmd": "#print List.cons", "env": 1}
{"env": 2}
```

使用 `#print` 命令查看定义，以及通过 `set_option` 控制输出格式。

### 策略示例：使用 natAbs 构造自然数

```python
# 定义返回自然数的函数
{"cmd" : "def f (x : Unit) : Nat := by sorry"}
{"sorries": [{"proofState": 0, "goal": "x : Unit\n⊢ Nat"}...]}

# 使用 Int.natAbs 将整数转换为自然数
{"tactic": "apply Int.natAbs", "proofState": 0}
{"proofState": 1, "goals": ["x : Unit\n⊢ Int"]}

# 提供具体整数值
{"tactic": "exact -37", "proofState": 1}
{"proofState": 2, "goals": []}
```

通过 `Int.natAbs` 将整数转换为自然数来构造 `Nat` 类型的值。

### 错误示例：错误的构造器使用

```python
# 尝试使用 constructor 构造 Nat
{"cmd": "def f (h : Int) : Nat := by constructor", "infotree": "substantive"}
{"messages": [{"data": "don't know how to synthesize placeholder\ncontext:\n⊢ Nat"}...]}
```

错误使用 `constructor` 策略的情况：不能直接用构造器构造 `Nat` 类型。

### 策略示例：错误处理演示

```python
# 定义定理
{"cmd": "theorem my_theorem (x : Nat) : x = x := by sorry"}
{"sorries": [{"proofState": 0, "goal": "x : Int\n⊢ x = x"}...]}

# 尝试使用未定义的前提
{"tactic": "exact my_fake_premise", "proofState": 0}
{"messages": [{"severity": "error", "data": "unknown identifier 'my_fake_premise'"}...]}
```

在使用未定义变量时 REPL 的错误处理机制。

### 示例：多个 sorry 的处理

```python
# 使用多个 sorry 的示例
{"cmd" : "example : True := by\n  sorry\n  sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}
```

在同一个证明中使用多个 `sorry`，REPL 会为每个 `sorry` 分配独立的 `proofState`。

### 策略示例：使用 have 引入中间结论

```python
# 定义定理
{"cmd": "theorem foo (x : Int) : x = x := by sorry"}
{"sorries": [{"proofState": 0, "goal": "x : Int\n⊢ x = x"}...]}

# 使用 have 引入中间结论
{"proofState" : 0, "tactic": "have h : x = 1 := sorry"}
{"messages": [{"data": "unsolved goals..."}...]}
```

使用 `have` 策略引入中间结论，这会产生两个证明目标：一个是证明中间结论，另一个是使用中间结论证明原目标。

### 策略示例：简单值定义

```python
# 定义带有 sorry 的自然数
{"cmd" : "def f : Nat := by sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ True"}...]}

# 尝试使用 exact 策略（错误示例）
{"tactic": "exact 42", "proofState": 1}
{"messages": [{"data": "no goals to be solved"}...]}
```

一个简单的值定义，以及当尝试在无效状态上使用策略时的错误处理。

### 文件模式示例：读取文件并处理错误

```python
# 读取并执行 Lean 文件
{"path": "test/file.lean", "allTactics": true}

# 输出包含错误信息
{"sorries": [{"proofState": 0, "goal": "x : Nat\n⊢ x = x"}...]}
{"proofState": 1, "messages": [
  {"data": "unknown identifier 'my_fake_premise'"}...]}
```

文件模式读取 Lean 文件并处理执行过程中的错误（如未知标识符）。

### 调试示例：使用 trace 和 simp

```python
# 定义函数和简化规则
{"cmd": "def f := 37"}
{"cmd": "@[simp] theorem f_def : f = 37 := by rfl", "env": 0}

# 启用 simp 跟踪
{"cmd": "set_option trace.Meta.Tactic.simp true", "env": 1}

# 使用 simp 证明
{"cmd": "example : f = 37 := by simp", "env": 2}

# 使用 trace 进行调试
{"cmd": "example : f = 37 := by sorry", "env": 2}
{"tactic": "trace \"37\"", "proofState": 0}
{"tactic": "simp", "proofState": 0}

# 在证明中嵌入 trace
{"cmd": "example : True := by\n  trace \"!\"\n  trivial"}
```

使用 `trace` 和 `simp` 进行调试和简化证明，以及设置跟踪选项。

### 策略示例：直接使用 sorry

```python
# 定义带有 sorry 的函数
{"cmd": "def f : Nat := by sorry"}
{"env": 0}

# 直接使用 sorry 完成证明
{"proofState": 0, "tactic": "sorry"}
{"env": 2}
```

最简单的 sorry 用法：直接用 sorry 完成定义或证明。

### 策略示例：使用 calc（计算块）

```python
# 使用 calc 块进行链式推导
{"cmd": "example : 3 = 5 := by calc\n  3 = 4 := by sorry\n  4 = 5 := by sorry", "allTactics": true }
{"tactics": [{"tactic": "exact rfl", "goals": "⊢ f + g = 39"...}]}
```

使用 `calc` 语法构建链式等式推导，每一步都使用 `sorry` 标记待证明的步骤。

### 错误处理示例：策略名拼写错误

```python
# 定义带有 sorry 的函数
{"cmd" : "def f : Nat := by sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}

# 错误的策略名称 (exat 应为 exact)
{"tactic": "exat 42", "proofState": 0}
{"proofState": 1, "goals": ["⊢ Nat"]}  # 策略执行失败，目标保持不变
```

当策略名称拼写错误时（`exat` 而不是 `exact`），REPL 会保持证明状态不变，允许继续尝试正确的策略。

### 示例：多个定理的连续定义

```python
# 定义第一个定理
{"cmd": "theorem thm1 : 1 = 1 := sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ 1 = 1"}...], "env": 0}

# 在同一环境下定义第二个定理
{"cmd": "theorem thm2 : 2 = 2 := sorry", "env": 0}
{"sorries": [{"proofState": 1, "goal": "⊢ 2 = 2"}...], "env": 1}
```

在同一环境中连续定义多个待证明的定理，每个定理获得独立的 `proofState`。

### 示例：sorry 占位符的基本使用

```python
# 使用 sorry 定义一个自然数
{"cmd": "def f : Nat := by sorry", "env": 5}
{"sorries": [{"proofState": 0, "goal": "⊢ ◾"}...],
 "messages": [{"data": "declaration uses 'sorry'"}...],
 "env": 2}
```

使用 `sorry` 作为占位符来定义一个尚未实现的自然数值，其中 `⊢ ◾` 表示需要提供一个 `Nat` 类型的值。

### 策略示例：定义自然数值

```python
# 定义带证明的自然数
{"cmd" : "def f : Nat := by sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}

# 尝试应用 Int.natAbs（错误示范）
{"tactic": "apply Int.natAbs", "proofState": 0}
{"messages": [{"data": "type expected, got (set Nat..."}...]}

# 引入中间值
{"tactic": "have t : Nat := 42", "proofState": 0}
{"proofState": 2...}

# 使用引入的值完成证明
{"tactic": "exact t", "proofState": 2}
{"proofState": 3, "goals": []}
```

通过引入具体值（42）来定义自然数，以及处理错误策略应用的情况。

### 策略示例：使用 have 引入中间结论

```python
# 方式一：在定理中直接使用 have
{"cmd": "theorem foo (x : Int) : x = x := by\n  have h : x = 1 := by sorry"}
{"messages": ["unsolved goals\nx : Int\nh : x = 1\n⊢ x = x"...]}

# 方式二：分步执行 have
{"cmd": "theorem foo (x : Int) : x = x := by sorry"}
{"sorries": [{"proofState": 1, "goal": "x : Int\n⊢ x = x"}...]}

{"proofState" : 0, "tactic": "have h : x = 1 := by sorry"}
{"sorries": [{"goal": "x : Int\n⊢ x = 1"}],
 "goals": ["x : Int\nh : x = 1\n⊢ x = 1"]}
```

两种使用 `have` 引入中间结论的方式，以及它们产生的证明状态。

### 策略示例：基本策略组合

```python
# 定义函数 f，使用策略模式
{"cmd": "def f : Nat := by"}
{"tactics": [
    # 第一个策略：引入中间变量
    {"tactic": "have t := 37", "goals": "⊢ Nat"...},
    # 第二个策略：使用引入的变量完成证明
    {"tactic": "exact t", "goals": "t : Nat\n⊢ Nat"...}
]}
```

使用 `have` 和 `exact` 策略的组合来构造一个简单的自然数定义。

## Pickle 模式

### Pickle 示例：保存和加载环境

```python
# 定义并保存环境
{"cmd": "def f := 42"}                         # 定义 f
{"pickleTo": "test/a.olean", "env": 0}        # 保存环境

# 加载环境并使用
{"unpickleEnvFrom": "test/a.olean"}           # 加载
```

环境的序列化操作。


### Pickle 示例：保存和加载环境

```python
# 导入基础库并定义函数
{"cmd": "import Lean"}
{"cmd": "def f := 42", "env": 0}

# 保存环境到文件
{"pickleTo": "test/b.olean", "env": 1}

# 从文件加载环境
{"unpickleEnvFrom": "test/b.olean"}

# 在加载的环境中验证定义
{"cmd": "example : f = 42 := by rfl", "env": 2}
```

使用 `pickleTo` 和 `unpickleEnvFrom` 命令来保存和恢复环境状态，并在恢复的环境中继续工作。

### Pickle 示例：保存和加载证明状态

```python
# 导入基础库并定义带 sorry 的函数
{"cmd" : "import Lean"}
{"cmd" : "def f : Nat := by sorry", "env": 0}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}

# 保存初始状态
{"pickleTo": "test/c.olean", "proofState": 0}

# 加载状态并继续证明
{"unpickleProofStateFrom": "test/c.olean", "env": 0}
{"tactic": "have t : Nat := 42", "proofState": 2}

# 保存中间状态
{"pickleTo": "test/d.olean", "proofState": 3}

# 加载中间状态并完成证明
{"unpickleProofStateFrom": "test/d.olean", "env": 0}
{"tactic": "exact t", "proofState": 5}
```

在证明过程中使用 pickle 保存和加载证明状态，实现证明的断点续传。

### Pickle 示例：加载并继续证明

```python
# 从文件加载证明状态
{"unpickleProofStateFrom": "test/d.olean"}
{"env": 0}

# 使用 exact 完成证明
{"tactic": "exact t", "proofState": 0}
{"messages": [{"data": "f : Nat"}...]}
```

从 `.olean` 文件加载证明状态，并继续完成证明过程。

### Pickle 示例：使用 open 导入定义

```python
# 在命名空间 X 中定义 Y
{"cmd": "def X.Y : Nat := 37"}
{"env": 0}

# 打开命名空间 X
{"cmd": "open X", "env": 0}
{"env": 1}

# 直接使用 Y（无需 X.Y）验证值
{"cmd": "example : Y = 37 := rfl", "env": 1}
{"env": 2}

# 保存环境状态
{"pickleTo": "test/e.olean", "env": 1}
```

使用命名空间（namespace）组织代码，以及通过 `open` 命令简化访问。

### Pickle 示例：加载环境变量

```python
# 加载已保存的环境
{"unpickleEnvFrom": "test/e.olean"}
{"env": 0}

# 在加载的环境中使用变量
{"cmd": "example : Y = 37 := rfl", "env": 0}
{"env": 1}
```

从 `.olean` 文件加载预定义的环境并使用其中的变量。

### 导入模块和使用 unsafe 示例

```python
# 导入 Lean 核心库并打开编译器命名空间
{"cmd": "import Lean"}
{"cmd": "open Lean.Compiler", "env": 0}

# 使用 unsafe 定义包含 sorry 的示例
{"cmd": "unsafe example : ◾ := sorry", "env": 1}

# 保存环境状态
{"pickleTo": "test/f.olean", "env": 1}
```

导入模块、使用 unsafe 关键字，以及将环境状态保存到文件。输出中包含了一些编译器的追踪信息（使用 `traces` 字段）和重写规则的应用过程。

### Pickle 示例：加载环境并定义 unsafe 示例

```python
# 从文件加载环境
{"unpickleEnvFrom": "test/f.olean"}

# 在加载的环境中定义不安全示例
{"cmd": "unsafe example : ◾ := sorry", "env": 0}
{"sorries": [{"proofState": 0, "goal": "⊢ Nat"}...]}
```

从持久化文件加载环境，并在该环境中定义一个带有 `unsafe` 标记的示例。


## Mathlib 示例

以下示例涉及 Mathlib 依赖。

### 数学定理示例：代数运算与 pickle

```python
# 导入必要的库
{"cmd": "import Mathlib\nopen BigOperators\nopen Real\nopen Nat"}
{"env": 0}

# 定义数学定理
{"cmd": "theorem mathd_algebra_455\n  (x : Nat)\n  (h : 2 * (2 * (2 * (2 * x))) = 48) :\n  x = 3 := by sorry", "env": 0}
{"sorries": [{"proofState": 0, "goal": "..."}...]}

# 保存证明状态
{"pickleTo": "test/pickle.olean", "proofState": 0}
```

设置一个包含数学运算的定理，并使用 pickle 保存证明状态，以便后续继续完成证明。

### Pickle 示例：加载已保存的证明状态

```python
# 从文件加载证明状态
{"unpickleProofStateFrom": "test/pickle.olean"}
{"sorries": [{"proofState": 0, "goal": "x : Nat\n⊢ x + 1 > x"}...]}

# 应用数值规范化策略
{"tactic": "norm_num at h", "proofState": 0}
{"proofState": 1, "goals": [
  "case zero\n⊢ 0 + 1 > 0",
  "case succ\nx : Nat\nhx : x + 1 > x\n⊢ x + 1 + 1 > x + 1"]}
```

从已保存的证明状态文件中恢复，并继续使用 `norm_num` 策略进行数值规范化。

### 复杂示例：实数分析中的指数函数估计

```python
# 导入数学库并设置幂运算符号
{"cmd": "import Mathlib\nopen Real\nlocal macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)"}
{"env": 0}

# 证明指数函数的近似估计定理
{"cmd": "example {n} {x a b : ℝ} (m : ℕ) (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm) 
        (h : |x| ≤ 1) (e : |1 - a| ≤ b - |x| / rm * ((rm + 1) / rm)) : 
        |exp x - expNear n x a| ≤ |x| ^ n / n.factorial * b := 
        by apply Real.exp_approx_end' m e₁ rm er h e", 
 "env": 0}
```

一个关于指数函数近似估计的复杂定理，使用 `Real.exp_approx_end'` 完成证明。

### 策略示例：数学归纳法

```python
# 导入必要的策略库
{"cmd": "import Mathlib.Tactic.Cases"}
{"env": 0}

# 使用归纳法证明自然数性质
{"cmd": "example {x : Nat} : x + 1 > x := by\n  induction' x with x hx", "env": 0}
{"sorries": [{"proofState": 0, 
  "goal": "x : ℕ\nh : 2 * (2 * (2 * (2 * x))) = 48\n⊢ x = 3"}...]}
```

使用 `induction'` 策略对自然数进行归纳证明。

### 数论定理示例：使用内置策略

```python
# 导入必要的库
{"cmd": "import Mathlib.Algebra.BigOperators.Group.Finset\n..."}
{"env": 0}

# GCD 计算示例
{"cmd": "theorem mathd_numbertheory_188 : Nat.gcd 180 168 = 12 := by norm_num"}

# 计算真因子之和
{"cmd": "theorem mathd_numbertheory_403 : ∑ k in (Nat.properDivisors 198), k = 270 := by simp..."}

# 数列求和取模
{"cmd": "theorem mathd_numbertheory_109 : (∑ k in Finset.Icc 1 100, v k) % 7 = 4 := by simp_rw..."}
```

使用 Lean 的内置策略（`norm_num`, `simp`）来证明数论相关的定理，包括 GCD 计算、因子求和和模运算。

### 示例：归纳法框架

```python
# 导入策略库
{"cmd": "import Mathlib.Tactic.Cases"}
{"env": 0}

# 使用归纳法证明自然数性质
{"cmd": "example {x : Nat} : x + 1 > x := by\n  induction' x with x hx\n  all_goals sorry", "env": 0}
{"env": 0}
```

使用 `induction'` 策略设置归纳证明的基本框架。虽然这里用 `sorry` 跳过了具体证明步骤，但展示了归纳证明的基本结构。

### 策略示例：使用 simpa 策略

```python
# 创建 False 的示例证明
{"cmd": "example : False := by sorry"}
{"sorries": [{"proofState": 0, "goal": "⊢ False"}...]}

# 使用 simpa 策略
{"tactic": "simpa using show False by done", "proofState": 0}
{"sorries": [...], "proofState": 3, "goals": [
  "case pos\nx : ℝ\nh0 : |x| > 1...",
  "case neg\nx : ℝ\nh0 : |x| > 1..."]}
```

使用 `simpa` 策略简化证明目标，并通过 `show` 指定中间结果。

### 策略示例：使用归纳法证明

```python
# 导入 Mathlib 并定义定理
{"cmd": "import Mathlib"}
{"env" : 0, "cmd": "theorem foo (x : Nat) : x = x := by sorry"}

# 方式一：使用 induction 后逐步处理
{"proofState" : 0, "tactic": "induction x"}        # 归纳
{"proofState" : 1, "tactic": "next => rfl"}        # 处理下一个分支

# 方式二：使用 induction with 模式匹配语法
{"proofState" : 0, "tactic": "induction x with\n| zero => sorry\n| succ x => sorry"}
```

两种使用归纳法的方式：逐步处理和模式匹配语法。两种方式都会生成基础情况和归纳步骤的证明目标。

### 数学示例：实数绝对值的讨论

```python
# 导入数学库并打开实数命名空间
{"cmd": "import Mathlib\nopen Real"}

# 定义关于实数绝对值的命题
{"cmd": "example {x : ℝ} (h0: |x| > 1) : (x < 0) ∨ (2 * x > 2) := by sorry", "env": 0}
{"sorries": [{"proofState": 0, "goal": "⊢ False"}...]}

# 尝试使用多个辅助引理和分类讨论
{"tactic": "on_goal 1 =>\n  have h1 : x = x := by sorry\n  have h2 : x = x := by sorry\n  by_cases h3 : x < 0", "proofState": 0}
{"proofState": 1, "messages": [{"data": "unsolved goals\n⊢ False"}...]}
```

处理涉及实数绝对值的命题，使用 `have` 引入辅助引理和 `by_cases` 进行分类讨论（虽然这个尝试未能完成证明）。

### 策略示例：使用归纳法证明

```python
# 导入策略库
{"cmd": "import Mathlib.Tactic.Cases"}
{"env": 0}

# 创建关于自然数的示例定理
{"cmd": "example {x : Nat} : x + 1 > x := by sorry", "env": 0}

# 应用归纳法策略，生成两个子目标
{"tactic": "induction' x with x hx", "proofState": 0}
{"messages": [{"data": "unsolved goals\n
  case zero\n⊢ 0 + 1 > 0\n
  case succ\nx : Nat\nhx : x + 1 > x\n⊢ x + 1 + 1 > x + 1"}...]}
```

使用 `induction'` 策略对自然数进行归纳证明，生成基础情况和归纳步骤两个子目标。

### 导入示例：保存数学库依赖环境

```python
# 导入数学库相关模块
{"cmd": "import Mathlib\nopen BigOperators\nopen Real\nopen Nat"}
{"env": 0}

# 保存环境到文件
{"pickleTo": "test/H20231215.olean", "env": 0}
```

导入 Mathlib 相关模块并将环境持久化保存，这对于需要频繁使用数学库的证明很有帮助。

### 数学证明示例：计算复合函数

```python
# 导入必要的库
{"cmd": "import Mathlib\nopen Real\nopen Nat\nopen BigOperators"}

# 定义定理：关于复合函数 p(q(2)) 的计算
{"cmd" : "theorem mathd_algebra_35
  (p q : ℝ → ℝ)
  (h₀ : ∀ x, p x = 2 - x^2)
  (h₁ : ∀ x, x ≠ 0 -> q x = 6 / x) :
  p (q 2) = -7 := by sorry", "env": 0}

# 尝试证明步骤（未完成）
{"tactic": "have hQ : ∀ x, p x = 6 / x", "proofState": 0}
{"tactic": "  intro x", "proofState": 1}
{"tactic": "  calc p x = 6 / x * p x := h₀ (x)...", "proofState": 2}
```

一个数学证明的开始，涉及实数函数的复合计算，尽管证明尚未完成。

### 示例：使用已保存的环境状态

```python
# 加载保存的环境状态
{"unpickleEnvFrom": "test/H20231215.olean"}
{"env": 0}

# 在加载的环境中定义新定理
{"cmd": "theorem mathd_numbertheory_739 :\n  9! % 10 = 0 := by sorry", "env": 0}
{"env": 1}
```

使用 pickle 功能加载预先保存的环境状态，并在其基础上定义新的定理。

### exact? 策略示例：自动推导

```python
# 导入 Mathlib
{"cmd": "import Mathlib"}

# 测试简单定理：0 < 1
{"cmd": "theorem test : 0 < 1 := by sorry", "env": 0}
{"tactic": "exact?", "proofState": 0}  # exact? 自动找到证明

# 测试不可能的定理：3 = 7
{"cmd": "theorem test : 3 = 7 := by sorry", "env": 0}
{"tactic": "exact?", "proofState": 2}   # exact? 无法找到证明
```

`exact?` 策略的自动推导能力：对于显然成立的命题能自动找到证明，对于明显错误的命题则无法完成证明。



