# Pantograph

相关链接:

- Lean 项目地址：https://github.com/lenianiva/Pantograph
- Python 封装：https://github.com/stanford-centaur/PyPantograph

Pantograph 是一个为 Lean 4 开发的交互工具，它主要提供了执行证明、构建表达式以及检查项目符号列表等功能，目标是支持机器学习应用场景。

创建 Pantograph 的主要动机是构造一个接口，使机器学习系统能够轻松利用这种逐步扩展的树结构进行数学推理。Pantograph 的潜在应用包括自动验证程序生成、为语言模型提供严谨推理以及数学结果的自动形式化。

**注意：如果你在寻找在 Python 中使用本工具与 Lean 4 交互的方法，请参阅 [PyPantograph](https://github.com/stanford-centaur/PyPantograph)**

## 名称

Pantograph 这个名字是双关语：
- Pantograph （缩放尺）指的是一种用来复制书写内容的仪器。当智能体在广阔的证明搜索空间中进行探索时，Pantograph 会记录当前状态，以确保证明的正确性。
- Pantograph （受电弓）也是电动车组列车上供电设备的名称，它为机车提供动力。相比之下，（相对）简单的 Pantograph 软件则为定理证明项目提供“动力”。

----------------------------

## 安装及使用

对于 Nix 用户，运行

``` sh
nix build .#{sharedLib,executable}
```

以构建共享库或可执行文件。

安装固定在 `lean-toolchain` 文件版本上的 `lake` 和 `lean`，然后运行

``` sh
lake build
```

这将在 `.lake/build/bin/pantograph-repl` 中构建可执行文件。

### 可执行文件使用方法

``` sh
pantograph-repl MODULES|LEAN_OPTIONS
```

`pantograph-repl` 可执行文件必须传入要导入的模块列表。它还可以接受形如 `--key=value` 的 Lean 选项，例如 `--pp.raw=true`。

REPL 循环接受单行 JSON 输入命令，并输出 `Error:`（表示命令格式错误）或者输出一个 JSON 返回值以表示命令执行结果。命令可以以以下两种格式传递：
```
command { ... }
{ "cmd": command, "payload": ... }
```
可用命令列表可在 `Pantograph/Protocol.lean` 中及下文中找到。空命令会中止 REPL。

示例：（约 5 千个符号）
```
$ pantograph Init
env.catalog
env.inspect {"name": "Nat.le_add_left"}
```
示例（使用 `mathlib4`，约 90 千个符号，可能会出现堆栈溢出问题，请参见故障排除）
```
$ pantograph Mathlib.Analysis.Seminorm
env.catalog
```
证明定理示例：（或者使用 `goal.start {"copyFrom": "Nat.add_comm"}` 来准备证明）
```
$ pantograph Init
goal.start {"expr": "∀ (n m : Nat), n + m = m + n"}
goal.tactic {"stateId": 0, "goalId": 0, "tactic": "intro n m"}
goal.tactic {"stateId": 1, "goalId": 0, "tactic": "assumption"}
goal.delete {"stateIds": [0]}
stat {}
goal.tactic {"stateId": 1, "goalId": 0, "tactic": "rw [Nat.add_comm]"}
stat
```
其中，应用 `assumption` 应当会导致失败。

有关命令列表，请参阅 [REPL 文档](https://github.com/lenianiva/Pantograph/blob/dev/doc/repl.md)。

### 项目环境

要在项目环境中使用 Pantograph，请设置 `LEAN_PATH` 环境变量，使其包含 Lean 库的路径。库必须提前构建。例如，如果 `mathlib4` 存放在 `../lib/mathlib4`，环境可以这样设置：

``` sh
LIB="../lib"
LIB_MATHLIB="$LIB/mathlib4/.lake"
export LEAN_PATH="$LIB/mathlib4/build/lib:$LIB_MATHLIB/aesop/build/lib:$LIB_MATHLIB/Qq/build/lib:$LIB_MATHLIB/std/build/lib"

LEAN_PATH=$LEAN_PATH build/bin/pantograph $@
```
任何项目的 `$LEAN_PATH` 可执行文件可以通过下面的命令提取：
``` sh
lake env printenv LEAN_PATH
```

### 故障排除

如果 Lean 在打印目录时遇到堆栈溢出问题，请在运行 Lean 之前执行：
```sh
ulimit -s unlimited
```

### 库用法

`Pantograph/Library.lean` 暴露了一系列接口，通过这些接口可以通过 FFI 调用 Pantograph，其功能与上面 REPL 命令相对应。建议通过此 FFI 调用 Pantograph，因为这样可以大大提高速度。

可执行文件可以直接使用，但链接共享库则需要 `lean-all` 的存在。注意，可执行文件（REPL）命令与库函数之间并不是一一对应的。

可通过 `pantograph_init_search` 函数注入任意项目路径。

### 开发

Nix flake 中提供了一个 Lean 开发 shell。

#### 测试

测试基于 `LSpec`。运行测试可以使用：
``` sh
nix flake check
```
或者
``` sh
lake test
```
你也可以通过指定前缀来运行单个测试：
``` sh
lake test -- "Tactic/No Confuse"
```

----------------------------

## 特性

Pantograph 的主要贡献包括：

- 与以往工作不同，用户可以决定独立解决目标。这使得诸如蒙特卡罗树搜索（MCTS）之类的更强大搜索算法成为可能。在此过程中，Pantograph 处理了元变量耦合 (metavariable
coupling) 问题，这一现象使树搜索复杂化。
- 与 LeanDojo 相比，Pantograph 支持使用 `have`、`let`、`conv` 和 `calc`。
- Pantograph 完全支持基本数据抽取任务（例如，它可以抽取策略执行前后的目标状态，而这些通常在原始 Lean 4 脚本中不可用）。此外，Pantograph 引入了几项新颖的数据抽取能力，包括能够提取带有注释的完整证明脚本（可用于自动形式化等任务），以及将证明表示抽取为程序的重要能力，从而实现证明的一次性预测。
- Pantograph 提供了部分执行 `conv` 和 `calc` 策略时的反馈，这在之前的工作中是无法实现的。
- Pantograph 允许用户恢复包含 Lean 4 中 `sorry` 关键字的不完整证明。这对机器学习模型十分有用，因为它们通常先生成证明草案，然后再完善证明细节。

### 基于表达式和策略的证明

Pantograph 通过提供一个自定义的 expr 策略支持表达式证明与策略证明之间的无缝切换。该策略接受一个表达式 `e[?1, ?2,...]` 并将其赋值给当前目标。占位项 ?1、?2 ... 随后成为新的目标。

证明可以从三种视角来观察：

- 演示视角：为展示和验证而书写的证明。此视角中不存在耦合，可能包含在通读整个证明之前无法看出来源的复杂界限值。
- 搜索视角：证明作为证明搜索智能体在搜索过程中所经历的轨迹，可能包含回溯、耦合和目标选择。
- 内核视角：证明作为一组元变量。

Pantograph 允许智能体在搜索视角中操作，并在内部以内核视角处理证明。

Lean 4 的人类操作员通常依赖 `conv` 和 `calc`，用于组合多个其他策略，尽管这些策略本质上可以通过一次性提供完整的组合策略序列来执行，但人类依赖其交互接口逐步探索可能的策略序列，并在每一步获得反馈。Pantograph 提供了一个名为 `goal.tactic` 的自定义策略，可以部分执行 `conv` 或 `calc` 策略并提供该部分执行的反馈。例如，考虑下面使用 `calc` 策略的情况，`calc` 在 Lean 4 中用于组合一系列传递性步骤。

```lean
example (a b c : Nat) : a + b = b + c := by
  calc
   a + b = a + a := sorry
   _ = b + b := sorry
   sorry
```

此处，目标 `a + b = b + c` 不能通过 `calc` 证明，但用户仍可以先执行第一行并观察其结果。在这种情况下，仅执行第一行后生成的新目标为：

```lean
a b c : Nat
⊢ a + a = b + c
```

Pantograph 支持这种部分执行模型，并能返回上述新目标。

Pantograph 同时支持 `have` 和 `let` 策略。这些策略在局部范围内定义临时表达式，是手写证明时不可或缺的。例如，考虑下面的代码片段：

```lean
example (n : Nat) : n + 0 = 0 + n := by
  have h1 : n + 0 = n := sorry
  sorry

```
使用 `have` 会引入一个新的表达式及对应的新目标。两个 `sorry` 分别对应两个目标，如下所示：

```lean
n : Nat
⊢ n + 0 = n

n : Nat
h1 : n + 0 = n
⊢ n + 0 = 0 + n
```

Pantograph 仓库中包含关于这些策略的文档和示例。

为了便于使用诸如蒙特卡罗树搜索之类的搜索方法，Pantograph 提供了一个接口用于增量执行策略。如果一个策略生成多个目标，则称之为分支策略。当证明状态中存在多个目标时，Pantograph 允许用户选择在其上应用策略的目标，这即是允许用户定义策略函数。

如果一个策略因某种原因无法执行，Pantograph 会输出与人类操作员在 Lean LSP 交互时看到的错误信息相对应的错误消息。

### 树搜索

树搜索是一种常见的搜索技术，并被 HyperTree、Aesop 等证明搜索方法使用。由于每个策略产生零个或多个目标，应用策略于目标构成的搜索结构可视为一棵“与-或树”（在没有元变量耦合的情况下，见第下节）。当当前证明状态存在多个目标时，Pantograph 允许用户选择下一个尝试的目标，即允许用户定义策略函数。

这自然引出了对兄弟目标命运的问题。假设当前证明状态中有两个目标 `[?1, ?2]`，用户对 `?1` 应用策略生成了 `?3`。那么 `?2` 的状态取决于自动模式选项。自动模式默认开启，这意味着兄弟目标会被保留到下一个证明状态。因此，在自动模式开启下，下一个证明状态包含 `[?3, ?2]`，所有目标均保持激活状态。如果用户关闭自动模式，则证明状态变为 `[?3]`，目标 `?2` 则变为休眠状态。休眠目标是当前证明状态中未出现的未赋值元变量。注意，休眠目标是 Pantograph 手动树搜索功能的产物：在使用 Lean 4 交互接口时不会出现。休眠目标必须由用户跟踪，或通过 `goal.continue` 命令重新引入证明状态。

简而言之，在自动模式下，策略执行后目标会立即继续。目标在自动模式下永不休眠。这为用户提供了类似 gym 的环境；而希望手动处理树搜索的用户则可禁用此模式。

### 元变量耦合

回顾，一个证明状态可能包含 0 个或多个目标，而元变量耦合指的是证明状态中目标之间的相互依赖。元变量耦合自然出现在许多情形中。例如，对目标 2 ≤ 5 应用 ≤ 的传递性公理，会产生如下目标：
```lean
?1 : 2 ≤ ?z
?2 : ?z ≤ 5
?z : ℕ
```
由于 `?z` 出现在这三个目标中，这些目标均相互耦合。这使得证明搜索复杂化，因为如果在某个目标中对 `z` 作出赋值，该赋值会传播到所有耦合的目标。在这种情况下，其它两个目标将不再耦合，但会包含 `z` 的赋值。

Pantograph 明确提供了哪些目标是耦合的。由于处理耦合有多种可能方法，如何处理耦合的选择留给用户。其中 Aesop 采用的一种方法是复制，即顺序解决耦合目标以避免冲突。

下图展示了上述证明的完整示例，使用自动模式关闭进行。应用传递性策略产生一个包含三个目标的证明状态。对 `?z` 目标使用 `exact 3` 策略后证明状态变为解决状态。然后应用 `goal.continue` 将目标 `?1` 和 `?2` 重新引入证明状态，此时它们不再耦合。随后，可以用如 `decide` 等额外策略分别消解它们。

![coupling](img\coupling.png)

### 环境

所有 Lean 4 的运行实例（包括通过 LSP 或 Pantograph 前端运行的实例）均维护着一个被称为“环境”的活跃符号库。Lean 4 内部将所有定理陈述和证明以表达式形式存储在环境中，无论它们如何构造。用户可以通过 `env.inspect` 命令抽取当前环境中任意定理的证明。

证明完成后，用户可以使用 `goal.print` 命令抽取根命题的证明表达式。然后，这些表达式可通过 `env.add` 命令重新插入当前环境。向环境中添加引理使其在未来证明中可作为步骤使用。注意，在不完整证明过程中无法向环境添加引理。

类似于 CoqGym，Pantograph 可选地通过开启 `printExprAST` 选项（通过 `options.set`）以 S 表达式格式输出证明表达式。用户还可以通过为 Pantograph REPL 提供命令行参数来更改 Lean 4 的表达式美化打印选项。例如，要关闭所有美化打印，可以使用 `--pp.all=true`。

### 策略训练数据

Lean 4 社区已经产生了多个包含人类书写形式化证明的大型定理集合，例如 Mathlib。这些集合可用于训练定理证明智能体。`frontend.process` 命令运行 Lean 4 编译器处理 Lean 4 文件，收集文件中所有策略，并以（执行前目标、执行后目标、策略）三元组形式返回。这些三元组以便于离线强化学习训练的格式呈现。Pantograph 还输出每个 Lean 4 命令在文件中的起始和结束位置的信息，便于用户处理注释或其它元数据。下面给出一个抽取的策略三元组示例：

```lean
{  "goalBefore": "⊢ ∀(p, q : Prop), p ∨ q → q ∨ p ",  "goalAfter": " p : Prop \n ⊢ ∀(q : Prop), p ∨ q → q ∨ p ",  "tactic": "intro p" }
```

### 草拟

草拟指的是一种定理证明技术，其起始步骤为生成证明大纲，而不是一步步构造完整证明。草拟证明首先以包含空洞的概览形式出现，之后通过证明证明中各空洞对应的具体目标来完成证明。例如，考虑在 Peano 算术中证明加法交换性的问题。一种方法是基于归纳证明，利用归纳假设 `n+m = m+n` 来证明归纳步 `m+(n+1) = (m+n)+1`。正如所述，该证明对 Lean 4 来说不够严格或详细，但可以写作草拟证明：
```lean
theorem add_comm : forall n m : Nat, n + m = m + n := by
  intros n m
  induction n with
  | zero =>
   have h_base : 0 + m = m := sorry
   
   have h_symm : m + 0 = m := sorry
   sorry
  | succ n ih =>
   have h_inductive : n + m = m + n := sorry
   have h_pull_succ_out_from_right : m + Nat.succ n = Nat.succ (m + n) := sorry
   sorry
```
上述证明中，空缺部分用 `sorry` 关键字标记。Pantograph 支持两种草拟方式。第一种方式是通过 `have` 策略。该策略引入一个引理或中间声明，并产生对应的新目标。

另一种草拟方式是通过 `sorry` 抽取。Pantograph 可以在证明或定义中查找所有 `sorry` 的出现，并将其转换为目标。例如，当上述 `add_comm` 被输入到 Pantograph 的 `frontend.process` 命令时，会生成如下目标列表：
```lean
m : Nat
⊢ 0 + m = m

m : Nat
h_base : 0 + m = m
⊢ m + 0 = m

m : Nat
h_base : 0 + m = m
h_symm : m + 0 = m
⊢ 0 + m = m + 0

m : Nat
n : Nat
ih : n + m = m + n
⊢ n + m = m + n

m : Nat
n : Nat
ih : n + m = m + n
h_inductive : n + m = m + n
⊢ m + n.succ = (m + n).succ

m : Nat
n : Nat
ih : n + m = m + n
h_inductive : n + m = m + n
h_pull_succ_out_from_right : m + n.succ = (m + n).succ
⊢ n + 1 + m = m + (n + 1)
```
用户随后可以对这些目标逐个执行策略。对于机器学习智能体来说，这一特性尤其有吸引力，因为它允许智能体（例如，大型语言模型）在不必深入探讨证明执行细节的情况下有效地草拟下一证明步骤。如果草图中存在无法修正的类型错误，Pantograph 会将 Lean 4 内核生成的错误转发给用户。

### 限制

Pantograph 受限于 Lean 提供的功能。例如，如果某个策略存在 bug 且舍弃了一个元变量，Pantograph 无法捕捉此问题直到证明结束。凡是 Lean 的类型系统无法表达的内容（例如，同伦类型论（HoTT））也无法在 Pantograph 中表达。由于 Pantograph 与 Lean 内部紧密耦合，当 Lean 发生重大版本更新时，更新 Pantograph 需要付出不小的工程努力。

此外，由于策略的用户定义特性，通过对象序列化（pickle）在 Pantograph 中分布式计算并不简单。例如，如果在两台机器上分别执行证明的两个分支，Pantograph 无法解决将两分支统一起来这一算法上十分困难的问题。

Pantograph 并不完全模仿 Lean LSP 的行为。完全复制 Lean LSP 的行为会限制其所提供的灵活性。为了支持树搜索，Pantograph 在某些时候必须与 Lean 的行为有所不同，但绝不会以牺牲证明正确性为代价。

- 当 Lean LSP 提示 “don't know how to synthesize placeholder”（不知道如何合成占位符）时，这表明人类操作员需要手动将光标移动到占位符处并输入正确的表达式。因此，这个错误不应中断证明过程，而应将该占位符转化为一个目标。
- 当 Lean LSP 提示 “unresolved goals”（未解决的目标）时，表示在 `by` 代码块结束时证明未能结束。Pantograph 在这种情况下会抛出错误，因为这表明某个证明搜索分支已经终止。
- `pick_goal` 或 `swap` 等命令无法使用，因为它们与树搜索范式相悖。然而，如果存在对多个目标同时执行非平凡操作的策略，这一限制可能在牺牲大量额外的用户管理开销的前提下得到放宽。

Pantograph 无法执行那些本质上受 Lean 限制的操作，包括：

- 如果某个策略失去了对元变量的跟踪，直到证明搜索结束时才会发现。这是策略本身的 bug。
- 执行策略的超时机制目前不可用，未来可能会有所变化。
- 由于 Lean 的解析系统原因，一般无法将解析错误（例如 `def mystery : Nat := :=`）转化为目标。
