# PyPantograph

本文档翻译自[PyPantograph用户文档](https://centaur.stanford.edu/PyPantograph/intro.html)，仅作介绍用，详细API请参考原始文档。

# 介绍

这是 Pantograph，一个用于 Lean 4 的机器对机器交互接口。它的主要目的是训练和评估定理证明智能体。主要特性包括：

1. 通过 Python 库、REPL 或 C 库进行接口交互
2. 结合基于表达式和基于策略的证明方式
3. Pantograph 设计时考虑了便于搜索的需求。定理证明智能体可以同时探索证明的多个分支。
4. 处理元变量耦合
5. 读取/添加环境中的符号
6. 提取策略训练数据
7. 支持草稿功能

## 名称由来

Pantograph 这个名字有双关含义：

* Pantograph 是一种用于复制书写内容的仪器。当智能体探索庞大的证明搜索空间时，Pantograph 记录当前状态以确保证明的正确性。
* Pantograph 也是电力机车的受电弓设备，向机车供应电力。相比之下，相对简单的 Pantograph 软件为定理证明项目提供动力。

## 设计理念

Lean 4 的接口不适合搜索。熟悉 Coq 的读者可能知道，Coq Serapi 被 CoqLSP 替代。作者认为这是一个错误。一个适合人工操作员编写证明的接口，往往并不适合自动搜索。

Pantograph 的大部分业务逻辑均用 Lean 编写，实现了数据提取和证明搜索组件间更紧密的耦合。

## 注意事项与限制

Pantograph 并不完全模仿 Lean LSP 的行为，这样才能提供更大的灵活性。为了支持树形搜索，Pantograph 有时必须区别于 Lean 的行为，但绝不以牺牲证明正确性为代价。

* 当 Lean LSP 报“无法综合占位符”时，意味着人工操作员需要手动将光标移至占位符并输入正确表达式。因此此错误不应终止证明过程，占位符应被视为一个目标。
* 当 Lean LSP 报“未解决的目标”时，意味着证明在 `by` 块结束时未能完成。Pantograph 会在此情况下报错，因为这表明一个证明搜索分支已终止。
* `pick_goal` 或 `swap` 无法使用，因为它们与树形搜索范式相悖。但若有策略能对多个目标同时执行非平凡操作，此限制可放宽，但会给用户带来较大管理负担。

Pantograph 无法执行 Lean 本身约束的操作，包括：

* 若策略丢失元变量追踪，直到证明搜索结束才会被发现，这属于策略本身的缺陷。
* 无法为策略执行设定超时，未来可能会改进。
* 解析错误通常无法转成目标（例如 `def mystery : Nat := :=`），因 Lean 的解析系统限制。

每个 Pantograph 版本都锚定在 `src/lean-toolchain` 中指定的 Lean 版本。如有需求，可以将功能回移植到旧版本 Lean。

## 参考文献

[论文链接](https://arxiv.org/abs/2410.16429)

```bib
@misc{pantograph,
      title={Pantograph: A Machine-to-Machine Interaction Interface for Advanced Theorem Proving, High Level Reasoning, and Data Extraction in Lean 4},
      author={Leni Aniva and Chuyue Sun and Brando Miranda and Clark Barrett and Sanmi Koyejo},
      year={2024},
      eprint={2410.16429},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/2410.16429},
}
```


# 安装与配置指南

## 安装步骤

1. 安装 `poetry`。

2. 执行命令构建 Pantograph 的 wheel 包：

   ```sh
   poetry build
   ```

   构建完成后，会在 `dist` 目录生成 Pantograph 的 wheel 文件，可以用于安装。

3. 在下游项目的 `pyproject.toml` 中添加依赖，例如：

   ```toml
   pantograph = { file = "path/to/wheel/dist/pantograph-0.3.0-cp312-cp312-manylinux_2_40_x86_64.whl" }
   ```

4. 运行示例和实验，先进入 poetry shell 环境：

   ```sh
   poetry install
   poetry shell
   ```

   这会启动一个包含开发包的环境，方便进行交互操作。

## 使用 Pantograph 服务器

Pantograph 中所有与 Lean 的交互都通过 `Server` 类完成。创建服务器实例的示例代码：

```python
from pantograph import Server
server = Server()
```

## Lean 依赖配置

通过默认的 `Server()` 创建的服务器，足以完成依赖于 Lean 自带的 `Init` 库的基础定理证明任务。若需要使用第三方或非内置库，如 Aesop 或 Mathlib4，则需要额外配置。

使用外部 Lean 依赖（例如 [Mathlib4](https://github.com/leanprover-community/mathlib4)）时，Pantograph 依赖已有的 Lean 仓库。创建仓库的具体说明见官方文档：[Lean4 Setup](https://docs.lean-lang.org/lean4/doc/setup.html#lake)。

创建仓库后，进入该仓库目录，执行：

```sh
lake build
```

该命令会编译仓库内所有文件。每次仓库文件修改后都需要执行此命令。

启动 Pantograph 服务器时，传入该 Lean 仓库路径：

```python
server = Server(project_path="./path-to-lean-repo/")
```

完整示例请参阅 `examples/` 目录。

## 服务器参数说明

* `core_options`：传递给 Lean 内核的选项，例如，Lean 中的 `set_option pp.all true` 对应传入参数 `pp.all=true`。
* `options`：传递给 Pantograph 的自定义选项，详见下文。
* `timeout`：服务器最大等待响应时间（秒），若 Lean 项目加载时间较长，可适当调大。

## Jupyter 环境使用提示

在 Jupyter 等异步环境中，建议使用异步版本接口，例如：

```python
server = await Server.create()
unit, = await server.load_sorry_async(sketch)
print(unit.goal_state)
```

## Pantograph 选项详解

* `automaticMode`：布尔值，设为 `false` 以关闭自动目标续写功能。
* `timeout`：正整数，设定策略执行的超时时间。
* `printDependentMVars`：布尔值，设为 `true` 以显式存储目标间的依赖关系。


# 目标与策略（Goals and Tactics）

在 Pantograph 中执行策略非常简单。要开始一个证明，调用 `Server.goal_start` 函数并传入一个表达式。

```python
from pantograph import Server
from pantograph.expr import TacticHave, TacticCalc, TacticExpr

server = Server()
state0 = server.goal_start("forall (p q: Prop), Or p q -> Or q p")
```

这会创建一个目标状态，包含有限数量的目标。在这个例子中，由于是状态的开始，只有一个目标。

```python
print(state0)
```

```
⊢ forall (p q: Prop), Or p q -> Or q p
```

要对目标状态执行策略，使用 `Server.goal_tactic`。该函数接收一个目标 ID 和一个策略。大多数 Lean 策略都是字符串形式。

```python
state1 = server.goal_tactic(state0, goal_id=0, tactic="intro a")
print(state1)
```

```
a : Prop
⊢ ∀ (q : Prop), a ∨ q → q ∨ a
```

执行策略会产生一个新的目标状态。如果该目标状态没有目标，证明即完成。你可以用 `str()` 方法获得目标的常规形式：

```python
str(state1.goals[0])
```

```
'a : Prop\n⊢ ∀ (q : Prop), a ∨ q → q ∨ a'
```

## 错误处理与垃圾回收（Error Handling and GC）

当策略执行失败时，会抛出异常：

```python
try:
    state2 = server.goal_tactic(state1, goal_id=0, tactic="assumption")
    print("Should not reach this")
except Exception as e:
    print(e)
```

```
["tactic 'assumption' failed\na : Prop\n⊢ ∀ (q : Prop), a ∨ q → q ∨ a"]
```

一个没有任何目标的状态被认为是已解决状态：

```python
state0 = server.goal_start("forall (p : Prop), p -> p")
state1 = server.goal_tactic(state0, goal_id=0, tactic="intro")
state2 = server.goal_tactic(state1, goal_id=0, tactic="intro h")
state3 = server.goal_tactic(state2, goal_id=0, tactic="exact h")
print(state3)
```

```
GoalState(state_id=5, goals=[], _sentinel=[0, 1])
```

请适时调用 `server.gc()` 删除未使用的目标。

```python
server.gc()
```

## 特殊策略

Lean 对某些策略有特殊处理，包括 `have`、`let`、`calc`。执行这些策略时，需创建相应的 `TacticHave`、`TacticLet`、`TacticCalc` 实例并传入 `server.goal_tactic`。

从技术上讲，`have` 和 `let` 在 Lean 中并非真正的策略，因此其执行需要特殊关注。

```python
state0 = server.goal_start("1 + 1 = 2")
state1 = server.goal_tactic(state0, goal_id=0, tactic=TacticHave(branch="2 = 1 + 1", binder_name="h"))
print(state1)
```

输出示例：

```
⊢ 2 = 1 + 1
h : 2 = 1 + 1
⊢ 1 + 1 = 2
```

`TacticExpr` “策略”会解析一个表达式并将其赋值给当前目标。这利用了 Lean 的类型统一系统，表达能力与 Lean 表达式相同。Mathlib4 中许多证明是表达式和策略混合写成的。

```python
state0 = server.goal_start("forall (p : Prop), p -> p")
state1 = server.goal_tactic(state0, goal_id=0, tactic="intro p")
state2 = server.goal_tactic(state1, goal_id=0, tactic=TacticExpr("fun h => h"))
print(state2)
```

要执行 `conv` 策略，使用 `server.goal_conv_begin` 进入目标的 conv 模式，使用 `server.goal_conv_end` 退出 conv 模式。Pantograph 会在 conv 模式下的每个策略执行后提供交互反馈。

# 搜索

Pantograph 支持基本的证明搜索。在此模式下，Pantograph 将目标视为与或树（and-or tree）上的节点。用户需要提供一个智能体，该智能体应实现两个函数：

- **Tactic**：应对某个目标使用哪种策略？  
- **Guidance**：某个目标的搜索优先级是多少？

用户的智能体应继承自 `pantograph.search.Agent`。下面是一个暴力穷举的智能体示例：

```python
from typing import Optional
import collections
from pantograph import Server
from pantograph.search import Agent
from pantograph.expr import GoalState, Tactic

class DumbAgent(Agent):

    def __init__(self):
        super().__init__()

        self.goal_tactic_id_map = collections.defaultdict(lambda : 0)
        self.intros = [
            "intro",
        ]
        self.tactics = [
            "intro h",
            "cases h",
            "apply Or.inl",
            "apply Or.inr",
        ]
        self.no_space_tactics = [
            "assumption",
        ]

    def next_tactic(
            self,
            state: GoalState,
            goal_id: int,
    ) -> Optional[Tactic]:
        key = (state.state_id, goal_id)
        i = self.goal_tactic_id_map[key]

        target = state.goals[goal_id].target
        if target.startswith('∀'):
            tactics = self.intros
        elif ' ' in target:
            tactics = self.tactics
        else:
            tactics = self.no_space_tactics

        if i >= len(tactics):
            return None

        self.goal_tactic_id_map[key] = i + 1
        return tactics[i]
```

执行搜索：

```python
server = Server()
agent = DumbAgent()
goal_state = server.goal_start("∀ (p q: Prop), Or p q -> Or q p")
agent.search(server=server, goal_state=goal_state, verbose=False)
```

```
SearchResult(n_goals_root=1, duration=0.7717759609222412, success=True, steps=16)
```

## 自动模式与手动模式

智能体会选择一个目标并在该目标上执行策略。那么其它未被选择的目标怎么办？默认情况下，服务器运行在自动模式（automatic mode）。在自动模式下，所有其他目标会自动被继承到子状态中，因此智能体可以在当前状态没有剩余目标时，判定证明已完成。

部分用户可能希望手动处理兄弟目标，例如 Aesop 对元变量耦合的处理不是自动完成的。要实现手动管理，可在创建服务器时传入参数：

```python
server = Server(options={"automaticMode": False})
```


# 数据提取

```python
import os
from pathlib import Path
from pantograph.server import Server
```

## 策略调用数据提取（Tactic Invocation）

Pantograph 可以从 Lean 文件中提取策略调用数据。策略调用由一个三元组组成，包含策略执行前的目标状态、策略执行后的目标状态，以及将前状态转变为后状态的策略。

使用 `server.tactic_invocations(file_name)` 方法，传入 Lean 文件路径即可提取策略调用数据。

示例代码：

```python
project_path = Path(os.getcwd()).parent.resolve() / 'examples/Example'
print(f"$PWD: {project_path}")

server = Server(imports=['Example'], project_path=project_path)
units = server.tactic_invocations(project_path / "Example.lean")
```

输出示例：

```
$PWD: /home/aniva/Projects/atp/PyPantograph/examples/Example
```

该函数返回一个 `CompilationUnit` 对象列表，对应输入 Lean 文件中的每个编译单元。为提升性能，仅加载文本边界到 `CompilationUnit` 中。

可以通过以下方式查看每个编译单元的文本内容：

```python
with open(project_path / "Example.lean", 'rb') as f:
    content = f.read()
    for i, unit in enumerate(units):
        print(f"#{i}: [{unit.i_begin},{unit.i_end}]")
        unit_text = content[unit.i_begin:unit.i_end].decode('utf-8')
        print(unit_text)
```

示例输出：

```
#0: [14,85]
/-- Ensure that Aesop is running -/
example : α → α :=
  by aesop


#1: [85,254]
example : ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  -- Here are some comments
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption
```

每个 `CompilationUnit` 包含一个 `TacticInvocations` 列表，记录多个策略调用。每个调用包含：

* `.before`：策略执行前的目标状态
* `.after`：策略执行后的目标状态
* `.tactic`：执行的策略

```python
for i in units[0].invocations:
    print(f"[Before]\n{i.before}")
    print(f"[Tactic]\n{i.tactic} (using {i.used_constants})")
    print(f"[After]\n{i.after}")
```
```
[Before]
α : Sort ?u.7
⊢ α → α
[Tactic]
aesop (using [])
[After]
```
```python
for i in units[1].invocations:
    print(f"[Before]\n{i.before}")
    print(f"[Tactic]\n{i.tactic} (using {i.used_constants})")
    print(f"[After]\n{i.after}")
```
```
[Before]
⊢ ∀ (p q : Prop), p ∨ q → q ∨ p
[Tactic]
intro p q h (using [])
[After]
p q : Prop
h : p ∨ q
⊢ q ∨ p
[Before]
p q : Prop
h : p ∨ q
⊢ q ∨ p
[Tactic]
cases h (using ['Eq.refl', 'Or'])
[After]
case inl
p q : Prop
h✝ : p
⊢ q ∨ p
case inr p q : Prop h✝ : q ⊢ q ∨ p
[Before]
case inl
p q : Prop
h✝ : p
⊢ q ∨ p
[Tactic]
apply Or.inr (using ['Or.inr'])
[After]
case inl.h
p q : Prop
h✝ : p
⊢ p
[Before]
case inl.h
p q : Prop
h✝ : p
⊢ p
[Tactic]
assumption (using [])
[After]

[Before]
case inr
p q : Prop
h✝ : q
⊢ q ∨ p
[Tactic]
apply Or.inl (using ['Or.inl'])
[After]
case inr.h
p q : Prop
h✝ : q
⊢ q
[Before]
case inr.h
p q : Prop
h✝ : q
⊢ q
[Tactic]
assumption (using [])
[After]
```


# 草稿功能
Pantograph 支持草稿功能（技术上称为草图步骤，即 Draft-Sketch-Prove）。Pantograph 的草稿功能更加强大：

- 在证明的任意位置，你可以用 `sorry` 替换一个表达式，`sorry` 会变成一个新的目标（goal）。
- 任何类型错误也会被转化为目标。
- 为了检测是否发生了类型错误，用户可以查看每个编译单元（compilation unit）中的消息。

## 编译单元（Compilation Units）

在此必须介绍“编译单元”的概念。每个 Lean 定义、定理、常量等，都是一个编译单元。当 Pantograph 从 Lean 源代码提取数据时，会将数据划分成这些编译单元。

例如，考虑下面由语言模型证明器生成的草稿（sketch）：  

```lean
by
   intros n m
   induction n with
   | zero =>
     have h_base: 0 + m = m := sorry
     have h_symm: m + 0 = m := sorry
     sorry
   | succ n ih =>
     have h_inductive: n + m = m + n := sorry
     have h_pull_succ_out_from_right: m + Nat.succ n = Nat.succ (m + n) := sorry
     have h_flip_n_plus_m: Nat.succ (n + m) = Nat.succ (m + n) := sorry
     have h_pull_succ_out_from_left: Nat.succ n + m = Nat.succ (n + m) := sorry
     sorry
```

在某些情况下，我们希望自动解决 `sorry` 生成的目标，这时可以使用 hammer 策略来完成。具体做法是通过草稿功能（drafting）实现：

- 首先使用 `load_sorry` 加载带有 `sorry` 的目标陈述。  
- 强烈建议在一个定理陈述中不要写超过一个 `sorry`，以保证证明的清晰性和可维护性。  

```python
from pantograph import Server

sketch = """
theorem add_comm_proved_formal_sketch : ∀ n m : Nat, n + m = m + n := sorry
"""
server = await Server.create()
unit, = await server.load_sorry_async(sketch)
print(unit.goal_state)
```
```
payload: {"printDependentMVars": true}
payload: {"file": "\ntheorem add_comm_proved_formal_sketch : ∀ n m : Nat, n + m = m + n := sorry\n", "invocations": false, "sorrys": true, "newConstants": false, "readHeader": false, "inheritEnv": false, "typeErrorsAsGoals": false}

⊢ ∀ (n m : Nat), n + m = m + n
```

更详细的示例请参见 `experiments/dsp` 目录。
```python
step = """
by
   -- Consider some n and m in Nats.
   intros n m
   -- Perform induction on n.
   induction n with
   | zero =>
     -- Base case: When n = 0, we need to show 0 + m = m + 0.
     -- We have the fact 0 + m = m by the definition of addition.
     have h_base: 0 + m = m := sorry
     -- We also have the fact m + 0 = m by the definition of addition.
     have h_symm: m + 0 = m := sorry
     -- Combine facts to close goal
     sorry
   | succ n ih =>
     sorry
"""
from pantograph.expr import TacticDraft
tactic = TacticDraft(step)
state1 = await server.goal_tactic_async(unit.goal_state, 0, tactic)
print(state1)
```
```
payload: {"stateId": 0, "goalId": 0, "draft": "\nby\n   -- Consider some n and m in Nats.\n   intros n m\n   -- Perform induction on n.\n   induction n with\n   | zero =>\n     -- Base case: When n = 0, we need to show 0 + m = m + 0.\n     -- We have the fact 0 + m = m by the definition of addition.\n     have h_base: 0 + m = m := sorry\n     -- We also have the fact m + 0 = m by the definition of addition.\n     have h_symm: m + 0 = m := sorry\n     -- Combine facts to close goal\n     sorry\n   | succ n ih =>\n     sorry\n"}
n : Nat
m : Nat
⊢ 0 + m = m
n : Nat
m : Nat
h_base : 0 + m = m
⊢ m + 0 = m
n : Nat
m : Nat
h_base : 0 + m = m
h_symm : m + 0 = m
⊢ 0 + m = m + 0
n✝ : Nat
m : Nat
n : Nat
ih : n + m = m + n
⊢ n + 1 + m = m + (n + 1)
```
