# Duper

Duper 是一个自动生成证明的定理证明器，广泛类似于 Isabelle 的 `Metis`。Duper 主要由 Joshua Clune（GitHub: JOSHCLUNE）、Yicheng Qian（GitHub: PratherConid）和 Alex Bentkamp（GitHub: abentkamp）开发。目前它正在积极开发中，欢迎提交 Pull Request。如果有其他问题或错误报告，请随时在 [Lean Zulip](https://leanprover.zulipchat.com) 上联系 Joshua Clune。

## 将 Duper 添加到现有项目

要在现有的 Lean 4 项目中使用 Duper，首先将此包添加为依赖项。在你的 `lakefile.lean` 中添加：

```lean
require Duper from git "https://github.com/leanprover-community/duper.git" @ "v0.0.23"
```

然后，确保你的 `lean-toolchain` 文件包含与 Duper 相同的 Lean 4 版本，并且如果你的项目导入了 [batteries](https://github.com/leanprover-community/batteries)，则它使用与 Duper 相同版本的 batteries。这一步是必要的，因为 Duper 依赖于 batteries，因此如果你的项目尝试导入与 Duper 导入的 batteries 版本不同的版本，可能会引发错误。

完成这些步骤后，将以下代码添加到你的项目根目录（通常是 Main.lean）依赖的 Lean 文件中：

```lean
import Duper

example : True := by duper [*]
```

添加上述代码片段后，你可以通过在 VS Code 中重启 Lean 服务器（使用 Ctrl-Shift-P 或 Command-Shift-P 打开命令面板，然后选择命令“Lean 4: Server: Restart Server”）或在项目目录中运行 `lake build`。在 Mac 和 Linux 上，这两种方法应该都能正常工作，但不幸的是，某些 Windows 版本可能会在 `lake build` 时失败，并出现“too many exported symbols”错误。如果发生这种情况，Windows 用户仍然可以通过 VS Code 构建 Duper。

完成后，你可以通过确认 `True` 的目标已被 Duper 证明来检查 Duper 是否已成功导入。

## 在新项目中试验 Duper

要在新的 Lean 4 项目中使用 Duper，一种选择是简单地创建一个新项目，然后按照上述部分描述的步骤进行操作。但对于只想试验 Duper 的用户，我们创建了 [DuperDemo](https://github.com/JOSHCLUNE/DuperDemo)，这是一个导入了 Duper 和 Mathlib 的仓库，可以轻松地试验 Duper 的功能。

## 使用 Duper

Duper 是一个终端策略，它会查看当前的主要目标并解决它或抛出错误。在策略模式下调用 Duper 的语法是 `duper [facts] {options}`。`facts` 参数用于指示 Duper 应尝试使用哪些引理或命题来证明目标，而 `options` 参数用于指定如何调用 Duper。

### 事实

提供给 Duper 的 `facts` 用逗号分隔，可以包括：
- 本地上下文中的假设（类型为 `Prop`）
- 外部引理
- 定义（这将提示 Duper 使用每个提供的定义的定义方程）
- 递归器（这将提示 Duper 为每个提供的递归器生成定义方程）
- 符号 `*` 表示 Duper 应考虑当前本地上下文中的所有证明

如果从 Duper 调用中省略了 `[facts]` 参数，则 Duper 将仅推理目标，这意味着 `by duper` 等同于 `by duper []`。要让 Duper 推理整个目标，包括本地上下文中的所有假设，我们建议使用 `by duper [*]`。当 Duper 获得一组可以用于证明目标的最小事实时，它的表现最好，并且当使用更具体的引理时，它的表现也更好（例如，如果给定 `Nat.mul_one` 而不是 `mul_one`，Duper 的表现通常会更好，尽管它能够处理两者）。我们尚未将 Duper 连接到相关性过滤器，因此目前需要手动提供 Duper 所需的所有引理，尽管我们希望在未来改进这一状况。

### 选项

提供给 Duper 的每个 `options` 都具有 `option := value` 的形式，并用逗号分隔。可用于自定义 Duper 调用的选项包括：
- `portfolioInstance`：可以设置为从 0 到 24 的自然数。每个数字对应于一组确切的选项，Duper 可以通过这些选项调用，因此指定 `portfolioInstance` 选项会使指定任何其他选项变得多余。`portfolioInstance` 选项的主要用途是确保当 `duper?` 成功时，可以向用户推荐形式为 `by duper [facts] {portfolioInstance := n}` 的简短证明脚本。
- `portfolioMode`：可以设置为 `true` 或 `false`，默认设置为 `true`。如果启用了 `portfolioMode`，则 Duper 将调用 3-4 个具有不同选项配置的自身实例，如果禁用了 `portfolioMode`，则 Duper 将仅调用一个自身实例。启用 `portfolioMode` 的好处是不同的选项配置更适合不同的问题，而缺点是如果启用了 `portfolioMode`，每个 Duper 实例在超时之前运行的时间会减少。通常，我们建议用户默认启用 `portfolioMode`，并使用 `set_option maxHeartbeats` 来控制每个 Duper 实例在放弃之前应运行多长时间（如果 `maxHeartbeats` 设置为 `n`，则每个实例将分配大约 `n/3` 的心跳）。
- `preprocessing`：可以设置为 `full`、`monomorphization` 或 `no_preprocessing`。此选项将控制在将引理提供给 Duper 之前对其进行预处理的程度。当启用了 `portfolioMode` 且未指定 `preprocessing` 选项时，3-4 个实例将进行完全预处理，1 个实例将不进行预处理。但当启用了 `preprocessing` 选项时，所有尝试的实例都将使用指定的预处理选项。通常，我们建议用户不要指定 `preprocessing` 选项，除非 Duper 特别提示。
- `inhabitationReasoning`：可以设置为 `true` 或 `false`。如果目标或任何提供的引理包含可能为空的类型，Duper 必须执行额外的推理以保证其证明的正确性。如果用户确信问题中的所有类型都是可证明非空的，即使是在当前问题的上下文之外，那么将 `inhabitationReasoning` 设置为 `false` 可以帮助 Duper 更高效地进行推理（尽管在证明重建期间，Duper 仍将验证任何关于类型可居性的假设是否有效）。同样，如果用户确信问题中至少有一个类型是空的，或者只能使用当前上下文中的事实验证为非空，那么将 `inhabitationReasoning` 设置为 `true` 将确保所有 Duper 实例从一开始就执行必要的类型可居性推理。
- `includeExpensiveRules`：可以设置为 `true` 或 `false`。Duper 用于推理高阶问题的一些规则可能会显著降低 Duper 的性能。此外，Duper 的一个规则评估可判定性实例，这对于某些问题来说可能是非常昂贵的。将 `includeExpensiveRules` 设置为 `false` 可以通过跳过这些可能消耗 Duper 运行时间大部分的规则来提高 Duper 的搜索效率。

### 证明脚本

尽管我们建议启用 Duper 的 `portfolioMode` 来找到初始证明，但运行多个 Duper 实例的效率低于仅运行用户知道会找到证明的单个实例。通过调用 `duper?` 而不是 `duper`，你可以指示 Duper 生成形式为 `duper [facts] {portfolioInstance := n}` 的策略脚本，该脚本将仅调用成功证明当前目标的 Duper 实例。

### 调试

Duper 是一个基于饱和的定理证明器（意味着它通过否定目标并生成子句直到推导出矛盾来尝试证明目标），这一事实带来了一些固有的调试挑战。如果 Duper 由于超时未能证明某个目标，那么它可能在尝试中生成数百或数千个子句。通常，生成子句的数量使得理解 Duper 未能证明目标的原因变得非常耗时。尽管如此，对于少数可以理解 Duper 失败原因的情况，我们提供了各种追踪选项以方便检查 Duper 的状态。

如果 Duper 超时，以下追踪选项可用：
- 使用 `set_option trace.duper.timeout.debug true` 将使 Duper 打印：
  - 活动集中的子句总数（这些是 Duper 已证明并完全处理的子句）
  - 被动集中的子句总数（这些是 Duper 已证明但尚未完全处理的子句）
  - 生成的子句总数
  - 活动集中的单元子句集（即可以表示为等式或不等式的完全处理的子句）
  - 关于问题中已识别类型的信息，以及它们是否通过类型类推理可证明为可居的、从提供给 Duper 的假设中可证明为非空的，或者可能为空的
- 使用 `set_option trace.duper.timeout.debug.fullActiveSet true` 将使 Duper 打印完整的活动集（即 Duper 已完全处理的所有子句，而不仅仅是那些可以表示为单个等式或不等式的子句）。请注意，对于某些问题，启用此选项可能会导致 VS Code 崩溃（因为它难以处理大量的追踪输出）。
- 使用 `set_option trace.duper.timeout.debug.fullPassiveSet true` 将使 Duper 打印完整的被动集（即 Duper 已证明但尚未完全处理的所有子句）。请注意，对于某些问题，启用此选项可能会导致 VS Code 崩溃（因为它难以处理大量的追踪输出）。

如果 Duper 饱和，意味着 Duper 完全处理了所有子句并且无法生成更多子句，那么 `set_option trace.duper.saturate.debug true` 将使 Duper 打印：
- 最终的活动集（即 Duper 生成并完全处理的所有子句）
- 关于问题中已识别类型的信息，以及它们是否通过类型类推理可证明为可居的、从提供给 Duper 的假设中可证明为非空的，或者可能为空的

如果 Duper 成功证明了目标，并且你想获取有关 Duper 找到的证明的更多信息，那么 `set_option trace.duper.printProof true` 将显示最终证明中使用的子句，而 `set_option trace.duper.proofReconstruction true` 将显示有关这些子句的证明以及用于解决目标的最终证明的信息。

根据我们的经验，我们通常发现尝试调试 Duper 饱和的问题比调试 Duper 超时的问题更有成效（因为通常需要查看的子句数量较少）。这在 Duper 原则上能够解决问题但需要提供一些它本身不知道的额外事实时最为有用。此外，我们通常发现禁用预处理时追踪输出更易读，因为当前的预处理过程将输入引理转换为具有不具信息性名称的事实。如果你需要在启用预处理的情况下查看 Duper 的追踪输出，那么 `set_option trace.duper.monomorphization.debug true` 将使 Duper 在单态化过程之前和之后打印其输入事实。这有助于理解 Duper 子句中出现的单态化常量如何与原始问题中的常量对应。