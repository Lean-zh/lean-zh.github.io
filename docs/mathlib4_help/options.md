# 选项

Mathlib 版本: `e4cf8333e0be712392567e370eead57e05d636a7`

## Elab.async
类型: `Bool`

默认值: `false`

尽可能使用多线程进行阐述

此选项默认为 `false`，但（未显式设置时）在语言服务器中被覆盖为 `true`。通过如 `Lean.Elab.Command.elabCommandTopLevel` 直接驱动阐述的元编程用户可通过设置此选项选择异步阐述，但需负责处理消息及其他数据，不仅来自最终命令状态，还需处理 `Lean.Command.Context.snap?` 及 `Lean.Command.State.snapshotTasks` 中的异步任务。

## Mathlib.Tactic.TFAE.useDeprecated
类型: `Bool`

默认值: `false`

重新启用“目标式”的 `tfae_have` 语法

## aesop.check.all
类型: `Bool`

默认值: `false`

(aesop) 启用所有运行时检查。个别检查仍可禁用。

## aesop.check.proofReconstruction
类型: `Bool`

默认值: `false`

(aesop) 在证明重构期间对部分证明项进行类型检查。

## aesop.check.rules
类型: `Bool`

默认值: `false`

(aesop) 检查规则报告的信息是否正确。

## aesop.check.script
类型: `Bool`

默认值: `false`

(aesop) 检查 Aesop 生成的战术脚本是否能证明目标。启用此检查时，即使未请求，Aesop 也会生成战术脚本。

## aesop.check.script.steps
类型: `Bool`

默认值: `false`

(aesop) 检查 Aesop 生成的战术脚本的每一步。启用此检查时，即使未请求，Aesop 也会生成战术脚本。

## aesop.check.tree
类型: `Bool`

默认值: `false`

(aesop) 在搜索循环的每次迭代后检查搜索树不变式。开销较大。

## aesop.collectStats
类型: `Bool`

默认值: `false`

(aesop) 收集有关 Aesop 调用的统计信息。使用 `#aesop_stats` 显示收集的统计信息。

## aesop.dev.dynamicStructuring
类型: `Bool`

默认值: `true`

(aesop) 仅供 Aesop 开发者使用。启用动态脚本结构化。

## aesop.dev.generateScript
类型: `Bool`

默认值: `false`

(aesop) 仅供 Aesop 开发者使用。即使未请求也生成脚本。

## aesop.dev.optimizedDynamicStructuring
类型: `Bool`

默认值: `true`

(aesop) 仅供 Aesop 开发者使用。若证明中无元变量，使用静态结构化替代动态结构化。

## aesop.dev.statefulForward
类型: `Bool`

默认值: `true`

(aesop) 仅供 Aesop 开发者使用。启用新的有状态前向推理引擎。

## aesop.smallErrorMessages
类型: `Bool`

默认值: `false`

(aesop) 打印更小的错误消息。用于测试。

## aesop.warn.applyIff
类型: `Bool`

默认值: `true`

(aesop) 当应用构建器于结论为 `A ↔ B` 形式的规则时发出警告。

## allowUnsafeReducibility
类型: `Bool`

默认值: `false`

允许用户修改声明的可约性设置，即使此类更改被视为潜在危险。例如，`simp` 及类型类解析维护可约声明展开的项索引。

## autoImplicit
类型: `Bool`

默认值: `true`

声明头部未绑定的局部变量变为隐式参数。在“宽松”模式（默认）下，任何原子标识符均符合条件，否则仅单字符后跟数字的标识符符合条件。例如，`def f (x : Vector α n) : Vector α n :=` 自动引入隐式变量 `{α n}`。

## autoLift
类型: `Bool`

默认值: `true`

在需要时插入单子提升（即 `liftM` 及强制转换）

## backward.eqns.deepRecursiveSplit
类型: `Bool`

默认值: `true`

为递归函数创建方程式引理如同非递归函数。若禁用，则递归函数定义中不含递归调用的匹配语句不会在方程式引理中引起进一步拆分。此为 Lean 4.12 之前的行为，此选项旨在帮助迁移旧代码。

## backward.eqns.nonrecursive
类型: `Bool`

默认值: `true`

为非递归定义创建细粒度方程式引理。

## backward.isDefEq.lazyProjDelta
类型: `Bool`

默认值: `true`

在解决形如 `(f a).i =?= (g b).i` 的统一约束时使用惰性 delta 归约

## backward.isDefEq.lazyWhnfCore
类型: `Bool`

默认值: `true`

指定形如 `(f a).i =?= s` 约束的规范化透明度模式，若为 `true`，仅在归约 `f a` 时展开可约定义及实例。否则使用默认设置

## backward.synthInstance.canonInstances
类型: `Bool`

默认值: `true`

在类型类解析期间使用依赖“道德规范”实例的优化

## bootstrap.genMatcherCode
类型: `Bool`

默认值: `true`

禁用辅助匹配器函数的代码生成

## bootstrap.inductiveCheckResultingUniverse
类型: `Bool`

默认值: `true`

默认情况下，`inductive`/`structure` 命令在结果宇宙非零但可能对某些宇宙参数为零时报告错误。原因：除非此类型为子单子，否则几乎非用户所需，因其仅可消去至 `Prop`。在 `Init` 包中，我们定义子单子，并利用此选项禁用检查。未来改进验证器后可能删除此选项。

## checkBinderAnnotations
类型: `Bool`

默认值: `true`

在使用绑定器注解 `[...]` 时检查类型是否为类实例

## compiler.check
类型: `Bool`

默认值: `true`

在每步编译器处理后进行类型检查（对调试过程有用）

## compiler.checkTypes
类型: `Bool`

默认值: `false`

(compiler) 在每步编译器处理后执行类型兼容性检查。注意此非完整检查，仅用于调试目的。在重度依赖类型的代码中可能失败。

## compiler.enableNew
类型: `Bool`

默认值: `false`

(compiler) 启用新代码生成器，此应对代码无显著影响，但有助于测试新代码生成器；取消设置则仅使用旧代码生成器

## compiler.extract_closed
类型: `Bool`

默认值: `true`

(compiler) 启用/禁用闭项缓存

## compiler.maxRecInline
类型: `Nat`

默认值: `1`

(compiler) 标记为 `[inline]` 的递归定义在编译期间可递归内联的最大次数，超过则生成错误。

## compiler.maxRecInlineIfReduce
类型: `Nat`

默认值: `16`

(compiler) 标记为 `[inline_if_reduce]` 的递归定义在编译期间可递归内联的最大次数，超过则生成错误。

## compiler.reuse
类型: `Bool`

默认值: `true`

启发式插入重置/重用指令对

## compiler.small
类型: `Nat`

默认值: `1`

(compiler) 大小 `≤ small` 的函数声明即使有多个出现也会内联。

## debug.byAsSorry
类型: `Bool`

默认值: `false`

若期望类型为命题，则将 `by ..` 块替换为 `sorry`

## debug.moduleNameAtTimeout
类型: `Bool`

默认值: `true`

在确定性超时错误消息中包含模块名。
注：我们将此选项设为 `false` 以提高测试套件的稳定性

## debug.proofAsSorry
类型: `Bool`

默认值: `false`

用 `sorry` 替换定理的证明部分

## debug.rawDecreasingByGoal
类型: `Bool`

默认值: `false`

显示原始的 `decreasing_by` 目标，包含内部实现细节，而非使用 `clean_wf` 战术清理。可启用以调试。若需此选项用于其他原因，请提交问题报告。

## debug.skipKernelTC
类型: `Bool`

默认值: `false`

跳过内核类型检查器。警告：将此选项设为 `true` 可能损害可靠性，因证明将不经 Lean 内核检查

## deprecated.oldSectionVars
类型: `Bool`

默认值: `false`

重新启用仅包含声明中使用的节变量的已弃用行为

## diagnostics
type: `Bool`
default: `false`
收集诊断信息

## diagnostics.threshold
type: `Nat`
default: `20`
仅报告定义等价性中超过此阈值的诊断计数器

## diagnostics.threshold.proofSize
type: `Nat`
default: `16384`
仅当证明至少包含此数量项时显示证明统计信息

## eval.derive.repr
type: `Bool`
default: `true`
('#eval' 命令) 启用自动派生 'Repr' 实例作为回退

## eval.pp
type: `Bool`
default: `true`
('#eval' 命令) 启用使用 'ToExpr' 实例美化输出结果，否则使用 'Repr' 或 'ToString' 实例

## eval.type
type: `Bool`
default: `false`
('#eval' 命令) 启用美化输出结果的类型信息

## exponentiation.threshold
type: `Nat`
default: `256`
幂运算安全评估的最大阈值。当指数值超过此阈值时，将不评估幂运算并记录警告。防止系统因过大计算量失去响应。

## format.indent
type: `Nat`
default: `2`
缩进量

## format.inputWidth
type: `Nat`
default: `100`
理想输入宽度

## format.unicode
type: `Bool`
default: `true`
使用Unicode字符

## format.width
type: `Nat`
default: `120`
缩进宽度

## genInjectivity
type: `Bool`
default: `true`
为归纳数据类型构造器生成单射性定理

## genSizeOf
type: `Bool`
default: `true`
为归纳类型及结构体自动生成 `SizeOf` 实例

## genSizeOfSpec
type: `Bool`
default: `true`
为自动生成的实例生成 `SizeOf` 规范定理

## grind.debug
type: `Bool`
default: `false`
更新后检查不变量

## grind.debug.proofs
type: `Bool`
default: `false`
检查所有等价类元素间的证明

## grind.warning
type: `Bool`
default: `true`
禁用 `grind` 使用警告

## guard_msgs.diff
type: `Bool`
default: `false`
若为真，当预期与实际消息不匹配时显示差异对比

## hygiene
type: `Bool`
default: `true`
对引用中的标识符进行注解，使其解析基于声明时的作用域而非使用/扩展时的作用域，避免意外捕获。注意已有引用/表示法不受影响。

## inductive.autoPromoteIndices
type: `Bool`
default: `true`
在可能时将归纳类型的索引提升为参数

## internal.cmdlineSnapshots
type: `Bool`
default: `false`
将快照中存储的信息缩减至命令行驱动所需最小量：每条命令的诊断信息及最终完整快照

## internal.parseQuotWithCurrentStage
type: `Bool`
default: `false`
(Lean 引导) 在引用中使用当前阶段的解析器

## interpreter.prefer_native
type: `Bool`
default: `true`
(解释器) 在可用时优先使用预编译代码

## lang.lemmaCmd
type: `Bool`
default: `false`
启用 `lemma` 命令作为 `theorem` 的同义词

## leansearch.queries
type: `Nat`
default: `6`
leansearch 请求的结果数量（默认 6）

## leansearchclient.backend
type: `String`
default: `"leansearch"`
默认使用的后端，可选值为 leansearch 或 moogle

## leansearchclient.useragent
type: `String`
default: `"LeanSearchClient"`
leansearchclient 的用户代理名称

## linter.admit
type: `Bool`
default: `false`
启用 admit 检查器

## linter.all
type: `Bool`
default: `false`
启用所有检查器

## linter.constructorNameAsVariable
type: `Bool`
default: `true`
启用警告绑定变量名为零元构造器名称的检查器

## linter.countHeartbeats
type: `Bool`
default: `false`
启用心跳计数检查器

## linter.countHeartbeatsApprox
type: `Bool`
default: `false`
若为真，countHeartbeats 检查器将心跳计数向下取整至最接近的千位数

## linter.deprecated
type: `Bool`
default: `true`
若为真，生成弃用警告

## linter.docPrime
type: `Bool`
default: `false`
启用 docPrime 检查器

## linter.dupNamespace
type: `Bool`
default: `true`
启用重复命名空间检查器

## linter.existingAttributeWarning
type: `Bool`
default: `true`
检查源声明是否具有某些属性的检查器，主要由 `@[to_additive]` 使用

## linter.flexible
type: `Bool`
default: `false`
启用 flexible 检查器

## linter.globalAttributeIn
type: `Bool`
default: `true`
启用 globalAttributeIn 检查器

## linter.hashCommand
type: `Bool`
default: `false`
启用 `#` 命令检查器

## linter.haveLet
type: `Nat`
default: `0`
启用 `have` 与 `let` 的检查：
* 0 -- 不启用；
* 1 -- 仅在存在噪音的声明中启用；
* 2 或更高 -- 始终启用。

## linter.indexVariables
type: `Bool`
default: `false`
验证作为索引出现的变量（如 `xs[i]` 或 `xs.take i` 中的 `i`）仅为 `i`、`j` 或 `k`

## linter.listVariables
type: `Bool`
default: `false`
验证所有 `List`/`Array`/`Vector` 变量使用允许的名称

## linter.minImports
type: `Bool`
default: `false`
启用 minImports 检查器

## linter.minImports.increases
type: `Bool`
default: `true`
在 minImports 检查器中启用报告规模增长变化

## linter.missingDocs
type: `Bool`
default: `false`
启用“缺失文档”检查器

## linter.oldObtain
type: `Bool`
default: `false`
启用 oldObtain 检查器

## linter.omit
type: `Bool`
default: `false`
启用“避免 omit”检查器

## linter.ppRoundtrip
type: `Bool`
default: `false`
启用 ppRoundtrip 检查器

## linter.simpsNoConstructor
type: `Bool`
default: `true`
检查是否使用了 `simps!` 的检查器

## linter.simpsUnusedCustomDeclarations
type: `Bool`
default: `true`
检查是否为 simps 声明了未使用的自定义声明的检查器

## linter.style.cases
type: `Bool`
default: `false`
启用 cases 样式检查器

## linter.style.cdot
type: `Bool`
default: `false`
启用 `cdot` 样式检查器

## linter.style.docString
type: `Bool`
default: `false`
启用文档字符串样式检查器

## linter.style.dollarSyntax
type: `Bool`
default: `false`
启用 `dollarSyntax` 样式检查器

## linter.style.header
type: `Bool`
default: `false`
启用标题样式检查器

## linter.style.lambdaSyntax
type: `Bool`
default: `false`
启用 `lambdaSyntax` 样式检查器

## linter.style.longFile
type: `Nat`
default: `0`
启用长文件检查器

## linter.style.longFileDefValue
type: `Nat`
default: `1500`
每个文件行数的软性上限

## linter.style.longLine
type: `Bool`
default: `false`
启用长行检查器

## linter.style.missingEnd
type: `Bool`
default: `false`
启用缺失 end 检查器

## linter.style.multiGoal
type: `Bool`
default: `false`
启用多目标检查器

## linter.style.nameCheck
type: `Bool`
default: `true`
启用 `nameCheck` 检查器

## linter.style.openClassical
type: `Bool`
default: `false`
启用 openClassical 检查器

## linter.style.refine
type: `Bool`
default: `false`
启用 refine 检查器

## linter.style.setOption
type: `Bool`
default: `false`
启用 `setOption` 检查器

## linter.suspiciousUnexpanderPatterns
type: `Bool`
default: `true`
启用“可疑未展开模式”检查器

## linter.toAdditiveExisting
type: `Bool`
default: `true`
由 `@[to_additive]` 使用的检查器，验证用户是否正确指定加法声明已存在

## linter.toAdditiveGenerateName
type: `Bool`
default: `true`
由 `@[to_additive]` 使用的检查器，检查是否自动生成用户指定名称

## linter.toAdditiveReorder
type: `Bool`
default: `true`
检查 reorder 属性未被手动指定的检查器

## linter.unnecessarySeqFocus
type: `Bool`
default: `true`
启用 '不必要的 <;>' 检查器

## linter.unnecessarySimpa
类型: `Bool`

默认值: `true`

启用 '不必要的 simpa' 检查器

## linter.unreachableTactic
类型: `Bool`

默认值: `true`

启用 '不可达策略' 检查器

## linter.unusedRCasesPattern
类型: `Bool`

默认值: `true`

启用 '未使用的 rcases 模式' 检查器

## linter.unusedSectionVars
类型: `Bool`

默认值: `true`

启用 '定理体中未使用的节变量' 检查器

## linter.unusedTactic
类型: `Bool`

默认值: `true`

启用 '未使用策略' 检查器

## linter.unusedVariables
类型: `Bool`

默认值: `true`

启用 '未使用变量' 检查器

## linter.unusedVariables.analyzeTactics
类型: `Bool`

默认值: `false`

启用对存在策略证明时局部变量的分析

默认情况下，当存在策略证明时，检查器将仅限于检查声明的参数，因为这些分析可能较为耗时。启用此选项会将检查范围扩展到策略证明内部和外部的局部变量，但也可能导致一些误报，因为中间策略状态可能引用某些变量而最终声明并不依赖它们。

## linter.unusedVariables.funArgs
类型: `Bool`

默认值: `true`

启用 '未使用变量' 检查器以标记未使用的函数参数

## linter.unusedVariables.patternVars
类型: `Bool`

默认值: `true`

启用 '未使用变量' 检查器以标记未使用的模式变量

## linter.upstreamableDecl
类型: `Bool`

默认值: `false`

启用 upstreamableDecl 检查器

## linter.upstreamableDecl.defs
类型: `Bool`

默认值: `false`

upstreamableDecl 对定义发出警告

## linter.upstreamableDecl.private
类型: `Bool`

默认值: `false`

upstreamableDecl 对私有声明发出警告

## loogle.queries
类型: `Nat`

默认值: `6`

向 loogle 请求的结果数量（默认 6）

## match.ignoreUnusedAlts
类型: `Bool`

默认值: `false`

若为 true，则在未使用备选分支时不生成错误

## maxBackwardChainingDepth
类型: `Nat`

默认值: `10`

在归纳谓词的 `brecOn` 证明的反向链部分中使用的最大搜索深度

## maxHeartbeats
类型: `Nat`

默认值: `200000`

每条命令的最大心跳次数。一次心跳指（小）内存分配次数（以千计），0 表示无限制

## maxRecDepth
类型: `Nat`

默认值: `512`

许多 Lean 过程的最大递归深度

## maxSynthPendingDepth
类型: `Nat`

默认值: `1`

嵌套 `synthPending` 调用的最大次数。在解决统一约束时，可能需要合成待处理的类型类问题。这些类型类问题可能创建新的统一约束，进而需要解决新的类型类问题。此选项设置了创建嵌套问题的阈值。

## maxTraceChildren
类型: `Nat`

默认值: `50`

跟踪节点子项的最大显示数量

## maxUniverseOffset
类型: `Nat`

默认值: `32`

最大宇宙层级偏移量

## moogle.queries
类型: `Nat`

默认值: `6`

向 moogle 请求的结果数量（默认 6）

## polyrith.sageUserAgent
类型: `String`

默认值: `"LeanProver (https://leanprover-community.github.io/)"`

调用 SageMath API 时的 User-Agent 标头值

## pp.all
类型: `Bool`

默认值: `false`

（漂亮打印器）显示强制转换、隐式参数、证明项、完全限定名、宇宙，并在漂亮打印期间禁用 beta 归约和符号

## pp.analyze
类型: `Bool`

默认值: `false`

（漂亮打印分析器）尝试确定足以确保往返的注释

## pp.analyze.checkInstances
类型: `Bool`

默认值: `false`

（漂亮打印分析器）确认实例可重新合成

## pp.analyze.explicitHoles
类型: `Bool`

默认值: `false`

（漂亮打印分析器）对可推断的显式参数使用 `_`

## pp.analyze.knowsType
类型: `Bool`

默认值: `true`

（漂亮打印分析器）假设原始表达式的类型已知

## pp.analyze.omitMax
类型: `Bool`

默认值: `true`

（漂亮打印分析器）省略宇宙 `max` 注释（这些约束实际上可能有害）

## pp.analyze.trustId
类型: `Bool`

默认值: `true`

（漂亮打印分析器）始终假设可推断隐式的 `fun x => x`

## pp.analyze.trustKnownFOType2TypeHOFuns
类型: `Bool`

默认值: `true`

（漂亮打印分析器）省略值似乎为 knownType2Type 的高阶函数

## pp.analyze.trustOfNat
类型: `Bool`

默认值: `true`

（漂亮打印分析器）始终“假装”`OfNat.ofNat` 应用可自底向上推导

## pp.analyze.trustOfScientific
类型: `Bool`

默认值: `true`

（漂亮打印分析器）始终“假装”`OfScientific.ofScientific` 应用可自底向上推导

## pp.analyze.trustSubst
类型: `Bool`

默认值: `false`

（漂亮打印分析器）始终“假装”可删除为 ▸ 的应用是“常规的”

## pp.analyze.trustSubtypeMk
类型: `Bool`

默认值: `true`

（漂亮打印分析器）假设 Subtype.mk 的隐式参数可推断

## pp.analyze.typeAscriptions
类型: `Bool`

默认值: `true`

（漂亮打印分析器）在认为必要时添加类型标注

## pp.auxDecls
类型: `Bool`

默认值: `false`

显示用于编译递归函数的辅助声明

## pp.beta
类型: `Bool`

默认值: `false`

（漂亮打印器）在漂亮打印时应用 beta 归约

## pp.coercions
类型: `Bool`

默认值: `true`

（漂亮打印器）隐藏强制转换应用

## pp.coercions.types
类型: `Bool`

默认值: `false`

（漂亮打印器）将带有类型标注的强制转换应用显示为类型标注

## pp.deepTerms
类型: `Bool`

默认值: `false`

（漂亮打印器）显示深度嵌套的项，若设为 false 则用 `⋯` 替换

## pp.deepTerms.threshold
类型: `Nat`

默认值: `50`

（漂亮打印器）当 `pp.deepTerms` 为 false 时，开始用 `⋯` 替换项的深度

## pp.explicit
类型: `Bool`

默认值: `false`

（漂亮打印器）显示隐式参数

## pp.exprSizes
类型: `Bool`

默认值: `false`

（漂亮打印器）为每个嵌入表达式前缀其大小，格式为（忽略共享的大小/带共享的大小/带最大共享的大小）

## pp.fieldNotation
类型: `Bool`

默认值: `true`

（漂亮打印器）使用字段符号进行漂亮打印，包括结构体投影，除非应用了 `@[pp_nodot]`

## pp.fieldNotation.generalized
类型: `Bool`

默认值: `true`

（漂亮打印器）当 `pp.fieldNotation` 为 true 时，启用广义字段符号，当字段符号的参数是第一个显式参数时

## pp.fullNames
类型: `Bool`

默认值: `false`

（漂亮打印器）显示完全限定名

## pp.funBinderTypes
类型: `Bool`

默认值: `false`

（漂亮打印器）显示 lambda 参数的类型

## pp.implementationDetailHyps
类型: `Bool`

默认值: `false`

在本地上下文中显示实现细节假设

## pp.inaccessibleNames
类型: `Bool`

默认值: `true`

在本地上下文中显示不可访问的声明

## pp.instanceTypes
类型: `Bool`

默认值: `false`

（漂亮打印器）在打印显式应用时，显示实例隐式参数的类型

## pp.instances
类型: `Bool`

默认值: `true`

（漂亮打印器）若设为 false，将显式应用中的实例隐式参数替换为占位符

## pp.instantiateMVars
类型: `Bool`

默认值: `true`

（漂亮打印器）在删除前实例化 mvars

## pp.letVarTypes
类型: `Bool`

默认值: `false`

（漂亮打印器）显示 let 绑定变量的类型

## pp.macroStack
类型: `Bool`

默认值: `false`

显示宏扩展堆栈

## pp.match
类型: `Bool`

默认值: `true`

（漂亮打印器）禁用/启用 'match' 符号

## pp.mathlib.binderPredicates
类型: `Bool`

默认值: `true`

（漂亮打印器）将如 `∀ (x : α) (x < 2), p x` 的绑定符漂亮打印为 `∀ x < 2, p x`

## pp.maxSteps
类型: `Nat`

默认值: `5000`

（漂亮打印器）访问表达式的最大数量，超过后将用 `⋯` 漂亮打印项

## pp.motives.all
type: `Bool`

default: `false`

(pretty printer) 打印所有 motive

## pp.motives.nonConst
type: `Bool`

default: `false`

(pretty printer) 打印所有非常量函数的 motive

## pp.motives.pi
type: `Bool`

default: `true`

(pretty printer) 打印所有返回 Pi 类型的 motive

## pp.mvars
type: `Bool`

default: `true`

(pretty printer) 当为 true 时显示元变量名称，否则将表达式元变量显示为 '?_'，将宇宙层级元变量显示为 '_'

## pp.mvars.anonymous
type: `Bool`

default: `true`

(pretty printer) 当为 true 时显示自动生成的元变量名称（如 `?m.22`），否则将表达式元变量显示为 '?_'，将宇宙层级元变量显示为 '_'。当 `pp.mvars` 为 false 时，此选项也为 false

## pp.mvars.delayed
type: `Bool`

default: `false`

(pretty printer) 当为 true 时显示延迟赋值的元变量，否则显示其赋值内容

## pp.mvars.levels
type: `Bool`

default: `true`

(pretty printer) 当为 true 时将宇宙层级元变量显示为 `?u.22`，否则显示为 '_'。当 `pp.mvars` 或 `pp.mvars.anonymous` 为 false 时，此选项也为 false

## pp.mvars.withType
type: `Bool`

default: `false`

(pretty printer) 显示带有类型标注的元变量

## pp.natLit
type: `Bool`

default: `false`

(pretty printer) 使用 `nat_lit` 前缀显示原始自然数字面量

## pp.notation
type: `Bool`

default: `true`

(pretty printer) 启用/禁用符号（中缀、混缀、后缀运算符及 Unicode 字符）

## pp.numericProj.prod
type: `Bool`

default: `true`

启用将 `Prod.fst x` 显示为 `x.1`，`Prod.snd x` 显示为 `x.2`

## pp.numericTypes
type: `Bool`

default: `false`

(pretty printer) 显示数字字面量的类型

## pp.oneline
type: `Bool`

default: `false`

(pretty printer) 仅保留漂亮打印输出的第一行，其余省略

## pp.parens
type: `Bool`

default: `false`

(pretty printer) 若为 true，无论优先级如何，符号均包裹在括号中

## pp.piBinderTypes
type: `Bool`

default: `true`

(pretty printer) 显示 Pi 参数的类型

## pp.privateNames
type: `Bool`

default: `false`

(pretty printer) 显示分配给私有声明的内部名称

## pp.proofs
type: `Bool`

default: `false`

(pretty printer) 当为 true 时显示证明，否则将表达式中的证明替换为 `⋯`

## pp.proofs.threshold
type: `Nat`

default: `0`

(pretty printer) 当 `pp.proofs` 为 false 时，控制开始将证明替换为 `⋯` 的复杂度阈值

## pp.proofs.withType
type: `Bool`

default: `false`

(pretty printer) 当 `pp.proofs` 为 false 时，为省略的证明添加类型标注

## pp.qq
type: `Bool`

default: `true`

(pretty printer) 将引文打印为 q(...) 和 Q(...)

## pp.raw
type: `Bool`

default: `false`

(pretty printer) 打印原始表达式/语法树

## pp.raw.maxDepth
type: `Nat`

default: `32`

(pretty printer) 原始打印器的最大 `Syntax` 深度

## pp.raw.showInfo
type: `Bool`

default: `false`

(pretty printer) 使用原始打印器打印 `SourceInfo` 元数据

## pp.rawOnError
type: `Bool`

default: `false`

(pretty printer) 当漂亮打印失败时回退到 'raw' 打印器

## pp.safeShadowing
type: `Bool`

default: `true`

(pretty printer) 若无冲突则允许变量遮蔽

## pp.sanitizeNames
type: `Bool`

default: `true`

在漂亮打印时为被遮蔽/不可访问的变量添加后缀

## pp.showLetValues
type: `Bool`

default: `true`

在信息视图中显示 let 声明的值

## pp.sorrySource
type: `Bool`

default: `false`

(pretty printer) 若为 true，在可用时显示 'sorry' 的原始源位置

## pp.structureInstanceTypes
type: `Bool`

default: `false`

(pretty printer) 显示结构实例的类型

## pp.structureInstances
type: `Bool`

default: `true`

(pretty printer) 使用 `{ fieldName := fieldValue, ... }` 符号显示结构实例，若结构标记有 `@[pp_using_anonymous_constructor]` 属性则使用 `⟨fieldValue, ... ⟩`

## pp.structureInstances.flatten
type: `Bool`

default: `true`

(pretty printer) 为父投影展开嵌套的结构实例

## pp.tagAppFns
type: `Bool`

default: `false`

(pretty printer) 标记所有作为函数应用中函数的常量

## pp.unicode.fun
type: `Bool`

default: `false`

(pretty printer) 禁用/启用函数的 Unicode ↦ 符号

## pp.universes
type: `Bool`

default: `false`

(pretty printer) 显示宇宙

## printMessageEndPos
type: `Bool`

default: `false`

打印每条消息的结束位置，附加到起始位置之后

## profiler
type: `Bool`

default: `false`

显示各 Lean 组件的独占执行时间
  
另见 `trace.profiler` 获取具有结构化输出的替代性能分析系统

## profiler.threshold
type: `Nat`

default: `100`

阈值（毫秒），低于此阈值的分析时间将不单独报告

## push_neg.use_distrib
type: `Bool`

default: `false`

使 `push_neg` 使用 `not_and_or` 而非默认的 `not_and`

## quotPrecheck
type: `Bool`

default: `true`

启用对符号的急切名称分析以尽早发现未绑定的标识符。
注意，类型敏感的语法（“elaborators”）需要特殊支持此类检查，因此在使用此类语法时可能需要关闭此选项

## quotPrecheck.allowSectionVars
type: `Bool`

default: `false`

允许在检查的引文中出现区域变量，这在声明局部符号时有用

## relaxedAutoImplicit
type: `Bool`

default: `true`

当启用“宽松”模式时，任何非空原子标识符均有资格作为自动绑定隐式局部变量（参见选项 `autoImplicit`）

## sat.solver
type: `String`

default: `""`

Lean.Elab.Tactic.BVDecide 策略使用的 SAT 求解器名称。

     1. 若设置为非空字符串，则使用该二进制文件

     2. 若设置为空字符串，将检查执行程序旁是否存在 cadical 二进制文件。通常该程序为 `lean`，我们确实在其旁附带了一个 `cadical`

     3. 若未找到，尝试从 PATH 调用 `cadical`。空字符串默认表示使用随 Lean 附带的求解器

## says.no_verify_in_CI
type: `Bool`

default: `false`

禁用重新验证，即使 `CI` 环境变量已设置

## says.verify
type: `Bool`

default: `false`

验证输出

## server.reportDelayMs
type: `Nat`

default: `200`

(server) 文档编辑后报告进度和诊断前等待的毫秒时间，以减少闪烁

此选项只能在命令行设置，不可在 lakefile 或通过 `set_option` 设置

## showInferredTerminationBy
type: `Bool`

default: `false`

在递归定义中显示推断的 `termination_by` 度量

## showPartialSyntaxErrors
type: `Bool`

default: `false`

显示部分语法树的精化错误（即解析器恢复后）

## showTacticDiff
type: `Bool`

default: `true`

当为 true 时，交互式战术目标将使用差异信息装饰

## simprocs
type: `Bool`

default: `true`

启用/禁用 `simproc`（简化过程）

## smartUnfolding
type: `Bool`

default: `true`

在计算弱头范式时，使用为结构递归定义的函数创建的辅助定义

## statesearch.queries
type: `Nat`

default: `6`

向 statesearch 请求的结果数量（默认 6）

## statesearch.revision
type: `String`

default: `"v4.18.0-rc1"`

使用的 LeanStateSearch 修订版本

## stderrAsMessages
type: `Bool`

default: `true`

(server) 在命令精化期间捕获 Lean stderr 通道的输出（如来自 `dbg_trace` 的输出）作为诊断消息

## structure.strictResolutionOrder
type: `Bool`
default: `false`

若为 true，要求结构体遵循严格的解析顺序

## structureDiamondWarning
type: `Bool`

default: `false`

若为 true，当结构体存在菱形继承时启用警告

## synthInstance.checkSynthOrder
type: `Bool`

default: `true`

检查实例是否不会在非输出参数中引入元变量

## synthInstance.maxHeartbeats
type: `Nat`

default: `20000`

每个类型类解析问题的最大心跳数。心跳指（小型）内存分配次数（以千计），0 表示无限制

## synthInstance.maxSize
type: `Nat`

default: `128`

类型类实例合成过程中用于构建解决方案的最大实例数

## tactic.customEliminators
type: `Bool`

default: `true`

启用在使用 `@[induction_eliminator]` 和 `@[cases_eliminator]` 属性定义的自定义消除器中执行 `induction` 和 `cases` 策略

## tactic.erw?.verbose
type: `Bool`

default: `false`

`erw?` 在尝试识别会阻碍使用 `rw` 的子表达式时记录更多信息

## tactic.hygienic
type: `Bool`

default: `true`

确保策略是卫生的（hygienic）

## tactic.simp.trace
type: `Bool`

default: `false`

启用追踪时，调用 `simp` 或 `dsimp` 将打印等效的 `simp only` 调用

## tactic.skipAssignedInstances
type: `Bool`

default: `true`

在 `rw` 和 `simp` 策略中，若实例隐式参数已赋值，则不尝试合成实例

## trace.Aesop.Util.EqualUpToIds
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.CancelDenoms
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.commonJoinPointArgs
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.cse
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.eagerLambdaLifting
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.elimDeadBranches
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.extendJoinPointContext
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.findJoinPoints
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.floatLetIn
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.init
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.jp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.lambdaLifting
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.pullFunDecls
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.pullInstances
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.reduceArity
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.reduceJpArity
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.result
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.saveBase
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.saveMono
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.simp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.simp.inline
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.simp.jpCases
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.simp.stat
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.simp.step
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.simp.step.new
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.specialize
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.specialize.candidate
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.specialize.info
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.specialize.step
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.stat
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.test
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.toMono
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Compiler.trace
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Debug.Meta.Tactic.cc
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Debug.Meta.Tactic.cc.ac
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Debug.Meta.Tactic.cc.parentOccs
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Debug.Meta.Tactic.fun_prop
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Debug.Meta.Tactic.simp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Debug.Meta.Tactic.simp.congr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.RpcEncodable
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.beq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.decEq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.fintype
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.fromJson
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.hashable
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.inhabited
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.ord
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.repr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.toExpr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Deriving.toJson
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.ProxyType
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.Tactic.monotonicity
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.app
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.app.args
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.app.elab_as_elim
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.app.finalize
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.app.propagateExpectedType
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.async
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.autoParam
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.axiom
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.binop
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.binrel
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.block
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.cases
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.coe
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.command
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.congr
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.debug
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.defaultInstance
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.body
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.eqns
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.mkClosure
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.partialFixpoint
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.partialFixpoint.induction
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.scc
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.structural
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.structural.eqns
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.unfoldEqn
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.wf
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.definition.wf.eqns
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.do
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.eval
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.fast_instance
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.fbinop
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.implicitForall
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.induction
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.inductive
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.info
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.input
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.instance.mkInstanceName
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.let
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.let.decl
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.letrec
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.lint
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.match
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.match_syntax
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.match_syntax.alt
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.match_syntax.onMatch
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.match_syntax.result
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.postpone
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.resume
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.reuse
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.snapshotTree
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.step
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.step.result
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.struct
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.struct.modifyOp
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.structure
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.structure.resolutionOrder
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.tactic
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Elab.tactic.backtrack
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Kernel
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Mathlib.Deriving.Encodable
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Mathlib.Deriving.countable
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Meta
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Meta.AC
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Meta.CongrTheorems
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的追踪

## trace.Meta.FunInd
类型: `Bool`

默认值: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.IndPredBelow
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.IndPredBelow.match
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.IndPredBelow.search
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Match
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Match.debug
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Match.match
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Match.matchEqs
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Match.unify
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.acyclic
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.bv
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.cases
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.cc.failure
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.cc.merge
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.contradiction
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.fun_prop
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.fun_prop.attr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.induction
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.polyrith
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.sat
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.all
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.congr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.discharge
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.ground
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.heads
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.numSteps
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.rewrite
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.simp.unify
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.solveByElim
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.splitIf
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.Tactic.subst
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.appBuilder
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.appBuilder.error
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.appBuilder.result
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.check
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.debug
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.gcongr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.injective
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.instantiateMVars
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign.beforeMkLambda
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign.checkTypes
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign.occursCheck
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign.outOfScopeFVar
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.assign.typeError
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.cache
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.constApprox
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.delta
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.delta.unfoldLeft
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.delta.unfoldLeftRight
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.delta.unfoldRight
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.eta.struct
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.foApprox
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.hint
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.onFailure
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.stuck
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.stuckMVar
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isDefEq.whnf.reduceBinOp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isLevelDefEq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isLevelDefEq.postponed
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isLevelDefEq.step
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪功能

## trace.Meta.isLevelDefEq.stuck
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.realizeConst
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.sizeOf
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.sizeOf.aux
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.sizeOf.loop
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.sizeOf.minor
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.sizeOf.minor.step
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance.answer
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance.instances
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance.newAnswer
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance.resume
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance.tryResolve
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthInstance.unusedArgs
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthOrder
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.synthPending
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Meta.whnf
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.delab
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.delab.input
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.format
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.format.backtrack
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.format.input
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.parenthesize
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.parenthesize.backtrack
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.PrettyPrinter.parenthesize.input
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.compute_degree
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.congrm
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.field_simp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.generalize_proofs
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.librarySearch
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.librarySearch.lemmas
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.move_oper
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.norm_cast
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.norm_num
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.positivity
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.positivity.failure
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.propose
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.rewrites
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.rewrites.lemmas
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.Tactic.trans
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.abel
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.abel.detail
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.adaptationNote
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.aesop
type: `Bool`

default: `false`

(aesop) 打印Aesop在证明搜索过程中采取的操作

## trace.aesop.debug
type: `Bool`

default: `false`

(aesop) 打印各种调试信息

## trace.aesop.extraction
type: `Bool`

default: `false`

(aesop) 打印证明提取过程的跟踪信息

## trace.aesop.forward
type: `Bool`

default: `false`

(aesop) 跟踪前向推理

## trace.aesop.forward.debug
type: `Bool`

default: `false`

(aesop) 跟踪更多关于前向推理的信息，主要用于性能分析

## trace.aesop.proof
type: `Bool`

default: `false`

(aesop) 如果搜索成功，打印生成的证明项

## trace.aesop.rpinf
type: `Bool`

default: `false`

(aesop) 跟踪RPINF计算

## trace.aesop.ruleSet
type: `Bool`

default: `false`

(aesop) 在开始搜索前打印规则集

## trace.aesop.script
type: `Bool`

default: `false`

(aesop) 打印脚本生成的跟踪信息

## trace.aesop.stats
type: `Bool`

default: `false`

(aesop) 如果搜索成功，打印一些统计信息

## trace.aesop.tree
type: `Bool`

default: `false`

(aesop) 在搜索结束后（无论成功与否），打印最终的搜索树

## trace.apply_fun
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.bicategory
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.bound.attribute
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.compiler
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.cce
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.code_gen
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.cse
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.eager_lambda_lifting
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.elim_dead_let
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.erase_irrelevant
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.eta_expand
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.extract_closed
type: `Bool`

default: `false`

(trace) 启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.inline
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.input
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.borrow
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.boxing
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.elim_dead
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.elim_dead_branches
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.expand_reset_reuse
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.init
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.push_proj
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.rc
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.reset_reuse
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.result
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ir.simp_case
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.lambda_lifting
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.lambda_pure
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.lcnf
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.ll_infer_type
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.llnf
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.optimize_bytecode
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.reduce_arity
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.result
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.simp
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.simp_app_args
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.simp_detail
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.simp_float_cases
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.spec_candidate
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.spec_info
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.specialize
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.stage1
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.stage2
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.compiler.struct_cases_on
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.congr!
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.congr!.synthesize
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.debug
type: `Bool`
default: `false`
（跟踪）启用/禁用对指定模块及其子模块的跟踪

## trace.explode
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.assert
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.beta
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.assert
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.assert.dvd
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.assert.le
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.assign
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.conflict
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.diseq
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.diseq.trivial
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd.solve
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd.solve.combine
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd.solve.elim
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd.trivial
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd.unsat
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.dvd.update
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.eq
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.eq.trivial
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.eq.unsat
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.internalize
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.internalize.term
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.le
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.le.lower
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.le.trivial
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.le.unsat
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.le.upper
type: `Bool`
default: `false`
启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.model
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.cutsat.subst
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.beta
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.canon
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.congr
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.cutsat.backtrack
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.cutsat.diseq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.cutsat.diseq.split
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.cutsat.eq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.ematch.pattern
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.final
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.forallPropagator
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.internalize
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.matchCond
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.matchCond.lambda
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.matchCond.proveFalse
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.offset
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.offset.proof
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.parent
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.proj
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.proof
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.proofs
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.debug.split
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.ematch
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.ematch.instance
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.ematch.instance.assignment
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.ematch.pattern
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.ematch.pattern.search
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.eqResolution
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.eqc
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.internalize
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.issues
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.dist
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.eq
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.eq.from
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.eq.to
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.internalize
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.internalize.term
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.offset.propagate
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.simp
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.split
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.split.candidate
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.split.resolved
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.grind.trace
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.linarith
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.linarith.detail
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.monoidal
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.notation3
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.omega
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.plausible.decoration
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.plausible.discarded
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.plausible.instance
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.plausible.shrink.candidates
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.plausible.shrink.steps
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.plausible.success
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.pp.analyze
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.pp.analyze.annotate
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.pp.analyze.error
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.pp.analyze.tryUnify
type: `Bool`

default: `false`

启用/禁用对指定模块及其子模块的跟踪

## trace.profiler
type: `Bool`

default: `false`

激活执行时间超过 `trace.profiler.threshold` 的嵌套跟踪并用时间进行注释

## trace.profiler.output
type: `String`

default: `""`

将 `trace.profiler` 数据以 Firefox Profiler 兼容格式输出到指定文件路径

## trace.profiler.output.pp
type: `Bool`

default: `false`

如果为 false，则导出的跟踪节点中的文本仅限跟踪类名和 `TraceData.tag`（如果有）

这在关注子系统耗时而非特定调用耗时的情况下非常有用（这是常见情况）。

## trace.profiler.threshold
类型: `Nat`

默认值: `10`

以毫秒为单位的阈值（若 `trace.profiler.useHeartbeats` 为真则采用心跳次数），低于阈值的追踪将不会激活

## trace.profiler.useHeartbeats
类型: `Bool`

默认值: `false`

若为真，使用心跳次数替代秒数进行测量和报告

## trace.rw_search
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.rw_search.detail
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.saturate
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.simps.debug
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.simps.verbose
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.split.debug
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.split.failure
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.string_diagram
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.tactic.use
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.tauto
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.to_additive
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.to_additive_detail
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.try
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.try.collect
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.try.collect.funInd
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.try.debug
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.try.debug.chain
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.try.debug.funInd
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## trace.variable?
类型: `Bool`

默认值: `false`

启用/禁用指定模块及其子模块的追踪功能

## variable?.checkRedundant
类型: `Bool`

默认值: `true`

若实例参数可从前序参数推断，则发出警告

## variable?.maxSteps
类型: `Nat`

默认值: `15`

`variable?` 在放弃前将尝试插入的实例参数最大数量

## warningAsError
类型: `Bool`

默认值: `false`

将警告视为错误处理

## wf.preprocess
类型: `Bool`

默认值: `true`

使用 `wf_preprocess` 简化集对通过良基递归定义的函数进行预处理
