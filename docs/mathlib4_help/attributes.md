# 属性

Mathlib 版本：`e4cf8333e0be712392567e370eead57e05d636a7`

## Std.Internal.tree_tac
内部 DTreeMap 引理使用的 simp 定理

## aesop
将声明注册为 Aesop 规则。

## aesop_Bound
Aesop 规则集 'Bound' 中的 simp 定理

## aesop_Bound_proc
Aesop 规则集 'Bound' 中的 simprocs

## aesop_CStarAlgebra
Aesop 规则集 'CStarAlgebra' 中的 simp 定理

## aesop_CStarAlgebra_proc
Aesop 规则集 'CStarAlgebra' 中的 simprocs

## aesop_CategoryTheory
Aesop 规则集 'CategoryTheory' 中的 simp 定理

## aesop_CategoryTheory_proc
Aesop 规则集 'CategoryTheory' 中的 simprocs

## aesop_Continuous
Aesop 规则集 'Continuous' 中的 simp 定理

## aesop_Continuous_proc
Aesop 规则集 'Continuous' 中的 simprocs

## aesop_IsMultiplicative
Aesop 规则集 'IsMultiplicative' 中的 simp 定理

## aesop_IsMultiplicative_proc
Aesop 规则集 'IsMultiplicative' 中的 simprocs

## aesop_Matroid
Aesop 规则集 'Matroid' 中的 simp 定理

## aesop_Matroid_proc
Aesop 规则集 'Matroid' 中的 simprocs

## aesop_Measurable
Aesop 规则集 'Measurable' 中的 simp 定理

## aesop_Measurable_proc
Aesop 规则集 'Measurable' 中的 simprocs

## aesop_Restrict
Aesop 规则集 'Restrict' 中的 simp 定理

## aesop_Restrict_proc
Aesop 规则集 'Restrict' 中的 simprocs

## aesop_SetLike
Aesop 规则集 'SetLike' 中的 simp 定理

## aesop_SetLike_proc
Aesop 规则集 'SetLike' 中的 simprocs

## aesop_SimpleGraph
Aesop 规则集 'SimpleGraph' 中的 simp 定理

## aesop_SimpleGraph_proc
Aesop 规则集 'SimpleGraph' 中的 simprocs

## aesop_Sym2
Aesop 规则集 'Sym2' 中的 simp 定理

## aesop_Sym2_proc
Aesop 规则集 'Sym2' 中的 simprocs

## aesop_builtin
Aesop 规则集 'builtin' 中的 simp 定理

## aesop_builtin_proc
Aesop 规则集 'builtin' 中的 simprocs

## aesop_default
Aesop 规则集 'default' 中的 simp 定理

## aesop_default_proc
Aesop 规则集 'default' 中的 simprocs

## aesop_finiteness
Aesop 规则集 'finiteness' 中的 simp 定理

## aesop_finiteness_proc
Aesop 规则集 'finiteness' 中的 simprocs

## aesop_finsetNonempty
Aesop 规则集 'finsetNonempty' 中的 simp 定理

## aesop_finsetNonempty_proc
Aesop 规则集 'finsetNonempty' 中的 simprocs

## algebraize
标记允许 `algebraize` 策略知道哪个 `Algebra` 属性对应于此 `RingHom` 属性。
用户属性，用于标记可以转换为 `Algebra` 属性的 `RingHom` 属性。使用（可选的）参数时，它还会生成声明名称，帮助 `algebraize` 策略访问相应的 `Algebra` 属性。

对应此名称的声明有两种情况：

1. 归纳类型（即 `Algebra` 属性本身），此时假设 `RingHom` 和 `Algebra` 属性在定义上相同，策略将通过将 `RingHom` 属性作为项来构造 `Algebra` 属性。
2. 从 `RingHom` 属性证明 `Algebra` 属性的引理（或构造器）。此时假设 `RingHom` 属性是最后一个显式参数，且不需要其他显式参数。策略通过应用引理或构造器来构造 `Algebra` 属性。

最后，如果未向 `algebraize` 属性提供参数，则假设标记声明的名称为 `RingHom.Property`，对应的 `Algebra` 属性名称为 `Algebra.Property`。属性随后返回 `Algebra.Property`（因此假设上述情况1）。

## always_inline
标记定义以始终内联

## app_unexpander
为给定常量的应用注册反展开器。

[app_unexpander c] 为常量 `c` 的应用注册 `Lean.PrettyPrinter.Unexpander`。反展开器被传递预打印应用的结果，不包括隐式传递的参数。如果 `pp.explicit` 设置为 true 或 `pp.notation` 设置为 false，则根本不会调用它。

## attr_parser
解析器

## bitvec_to_nat
将 `BitVec` 目标转换为 `Nat` 目标的 simp 引理

## boolToPropSimps
将基于 `decide` 的布尔表达式转换为命题语句的 simp 引理

## bool_to_prop
将基于 `decide` 的布尔表达式转换为命题语句的 simp 引理

## bound
将定理注册为 `bound` 策略的应用规则。
将引理注册为 `bound` 策略的 `apply` 规则。

适合 `bound` 的引理是通过结构上更简单的不等式证明不等式，假设在有用处为正性或非负性，递归处理涉及表达式的结构。例如：
1. 类似 `gcongr` 的 `<` 和 `≤` 不等式，如 `f x ≤ f y`，其中 `f` 是单调的（注意 `gcongr` 支持其他关系）。
2. `mul_le_mul`，通过 `a ≤ c ∧ b ≤ d ∧ 0 ≤ b ∧ 0 ≤ c` 证明 `a * b ≤ c * d`
3. 正性或非负性不等式，如 `sub_nonneg`：`a ≤ b → 0 ≤ b - a`
4. 涉及 `1` 的不等式，如 `one_le_div` 或 `Real.one_le_exp`
5. 自然递归分支的析取，如 `a ^ n ≤ a ^ m`，其中 `n,m` 的不等式取决于 `1 ≤ a ∨ a ≤ 1`

每个 `@[bound]` 引理根据其假设的数量和复杂性分配分数，`aesop` 实现优先选择分数较低的引理：
1. 涉及 `0` 的不等式假设增加 1 分。
2. 一般不等式增加 10 分。
3. 析取 `a ∨ b` 增加 100 分加上 `a` 和 `b` 分数的总和。

`bound` 的功能与 `positivity` 和 `gcongr` 重叠，但可以在 `0 ≤ x` 和 `x ≤ y` 类型的不等式之间来回跳跃。例如，`bound` 通过将目标转换为 `b * c ≤ a * c`，然后使用 `mul_le_mul_of_nonneg_right` 证明 `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`。`bound` 还为形式为 `1 ≤ x, 1 < x, x ≤ 1, x < 1` 的目标使用专门的引理。

另见 `@[bound_forward]`，它将引理标记为 `bound` 的前向规则：这些引理应用于假设以提取不等式（例如 `HasPowerSeriesOnBall.r_pos`）。

## builtin_attr_parser
内置解析器

## builtin_category_parenthesizer
（内置）为语法类别注册括号器。

  [category_parenthesizer cat] 为类别 `cat` 注册类型为 `Lean.PrettyPrinter.CategoryParenthesizer` 的声明，用于括号化 `categoryParser cat prec` 的调用。实现应调用 `maybeParenthesize` 并传递优先级和 `cat`。如果未注册类别括号器，则类别永远不会被括号化，但仍会遍历以括号化嵌套类别。

## builtin_code_action_provider
（内置）用于装饰建议代码动作的方法。这是制作代码动作的低级接口。

## builtin_command_code_action
声明新的内置命令代码动作，出现在命令的代码动作中

## builtin_command_elab
（内置）命令精化器

## builtin_command_parser
内置解析器

## builtin_delab
（内置）注册反精化器。

  [delab k] 为 `Lean.Expr` 构造函数 `k` 注册类型为 `Lean.PrettyPrinter.Delaborator.Delab` 的声明。为单个构造函数注册的多个反精化器依次尝试，直到首次成功。如果待反精化的项是常量 `c` 的应用，则首先尝试 `app.c` 的反精化器；对于 `Expr.const`（“零元应用”）也这样做以减少特殊情况处理。如果项是具有单个键 `k` 的 `Expr.mdata`，则首先尝试 `mdata.k`。

## builtin_doElem_parser
内置解析器

## builtin_doc
使此声明的文档和位置作为内置可用

## builtin_formatter
（内置）为解析器注册格式化器。

  [formatter k] 为 `SyntaxNodeKind` `k` 注册类型为 `Lean.PrettyPrinter.Formatter` 的声明。

## builtin_incremental
（内置）将精化器（当前为策略或命令）标记为支持增量精化。对于未标记的精化器，精化上下文中的相应快照包字段未设置，以防止意外的不正确重用。

## builtin_inductive_elab
 (builtin) 为归纳类型注册一个展开器
用于注册归纳类型展开器命令的环境扩展。

## builtin_init
 全局引用的初始化过程

## builtin_level_parser
 内置解析器

## builtin_macro
 (builtin) 宏展开器

## builtin_missing_docs_handler
 (builtin) 为缺失文档的 linter 添加语法遍历

## builtin_parenthesizer
 (builtin) 为解析器注册括号化器。

  [parenthesizer k] 为语法节点类型 `k` 注册一个类型为 `Lean.PrettyPrinter.Parenthesizer` 的声明。

## builtin_prec_parser
 内置解析器

## builtin_prio_parser
 内置解析器

## builtin_quot_precheck
 (builtin) 注册双反引号语法引用的预检查。

[quot_precheck k] 为语法节点类型 `k` 注册一个类型为 `Lean.Elab.Term.Quotation.Precheck` 的声明。
它应对传递的语法执行急切名称分析，对未绑定的标识符抛出异常，并在嵌套项上递归调用 `precheck`，可能带有扩展的本地上下文（`withNewLocal`）。
未注册预检查钩子的宏将被展开，最终假设无标识符的语法是良构的。

## builtin_structInstFieldDecl_parser
 内置解析器

## builtin_syntax_parser
 内置解析器

## builtin_tactic
 (builtin) 策略展开器

## builtin_tactic_parser
 内置解析器

## builtin_term_elab
 (builtin) 项展开器

## builtin_term_parser
 内置解析器

## builtin_unused_variables_ignore_fn
 (builtin) 标记一个类型为 `Lean.Linter.IgnoreFunction` 的函数，用于抑制未使用变量的警告
添加 `@[{builtin_}unused_variables_ignore_fn]` 属性，该属性应用于类型为 `IgnoreFunction` 的声明，供未使用变量 linter 使用。

## builtin_widget_module
 (builtin) 注册一个小组件模块。其类型必须实现 `Lean.Widget.ToModule`。
注册一个小组件模块。其类型必须实现 `Lean.Widget.ToModule`。

## bvNormalizeProcBuiltinAttr
 内置 bv_normalize 模拟过程

## bv_normalize
 bv_normalize 使用的简化定理

## bv_normalize_proc
 bv_normalize 使用的模拟过程

## bv_toNat
 将 `BitVec` 目标转换为 `Nat` 目标的简化引理，用于 `bv_omega` 预处理程序

## cases_eliminator
 用于 `cases` 策略的自定义 `casesOn` 类消除器

## category_parenthesizer
 为语法类别注册括号化器。

  [category_parenthesizer cat] 为类别 `cat` 注册一个类型为 `Lean.PrettyPrinter.CategoryParenthesizer` 的声明，
  用于在父级化调用 `categoryParser cat prec` 时使用。实现应使用优先级和 `cat` 调用 `maybeParenthesize`。
  若未注册类别括号化器，则该类别永远不会被父级化，但仍会遍历以父级化嵌套类别。

## class
 类型类

## code_action_provider
 用于装饰建议代码动作的方法。这是生成代码动作的低级接口。

## coe
 将定义添加为强制转换

## coe_decl
 用于实现强制转换的辅助定义（在展开期间展开）

## combinator_formatter
 为解析器组合器注册格式化器。

  [combinator_formatter c] 为解析器声明 `c` 注册一个类型为 `Lean.PrettyPrinter.Formatter` 的声明。
  注意，与 [formatter] 不同，这不是节点类型，因为组合器通常不会引入自己的节点类型。
  标记的声明可以选择性地接受与 `c` 参数（前缀）对应的参数，其中参数类型中的 `Parser` 替换为 `Formatter`。

## combinator_parenthesizer
 为解析器组合器注册括号化器。

  [combinator_parenthesizer c] 为解析器声明 `c` 注册一个类型为 `Lean.PrettyPrinter.Parenthesizer` 的声明。
  注意，与 [parenthesizer] 不同，这不是节点类型，因为组合器通常不会引入自己的节点类型。
  标记的声明可以选择性地接受与 `c` 参数（前缀）对应的参数，其中参数类型中的 `Parser` 替换为 `Parenthesizer`。

## command_code_action
 声明一个新的命令代码动作，以在命令的代码动作中出现

## command_elab
 命令展开器

## command_parser
 解析器

## computed_field
 将函数标记为归纳类型的计算字段

## congr
 同余定理

## cpass
 代码生成器的编译器传递

## csimp
 编译器的简化定理

## default_instance
 类型类默认实例

## delab
 注册反展开器。

  [delab k] 为 `Lean.Expr` 构造器 `k` 注册一个类型为 `Lean.PrettyPrinter.Delaborator.Delab` 的声明。
  单个构造器的多个反展开器将依次尝试，直到第一个成功。若待反展开的项是常量 `c` 的应用，
  则首先尝试 `app.c` 的反展开器；对于 `Expr.const`（“零元应用”）也是如此，以减少特殊情况处理。
  若项是具有单个键 `k` 的 `Expr.mdata`，则首先尝试 `mdata.k`。

## deprecated
 将声明标记为已弃用

## doElem_parser
 解析器

## elab_as_elim
 指示展开器应将函数应用的参数作为消除器展开

## elab_without_expected_type
 标记应在没有预期类型的情况下展开给定声明的应用

## elementwise
 

## enat_to_nat_coe
 用于在 `enat_to_nat` 中推动从 `ℕ` 到 `ℕ∞` 强制转换的简化集。

## enat_to_nat_coe_proc
 enat_to_nat_coe_proc 的模拟过程集

## enat_to_nat_top
 用于在 `enat_to_nat` 中简化涉及 `⊤` 的表达式的简化集。

## enat_to_nat_top_proc
 enat_to_nat_top_proc 的模拟过程集

## env_linter
 在 #lint 中将此声明用作 lint 测试

## eqns
 将声明的方程引理覆盖为提供的列表
类似于 `registerParametricAttribute`，但属性不必在与声明相同的文件中分配。

## export
 供代码生成器使用的名称

## expr_presenter
 注册一个 Expr 展示器。其类型必须为 `ProofWidgets.ExprPresenter`。
注册一个 Expr 展示器。其类型必须为 `ProofWidgets.ExprPresenter`。

## ext
 将定理标记为外延性定理

## extern
 内置和外部函数

## field_simps
 简化集 `field_simps` 由策略 `field_simp` 使用，
将字段中的表达式简化为形式 `n / d`，其中 `n` 和 `d` 无除法。

## field_simps_proc
 field_simps_proc 的模拟过程集

## fin_omega
 用于 `fin_omega` 包装器围绕 `omega` 的简化集。

## fin_omega_proc
 fin_omega_proc 的模拟过程集

## formatter
 为解析器注册格式化器。

  [formatter k] 为语法节点类型 `k` 注册一个类型为 `Lean.PrettyPrinter.Formatter` 的声明。

## fun_prop
 `fun_prop` 策略用于证明函数属性，如 `Continuous`、`Differentiable`、`IsLinearMap`
初始化 `funProp` 属性

## functor_norm
 `functor_norm` 的简化集 

## functor_norm_proc
 functor_norm_proc 的模拟过程集

## gcongr
 广义同余
属性标记“广义同余”（`gcongr`）引理。此类引理的结论必须具有诸如 `f x₁ y z₁ ∼ f x₂ y z₂` 的形式；
即，函数应用到两个参数列表之间的关系，其中“变化参数”对（此处为 `x₁`/`x₂` 和 `z₁`/`z₂`）均为自由变量。

此类引理的前件若形式为某个“变化参数”对 `x₁`/`x₂` 的 `x₁ ≈ x₂`（且可能不同的关系 `≈` 到 `∼`），
或更一般地形式为 `∀ i h h' j h'', f₁ i j ≈ f₂ i j`（例如），则被分类为生成“主要目标”。
（其他前件被视为生成“次要目标”。）每个“主要”前件对应的“变化参数”对的索引被记录。

涉及 `<` 或 `≤` 的引理也可标记 `@[bound]`，供相关 `bound` 策略使用。

## builtin_inductive_elab
 (builtin) 为归纳类型注册一个展开器
用于注册归纳类型展开器命令的环境扩展。

## builtin_init
 全局引用的初始化过程

## builtin_level_parser
 内置解析器

## builtin_macro
 (builtin) 宏展开器

## builtin_missing_docs_handler
 (builtin) 为缺失文档的 linter 添加语法遍历

## builtin_parenthesizer
 (builtin) 为解析器注册括号化器。

  [parenthesizer k] 为语法节点类型 `k` 注册一个类型为 `Lean.PrettyPrinter.Parenthesizer` 的声明。

## builtin_prec_parser
 内置解析器

## builtin_prio_parser
 内置解析器

## builtin_quot_precheck
 (builtin) 注册双反引号语法引用的预检查。

[quot_precheck k] 为语法节点类型 `k` 注册一个类型为 `Lean.Elab.Term.Quotation.Precheck` 的声明。
它应对传递的语法执行急切名称分析，对未绑定的标识符抛出异常，并在嵌套项上递归调用 `precheck`，可能带有扩展的本地上下文（`withNewLocal`）。
未注册预检查钩子的宏将被展开，最终假设无标识符的语法是良构的。

## builtin_structInstFieldDecl_parser
 内置解析器

## builtin_syntax_parser
 内置解析器

## builtin_tactic
 (builtin) 策略展开器

## builtin_tactic_parser
 内置解析器

## builtin_term_elab
 (builtin) 项展开器

## builtin_term_parser
 内置解析器

## builtin_unused_variables_ignore_fn
 (builtin) 标记一个类型为 `Lean.Linter.IgnoreFunction` 的函数，用于抑制未使用变量的警告
添加 `@[{builtin_}unused_variables_ignore_fn]` 属性，该属性应用于类型为 `IgnoreFunction` 的声明，供未使用变量 linter 使用。

## builtin_widget_module
 (builtin) 注册一个小组件模块。其类型必须实现 `Lean.Widget.ToModule`。
注册一个小组件模块。其类型必须实现 `Lean.Widget.ToModule`。

## bvNormalizeProcBuiltinAttr
 内置 bv_normalize 模拟过程

## bv_normalize
 bv_normalize 使用的简化定理

## bv_normalize_proc
 bv_normalize 使用的模拟过程

## bv_toNat
 将 `BitVec` 目标转换为 `Nat` 目标的简化引理，用于 `bv_omega` 预处理程序

## cases_eliminator
 用于 `cases` 策略的自定义 `casesOn` 类消除器

## category_parenthesizer
 为语法类别注册括号化器。

  [category_parenthesizer cat] 为类别 `cat` 注册一个类型为 `Lean.PrettyPrinter.CategoryParenthesizer` 的声明，
  用于在父级化调用 `categoryParser cat prec` 时使用。实现应使用优先级和 `cat` 调用 `maybeParenthesize`。
  若未注册类别括号化器，则该类别永远不会被父级化，但仍会遍历以父级化嵌套类别。

## class
 类型类

## code_action_provider
 用于装饰建议代码动作的方法。这是生成代码动作的低级接口。

## coe
 将定义添加为强制转换

## coe_decl
 用于实现强制转换的辅助定义（在展开期间展开）

## combinator_formatter
 为解析器组合器注册格式化器。

  [combinator_formatter c] 为解析器声明 `c` 注册一个类型为 `Lean.PrettyPrinter.Formatter` 的声明。
  注意，与 [formatter] 不同，这不是节点类型，因为组合器通常不会引入自己的节点类型。
  标记的声明可以选择性地接受与 `c` 参数（前缀）对应的参数，其中参数类型中的 `Parser` 替换为 `Formatter`。

## combinator_parenthesizer
 为解析器组合器注册括号化器。

  [combinator_parenthesizer c] 为解析器声明 `c` 注册一个类型为 `Lean.PrettyPrinter.Parenthesizer` 的声明。
  注意，与 [parenthesizer] 不同，这不是节点类型，因为组合器通常不会引入自己的节点类型。
  标记的声明可以选择性地接受与 `c` 参数（前缀）对应的参数，其中参数类型中的 `Parser` 替换为 `Parenthesizer`。

## command_code_action
 声明一个新的命令代码动作，以在命令的代码动作中出现

## command_elab
 命令展开器

## command_parser
 解析器

## computed_field
 将函数标记为归纳类型的计算字段

## congr
 同余定理

## cpass
 代码生成器的编译器传递

## csimp
 编译器的简化定理

## default_instance
 类型类默认实例

## delab
 注册反展开器。

  [delab k] 为 `Lean.Expr` 构造器 `k` 注册一个类型为 `Lean.PrettyPrinter.Delaborator.Delab` 的声明。
  单个构造器的多个反展开器将依次尝试，直到第一个成功。若待反展开的项是常量 `c` 的应用，
  则首先尝试 `app.c` 的反展开器；对于 `Expr.const`（“零元应用”）也是如此，以减少特殊情况处理。
  若项是具有单个键 `k` 的 `Expr.mdata`，则首先尝试 `mdata.k`。

## deprecated
 将声明标记为已弃用

## doElem_parser
 解析器

## elab_as_elim
 指示展开器应将函数应用的参数作为消除器展开

## elab_without_expected_type
 标记应在没有预期类型的情况下展开给定声明的应用

## elementwise
 

## enat_to_nat_coe
 用于在 `enat_to_nat` 中推动从 `ℕ` 到 `ℕ∞` 强制转换的简化集。

## enat_to_nat_coe_proc
 enat_to_nat_coe_proc 的模拟过程集

## enat_to_nat_top
 用于在 `enat_to_nat` 中简化涉及 `⊤` 的表达式的简化集。

## enat_to_nat_top_proc
 enat_to_nat_top_proc 的模拟过程集

## env_linter
 在 #lint 中将此声明用作 lint 测试

## eqns
 将声明的方程引理覆盖为提供的列表
类似于 `registerParametricAttribute`，但属性不必在与声明相同的文件中分配。

## export
 供代码生成器使用的名称

## expr_presenter
 注册一个 Expr 展示器。其类型必须为 `ProofWidgets.ExprPresenter`。
注册一个 Expr 展示器。其类型必须为 `ProofWidgets.ExprPresenter`。

## ext
 将定理标记为外延性定理

## extern
 内置和外部函数

## field_simps
 简化集 `field_simps` 由策略 `field_simp` 使用，
将字段中的表达式简化为形式 `n / d`，其中 `n` 和 `d` 无除法。

## field_simps_proc
 field_simps_proc 的模拟过程集

## fin_omega
 用于 `fin_omega` 包装器围绕 `omega` 的简化集。

## fin_omega_proc
 fin_omega_proc 的模拟过程集

## formatter
 为解析器注册格式化器。

  [formatter k] 为语法节点类型 `k` 注册一个类型为 `Lean.PrettyPrinter.Formatter` 的声明。

## fun_prop
 `fun_prop` 策略用于证明函数属性，如 `Continuous`、`Differentiable`、`IsLinearMap`
初始化 `funProp` 属性

## functor_norm
 `functor_norm` 的简化集 

## functor_norm_proc
 functor_norm_proc 的模拟过程集

## gcongr
 广义同余
属性标记“广义同余”（`gcongr`）引理。此类引理的结论必须具有诸如 `f x₁ y z₁ ∼ f x₂ y z₂` 的形式；
即，函数应用到两个参数列表之间的关系，其中“变化参数”对（此处为 `x₁`/`x₂` 和 `z₁`/`z₂`）均为自由变量。

此类引理的前件若形式为某个“变化参数”对 `x₁`/`x₂` 的 `x₁ ≈ x₂`（且可能不同的关系 `≈` 到 `∼`），
或更一般地形式为 `∀ i h h' j h'', f₁ i j ≈ f₂ i j`（例如），则被分类为生成“主要目标”。
（其他前件被视为生成“次要目标”。）每个“主要”前件对应的“变化参数”对的索引被记录。

涉及 `<` 或 `≤` 的引理也可标记 `@[bound]`，供相关 `bound` 策略使用。

## gcongr_forward
 添加一个 `gcongr_forward` 扩展

## ghost_simps
 用于幽灵方程的简化规则。

## ghost_simps_proc
 `ghost_simps_proc` 的模拟过程集合

## grind
 `[grind]` 属性用于标注声明。当应用于等式定理时，`[grind =]`、`[grind =_]` 或 `[grind _=_]` 将标记该定理供 `grind` 策略在启发式实例化中使用，分别使用定理的左侧、右侧或两侧。当应用于函数时，`[grind =]` 自动标注与该函数关联的等式定理。当应用于定理 `[grind ←]` 时，每当遇到定理的结论时将实例化该定理（即，将定理用于逆向推理）。当应用于定理 `[grind →]` 时，每当遇到足够多的命题假设时将实例化该定理（即，将定理用于前向推理）。单独使用 `[grind]` 属性将有效尝试 `[grind ←]`（如果结论足以进行实例化）然后 `[grind →]`。`grind` 策略利用标注的定理在证明搜索期间将匹配模式的实例添加到本地上下文中。例如，如果标注了定理 `@[grind =] theorem foo_idempotent : foo (foo x) = foo x`，`grind` 将在遇到模式 `foo (foo x)` 时将此定理的实例添加到本地上下文中。

## grindPropagatorBuiltinAttr
 内置的 `grind` 传播器过程

## higherOrder
 从形如 `∀ x, f (g x) = h x` 的引理派生出一个辅助引理 `f ∘ g = h`，用于高阶函数的推理。

语法：`[higher_order]` 或 `[higher_order 名称]`，其中给定名称用于生成的定理。
`higher_order` 属性。从形如 `∀ x, f (g x) = h x` 的引理派生出一个辅助引理 `f ∘ g = h`，用于高阶函数的推理。

语法：`[higher_order]` 或 `[higher_order 名称]`，其中给定名称用于生成的定理。

## hole_code_action
 声明一个新的孔代码动作，出现在 `?_` 和 `_` 的代码动作中

## implemented_by
 实现不透明常量的 Lean（可能不安全的）函数的名称

## incremental
 标记一个支持增量细化的细化器（目前为策略或命令）。对于未标记的细化器，细化上下文中的相应快照包字段未设置，以防止意外错误的重用。

## induction_eliminator
 `induction` 策略的自定义 `rec` 类消除器

## inductive_elab
 注册归纳类型的细化器
环境扩展以注册归纳类型细化器命令。

## inherit_doc
 从指定声明继承文档

## init
 全局引用的初始化过程

## inline
 标记要内联的定义

## inline_if_reduce
 标记当简化后的结果项不是 `cases_on` 应用时要内联的定义

## instance
 类型类实例

## int_toBitVec
 用于将 UIntX/IntX 语句转换为 BitVec 语句的简化定理

## integral_simps
 积分规则的简化集合。

## integral_simps_proc
 `integral_simps_proc` 的模拟过程集合

## irreducible
 不可约声明

## is_poly
 `is_poly` 的存根属性。

## macro
 宏细化器

## macro_inline
 标记定义在 ANF 转换前始终内联

## match_pattern
 标记定义可用于模式（备注：依赖模式匹配编译器将展开该定义）

## mfld_simps
 简化集 `mfld_simps` 记录了多个在流形中特别有用的简化引理。它是整个简化引理集的子集，但结合 `squeeze_simp` 或 `simp only` 使用时，可以在保持可读性的同时加快证明速度。

典型用例是在流形相关文件中：如果 `simp [foo, bar]` 速度慢，可替换为 `squeeze_simp [foo, bar, mfld_simps]` 并粘贴其输出。引理列表应合理（与 `squeeze_simp [foo, bar]` 可能包含数十条引理的输出相反），且结果应足够快。

## mfld_simps_proc
 `mfld_simps_proc` 的模拟过程集合

## missing_docs_handler
 添加缺失文档 linter 的语法遍历

## mkIff
 为归纳 `Prop` 生成 `iff` 引理。

## monad_norm
 `functor_norm` 的简化集

## monad_norm_proc
 `monad_norm_proc` 的模拟过程集合

## mono
 陈述某些函数在适当域和范围关系下的单调性的引理，可能附带条件。

## multigoal
 此策略作用于多个目标
`multigoal` 属性跟踪作用于多个目标的策略，意味着 `tac` 的行为与 `focus tac` 不同。这用于“不必要的 `<;>`” linter 以防止误报，其中 `tac <;> tac'` 无法替换为 `(tac; tac')`，因为后者将暴露 `tac` 到不同的目标集。

## never_extract
 指示编译器在提取闭项时不应提取使用标记声明的函数应用，也不应执行公共子表达式消除。这对于具有隐式效果的声明很有用。

## noinline
 标记定义永不内联

## nolint
 不在 `#lint` 的任何测试中报告此声明
定义用户属性 `nolint` 以跳过 `#lint`

## nontriviality
 `@[nontriviality]` 简化集被 `nontriviality` 策略用于自动处理平凡情况（已知 `Subsingleton α` 时，许多群论定理等均平凡成立）。

## nontriviality_proc
 `nontriviality_proc` 的模拟过程集合

## norm_cast
 `norm_cast` 的属性

## norm_num
 添加 `norm_num` 扩展

## nospecialize
 标记定义永不特化

## notation_class
 指定此为符号类的属性。由 `@[simps]` 使用。
`@[notation_class]` 属性。注意：这不是 `NameMapAttribute`，因为我们根据属性参数而非声明名称键控。

## parenthesizer
 为解析器注册括号器。

  [parenthesizer k] 为 `SyntaxNodeKind` `k` 注册类型为 `Lean.PrettyPrinter.Parenthesizer` 的声明。

## parity_simps
 `Even` 相关引理的简化属性

## parity_simps_proc
 `parity_simps_proc` 的模拟过程集合

## partial_fixpoint_monotone
 单调性定理

## pnat_to_nat_coe
 `pnat_to_nat` 策略的简化集合。

## pnat_to_nat_coe_proc
 `pnat_to_nat_coe_proc` 的模拟过程集合

## positivity
 添加 `positivity` 扩展

## ppWithUnivAttr
 

## pp_nodot
 标记声明永不使用字段符号进行漂亮打印

## pp_using_anonymous_constructor
 标记结构体使用 `⟨a,b,c⟩` 符号进行漂亮打印

## prec_parser
 解析器

## prio_parser
 解析器

## push_cast
 `push_cast` 简化属性使用 `norm_cast` 引理将强制转换向表达式的叶节点移动。
`push_cast` 简化属性。

## qify_simps
 简化集 `qify_simps` 被 `qify` 策略用于将表达式从 `ℕ` 或 `ℤ` 移动到 `ℚ`，从而获得良好行为的除法。

## qify_simps_proc
 `qify_simps_proc` 的模拟过程集合

## quot_precheck
 注册双反引号语法引用预检查。

[quot_precheck k] 为 `SyntaxNodeKind` `k` 注册类型为 `Lean.Elab.Term.Quotation.Precheck` 的声明。它应通过对传递的语法进行急切名称分析，在未绑定标识符时抛出异常，并在嵌套项上递归调用 `precheck`，可能带有扩展的本地上下文（`withNewLocal`）。未注册预检查钩子的宏被展开，最终假设无标识符的语法是良构的。

## rclike_simps
 `RCLike` 相关引理的简化属性

## rclike_simps_proc
 `rclike_simps_proc` 的模拟过程集合

## reassoc
 

## recursor
 用户定义的递归器，数值参数指定主要前提的位置

## reduce_mod_char
 用于`reduce_mod_char`策略中预处理和清理的引理
`@[reduce_mod_char]`是一个属性，用于标记在`reduce_mod_char`策略中进行预处理和清理的引理

## reducible
 可约简声明

## refl
 自反关系

## rify_simps
 simpset `rify_simps`被策略`rify`用来将表达式从`ℕ`、`ℤ`或`ℚ`移动到`ℝ`

## rify_simps_proc
 用于`rify_simps_proc`的simproc集合

## run_builtin_parser_attribute_hooks
 显式运行通常由内置解析器属性激活的钩子

## run_parser_attribute_hooks
 显式运行通常由解析器属性激活的钩子

## semireducible
 半可约简声明

## server_rpc_method
 将函数标记为Lean服务器RPC方法。
    简写为`registerRpcProcedure`。
    该函数必须具有类型`α → RequestM (RequestTask β)`，且带有`[RpcEncodable α]`和`[RpcEncodable β]`。

## server_rpc_method_cancellable
 类似于`server_rpc_method`，但对此方法的请求可被取消。方法应使用`IO.checkCanceled`进行检查。可取消方法在JavaScript中的调用方式不同：参见`cancellable.ts`中的`callCancellable`。
类似于`server_rpc_method`，但对此方法的请求可被取消。
方法应使用`IO.checkCanceled`进行检查。
可取消方法在JavaScript中的调用方式不同：
参见`cancellable.ts`中的`callCancellable`。

## seval
 符号求值器定理

## sevalprocAttr
 符号求值器过程

## sevalprocBuiltinAttr
 内置符号求值过程

## simp
 简化定理

## simprocAttr
 简化过程

## simprocBuiltinAttr
 内置简化过程

## simps
 自动派生指定此声明投影的引理。
`simps`属性。

## specialize
 标记定义以始终特化

## stacksTag
 将Stacks或Kerodon项目标签应用于定理。

## stx_parser
 解析器

## symm
 对称关系

## tactic
 策略扩展器

## tactic_alt
 将策略解析器注册为现有策略的替代形式，以便在文档中分组展示。

## tactic_code_action
 声明新的策略代码操作，以在策略的代码操作中显示

## tactic_parser
 解析器

## tactic_tag
 将策略解析器注册为现有策略的替代形式，以便在文档中分组展示。

## term_elab
 项扩展器

## term_parser
 解析器

## to_additive
 将乘性结构转换为加性结构

## to_additive_change_numeral
 `to_additive`的辅助属性，存储以数字为参数的函数。
类似于`registerParametricAttribute`，但属性不必在声明所在的同一文件中分配。

## to_additive_dont_translate
 `to_additive`的辅助属性，声明此类型上的操作不应被翻译。
类似于`registerParametricAttribute`，但属性不必在声明所在的同一文件中分配。

## to_additive_ignore_args
 `to_additive`的辅助属性，声明某些参数不被加性化。
类似于`registerParametricAttribute`，但属性不必在声明所在的同一文件中分配。

## to_additive_relevant_arg
 `to_additive`的辅助属性，声明哪些参数是具有乘性结构的类型。
类似于`registerParametricAttribute`，但属性不必在声明所在的同一文件中分配。

## to_additive_reorder
 `to_additive`的辅助属性，存储需要重新排序的参数。此属性不应出现在任何文件中。目前仍保留为属性以便mathport仍可使用它，并生成警告。
类似于`registerParametricAttribute`，但属性不必在声明所在的同一文件中分配。

## to_app
 

## trans
 传递关系

## typevec
 用于操作typevec和箭头表达式的simp集合 

## typevec_proc
 用于`typevec_proc`的simproc集合

## unbox
 如果结果值的类型被标记为`[unbox]`，编译器将尝试拆箱

## unification_hint
 统一提示

## unused_variables_ignore_fn
 标记类型为`Lean.Linter.IgnoreFunction`的函数，用于抑制未使用变量警告
添加`@[{builtin_}unused_variables_ignore_fn]`属性，该属性应用于类型为`IgnoreFunction`的声明，供未使用变量检查器使用。

## variable_alias
 记录`variable?`命令别名的属性。
记录`variable?`命令别名的属性。别名是没有字段的结构体，附加的类型类被记录为结构体的*参数*。

示例：
```lean
@[variable_alias]
structure VectorSpace (k V : Type*)
  [Field k] [AddCommGroup V] [Module k V]
```
然后`variable? [VectorSpace k V]`确保当前作用域中存在这三个类型类。注意它查看的是`VectorSpace`类型构造函数的参数。`variable_alias`结构体中不应有任何字段。

注意`VectorSpace`不是类；`variable?`命令允许具有`variable_alias`属性的非类使用实例绑定器。

## wf_preprocess
 用于预处理良基递归函数定义的simp引理，特别是向上下文添加额外假设。另见`wfParam`。

## widget_module
 注册小部件模块。其类型必须实现`Lean.Widget.ToModule`。
注册小部件模块。其类型必须实现`Lean.Widget.ToModule`。

## zify_simps
 simpset `zify_simps`被策略`zify`用来将表达式从`ℕ`移动到`ℤ`，从而获得良好行为的减法。   ## zify_simps_proc
 用于`zify_simps_proc`的simproc集合