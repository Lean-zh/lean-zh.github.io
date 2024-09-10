<!-- 
# Lake
-->

# Lake 官方文档
***

<!--
Lake (Lean Make) is the new build system and package manager for Lean 4. With Lake, the package's configuration is written in Lean inside a dedicated `lakefile.lean` stored in the root of the package's directory.
-->

Lake（Lean Make）是 Lean 4 新的构建系统和包管理器。借助 Lake，包的配置可以写入位于包根目录下的专用 `lakefile.lean` 文件中。

<!--
Each `lakefile.lean` includes a `package` declaration (akin to `main`) which defines the package's basic configuration. It also typically includes build configurations for different targets (e.g., Lean libraries and binary executables) and Lean scripts to run on the command line (via `lake script run`).
-->

每个 `lakefile.lean` 文件包含一个 `package` 声明（类似于 `main` 函数），用于定义包的基本配置。通常，还包括不同目标的构建配置（例如 Lean 库文件和二进制可执行文件），以及通过 `lake script run` 运行的命令行脚本。

<!--
_**This README provides information about Lake relative to the current commit. If you are looking for documentation for the Lake version shipped with a given Lean release, you should look at the README of that version.**_
-->

_**此 README 提供了与当前提交相关的 Lake 信息。如果您正在查找随特定 Lean 版本发布的 Lake 文档，请查看该版本的 README。**_


<!--
## Getting Lake
-->

## 获取 Lake

<!--
Lake is part of the [lean4](https://github.com/leanprover/lean4) repository and is distributed along with its official releases (e.g., as part of the [elan](https://github.com/leanprover/elan) toolchain). So if you have installed a semi-recent Lean 4 nightly, you should already have it! If you want to build the latest version from the source yourself, check out the [build instructions](https://github.com/leanprover/lean4/tree/master/src/lake#building-and-running-lake-from-the-source) at the bottom of this README.
-->

Lake 是 [lean4](https://github.com/leanprover/lean4) 仓库的一部分，随其官方版本一同发布（例如，作为 [elan](https://github.com/leanprover/elan) 工具链的一部分）。所以，如果你已经安装了近期版本的 Lean 4，你也应该已经拥有了 Lake！如果你想自己从源码构建最新版本，请参阅此 README 最后的[构建指南](https://github.com/leanprover/lean4/tree/master/src/lake#building-and-running-lake-from-the-source)。

<!--
## Creating and Building a Package
-->

## 创建并构建一个包

<!--
To create a new package, either run `lake init` to setup the package in the current directory or `lake new` to create it in a new directory. For example, we could create the package `hello` like so:
-->

要创建一个新包，可以运行 `lake init` 在当前目录中设置包，或运行 `lake new` 在新目录中创建包。例如，我们可以这样创建包 `hello`：

```bash
$ mkdir hello
$ cd hello
$ lake init hello
```

<!--
or like so:
-->

或者这样：

```bash
$ lake new hello
$ cd hello
```

<!--
Either way, Lake will create the following template directory structure and initialize a Git repository for the package.
-->

无论采用哪种方式，Lake 都会创建如下模板目录结构并为包初始化一个 Git 仓库。

<!--
```
.lake/         # Lake output directory
Hello/         # library source files; accessible via `import Hello.*`
  Basic.lean   # an example library module file
  ...          # additional files should be added here
Hello.lean     # library root; imports standard modules from Hello
Main.lean      # main file of the executable (contains `def main`)
lakefile.lean  # Lake package configuration
lean-toolchain # the Lean version used by the package
.gitignore     # excludes system-specific files (e.g. `build`) from Git
```
-->

```bash
.lake/         # Lake 的输出目录
Hello/         # 库的源文件目录; 通过 `import Hello.*` 导入
  Basic.lean   # 一个示例库模块文件
  ...          # 在此处添加其他文件
Hello.lean     # 库的根文件; 从 Hello 导入标准模块
Main.lean      # 可执行文件的主文件 (含 `def main`)
lakefile.lean  # Lake 的包配置文件
lean-toolchain # 包所使用的 Lean 版本
.gitignore     # 排除系统特定文件 (如 `build`) 从 Git 版本控制中
```

<!--
The example modules files contain the following dummy "Hello World" program.
-->

示例模块文件包含以下 "Hello World" 程序。

**Hello/Basic.lean**

```lean
def hello := "world"
```

**Hello.lean**

<!--
```lean
-- This module serves as the root of the `Hello` library.
-- Import modules here that should be built as part of the library.
import «Hello».Basic
```
-->

```lean
-- 这个模块是 `Hello` 库的根文件
-- 在这里导入应作为库一部分构建的模块。
import «Hello».Basic
```

**Main.lean**

```lean
import «Hello»

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

<!--
Lake also creates a basic `lakefile.lean` for the package along with a `lean-toolchain` file that contains the name of the Lean toolchain Lake belongs to, which tells [`elan`](https://github.com/leanprover/elan) to use that Lean toolchain for the package.
-->

Lake 还会为包创建一个基础的 `lakefile.lean` 文件以及一个包含 Lean 工具链名称的 `lean-toolchain` 文件，这样 [elan](https://github.com/leanprover/elan) 就知道该为这个包使用哪个 Lean 工具链。

**lakefile.lean**

<!--
import Lake
open Lake DSL

package «hello» where
  -- add package configuration options here

lean_lib «Hello» where
  -- add library configuration options here

@[default_target]
lean_exe «hello» where
  root := `Main
-->
  
```lean
import Lake
open Lake DSL

package «hello» where
  -- 在此添加包配置选项

lean_lib «Hello» where
  -- 在此添加库配置选项

@[default_target]
lean_exe «hello» where
  root := `Main
```

<!--
The command `lake build` is used to build the package (and its [dependencies](https://github.com/leanprover/lean4/tree/master/src/lake#adding-dependencies), if it has them) into a native executable. The result will be placed in `.lake/build/bin`. The command `lake clean` deletes `build`.
-->

`lake build` 命令用于构建包（及其[依赖项](https://github.com/leanprover/lean4/tree/master/src/lake#adding-dependencies)，如果有的话）为本地可执行文件。结果将放置在 `.lake/build/bin` 目录下。`lake clean` 命令会删除 `build` 目录。

```
$ lake build
...
$ ./.lake/build/bin/hello
Hello, world!
```

<!--
Examples of different package configurations can be found in the [`examples`](https://github.com/leanprover/lean4/blob/master/src/lake/examples) folder of this repository. You can also pass a package template tp `lake init` or `lake new` to control what files Lake creates. For example, instead of using a Lean configuration file for this package, one could produce a TOML version via `lake new hello .toml`.
-->

在此仓库的 [`examples`](https://github.com/leanprover/lean4/blob/master/src/lake/examples) 文件夹中可以找到不同包配置的示例。你也可以为 `lake init` 或 `lake new` 命令传入模板以控制 Lake 创建的文件。例如，你可以通过 `lake new hello .toml` 命令生成一个 TOML 版本的配置文件，而不是使用 Lean 配置文件。

**lakefile.toml**

```toml
name = "hello"
defaultTargets = ["hello"]

[[lean_lib]]
name = "Hello"

[[lean_exe]]
name = "hello"
root = "Main"
```

<!--
See `lake help init` or `lake help new` for more details on other template options.
-->

使用 `lake help init` 或 `lake help new` 命令可以查看有关其他模板选项的更多详细信息。

<!--
## Glossary of Terms
-->
## 术语表

<!--
Lake uses a lot of terms common in software development -- like workspace, package, library, executable, target, etc. -- and some more esoteric ones -- like facet. However, whether common or not, these terms mean different things to different people, so it is important to elucidate how Lake defines these terms:
-->

在软件开发过程中，Lake 会用到一系列的术语 —— 如工作空间（workspace）、包（package）、库（library）、可执行文件（executable）、目标（target）等等 —— 还有些更难理解的术语，如 facet。不过，无论这些术语是否常见，不同的人对其都有着不同的理解，因此有必要明确 Lake 对这些术语的定义：

<!--
- A **package** is the **fundamental unit of code distribution in Lake**. Packages can be sourced from the local file system or downloaded from the web (e.g., via Git). The `package` declaration in package's lakefile names it and [defines its basic properties](https://github.com/leanprover/lean4/tree/master/src/lake#package-configuration-options).
-->

- **包（package）** 是 Lake **代码分发的基本单元**。包可以来源于本地文件系统，也可以从网络下载（如通过 Git）。包的 lakefile 中的 `package` 声明决定了包的名称，并[定义其基本属性](https://github.com/leanprover/lean4/tree/master/src/lake#package-configuration-options)。

<!--
- A **lakefile** is the Lean file that configures a package. It defines how to view, edit, build, and run the code within it, and it specifies what other packages it may require in order to do so.
-->

- **lakefile** 是记录整个包配置的 Lean 文件。它定义了如何查看、编辑、构建和运行包中的代码，并指定了所依赖的其它包。

<!--
- If package `B` requires package `A`, then package `A` is a **dependency** of package B and package `B` is its **dependent**. Package `A` is **upstream** of package `B` and package `B` is reversely **downstream** of package `A`. See the [Adding Dependencies section](https://github.com/leanprover/lean4/tree/master/src/lake#adding-dependencies) for details on how to specify dependencies.
-->

- 如果包 B 依赖包 A，包 A 就是包 B 的 **依赖**（dependency），而包 B 就是包 A 的 **下游依赖**（dependent）。包 A 是包 B 的 **上游**，反之包 B 是包 A 的 **下游**。参见[添加依赖](https://github.com/leanprover/lean4/tree/master/src/lake#adding-dependencies) 以了解如何指定依赖。

<!--
- A **workspace** is the **broadest organizational unit in Lake**. It bundles together a package (termed the **root**), its transitive dependencies, and Lake's environment. Every package can operate as the root of a workspace and the workspace will derive its configuration from this root.
-->

- **工作空间（workspace）** 是 Lake 中 **最大的组织单元**。它将一个被称为 **根** 的包、其传递依赖以及 Lake 的环境组合在一起。每个包都可以作为工作区的根，并且工作区将从这个根派生其配置。

<!--
A **module** is the **smallest unit of code visible to Lake's build system**. It is generally represented by a Lean source file and a set of binary libraries (i.e., a Lean `olean` and `ilean` plus a system shared library if `precompileModules` is turned on). Modules can import one another in order to use each other's code and Lake exists primarily to facilitate this process.
-->

- **模块（module）** 是 Lake **构建系统可见的最小代码单元**。模块通常由一个 Lean 源文件和一组二进制库文件（如 `olean` 和 `ilean`，若 `precompileModules` 选项开启，还包括系统共享库）组成。模块之间可以相互导入以使用彼此的代码，Lake 的主要作用就是促进这一过程。

<!--
A **Lean library** is a collection of modules that share a single configuration. Its configuration defines a set of **module roots** that determines which modules are part of the library, and a set of **module globs** that selects which modules to build on a `lake build` of the library. See the [Lean Libraries section](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries) for more details.
-->

- **Lean 库（Lean library）** 是一组共享同一配置的模块集合。其配置定义了一组 **模块根（module roots）**，用于确定哪些模块属于该库，以及一组 **模块全局模式（module globs）**，用于在库的 `lake build` 过程中选择要构建的模块。参见[Lean 库部分](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries)了解更多详情。

<!--
A **Lean binary executable** is a binary executable (i.e., a program a user can run on their computer without Lean installed) built from a Lean module termed its **root** (which should have a `main` definition). See the [Binary Executables section](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables) for more details.
-->

- **Lean 二进制可执行文件（Lean binary executable）** 是一个由根模块（其中应包含 `main` 定义）构建的二进制可执行文件（即用户在未安装 Lean 时就能在电脑上运行的程序）。参见[二进制可执行文件部分](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables)了解更多详情。

<!--
An **external library** is a native (static) library built from foreign code (e.g., C) that is required by a package's Lean code in order to function (e.g., because it uses `@[extern]` to invoke code written in a foreign language). An `extern_lib` target is used to inform Lake of such a requirement and instruct Lake on how to build requisite library. Lake then automatically links the external library when appropriate to give the Lean code access to the foreign functions (or, more technically, the foreign symbols) it needs. See the [External Libraries section](https://github.com/leanprover/lean4/tree/master/src/lake#external-libraries) for more details.
-->

- **外部库（external library）** 是由外部代码（如 C 语言）构建的原生（静态）库，Lean 代码需要这些库来实现功能（例如，使用 `@[extern]` 调用外部代码）。`extern_lib` 目标用于告知 Lake 此类需求并指示 Lake 如何构建必要的库。Lake 随后会在适当时自动链接外部库，以便使 Lean 代码能够访问所需的外部函数（或更专业地说，是外部符号）。参见[外部库部分](https://github.com/leanprover/lean4/tree/master/src/lake#external-libraries)了解更多详情。

<!--
A **target** is the **fundamental build unit of Lake**. A package can defining any number of targets. Each target has a name, which is used to instruct Lake to build the target (e.g., through `lake build <target>`) and to keep track internally of a target's build status. Lake defines a set of builtin target types -- [Lean libraries](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries), [binary executables](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables), and [external libraries](https://github.com/leanprover/lean4/tree/master/src/lake#external-libraries) -- but a user can [define their own custom targets as well](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets). Complex types (e.g., packages, libraries, modules) have multiple facets, each of which count as separate buildable targets. See the [Defining Build Targets section](https://github.com/leanprover/lean4/tree/master/src/lake#defining-build-targets) for more details.
-->

- **目标（target）** 是 Lake **构建的基本单元**。一个包可以定义任意数量的目标。每个目标都有一个名称，用于指示 Lake 去构建该目标（例如，通过 `lake build <target>`）并在内部跟踪目标的构建状态。Lake 定义了一组内置目标类型 —— [Lean 库](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries)、[二进制可执行文件](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables) 和 [外部库](https://github.com/leanprover/lean4/tree/master/src/lake#external-libraries) —— 但用户也可以[定义自己的自定义目标](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets)。复杂类型（如包、库、模块）具有多个 facet，每个 facet 都算作独立的可构建目标。参见[定义构建目标部分](https://github.com/leanprover/lean4/tree/master/src/lake#defining-build-targets)了解更多详情。

<!--
A **facet** is an element built from another organizational unit (e.g., a package, module, library, etc.). For instance, Lake produces `olean`, `ilean`, `c`, and `o` files all from a single module. Each of these components are thus termed a _facet_ of the module. Similarly, Lake can build both static and shared binaries from a library. Thus, libraries have both `static` and `shared` facets. Lake also allows users to define their own custom facets to build from modules and packages, but this feature is currently experimental and not yet documented.
-->

- **facet** 是从其它组织单位构建出的单个元素（如包、模块、库等）。例如，Lake 从单个模块生成 `olean`、`ilean`、`c` 和 `o` 文件，这些组件都被称为该模块的一个 facet。同样地，Lake 可以从一个库中编译静态和共享两种二进制文件。也就是说，库同时具有 `static` 和 `shared` 两种 facet。Lake 还允许用户定义自己的自定义 facet 来从模块和包构建，但这一特性当前仍在试验阶段且尚无相关文档。

<!--
A **trace** is a piece of data (generally a hash) which is used to verify whether a given target is up-to-date (i.e., does not need to be rebuilt). If the trace stored with a built target matches the trace computed during build, then a target is considered up-to-date. A target's trace is derived from its various **inputs** (e.g., source file, Lean toolchain, imports, etc.).
-->

- **trace** 是用来检查目标是否最新（即是否需要重新构建）的一些数据（通常是哈希值）。如果已构建目标的 trace 与构建过程中计算的 trace 相匹配，则目标被认为是最新的。目标的 trace 源于其各种**输入**（如源文件、Lean 工具链、导入等）。

<!--
## Package Configuration Options
-->
## 包配置选项

Lake 提供了多种多样的包配置选项。

<!-- ### Layout -->

### 布局

这些选项控制包及其构建目录的顶层目录布局。库、可执行文件和包内的目标指定的进一步路径相对于这些目录。

<!--
- `packagesDir`: The directory to which Lake should download remote dependencies. Defaults to `.lake/packages`.
-->
- `packagesDir`: Lake 下载远程依赖项的目录。默认为 `.lake/packages`。

<!--
- `srcDir`: The directory containing the package's Lean source files. Defaults to the package's directory.
-->
- `srcDir`: 包含包的 Lean 源文件的目录。默认为包目录。

<!--
- `buildDir`: The directory to which Lake should output the package's build results. Defaults to `build`.
-->
- `buildDir`: Lake 输出包构建结果的目录。默认值为 `build`。

<!--
- `leanLibDir`: The build subdirectory to which Lake should output the package's binary Lean libraries (e.g., `.olean`, `.ilean` files). Defaults to `lib`.
-->
- `leanLibDir`: Lake 输出包的二进制 Lean 库文件（如 `.olean`、`.ilean` 文件）的构建子目录。默认为 `lib`。

<!--
- `nativeLibDir`: The build subdirectory to which Lake should output the package's native libraries (e.g., `.a`, `.so`, `.dll` files). Defaults to `lib`.
-->
- `nativeLibDir`: Lake 输出包的本地库文件（如 `.a`、`.so`、`.dll` 文件）的构建子目录。默认为 `lib`。

<!--
- `binDir`: The build subdirectory to which Lake should output the package's binary executables. Defaults to `bin`.
-->
- `binDir`: Lake 输出包的二进制可执行文件的构建子目录。默认为 `bin`。

<!--
- `irDir`: The build subdirectory to which Lake should output the package's intermediary results (e.g., `.c`, `.o` files). Defaults to `ir`.
-->
- `irDir`: Lake 输出包的中间结果（如 `.c`、`.o` 文件）的构建子目录。默认为 `ir`。

<!-- ### Build & Run -->

### 构建与运行

这些选项配置包中代码的构建和运行方式。包内的库、可执行文件和其他目标可以进一步添加到此配置的部分内容。

<!--
- `platformIndependent`: Asserts whether Lake should assume Lean modules are platform-independent. That is, whether lake should include the platform and platform-dependent elements in a module's trace. See the docstring of `Lake.LeanConfig.platformIndependent` for more details. Defaults to `none`.
-->
- `platformIndependent`: 确定 Lake 是否应假设 Lean 模块平台无关。即，Lake 是否应在模块的 trace 中包含平台及其依赖的元素。有关更多详情，请参阅 `Lake.LeanConfig.platformIndependent` 的文档字符串。默认值为 `none`。

<!--
- `precompileModules`: Whether to compile each module into a native shared library that is loaded whenever the module is imported. This speeds up the evaluation of metaprograms and enables the interpreter to run functions marked `@[extern]`. Defaults to `false`.
-->
- `precompileModules`: 是否将每个模块编译为本地共享库文件，该文件在模块导入时加载。这加快了元程序的评估，并允许解释器运行带有 `@[extern]` 标记的函数。默认值为 `false`。

<!--
- `moreServerOptions`: An `Array` of additional options to pass to the Lean language server (i.e., `lean --server`) launched by `lake serve`.
-->
- `moreServerOptions`: 传递给由 `lake serve` 启动的 Lean 语言服务器（即 `lean --server`）的附加选项数组。

<!--
- `moreGlobalServerArgs`: An `Array` of additional arguments to pass to `lean --server` which apply both to this package and anything else in the same server session (e.g. when browsing other packages from the same session via go-to-definition)
-->
- `moreGlobalServerArgs`: 传递给 `lean --server` 的附加参数数组，这些参数适用于此包及同一服务器会话中的其他任何内容（例如，通过 go-to-definition 在同一会话中浏览其他包时）。

<!--
- `buildType`: The `BuildType` of targets in the package (see [`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670)). One of `debug`, `relWithDebInfo`, `minSizeRel`, or `release`. Defaults to `release`.
-->
- `buildType`: 包中目标的 `BuildType`（参见 [`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670)）。可以为 `debug`、`relWithDebInfo`、`minSizeRel` 或 `release` 其中之一。默认值为 `release`。

<!--
- `leanOptions`: Additional options to pass to both the Lean language server (i.e., `lean --server`) launched by `lake serve` and to `lean` while compiling Lean source files.
-->
- `leanOptions`: 传递给由 `lake serve` 启动的 Lean 语言服务器（即 `lean --server`）和在编译 Lean 源文件时传递给 `lean` 的附加选项。

<!--
- `moreLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files.
-->
- `moreLeanArgs`: 编译 Lean 源文件时传递给 `lean` 的附加参数数组。

<!--
- `weakLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files. Unlike `moreLeanArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come _before_ `moreLeanArgs`.
-->
- `weakLeanArgs`: 编译 Lean 源文件时传递给 `lean` 的附加参数数组。与 `moreLeanArgs` 不同的是，这些参数不会影响构建结果的 trace，因此可以在不触发重构的情况下更改。在 `moreLeanArgs` 之前传递。

<!--
- `moreLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Lake already passes some flags based on the `buildType`, but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
-->
- `moreLeancArgs`: 编译由 `lean` 生成的 C 源文件时传递给 `leanc` 的附加参数数组。Lake 已经根据 `buildType` 传递了一些标志，但你可以通过添加 `-O0` 和 `-UNDEBUG` 之类的参数来更改它。

<!--
- `weakLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Unlike `moreLeancArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come _before_ `moreLeancArgs`.
-->
- `weakLeancArgs`: 编译由 `lean` 生成的 C 源文件时传递给 `leanc` 的附加参数数组。与 `moreLeancArgs` 不同的是，这些参数不会影响构建结果的 trace，因此可以在不触发重建的情况下更改。在 `moreLeancArgs` 之前传递。

<!--
- `moreLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries). These will come _after_ the paths of `extern_lib` targets.
-->
- `moreLinkArgs`: 链接时（例如，二进制可执行文件或共享库）传递给 `leanc` 的附加参数数组。这些参数将位于 `extern_lib` 目标的路径之后。

<!--
- `weakLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries). Unlike `moreLinkArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come _before_ `moreLinkArgs`.
-->
- `weakLinkArgs`: 链接时（例如，二进制可执行文件或共享库）传递给 `leanc` 的附加参数数组。与 `moreLinkArgs` 不同的是，这些参数不会影响构建结果的 trace，因此可以在不触发重建的情况下更改。在 `moreLinkArgs` 之前传递。

<!--
- `extraDepTargets`: An `Array` of [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) names that the package should always build before anything else.
-->
- `extraDepTargets`: 包应始终最先构建的[目标](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets)名称数组。

<!-- ### Test & Lint -->

### 测试与检查

<!--
The CLI commands `lake test` and `lake lint` use definitions configured by the workspace's root package to perform testing and linting (this referred to as the test or lint _driver_). In Lean configuration files, these can be specified by applying the `@[test_driver]` or `@[lint_driver]` to a `script`, `lean_exe`, or `lean_lb`. They can also be configured (in Lean or TOML format) via the following options on the package.
-->
CLI 命令 `lake test` 和 `lake lint` 使用由工作空间的根包配置的定义来执行测试和检查（这称为测试或检查 _driver_）。在 Lean 配置文件中，可以通过将 `@[test_driver]` 或 `@[lint_driver]` 应用于 `script`、`lean_exe` 或 `lean_lib` 来指定这些定义。也可以通过包中的以下选项（以 Lean 或 TOML 格式）进行配置。

<!--
- `testDriver`: The name of the script, executable, or library to drive `lake test`.
-->
- `testDriver`: 驱动 `lake test` 的脚本、可执行文件或库的名称。

<!--
- `testDriverArgs`: An `Array` of arguments to pass to the package's test driver.
-->
- `testDriverArgs`: 传递给包的测试驱动程序的参数数组。

<!--
- `lintDriver`: The name of the script or executable used by `lake lint`. Libraries cannot be lint drivers.
-->
- `lintDriver`: `lake lint` 使用的脚本或可执行文件的名称。库不能用作检查驱动程序。

<!--
- `lintDriverArgs`: An `Array` of arguments to pass to the package's lint driver.
-->
- `lintDriverArgs`: 传递给包的检查驱动程序的参数数组。

<!--
You can specify definition from a dependency as a package's test or lint driver by using the syntax `<pkg>/<name>`. An executable driver will be built and then run, a script driver will just be run, and a library driver will just be built. A script or executable driver is run with any arguments configured by package (e.g., via `testDriverArgs`) followed by any specified on the CLI (e.g., via `lake lint -- <args>...`).
-->
你可以使用语法 `<pkg>/<name>` 将依赖项中的定义指定为包的测试或检查驱动程序。可执行驱动程序将被构建然后运行，脚本驱动程序将仅运行，而库驱动程序将仅构建。脚本或可执行驱动程序会运行包配置的任何参数（例如，通过 `testDriverArgs`），然后是 CLI 中指定的任何参数（例如，通过 `lake lint -- <args>...`）。

<!-- ### Cloud Releases -->

### 云发布


<!--
These options define a cloud release for the package. See the section on [GitHub Release Builds](https://github.com/leanprover/lean4/tree/master/src/lake#github-release-builds) for more information.
-->
这些选项为包定义云发布。详细信息参见[GitHub 发布构建](https://github.com/leanprover/lean4/tree/master/src/lake#github-release-builds)部分。

<!--
- `releaseRepo`: The URL of the GitHub repository to upload and download releases of this package. If `none` (the default), for downloads, Lake uses the URL the package was download from (if it is a dependency) and for uploads, uses `gh`'s default.
-->
- `releaseRepo`: 上传和下载此包发布版本的 GitHub 仓库 URL。如果为 `none`（默认），则下载时，Lake 使用包的下载 URL（如果是依赖项），上传时使用 `gh` 的默认 URL。

<!--
- `buildArchive`: The name of the build archive for the GitHub cloud release. Defaults to `{(pkg-)name}-{System.Platform.target}.tar.gz`.
-->
- `buildArchive`: GitHub 云发布的构建归档名称。默认为 `{(pkg-)name}-{System.Platform.target}.tar.gz`。

<!--
- `preferReleaseBuild`: Whether to prefer downloading a prebuilt release (from GitHub) rather than building this package from the source when this package is used as a dependency.
-->
- `preferReleaseBuild`: 当此包用作依赖项时，是否优先下载预构建发布（从 GitHub），而不是从源码构建此包。


<!--
## Defining Build Targets
-->

## 设定构建目标

<!--
A Lake package can have many build targets, such as different Lean libraries and multiple binary executables. Any number of these declarations can be marked with the `@[default_target]` attribute to tell Lake to build them on a bare `lake build` of the package.
-->

一个 Lake 包可能有许多的构建目标，比如不同的 Lean 库和诸多二进制可执行文件。不论数量多少，你总可以在 `@[default_target]` 后声明它们，这样就可以用 `lake build` 轻松构建。

<!--
### Lean Libraries
-->

### Lean 库

<!--
A Lean library target defines a set of Lean modules available to `import` and how to build them.
-->
Lean 库目标定义了可供 `import` 的 Lean 模块以及它们的构建方式。

<!--
**Syntax**
-->

**语法**

<!--
```lean
lean_lib «target-name» where
  -- configuration options go here
```

```toml
[[lean_lib]]
name = "«target-name»"
# more configuration options go here
```
-->

```lean
lean_lib «target-name» where
  -- 配置选项从这里开始
```

```toml
[[lean_lib]]
name = "«target-name»"
# 更多配置选项从这里开始
```

<!--
**Configuration Options**
-->

**配置选项**

<!--
- `srcDir`: The subdirectory of the package's source directory containing the library's source files. Defaults to the package's `srcDir`. (This will be passed to `lean` as the `-R` option.)
-->
- `srcDir`: 包目录下的子目录，包含库的源文件。默认值为包的 `srcDir`。（这将作为 `-R` 选项传递给 `lean`。）

<!--
- `roots`: An `Array` of root module `Name`(s) of the library. Submodules of these roots (e.g., `Lib.Foo` of `Lib`) are considered part of the library. Defaults to a single root of the target's name.
-->
- `roots`: 库的根模块名数组。这些根模块的子模块（例如，`Lib` 的 `Lib.Foo`）被视为库的一部分。默认值为目标名的单一根。

<!--
- `globs`: An `Array` of module `Glob`(s) to build for the library. The term `glob` comes from [file globs](https://en.wikipedia.org/wiki/Glob_(programming)) (e.g., `foo/*`) on Unix. A submodule glob builds every Lean source file within the module's directory (i.e., ``Glob.submodules `Foo`` is essentially equivalent to a theoretical `import Foo.*`). Local imports of glob'ed files (i.e., fellow modules of the workspace) are also recursively built. Defaults to a `Glob.one` of each of the library's `roots`.
-->
- `globs`: 构建库的模块 glob 数组。术语 `glob` 来源于 Unix 的 [文件 glob](https://en.wikipedia.org/wiki/Glob_(programming))（例如，`foo/*`）。子模块 glob 构建模块目录中的每个 Lean 源文件（即， ``Glob.submodules `Foo`` 基本上等同于理论上的 `import Foo.*`）。glob 文件的本地导入（即工作区的其他模块）也会递归构建。默认值为库中每个 `roots` 的 `Glob.one`。

<!--
- `libName`: The `String` name of the library. Used as a base for the file names of its static and dynamic binaries. Defaults to the name of the target.
-->
- `libName`: 库的字符串名称。用作其静态和动态二进制文件名的基础。默认值为目标名称。

<!--
- `extraDepTargets`: An `Array` of [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) names to build before the library's modules.
-->
- `extraDepTargets`: 在库模块之前构建的 [目标](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) 名称数组。

<!--
- `defaultFacets`: An `Array` of library facets to build on a bare `lake build` of the library. For example, setting this to `#[LeanLib.sharedLib]` will build the shared library facet.
-->
- `defaultFacets`: 库的 facets 数组，用于在 `lake build` 中构建库。例如，将其设置为 `#[LeanLib.sharedLib]` 将构建共享库 facet。

<!--
- `nativeFacets`: A function `(shouldExport : Bool) → Array` determining the [module facets](https://github.com/leanprover/lean4/tree/master/src/lake#defining-new-facets) to build and combine into the library's static and shared libraries. If `shouldExport` is true, the module facets should export any symbols a user may expect to lookup in the library. For example, the Lean interpreter will use exported symbols in linked libraries. Defaults to a singleton of `Module.oExportFacet` (if `shouldExport`) or `Module.oFacet`. That is, the object files compiled from the Lean sources, potentially with exported Lean symbols.
-->
- `nativeFacets`: 一个函数 `(shouldExport : Bool) → Array`，确定构建并组合到库的静态和共享库中的 [模块 facets](https://github.com/leanprover/lean4/tree/master/src/lake#defining-new-facets)。如果 `shouldExport` 为真，模块 facets 应导出用户可能期望在库中查找的任何符号。例如，Lean 解释器将使用链接库中的导出符号。默认值为 `Module.oExportFacet` 的单例（如果 `shouldExport`）或 `Module.oFacet`。也就是说，从 Lean 源文件编译的目标文件，可能包含导出的 Lean 符号。

<!--
- `platformIndependent`, `precompileModules`, `buildType`, `leanOptions`, `<more|weak><Lean|Leanc|Link>Args`, `moreServerOptions`: Augments the package's corresponding configuration option. The library's arguments come after, modules are precompiled if either the library or package are, `platformIndependent` falls back to the package on `none`, and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest).
-->
- `platformIndependent`、`precompileModules`、`buildType`、`leanOptions`、`<more|weak><Lean|Leanc|Link>Args`、`moreServerOptions`：增强包的相应配置选项。库的参数紧随其后，如果库或包都预编译，则模块会被预编译，`platformIndependent` 在 `none` 情况下会回退到包，并且构建类型是两者中的最低值（`debug` 是最低的，而 `release` 是最高的）。

<!--
### Binary Executables
-->

### 二进制可执行文件

<!--
A Lean executable target builds a binary executable from a Lean module with a `main` function.
-->

一个 Lean 二进制可执行文件目标从带有 `main` 函数的 Lean 模块文件构建出可执行文件。

<!--
**Syntax**
-->

**语法**

<!--
```lean
lean_exe «target-name» where
  -- configuration options go here
```

```toml
[[lean_exe]]
name = "«target-name»"
# more configuration options go here
```
-->

```lean
lean_exe «target-name» where
  -- 配置选项从这里开始
```

```toml
[[lean_exe]]
name = "«target-name»"
# 更多配置选项从这里开始
```

<!--
**Configuration Options**
-->

**配置选项**

<!--
- `srcDir`: The subdirectory of the package's source directory containing the executable's source file. Defaults to the package's `srcDir`. (This will be passed to `lean` as the `-R` option.)
-->
- `srcDir`: 包目录下的子目录，包含可执行文件的源文件。默认值为包的 `srcDir`。（这将作为 `-R` 选项传递给 `lean`。）

<!--
- `root`: The root module `Name` of the binary executable. Should include a `main` definition that will serve as the entry point of the program. The root is built by recursively building its local imports (i.e., fellow modules of the workspace). Defaults to the name of the target.
-->
- `root`: 二进制可执行文件的根模块名。应包含一个 `main` 定义，它将作为程序的入口点。通过递归构建其本地导入（即工作区的其他模块）来构建根。默认值为目标名称。

<!--
- `exeName`: The `String` name of the binary executable. Defaults to the target name with any `.` replaced with a `-`.
-->
- `exeName`: 二进制可执行文件的字符串名称。默认值为目标名称，且其中的 `.` 替换为 `-`。

<!--
- `extraDepTargets`: An `Array` of [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) names to build before the executable's modules.
-->
- `extraDepTargets`: 在可执行文件模块之前构建的 [目标](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) 名称数组。

<!--
- `nativeFacets`: A function `(shouldExport : Bool) → Array` determining the [module facets](https://github.com/leanprover/lean4/tree/master/src/lake#defining-new-facets) to build and link into the executable. If `shouldExport` is true, the module facets should export any symbols a user may expect to lookup in the library. For example, the Lean interpreter will use exported symbols in linked libraries. Defaults to a singleton of `Module.oExportFacet` (if `shouldExport`) or `Module.oFacet`. That is, the object file compiled from the Lean source, potentially with exported Lean symbols.
-->
- `nativeFacets`: 一个函数 `(shouldExport : Bool) → Array`，确定将哪些 [模块 facets](https://github.com/leanprover/lean4/tree/master/src/lake#defining-new-facets) 构建并链接到可执行文件中。如果 `shouldExport` 为真，模块 facets 应导出用户可能期望在库中查找的任何符号。例如，Lean 解释器将使用链接库中的导出符号。默认值为 `Module.oExportFacet` 的单例（如果 `shouldExport`）或 `Module.oFacet`。也就是说，从 Lean 源文件编译的目标文件，可能包含导出的 Lean 符号。

<!--
- `supportInterpreter`: Whether to expose symbols within the executable to the Lean interpreter. This allows the executable to interpret Lean files (e.g., via `Lean.Elab.runFrontend`). Implementation-wise, on Windows, the Lean shared libraries are linked to the executable and, on other systems, the executable is linked with `-rdynamic`. This increases the size of the binary on Linux and, on Windows, requires `libInit_shared.dll` and `libleanshared.dll` to be co-located with the executable or part of `PATH` (e.g., via `lake exe`). Thus, this feature should only be enabled when necessary. Defaults to `false`.
-->
- `supportInterpreter`: 是否将可执行文件中的符号暴露给 Lean 解释器。这允许可执行文件解释 Lean 文件（例如，通过 `Lean.Elab.runFrontend`）。在实现方面，在 Windows 上，Lean 共享库链接到可执行文件，其他系统上，可执行文件使用 `-rdynamic` 进行链接。这会增加 Linux 上二进制文件的大小，在 Windows 上，需要 `libInit_shared.dll` 和 `libleanshared.dll` 与可执行文件共同定位或作为 `PATH` 的一部分（例如，通过 `lake exe`）。因此，此功能应仅在必要时启用。默认值为 `false`。

<!--
- `platformIndependent`, `precompileModules`, `buildType`, `leanOptions`, `<more|weak><Lean|Leanc|Link>Args`, `moreServerOptions`: Augments the package's corresponding configuration option. The library's arguments come after, modules are precompiled if either the library or package are, `platformIndependent` falls back to the package on `none`, and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest).
-->
- `platformIndependent`、`precompileModules`、`buildType`、`leanOptions`、`<more|weak><Lean|Leanc|Link>Args`、`moreServerOptions`：增加包的相应配置选项。可执行文件的参数在库参数之后，如果库或包都预编译，则模块会被预编译，`platformIndependent` 在 `none` 情况下会回退到包，并且构建类型是两者中的最低值（`debug` 是最低的，而 `release` 是最高的）。

<!--
### External Libraries
-->

### 外部库

<!--
A external library target is a non-Lean **static** library that will be linked to the binaries of the package and its dependents (e.g., their shared libraries and executables).
-->

外部库目标是一个非 Lean 的**静态**库，将链接到包及其依赖项的二进制文件（例如，它们的共享库和可执行文件）。

**Important:** For the external library to link properly when `precompileModules` is on, the static library produced by an `extern_lib` target must following the platform's naming conventions for libraries (i.e., be named `foo.a` on Windows and `libfoo.a` on Unix). To make this easy, there is the `Lake.nameToStaticLib` utility function to convert a library name into its proper file name for the platform.

**重要:** 为了在 `precompileModules` 开启时外部库正确链接，由 `extern_lib` 目标生成的静态库必须遵循平台的库命名约定（即在 Windows 上命名为 `foo.a`，在 Unix 上命名为 `libfoo.a`）。为了简化此操作，可以使用 `Lake.nameToStaticLib` 实用函数将库名称转换为适合平台的正确文件名称。

<!--
**Syntax**
-->

**语法**

<!--
```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  -- a build function that produces its static library
```
-->

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  -- 生成静态库的构建函数
```

<!--
The declaration is essentially a wrapper around a `System.FilePath` [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets). Like such a target, the `pkg` parameter and its type specifier are optional and body should be a term of type `FetchM (BuildJob System.FilePath)` function that builds the static library. The `pkg` parameter is of type `NPackage _package.name` to provably demonstrate that it is the package in which the external library is defined.
-->

该声明本质上是围绕 `System.FilePath` [目标](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) 的包装。类似于这样的目标，`pkg` 参数及其类型说明是可选的，主体应为类型 `FetchM (BuildJob System.FilePath)` 的函数，该函数构建静态库。`pkg` 参数的类型为 `NPackage _package.name`，以确凿地表明这是定义外部库的包。

<!--
### Custom Targets
-->


### 自定义目标

<!--
A arbitrary target that can be built via `lake build <target-name>`.
-->
可以通过 `lake build <target-name>` 构建的任意目标。

<!--
**Syntax**
-->

**语法**

<!--
```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  -- a build function that produces a `BuildJob α`
```
-->
```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  -- 生成一个 `BuildJob α` 的构建函数
```

<!--
The `pkg` parameter and its type specifier are optional and the body should be a term of type `FetchM (BuildJob α)`. The `pkg` parameter is of type `NPackage _package.name` to provably demonstrate that it is the package in which the target is defined.
-->
`pkg` 参数及其类型说明是可选的，主体应为类型 `FetchM (BuildJob α)` 的表达式。`pkg` 参数的类型为 `NPackage _package.name`，以确凿地表明这是定义该目标的包。

<!--
## 定义新 facet
-->
## 定义新 facet

<!--
A Lake package can also define new _facets_ for packages, modules, and libraries. Once defined, the new facet (e.g., `facet`) can be built on any current or future object of its type (e.g., through `lake build pkg:facet` for a package facet). Module facets can also be provided to [`LeanLib.nativeFacets`](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries) to have Lake build and use them automatically when producing shared libraries.
-->
Lake 包也可以为包、模块和库定义新的 _facet_。定义后，新 facet（例如 `facet`）可以在其类型的任何当前或未来对象上构建（例如，通过 `lake build pkg:facet` 进行包 facet 的构建）。模块 facet 也可以提供给 [`LeanLib.nativeFacets`](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries) 以便在生成共享库时由 Lake 自动构建和使用。

<!--
**Syntax**
-->

**语法**

<!--
```lean
package_facet «facet-name» (pkg : Package) : α :=
  -- a build function that produces a `BuildJob α`

module_facet «facet-name» (mod : Module) : α :=
  -- a build function that produces a `BuildJob α`

library_facet «facet-name» (lib : LeanLib) : α :=
  -- a build function that produces a `BuildJob α`
```
-->
```lean
package_facet «facet-name» (pkg : Package) : α :=
  -- 生成一个 `BuildJob α` 的构建函数

module_facet «facet-name» (mod : Module) : α :=
  -- 生成一个 `BuildJob α` 的构建函数

library_facet «facet-name» (lib : LeanLib) : α :=
  -- 生成一个 `BuildJob α` 的构建函数
```

<!--
In all of these, the object parameter and its type specifier are optional and the body should be a term of type `FetchM (BuildJob α)`.
-->
在这些定义中，目标参数及其类型说明是可选的，主体应为类型 `FetchM (BuildJob α)` 的表达式。

<!--
## Adding Dependencies
-->

## 添加依赖

<!--
Lake packages can have dependencies. Dependencies are other Lake packages the current package needs in order to function. They can be sourced directly from a local folder (e.g., a subdirectory of the package) or come from remote Git repositories. For example, one can depend on [mathlib](https://reservoir.lean-lang.org/@leanprover-community/mathlib) like so:
-->
Lake 包可添加依赖。依赖是当前包为了运行所需要的其他 Lake 包。它们可以直接来自本地文件夹（如包的子目录），也可以来自远程 Git 仓库。例如，你可以这样添加 [mathlib](https://reservoir.lean-lang.org/@leanprover-community/mathlib) 依赖：

<!--
```lean
package hello

require "leanprover-community" / "mathlib"
```
-->
```lean
package hello

require "leanprover-community" / "mathlib"
```

<!--
The next run of `lake build` (or refreshing dependencies in an editor like VSCode) will clone the mathlib repository and build it. Information on the specific revision cloned will then be saved to `lake-manifest.json` to enable reproducibility (i.e., ensure the same version of mathlib is used by future builds). To update `mathlib` after this, you will need to run `lake update` -- other commands do not update resolved dependencies.
-->
下次运行 `lake build` （或是用 VSCode 一类的编辑器刷新依赖）时将会克隆并构建 mathlib 仓库。克隆的特定版本的信息将存入 `lake-manifest.json` 以确保可复现性（即保证未来的构建使用同一版本的 mathlib）。在这之后如果想要更新 `mathlib`，你需要使用 `lake update` —— 其它的命令都将不会更新已解析的依赖。

<!--
For theorem proving packages which depend on `mathlib`, you can also run `lake new <package-name> math` to generate a package configuration file that already has the `mathlib` dependency (and no binary executable target).
-->
对于依赖 `mathlib` 的定理证明包，你也可以用 `lake new <package-name> math` 直接创建带有 mathlib 依赖的包配置（且无二进制可执行文件目标）。

<!--
**NOTE:** For mathlib in particular, you should run `lake exe cache get` prior to a `lake build` after adding or updating a mathlib dependency. Otherwise, it will be rebuilt from scratch (which can take hours). For more information, see mathlib's [wiki page](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency) on using it as a dependency.
-->
**注意：** 对于 mathlib 而言，在添加或升级其作为依赖后，你还需要在 `lake build` 之前使用 `lake exe cache get`。否则构建将从零开始（耗时数小时）。参阅 [mathlib wiki 页面](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency) 获取更多信息。

<!--
## Lean `require`
-->

## Lean `require`

<!--
The `require` command in Lean Lake configuration follows the general syntax:
-->
Lean 的 Lake 配置文件中 `require` 命令的基本语法如下：

<!--
```lean
require ["<scope>" /] <pkg-name> [@ <version>]
  [from <source>] [with <options>]
```
-->
```lean
require ["<scope>" /] <pkg-name> [@ <version>]
  [from <source>] [with <options>]
```

<!--
The `from` clause tells Lake where to locate the dependency. Without a `from` clause, Lake will lookup the package in the default registry (i.e., [Reservoir](https://reservoir.lean-lang.org/@lean-dojo/LeanCopilot)) and use the information there to download the package at the specified `version`. The optional `scope` is used to disambiguate which package with `pkg-name` to lookup. In Reservoir, this scope is the package owner (e.g., `leanprover` of [@leanprover/doc-gen4](https://reservoir.lean-lang.org/@leanprover/doc-gen4)).
-->
`from` 从句告知 Lake 依赖的地址。没有 `from` 从句，Lake 将从默认注册表（例如 [Reservoir](https://reservoir.lean-lang.org/@lean-dojo/LeanCopilot)）中查找包，并使用获得的信息下载指定 `version` 的包。可选的 `scope` 用来消除同名包的歧义。在 Reservoir 中，scope 部分是包的所有者（例如，[@leanprover/doc-gen4](https://reservoir.lean-lang.org/@leanprover/doc-gen4) 中的 `leanprover`）。

<!--
The `with` clause specifies a `NameMap String` of Lake options used to configure the dependency. This is equivalent to passing `-K` options to the dependency on the command line.
-->
`with` 子句指定用于配置依赖项的 Lake 选项的 `NameMap String`。这相当于在命令行中将 `-K` 选项传递给依赖项。<!--TODO: NameMap-->


<!--
## Supported Sources
-->

## 受支持的源

<!--
Lake supports the following types of dependencies as sources in a `from` clause.
-->

在 `from` 子句中，Lake 支持下列依赖源。

<!--
### Path Dependencies
-->
### 路径依赖

```
from <path>
```

Lake 将从 `path` 目录（相对于所依赖包的目录）中加载包。

<!--
### Git Dependencies
-->

### Git 依赖

```
from git <url> [@ <rev>] [/ <subDir>]
```

<!--
Lake clones the Git repository available at the specified fixed Git `url`, and checks out the specified revision `rev`. The revision can be a commit hash, branch, or tag. If none is provided, Lake defaults to `master`. After checkout, Lake loads the package located in `subDir` (or the repository root if no subdirectory is specified).
-->

Lake 从固定的 `url` 中克隆 Git 仓库，并 checkout 到指定的 `rev`。其中 `rev` 可以是 commit hash、branch 或 tag。如果都没有指定，Lake 将使用默认的 `master` 分支。checkout 之后，Lake 将从子目录 `subDir` 中加载包（如果未指定子目录，则从仓库根目录加载）。

<!--
## TOML `require`
-->

## TOML `require`

<!--
To `require` a package in a TOML configuration, the parallel syntax for the above examples is:
-->

要在 TOML 配置文件中 `require` 一个包，其等价语法如下：

```toml
# A Reservoir dependency
[[require]]
name = "<pkg-name>"
scope = "<scope>"
version = "<version>"
options = {<options>}

# A path dependency
[[require]]
name = "<pkg-name>"
path = "<path>"

# A Git dependency
[[require]]
name = "<pkg-name>"
git = "<url>"
rev = "<rev>"
subDir = "<subDir>"
```

<!--
## Github Release Builds
-->

## GitHub 发布构建

<!--
Lake supports uploading and downloading build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages. This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from the source themselves.
-->

Lake 支持将构建产物（即已归档的构建目录）上传到 GitHub 发布版本，或从中下载。这使得终端用户可以从云端获取预构建的产物，而无需自己从源码重建包。

<!--
### Downloading
-->

### 下载

要下载产物，用户应配置包的 [选项](https://github.com/leanprover/lean4/tree/master/src/lake#cloud-releases)`releaseRepo?` 和 `buildArchive?`，指向托管发布的 GitHub 仓库及其中的正确产物名称（如果默认设置不够）。然后，设置 `preferReleaseBuild := true` 以告知 Lake 获取并解压它作为额外的包依赖项。

Lake 仅在其标准构建过程中才会获取发布构建，如果需要的包是依赖项（因为根包通常会被修改，因此不常与此方案兼容）。然而，如果希望获取根包的发布（例如，在克隆发布的源码后但在编辑之前），可以通过 `lake build :release` 手动执行此操作。

Lake 内部使用 `curl` 下载发布，并使用 `tar` 解压缩它，因此终端用户必须安装这两种工具才能使用此功能。如果 Lake 由于任何原因无法获取发布，它将转而从源码构建。另外请注意，此机制在技术上不仅限于 GitHub，任何使用相同 URL 方案的 Git 主机也可以使用。

<!--
### Uploading
-->

### 上传

要将构建的包作为产物上传到 GitHub 发布，Lake 提供了一个便捷的简写命令 `lake upload <tag>`。此命令使用 `tar` 将包的构建目录打包成档案，并使用 `gh release upload` 将其附加到 `tag` 对应的预先存在的 GitHub 发布版本中。因此，为了使用它，包上传者（但不是下载者）需要安装 `gh`，即 [GitHub CLI](https://cli.github.com/)，并将其添加到 `PATH`。

<!--
## Writing and Running Scripts
-->

## 编写及运行脚本

<!--
A configuration file can also contain a number of `scripts` declaration. A script is an arbitrary `(args : List String) → ScriptM UInt32` definition that can be run by `lake script run`. For example, given the following `lakefile.lean`:
-->

配置文件中也可能包含 `scripts` 声明。脚本是任意的 `(args : List String) → ScriptM UInt32` 类型的定义，可以通过 `lake script run` 来运行。例如以下的 `lakefile.lean`：

```lean
import Lake
open Lake DSL

package scripts

/--
Display a greeting

USAGE:
  lake run greet [name]

Greet the entity with the given name. Otherwise, greet the whole world.
-/
script greet (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args[0]'h}!"
  else
    IO.println "Hello, world!"
  return 0
```

<!--
The script `greet` can be run like so:
-->

脚本 `greet` 可以这样运行：

```
$ lake script run greet
Hello, world!
$ lake script run greet me
Hello, me!
```

<!--
You can print the docstring of a script with `lake script doc`:
-->

你可以用 `lake script doc` 输出一个脚本的 docstring：

```
$ lake script doc greet
Display a greeting

USAGE:
  lake run greet [name]

Greet the entity with the given name. Otherwise, greet the whole world.
```

<!--
## Building and Running Lake from the Source
-->
## 从源码构建并运行 Lake

<!--
If you already have a Lean installation with `lake` packaged with it, you can build a new `lake` by just running `lake build`.
-->

如果你已经安装了带有 `lake` 的 Lean，可以直接用 `lake build` 构建一个新的 `lake`。

<!--
Otherwise, there is a pre-packaged `build.sh` shell script that can be used to build Lake. It passes it arguments down to a `make` command. So, if you have more than one core, you will probably want to use a `-jX` option to specify how many build tasks you want it to run in parallel. For example:
-->

或者，你可以使用已预打包的 `build.sh` 脚本来构建 Lake。它将参数传递给 `make` 命令。所以，如果你的处理器支持多核心，可以使用 `-jX` 选项指定希望并行运行的构建任务数。例如：

```shell
$ ./build.sh -j4
```

<!--
After building, the `lake` binary will be located at `.lake/build/bin/lake` and the library's `.olean` files will be located in `.lake/build/lib`.
-->

构建后，`lake` 二进制文件将位于 `.lake/build/bin/lake` 中，而库的 `.olean` 文件将位于 `.lake/build/lib` 下。

<!--
### Building with Nix Flakes
-->

### 使用 Nix Flakes 构建

Lake 是 Lean 4 flake 的一部分，在仓库根目录下构建。

<!-- 
### Augmenting Lake's Search Path
-->

### 增强 Lake 的搜索路径

<!--
The `lake` executable needs to know where to find the Lean library files (e.g., `.olean`, `.ilean`) for the modules used in the package configuration file (and their source files for go-to-definition support in the editor). Lake will intelligently setup an initial search path based on the location of its own executable and `lean`.
-->

`lake` 可执行文件需要知道在包配置文件中使用的模块的 Lean 库文件（例如 `.olean`, `.ilean`）在哪里（以及编辑器中 go-to-definition 支持的源文件）。Lake 将基于自身可执行文件和 `lean` 的位置智能地设置初始搜索路径。

<!--
Specifically, if Lake is co-located with `lean` (i.e., there is `lean` executable in the same directory as itself), it will assume it was installed with Lean and that both Lean and Lake are located under their shared sysroot. In particular, their binaries are located in `<sysroot>/bin`, their Lean libraries in `<sysroot>/lib/lean`, Lean's source files in `<sysroot>/src/lean`, and Lake's source files in `<sysroot>/src/lean/lake`. Otherwise, it will run `lean --print-prefix` to find Lean's sysroot and assume that Lean's files are located as aforementioned, but that `lake` is at `<lake-home>/.lake/build/bin/lake` with its Lean libraries at `<lake-home>/.lake/build/lib` and its sources directly in `<lake-home>`.
-->

具体而言，如果 Lake 与 `lean` 位于同一位置（即与 `lake` 在同一目录下有 `lean` 可执行文件），它将假定它是与 Lean 一起安装的，并且 Lean 和 Lake 位于其共享的 sysroot 下。具体来说，它们的二进制文件位于 `<sysroot>/bin`，它们的 Lean 库文件位于 `<sysroot>/lib/lean`，Lean 的源文件位于 `<sysroot>/src/lean`，而 Lake 的源文件位于 `<sysroot>/src/lean/lake`。否则，它将运行 `lean --print-prefix` 以找到 Lean 的 sysroot，并假定 Lean 的文件如前所述，而 `lake` 位于 `<lake-home>/.lake/build/bin/lake`，其 Lean 库文件位于 `<lake-home>/.lake/build/lib`，其源文件直接位于 `<lake-home>`。

<!--
This search path can be augmented by including other directories of Lean libraries in the `LEAN_PATH` environment variable (and their sources in `LEAN_SRC_PATH`). This can allow the user to correct Lake's search when the files for Lean (or Lake itself) are in non-standard locations. However, such directories will _not_ take precedence over the initial search path. This is important during development, as this prevents the Lake version used to build Lake from using the Lake version being built's Lean libraries (instead of its own) to elaborate Lake's `lakefile.lean` (which can lead to all kinds of errors).
-->

可以通过在 `LEAN_PATH` 环境变量中包含其他 Lean 库目录（以及在 `LEAN_SRC_PATH` 中的源文件目录）来增强此搜索路径。这允许用户在 Lean 的文件（或 Lake 本身）位于非标准位置时更正 Lake 的搜索路径。然而，这些目录不会优先于初始搜索路径。这在开发期间很重要，因为这可以防止用于构建 Lake 的 Lake 版本使用正在构建的 Lake 版本的 Lean 库（而不是它自己的）来详细说明 Lake 的 `lakefile.lean`（这可能会导致各种错误）。
