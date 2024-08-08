<!-- 
# Lake
-->

# Lake 官方文档
***

<!--
Lake (Lean Make) is the new build system and package manager for Lean 4. With Lake, the package's configuration is written in Lean inside a dedicated `lakefile.lean` stored in the root of the package's directory.
-->

Lake (Lean Make) 是 Lean 4 新的构建系统及包管理器。Lake 让包配置可以记载在包根目录下一个精巧的 `lakefile.lean` 文件里。

<!--
Each `lakefile.lean` includes a `package` declaration (akin to `main`) which defines the package's basic configuration. It also typically includes build configurations for different targets (e.g., Lean libraries and binary executables) and Lean scripts to run on the command line (via `lake script run`).
-->

每一个 `lakefile.lean` 文件包含有一段 `package` 声明（像 `main` 函数一样），用来设定包的基本配置。通常，文件中也会写明对于不同目标的构建配置（例如，Lean 的库文件和二进制可执行文件），同时还有通过 `lake script run` 运行的命令行脚本信息。

<!--
_**This README provides information about Lake relative to the current commit. If you are looking for documentation for the Lake version shipped with a given Lean release, you should look at the README of that version.**_
-->

_**此文档对应版本：Lean (version 4.10.0-rc2, commit 702c31b80712)**_

<!--
## Getting Lake
-->

## 获取 Lake

<!--
Lake is part of the [lean4](https://github.com/leanprover/lean4) repository and is distributed along with its official releases (e.g., as part of the [elan](https://github.com/leanprover/elan) toolchain). So if you have installed a semi-recent Lean 4 nightly, you should already have it! If you want to build the latest version from the source yourself, check out the [build instructions](https://github.com/leanprover/lean4/tree/master/src/lake#building-and-running-lake-from-the-source) at the bottom of this README.
-->

Lake 目前被包含在 lean4 仓库中，随 lean4 的官方版本发布而分发（例如，作为 elan 工具链的一部分）。所以，如果你已经安装了 Lean 4，你也同样拥有了 lake。如果你想自己进行构建，请查看 [从源码构建并运行 Lake](#从源码构建并运行-lake) 部分

<!--
## Creating and Building a Package
-->

## 创建并构建一个包

<!--
To create a new package, either run `lake init` to setup the package in the current directory or `lake new` to create it in a new directory. For example, we could create the package `hello` like so:
-->

你可以用在已有文件夹目录下 `lake init` 或直接 `lake new` 两种方式创建新的包。比如，可以这样创建包 `hello` ：

```
$ mkdir hello
$ cd hello
$ lake init hello
```

<!--
or like so:
-->

或者这样：

```
$ lake new hello
$ cd hello
```

<!--
Either way, Lake will create the following template directory structure and initialize a Git repository for the package.
-->

不同方式下，Lake 都会按如下模板结构创建一个项目并初始化 Git 仓库。

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

```
.lake/         # Lake 的输出目录
Hello/         # 库的源文件目录; 通过`import Hello.*`导入
  Basic.lean   # 一个样例库模块文件
  ...          # 添加其它文件
Hello.lean     # 库的根文件; 从 Hello 导入标准模块
Main.lean      # 可执行文件的 main 文件 (含 `def main`)
lakefile.lean  # Lake 的包配置文件
lean-toolchain # 包所使用的 Lean 版本
.gitignore     # Git 的排除文件
```

<!--
The example modules files contain the following dummy "Hello World" program.
-->

和你第一次创建所有语言的项目时一样，生成的示例文件构成了一个 "Hello World" 程序

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
-- 这个模块（文件）是 `Hello` 库的根文件
-- 在这里引入应当作为库的一部分被构建的模块
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

Lake 同时也会创建 `lakefile.lean` 和 `lean-toolchain` 文件。`lean-toolchain` 文件包含了 Lake 所属的 Lean 工具链版本，这样版本管理器 elan 就会知道该为这个包使用哪一个版本的 Lean 工具链。

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
  -- 这里添加包配置选项

lean_lib «Hello» where
  -- 这里添加库配置选项

@[default_target]
lean_exe «hello» where
  root := `Main
```

<!--
The command `lake build` is used to build the package (and its [dependencies](https://github.com/leanprover/lean4/tree/master/src/lake#adding-dependencies), if it has them) into a native executable. The result will be placed in `.lake/build/bin`. The command `lake clean` deletes `build`.
-->

命令 `lake build` 用来构建整个包（及其依赖）以生成一个本地可执行文件。文件位于 `.lake/build/bin` 。命令 `lake clean` 将删除 `build` 文件夹。

```
$ lake build
...
$ ./.lake/build/bin/hello
Hello, world!
```

<!--
Examples of different package configurations can be found in the [`examples`](https://github.com/leanprover/lean4/blob/master/src/lake/examples) folder of this repository. You can also pass a package template tp `lake init` or `lake new` to control what files Lake creates. For example, instead of using a Lean configuration file for this package, one could produce a TOML version via `lake new hello .toml`.
-->

不同的包配置样例可以在 [`Lean4/src/lake/examples`](https://github.com/leanprover/lean4/blob/master/src/lake/examples) 中找到。你也可以给 `lake init` 和 `lake new` 命令传入模板选项。比如，使用 `lake new hello .toml` 命令，Lake 将使用 .toml 格式的配置文件。


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

使用 `lake help init` 和 `lake help new` 命令可查看更多的模板选项

<!--
## Glossary of Terms
-->
## 术语表

<!--
Lake uses a lot of terms common in software development -- like workspace, package, library, executable, target, etc. -- and some more esoteric ones -- like facet. However, whether common or not, these terms mean different things to different people, so it is important to elucidate how Lake defines these terms:
-->

在软件开发过程中，Lake 会用到一系列的术语 —— 如工作空间 (workspace)，包 (package)，库 (library)，可执行文件 (executable)，目标 (target)，等等 —— 还有些更深晦的 —— 如 facet。不过，无论常见与否，术语对不同人总有着不同的含义，所以有必要好好地阐明这些术语在 Lake 中的意义：

<!--
- A **package** is the **fundamental unit of code distribution in Lake**. Packages can be sourced from the local file system or downloaded from the web (e.g., via Git). The `package` declaration in package's lakefile names it and [defines its basic properties](https://github.com/leanprover/lean4/tree/master/src/lake#package-configuration-options).
-->

-  **包 (package)** 是 Lake **代码分发的基本单元**。包可以来源于本地的文件，也可以从网络中下载（比如说用 Git），lakefile 中的 `package` 声明决定了包的名字和基本属性

<!--
- A **lakefile** is the Lean file that configures a package. It defines how to view, edit, build, and run the code within it, and it specifies what other packages it may require in order to do so.
-->

-  **lakefile** 是记载整个包配置的 Lean 文件。其中指明了如何浏览，编辑，构建及运行包中的代码，同时也指定了所依赖的其它包

<!--
- If package `B` requires package `A`, then package `A` is a **dependency** of package B and package `B` is its **dependent**. Package `A` is **upstream** of package `B` and package `B` is reversely **downstream** of package `A`. See the [Adding Dependencies section](https://github.com/leanprover/lean4/tree/master/src/lake#adding-dependencies) for details on how to specify dependencies.
-->

-  如果包 B 依赖包 A，包 A 就被称为包 B 的 **上游 (upstream)** ，反之包 B 是包 A 的 **下游 (downstream)** 。参考 [添加依赖](#添加依赖) 以了解如何指定依赖。

<!--
- A **workspace** is the **broadest organizational unit in Lake**. It bundles together a package (termed the **root**), its transitive dependencies, and Lake's environment. Every package can operate as the root of a workspace and the workspace will derive its configuration from this root.
-->

-  **工作空间 (workspace)** 是 Lake 中 **最大的组织单元**，它将一个被称为 **根** 的包、其传递依赖以及Lake的环境组合在一起。每个包都可以作为工作区的根，并且工作区将从这个根派生其配置。

<!--
A **module** is the **smallest unit of code visible to Lake's build system**. It is generally represented by a Lean source file and a set of binary libraries (i.e., a Lean `olean` and `ilean` plus a system shared library if `precompileModules` is turned on). Modules can import one another in order to use each other's code and Lake exists primarily to facilitate this process.
-->

-  **模块 (module)** 是 Lake 的 **构建系统可见的最小代码单元**。模块常常表现为一个单独的 Lean 源文件或者一系列二进制库文件（即 `olean` 、 `ilean` 加上一个系统共享库）。<!--TODO: if `precompileModules` is turned on 语义不明--> 一个模块可以从另一个模块导入并使用代码<!--也许可以交叉导入？-->，而 Lake 的存在就是为了促进这一过程。

<!--
A **Lean library** is a collection of modules that share a single configuration. Its configuration defines a set of **module roots** that determines which modules are part of the library, and a set of **module globs** that selects which modules to build on a `lake build` of the library. See the [Lean Libraries section](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries) for more details.
-->

-  **Lean 中的库 (Lean library)** 是共用同一配置的模块的集合。其配置定义了一组 **模块根 (module roots)** ，用以确定哪些模块属于该库，以及一组 **模块全局模式 (module globs)** ，用于在库的 `lake build` 过程中选择要构建的模块。参见 [Lean 库部分](#lean-库)

<!--
A **Lean binary executable** is a binary executable (i.e., a program a user can run on their computer without Lean installed) built from a Lean module termed its **root** (which should have a `main` definition). See the [Binary Executables section](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables) for more details.
-->

-  **Lean 中的二进制可执行文件 (Lean binary executable)** 是一个单独的从根模块（定义了 `main` ）构建出的可执行文件（即用户在未安装 Lean 时就能在电脑上运行的文件）。参见 [二进制可执行文件部分](#二进制可执行文件)

<!--
An **external library** is a native (static) library built from foreign code (e.g., C) that is required by a package's Lean code in order to function (e.g., because it uses `@[extern]` to invoke code written in a foreign language). An `extern_lib` target is used to inform Lake of such a requirement and instruct Lake on how to build requisite library. Lake then automatically links the external library when appropriate to give the Lean code access to the foreign functions (or, more technically, the foreign symbols) it needs. See the [External Libraries section](https://github.com/leanprover/lean4/tree/master/src/lake#external-libraries) for more details.
-->

-  **外部库 (external library)** 是 Lean 代码中所依赖的来自其它语言（如 C）的原生（静态）库（例如使用 `@[extern]` 调用的其它语言代码）。`extern_lib` 目标就用来告知 Lake 如何处理这样的依赖，使之自动地以正确方式链接外部库。这样 Lean 代码就可以正常访问所需外部函数（更专业地说是外部符号）。参见 [外部库部分](#外部库) 

<!--
A **target** is the **fundamental build unit of Lake**. A package can defining any number of targets. Each target has a name, which is used to instruct Lake to build the target (e.g., through `lake build <target>`) and to keep track internally of a target's build status. Lake defines a set of builtin target types -- [Lean libraries](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries), [binary executables](https://github.com/leanprover/lean4/tree/master/src/lake#binary-executables), and [external libraries](https://github.com/leanprover/lean4/tree/master/src/lake#external-libraries) -- but a user can [define their own custom targets as well](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets). Complex types (e.g., packages, libraries, modules) have multiple facets, each of which count as separate buildable targets. See the [Defining Build Targets section](https://github.com/leanprover/lean4/tree/master/src/lake#defining-build-targets) for more details.
-->

-  **目标 (target)** <!--不知道会不会不翻过来好一点-->是 Lake **构建的基本单元** 。一个包可以有任意数量的目标。每个目标都有一个名称，该名称用于指示 Lake 构建目标（例如，通过 `lake build <target>`）并内部跟踪目标的构建状态。Lake 定义了一套内置目标类型 —— [Lean 库](#lean-库)，[二进制可执行文件](#二进制可执行文件) 和 [外部库](#外部库) —— 但用户也可以 [定义他们自己的自定义目标](#自定义目标)。复杂类型（例如，包、库、模块）具有多个 facet，每个facet都算作独立的可构建目标。有关更多详细信息，请参阅 [定义构建目标部分](#设定构建目标)。

<!--
A **facet** is an element built from another organizational unit (e.g., a package, module, library, etc.). For instance, Lake produces `olean`, `ilean`, `c`, and `o` files all from a single module. Each of these components are thus termed a _facet_ of the module. Similarly, Lake can build both static and shared binaries from a library. Thus, libraries have both `static` and `shared` facets. Lake also allows users to define their own custom facets to build from modules and packages, but this feature is currently experimental and not yet documented.
-->

-  **facet** 是从其它组织单位构建出的单个元素（如一个包、模块、库等等）。例如，Lake 从单个模块文件产生了 `olean` ， `ilean` ， `c` ，和 `o` 文件。这些每一个都被称为模块的一个 *facet* 。相似的， Lake 可以从一个库中编译静态 `static` 和共享 `shared` 两种二进制文件。这就是说，库同时具有 `static` 和 `shared` 两种 facet。Lake 也允许用户按自己的方式定义模块和包构建出的 facet，但这一特性还处测试阶段且尚无相应文档。

<!--
A **trace** is a piece of data (generally a hash) which is used to verify whether a given target is up-to-date (i.e., does not need to be rebuilt). If the trace stored with a built target matches the trace computed during build, then a target is considered up-to-date. A target's trace is derived from its various **inputs** (e.g., source file, Lean toolchain, imports, etc.).
-->

-  **trace** 是用来检验 target 是否已是最新（即是否不用重新构建）的一些数据（一般是 hash ）。如果已经构建的目标的 trace 和构建中计算的 trace 相符，该目标就会被认为是最新的。一个目标的 trace 从它的许多**输入**得出（例如，源文件，Lean 工具链，导入列表等等）。

<!--
## Package Configuration Options
-->
## 包配置选项

Lake 提供了多种多样的包配置选项

### Layout  布局

These options control the top-level directory layout of the package and its build directory. Further paths specified by libraries, executables, and targets within the package are relative to these directories.

- `packagesDir`: The directory to which Lake should download remote dependencies. Defaults to `.lake/packages`.
- `srcDir`: The directory containing the package's Lean source files. Defaults to the package's directory.
- `buildDir`: The directory to which Lake should output the package's build results. Defaults to `build`.
- `leanLibDir`: The build subdirectory to which Lake should output the package's binary Lean libraries (e.g., `.olean`, `.ilean` files). Defaults to `lib`.
- `nativeLibDir`: The build subdirectory to which Lake should output the package's native libraries (e.g., `.a`, `.so`, `.dll` files). Defaults to `lib`.
- `binDir`: The build subdirectory to which Lake should output the package's binary executables. Defaults to `bin`.
- `irDir`: The build subdirectory to which Lake should output the package's intermediary results (e.g., `.c`, `.o` files). Defaults to `ir`.

### Build & Run  构建 & 运行

These options configure how code is built and run in the package. Libraries, executables, and other targets within a package can further add to parts of this configuration.

- `platformIndependent`: Asserts whether Lake should assume Lean modules are platform-independent. That is, whether lake should include the platform and platform-dependent elements in a module's trace. See the docstring of `Lake.LeanConfig.platformIndependent` for more details. Defaults to `none`.
- `precompileModules`: Whether to compile each module into a native shared library that is loaded whenever the module is imported. This speeds up the evaluation of metaprograms and enables the interpreter to run functions marked `@[extern]`. Defaults to `false`.
- `moreServerOptions`: An `Array` of additional options to pass to the Lean language server (i.e., `lean --server`) launched by `lake serve`.
- `moreGlobalServerArgs`: An `Array` of additional arguments to pass to `lean --server` which apply both to this package and anything else in the same server session (e.g. when browsing other packages from the same session via go-to-definition)
- `buildType`: The `BuildType` of targets in the package (see [`CMAKE_BUILD_TYPE`](https://stackoverflow.com/a/59314670)). One of `debug`, `relWithDebInfo`, `minSizeRel`, or `release`. Defaults to `release`.
- `leanOptions`: Additional options to pass to both the Lean language server (i.e., `lean --server`) launched by `lake serve` and to `lean` while compiling Lean source files.
- `moreLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files.
- `weakLeanArgs`: An `Array` of additional arguments to pass to `lean` while compiling Lean source files. Unlike `moreLeanArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come _before_ `moreLeanArgs`.
- `moreLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Lake already passes some flags based on the `buildType`, but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
- `weakLeancArgs`: An `Array` of additional arguments to pass to `leanc` while compiling the C source files generated by `lean`. Unlike `moreLeancArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come _before_ `moreLeancArgs`.
- `moreLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries). These will come _after_ the paths of `extern_lib` targets.
- `weakLinkArgs`: An `Array` of additional arguments to pass to `leanc` when linking (e.g., binary executables or shared libraries) Unlike `moreLinkArgs`, these arguments do not affect the trace of the build result, so they can be changed without triggering a rebuild. They come _before_ `moreLinkArgs`.
- `extraDepTargets`: An `Array` of [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) names that the package should always build before anything else.

### Test & Lint  测试 & 检查

The CLI commands `lake test` and `lake lint` use definitions configured by the workspace's root package to perform testing and linting (this referred to as the test or lint _driver_). In Lean configuration files, these can be specified by applying the `@[test_driver]` or `@[lint_driver]` to a `script`, `lean_exe`, or `lean_lb`. They can also be configured (in Lean or TOML format) via the following options on the package.

- `testDriver`: The name of the script, executable, or library to drive `lake test`.
- `testDriverArgs`: An `Array` of arguments to pass to the package's test driver.
- `lintDriver`: The name of the script or executable used by `lake lint`. Libraries cannot be lint drivers.
- `lintDriverArgs`: An `Array` of arguments to pass to the package's lint driver.

You can specify definition from a dependency as a package's test or lint driver by using the syntax `<pkg>/<name>`. An executable driver will be built and then run, a script driver will just be run, and a library driver will just be built. A script or executable driver is run with any arguments configured by package (e.g., via `testDriverArgs`) followed by any specified on the CLI (e.g., via `lake lint -- <args>...`).

### Cloud Releases  云发布

These options define a cloud release for the package. See the section on [GitHub Release Builds](https://github.com/leanprover/lean4/tree/master/src/lake#github-release-builds) for more information.

- `releaseRepo`: The URL of the GitHub repository to upload and download releases of this package. If `none` (the default), for downloads, Lake uses the URL the package was download from (if it is a dependency) and for uploads, uses `gh`'s default.
- `buildArchive`: The name of the build archive for the GitHub cloud release. Defaults to `{(pkg-)name}-{System.Platform.target}.tar.gz`.
- `preferReleaseBuild`: Whether to prefer downloading a prebuilt release (from GitHub) rather than building this package from the source when this package is used as a dependency.

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
Lean 库目标定义了可用 `import` 导入的 Lean 模块及其构建方式

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

- `srcDir`: The subdirectory of the package's source directory containing the library's source files. Defaults to the package's `srcDir`. (This will be passed to `lean` as the `-R` option.)
- `roots`: An `Array` of root module `Name`(s) of the library. Submodules of these roots (e.g., `Lib.Foo` of `Lib`) are considered part of the library. Defaults to a single root of the target's name.
- `globs`: An `Array` of module `Glob`(s) to build for the library. The term `glob` comes from [file globs](https://en.wikipedia.org/wiki/Glob_(programming)) (e.g., `foo/*`) on Unix. A submodule glob builds every Lean source file within the module's directory (i.e., ``Glob.submodules `Foo`` is essentially equivalent to a theoretical `import Foo.*`). Local imports of glob'ed files (i.e., fellow modules of the workspace) are also recursively built. Defaults to a `Glob.one` of each of the library's `roots`.
- `libName`: The `String` name of the library. Used as a base for the file names of its static and dynamic binaries. Defaults to the name of the target.
- `extraDepTargets`: An `Array` of [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) names to build before the library's modules.
- `defaultFacets`: An `Array` of library facets to build on a bare `lake build` of the library. For example, setting this to `#[LeanLib.sharedLib]` will build the shared library facet.
- `nativeFacets`: A function `(shouldExport : Bool) → Array` determining the [module facets](https://github.com/leanprover/lean4/tree/master/src/lake#defining-new-facets) to build and combine into the library's static and shared libraries. If `shouldExport` is true, the module facets should export any symbols a user may expect to lookup in the library. For example, the Lean interpreter will use exported symbols in linked libraries. Defaults to a singleton of `Module.oExportFacet` (if `shouldExport`) or `Module.oFacet`. That is, the object files compiled from the Lean sources, potentially with exported Lean symbols.
- `platformIndependent`, `precompileModules`, `buildType`, `leanOptions`, `<more|weak><Lean|Leanc|Link>Args`, `moreServerOptions`: Augments the package's corresponding configuration option. The library's arguments come after, modules are precompiled if either the library or package are, `platformIndependent` falls back to the package on `none`, and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest).

<!--
### Binary Executables
-->
### 二进制可执行文件

<!--
A Lean executable target builds a binary executable from a Lean module with a `main` function.
-->

一个 Lean 二进制可执行文件目标从带有 `main` 函数的文件构建出可执行文件

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

- `srcDir`: The subdirectory of the package's source directory containing the executable's source file. Defaults to the package's `srcDir`. (This will be passed to `lean` as the `-R` option.)
- `root`: The root module `Name` of the binary executable. Should include a `main` definition that will serve as the entry point of the program. The root is built by recursively building its local imports (i.e., fellow modules of the workspace). Defaults to the name of the target.
- `exeName`: The `String` name of the binary executable. Defaults to the target name with any `.` replaced with a `-`.
- `extraDepTargets`: An `Array` of [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets) names to build before the executable's modules.
- `nativeFacets`: A function `(shouldExport : Bool) → Array` determining the [module facets](https://github.com/leanprover/lean4/tree/master/src/lake#defining-new-facets) to build and link into the executable. If `shouldExport` is true, the module facets should export any symbols a user may expect to lookup in the library. For example, the Lean interpreter will use exported symbols in linked libraries. Defaults to a singleton of `Module.oExportFacet` (if `shouldExport`) or `Module.oFacet`. That is, the object file compiled from the Lean source, potentially with exported Lean symbols.
- `supportInterpreter`: Whether to expose symbols within the executable to the Lean interpreter. This allows the executable to interpret Lean files (e.g., via `Lean.Elab.runFrontend`). Implementation-wise, on Windows, the Lean shared libraries are linked to the executable and, on other systems, the executable is linked with `-rdynamic`. This increases the size of the binary on Linux and, on Windows, requires `libInit_shared.dll` and `libleanshared.dll` to be co-located with the executable or part of `PATH` (e.g., via `lake exe`). Thus, this feature should only be enabled when necessary. Defaults to `false`.
- `platformIndependent`, `precompileModules`, `buildType`, `leanOptions`, `<more|weak><Lean|Leanc|Link>Args`, `moreServerOptions`: Augments the package's corresponding configuration option. The library's arguments come after, modules are precompiled if either the library or package are, `platformIndependent` falls back to the package on `none`, and the build type is the minimum of the two (`debug` is the lowest, and `release` is the highest).

<!--
### External Libraries
-->

### 外部库

A external library target is a non-Lean **static** library that will be linked to the binaries of the package and its dependents (e.g., their shared libraries and executables).

**Important:** For the external library to link properly when `precompileModules` is on, the static library produced by an `extern_lib` target must following the platform's naming conventions for libraries (i.e., be named `foo.a` on Windows and `libfoo.a` on Unix). To make this easy, there is the `Lake.nameToStaticLib` utility function to convert a library name into its proper file name for the platform.

**Syntax**

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  -- a build function that produces its static library
```

The declaration is essentially a wrapper around a `System.FilePath` [target](https://github.com/leanprover/lean4/tree/master/src/lake#custom-targets). Like such a target, the `pkg` parameter and its type specifier are optional and body should be a term of type `FetchM (BuildJob System.FilePath)` function that builds the static library. The `pkg` parameter is of type `NPackage _package.name` to provably demonstrate that it is the package in which the external library is defined.

<!--
### Custom Targets
-->

### 自定义目标

A arbitrary target that can be built via `lake build <target-name>`.

**Syntax**

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  -- a build function that produces a `BuildJob α`
```
The `pkg` parameter and its type specifier are optional and the body should be a term of type `FetchM (BuildJob α)`. The `pkg` parameter is of type `NPackage _package.name` to provably demonstrate that it is the package in which the target is defined.

<!--
Defining New Facets
-->
## 定义新 facet

A Lake package can also define new _facets_ for packages, modules, and libraries. Once defined, the new facet (e.g., `facet`) can be built on any current or future object of its type (e.g., through `lake build pkg:facet` for a package facet). Module facets can also be provided to [`LeanLib.nativeFacets`](https://github.com/leanprover/lean4/tree/master/src/lake#lean-libraries) to have Lake build and use them automatically when producing shared libraries.

**Syntax**

```lean
package_facet «facet-name» (pkg : Package) : α :=
  -- a build function that produces a `BuildJob α`

module_facet «facet-name» (mod : Module) : α :=
  -- a build function that produces a `BuildJob α`

library_facet «facet-name» (lib : LeanLib) : α :=
  -- a build function that produces a `BuildJob α`
```

In all of these, the object parameter and its type specifier are optional and the body should be a term of type `FetchM (BuildJob α)`.

<!--
## Adding Dependencies
-->

## 添加依赖

<!--
Lake packages can have dependencies. Dependencies are other Lake packages the current package needs in order to function. They can be sourced directly from a local folder (e.g., a subdirectory of the package) or come from remote Git repositories. For example, one can depend on [mathlib](https://reservoir.lean-lang.org/@leanprover-community/mathlib) like so:
-->

Lake 包可添加依赖。依赖可以来自本地目录（如包的子目录）或远程 Git 仓库。例如，你可以这样添加 [mathlib](https://reservoir.lean-lang.org/@leanprover-community/mathlib) 依赖：

```lean
package hello

require "leanprover-community" / "mathlib"
```

<!--
The next run of `lake build` (or refreshing dependencies in an editor like VSCode) will clone the mathlib repository and build it. Information on the specific revision cloned will then be saved to `lake-manifest.json` to enable reproducibility (i.e., ensure the same version of mathlib is used by future builds). To update `mathlib` after this, you will need to run `lake update` -- other commands do not update resolved dependencies.
-->

下次运行 `lake build` （或是用 VSCode 一类的编辑器刷新依赖）时将会克隆并构建 mathlib 仓库。克隆的特定版本的信息将存入 `lake-manifest.json` 以确保可复现性（即保证未来的构建使用同一版本的 mathlib）。在这之后如果想要更新 `mathlib` ，你需要使用 `lake update` —— 其它的命令都将不会更新已解析的依赖。

<!--
For theorem proving packages which depend on `mathlib`, you can also run `lake new <package-name> math` to generate a package configuration file that already has the `mathlib` dependency (and no binary executable target).
-->

对于依赖 `mathlib` 的定理证明包，你也可以用 `lake new <package-name> math` 直接创建带有 mathlib 依赖的包配置（无二进制可执行文件目标）。

<!--
**NOTE:** For mathlib in particular, you should run `lake exe cache get` prior to a `lake build` after adding or updating a mathlib dependency. Otherwise, it will be rebuilt from scratch (which can take hours). For more information, see mathlib's [wiki page](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency) on using it as a dependency.
-->

**注意：** 对于 mathlib 而言，在添加或升级其作为依赖后，你还需要在 `lake build` 之前使用 `lake exe cache get` 。否则构建将从零开始（耗时数小时）。参阅 [mathlib wiki page](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency) 


## Lean `require`

<!--
The `require` command in Lean Lake configuration follows the general syntax:
-->

Lean 的 Lake 配置文件中 `require` 命令的基本语法是这样的：

```lean
require ["<scope>" /] <pkg-name> [@ <version>]
  [from <source>] [with <options>]
```

<!--
The `from` clause tells Lake where to locate the dependency. Without a `from` clause, Lake will lookup the package in the default registry (i.e., [Reservoir](https://reservoir.lean-lang.org/@lean-dojo/LeanCopilot)) and use the information there to download the package at the specified `version`. The optional `scope` is used to disambiguate which package with `pkg-name` to lookup. In Reservoir, this scope is the package owner (e.g., `leanprover` of [@leanprover/doc-gen4](https://reservoir.lean-lang.org/@leanprover/doc-gen4)).
-->

`from` 子句告知 Lake 依赖的地址。没有 `from` 从句，Lake 将从默认 registry 查找包（即 [Reservoir](https://reservoir.lean-lang.org/@lean-dojo/LeanCopilot) ）并使用获得的信息下载指定 `version` 的包。可选的 `scope` 用来消除同具有 `pkg-name` 的包的歧义。在 Reservoir 中，scope 部分是包的所有者（例如，[@leanprover/doc-gen4](https://reservoir.lean-lang.org/@leanprover/doc-gen4) 中的 `leanprover` ）。

<!--
The `with` clause specifies a `NameMap String` of Lake options used to configure the dependency. This is equivalent to passing `-K` options to the dependency on the command line.
-->

`with` 子句指定了一个 `NameMap String` 类型的 Lake 选项，用于配置依赖。这相当于用命令行将 `-K` 选项传递给依赖项。<!--TODO: NameMap-->

<!--
## Supported Sources
-->

## 受支持的源

<!--
Lake supports the following types of dependencies as sources in a `from` clause.
-->

在 `from` 子句中，Lake 支持下列依赖源

<!--
### Path Dependencies
-->
### 路径依赖


```
from <path>
```

Lake 将从的 `path` 目录（相对于所依赖包的目录）中加载包。<!--TODO: 还不清楚具体用法，可能有误-->

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

Lake 从固定的 `url` 中克隆 Git 版本并 checkout 到指定的 `rev` 。其中版本标识 `rev` 可以是 commit hash, branch，或 tag。如果都没有，Lake 将使用默认的 `master` 分支。checkout 之后，Lake 将从子目录 `subDir` 中加载包（未指定子目录则使用根目录）。

## TOML `require`

<!--
To `require` a package in a TOML configuration, the parallel syntax for the above examples is:
-->

TOML 版本的配置文件中等价语法如下：

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

## Github Release Builds


Lake supports uploading and downloading build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages. This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from the source themselves.

### Downloading

[](https://github.com/leanprover/lean4/tree/master/src/lake#downloading)

To download artifacts, one should configure the package [options](https://github.com/leanprover/lean4/tree/master/src/lake#cloud-releases) `releaseRepo?` and `buildArchive?` as necessary to point to the GitHub repository hosting the release and the correct artifact name within it (if the defaults are not sufficient). Then, set `preferReleaseBuild := true` to tell Lake to fetch and unpack it as an extra package dependency.

Lake will only fetch release builds as part of its standard build process if the package wanting it is a dependency (as the root package is expected to modified and thus not often compatible with this scheme). However, should one wish to fetch a release for a root package (e.g., after cloning the release's source but before editing), one can manually do so via `lake build :release`.

Lake internally uses `curl` to download the release and `tar` to unpack it, so the end user must have both tools installed to use this feature. If Lake fails to fetch a release for any reason, it will move on to building from the source. Also note that this mechanism is not technically limited to GitHub, any Git host that uses the same URL scheme works as well.

### Uploading

[](https://github.com/leanprover/lean4/tree/master/src/lake#uploading)

To upload a built package as an artifact to a GitHub release, Lake provides the `lake upload <tag>` command as a convenient shorthand. This command uses `tar` to pack the package's build directory into an archive and uses `gh release upload` to attach it to a pre-existing GitHub release for `tag`. Thus, in order to use it, the package uploader (but not the downloader) needs to have `gh`, the [GitHub CLI](https://cli.github.com/), installed and in `PATH`.


<!--
## Writing and Running Scripts
-->

## 编写及运行脚本

<!--
A configuration file can also contain a number of `scripts` declaration. A script is an arbitrary `(args : List String) → ScriptM UInt32` definition that can be run by `lake script run`. For example, given the following `lakefile.lean`:
-->

配置文件中也可能包含有脚本声明。脚本，就是任意的 `(args : List String) → ScriptM UInt32` 类型的定义，它可通过 `lake script run` 来运行。例如以下的 `lakefile.lean` ：

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

你可以用 `lake scripts doc` 输出一个脚本的 docstring：

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

如果你已经安装了带有 `lake` 的 Lean ，你可以直接用 `lake build` 构建一个新 `lake` 。

<!--
Otherwise, there is a pre-packaged `build.sh` shell script that can be used to build Lake. It passes it arguments down to a `make` command. So, if you have more than one core, you will probably want to use a `-jX` option to specify how many build tasks you want it to run in parallel. For example:
-->

或者，也可以用已经提前备好的 `build.sh` 脚本来构建 Lake。它将参数传给 `make` 命令。所以，如果你的处理器支持多核心，你可以用 `-jX` 选项指定你想并行的构建任务数。例如：

```shell
$ ./build.sh -j4
```

<!--
After building, the `lake` binary will be located at `.lake/build/bin/lake` and the library's `.olean` files will be located in `.lake/build/lib`.
-->

构建后，`lake` 二进制文件将位于 `.lake/build/bin/lake` 中，而库的 `.olean` 文件将位于 `.lake/build/lib` 下。

### Building with Nix Flakes

Lake is built as part of the main Lean 4 flake at the repository root.

<!--还不知道这是啥，不翻-->

### Augmenting Lake's Search Path

The `lake` executable needs to know where to find the Lean library files (e.g., `.olean`, `.ilean`) for the modules used in the package configuration file (and their source files for go-to-definition support in the editor). Lake will intelligently setup an initial search path based on the location of its own executable and `lean`.

Specifically, if Lake is co-located with `lean` (i.e., there is `lean` executable in the same directory as itself), it will assume it was installed with Lean and that both Lean and Lake are located under their shared sysroot. In particular, their binaries are located in `<sysroot>/bin`, their Lean libraries in `<sysroot>/lib/lean`, Lean's source files in `<sysroot>/src/lean`, and Lake's source files in `<sysroot>/src/lean/lake`. Otherwise, it will run `lean --print-prefix` to find Lean's sysroot and assume that Lean's files are located as aforementioned, but that `lake` is at `<lake-home>/.lake/build/bin/lake` with its Lean libraries at `<lake-home>/.lake/build/lib` and its sources directly in `<lake-home>`.

This search path can be augmented by including other directories of Lean libraries in the `LEAN_PATH` environment variable (and their sources in `LEAN_SRC_PATH`). This can allow the user to correct Lake's search when the files for Lean (or Lake itself) are in non-standard locations. However, such directories will _not_ take precedence over the initial search path. This is important during development, as this prevents the Lake version used to build Lake from using the Lake version being built's Lean libraries (instead of its own) to elaborate Lake's `lakefile.lean` (which can lead to all kinds of errors).