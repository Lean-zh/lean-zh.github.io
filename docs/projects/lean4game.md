
## 引言

本篇介绍如何用 Lean4Game 添加 Lean4 游戏。这类互动游戏不仅利于 Lean 本身的学习，还能促进对学科知识的理解，让关联的学科群体对 Lean 有更直观的认识。

当前部署了 NNG4 游戏：[nng4.leanprover.cn](https://nng4.leanprover.cn) ，可在线体验，后续计划写一个李代数入门的（mark 开坑）。

### 相关项目与资源

教程涉及的项目和资源链接：

- **lean4game**：LEAN 社区驱动的项目，用于开发 Lean4 游戏（[GitHub 仓库](https://github.com/leanprover-community/lean4game)）。
- **GameSkeleton**：Lean4 游戏的模板代码（[GitHub 仓库](https://github.com/hhu-adam/GameSkeleton.git)）。
- **NNG4**：自然数游戏，从皮亚诺公理开始，构建自然数的基本运算和性质（[GitHub 仓库](https://github.com/leanprover-community/NNG4)）。

社区官网目前提供了自然数和集合论等游戏，也欢迎根据自己的学科知识，贡献更多的游戏~

<!-- ![20240623160501](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240623160501.png) -->

## 发布游戏

我们通过一个简单的示例介绍游戏的发布过程。

### 下载游戏模板

首先，下载 GameSkeleton 模板仓库，这个是网页上最终展示的内容：

```bash
git clone https://github.com/hhu-adam/GameSkeleton.git
```

文件结构如下：

```bash
├── Game
│   ├── Levels
│   │   ├── DemoWorld
│   │   │   └── L01_HelloWorld.lean
│   │   └── DemoWorld.lean
│   └── Metadata.lean
├── Game.lean
├── LICENSE
├── README.md
├── lake-manifest.json
├── lakefile.lean
└── lean-toolchain
```

这是一个标准的 Lean 包结构，其中 `lean-toolchain`、`lakefile.lean` 和 `lake-manifest.json` 是 Lean 包的基本文件。`Game` 文件夹包含游戏内容，而 `Game.lean` 是游戏的入口文件。

更新依赖并构建项目：

```bash
lake update -R
lake build
```

类似地，也可以下载其他游戏模板，例如 NNG4：

```bash
# cd .. # 回到同一级目录
git clone https://github.com/leanprover-community/NNG4.git
cd NNG4
lake update -R
lake build
```

### 下载 Lean4Game

Lean4Game 是游戏的前后端框架，用于创建游戏的主页面。

首先，安装 Node.js 和 npm

```bash
# 安装 nvm
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.3/install.sh | bash
# 安装 nodejs
nvm install node
nvm use node
```

下载 Lean4Game，并将其放在游戏的**同级目录**：

```bash
# 下载 Lean4Game
git clone https://github.com/leanprover-community/lean4game.git
cd lean4game
# 安装依赖
npm install --force
```

设置环境变量（可选）：

```bash
export PORT=8080
export CLIENT_PORT=3000
export VITE_CLIENT_DEFAULT_LANGUAGE=zh
```

其中 `PORT` 为运行 Lean 代码的后端端口，默认是 `8080`；`CLIENT_PORT` 为前端访问端口，默认是 `3000`；`VITE_CLIENT_DEFAULT_LANGUAGE` 为界面语言，默认为 `en`。

执行 `npm start` 启动游戏，如果看到以下页面，就表示访问成功：

![20240623121710](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240623121710.png)

此外，可以在右上角的偏好设置切换语言：

![20240623164430](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240623164430.png)

### Nginx 配置

如果一切顺利，访问 `http://localhost:3000/#/g/local/GameSkeleton` 会看到 “Hello World” 的界面：

![20240623130158](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240623130158.png)

假设服务启动在 3000 端口，可以将域名 `game.leanprover.cn` 配置为游戏主页面，参考配置如下：

```bash
server {
    listen 443 ssl;
    ssl_certificate /etc/letsencrypt/live/game.leanprover.cn/fullchain.pem; 
    ssl_certificate_key /etc/letsencrypt/live/game.leanprover.cn/privkey.pem; 
    server_name game.leanprover.cn;
    location / {
        proxy_pass http://localhost:3000;
        proxy_set_header Upgrade $http_upgrade;
        proxy_set_header Connection "Upgrade";
        proxy_set_header Host $host;
        proxy_read_timeout 86400;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_ssl_server_name on;
        proxy_http_version 1.1;
        chunked_transfer_encoding off;
        proxy_buffering off;
        proxy_cache off;
        proxy_set_header X-Forwarded-Proto $scheme;
        client_max_body_size 0;
    }
}
```

为简化输入，可以为游戏单独配置一个子域名进行跳转，例如 `nng4.leanprover.cn`：

```bash
server {
    listen 443 ssl; 
    ssl_certificate /etc/letsencrypt/live/nng4.leanprover.cn/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/nng4.leanprover.cn/privkey.pem;
    server_name nng4.leanprover.cn;
    return 301 https://game.leanprover.cn/#/g/local/NNG4;
}
```

这样只需访问 nng4.leanprover.cn，而不需要输入后面的一长串 URI。


<!-- 通常，对 `client/` 或 `relay/` 中文件的任何更改都会导致服务器自动重新启动。

在生产环境中，可以执行 `npm run build` 在 `client/dist` 下构建代码，再启动服务：

npm run build
npm run start_client
npm run production

这里似乎存在 bug
-->

## 游戏修改指南

本节以 NNG4 为例，介绍游戏文件结构和如何添加游戏内容。

### 游戏入口 `Game.lean`

文件 `Game.lean` 是整个游戏的主干，负责整合所有内容。以下是示例代码：

```lean
import GameServer.Commands

-- 导入所有世界
import Game.Levels.Tutorial

Title "My Game"

Introduction "
Hi, nice you're here! Click on a world to start.
"

Info "
This game has been developed by me.
"

-- Dependency World₁ → World₂ -- 由于使用了 `≠`
MakeGame
```

代码解析：

1. `import`：导入游戏服务器命令。其中 `GameServer` 是从 lean4game 引入的，不是来自当前的模板仓库。
2. `Title "My Game"`：设置游戏的标题。
3. `Introduction`：在世界选择界面旁显示的介绍文本。
4. `Info`：在游戏菜单中显示的信息，介绍游戏的背景和开发者信息等。
5. `Dependency`：一个可选命令，用于设置世界之间的依赖关系。例如，若一个世界介绍了 `≠` 符号，而在另一个世界中用户需要已知此符号，则可使用此命令。
6. `MakeGame`：构建游戏的命令。如果存在需要修复的问题，将以警告或错误的形式显示（在 VSCode 中为橙色/红色波浪线）。

可对照下图：

![20240623142725](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240623142725.png)

#### 创建关卡

下面是一个最简关卡文件示例：

```lean
import GameServer.Commands

World "MyWorld"
Level 1
Title "Hello World"

Introduction "
A message shown at the beginning of the level. Use it to explain any new concepts.
"

/-- The exercise statement in natural language using latex: $\iff$. -/
Statement (n : Nat) : 0 + n = n := by
  sorry

Conclusion "
The message shown when the level is completed
"
```

操作步骤：
1. 创建文件夹 `Game/Levels/MyWorld`
2. 创建文件 `Game/Levels/MyWorld/L01_hello.lean`
3. 将上述代码复制到你的第一个关卡文件中。


#### 创建世界

接下来，我们创建一个世界。需要创建一个名为 `MyWorld.lean` 的文件，并将所有关卡文件导入到该世界中：

```lean
import Game.Levels.MyWorld.L01_hello

World "MyWorld"
Title "My First World"

Introduction "
This introduction text is shown when one first enters a world.
"
```

操作步骤：
1. 创建文件 `Game/Levels/MyWorld.lean`
2. 使用上面的模板，确保导入了该世界的所有关卡。
3. 在 `Game.lean` 中导入该世界：`import Game.Levels.MyWorld`

至此，我们已成功创建一个包含一个关卡的世界并将其加入到游戏中 🎉。

`Game.lean` 中的 `MakeGame` 命令会指出需要修复的任何问题。例如，如果显示：

![makegame](https://qiniu.wzhecnu.cn/PicBed6/picgo/20240623145644.png)

这意味着世界 `MyWorld` 使用了 `sorry` 策略，但此策略尚未在任何地方被引入。

每次添加或修改游戏内容后，都需要重新构建更新：

```bash
# cd NNG4 # 进入游戏目录
lake build
```

### 高级交互特性

接下来我们将粗略介绍游戏中的高级交互功能。这部分功能十分丰富，目前只进行初步说明。后续添加小游戏的过程，再进一步拓展和补充。

#### 定理和策略的管理

玩家在游戏中拥有一个逐步解锁的定理和策略清单。在关卡设计中，通过以下命令在 `Statement` 下方解锁或引入新的定理和策略：

```lean
NewTactic induction simp -- 解锁 `induction` 和 `simp`
NewTheorem Nat.zero_mul
NewDefinition Pow
```

**重要提示**：所有命令中的名称都需要使用**全限定名**。例如，应使用 `NewTheorem Nat.zero_mul` 而非 `NewTheorem zero_mul`。

#### 文档条目

如果发现定理文档缺失，系统会显示警告。可以通过添加文档条目解决这一问题：

```lean
/--
some description
-/
TheoremDoc Nat.zero_mul as "zero_mul" in "Mul"

/--
some description
-/
TacticDoc simp

/--
some description
-/
DefinitionDoc Pow as "^"
```

创建一个文件 `Game/Doc/MyTheorems.lean`，在其中添加文档并将其导入项目中。

如果未提供任何文档内容，游戏将尝试寻找并展示该条目的文档字符串。

#### 清单管理

玩家可以通过以下命令在关卡中禁用或只启用特定的已解锁条目：

```lean
DisabledTactic, DisabledTheorem, OnlyTactic, OnlyTheorem
```

这些命令的语法与前边相同。前两个命令用于禁用该关卡的特定条目，后两个命令用于只启用指定的条目。

#### 定理标签

通过 `TheoremTab "Mul"` 命令为定理分组，并指定在关卡中默认打开的标签。

#### 隐藏策略

使用 `NewHiddenTactic` 命令可以添加允许策略而不在玩家清单中显示。例如：

```lean
NewTactic rw
NewHiddenTactic rewrite nth_rewrite rwa
```

在此例中，只有 `rw` 会在清单中显示。

### 关卡设计

通过一个示例来查看关卡的代码：

```lean
/-- 我们定义一个从 ℕ 到 ℕ 的函数。 -/
Statement
    : ℕ → ℕ := by
  Hint "为了解决这个目标，
  你需要构想一个从 `ℕ`
  到 `ℕ` 的函数。开始使用

  `intro n`"
  intro n
  Hint "我们的任务现在是构造一个自然数，这个数可以依赖于 ${n}。我们可以使用 `exact` 并写出我们想要定义的函数的公式。例如
  我们在文件顶部导入了加法和乘法，
  所以

  `exact 3 * {n} + 2`

  将完成目标，最终定义函数 $f({n})=3{n}+2$."
  exact 3 * n + 2
```

`Statement` 用于定义练习，其用法类似于 `example` 或 `theorem`，但必须使用策略证明，即 `:= by` 是固定的语法部分。

`Statement` 可以接练习的命名，比如：`Statement my_first_exercise (n : Nat) …`。命名后它会被添加到清单中，并在后续关卡中可用。

此外，`Statement` 前的注释将作为练习的描述显示在游戏中，且支持 Latex。

#### 证明

证明必须是策略证明，即 `:= by` 是固定的语法部分。

以下是一些有助于结构化证明的策略：

- `Hint`：可以使用 `Hint "text"` 在游戏的目标状态匹配时显示文本。更多关于提示的选项，请参见相关文档。
- `Branch`：可以在证明中添加 `Branch`，执行替代策略序列，帮助在不同位置设置 `Hint`。`Branch` 不会影响主证明且不需完成任何目标。
- `Template`/`Hole`：用于提供示例证明模板。`Template` 中的内容将被复制到编辑器中，所有 `Hole` 将被替换为 `sorry`。注意，拥有 `Template` 将强制用户在该关卡使用编辑器模式。

### 提示

提示是游戏开发中可能是最重要的部分。提示将在玩家的当前目标与示例证明中的目标匹配时显示。可以使用 `Branch` 在死胡同或替代证明路径中设置提示。

### 添加图片

可以在游戏的任何层级（游戏/世界/关卡）添加图片，这些图像将显示在游戏中。

文件需放置在 `images/` 中，并通过在创建的文件中添加如 `Image "images/path/to/myWorldImage.png"` 的命令来引用。

## 注意事项

设计新游戏时应考虑的其他事项：

* 在字符串内部需要转义反斜杠，但在文档注释的字符串内部则不需要，因此你会写 `Introduction "some latex here: $\\iff$."` 但 `/-- some latex here: $\iff$. -/ Statement ...`
* 拥有超过 16 个关卡的世界将以螺旋形向外显示，最好保持在这个范围以下。超过 22 个关卡时，螺旋形开始变得难以控制。

## 游戏翻译

通过使用 lean-i18n 和 i18next，可以为游戏添加多语言支持。TODO Ref： https://github.com/leanprover-community/lean4game/blob/main/doc/translate.md

---

以上，一些内容细节待补充完善，欢迎交流~
