# SF-lean4: 《软件基础》Lean 4 中文社区重制版

> **Software Foundations in Modern Lean 4 (Chinese Edition)**  
> 致力于用现代 Lean 4 重塑经典形式化验证教材《软件基础》（Software Foundations），提供地道、惯用（Idiomatic）的形式化代码实现与通俗详尽的中文解析。

---

## 🎯 项目愿景

《软件基础》（*Software Foundations*, 简称 **SF**）由宾夕法尼亚大学 Benjamin C. Pierce 教授团队打造，是程序语言理论（PLT）、形式化方法与软件验证领域最广为流传的经典教材。

原书基于 Coq（现 Rocq）编写，虽然逻辑严密，但在现代编辑器集成、函数式编程人体工学以及现代语言生态上稍显沧桑。**SF-lean4** 旨在：

1. **紧贴最新 Lean 4 语法与哲学**：不机械地直译 Coq 策略，而是采用 Lean 4 现代的方程编译器（Equation Compiler）、模式匹配、宏、类型类及现代策略（如 `omega`, `aesop`, `cases`）。
2. **高质量全中文教学注释**：保持文学化编程（Literate Programming）风格，在 `.lean` 源码内直接嵌入中文概念讲解、证明思路梳理与练习指引。
3. **100% 忠实还原与严格审计**：每一章均对照英文原版进行逐字逐句严谨审计，确保定义、定理、引理与练习题**无删减、无遗漏**，习题名称与星级完全契合原版自动化评分标准。
4. **沉浸式 Neovim / VS Code 体验**：结合 `lean.nvim` 的实时 Infoview，让学习者像玩解谜游戏一样一步步填补 `sorry`。
5. **配套在线文档（规划中）**：后续将通过 `mdbook` / `Verso` 一键生成与原书类似的交互式中文 HTML 网页教程。

---

## 📚 卷次规划与翻译进度

### 第一卷：逻辑基础 (Volume 1: Logical Foundations - LF)

- **核心基础模块**
  - [x] `Basics.lean` (基础篇：函数式编程与基础策略) *(✅ 124/124 项声明，20/20 道习题已 100% 审计完成)*
  - [x] `Induction.lean` (归纳证明篇：数学归纳法、局部引理与数制规范化) *(✅ 53/53 项声明，14/14 道习题已 100% 审计完成)*
  - [x] `Lists.lean` (结构化数据：列表、数据对与偏映射词典) *(✅ 116/116 项声明，19/19 道习题已 100% 审计完成)*
  - [x] `Poly.lean` (多态与高阶函数：全称多态、高阶变换、Church 数) *(✅ 123/123 项声明，20/20 道习题已 100% 审计完成)*
  - [x] `Tactics.lean` (证明策略进阶：`apply`, `injection`, `discriminate`, `revert`, `split`) *(✅ 66/66 项声明，18/18 道习题已 100% 审计完成)*
  - [x] `Logic.lean` (逻辑学基础：构造性命题、经典逻辑与一等公民逻辑联结词) *(✅ 128/128 项声明，31/31 道习题已 100% 审计完成)*
  - [x] `IndProp.lean` (归纳命题与关系：归纳谓词、置换、泵引理、布尔反射与正则导数) *(✅ 172/172 项声明，46/46 道习题已 100% 审计完成)*
  - [x] `Maps.lean` (全域映射与偏映射：形式化状态机基础) *(✅ 28/28 项声明，6/6 道习题已 100% 审计完成)*
- **进阶与形式化语言模块**
  - [x] `ProofObjects.lean` (柯里-霍华德同构与证明对象) *(✅ 59/59 项声明，18/18 道习题已 100% 审计完成)*
  - [x] `IndPrinciples.lean` (归纳法则与自定义归纳模式) *(✅ 42/42 项声明，10/10 道习题已 100% 审计完成)*
  - [x] `Rel.lean` (关系性质与二元关系模型) *(✅ 34/34 项声明，12/12 道习题已 100% 审计完成)*
  - [x] `ImpParser.lean` (词法与语法分析器) *(✅ 34/34 项声明，端到端编译解析器与用例 100% 审计完成)*
  - [ ] `ImpCEvalFun.lean` (命令式语言求值函数) *(⏳ 进行中)*
  - [ ] `Extraction.lean` (代码抽取与 AOT 编译)
  - [ ] `Auto.lean` / `AltAuto.lean` (自动化证明策略 `omega`, `aesop`, `simp` 深入)
  - [ ] `Postscript.lean` / `Bib.lean` (后记与参考文献)

### 第二卷：程序语言基础 (Volume 2: Programming Language Foundations - PLF) *(规划中)*
### 第三卷：函数式算法验证 (Volume 3: Verified Functional Algorithms - VFA) *(规划中)*

---

## 🚀 快速上手

### 1. 环境准备

确保本机已安装 Lean 4 版本管理器 `elan`：

```bash
# 安装 elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### 2. 编译与检查

在项目根目录下构建整个工程：

```bash
lake build
```

*(注：练习题中的 `sorry` 占位符会在编译时提示 `warning: declaration uses 'sorry'`，这是正常现象)*

### 3. 开始做题（Neovim / VS Code）

使用 Neovim 打开章节文件：

```bash
nvim SFLean4/LF/Basics.lean
```

- 编辑器右侧会自动弹出 **Infoview** 窗口；
- 寻找到带有 `sorry` 的练习题（如 `nandb`、`factorial`、`plus_id_exercise`）；
- 将光标停在 `sorry` 上，右侧将实时渲染待证明的目标（Goal）与已知假设（Hypotheses）；
- 写出你的证明并替换 `sorry`，当 Infoview 显示 **`No goals`** 时即代表证明通过！

---

## ⚖️ 许可与致谢

- 原始英文版教程版权归属于 Benjamin C. Pierce 等原作者，遵循其原版开源教学分发许可。
- 本项目遵循开源理念，旨在推进中文社区在依赖类型论与形式化验证领域的教学普及。