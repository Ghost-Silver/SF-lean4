---
layout: home

hero:
  name: "Software Foundations"
  text: "in Lean 4 (中文版)"
  tagline: "形式化逻辑、编程语言理论与算法验证 · 现代 Lean 4 交互式社区重制版"
  image:
    src: /logo.svg
    alt: SF-lean4 Logo
  actions:
    - theme: brand
      text: 🚀 卷一：逻辑基础 (LF)
      link: /LF/Basics
    - theme: alt
      text: ⚡ 卷二：语言基础 (PLF)
      link: /PLF/Preface
    - theme: alt
      text: 🛡️ 卷三：算法验证 (VFA)
      link: /VFA/Preface
    - theme: alt
      text: ⭐️ GitHub 源码
      link: https://github.com/Ghost-Silver/SF-lean4

features:
  - icon: 📐
    title: 卷一：逻辑基础 (LF) · 19 章
    details: 从布尔计算与归纳证明起步，深入柯里-霍华德同构（证明即程序）、构造性逻辑、自反传递闭包以及 Imp 命令式语言语义与自动化策略。
    link: /LF/Basics
  - icon: 🔬
    title: 卷二：语言基础 (PLF) · 21 章
    details: 探索操作语义、程序等价性同余证明、霍尔逻辑三元组与 VCGen、STLC 简单类型系统保型与进益、子类型化、堆内存引用及强规范化停机性。
    link: /PLF/Preface
  - icon: 🛡️
    title: 卷三：算法验证 (VFA) · 17 章
    details: 聚焦经典函数式算法全规约验证：置换判定、插入/归并/选择排序、红黑树对数平衡、前缀树二进制双射、优先队列与二项堆进位链。
    link: /VFA/Preface
  - icon: 💎
    title: 纯正 Lean 4 惯用设计
    details: 摒弃 Coq 历史包袱与冗余战术，深度利用 Lean 4 现代语法、依赖类型系统、递归方程、类型类、宏扩展与现代求解器 (omega/aesop)。
  - icon: ⚡
    title: 零延迟本地全文检索
    details: 集成 MiniSearch 客户端毫秒级模糊检索，支持中英文双语搜索、数学符号与核心定理，随时随地离线闪电查阅。
  - icon: 🎯
    title: 800+ 习题进阶标注
    details: 全卷题目配备清晰难度星级、选做/必做分类标签与详尽的中文引导演示，配合标准 Lake 构建系统，随时开箱练习。
---

<div class="home-content">

## 🌟 项目初衷与理念

《软件基础》（*Software Foundations*，由 Benjamin C. Pierce 等教授开创）是全球计算机科学与形式化方法领域最权威、最经典的教学著作之一。

随着定理证明助手与函数式编程语言 **Lean 4** 在数学界（如陶哲轩主持的形式化项目）以及工业界软件验证领域的迅速崛起，我们启动了 **SF-lean4** 社区重制计划：
- **现代化语言底座**：从 Coq 迁移至 Lean 4，享受极具表达力的语法与宏体系；
- **全量无缝覆盖**：三卷 57 章代码与解析 100% 全量形式化对齐；
- **中文深度精校**：融合地道计算机科学中文表达与原文数学严谨性，为中文学习者破除门槛。

---

## 🗺️ 全书三卷全景路线图

| 卷别 | 篇章数 | 核心内容与理论高光 | 推荐先修 | 章节入口 |
| :--- | :---: | :--- | :--- | :--- |
| **卷一：逻辑基础 (LF)** | 19 章 | 函数式编程、归纳证明、多态、柯里-霍华德同构、Imp 语义、自动化 | 基础函数式编程认知 | [开始阅读 LF →](/LF/Basics) |
| **卷二：编程语言基础 (PLF)** | 21 章 | 霍尔逻辑与 VCGen、小步操作语义、STLC 类型健全性、子类型化、引用、Tait 强规范化 | 卷一 (LF) 基础知识 | [开始阅读 PLF →](/PLF/Preface) |
| **卷三：算法验证 (VFA)** | 17 章 | 排序算法全规约、多重集、二叉搜索树、Okasaki 红黑树、二进制 Trie、二项堆、图着色 | 卷一 (LF) 数据结构基础 | [开始阅读 VFA →](/VFA/Preface) |

---

## ⚡ 5 分钟极速上手本地证明环境

如果你不仅想在网页上查阅，还想在本地 VS Code / Neovim 中亲手填补证明中的 `sorry`，只需以下三步：

### 1. 安装 Lean 4 工具链

推荐通过官方版本管理器 `elan` 安装：

```bash
# macOS / Linux
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### 2. 克隆本仓库

```bash
git clone https://github.com/Ghost-Silver/SF-lean4.git
cd SF-lean4
```

### 3. 一键编译与环境验证

使用 Lean 4 官方构建工具 Lake：

```bash
# 验证构建所有章节
lake build
```

在 VS Code 中安装官方插件 **Lean 4**，打开任何 `.lean` 文件（例如 `SFLean4/LF/Basics.lean`），右侧信息窗即可实时呈现 Goal 证明状态！

---

## 🎯 习题自测与进阶建议

- **标准习题 (Standard)**：标有 1~2 星的题目是掌握每章核心知识必做的巩固练习。
- **进阶与挑战 (Advanced)**：标有 3~5 星的题目涵盖了较复杂的归纳不变量推导（如红黑树平衡、强规范化 Tait 引理），适合深入钻研。
- **互动证明**：每道习题均在源码中以 `sorry` 占位，并附带针对性的测试用例或引理，做题时替换 `sorry` 并保持 `lake build` 零警告即代表证明通过！

---

## 📜 开源协议与致谢

本重制项目代码与中文导读基于 **MIT License** 开源。原版《Software Foundations》系列教材版权属于 Benjamin C. Pierce, Arthur Azevedo de Amorim, Chris Casinghino, Marco Gaboardi, Michael Greenberg, Cătălin Hriţcu, Vilhelm Sjöberg, Brent Yorgey 等原作者。

感谢开源社区对形式化方法与 Lean 4 生态的无私贡献！

</div>
