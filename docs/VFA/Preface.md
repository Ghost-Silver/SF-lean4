---
title: "Preface: 全书前言：算法形式化验证路线图"
---

# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 前言 (Preface)

欢迎阅读《软件基础》第三卷：**函数式算法验证 (Verified Functional Algorithms, 简称 VFA)**！

---

## 1. 欢迎来到算法形式化验证的世界 (Welcome)

在现代计算机科学与软件工程中，构建**经过形式化数学验证、证明绝无缺陷的高可靠软件**通常遵循如下范式：
1. **在具备优秀证明理论的表达性高级语言中编写程序**（在 Coq 中是 Gallina，在 Lean 4 中是其原生纯函数式核心语言）；
2. **在定理证明器中形式化证明其功能正确性 (Correctness Proof)**；
3. **通过优化编译器（如 Lean 4 原生 AOT 编译或 OCaml 抽取）生成高效的本地机器码**。

由于现实工程对软件的运行效率有极致要求，我们必须实现复杂的高性能数据结构与经典算法（如二叉搜索树、红黑树平衡旋转、二项堆优先队列、图着色算法等）。
而在 Lean 4 这样的纯函数式语言中，不可变数据结构上的算法（Purely Functional Data Structures & Algorithms）拥有无与伦比的数学确定性与结构归纳优势。

在本卷中，你将系统学习如何**规范规约（Specification）**并**形式化证明（Verification）**一系列经典的计算机科学核心算法：
- **排序算法族**：插入排序（Insertion Sort）、选择排序（Selection Sort）、归并排序（Merge Sort）；
- **置换与多重集理论**：列表置换关系（Permutation）、基于内容的多重集等价（Multisets）、包置换（Bags）；
- **查找表与二叉搜索树**：二叉查找树（BST）、抽象数据类型不变量（ADT Invariants）、前缀树（Tries）；
- **平衡树机制**：红黑树（Red-Black Trees）的着色平衡性与旋转保持；
- **高效优先队列**：二叉堆（Heaps）、二项堆（Binomial Queues）；
- **决策过程与反射**：可判定性自动化策略（Decide）；
- **高阶实战**：编译器寄存器分配中的 Kempe 启发式图着色算法（Graph Coloring）。

在阅读本书之前，读者宜具备本科层次的数据结构与算法基础知识，并已熟悉第一卷《逻辑基础》(Logical Foundations - LF) 中的核心内容。
本卷建立在第一卷《逻辑基础》之上，独立于第二卷《程序语言基础》(PLF)。

---

## 2. 章节依赖路线图 (Chapter Dependencies)

在学习本卷前，建议先掌握第一卷《逻辑基础》的核心章节：
`Preface`, `Basics`, `Induction`, `Lists`, `Poly`, `Tactics`, `Logic`, `IndProp`, `Maps`，以及 `ProofObjects` 与 `IndPrinciples`。

在本卷内部，核心必读路线为：

```
[Preface] ──> [Perm] ──> [Sort] ──> [SearchTree] ──> [Extract] ──> [Redblack]
```

各进阶选读分支路线如下：
- **分支 1（高级排序与规约对比）**：`[Sort] ──> [Multiset]` 或 `[Selection]` 或 `[Decide]`
- **分支 2（抽象数据类型与表示不变量）**：`[SearchTree] ──> [ADT]`
- **分支 3（前缀字典与位操作）**：`[Perm] ──> [Trie]`
- **分支 4（优先队列与高级堆结构）**：`[Sort] ──> [Selection] ──> [SearchTree] ──> [ADT] ──> [Priqueue] ──> [Binom]`
- **高阶专题（图着色寄存器分配）**：`[Color]`（包含完整的图论形式化与编译器后端寄存器分配验证，建议在完成前述基础章节后攻坚）。

---

## 3. 习题与星级标准 (Exercises & Grading)

本卷每章均配有丰富的形式化练习题，星级标准如下：
- **1 星（⭐）**：基础概念题，加深对正文定义与简单引理的理解（1-2 分钟）；
- **2 星（⭐⭐）**：标准练习题，涉及直接的归纳证明或辅助引理调用（5-10 分钟）；
- **3 星（⭐⭐⭐）**：进阶思考题，需要构思关键循环/归纳不变量或拆分复杂分支（15-30 分钟）；
- **4 星与 5 星（⭐⭐⭐⭐ / ⭐⭐⭐⭐⭐）**：高难度挑战题与大定理，涵盖完整的数据结构健全性与同构证明（半小时以上）。

所有习题均以 `sorry` 作为占位符留待读者亲自实战填写。当 Infoview 提示 `No goals` 时即代表该题证明通过！

```lean
namespace VFA.Preface

/-- 第三卷函数式算法验证卷首导言已就绪 -/
def vfa_preface_ready : Bool := true

theorem vfa_preface_ready_theorem : vfa_preface_ready = true := by
  rfl

end VFA.Preface
```
