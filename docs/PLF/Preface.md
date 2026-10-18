---
title: "Preface: 前言：课程指引与 PLF 路线图"
---

# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 前言 (Preface)

### 欢迎来到第二卷

本书系统探讨了程序与程序设计语言数学研究的核心概念。
涵盖的主题包括：
- 交互式证明助理的高阶应用；
- 操作语义（大步语义与小步语义）；
- 霍尔逻辑（Hoare Logic）与程序验证；
- 静态类型系统（简单类型 Lambda 演算、子类型化、规范化等）。

本书面向广大读者，无论是高年级本科生、研究生还是形式化方法的研究人员均能从中获益。
我们不预设任何逻辑学或程序语言理论的高深背景，但具备一定的数学成熟度（Mathematical Maturity）将大有裨益。

与《软件基础》全系列图书一致，本书**百分之百形式化且由机器检验**：
全书的所有正文叙述与代码均直接嵌入在 Lean 4 证明脚本中。
学习本书的最佳方式是在交互式 Lean 4 环境中，伴随着实时目标查看器（Infoview）一步步跟随推导。

本书建立在第一卷《逻辑基础》（*Logical Foundations*, LF）的基础之上。
它与第一卷共同构成了一门完整的程序语言理论课程。

---

### 全卷架构与核心主线

本书围绕两大核心概念主线展开：

1. **针对特定程序性质的形式化推理 (Program Verification)**：
   - 证明具体程序是否满足特定形式化规范（例如：编译器优化是否保真、排序算法是否正确）；
   - 形式化工具包括：**抽象语法**、**操作语义（大步语义与小步语义）**、**程序等价性（Behavioral Equivalence）** 以及 **霍尔逻辑（Hoare Logic）**。

2. **建立语言全局安全保证的类型系统 (Type Systems)**：
   - 为给定语言中的*所有*程序建立运行期“行为良好”的全局保证（例如：良类型的程序在运行时绝不崩溃或陷入非法状态）；
   - 类型系统是轻量级形式化方法中最成熟、最普及的技术代表，广泛应用于现代编程语言与工业级工具链中；
   - 本书以**简单类型 Lambda 演算 (STLC)** 为核心模型，全面探讨进展性（Progress）、类型保持性（Preservation）、类型检查算法、记录与子类型化（Subtyping）。

---

### 推荐引用格式

```bibtex
@book{Pierce:SF2,
  author    = {Benjamin C. Pierce and
               Arthur Azevedo de Amorim and
               Chris Casinghino and
               Marco Gaboardi and
               Michael Greenberg and
               Cătălin Hriţcu and
               Vilhelm Sjöberg and
               Andrew Tolmach and
               Brent Yorgey},
  editor    = {Benjamin C. Pierce},
  title     = {Programming Language Foundations},
  series    = {Software Foundations},
  volume    = {2},
  year      = {2024},
  publisher = {Electronic textbook},
  note      = {Version 6.6}
}
```

---

### 做题建议与工作指引

1. **理解先于动笔**：在着手证明之前，务必先在草稿纸上梳理非形式化证明思路，或向同行用自然语言解释清楚“为什么这个定理为真”；
2. **充分利用自动化**：随着形式化规模的急剧扩大，完全的手工推导将异常冗长。善于使用第一卷学到的组合子、免命名策略、`omega`、`congr`、`solve_by_elim` 与宏定义；
3. **保持编译通过**：在做题过程中随时保存并利用 Lean 4 编译器实时检查目标状态。

```lean
namespace PLF

/-- PLF 卷次元信息标记 -/
def volume_name : String := "Programming Language Foundations"

/-- PLF 卷次版本 -/
def volume_version : String := "6.6"

end PLF
```
