---
title: "Lists: 结构化数据：列表、数据对与多态偏映射"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)
## 第三章：结构化数据与列表 (Lists: Working with Structured Data)

在前面两章《基础》(Basics) 与《归纳》(Induction) 中，我们已经熟悉了基本的函数式编程思想，
并探索了全称量词引入、自反性化简、等式重写与皮亚诺自然数上的数学归纳法。
然而，迄今为止我们处理的数据结构要么是有限枚举（如 `Day`、`Bool`），要么是简单的一进制数值（`Nat`）。

在现实世界的程序设计与形式化建模中，我们几乎不可避免地需要处理**复合与归纳数据类型**。
本章将从形式化依赖类型论的底层出发，从零构建两种最具代表性的结构化数据：
1. **数对 (Pairs of Numbers)**：最简单非递归多字段归纳类型，探索投影与满射配对；
2. **自然数列表 (Lists of Numbers)**：经典的单向链表结构，定义拼接、翻转等核心算法；
3. **基于列表的多重集 (Bags via Lists)**：利用列表对数学上的多重集（Multiset）进行建模；
4. **列表上的推理与结构归纳法 (Reasoning About Lists)**：掌握对递归数据结构的归纳证明，学会归纳假设的泛化；
5. **可选类型 (Options)**：为具有潜在“计算失败 / 越界”的偏函数提供类型安全封装；
6. **偏映射数据结构 (Partial Maps)**：构建形式化验证中最核心的基础设施——符号键值字典。

```lean
namespace NatList

/- ================================================================== -/
```

## 1. 数对 (Pairs of Numbers)

```lean
/- ================================================================== -/
```

在 `inductive` 类型声明中，每一个构造子（Constructor）都可以接收任意数量的参数：
- 可以是零个参数（例如布尔构造子 `true`、`false` 与自然数基底 `0`）；
- 可以是一个参数（例如自然数后继构造子 `succ`）；
- 也可以是多个参数（例如我们在第一章定义的四位半字节 `nybble`，以及接下来的数对类型）：

```lean
/-- 自然数数对：由两个自然数构成的有序二元组。
    该声明阐明：构造一个数对的唯一方式就是将构造子 `pair` 作用于两个 `Nat` 类型的参数上。 -/
inductive natprod where
  | pair (n1 n2 : Nat)
  deriving Repr, DecidableEq

open natprod

#check (natprod.pair 3 5)
-- 输出: natprod.pair 3 5 : natprod
```

我们可以通过模式匹配（Pattern Matching）编写从数对中提取第一分量与第二分量的投影函数：

```lean
/-- 提取数对的第一分量 -/
def fst (p : natprod) : Nat :=
  match p with
  | pair x _ => x

/-- 提取数对的第二分量 -/
def snd (p : natprod) : Nat :=
  match p with
  | pair _ y => y

#eval fst (pair 3 5)
-- 输出: 3
```

### 1.1 数对的记号表示 (Notation for Pairs)

由于数对在形式化世界中极其常用，直接写 `pair x y` 显得繁冗。
我们更习惯使用标准的数学记号 `(x, y)`。
在 Lean 4 中，标准库已将纯圆括号 `(x, y)` 用于原生积类型 `Prod`；为避免语法歧义，
我们引入专门的下标角标记号 `(x, y)ₚ`：

```lean
/-- 为自定义数对引入下标注号记号 `(x, y)ₚ` -/
scoped notation "(" x ", " y ")ₚ" => natprod.pair x y

#eval fst (3, 5)ₚ
-- 输出: 3

/-- 使用模式匹配定义的提取第一分量函数 -/
def fst' (p : natprod) : Nat :=
  match p with
  | (x, _)ₚ => x

/-- 使用模式匹配定义的提取第二分量函数 -/
def snd' (p : natprod) : Nat :=
  match p with
  | (_, y)ₚ => y

/-- 交换数对中的两个元素 -/
def swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y)ₚ => (y, x)ₚ
```

💡 **语法细微差别提醒**：
对数对进行模式匹配时带有括号 `(x, y)ₚ`；这不要与我们在 `Basics` 中见过的多参数并行模式匹配 `match n, m with` 相混淆。
前者匹配的是单一的复合数对值，后者则是同时对两个独立参数进行多维解构。

### 1.2 满射配对性质与分类讨论

```lean
/-- 如果以稍微偏向计算的方式陈述数对性质，直接使用自反性 `rfl` 即可完成证明： -/
theorem surjective_pairing' (n m : Nat) :
    (n, m)ₚ = (fst (n, m)ₚ, snd (n, m)ₚ)ₚ := by
  rfl

/-- 首次尝试：但如果我们以更自然的抽象形式陈述该引理，直接化简便无法推进！
    因为 p 是一个未知的抽象数对，内核在不知道 p 内部具体形式前无法对 `fst p` 展开模式匹配。
    在原版 Coq 中此定理以 `Abort` 放弃；在 Lean 4 中我们使用 `sorry` 说明此受阻尝试。 -/
theorem surjective_pairing_stuck (p : natprod) :
    p = (fst p, snd p)ₚ := by
  -- rfl 无法闭合，因为 fst p 和 snd p 无法继续化简
  sorry

/-- 满射配对定理（Surjective Pairing）：
    通过对 p 进行分类讨论（`cases`），暴露出数对的具体归纳构造，等式两边即可顺利化简判定一致！ -/
theorem surjective_pairing (p : natprod) :
    p = (fst p, snd p)ₚ := by
  cases p with
  | pair n m =>
    -- 此时 p 已被具体化为 (n, m)ₚ，fst 与 snd 自然展开
    rfl
```

### 🎯 练习：`snd_fst_is_swap` <Badge type="tip" text="1 星，标准" />

请证明：先分别提取数对的两分量再反向重构，与直接调用 `swap_pair` 的结果恒等。

```lean
theorem snd_fst_is_swap (p : natprod) :
    (snd p, fst p)ₚ = swap_pair p := by
  sorry
```

### 🎯 练习：`fst_swap_is_snd` <Badge type="tip" text="1 星，标准，可选" />

请证明：先对数对调用 `swap_pair` 再取第一分量，恒等于直接取原始数对的第二分量。

```lean
theorem fst_swap_is_snd (p : natprod) :
    fst (swap_pair p) = snd p := by
  sorry


/- ================================================================== -/
```

## 2. 自然数列表 (Lists of Numbers)

```lean
/- ================================================================== -/
```

推广数对的思想，我们可以定义由任意数量的自然数依序构成的**列表（List）**：
“一个列表要么是空列表（`nil`），要么是一个数值与另一个已有列表构成的有序对（`cons`）。”

```lean
/-- 自定义自然数单向链表 -/
inductive natlist where
  | nil : natlist
  | cons (n : Nat) (l : natlist) : natlist
  deriving Repr, DecidableEq

/-- 构造一个包含 1、2、3 三个元素的基础列表 -/
def mylist := natlist.cons 1 (natlist.cons 2 (natlist.cons 3 natlist.nil))
```

### 2.1 列表的中缀与方括号记号

在日常编程中，频繁书写 `cons` 和 `nil` 极其繁琐。
我们引入右结合的中缀构造子 `::`，并借助 Lean 4 强大的宏系统支持用分号隔开的方括号字面量 `[x; y; z]`：

```lean
open Lean

scoped infixr:67 " :: " => natlist.cons

syntax (name := natlist_semi) "[" sepBy(term, ";") "]" : term

macro_rules (kind := natlist_semi)
  | `([ ]) => `(natlist.nil)
  | `([ $x ]) => `(natlist.cons $x natlist.nil)
  | `([ $x; $xs;* ]) => `(natlist.cons $x [ $xs;* ])

/-- 以下三种书写方式完全等价 -/
def mylist1 : natlist := 1 :: (2 :: (3 :: []))
def mylist2 : natlist := 1 :: 2 :: 3 :: []
def mylist3 : natlist := [1; 2; 3]

#check mylist3
-- 输出: mylist3 : natlist
```

### 2.2 基础列表操作函数：repeat、length、app、hd、tl

```lean
/-- 重复生成指定数量的特定元素：`repeat n count` 生成包含 `count` 个 `n` 的列表 -/
def «repeat» (n count : Nat) : natlist :=
  match count with
  | 0          => []
  | count' + 1 => n :: («repeat» n count')

/-- 计算列表长度 -/
def length (l : natlist) : Nat :=
  match l with
  | []     => 0
  | _ :: t => (length t) + 1

/-- 列表拼接函数（Append）：将列表 l2 连接在 l1 的尾部 -/
def app (l1 l2 : natlist) : natlist :=
  match l1 with
  | []     => l2
  | h :: t => h :: (app t l2)

/-- 为列表拼接定义常用中缀记号 `++` -/
scoped infixr:60 " ++ " => app

theorem test_app1 : [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5] := by rfl
theorem test_app2 : [] ++ [4; 5] = [4; 5] := by rfl
theorem test_app3 : [1; 2; 3] ++ [] = [1; 2; 3] := by rfl

/-- 取出列表的表头元素；若列表为空则返回给定的默认值 `default` -/
def hd (default : Nat) (l : natlist) : Nat :=
  match l with
  | []     => default
  | h :: _ => h

/-- 取出列表除表头外的尾部列表；若列表为空则返回空列表 -/
def tl (l : natlist) : natlist :=
  match l with
  | []     => []
  | _ :: t => t

theorem test_hd1 : hd 0 [1; 2; 3] = 1 := by rfl
theorem test_hd2 : hd 0 [] = 0 := by rfl
theorem test_tl  : tl [1; 2; 3] = [2; 3] := by rfl


/- ================================================================== -/
```

## 3. 列表操作函数综合练习 (List Exercises)

```lean
/- ================================================================== -/
```

### 🎯 练习：`list_funs` <Badge type="info" text="2 星，标准，特别有用" />

请完成下列关于自然数列表的三个函数定义：
1. `nonzeros`：过滤掉列表中所有为 `0` 的项；
2. `oddmembers`：仅保留列表中的所有奇数；
3. `countoddmembers`：统计列表中奇数的总数（鼓励直接结合 `length` 与 `oddmembers` 实现）。

```lean
/-- 移除列表中的所有 0 -/
def nonzeros (l : natlist) : natlist :=
  match l with
  | []     => []
  | 0 :: t => nonzeros t
  | n :: t => n :: nonzeros t

theorem test_nonzeros : nonzeros [0; 1; 0; 2; 3; 0; 0] = [1; 2; 3] := by rfl

/-- 仅提取列表中的奇数项 -/
def oddmembers (l : natlist) : natlist :=
  match l with
  | []     => []
  | n :: t => if odd n then n :: oddmembers t else oddmembers t

theorem test_oddmembers : oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3] := by rfl

/-- 统计奇数元素个数 -/
def countoddmembers (l : natlist) : Nat :=
  length (oddmembers l)

theorem test_countoddmembers1 : countoddmembers [1; 0; 3; 1; 4; 5] = 4 := by rfl
theorem test_countoddmembers2 : countoddmembers [0; 2; 4] = 0 := by rfl
theorem test_countoddmembers3 : countoddmembers [] = 0 := by rfl
```

### 🎯 练习：`alternate` <Badge type="warning" text="3 星，进阶" />

请定义交替穿插函数 `alternate`：交替从两个列表中各取一个元素合并为一个新列表。
例如 `alternate [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6]`。
如果其中一个列表较长，剩余元素原样追加到尾部。

```lean
/-- 双列表交替穿插 -/
def alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2

theorem test_alternate1 : alternate [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6] := by rfl
theorem test_alternate2 : alternate [1] [4; 5; 6] = [1; 4; 5; 6] := by rfl
theorem test_alternate3 : alternate [1; 2; 3] [4] = [1; 4; 2; 3] := by rfl
theorem test_alternate4 : alternate [] [20; 30] = [20; 30] := by rfl


/- ================================================================== -/
```

## 4. 基于列表的多重集 (Bags via Lists)

```lean
/- ================================================================== -/
```

多重集（Bag / Multiset）类似于集合，但允许同一个元素重复出现多次。
我们可以直接把自然数列表 `natlist` 作为多重集的一种直观具体表征：

```lean
def bag := natlist
```

### 🎯 练习：`bag_functions` <Badge type="warning" text="3 星，标准，特别有用" />

请完成多重集的核心操作函数：
- `count`：统计某个数值在多重集中出现的频次；
- `sum`：合并两个多重集（相当于列表拼接）；
- `add`：向多重集中插入一个元素；
- `member`：检验某个数值是否在多重集中出现至少一次。

```lean
/-- 统计数值 v 在多重集 s 中的出现次数 -/
def count (v : Nat) (s : bag) : Nat :=
  match s with
  | []      => 0
  | n :: s' => if v =? n then (count v s') + 1 else count v s'

theorem test_count1 : count 1 [1; 2; 3; 1; 4; 1] = 3 := by rfl
theorem test_count2 : count 6 [1; 2; 3; 1; 4; 1] = 0 := by rfl

/-- 多重集的合并（求和）：直接使用底层列表拼接 `app` -/
def sum : bag → bag → bag := app

theorem test_sum1 : count 1 (sum [1; 2; 3] [1; 4; 1]) = 3 := by rfl

/-- 向多重集中加入单个元素 -/
def add (v : Nat) (s : bag) : bag := v :: s

theorem test_add1 : count 1 (add 1 [1; 4; 1]) = 3 := by rfl
theorem test_add2 : count 5 (add 1 [1; 4; 1]) = 0 := by rfl

/-- 判断元素是否属于多重集 -/
def member (v : Nat) (s : bag) : Bool :=
  !((count v s) =? 0)

theorem test_member1 : member 1 [1; 4; 1] = true := by rfl
theorem test_member2 : member 2 [1; 4; 1] = false := by rfl
```

### 🎯 练习：`bag_more_functions` <Badge type="warning" text="3 星，标准，可选" />

实现更多多重集操作函数：
- `remove_one`：从多重集中删除某个元素的一个副本（若不存在则原样返回）；
- `remove_all`：删除某个元素的所有副本；
- `included`：多重集包含判断（子集检验）。

```lean
/-- 移除多重集中指定元素的一个副本 -/
def remove_one (v : Nat) (s : bag) : bag :=
  match s with
  | []      => []
  | n :: s' => if n =? v then s' else n :: remove_one v s'

theorem test_remove_one1 : count 5 (remove_one 5 [2; 1; 5; 4; 1]) = 0 := by rfl
theorem test_remove_one2 : count 5 (remove_one 5 [2; 1; 4; 1]) = 0 := by rfl
theorem test_remove_one3 : count 4 (remove_one 5 [2; 1; 4; 5; 1; 4]) = 2 := by rfl
theorem test_remove_one4 : count 5 (remove_one 5 [2; 1; 5; 4; 5; 1; 4]) = 1 := by rfl

/-- 移除多重集中指定元素的所有副本 -/
def remove_all (v : Nat) (s : bag) : bag :=
  match s with
  | []      => []
  | n :: s' => if n =? v then remove_all v s' else n :: remove_all v s'

theorem test_remove_all1 : count 5 (remove_all 5 [2; 1; 5; 4; 1]) = 0 := by rfl
theorem test_remove_all2 : count 5 (remove_all 5 [2; 1; 4; 1]) = 0 := by rfl
theorem test_remove_all3 : count 4 (remove_all 5 [2; 1; 4; 5; 1; 4]) = 2 := by rfl
theorem test_remove_all4 : count 5 (remove_all 5 [2; 1; 5; 4; 5; 1; 4]) = 0 := by rfl

/-- 多重集包含判断：s1 的所有元素是否都在 s2 中出现足够的频次 -/
def included (s1 s2 : bag) : Bool :=
  match s1 with
  | []       => true
  | n :: s1' => if member n s2 then included s1' (remove_one n s2) else false

theorem test_included1 : included [1; 2] [2; 1; 4; 1] = true := by rfl
theorem test_included2 : included [1; 2; 2] [2; 1; 4; 1] = false := by rfl
```

### 🎯 练习：`add_inc_count` <Badge type="info" text="2 星，标准，特别有用" />

证明定理：向多重集 `s` 中添加数值 `c`，会使 `c` 的计数精准增加 1。

```lean
theorem add_inc_count (c : Nat) (s : bag) :
    count c (add c s) = (count c s) + 1 := by
  sorry

/-- 自动评分占位定义 -/
def manual_grade_for_add_inc_count : Option (Nat × String) := none


/- ================================================================== -/
```

## 5. 列表上的推理与数学归纳法 (Reasoning About Lists)

```lean
/- ================================================================== -/
```

与处理数值类似，关于列表函数的简单性质有时仅通过定义化简就能直接得证。
例如空列表左拼接恒等定理：

```lean
theorem nil_app (l : natlist) : [] ++ l = l := by
  rfl

/-- 表头截断后列表长度减 1：使用分类讨论 `cases` 分别核查空列表与非空列表 -/
theorem tl_length_pred (l : natlist) :
    Nat.pred (length l) = length (tl l) := by
  cases l with
  | nil => rfl
  | cons n l' => rfl
```

### 列表归纳原理 (Induction on Lists)

对于涉及任意长度列表的普遍定理，单纯靠分类讨论往往不够，我们需要使用**列表归纳法**：
1. **基底情形 (Base Case)**：证明命题对空列表 `[]` 成立；
2. **归纳步骤 (Inductive Step)**：假设命题对较短列表 `l'` 成立（归纳假设 `ih`），证明命题对任意前缀扩充 `n :: l'` 依然成立。

```lean
/-- 列表拼接结合律：(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) -/
theorem app_assoc (l1 l2 l3 : natlist) :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil => rfl
  | cons n l1' ih =>
    dsimp [app]
    rw [ih]
```

### 5.1 归纳命题的泛化 (Generalizing Statements)

```lean
/-- 首次尝试：如果我们尝试直接归纳证明特化的命题 `repeat n c ++ repeat n c = repeat n (c + c)`，
    归纳假设仅仅适用于完全相同的第二个参数，无法处理后继展开后的加法形式，证明陷入停滞！
    原版 Coq 使用 `Abort` 说明；在 Lean 4 中以 `sorry` 演示该卡住状态。 -/
theorem repeat_double_firsttry (c n : Nat) :
    («repeat» n c) ++ («repeat» n c) = «repeat» n (c + c) := by
  sorry

/-- 泛化版本：通过将第二个参数泛化为任意独立的 `c2`，归纳假设变得更加强大通用，证明自然迎刃而解！ -/
theorem repeat_plus (c1 c2 n : Nat) :
    («repeat» n c1) ++ («repeat» n c2) = «repeat» n (c1 + c2) := by
  induction c1 with
  | zero =>
    dsimp [«repeat», app]
    rw [Nat.zero_add]
  | succ c1' ih =>
    dsimp [«repeat», app]
    rw [ih]
    have h : c1' + 1 + c2 = (c1' + c2) + 1 := by omega
    rw [h]
    dsimp [«repeat»]
```

### 5.2 列表翻转 (Reversing a List)

```lean
/-- 递归定义列表翻转函数 -/
def rev (l : natlist) : natlist :=
  match l with
  | []     => []
  | h :: t => rev t ++ [h]

theorem test_rev1 : rev [1; 2; 3] = [3; 2; 1] := by rfl
theorem test_rev2 : rev natlist.nil = natlist.nil := by rfl

/-- 翻转保长首次尝试：直接对翻转保长进行归纳，由于缺少拼接与长度关系的引理，在归纳步卡住。 -/
theorem rev_length_firsttry (l : natlist) :
    length (rev l) = length l := by
  sorry

/-- 尝试证明翻转列表末尾追加单元素的保长性质，由于特化为 rev l，归纳假设无法闭合。 -/
theorem app_rev_length_S_firsttry (l : natlist) (n : Nat) :
    length (rev l ++ [n]) = (length (rev l)) + 1 := by
  sorry

/-- 泛化到任意列表追加单元素：长度必然加 1。 -/
theorem app_length_S (l : natlist) (n : Nat) :
    length (l ++ [n]) = (length l) + 1 := by
  induction l with
  | nil => rfl
  | cons m l' ih =>
    dsimp [app, length]
    rw [ih]

/-- 最强泛化引理：任意两列表拼接后的长度等于各自分别计算的长度之和。 -/
theorem app_length (l1 l2 : natlist) :
    length (l1 ++ l2) = (length l1) + (length l2) := by
  induction l1 with
  | nil =>
    dsimp [app, length]
    rw [Nat.zero_add]
  | cons n l1' ih =>
    dsimp [app, length]
    rw [ih]
    omega

/-- 最终翻转保长定理：利用已证明的 app_length 引理顺利得证！ -/
theorem rev_length (l : natlist) :
    length (rev l) = length l := by
  induction l with
  | nil => rfl
  | cons n l' ih =>
    dsimp [rev, length]
    rw [app_length]
    dsimp [length]
    rw [ih]


/- ================================================================== -/
```

## 6. 列表形式化练习题 (List Exercises)

```lean
/- ================================================================== -/
```

### 6.1 第一部分练习题 (List Exercises, Part 1)

### 🎯 练习：`list_exercises` <Badge type="warning" text="3 星，标准" />

包含以下五个列表核心定理：
1. `app_nil_r`：列表与空列表右拼接恒等于自身；
2. `rev_app_distr`：翻转在拼接上的分配律（`rev (l1 ++ l2) = rev l2 ++ rev l1`）；
3. `rev_involutive`：翻转操作是对合的（两次翻转等于自身）；
4. `app_assoc4`：四个列表的连续拼接结合律；
5. `nonzeros_app`：`nonzeros` 在列表拼接上的分配性。

```lean
theorem app_nil_r (l : natlist) : l ++ [] = l := by
  sorry

theorem rev_app_distr (l1 l2 : natlist) :
    rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  sorry

/-- 对合函数（Involution）：连续应用两次等价于恒等映射。 -/
theorem rev_involutive (l : natlist) :
    rev (rev l) = l := by
  sorry

theorem app_assoc4 (l1 l2 l3 l4 : natlist) :
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by
  sorry

theorem nonzeros_app (l1 l2 : natlist) :
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2) := by
  sorry
```

### 🎯 练习：`eqblist` <Badge type="info" text="2 星，标准" />

请完成自然数列表可判定判等函数 `eqblist`，并证明其自反性 `eqblist_refl`。

```lean
def eqblist (l1 l2 : natlist) : Bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => (h1 =? h2) && eqblist t1 t2
  | _, _ => false

theorem test_eqblist1 : eqblist [] [] = true := by rfl
theorem test_eqblist2 : eqblist [1; 2; 3] [1; 2; 3] = true := by rfl
theorem test_eqblist3 : eqblist [1; 2; 3] [1; 2; 4] = false := by rfl

theorem eqblist_refl (l : natlist) : eqblist l l = true := by
  sorry
```

### 6.2 第二部分练习题 (List Exercises, Part 2)

### 🎯 练习：`count_member_nonzero` <Badge type="tip" text="1 星，标准" />

证明：如果列表中包含元素 1，那么在其中计数 1 的结果至少为 1（即 $1 \le \text{count } 1\ (1 :: s)$ 为真）。

```lean
theorem count_member_nonzero (s : bag) :
    (1 <=? (count 1 (1 :: s))) = true := by
  sorry

/-- 自然数小于等于后继引理：n <=? n + 1 恒为 true。 -/
theorem leb_n_Sn (n : Nat) : (leb n (n + 1)) = true := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    exact ih
```

### 🎯 练习：`remove_does_not_increase_count` <Badge type="warning" text="3 星，进阶" />

证明：从多重集中移除元素 0 不会增加 0 的计数。
提示：对 s 进行归纳，并结合引理 `leb_n_Sn`。

```lean
theorem remove_does_not_increase_count (s : bag) :
    (count 0 (remove_one 0 s) <=? count 0 s) = true := by
  sorry
```

### 🎯 练习：`bag_count_sum` <Badge type="warning" text="3 星，标准，可选" />

证明关于多重集并集与其元素计数的分配律：
对任意多重集 `s1`、`s2` 与自然数 `n`，`count n (sum s1 s2) = count n s1 + count n s2`。

```lean
theorem bag_count_sum (s1 s2 : bag) (n : Nat) :
    count n (sum s1 s2) = (count n s1) + (count n s2) := by
  sorry
```

### 🎯 练习：`involution_injective` <Badge type="warning" text="3 星，进阶" />

证明：任何对合函数（满足 $\forall n, f (f\ n) = n$）必然是单射的（Injective）。

```lean
theorem involution_injective (f : Nat → Nat)
    (h_inv : ∀ n : Nat, n = f (f n)) :
    ∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2 := by
  sorry
```

### 🎯 练习：`rev_injective` <Badge type="info" text="2 星，进阶" />

利用翻转的对合性质（`rev_involutive`）直接证明 `rev` 是单射函数。
提示：无需对列表使用归纳法，复用 `involution_injective` 的证明思路即可！

```lean
theorem rev_injective (l1 l2 : natlist) :
    rev l1 = rev l2 → l1 = l2 := by
  sorry


/- ================================================================== -/
```

## 7. 可选类型 (Options)

```lean
/- ================================================================== -/
```

假设我们需要编写一个函数返回列表的第 n 个元素。
如果该函数的签名是 `Nat → natlist → Nat`，那么当列表长度不足时我们必须返回一个随意的“魔数”（例如 42）：

```lean
def nth_bad (l : natlist) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' => match n with
    | 0 => a
    | n' + 1 => nth_bad l' n'
```

这种处理异常的方法极不安全。现代函数式编程采用可选类型（Option Type）：
计算成功时返回 `.Some n`，越界或失败时返回 `.None`。

```lean
/-- 可选自然数类型：用于安全表示可能失败的计算结果 -/
inductive natoption where
  | Some (n : Nat) : natoption
  | None : natoption
  deriving Repr, DecidableEq

def nth_error (l : natlist) (n : Nat) : natoption :=
  match l with
  | [] => .None
  | a :: l' => match n with
    | 0 => .Some a
    | n' + 1 => nth_error l' n'

theorem test_nth_error1 : nth_error [4; 5; 6; 7] 0 = .Some 4 := by rfl
theorem test_nth_error2 : nth_error [4; 5; 6; 7] 3 = .Some 7 := by rfl
theorem test_nth_error3 : nth_error [4; 5; 6; 7] 9 = .None := by rfl

/-- 解构可选类型：有值时返回其内含值，为 None 时返回默认值 `default` -/
def option_elim (d : Nat) (o : natoption) : Nat :=
  match o with
  | .Some n' => n'
  | .None => d
```

### 🎯 练习：`hd_error` <Badge type="info" text="2 星，标准" />

定义一个类型安全的表头提取函数 `hd_error`：当列表非空时返回 `.Some h`，空列表时返回 `.None`。

```lean
def hd_error (l : natlist) : natoption :=
  match l with
  | []     => .None
  | h :: _ => .Some h

theorem test_hd_error1 : hd_error [] = .None := by rfl
theorem test_hd_error2 : hd_error [1] = .Some 1 := by rfl
theorem test_hd_error3 : hd_error [5; 6] = .Some 5 := by rfl
```

### 🎯 练习：`option_elim_hd` <Badge type="tip" text="1 星，标准，可选" />

请证明：带默认值的旧函数 `hd default l` 恒等同于先取 `hd_error l` 再通过 `option_elim default` 解包的结果。

```lean
theorem option_elim_hd (l : natlist) (default : Nat) :
    hd default l = option_elim default (hd_error l) := by
  sorry

end NatList


/- ================================================================== -/
```

## 8. 偏映射数据结构 (Partial Maps)

```lean
/- ================================================================== -/
```

作为本章数据结构形式化建模的压轴案例，我们来构造一个**偏映射（Partial Map）**类型。
它在功能上类似于主流编程语言中的字典（Dictionary）或哈希映射（Map），
将唯一的键（Key）关联到对应的值（Value）。

```lean
namespace PartialMap

open NatList

/-- 键标识符类型：将自然数封装在 Id 标签中 -/
inductive id where
  | Id (n : Nat)
  deriving Repr, DecidableEq

/-- 检验两个标识符是否相等 -/
def eqb_id (x1 x2 : id) : Bool :=
  match x1, x2 with
  | .Id n1, .Id n2 => n1 =? n2
```

### 🎯 练习：`eqb_id_refl` <Badge type="tip" text="1 星，标准" />

证明 `eqb_id` 的自反性：任何标识符与自身比较恒为 `true`。
提示：使用前一章证明过的引理 `eqb_refl`。

```lean
theorem eqb_id_refl (x : id) : eqb_id x x = true := by
  sorry

/-- 偏映射数据结构：关联列表（Association List）模型 -/
inductive partial_map where
  | empty : partial_map
  | record (i : id) (v : Nat) (m : partial_map) : partial_map
  deriving Repr, DecidableEq

/-- 更新或插入键值对：新的映射项直接置于最前端，实现遮蔽（Shadowing）语义 -/
def update (d : partial_map) (x : id) (value : Nat) : partial_map :=
  .record x value d

/-- 根据键检索对应的值：若键不存在则返回 None -/
def find (x : id) (d : partial_map) : natoption :=
  match d with
  | .empty => .None
  | .record y v d' => if eqb_id x y then .Some v else find x d'
```

### 🎯 练习：`update_eq` <Badge type="tip" text="1 星，标准" />

证明：向偏映射中插入键 `x` 与值 `v` 后，立即查找 `x` 必然成功返回 `.Some v`。

```lean
theorem update_eq (d : partial_map) (x : id) (v : Nat) :
    find x (update d x v) = .Some v := by
  sorry
```

### 🎯 练习：`update_neq` <Badge type="tip" text="1 星，标准" />

证明：当更新的键 `y` 与查询的键 `x` 不同（`eqb_id x y = false`）时，更新操作不会改变对 `x` 的查询结果。

```lean
theorem update_neq (d : partial_map) (x y : id) (o : Nat)
    (h : eqb_id x y = false) : find x (update d y o) = find x d := by
  sorry

end PartialMap
```
