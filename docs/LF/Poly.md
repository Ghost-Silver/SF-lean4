---
title: "Poly: 多态与高阶函数：全称多态与 Church 数"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第四章：多态与高阶函数 (Poly: Polymorphism and Higher-Order Functions)

在上一章《结构化数据与列表》(Lists) 中，我们已经熟悉了如何定义并形式化推理复合数据类型（如数对 `natprod` 与自然数列表 `natlist`）。
然而，前一章的列表仅仅局限于存储单一的自然数元素。如果我们需要操作布尔值列表、列表的列表、或者其他任意数据类型的列表，
难道我们必须为每一种数据类型都机械地重新定义一套一模一样的列表类型和配套函数（`length`、`rev`、`app`）以及相关定理吗？

这显然是极其繁冗且不可接受的。为了避免代码与证明的死板重复，现代函数式编程语言与依赖类型论引入了两项至关重要的核心抽象：
1. **多态 (Polymorphism)**：将函数与归纳数据类型对数据所持有的“类型”本身进行抽象参数化；
2. **高阶函数 (Higher-Order Functions)**：将函数视为“一等公民数据”（First-Class Citizens），函数既可以作为参数传递给其他函数，也可以作为其他函数的计算结果返回。

本章我们将完整深入探讨这两项核心机制，并探索丘奇数（Church Numerals）——一种完全利用函数本身从零定义算术系统的精妙构造。

```lean
namespace Poly
```

## 1. 多态 (Polymorphism)

### 1.1 多态列表 (Polymorphic Lists)

在上一章中，我们处理的列表完全局限于包含自然数的列表。
显然，实际程序需要处理包含任意类型元素的列表——例如布尔值列表、列表的列表等。
我们*固然可以*为每一种类型单独定义一个专属的归纳类型，例如：

```lean
/-- 布尔值专用列表类型 -/
inductive boollist : Type where
  | bool_nil : boollist
  | bool_cons (b : Bool) (l : boollist) : boollist
  deriving Repr, DecidableEq
```

然而，这种做法很快就会变得难以维系：
不仅需要为每个类型发明不同的构造子名称，更致命的是，我们还需要为每种列表类型重新编写所有的列表处理函数
（如 `length`、`rev` 等）并重复证明它们的所有代数性质（如 `rev_length`、`app_assoc` 等）。

为了避免无休止的重复，Lean 4 支持**多态归纳类型定义**（Polymorphic Inductive Type Definitions）。
下面我们定义通用的多态列表类型 `list`：

```lean
/-- 多态列表类型：带有一个类型参数 `X : Type` 的归纳类型 -/
inductive list (X : Type) : Type where
  | nil : list X
  | cons (x : X) (l : list X) : list X
  deriving Repr, DecidableEq

open list
```

这个定义与上一章的 `natlist` 几乎完全相同，唯一关键的区别在于：
构造子 `cons` 原本固定的 `Nat` 参数被任意类型参数 `X` 所取代，类型签名的第一行增加了参数绑定 `(X : Type)`，
并且构造子类型签名中所有原本出现 `natlist` 的位置均被替换为了 `list X`。

那么类型构造子 `list` 本身究竟是什么呢？
在依赖类型论中，可以将 `list` 本身视为一个“从类型到归纳类型的函数”，简而言之，`list` 是一个函数 `Type → Type`：

```lean
#check list
-- 输出: list : Type → Type
```

在 Lean 4 中，归纳类型声明的参数 `X : Type` 会自动作为隐式参数绑定给构造子 `nil` 和 `cons`。
若我们需要显式指定类型实参，只需在构造子前添加前缀 `@` 即可，例如 `@nil Nat` 构造自然数空列表：

```lean
#check (@nil Nat)
-- 输出: nil : list Nat

#check (@cons Nat 3 (@nil Nat))
-- 输出: cons 3 nil : list Nat
```

构造子 `@nil` 与 `@cons` 的全称量化类型签名如下：

```lean
#check @nil
-- 输出: @nil : {X : Type} → list X

#check @cons
-- 输出: @cons : {X : Type} → X → list X → list X
```

有了多态列表，我们便可以编写各类多态列表处理函数。
首先来看通用的 `repeat` 函数（在 Lean 4 中，由于 `repeat` 是保留的战术关键字，我们使用法文引号 `«repeat»` 进行转义）：

```lean
/-- 多态重复构造函数：生成包含 `count` 个元素 `x` 的列表 -/
def «repeat» (X : Type) (x : X) (count : Nat) : list X :=
  match count with
  | 0 => @nil X
  | count' + 1 => @cons X x («repeat» X x count')

/-- 测试用例 1：重复构造自然数列表 -/
theorem test_repeat1 : «repeat» Nat 4 2 = @cons Nat 4 (@cons Nat 4 (@nil Nat)) := by
  rfl

/-- 测试用例 2：重复构造布尔值列表 -/
theorem test_repeat2 : «repeat» Bool false 1 = @cons Bool false (@nil Bool) := by
  rfl
```

### 🎯 练习：`mumble_grumble` <Badge type="info" text="2 星 · standard, optional" />

考虑如下两个归纳类型定义：

```lean
namespace MumbleGrumble

inductive mumble : Type where
  | a : mumble
  | b (x : mumble) (y : Nat) : mumble
  | c : mumble
  deriving Repr, DecidableEq

inductive grumble (X : Type) : Type where
  | d (m : mumble) : grumble X
  | e (x : X) : grumble X
  deriving Repr, DecidableEq

open mumble grumble
```

问：对于某个具体的类型 `X`，下列各项中哪些是良类型（Well-typed）的 `grumble X` 元素？
（请在注释中注明 YES 或 NO 并说明理由）：

1. `d (b a 5)`
   - 答案：YES（在 Lean 4 中若隐式参数 `X` 可由上下文推断，或者显式写为 `@d X (b a 5)`，它是良类型的 `grumble X`）。
2. `d mumble (b a 5)`
   - 答案：YES（在 Coq 中显式传参；在 Lean 4 中写作 `@d mumble (b a 5)`，其类型为 `grumble mumble`）。
3. `d bool (b a 5)`
   - 答案：YES（写作 `@d Bool (b a 5)`，其类型为 `grumble Bool`）。
4. `e bool true`
   - 答案：YES（写作 `@e Bool true`，其类型为 `grumble Bool`）。
5. `e mumble (b c 0)`
   - 答案：YES（写作 `@e mumble (b c 0)`，其类型为 `grumble mumble`）。
6. `e bool (b c 0)`
   - 答案：NO（`(b c 0)` 的类型是 `mumble`，无法作为类型为 `Bool` 的实参传给构造子 `e`）。
7. `c`
   - 答案：NO（`c` 的类型是 `mumble`，而不是 `grumble X`）。

```lean
#check (@d mumble (b a 5))
#check (@d Bool (b a 5))
#check (@e Bool true)
#check (@e mumble (b c 0))

end MumbleGrumble
```

### 1.2 类型注解推断 (Type Annotation Inference)

在 Coq 中，函数定义可以省略部分参数的显式类型注解，完全依赖函数体的双向类型推导。
而在现代 Lean 4 中，顶层声明的参数绑定器通常需要给出显式类型注解，以保证编译的高效与代码的可读性：

```lean
/-- 类型推断版本的 repeat 函数 -/
def «repeat'» (X : Type) (x : X) (count : Nat) : list X :=
  match count with
  | 0 => @nil X
  | count' + 1 => @cons X x («repeat'» X x count')

#check @«repeat'»
#check @«repeat»
```

### 1.3 类型实参综合与通配符 `_` (Type Argument Synthesis)

在调用多态函数时，每次都要显式传入类型参数 `X` 显得繁冗。
既然第二个实参 `x` 的类型就是 `X`，那么类型检查器完全可以通过统一化（Unification）自动解出该类型！
在 Lean 4 中，我们可以使用通配符（Hole）`_` 告诉编译器：“请在此处自动为我推断适当的类型”。

```lean
/-- 利用通配符 `_` 自动综合类型实参的 repeat -/
def «repeat''» (X : Type) (x : X) (count : Nat) : list X :=
  match count with
  | 0 => @nil _
  | count' + 1 => @cons _ x («repeat''» _ x count')

/-- 构造包含 [1; 2; 3] 的自然数列表（显式指定类型） -/
def list123 :=
  @cons Nat 1 (@cons Nat 2 (@cons Nat 3 (@nil Nat)))

/-- 利用通配符 `_` 简化书写 -/
def list123' :=
  @cons _ 1 (@cons _ 2 (@cons _ 3 (@nil _)))
```

### 1.4 隐式参数机制 (Implicit Arguments)

在 Lean 4 中，我们可以直接使用花括号 `{X : Type}` 将类型参数声明为**隐式参数**（Implicit Arguments）。
一旦声明为隐式，调用该函数或构造子时不仅不必写出类型实参，甚至连通配符 `_` 都不需要写：

```lean
/-- 在定义时直接将类型参数 `X` 声明为隐式参数 `{X : Type}` -/
def «repeat'''» {X : Type} (x : X) (count : Nat) : list X :=
  match count with
  | 0 => nil
  | count' + 1 => cons x («repeat'''» x count')

/-- 构造子隐式参数生效后的极简列表构造 -/
def list123'' := cons 1 (cons 2 (cons 3 nil))
```

注意：在为归纳类型本身声明参数时，如果将参数标记为隐式，会导致类型名本身也要求隐式应用。
例如：

```lean
inductive list' {X : Type} : Type where
  | nil' : @list' X
  | cons' (x : X) (l : @list' X) : @list' X
```

这样会导致无论是自然数列表还是布尔值列表，类型都写为 `list'`，抹杀了具体类型的直观区分。
因此在现代 Lean 4 中，归纳类型参数通常保留为小括号显式绑定 `(X : Type)`，
而编译器会自动将其构造子参数默认处理为隐式 `{X : Type}`，这提供了最为优雅的人体工学体验。

现在，让我们在多态列表上重新实现经典列表操作函数：

```lean
/-- 多态列表拼接函数 -/
def app {X : Type} : list X → list X → list X
  | nil, l2 => l2
  | cons h t, l2 => cons h (app t l2)

/-- 多态列表翻转函数 -/
def rev {X : Type} : list X → list X
  | nil => nil
  | cons h t => app (rev t) (cons h nil)

/-- 多态列表长度函数 -/
def length {X : Type} : list X → Nat
  | nil => 0
  | cons _ t => 1 + length t

/-- 翻转测试用例 1 -/
theorem test_rev1 : rev (cons 1 (cons 2 nil)) = cons 2 (cons 1 nil) := by
  rfl

/-- 翻转测试用例 2 -/
theorem test_rev2 : rev (cons true nil) = cons true nil := by
  rfl

/-- 长度测试用例 1 -/
theorem test_length1 : length (cons 1 (cons 2 (cons 3 nil))) = 3 := by
  rfl
```

### 1.5 显式提供类型实参与 `@` 标记

当编译器缺乏足够的局部类型信息来推断隐式参数时，会产生类型推导错误。
此时我们可以使用 `@` 前缀强制将所有隐式参数显式列出：

```lean
/-- 通过显式类型标注辅助推断空列表类型 -/
def mynil : list Nat := nil

/-- 通过 `@` 强制显式传递类型实参 `Nat` -/
def mynil' := @nil Nat

#check @nil
-- 输出: @nil : {X : Type} → list X
```

### 1.6 列表专用记号 (Notations for Lists)

我们为多态列表引入直观的中缀与方括号记号：

```lean
scoped infixr:67 " :: " => cons
scoped infixr:65 " ++ " => app

macro_rules (kind := NatList.natlist_semi)
  | `([ ]) => `(list.nil)
  | `([ $x ]) => `(list.cons $x list.nil)
  | `([ $x; $xs;* ]) => `(list.cons $x [ $xs;* ])

/-- 使用方括号分号记号构造多态列表 -/
def list123''' : list Nat := [1; 2; 3]
```

### 1.7 练习题：多态列表练习 (Polymorphic List Exercises)

### 🎯 练习：`poly_exercises` <Badge type="info" text="2 星 · standard" />

```lean
/-- 右拼空列表保持原列表不变 -/
theorem app_nil_r {X : Type} (l : list X) :
    l ++ nil = l := by
  sorry

/-- 列表拼接的结合律 -/
theorem app_assoc {A : Type} (l m n : list A) :
    l ++ m ++ n = (l ++ m) ++ n := by
  sorry

/-- 拼接后列表的长度等于各自长度之和 -/
theorem app_length {X : Type} (l1 l2 : list X) :
    length (l1 ++ l2) = length l1 + length l2 := by
  sorry
```

### 🎯 练习：`more_poly_exercises` <Badge type="info" text="2 星 · standard" />

```lean
/-- 翻转在拼接上的分配律 -/
theorem rev_app_distr {X : Type} (l1 l2 : list X) :
    rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  sorry

/-- 两次翻转还原原列表（对合性） -/
theorem rev_involutive {X : Type} (l : list X) :
    rev (rev l) = l := by
  sorry
```

## 2. 多态数对 / 乘积类型 (Polymorphic Pairs)

遵循相同的多态化思路，我们可以将上一章专门针对自然数的数对类型 `natprod`
泛化为支持任意两个类型的**多态积类型**（Products）：

```lean
/-- 多态乘积类型（积类型）：包含任意两个类型 `X` 与 `Y` 的元素对 -/
inductive prod (X Y : Type) : Type where
  | pair (x : X) (y : Y) : prod X Y
  deriving Repr, DecidableEq

open prod

/-- 为多态数对引入专用的数对构造记号 `(x, y)ₚ` -/
scoped notation "(" x ", " y ")ₚ" => prod.pair x y

/-- 为多态积类型引入中缀记号 `*ₚ` -/
scoped notation:35 X " *ₚ " Y => prod X Y

/-- 提取积类型的第一分量（左投影） -/
def fst {X Y : Type} (p : X *ₚ Y) : X :=
  match p with
  | (x, _)ₚ => x

/-- 提取积类型的第二分量（右投影） -/
def snd {X Y : Type} (p : X *ₚ Y) : Y :=
  match p with
  | (_, y)ₚ => y

/-- 组合函数（Zip）：将两个列表合并为数对列表 -/
def combine {X Y : Type} : list X → list Y → list (X *ₚ Y)
  | nil, _ => nil
  | _, nil => nil
  | x :: tx, y :: ty => (x, y)ₚ :: combine tx ty
```

### 🎯 练习：`combine_checks` <Badge type="tip" text="1 星 · standard, optional" />

思考下列问题：
1. `combine` 的类型是什么？
   答：`{X Y : Type} → list X → list Y → list (X *ₚ Y)`。
2. 计算 `combine [1; 2] [false; false; true; true]` 的结果是什么？
   答：`[(1, false)ₚ; (2, false)ₚ]`（由于第一个列表长度为 2，较短列表耗尽后即截断停止）。

```lean
#check @combine
#eval combine [1; 2] [false; false; true; true]
```

### 🎯 练习：`split` <Badge type="info" text="2 星 · standard, especially useful" />

函数 `split` 是 `combine` 的右逆运算：它接收一个数对列表并将其拆分成一对列表（在其他函数式语言中通常称为 `unzip`）。
请完成下面的 `split` 定义，并确保通过单元测试。

```lean
/-- 将数对列表解绑为两个平行的列表 -/
def split {X Y : Type} : list (X *ₚ Y) → (list X) *ₚ (list Y) :=
  sorry

/-- split 单元测试 -/
theorem test_split : split [(1, false)ₚ; (2, false)ₚ] = ([1; 2], [false; false])ₚ := by
  sorry
```

## 3. 多态可选类型 (Polymorphic Options)

我们上章定义的 `natoption` 同样可以泛化为通用的多态可选类型。
为了展示这一过程，我们首先在独立模块中进行探索：

```lean
namespace OptionPlayground

inductive option (X : Type) : Type where
  | Some (x : X) : option X
  | None : option X
  deriving Repr, DecidableEq

end OptionPlayground

/-- 通用多态可选类型 -/
inductive option (X : Type) : Type where
  | Some (x : X) : option X
  | None : option X
  deriving Repr, DecidableEq

open option

/-- 安全索引查找函数：获取列表中第 n 个元素，越界返回 None -/
def nth_error {X : Type} : list X → Nat → option X
  | nil, _ => None
  | a :: _, 0 => Some a
  | _ :: l', n + 1 => nth_error l' n

/-- nth_error 测试用例 1 -/
theorem test_nth_error1 : nth_error [4; 5; 6; 7] 0 = Some 4 := by
  rfl

/-- nth_error 测试用例 2（注：单元素列表使用 1 :: nil 避免与标准 List 歧义） -/
theorem test_nth_error2 : nth_error [1 :: nil; 2 :: nil] 1 = Some (2 :: nil) := by
  rfl

/-- nth_error 测试用例 3 -/
theorem test_nth_error3 : nth_error (true :: nil) 2 = None := by
  rfl
```

### 🎯 练习：`hd_error_poly` <Badge type="tip" text="1 星 · standard, optional" />

完成多态版本的 `hd_error` 函数定义，安全获取列表表头：

```lean
/-- 多态安全表头函数 -/
def hd_error {X : Type} (l : list X) : option X :=
  sorry

#check @hd_error

/-- hd_error 测试用例 1 -/
theorem test_hd_error1 : hd_error [1; 2] = Some 1 := by
  sorry

/-- hd_error 测试用例 2 -/
theorem test_hd_error2 : hd_error [1 :: nil; 2 :: nil] = Some (1 :: nil) := by
  sorry
```

## 4. 函数作为一等公民数据 (Functions as Data)

### 4.1 高阶函数 (Higher-Order Functions)

在现代函数式编程语言中，函数是一等公民（First-Class Citizens）：
函数可以像普通数据一样作为实参传给其他函数，也可以作为计算结果返回。
接收或返回函数的函数被称为**高阶函数**（Higher-Order Functions）。

```lean
/-- 对输入值 n 重复应用函数 f 三次 -/
def doit3times {X : Type} (f : X → X) (n : X) : X :=
  f (f (f n))

#check @doit3times

/-- doit3times 测试用例 1：重复减 2 三次 -/
theorem test_doit3times : doit3times minustwo 9 = 3 := by
  rfl

/-- doit3times 测试用例 2：重复布尔取反三次 -/
theorem test_doit3times' : doit3times negb true = false := by
  rfl
```

### 4.2 过滤器 (Filter)

`filter` 接收一个谓词函数 `test : X → Bool` 与一个列表，返回仅保留满足该谓词所有元素的新列表：

```lean
/-- 列表过滤器函数 -/
def filter {X : Type} (test : X → Bool) : list X → list X
  | nil => nil
  | h :: t =>
    if test h then h :: filter test t
    else filter test t

/-- 过滤偶数测试 -/
theorem test_filter1 : filter even [1; 2; 3; 4] = [2; 4] := by
  rfl

/-- 判定列表长度是否为 1 的谓词 -/
def length_is_1 {X : Type} (l : list X) : Bool :=
  length l == 1

/-- 过滤长度为 1 的子列表 -/
theorem test_filter2 : filter length_is_1 [ [1; 2]; 3 :: nil; 4 :: nil; [5; 6; 7]; nil; 8 :: nil ] =
    [ 3 :: nil; 4 :: nil; 8 :: nil ] := by
  rfl

/-- 基于 filter 实现的奇数成员计数函数 -/
def countoddmembers' (l : list Nat) : Nat :=
  length (filter odd l)

theorem «test_countoddmembers'1» : countoddmembers' [1; 0; 3; 1; 4; 5] = 4 := by
  rfl
theorem «test_countoddmembers'2» : countoddmembers' [0; 2; 4] = 0 := by
  rfl
theorem «test_countoddmembers'3» : countoddmembers' nil = 0 := by
  rfl
```

### 4.3 匿名函数 (Anonymous Functions)

有时候我们只需要临时传递一个简单的单次函数，单独使用 `def` 为其命名显得非常繁琐。
我们可以使用匿名函数（即 Lambda 表达式 `fun x => ...`）：

```lean
/-- 使用匿名平方函数 -/
theorem test_anon_fun' : doit3times (fun n => n * n) 2 = 256 := by
  rfl

/-- 使用匿名谓词进行过滤 -/
theorem test_filter2' : filter (fun l => length l == 1) [ [1; 2]; 3 :: nil; 4 :: nil; [5; 6; 7]; nil; 8 :: nil ] =
    [ 3 :: nil; 4 :: nil; 8 :: nil ] := by
  rfl
```

### 🎯 练习：`filter_even_gt7` <Badge type="info" text="2 星 · standard" />

利用 `filter`（而不是显式写结构递归 `match`）编写一个函数 `filter_even_gt7`，
过滤出自然数列表中所有既是偶数且大于 7 的数字：

```lean
/-- 过滤既为偶数且严格大于 7 的元素 -/
def filter_even_gt7 (l : list Nat) : list Nat :=
  sorry

theorem test_filter_even_gt7_1 : filter_even_gt7 [1; 2; 6; 9; 10; 3; 12; 8] = [10; 12; 8] := by
  sorry

theorem test_filter_even_gt7_2 : filter_even_gt7 [5; 2; 6; 19; 129] = nil := by
  sorry
```

### 🎯 练习：`partition` <Badge type="warning" text="3 星 · standard" />

利用 `filter` 编写划分函数 `partition`：
给定类型 `X`、谓词 `test : X → Bool` 与列表 `l`，`partition` 应返回数对 `(l1, l2)ₚ`，
其中 `l1` 为满足测试的所有元素，`l2` 为不满足测试的所有元素，且各元素在子列表中的相对顺序保持不变。

```lean
/-- 根据谓词对列表进行二元分割 -/
def partition {X : Type} (test : X → Bool) (l : list X) : (list X) *ₚ (list X) :=
  sorry

theorem test_partition1 : partition odd [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4])ₚ := by
  sorry

theorem test_partition2 : partition (fun _ => false) [5; 9; 0] = (nil, [5; 9; 0])ₚ := by
  sorry
```

## 5. 映射函数 (Map)

高阶函数 `map` 将变换函数 `f : X → Y` 逐一作用到列表 `[x1, x2, ...]` 的每一个元素上，
得到新的列表 `[f x1, f x2, ...]`:

```lean
/-- 列表元素逐项映射函数 -/
def map {X Y : Type} (f : X → Y) : list X → list Y
  | nil => nil
  | h :: t => f h :: map f t

theorem test_map1 : map (fun x => 3 + x) [2; 0; 2] = [5; 3; 5] := by
  rfl

theorem test_map2 : map odd [2; 1; 2; 5] = [false; true; false; true] := by
  rfl

theorem test_map3 : map (fun n => [even n; odd n]) [2; 1; 2; 5] =
    [[true; false]; [false; true]; [true; false]; [false; true]] := by
  rfl
```

### 5.1 练习题：Map 的性质与扁平化

### 🎯 练习：`map_rev` <Badge type="warning" text="3 星 · standard" />

证明 `map` 与 `rev` 可以交换复合顺序。你可能需要首先提出并证明一个关于 `map` 与 `app` 的辅助引理。

```lean
/-- map 分配到单元素列表拼接上的辅助引理 -/
theorem app_map {X Y : Type} (f : X → Y) (l : list X) (x : X) :
    app (map f l) (cons (f x) nil) = map f (app l (cons x nil)) := by
  sorry

/-- map 与列表翻转 rev 具有可交换性 -/
theorem map_rev {X Y : Type} (f : X → Y) (l : list X) :
    map f (rev l) = rev (map f l) := by
  sorry
```

### 🎯 练习：`flat_map` <Badge type="info" text="2 星 · standard, especially useful" />

`map` 函数将 `list X` 映射到 `list Y`，而 `flat_map` 则接收生成列表的函数 `f : X → list Y`，
并通过拼接将所有结果“展平”为一个统一的 `list Y`：

```lean
/-- 展平映射函数 -/
def flat_map {X Y : Type} (f : X → list Y) : list X → list Y :=
  sorry

theorem test_flat_map1 : flat_map (fun n => [n; n; n]) [1; 5; 4] =
    [1; 1; 1; 5; 5; 5; 4; 4; 4] := by
  sorry

/-- 可选类型上的映射函数 -/
def option_map {X Y : Type} (f : X → Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
```

### 🎯 练习：`implicit_args` <Badge type="info" text="2 星 · standard, optional" />

在原书 Coq 中，该练习鼓励读者通过手动将隐式参数改为显式小括号，练习掌握隐式参数的推导机制。
在 Lean 4 中，可以通过在函数名前加 `@` 观察完全显式化的签名与应用。

## 6. 折叠函数 (Fold)

更为强大通用的高阶函数是 `fold`（在现代数据工程中常被称为 `reduce`，是 Google MapReduce 模型的核心操作之一）。
直观上，`fold` 操作将二元运算符 `f` 依次插入到列表的所有相邻元素之间：
例如 `fold f [1; 2; 3; 4] b` 计算 `f 1 (f 2 (f 3 (f 4 b)))`。

```lean
/-- 右折叠函数 -/
def fold {X Y : Type} (f : X → Y → Y) : list X → Y → Y
  | nil, b => b
  | h :: t, b => f h (fold f t b)

#check (fold andb)
-- 输出: fold andb : list Bool → Bool → Bool

theorem fold_example1 : fold andb [true; true; false; true] true = false := by
  rfl

theorem fold_example2 : fold Nat.mul [1; 2; 3; 4] 1 = 24 := by
  rfl

theorem fold_example3 : fold app [1 :: nil; nil; [2; 3]; 4 :: nil] nil = [1; 2; 3; 4] := by
  rfl
```

### 🎯 练习：`fold_types_different` <Badge type="tip" text="1 星 · standard, optional" />

注意到 `fold` 由两个类型参数 `X` 与 `Y` 参数化，其中 `f : X → Y → Y`。
你能想到一个 `X` 和 `Y` 为不同类型的实际场景吗？
（例如统计列表中满足某条件的元素个数时，`X` 为列表元素类型，`Y` 为计数器类型 `Nat`；
或者在后面我们要实现的 `fold_length` 中也是如此）。

```lean
/-- 利用 fold 实现嵌套列表展平 -/
def flat_map' {X : Type} (l : list (list X)) : list X :=
  fold app l nil
```

## 7. 构造函数的函数与偏应用 (Functions That Construct Functions)

高阶函数不仅能接收函数作为输入，还可以**返回函数**作为输出：

```lean
/-- 常量函数发生器：返回一个无论接收何种自然数输入都恒返回 x 的函数 -/
def constfun {X : Type} (x : X) : Nat → X :=
  fun _ => x

def ftrue := constfun true

theorem constfun_example1 : ftrue 0 = true := by
  rfl

theorem constfun_example2 : (constfun 5) 99 = 5 := by
  rfl
```

实际上，多参数函数 `f : X → Y → Z` 本质上就是返回函数的函数：
类型箭头 `→` 是**右结合**的，因此 `X → Y → Z` 等价于 `X → (Y → Z)`。
当我们仅传入前一个参数时，所得到的即是一个全新的单参数函数，这种技术称为**偏函数应用**（Partial Application）：

```lean
/-- 自然数加 3 函数（偏应用） -/
def plus3 := Nat.add 3

#check plus3
-- 输出: plus3 : Nat → Nat

theorem test_plus3 : plus3 4 = 7 := by
  rfl

theorem test_plus3' : doit3times plus3 0 = 9 := by
  rfl

theorem test_plus3'' : doit3times (Nat.add 3) 0 = 9 := by
  rfl
```

## 8. 附加习题 (Additional Exercises)

```lean
namespace Exercises
```

### 🎯 练习：`fold_length` <Badge type="info" text="2 星 · standard" />

列表上的许多经典函数均可直接通过 `fold` 一行实现。
例如，使用 `fold` 重新实现 `length`：

```lean
/-- 利用 fold 计算列表长度 -/
def fold_length {X : Type} (l : list X) : Nat :=
  sorry

theorem test_fold_length1 : fold_length [4; 7; 0] = 3 := by
  sorry

/-- 证明 fold_length 与原生 length 的等价性 -/
theorem fold_length_correct {X : Type} (l : list X) :
    fold_length l = length l := by
  sorry
```

### 🎯 练习：`fold_map` <Badge type="warning" text="3 星 · standard" />

我们同样可以利用 `fold` 来定义 `map`：

```lean
/-- 利用 fold 实现 map -/
def fold_map {X Y : Type} (f : X → Y) (l : list X) : list Y :=
  sorry

/-- 证明 fold_map 与 map 严格等价 -/
theorem fold_map_correct {X Y : Type} (f : X → Y) (l : list X) :
    map f l = fold_map f l := by
  sorry

/-- 自动化评分占位声明（请勿修改） -/
def manual_grade_for_fold_map : Option (Nat × String) := none
```

### 🎯 练习：`currying` <Badge type="info" text="2 星 · advanced" />

函数类型 `X → Y → Z` 与 `(X *ₚ Y) → Z` 描述了两种接收双参数的形式：
前者支持柯里化（Curried），可分步进行偏应用；
后者接收一个紧凑的数对。
将 `(X *ₚ Y) → Z` 转换为 `X → Y → Z` 称为**柯里化**（Currying），以逻辑学家 Haskell Curry 命名；
其逆转换称为**反柯里化**（Uncurrying）。

```lean
/-- 柯里化函数 -/
def prod_curry {X Y Z : Type} (f : (X *ₚ Y) → Z) (x : X) (y : Y) : Z :=
  f (x, y)ₚ

/-- 反柯里化函数 -/
def prod_uncurry {X Y Z : Type} (f : X → Y → Z) (p : X *ₚ Y) : Z :=
  sorry

/-- 柯里化应用测试 -/
theorem test_map1' : map (Nat.add 3) [2; 0; 2] = [5; 3; 5] := by
  rfl

#check @prod_curry
#check @prod_uncurry

/-- 证明反柯里化与柯里化互为逆运算 1 -/
theorem uncurry_curry {X Y Z : Type} (f : X → Y → Z) (x : X) (y : Y) :
    prod_curry (prod_uncurry f) x y = f x y := by
  sorry

/-- 证明反柯里化与柯里化互为逆运算 2 -/
theorem curry_uncurry {X Y Z : Type} (f : (X *ₚ Y) → Z) (p : X *ₚ Y) :
    prod_uncurry (prod_curry f) p = f p := by
  sorry
```

### 🎯 练习：`nth_error_informal` <Badge type="info" text="2 星 · advanced" />

回顾 `nth_error` 的定义：
```lean
def nth_error {X : Type} : list X → Nat → option X
  | nil, _ => None
  | a :: _, 0 => Some a
  | _ :: l', n + 1 => nth_error l' n
```

请仔细撰写下列定理的非形式化数学证明：
`∀ (X : Type) (l : list X) (n : Nat), length l = n → nth_error l n = None`

【数学证明整理如下】：
- 对列表 `l : list X` 进行结构归纳：
  1. **基底情况**：`l = nil`。
     由定义可知 `length nil = 0`。假设 `length nil = n`，因此 `n = 0`。
     此时目标为证明 `nth_error nil 0 = None`。
     根据 `nth_error` 针对空列表的第一条模式匹配规则，`nth_error nil _ = None` 恒成立。
     基底获证。
  2. **归纳步**：设 `l = a :: l'`，并显式给出归纳假设：
     对于任意自然数 `k`，若 `length l' = k`，则 `nth_error l' k = None`。
     现假设 `length (a :: l') = n`。
     根据 `length` 的定义可知 `length (a :: l') = 1 + length l'`，因此 `n = 1 + length l'`。
     这表明 `n > 0`，故可记 `n = m + 1`，其中 `m = length l'`。
     根据 `nth_error` 对非空列表且非零索引的计算法则：
     `nth_error (a :: l') (m + 1) = nth_error l' m`。
     利用归纳假设（取 `k = m`，条件 `length l' = m` 满足），立即推得 `nth_error l' m = None`。
     归纳步获证。
  综上所述，由列表结构归纳原理，定理对所有列表 `l` 与自然数 `n` 均成立。证毕。

```lean
/-- 非形式化证明评分标记（请勿修改） -/
def manual_grade_for_informal_proof : Option (Nat × String) := none
```

### 8.1 丘奇数 (Church Numerals)

丘奇数是由数学家阿隆佐·丘奇（Alonzo Church）提出的一种使用纯高阶函数编码自然数的精妙理论。
在丘奇数编码中，一个自然数 `n` 被表示为一个接收函数 `f` 与基底 `x`、并计算将 `f` 重复迭代 `n` 次的高阶函数：
即 `n` 编码为 `fun X f x => fⁿ x`。

```lean
namespace Church

/-- 丘奇数的类型定义：接收任意类型 X、变换函数 f 与初值 x -/
def cnat := (X : Type) → (X → X) → X → X

/-- 丘奇数 1：应用函数 f 一次 -/
def one : cnat :=
  fun _X f x => f x

/-- 丘奇数 2：应用函数 f 两次 -/
def two : cnat :=
  fun _X f x => f (f x)

/-- 丘奇数 0：零次应用（直接返回初值 x） -/
def zero : cnat :=
  fun _X _f x => x

/-- 丘奇数 3：应用函数 f 三次（恰好等同于前面的 doit3times） -/
def three : cnat :=
  @doit3times

/-- 另一种等价形式：将 f 视为后继器 succ，x 视为零元 zero -/
def zero' : cnat :=
  fun _X _succ zero => zero

def one' : cnat :=
  fun _X succ zero => succ zero

def two' : cnat :=
  fun _X succ zero => succ (succ zero)

/-- 转化为标准皮亚诺自然数：测试零 -/
theorem zero_church_peano : zero Nat Nat.succ 0 = 0 := by
  rfl

/-- 转化为标准皮亚诺自然数：测试一 -/
theorem one_church_peano : one Nat Nat.succ 0 = 1 := by
  rfl

/-- 转化为标准皮亚诺自然数：测试二 -/
theorem two_church_peano : two Nat Nat.succ 0 = 2 := by
  rfl
```

### 🎯 练习：`church_scc` <Badge type="info" text="2 星 · advanced" />

定义丘奇数的后继函数 `scc`。给定丘奇数 `n`（即 `fun X f x => fⁿ x`），
`scc n` 应当迭代应用 `f` 共 `n + 1` 次：

```lean
/-- 丘奇数后继函数 -/
def scc (n : cnat) : cnat :=
  sorry

theorem scc_1 : scc zero = one := by
  sorry

theorem scc_2 : scc one = two := by
  sorry

theorem scc_3 : scc two = three := by
  sorry
```

### 🎯 练习：`church_plus` <Badge type="warning" text="3 星 · advanced" />

定义丘奇数的加法函数 `plus`。计算 `fⁿ (fᵐ x)`：

```lean
/-- 丘奇数加法函数 -/
def plus (n m : cnat) : cnat :=
  sorry

theorem plus_1 : plus zero one = one := by
  sorry

theorem plus_2 : plus two three = plus three two := by
  sorry

theorem plus_3 : plus (plus two two) three = plus one (plus three three) := by
  sorry
```

### 🎯 练习：`church_mult` <Badge type="warning" text="3 星 · advanced" />

定义丘奇数的乘法函数 `mult`：

```lean
/-- 丘奇数乘法函数 -/
def mult (n m : cnat) : cnat :=
  sorry

theorem mult_1 : mult one one = one := by
  sorry

theorem mult_2 : mult zero (plus three three) = zero := by
  sorry

theorem mult_3 : mult two three = plus three three := by
  sorry
```

### 🎯 练习：`church_exp` <Badge type="warning" text="3 星 · advanced" />

定义丘奇数的幂运算函数 `exp`：

```lean
/-- 丘奇数幂运算函数 -/
def exp (n m : cnat) : cnat :=
  sorry

theorem exp_1 : exp two two = plus two two := by
  sorry

theorem exp_2 : exp three zero = one := by
  sorry

theorem exp_3 : exp three two = plus (mult two (mult two two)) one := by
  sorry

end Church

end Exercises

end Poly
```
