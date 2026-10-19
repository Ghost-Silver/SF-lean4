import SFLean4.LF.Maps
import SFLean4.LF.Imp

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十三章：词法分析与语法分析 (ImpParser: Lexing and Parsing in Coq / Lean 4)

在前一章 [Imp](/LF/Imp) 中，我们建立 Imp 语言时完全跳过了**具体语法 (Concrete Syntax)** 的处理——
即程序员手写的 ASCII 文本字符串是如何被转化为抽象语法树（AST，即数据类型 `aexp`、`bexp` 和 `com`）的。

在本章中，我们将展示如何仅利用函数式编程设施，在证明助理中完整构建一个用于 Imp 语言的：
1. **词法分析器 (Lexer / Tokenizer)**：将源代码字符串切分为词法记号（Tokens）流；
2. **递归下降语法分析器 (Recursive-Descent Parser)**：自顶向下构造出对应的表达式与命令抽象语法树。

> **阅读提示**：本章不包含证明题或练习题。其主要目的在于概念性验证：
> 在纯函数式逻辑环境中，无需借助外部工具（如 Lex/Yacc/Flex/Bison），也能完整优雅地实现编译器前端的词法与语法解析。
> 读者可重点关注递归下降解析器的单子（Monad）化组织方式与文法结合性处理。
-/

namespace ImpParser

open Maps
open Imp
open Imp.com
open Imp.aexp
open Imp.bexp

-- #################################################################
-- * 内部实现机制 (Internals)
-- #################################################################

-- =================================================================
-- ** 词法分析 (Lexical Analysis)
-- =================================================================

/-!
### 1. 字符分类与词法记号识别

词法分析器的核心任务是逐字符扫描输入流，剔除无意义的空白字符，并将标识符、数字及操作符凝聚为 Token。
-/

/-- 判断字符是否为空白字符（空格、制表符、换行符、回车符） -/
def isWhite (c : Char) : Bool :=
  let n := c.toNat
  n == 32 || n == 9 || n == 10 || n == 13

/-- 判断字符是否为小写英文字母 ('a'..'z') -/
def isLowerAlpha (c : Char) : Bool :=
  let n := c.toNat
  97 <= n && n <= 122

/-- 判断字符是否为英文字母（大写或小写） -/
def isAlpha (c : Char) : Bool :=
  let n := c.toNat
  (65 <= n && n <= 90) || (97 <= n && n <= 122)

/-- 判断字符是否为十进制数字 ('0'..'9') -/
def isDigit (c : Char) : Bool :=
  let n := c.toNat
  48 <= n && n <= 57

/-- 字符种类分类标签 -/
inductive chartype where
  | white
  | alpha
  | digit
  | other
deriving DecidableEq, Repr

/-- 对单个字符进行分类 -/
def classifyChar (c : Char) : chartype :=
  if isWhite c then
    chartype.white
  else if isAlpha c then
    chartype.alpha
  else if isDigit c then
    chartype.digit
  else
    chartype.other

/-- 将字符串转化为字符列表 -/
def list_of_string (s : String) : List Char := s.toList

/-- 将字符列表聚合为字符串 -/
def string_of_list (xs : List Char) : String := String.ofList xs

/-- 词法记号类型别名 -/
abbrev token := String

/-- 词法分析核心递归辅助函数：
    - `cls`: 当前累计 Token 预期的字符种类；
    - `acc`: 当前累积但尚未输出的字符（倒序存放）；
    - `xs`: 待处理的字符流。 -/
def tokenize_helper (cls : chartype) (acc xs : List Char) : List (List Char) :=
  let tk : List (List Char) := match acc with | [] => [] | _ => acc.reverse :: []
  match xs with
  | [] => tk
  | x :: xs' =>
    if x == '(' then
      tk ++ ('(' :: []) :: tokenize_helper chartype.other [] xs'
    else if x == ')' then
      tk ++ (')' :: []) :: tokenize_helper chartype.other [] xs'
    else
      let tp := classifyChar x
      match cls, tp with
      | _, chartype.white =>
        tk ++ tokenize_helper chartype.white [] xs'
      | chartype.alpha, chartype.alpha =>
        tokenize_helper chartype.alpha (x :: acc) xs'
      | chartype.digit, chartype.digit =>
        tokenize_helper chartype.digit (x :: acc) xs'
      | chartype.other, chartype.other =>
        tokenize_helper chartype.other (x :: acc) xs'
      | _, _ =>
        tk ++ tokenize_helper tp (x :: []) xs'

/-- 将输入字符串切分为记号（Token）列表 -/
def tokenize (s : String) : List String :=
  (tokenize_helper chartype.white [] (list_of_string s)).map string_of_list

/-- 词法分析测试示例 1 -/
theorem tokenize_ex1 :
    tokenize "abc12=3  223*(3+(a+c))"
  = ["abc", "12", "=", "3", "223",
       "*", "(", "3", "+", "(",
       "a", "+", "c", ")", ")"] := by
  native_decide

-- =================================================================
-- ** 语法分析 (Parsing)
-- =================================================================

-- -----------------------------------------------------------------
-- *** 带错误信息的选项类型 (Options With Errors)
-- -----------------------------------------------------------------

/-!
### 2. 错误处理单子 `optionE`

在解析过程中，分析器随时可能遭遇不合语法的符号。
`optionE` 在成功时返回解析出的值 `SomeE x`，失败时携带诊断错误信息 `NoneE s`。
-/

/-- 携带错误信息的解析结果单子类型 -/
inductive optionE (X : Type) : Type where
  | SomeE (x : X) : optionE X
  | NoneE (s : String) : optionE X
deriving Repr, DecidableEq

open optionE

instance : Functor optionE where
  map f
    | SomeE x => SomeE (f x)
    | NoneE err => NoneE err

instance : Applicative optionE where
  pure x := SomeE x
  seq f x :=
    match f with
    | SomeE g =>
      match x () with
      | SomeE y => SomeE (g y)
      | NoneE err => NoneE err
    | NoneE err => NoneE err

instance : Monad optionE where
  bind ma f :=
    match ma with
    | SomeE x => f x
    | NoneE err => NoneE err

instance : OrElse (optionE α) where
  orElse a b :=
    match a with
    | SomeE x => SomeE x
    | NoneE _ => b ()

-- -----------------------------------------------------------------
-- *** 构建语法分析器的通用组合子 (Generic Combinators)
-- -----------------------------------------------------------------

/-!
### 3. 解析器组合子 (Parser Combinators)

一个解析器是一个函数：输入未消费的记号列表，返回解析所得目标及剩余记号。
-/

/-- 语法分析器类型：接收 Token 列表，输出解析结果与剩余 Token 列表 -/
abbrev parser (T : Type) := List token -> optionE (Prod T (List token))

/-- 步数索引的重复匹配辅助函数 -/
def many_helper {T : Type} (p : parser T) (acc : List T) (steps : Nat) (xs : List token)
    : optionE (Prod (List T) (List token)) :=
  match steps, p xs with
  | 0, _ => NoneE "Too many recursive calls"
  | _, NoneE _ => SomeE (acc.reverse, xs)
  | steps' + 1, SomeE (t, xs') => many_helper p (t :: acc) steps' xs'

/-- 步数索引的零次或多次重复匹配组合子 `many` -/
def many {T : Type} (p : parser T) (steps : Nat) : parser (List T) :=
  many_helper p [] steps

/-- 期望首先匹配指定 Token `t`，随后调用解析器 `p` -/
def firstExpect {T : Type} (t : token) (p : parser T) : parser T :=
  fun xs =>
    match xs with
    | x :: xs' =>
      if x == t then p xs'
      else NoneE s!"expected '{t}'."
    | [] => NoneE s!"expected '{t}'."

/-- 专门匹配单个指定 Token 的断言解析器 -/
def expect (t : token) : parser Unit :=
  firstExpect t (fun xs => SomeE ((), xs))

-- -----------------------------------------------------------------
-- *** Imp 的递归下降语法分析器 (A Recursive-Descent Parser for Imp)
-- -----------------------------------------------------------------

/-!
### 4. 标识符与数值的解析
-/

/-- 解析合法变量标识符（由全小写字母构成） -/
def parseIdentifier (xs : List token) : optionE (Prod String (List token)) :=
  match xs with
  | [] => NoneE "Expected identifier"
  | x :: xs' =>
    if x.toList.all isLowerAlpha then
      SomeE (x, xs')
    else
      NoneE s!"Illegal identifier:'{x}'"

/-- 解析自然数常量（由数字构成，按十进制累加） -/
def parseNumber (xs : List token) : optionE (Prod Nat (List token)) :=
  match xs with
  | [] => NoneE "Expected number"
  | x :: xs' =>
    if x.toList.all isDigit then
      SomeE (x.toList.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0, xs')
    else
      NoneE "Expected number"

/-!
### 5. 算术表达式解析 (Parsing Arithmetic Expressions)

为了正确体现运算符优先级与左结合律，我们将算术文法分层为：
- `PrimaryExp`: 基础项（原子：变量、数字、括号表达式）；
- `ProductExp`: 乘法项（优先级高于加减法）；
- `SumExp`: 加减法表达式。
-/

mutual
  /-- 解析基础算术表达式（变量、数字或带括号算式） -/
  def parsePrimaryExp (steps : Nat) (xs : List token) : optionE (Prod aexp (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 =>
      (do
        let (i, rest) ← parseIdentifier xs
        pure (AId i, rest)) <|>
      (do
        let (n, rest) ← parseNumber xs
        pure (ANum n, rest)) <|>
      (do
        let (e, rest) ← firstExpect "(" (parseSumExp steps') xs
        let (_, rest') ← expect ")" rest
        pure (e, rest'))

  /-- 解析乘法表达式（左结合） -/
  def parseProductExp (steps : Nat) (xs : List token) : optionE (Prod aexp (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 => do
      let (e, rest) ← parsePrimaryExp steps' xs
      let (es, rest') ← many (firstExpect "*" (parsePrimaryExp steps')) steps' rest
      pure (es.foldl AMult e, rest')

  /-- 解析加法与减法表达式（左结合） -/
  def parseSumExp (steps : Nat) (xs : List token) : optionE (Prod aexp (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 => do
      let (e, rest) ← parseProductExp steps' xs
      let (es, rest') ← many (fun xs =>
        (do
          let (e, rest') ← firstExpect "+" (parseProductExp steps') xs
          pure ((true, e), rest')) <|>
        (do
          let (e, rest') ← firstExpect "-" (parseProductExp steps') xs
          pure ((false, e), rest'))) steps' rest
      pure (es.foldl (fun e0 term =>
        match term with
        | (true, e) => APlus e0 e
        | (false, e) => AMinus e0 e) e, rest')
end

/-- 完整算术表达式解析器（顶层入口即加减法层级） -/
def parseAExp := parseSumExp

/-!
### 6. 布尔表达式解析 (Parsing Boolean Expressions)

布尔表达式的优先级同样通过分层处理：
- `AtomicExp`: 原子布尔项（`true`、`false`、非操作 `~`、括号布尔式、以及算术关系比较 `=`、`<=`）；
- `ConjunctionExp`: 合取项（`&&`）。
-/

mutual
  /-- 解析原子布尔表达式 -/
  def parseAtomicExp (steps : Nat) (xs : List token) : optionE (Prod bexp (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 =>
      (do
        let (_, rest) ← expect "true" xs
        pure (BTrue, rest)) <|>
      (do
        let (_, rest) ← expect "false" xs
        pure (BFalse, rest)) <|>
      (do
        let (e, rest) ← firstExpect "~" (parseAtomicExp steps') xs
        pure (BNot e, rest)) <|>
      (do
        let (e, rest) ← firstExpect "(" (parseConjunctionExp steps') xs
        let (_, rest') ← expect ")" rest
        pure (e, rest')) <|>
      (do
        let (e, rest) ← parseProductExp steps' xs
        (do
          let (e', rest') ← firstExpect "=" (parseAExp steps') rest
          pure (BEq e e', rest')) <|>
        (do
          let (e', rest') ← firstExpect "<=" (parseAExp steps') rest
          pure (BLe e e', rest')) <|>
        NoneE "Expected '=' or '<=' after arithmetic expression")

  /-- 解析合取表达式（`&&`，左结合） -/
  def parseConjunctionExp (steps : Nat) (xs : List token) : optionE (Prod bexp (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 => do
      let (e, rest) ← parseAtomicExp steps' xs
      let (es, rest') ← many (firstExpect "&&" (parseAtomicExp steps')) steps' rest
      pure (es.foldl BAnd e, rest')
end

/-- 完整布尔表达式解析器 -/
def parseBExp := parseConjunctionExp

#check parseConjunctionExp

/-- 带有 100 步调用预算的交互式测试辅助函数 -/
def testParsing {X : Type}
    (p : Nat -> List token -> optionE (Prod X (List token)))
    (s : String) :=
  let t := tokenize s
  p 100 t

/-!
### 7. 命令语句解析 (Parsing Commands)

语句文法分为：
- `SimpleCommand`: 基本控制语句（`skip`、`if ... then ... else ... end`、`while ... do ... end`、赋值 `x := a`）；
- `SequencedCommand`: 分号连接的语句序列。
-/

mutual
  /-- 解析单一简单语句 -/
  def parseSimpleCommand (steps : Nat) (xs : List token) : optionE (Prod com (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 =>
      (do
        let (_, rest) ← expect "skip" xs
        pure (CSkip, rest)) <|>
      (do
        let (e, rest) ← firstExpect "if" (parseBExp steps') xs
        let (c, rest') ← firstExpect "then" (parseSequencedCommand steps') rest
        let (c', rest'') ← firstExpect "else" (parseSequencedCommand steps') rest'
        let (_, rest''') ← expect "end" rest''
        pure (CIf e c c', rest''')) <|>
      (do
        let (e, rest) ← firstExpect "while" (parseBExp steps') xs
        let (c, rest') ← firstExpect "do" (parseSequencedCommand steps') rest
        let (_, rest'') ← expect "end" rest'
        pure (CWhile e c, rest'')) <|>
      (do
        let (i, rest) ← parseIdentifier xs
        let (e, rest') ← firstExpect ":=" (parseAExp steps') rest
        pure (CAsgn i e, rest')) <|>
      NoneE "Expecting a command"

  /-- 解析分号顺序复合语句（右结合序列） -/
  def parseSequencedCommand (steps : Nat) (xs : List token) : optionE (Prod com (List token)) :=
    match steps with
    | 0 => NoneE "Too many recursive calls"
    | steps' + 1 => do
      let (c, rest) ← parseSimpleCommand steps' xs
      (do
        let (c', rest') ← firstExpect ";" (parseSequencedCommand steps') rest
        pure (CSeq c c', rest')) <|>
      pure (c, rest)
end

/-- 解析上限递归步数 -/
def bignumber := 1000

/-- 端到端顶层解析入口：将源码字符串解析为 Imp 命令抽象语法树 -/
def parse (str : String) : optionE com :=
  let tokens := tokenize str
  match parseSequencedCommand bignumber tokens with
  | SomeE (c, []) => SomeE c
  | SomeE (_, t :: _) => NoneE s!"Trailing tokens remaining: {t}"
  | NoneE err => NoneE err

-- #################################################################
-- * 综合示例 (Examples)
-- #################################################################

/-!
### 8. 端到端综合测试用例
-/

/-- 示例 1 预期 AST -/
def eg1_expected : optionE com :=
  SomeE (CIf (BEq (AId "x")
                  (APlus (AMinus (APlus (APlus (AId "y") (ANum 1)) (ANum 2))
                                 (AMult (AId "y") (ANum 6)))
                         (ANum 3)))
             (CSeq (CAsgn "x" (AMult (AId "x") (ANum 1)))
                   (CAsgn "y" (ANum 0)))
             CSkip)

/-- 端到端综合解析示例 1：带复合算术表达式的分支与赋值语句 -/
theorem eg1 : parse "
  if x = y + 1 + 2 - y * 6 + 3 then
    x := x * 1;
    y := 0
  else
    skip
  end  " = eg1_expected := by
  native_decide

/-- 示例 2 预期 AST -/
def eg2_expected : optionE com :=
  SomeE (CSeq CSkip
        (CSeq (CAsgn "z" (AMult (AMult (AId "x") (AId "y"))
                               (AMult (AId "x") (AId "x"))))
        (CSeq (CWhile (BEq (AId "x") (AId "x"))
                      (CSeq (CIf (BAnd (BLe (AId "z") (AMult (AId "z") (AId "z")))
                                       (BNot (BEq (AId "x") (ANum 2))))
                                 (CSeq (CAsgn "x" (AId "z"))
                                       (CAsgn "y" (AId "z")))
                                 CSkip)
                            CSkip))
              (CAsgn "x" (AId "z")))))

/-- 端到端综合解析示例 2：嵌套循环、分支与复合赋值程序 -/
theorem eg2 : parse "
  skip;
  z:=x*y*(x*x);
  while x=x do
    if (z <= z*z) && ~(x = 2) then
      x := z;
      y := z
    else
      skip
    end;
    skip
  end;
  x:=z  " = eg2_expected := by
  native_decide

end ImpParser
