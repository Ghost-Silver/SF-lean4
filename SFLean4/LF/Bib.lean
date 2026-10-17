/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 参考文献 (Bib: Bibliography)

本卷中引用的主要经典学术文献与著作列表：

---

### [Bertot 2004]
Yves Bertot and Pierre Castéran.
*Interactive Theorem Proving and Program Development: Coq'Art: The Calculus of Inductive Constructions*.
Springer-Verlag, 2004.
DOI / Link: [https://www.labri.fr/perso/casteran/CoqArt/](https://www.labri.fr/perso/casteran/CoqArt/)

### [Chlipala 2013]
Adam Chlipala.
*Certified Programming with Dependent Types: A Pragmatic Introduction to the Coq Proof Assistant*.
MIT Press, 2013.
Online: [http://adam.chlipala.net/cpdt/](http://adam.chlipala.net/cpdt/)

### [Lipovaca 2011]
Miran Lipovača.
*Learn You a Haskell for Great Good! A Beginner's Guide*.
No Starch Press, April 2011.
Online: [http://learnyouahaskell.com](http://learnyouahaskell.com)

### [O'Sullivan 2008]
Bryan O'Sullivan, John Goerzen, and Don Stewart.
*Real World Haskell: Code You Can Believe In*.
O'Reilly Media, 2008.
Online: [http://book.realworldhaskell.org](http://book.realworldhaskell.org)

### [Pugh 1991]
William Pugh.
*"The Omega test: a fast and practical integer programming algorithm for dependence analysis"*.
Proceedings of the 1991 ACM/IEEE conference on Supercomputing (Supercomputing '91), ACM, 1991.
DOI: [https://doi.org/10.1145/125826.125848](https://doi.org/10.1145/125826.125848)

### [Wadler 2015]
Philip Wadler.
*"Propositions as Types"*.
Communications of the ACM, Vol. 58, No. 12 (2015): 75–84.
DOI: [https://doi.org/10.1145/2699407](https://doi.org/10.1145/2699407)
-/

namespace Bib

/-- 参考文献条目数据结构 -/
structure Entry where
  key : String
  authors : String
  title : String
  year : Nat
  publisher : String

/-- 本书引用之核心文献库 -/
def bibliography : List Entry := [
  { key := "Bertot 2004"
  , authors := "Yves Bertot and Pierre Castéran"
  , title := "Interactive Theorem Proving and Program Development"
  , year := 2004
  , publisher := "Springer-Verlag" },
  { key := "Chlipala 2013"
  , authors := "Adam Chlipala"
  , title := "Certified Programming with Dependent Types"
  , year := 2013
  , publisher := "MIT Press" },
  { key := "Lipovaca 2011"
  , authors := "Miran Lipovača"
  , title := "Learn You a Haskell for Great Good!"
  , year := 2011
  , publisher := "No Starch Press" },
  { key := "O'Sullivan 2008"
  , authors := "Bryan O'Sullivan, John Goerzen, and Don Stewart"
  , title := "Real World Haskell"
  , year := 2008
  , publisher := "O'Reilly Media" },
  { key := "Pugh 1991"
  , authors := "William Pugh"
  , title := "The Omega test: a fast and practical integer programming algorithm for dependence analysis"
  , year := 1991
  , publisher := "ACM" },
  { key := "Wadler 2015"
  , authors := "Philip Wadler"
  , title := "Propositions as Types"
  , year := 2015
  , publisher := "ACM" }
]

end Bib
