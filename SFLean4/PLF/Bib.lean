/-!
# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 参考文献 (Bib: Bibliography)

本卷中引用的核心经典学术文献与著作列表：

---

### [Aydemir 2008]
Brian Aydemir, Arthur Charguéraud, Benjamin C. Pierce, Randy Pollack, and Stephanie Weirich.
*"Engineering Formal Metatheory"*.
In ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL), San Francisco, California, pages 3–15. ACM, January 2008.
Link: [https://www.cis.upenn.edu/~bcpierce/papers/binders.pdf](https://www.cis.upenn.edu/~bcpierce/papers/binders.pdf)

### [Harper 2015]
Robert Harper.
*Practical Foundations for Programming Languages*.
Cambridge University Press. Second edition, 2016.
Online: [https://www.cs.cmu.edu/~rwh/pfpl/](https://www.cs.cmu.edu/~rwh/pfpl/)

### [Mitchell 1996]
John C. Mitchell.
*Foundations for Programming Languages*.
MIT Press, 1996.

### [Nipkow 2014]
Tobias Nipkow and Gerwin Klein.
*Concrete Semantics with Isabelle/HOL*.
Springer, 2014.
Online: [http://www.concrete-semantics.org](http://www.concrete-semantics.org)

### [Pierce 2002]
Benjamin C. Pierce.
*Types and Programming Languages* (TAPL).
MIT Press, 2002.

### [Pugh 1991]
William Pugh.
*"The Omega test: a fast and practical integer programming algorithm for dependence analysis"*.
Proceedings of the 1991 ACM/IEEE conference on Supercomputing. ACM, 1991.
DOI: [https://dl.acm.org/citation.cfm?id=125848](https://dl.acm.org/citation.cfm?id=125848)

### [Winskel 1993]
Glynn Winskel.
*The Formal Semantics of Programming Languages: An Introduction*.
MIT Press, 1993.
-/

namespace PLF.Bib

/-- 参考文献条目数据结构 -/
structure Entry where
  key : String
  authors : String
  title : String
  year : Nat
  publisher : String

/-- 本书引用之核心文献库 -/
def bibliography : List Entry := [
  { key := "Aydemir 2008"
  , authors := "Brian Aydemir, Arthur Charguéraud, Benjamin C. Pierce, Randy Pollack, and Stephanie Weirich"
  , title := "Engineering Formal Metatheory"
  , year := 2008
  , publisher := "ACM" },
  { key := "Harper 2015"
  , authors := "Robert Harper"
  , title := "Practical Foundations for Programming Languages"
  , year := 2016
  , publisher := "Cambridge University Press" },
  { key := "Mitchell 1996"
  , authors := "John C. Mitchell"
  , title := "Foundations for Programming Languages"
  , year := 1996
  , publisher := "MIT Press" },
  { key := "Nipkow 2014"
  , authors := "Tobias Nipkow and Gerwin Klein"
  , title := "Concrete Semantics with Isabelle/HOL"
  , year := 2014
  , publisher := "Springer" },
  { key := "Pierce 2002"
  , authors := "Benjamin C. Pierce"
  , title := "Types and Programming Languages"
  , year := 2002
  , publisher := "MIT Press" },
  { key := "Pugh 1991"
  , authors := "William Pugh"
  , title := "The Omega test: a fast and practical integer programming algorithm for dependence analysis"
  , year := 1991
  , publisher := "ACM" },
  { key := "Winskel 1993"
  , authors := "Glynn Winskel"
  , title := "The Formal Semantics of Programming Languages: An Introduction"
  , year := 1993
  , publisher := "MIT Press" }
]

end PLF.Bib
