
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/cetz:0.4.0"
#import "@local/math-notes:0.3.0": *
#import "@preview/xarrow:0.3.1": xarrow
#import "@preview/in-dexter:0.7.2" as in-dexter: index

#show: math_notes.with(title: [Functional Analysis])

#let index_math = index.with(index: "Math")

#let enum_numbering = (..it) => {
  counter("enum").update(it.pos())
  numbering("(i)", ..it)
}

#let enum_label_mark = metadata("enumeration_label")

#show ref: it => {
  let el = it.element
  if el == enum_label_mark {
    let loc = el.location()
    link(loc, numbering("(i)", ..counter("enum").at(loc)))
  } else {
    it
  }
}

#let enum-label(label) = [#enum_label_mark#label]


#let injlim = $limits(limits(lim)_(xarrow(#v(-50em), width: #1.8em)))$
#let projlim = $limits(limits(lim)_(xarrow(sym: arrow.l.long, #v(-50em), width: #1.8em)))$

#let topdual(X) = $#X^(')$
#let kk = $bb(k)$

#let Grp = $sans("Grp")$
#let normdot = $norm(#h(0.15em)dot#h(0.15em))$

#let scr(it) = text(features: ("ss01",), box($cal(it)$))

= Measures
== Class of Sets <class-of-sets>
If $2^Omega$ denotes the power set of the set $Omega$ and a collection of subsets $cal(C) subset 2^Omega$, we say $cal(C)$ is defined on $Omega$.

For convenience, let's define some operations on a collection of sets $cal(C) in 2^Omega$.

- Given $f : Sigma arrow.r Omega$, $f^(- 1) (cal(C)) := { f^(- 1) (A) in Sigma divides A in cal(C) }$,

- Given $B subset Omega$, $B inter cal(C) := { B inter A divides A in cal(C) }$.

#definition[Semiring][
  A nonempty family of sets $cal(S)$ is called a *semiring (of sets)* if the following three statements are true for all sets $A$ and $B$,

  + $diameter in cal(S)$

  + $A , B in cal(S) ==> A inter B in cal(S)$

  + $A , B in cal(S)$ implies $A - B = union_(i = 1)^n C_i$, where ${ C_i }_(i = 1)^n$ is a collection of pairwise disjoint sets in $cal(S)$.


  Since condition (3) together with $cal(S) eq.not diameter$ implies that $diameter in cal(S)$, conditions (1) is actually unnecessary.

]
#definition[Ring][
  A nonempty family of sets $cal(R)$ is called a *ring (of sets)* if it is closed under finite union and difference. That is, the following two statements are true for all sets $A$ and $B$,

  + $A , B in cal(R)$ implies $A union B in cal(R)$

  + $A , B in cal(R)$ implies $A - B in cal(R)$.
] <ring-of-sets>
A ring of sets $cal(R)$ is a ring in the context of abstract algebra with the operations intersection(multiplication) and symmetric difference(addition), where the multiplicative identity is the set $union_(A in cal(R)) A$.

#definition[Semialgebra#super[\#1]][
  A subring $cal(S)$ defined on $Omega$ is called an #strong[semialgebra] if it contains $Omega$.
]

#definition[Semialgebra#super[\#2]][
  A collection of sets $cal(S) subset 2^Omega$ is called an #strong[semialgebra] the following two statements are true for all sets $A$ and $B$,

  + $A , B in cal(S)$ implies $A inter B in cal(S)$

  + $A in cal(S)$ implies $A^complement = union_(i = 1)^n C_i$, where ${ C_i }_(i = 1)^n$ is a collection of pairwise disjoint sets in $cal(S)$.

]
#example[
  $ cal(C) equiv { ( a , b \] in bb(R) divides - oo lt.eq a lt.eq b < oo } union { (a , oo) in bb(R) divides - oo lt.eq a < oo } $ is a semialgebra on $bb(R)$.

]
#definition[Algebra#super[\#1]][
  A #link(<ring-of-sets>)[ring] $cal(F)$ defined on $Omega$ is called an #strong[algebra (of sets)] if it contains $Omega$.
]<algebra-of-sets-1>
#proposition[
  Every #link(<ring-of-sets>)[ring] is a semiring.
]
#proof[
  Let $cal(R)$ be a ring. First we see $diameter = A - A in cal(R)$. Second, it is straightforward to check $ A inter B = (A union B - (A - B)) - (B - A) in cal(R) . $ Finally, it is a trivial fact that $A - B = C_1 in cal(R)$. Thus we show the ring $cal(R)$ is also a semiring.~◻
]

The following equivalent definitions of algebra are common to see.

#definition[Algebra#super[\#2]][A collection of sets $cal(F) subset 2^Omega$ is called an #strong[algebra (of sets)] if

  + $Omega in cal(F)$,

  + $A in cal(F)$ implies $A^complement in cal(F)$,

  + $A , B in cal(F)$ implies $A union B in cal(F)$.

]<algebra-of-sets-2>
An algebra of sets is an associative algebra over a field in the context of abstract algebra: it is a ring and also a vector space over the field $F_2$ of 2 elements, which makes it an $F_2$-algebra.

#proposition[
  Every algebra is a #link(<ring-of-sets>)[ring].
]
#proof[
  Note it holds that $ A - B = A inter B^complement = (A^complement union B)^complement . $

]
#example[
  Let $Omega$ be a nonempty set, and let $\# A$ denote the number of elements of a set $A subset Omega$. Then
  $
    cal(F) = { A subset Omega : "either" \# A "is finite or" \# A^complement "is finite" }
  $
  is an algebra defined on $Omega$.
]
#definition[$sigma$-algebra][
  A class $cal(F) subset 2^Omega$ is called a #strong[$sigma$-algebra] if it is an algebra and if it satisfies

  #set enum(numbering: "(a)", start: 4)

  + $A_n in cal(F)$ for $n gt.eq 1$ $arrow.r.double.long$ $union.big_(n = 1)^oo A_n in cal(F)$.

]<sigma-algebra>
Under the assumption that $cal(F)$ is an algebra, condition (d) can be replaced by a weaker condition (d'), which leads to the following equivalent definition.

#definition[$sigma$-algebra][
  A class $cal(F) subset 2^Omega$ is called a #strong[$sigma$-algebra] if it is an algebra and if it satisfies

  + $A_n in cal(F) , med A_n subset A_(n + 1)$ for $n gt.eq 1$ $arrow.r.double.long$ $union.big_(n = 1)^oo A_n in cal(F)$.

]
#example[
  Let $Omega$ be a nonempty set. Then
  $
    cal(F) = { A subset Omega : "either" A "is a countable set or" A^complement "is a countable set" }
  $
  is a $sigma$-algebra defined on $Omega$.
]


It is easy to check the intersection of a family of $sigma$-algebras on $Omega$ is also a $sigma$-algebra. However, the union of two $sigma$-algebras may not even be an algebra. In many instances, given an arbitrary collection of subsets of $Omega$, one would like to extend it to a $sigma$-algebra by adding extra subsets of $Omega$ as few as possible. This leads to the following definition.

#definition[$sigma$-algebra Generated by Sets][
  If $cal(A) subset 2^Omega$, then the #strong[$sigma$-algebra generated by] $cal(A)$, denoted by $sigma (cal(A))$, is defined as
  $ sigma (cal(A)) = inter.big_(cal(F) in cal(I) (cal(A))) cal(F) $ where
  $
    cal(I) (cal(A)) = { cal(F) : cal(A) subset cal(F) "and" cal(F) "is a" sigma "-algebra defined on" Omega }
  $
  is the collection of all $sigma$-algebras containing the class $cal(A)$.
]
Note that since the power set $2^Omega$ contains $cal(A)$ and is itself a $sigma$-algebra defined on $Omega$, the collection $cal(I) (cal(A))$ is not empty and hence, the intersection in the above definition is well defined.

#definition[Borel $sigma$-algebra][
  The #strong[Borel $sigma$-algebra] on a topological space $bb(S)$ is defined as the $sigma$-algebra generated by the collection of open sets in $bb(S)$.
]
#example[
  Let $cal(B) (bb(R)^k)$ denote the Borel $sigma$-algebra on the Euclidean space $bb(R)^k$ with standard topology, $1 lt.eq k < + oo$. Then, $cal(B) (bb(R)^k) = sigma ({ A : A upright("is an open subset of") bb(R)^k })$ is also generated by each of the following classes of sets $ cal(O)_1 & = { (a_1 , b_1) times dots.h.c times (a_k , b_k) : - oo lt.eq a_i < b_i lt.eq + oo , 1 lt.eq i lt.eq k } ; \
  cal(O)_2 & = { (- oo , x_1) times dots.h.c times (- oo , x_k) : x_i in bb(R) , 1 lt.eq i lt.eq k } ; \
  cal(O)_3 & = { (a_1 , b_1) times dots.h.c times (a_k , b_k) : a_i , b_i in bb(Q) , a_i < b_i , 1 lt.eq i lt.eq k } ; \
  cal(O)_4 & = { (- oo , x_1) times dots.h.c times (- oo , x_k) : x_i in bb(Q) , 1 lt.eq i lt.eq k } . \ $

]<borel-sigma-algebra-generated-by-sets>
#definition[$pi$-system][
  A class $cal(C)$ of subsets of $Omega$ is a *$pi$-system* or a *$pi$-class* if
  $
    A , B in cal(C) arrow.r.double.long A inter B in cal(C) .
  $
]
#example[
  The classes $cal(O)_i med (i = 1 , 2 , 3 , 4)$ in @borel-sigma-algebra-generated-by-sets are all $pi$-systems.
]


#definition[$lambda$-system][
  A class $cal(L)$ of subsets of $Omega$ is a *$lambda$-system* or a *$lambda$-class* if

  + $Omega in cal(L)$,

  + $A , B in cal(L) , A subset B arrow.r.double.long B \\ A in cal(L)$,

  + $A_n in cal(L) , A_n subset A_(n + 1)$ for all $n gt.eq 1$ $arrow.r.double.long A_n in cal(L)$ for $n gt.eq 1$.

]

#example[
  Every $sigma$-algebra is a $lambda$-system.
]
#theorem[
  If $cal(C)$ is a $pi$-system, then $lambda (cal(C)) = sigma (cal(C))$.
]

== Measurable Space <measurable-space>
#definition[Measurable space][
  Given a nonempty set $Omega$ and a $sigma$-algebra $cal(F)$ on $Omega$, the tuple $(Omega , cal(F))$ is called a #strong[measurable space];.

]
#definition[Measurable Map][
  Given two measurable spaces $(Omega , cal(F))$ and $(S , cal(S))$, the map $f : Omega arrow.r S$ is $cal(F) \/ cal(S)$-#strong[measurable] if
  $
    f^(-1) (B) in cal(F) , quad forall B in cal(S).
  $
  We say $f$ is measurable if the underlying $sigma$-algebras $cal(F)$ and $cal(S)$ are self-evident.
]
Note $f^(- 1)$ preserves $sigma$-algebra, which leads to the following definition.

#definition[$sigma$-algebra generated by measurable map][
  Assume $f$ is a measurable map from $(Omega , cal(F))$ to $(S , cal(S))$. The $sigma$-algebra generated by $f$ is defined as
  $
    sigma (f) := sigma (f^(- 1) (cal(S))) = f^(- 1) (cal(S)) .
  $

]
$sigma (f)$ is the smallest $sigma$-algebra on $Omega$ such that $f$ is $cal(F) \/ cal(S)$-measurable;. That is,
$
  f "is" cal(F)\/cal(S)"-measurable" ==> sigma(f)subset.eq cal(F).
$

#definition[Tensor Product $sigma$-algebra][
  Let $(Omega_1 , cal(F)_1)$ and $(Omega_2 , cal(F)_2)$ be two measurable spaces. Denote by $cal(F)_1 times.circle cal(F)_2$ the $sigma$-algebra on the Cartesian product $Omega_1 times Omega_2$ generated by subsets of the form $B_1 times B_2$, where $B_1 in cal(F)_1$ and $B_2 in cal(F)_2$, i.e., $ cal(F)_1 times.circle cal(F)_2 = sigma ({B_1 times B_2 : B_1 in cal(F)_1 , B_2 in cal(F)_2}) . $

]
#definition[Product Measurable Space][
  Let $(Omega_1 , cal(F)_1)$ and $(Omega_2 , cal(F)_2)$ be two measurable spaces. The #strong[product measurable space] of $(Omega_1 , cal(F)_1)$ and $(Omega_2 , cal(F)_2)$ is defined as $(Omega_1 times Omega_2 , cal(F)_1 times.circle cal(F)_2)$.
]
#definition[Infinite Product Measurable Space][
  Let ${ (Omega_i , cal(F)_i) }_(i in T)$ be a collection of measurable spaces. The #strong[infinite product measurable space] of ${ (Omega_i , cal(F)_i) }_(i in T)$ is defined as $(product_(i in T) Omega_i , times.circle.big_(i in T) cal(F)_i)$, where $ cal(M C) ({ cal(F)_i }_(i in T)) := {product_(i in T) B_i : B_i in cal(F)_i , #h(0em) B_i = Omega_i "for all but a finite number of" i in T} $ is called the collection of #strong[measurable cylinders] and $ times.circle.big_(i in T) cal(F)_i = sigma (cal(M C) ({ cal(F)_i }_(i in T))) . $
]
Product measurable space is the product in the category consisting of all measurable spaces and measurable functions and satisfies the following universal property: for every cone consisting of a measurable space $Y$ and a family of measurable functions ${ f_i : Y arrow.r Omega_i }_(i in T)$, there exists a unique measurable function
$
  f : Y & --> product_(i in T) Omega_i , \
      y & arrow.r.bar.long (f_i (y))_(i in T)
$
denoted by $product_(i in T) f_i$ such that the following diagrams commute for all $i$ in $T$,
//
//
//  \$\$\\xymatrix{
// Y\\ar\@{--\>}\[r\]^{\\exists!f\\quad}\\ar\[rd\]\_{f\_i} &\\prod\\limits\_{i\\in T}\\ar\[d\]^{\\pi\_i}\\Omega\_i\\\\
// &\\Omega\_i
// }\$\$ where $pi_i : (omega_k)_(k in T) arrow.r.bar omega_i$ is the projection map. Thus we see that $times.circle.big_(i in T) cal(F)_i$ is the smallest $sigma$-algebra on $product_(i in T) Omega_i$ such that every projection map $pi_i$ is measurable, that is $ times.circle.big_(i in T) cal(F)_i = sigma (union.big_(i in T) sigma (pi_i)) . $ Generally, we have the following proposition.

#proposition[
  $ sigma (product_(i in T) f_i) = sigma (union.big_(i in T) sigma (f_i)) . $
]

#proposition[Product and Borel $sigma$-fields][
  Let ${ S_i }_(i = 1)^oo$ be a sequence of separable metric spaces. Then
  $
    cal(B) (product_(i = 1)^oo S_i) = times.circle.big_(i = 1)^oo cal(B) (S_i).
  $
]
In particular, $cal(B) (bb(R)^d) = (cal(B) (bb(R)))^d$.

#proposition[Convergence and Limits][
  Let $f_1 , f_2 , dots.h$ be measurable functions from a measurable space $(Omega , cal(F))$ into some metric space $(S , rho) .$ Then

  + ${omega in Omega : f_n (omega) "converges"} in cal(A)$ if $S$ is complete;

  + $f_n arrow.r f$ on $Omega$ implies that $f$ is measurable.

]
#example[Bounded Measurable Real Functions][
  Let $(Omega , cal(F))$ be a measurable space. The set of bounded measurable real functions on $Omega$ with norm $normdot_oo$ defined by
  $
    norm(f)_oo:= sup_(omega in Omega) abs(f(omega))
  $
  is a Banach space over $bb(R)$ and is denoted by $upright(B M)(Omega, cal(F))$.
]


== Measure <measure>
#definition[Measure][
  Given a measurable space $(Omega , cal(F))$, a set function $mu : cal(F) arrow.r [0 , + oo]$ is called a #strong[measure] if

  + $mu (diameter) = 0$;

  + $sigma$-additivity: for any countable collection ${ A_i }_(i = 1)^oo$ of pairwise disjoint sets in $cal(F)$, $ mu (union.big_(n = 1)^oo A_n) = sum_(n = 1)^oo mu (A_n) . $

]
#definition[Measure Space][
  is a triple $(Omega , cal(F) , mu)$ where $Omega$ is a set, $cal(F)$ is a $sigma$-algebra on $Omega$ and $mu : cal(F) arrow.r [0 , + oo]$ is a measure.
]

#proposition[
  Suppose $(Omega , cal(F) , mu)$ is a measure space.

  + Monotonicity: If $A , B in cal(F)$ and $A subset B$, then $mu (A) lt.eq mu (B)$;

  + Subadditivity: For any measurable sets ${ A_n }_(n = 1)^oo$ in $cal(F)$, $ mu (union.big_(n = 1)^oo A_n) lt.eq sum_(n = 1)^oo mu (A_n) $

  + Continuity from below: If ${ A_n }_(n = 1)^oo$ is a collection of sets in $cal(F)$ that are increasing (meaning that $A_1 subset A_2 subset A_3 subset dots.h.c$ ) then the union of the sets $A_n$ is measurable and $ mu (union.big_(n = 1)^oo A_n) = mu (lim_(n arrow.r oo) A_n) = lim_(n arrow.r oo) mu (A_n) = sup_(n gt.eq 1) mu (A_n) ; $

  + Continuity from above: If ${ A_n }_(n = 1)^oo$ is a collection of sets in $cal(F)$ that are decreasing (meaning that $A_1 supset A_2 supset A_3 supset dots.h.c$ ) then the intersection of the sets $A_n$ is measurable. Furthermore, if at least one of the $A_n$ has finite measure then $ mu (inter.big_(n = 1)^oo A_n) = mu (lim_(n arrow.r oo) A_n) = lim_(n arrow.r oo) mu (A_n) = inf_(n gt.eq 1) mu (A_n) . $
]

#corollary[
  Suppose $(Omega , cal(F) , mu)$ is a measure space.

  + If ${ A_n }_(n = 1)^oo$ is a collection of sets in $cal(F)$, then $ mu (lim_(n arrow.r oo) A_n) = lim_(n arrow.r oo) mu (inter.big_(k = n)^oo A_k) lt.eq lim_(n arrow.r oo) mu (A_n) ; $

  + If ${ A_n }_(n = 1)^oo$ is a collection of sets in $cal(F)$, and $mu (A_n)$ is finite for all $n gt.eq 1$, $ mu (lim_(n arrow.r oo) A_n) = lim_(n arrow.r oo) mu (union.big_(k = n)^oo A_k) gt.eq lim_(n arrow.r oo) mu (A_n) . $

]
#definition[Pre-measure][
  Let $cal(S)$ be a semiring on $Omega$. A set function $mu_0 : cal(S) arrow.r [0 , + oo]$ is called a #strong[pre-measure] if

  + $mu_0 (diameter) = 0$;

  + $sigma$-additivity: for any countable collection ${ A_i }_(i = 1)^oo$ of pairwise disjoint sets in $cal(S)$, $ mu_0 (union.big_(n = 1)^oo A_n) = sum_(n = 1)^oo mu_0 (A_n) . $
]<pre-measure>
Clearly we see every measure is a pre-measure, since every $sigma$-algebra is a semiring.

#definition[$sigma$-finite Measure][
  Let $(Omega , cal(F))$ be a measurable space and $mu$ a measure on it. The measure $mu$ is called a #strong[$sigma$-finite measure] if the set $Omega$ can be covered with at most countably many measurable sets with finite measure, which means that there are sets $A_1 , A_2 , dots.h in cal(F)$ with $mu (A_n) < oo$ for all $n in bb(N_(+))$ that satisfy $ union.big_(n = 1)^oo A_n = Omega . $
]

*$sigma$-finite Pre-measure* can be defined in a similar way.

#definition[Finite Measure][
  Let $(Omega , cal(F))$ be a measurable space and $mu$ a measure on it. The measure $mu$ is called a #strong[finite measure] if $mu (Omega) < oo$.
]
#definition[Probability Measure][
  Let $(Omega , cal(F))$ be a measurable space and $mu$ a measure on it. The measure $mu$ is called a #strong[probability measure] if $mu (Omega) = 1$. In this case, $(Omega , cal(F) , mu)$ is called a #strong[probability measure space] or #strong[probability space] in short.
]
#example[Dirac Measure][
  Let $(Omega , cal(F))$ be a measurable space. For any $x in Omega$, the #strong[Dirac measure] $delta_x$ is defined by
  $
    delta_x (A) = upright(bold(1))_A (x) = cases(
      1\, & x in A\,, ,
      0\, & x in.not A .
    )
  $
]
#definition[Complete Measure][
  A measure $mu$ defined on the measurable space $(Omega , cal(F))$ is called #strong[complete] if for any $A in cal(F)$ with $mu (A) = 0$, $2^A subset cal(F)$. In this case, the measure space $(Omega , cal(F) , mu)$ is called a complete measure space.
]
#definition[Borel Measure][
  Suppose $cal(B) (bb(S))$ is the Borel $sigma$-algebra on a topological space $bb(S)$. A #strong[Borel measure] is measure defined on the measurable space $(bb(S) , cal(B) (bb(S)))$.
]

#definition[$mu$-null Set][
  Given a measure space $(Omega , cal(F) , mu)$, a set $A in cal(F)$ is called a $mu$-null set is $mu (A) = 0$.

]
#definition[Extension of a Measure Space][
  The measure space $(Omega , tilde(cal(F)) , tilde(mu))$ is called the extension of the measure space $(Omega , cal(F) , mu)$ if $cal(F) subset tilde(cal(F))$ and $tilde(mu)|_(cal(F)) = mu$.
]

#proposition[
  Given a measure space $(Omega , cal(F) , mu)$, define $ tilde(cal(F)) = { A union E in 2^Omega divides A in cal(F) , E upright(" is a subset of a ") mu upright("-null set") } $ and $ tilde(mu) : tilde(cal(F)) & arrow.r [0 , + oo] , \
                  A union E & arrow.r.bar mu (A) . $ Then we have

  + $tilde(mu)$ is well-defined,

  + $(Omega , tilde(cal(F)) , tilde(mu))$ is a complete measure space,

  + $tilde(mu)$ is the unique measure on $(Omega , tilde(cal(F)))$ that coincides with $mu$ on $cal(F)$,

  + $(Omega , tilde(cal(F)) , tilde(mu))$ is the smallest complete extension of $(Omega , cal(F) , mu)$.
]
#definition[Completion of a Measure Space][
  Given a measure space $(Omega , cal(F) , mu)$, define $ tilde(cal(F)) = { A union E in 2^Omega divides A in cal(F) , E upright(" is a subset of a ") mu upright("-null set") } $ and
  $
    tilde(mu) : tilde(cal(F)) & arrow.r [0 , + oo] , \
                    A union E & arrow.r.bar mu (A) .
  $
  The measure space $(Omega , tilde(cal(F)) , tilde(mu))$ is called the #strong[completion of $(Omega , cal(F) , mu)$];.

]
#definition[Outer Measure][
  A set function $mu^* : 2^Omega arrow.r [0 , + oo]$ is called a #strong[outer measure] on $Omega$ if

  + $mu^* (diameter) = 0$;

  + $A subset B subset Omega arrow.r.double.long mu^* (A) lt.eq mu^* (B)$;

  + countable subadditivity: for any countable collection ${ A_i }_(i = 1)^oo$ of sets in $2^Omega$, $ mu^* (union.big_(n = 1)^oo A_n) lt.eq sum_(n = 1)^oo mu^* (A_n) . $
]<outer-measure>
#definition[$mu^*$-measurable][
  Suppose that $mu^*$ is an #link(<outer-measure>)[outer measure] on $Omega$. A set $A$ is said to be #strong[$mu^*$-measurable] if
  $
    mu^* (E) = mu^* (E inter A) + mu^* (E inter A^c) upright("for all") E subset Omega .
  $
]
#proposition[Construction of a Measure from an Outer Measure][
  Let $Omega$ be a set, let $mu^*$ be an #link(<outer-measure>)[outer measure] on $Omega$, and let $cal(M)_(mu^*)$ be the collection of all $mu^*$-measurable subsets of $Omega$. Then

  + $cal(M)_(mu^*)$ is a $sigma$-algebra,

  + the restriction of $mu^*$ to $cal(M)_(mu^*)$ is a measure on $cal(M)_(mu^*)$,

  + $(Omega , cal(M)_(mu^*) , mu^* \|_(cal(M)_(mu^*)))$ is a complete measure space.

]
#definition[Induced Outer Measure][
  Given a pre-measure $mu_0$ on a semialgebra, $cal(S) subset.eq 2^Omega$, the #strong[outer measure induced by $mu_0$] is the set function $mu_0^* : 2^Omega arrow.r [0 , + oo]$, as $ mu_0^* (A) = inf {sum_(n = 1)^oo mu_0 (A_n) : {A_n}_(n gt.eq 1) subset cal(S) , A subset.eq union.big_(n gt.eq 1) A_n} . $

  Especially, given a measure $mu$ on a measurable space $(Omega , cal(F))$, the #strong[outer measure induced by $mu$] is the set function $mu^* : 2^Omega arrow.r [0 , + oo]$, defined as $ mu^* (A) = inf {mu (C) : C in cal(F) , A subset C} . $

]

#theorem[Carathéodory's Extension Theorem][
  Let $cal(C)$ be a semialgebra on $Omega$, let $mu_0 : cal(C) arrow.r [0 , + oo]$ be a pre-measure and let $mu_0^*$ be the outer measure induced by $mu_0$. Then

  + $cal(C) subset.eq sigma (cal(C)) subset.eq cal(M)_(mu_0^*)$, where $cal(M)_(mu_0^*)$ denotes the collection of all $mu_0^*$-measurable subsets of $Omega$,

  + $mu_0^* \|_(cal(C)) = mu_0$,

  + $(Omega , sigma (cal(C)) , mu_0^* \|_(sigma (cal(C))))$ is a measure space. $(Omega , cal(M)_(mu_0^*) , mu_0^* \|_(cal(M)_(mu_0^*)))$ is a complete measure space,

  + If $mu_0$ is $sigma$-finite, then

    #block[
      #set enum(numbering: "(a)", indent: 0em)

      + $mu_0^* \|_(sigma (cal(C)))$ is the unique measure on $(Omega , sigma (cal(C)))$ that coincides with $mu_0$ on $cal(C)$. In this case, $mu_0^* \|_(sigma (cal(C)))$ is also $sigma$-finite,

      + $(Omega , cal(M)_(mu_0^*) , mu_0^* \|_(cal(M)_(mu_0^*)))$ is the completion of $(Omega , sigma (cal(C)) , mu_0^* \|_(sigma (cal(C))))$,

      + $mu_0^* \|_(cal(M)_(mu_0^*))$ is the unique measure on $(Omega , cal(M)_(mu_0^*))$ that coincides with $mu_0$ on $cal(C)$.
    ]

  For simplicity, $(Omega , sigma (cal(C)) , mu_0^*|_(sigma (cal(C))))$ and $(Omega , cal(M)_(mu_0^*) , mu_0^*|_(cal(M)_(mu_0^(*))))$ can be denoted as $(Omega , sigma (cal(C)) , mu_0^(*))$ and $(Omega , cal(M)_(mu_0^(*)) , mu_0^(*))$.

]<caratheodory-extension-theorem>

=== Product Measure <product-measure>
#definition[Product Measure][
  Let $(Omega_1 , cal(F)_1 , mu_1)$ and $(Omega_2 , cal(F)_2 , mu_2)$ be two measure spaces. A measure $mu$ on the measurable space $(Omega_1 times Omega_2 , cal(F)_1 times.circle cal(F)_2)$ is said to be a #strong[product measure] of $mu_1$ and $mu_2$ if it satisfies the property
  $
    mu (B_1 times B_2) = mu_1 (B_1) mu_2 (B_2)
  $
  for all $B_1 in Omega_1$, $B_2 in Omega_2$. In this case, the measure space $(Omega_1 times Omega_2 , cal(F)_1 times.circle cal(F)_2 , mu)$ is called the product measure space of $(Omega_1 , cal(F)_1 , mu_1)$ and $(Omega_2 , cal(F)_2 , mu_2)$.

]
#proposition[Existence and Uniqueness of Product Measure][
  Let $(Omega_1 , cal(F)_1 , mu_1)$ and $(Omega_2 , cal(F)_2 , mu_2)$ be two measure spaces.

  + There exists a unique product measure $mu_1 times_max mu_2$ on $(Omega_1 times Omega_2 , cal(F)_1 times.circle cal(F)_2)$ satisfying the following property: if $(mu_1 times_max mu_2) (A)$ is finite for some measurable set $A in cal(F)_1 times.circle cal(F)_2$, then for any product measure $mu$ on $(Omega_1 times Omega_2 , cal(F)_1 times.circle cal(F)_2)$,
    $
      mu (A) = (mu_1 times_max mu_2) (A).
    $
    $mu_1 times_max mu_2$ is called the *maximal product measure* of $mu_1$ and $mu_2$.

  + If the measure $mu_1$ and $mu_2$ are $sigma$-finite, then $mu_1 times_max mu_2$ is the unique product measure of $mu_1$ and $mu_2$ and we denote $mu_1 times_max mu_2$ by $mu_1 times mu_2$.
]
#proof[
  + Let
    $
              cal(R)_(X , Y) & := {A times B in cal(F)_1 times.circle cal(F)_2 mid(|) A in cal(F)_1 , B in cal(F)_2} , \
      cal(U)(cal(R)_(X , Y)) & := {union.big_(k=1)^n C_k mid(|) n in ZZ_(>=0), med C_k in cal(R)_(X , Y) } .
    $
    Here we use the convention that $limits(union.big)_(k=1)^0 C_k = emptyset$. It is straightforward to check $cal(U)(cal(R)_(X , Y))$ is an #link(<algebra-of-sets-1>)[algebra of sets] defined on $Omega_1 times Omega_2$. Define a #link(<pre-measure>)[pre-measure]
    $
              mu_0: cal(U)(cal(R)_(X , Y)) & --> [0 , + oo] \
      union.plus.big_(k=1)^n A_k times B_k & mapsto.long sum_(k=1)^n mu_1 (A_k) mu_2 (B_k)
    $
    Here $union.plus$ means it is a union of pairwise disjoint sets. $mu$ induces an outer measure $mu_0^*$ on $Omega_1 times Omega_2$. Note that $sigma(cal(U)(cal(R)_(X , Y)))=cal(F)_1 times.circle cal(F)_2$. By #link(<caratheodory-extension-theorem>)[Carathéodory's Extension Theorem], it follows that $(Omega , cal(F)_1 times.circle cal(F)_2 , mu_0^*\|_(cal(F)_1 times.circle cal(F)_2))$ is a measure space. Let $mu_1 times_max mu_2:=mu_0^*\|_(cal(F)_1 times.circle cal(F)_2)$. It clear that $mu_1 times_max mu_2$ is a product measure of $mu_1$ and $mu_2$.

  + If $mu_1$ and $mu_2$ are $sigma$-finite, then $mu_0$ is also $sigma$-finite. If $mu'$ is a product measure of $mu_1$ and $mu_2$, then $mu'$ must coincide with $mu_0$ on $cal(U)(cal(R)_(X , Y))$. By #link(<caratheodory-extension-theorem>)[Carathéodory's Extension Theorem], $mu_1 times_max mu_2$ is the unique measure on $(Omega , cal(F)_1 times.circle cal(F)_2)$ that coincides with $mu_0$ on $cal(U)(cal(R)_(X , Y))$. Thus, we have $mu'=mu_1 times_max mu_2$.
]
#definition[Product Probability Measure][
  Let ${ (Omega_i , cal(F)_i , upright(P)_i) }_(i in T)$ be a collection of probability measure spaces. The map
  $
    upright(P)_0 : cal(M C) ({ cal(F)_i }_(i in T)) & --> [0 , 1]\
    product_(i in T) B_i & arrow.r.bar.long product_(i in T : upright(P)_i (B_i) < 1) upright(P)_i (B_i)
  $
  can be uniquely extended to a probability measure $upright(P)$ on the product measurable space $(product_(i in T) Omega_i , times.circle.big_(i in T) cal(F)_i)$. The #strong[product probability space] of ${ (Omega_i , cal(F)_i , upright(P)_i) }_(i in T)$ is defined as $(product_(i in T) Omega_i , times.circle.big_(i in T) cal(F)_i , upright(P))$.
]

#theorem[Fubini-Tonelli Theorem][
  Let $(Omega_1 , cal(F)_1 , mu_1)$ and $(Omega_2 , cal(F)_2 , mu_2)$ be two $sigma$-finite measure spaces. Let $mu = mu_1 times mu_2$ be the product measure of $mu_1$ and $mu_2$. Suppose $f : Omega_1 times Omega_2 arrow.r Y$ is a $cal(F)_1 times.circle cal(F)_2$-measurable function. Then the function
  $
    f(omega_1,dot.c): Omega_2 & --> Y, \
                      omega_2 & arrow.long.bar f (omega_1 , omega_2)
  $
  is $cal(F)_2$-measurable. The function
  $
    f(dot.c, omega_2): Omega_1 & --> Y, \
                       omega_1 & arrow.long.bar f (omega_1 , omega_2).
  $
  is $cal(F)_1$-measurable.

  + (Tonelli) If $f(Omega_1 times Omega_2)subset.eq [0 , + oo]$,

    - The function
      $
        g: Omega_1 & --> [0 , + oo], \
           omega_1 & arrow.long.bar integral_(Omega_2) f (omega_1 , omega_2) dif mu_2 (omega_2)
      $
      is $cal(F)_1$-measurable.

    - The function
      $
        h: Omega_2 & --> [0 , + oo], \
           omega_2 & arrow.long.bar integral_(Omega_1) f (omega_1 , omega_2) dif mu_1 (omega_1)
      $
      is $cal(F)_2$-measurable.

    - $
        integral_(Omega_1 times Omega_2) f dif mu & = integral_(Omega_1) (integral_(Omega_2) f (omega_1 , omega_2) dif mu_2 (omega_2)) dif mu_1 (omega_1)\
        & = integral_(Omega_2) (integral_(Omega_1) f (omega_1 , omega_2) dif mu_1 (omega_1)) dif mu_2 (omega_2) .
      $


  + (Fubini) If $f in L^1(mu)$, then

    - $f(omega_1,dot.c) in L^1(mu_2)$ for $mu_1$-almost every $omega_1 in Omega_1$. So the function
      $
        g: Omega_1 & --> CC, \
           omega_1 & arrow.bar.long integral_(Omega_2) f (omega_1 , omega_2) dif mu_2 (omega_2)
      $
      is well-defined for $mu_1$-almost every $omega_1 in Omega_1$.

    - $f(dot.c, omega_2) in L^1(mu_1)$ for $mu_2$-almost every $omega_2 in Omega_2$. So the function
      $
        h: Omega_2 & --> CC, \
           omega_2 & arrow.long.bar integral_(Omega_1) f (omega_1 , omega_2) dif mu_1 (omega_1)
      $
      is well-defined for $mu_1$-almost every $omega_1 in Omega_1$ and

    - $g in L^1(mu_1)$ and $h in L^1(mu_2)$.


    - $
        integral_(Omega_1 times Omega_2) f dif mu & = integral_(Omega_1) (integral_(Omega_2) f (omega_1 , omega_2) dif mu_2 (omega_2)) dif mu_1 (omega_1)\
        & = integral_(Omega_2) (integral_(Omega_1) f (omega_1 , omega_2) dif mu_1 (omega_1)) dif mu_2 (omega_2) .
      $
]<fubini-tonelli-theorem>
#definition[Measurable Semigroup][
  Let $G$ be a semigroup and $(G , cal(F))$ be a measurable space. We say that $(G , cal(F))$ is a #strong[measurable semigroup] if the multiplication map $ m : G times G & arrow.r G , \
    (g_1 , g_2) & arrow.r.bar g_1 g_2 $ is $cal(F) times.circle cal(F)$-measurable, i.e., $m^(- 1) (B) in cal(F) times.circle cal(F)$ for all $B in cal(F)$.
]
#definition[Convolution of $sigma$-finite Measures][
  Let $(G , cal(F))$ be a measurable semigroup and $mu_1 , mu_2$ be two $sigma$-finite measures on $(G , cal(F))$. The #strong[convolution] of $mu_1$ and $mu_2$, denoted by $mu_1 * mu_2$, is defined as the pushforward measure $ mu_1 * mu_2 := m_(*) (mu_1 times mu_2) . $ More explicitly, for any $A in cal(F)$, we have
  $
    mu_1 * mu_2 (A) & = (mu_1 times mu_2) (m^(- 1) (A)) \
                    & = integral_(G times G) upright(bold(1))_(m^(- 1) (A)) dif (mu_1 times mu_2) \
                    & = integral_(G times G) upright(bold(1))_A (g_1 g_2) dif (mu_1 times mu_2) (g_1 , g_2) \
                    & = integral_G integral_G upright(bold(1))_A (g_1 g_2) dif mu_1 (g_1) dif mu_2 (g_2) .
  $
]


=== Lebesgue-Stieltjes measure <lebesgue-stieltjes-measure>
#definition[Lebesgue-Stieltjes Measure on $bb(R)$][
  Given nondecreasing function $F : bb(R) arrow.r bb(R)$ and semialgebra $ cal(C) equiv { ( a , b \] in bb(R) divides - oo lt.eq a lt.eq b < oo } union { (a , oo) in bb(R) divides - oo lt.eq a < oo } $ we can define a pre-measure $mu_F$ on $cal(C)$ as follows
  $
    mu_F ( (a , b \]) & = F (b +) - F (a +) , \
      mu_F ((a , oo)) & = F (oo) - F (a +) .
  $
  The measure space $(bb(R) , cal(M)_(mu_F^(*)) , mu_F^(*))$ is called a #strong[Lebesgue-Stieltjes measure space] and $mu_F^(*)$ is the #strong[Lebesgue-Stieltjes measure] generated by $F$.
]


=== Radon measure <radon-measure>
#definition[Radon Measure][
  Let $(X , tau)$ be a Hausdorff topological space and $cal(B) (X)$ be the Borel $sigma$-algebra on $X$. A measure $mu$ on $(X , cal(B) (X))$ is called a #strong[Radon measure] if

  + (locally finite) for any $x in X$, there exists a neighborhood $U$ of $x$ such that $mu (U) < oo$.

  + (inner regularity for Borel sets) for any $B in cal(B) (X)$, $ mu (B) = sup { mu (K) : K subset.eq B , K "is compact" } ; $


]
#remark[
  In some literature, we define Radon measure as a measure $m$ on $(X , cal(B) (X))$ that satisfies the following conditions:

  + (locally finite) for any $x in X$, there exists a neighborhood $U$ of $x$ such that $m (U) < oo$.

  + (inner regularity for open sets) for any $U in tau$, $ m (U) = sup { m (K) : K subset.eq U , K "is compact" } ; $

  + (outer regularity for Borel sets) for any $B in cal(B) (X)$, $ m (B) = inf { m (U) : U supset.eq B , U "is open" } . $

  Let's call the Borel measures that satisfy (1) and (2) #strong[type-1 Radon measures] and the Borel measures that satisfy (1$'$), (2$'$) and (3$'$) #strong[type-2 Radon measures];. There is a bijection between these two classes of Radon measures,
  $
    { "type-1 Radon measures on" (X , cal(B) (X)) } & arrow.r.long^tilde.op { "type-2 Radon measures on" (X , cal(B) (X)) }\
    mu & arrow.r.bar.long (B arrow.r.bar.long inf {mu (U) : U supset.eq B , U "is open"})\
    (B arrow.r.bar.long sup {m (B') : B' subset.eq B , B' "is Borel" , m(B') "is finite"}) & arrow.l.long.bar m
  $

]
If $m$ is locally finite, then it follows that $m$ is finite on compact sets, and for locally compact Hausdorff spaces, the converse holds, too. Thus, in this case, local finiteness may be equivalently replaced by finiteness on compact subsets.

#proposition[
  Let $(X , tau)$ be a locally compact Hausdorff topological space and $cal(B) (X)$ be the Borel $sigma$-algebra on $X$. Then a measure $mu$ on $(X , cal(B) (X))$ is a Radon measure if and only if it satisfies the following conditions:

  + $mu$ is finite on all compact subsets of $X$.

  + (inner regularity for open sets) for any open set $U in tau$, $ mu (U) = sup { mu (K) : K subset.eq U , K "is compact" } ; $

  + (outer regularity for Borel sets) for any $B in cal(B) (X)$, $ mu (B) = inf { mu (U) : U supset.eq B , U "is open" } . $


]
#definition[Finite Signed Radon Measure][
  Let $(X , tau)$ be a Hausdorff topological space and $cal(B) (X)$ be the Borel $sigma$-algebra on $X$. A finite signed measure $mu$ on $(X , cal(B) (X))$ is called a #strong[finite signed Radon measure] if $mu^(+)$ and $mu^(-)$ are Radon measures, where $mu^(+)$ and $mu^(-)$ are the positive and negative parts of $mu$, respectively.
]
#definition[Complex Radon Measure][
  Let $(X , tau)$ be a Hausdorff topological space and $cal(B) (X)$ be the Borel $sigma$-algebra on $X$. A complex measure $mu$ on $(X , cal(B) (X))$ is called a #strong[complex Radon measure] if both its real part and imaginary part are finite signed Radon measures.
]

#example[Banach Space of Complex Radon Measures][
  Let $X$ be a locally compact Hausdorff space. Then the space of all complex Radon measures on $X$ is denoted as $M_("Rad")(X; CC)$. This is a Banach space with respect to the total variation norm
  $
    ||dot.c||: M_("Rad")(X; CC) & --> [0, oo) \
                             mu & arrow.long.bar norm(mu)=|mu|(X).
  $
]



#lemma[
  Let $G$ be a locally compact Hausdorff topological group and $M_("Rad")(X; CC)$ be the set of complex Radon measures on $(G,cal(B)(G))$. Given two complex measures $mu_1 , mu_2 in M_("Rad")(X; CC)$, define
  $
    I: C_0(G; CC) & --> CC \
                f & arrow.long.bar integral_G integral_G f(x y) dif mu_1(x) dif mu_2(y)
  $
  Then  $I$ is a continuous linear functional on $C_0(G; CC)$ and we have
  $
    abs(I(f)) <= norm(f)_oo norm(mu_1) norm(mu_2).
  $
]<bounded-linear-functional-from-convolution-of-measure>

#definition[Convolution of Complex Radon Measures][
  Let $(G , cal(B) (G))$ be a locally compact Hausdorff topological group and $M_("Rad")(X; CC)$ be the set of complex Radon measures on $G$. Given two complex measures $mu_1 , mu_2 in M_("Rad")(X; CC)$, define
  $
    I: C_0(G; CC) & --> CC \
                f & arrow.long.bar integral_G integral_G f(x y) dif mu_1(x) dif mu_2(y)
  $
  and we see $I in C_0(G; CC)'$ according to @bounded-linear-functional-from-convolution-of-measure. By #link(<riesz-markov-kakutani-representation-theorem-for-complex-radon-measure>)[Riesz-Markov-Kakutani representation theorem], there exists a unique complex Radon measure on $(G , cal(B) (G))$, which we denote by $mu_1 * mu_2$, such that
  $
    I(f) = integral_G f dif (mu_1 * mu_2), quad forall f in C_0(G; CC).
  $
  $mu_1 * mu_2$ is called the *convolution* of $mu_1$ and $mu_2$.
]
If $g in C_c ( X )$ and $h in C_c ( Y )$, define
$
  g times.circle h: X times Y & --> CC \
                        (x,y) & mapsto.long g(x) h(y)
$

#proposition[
  Suppose $X$ and $Y$ are locally compact Hausdorff spaces.

  + $cal(B) (X) times.circle cal(B) (Y) subset.eq cal(B) (X times Y)$.

  + If $X$ and $Y$ are second countable, then

    - $cal(B) (X) times.circle cal(B) (Y) = cal(B) (X times Y)$.

    - Given any Radon measure $mu$ on $X$ and any Radon measure $nu$ on $Y$, the maximal product measure $mu times_max nu$ is a Radon measure on $X times Y$.
]

If $X$ or $Y$ is not second countable, it is likely that $cal(B) (X) times.circle cal(B) (Y) subset.neq cal(B) (X times Y)$. So generally $mu times_max nu$ is not a Radon measure on $X times Y$. However, there exists a natural way to extend $mu times_max nu$ to a Radon measure on $X times Y$.

#lemma[][
  Let
  $
    cal(P):=op("span"){ g times.circle h in C_c ( X times.circle Y )mid(|) g in C_c ( X ) \, h in C_c ( Y ) }
  $
  be the vector space spanned by the functions $g times.circle h$ with $g in C_c ( X )$, $h in C_c ( Y )$. Then $cal(P)$ is dense in $C_c ( X times.circle Y )$ in the uniform norm. More precisely, given any $f in C_c ( X times Y )$, any $epsilon.alt > 0$, and any precompact open sets $U subset.eq X$ and $V subset.eq Y$ containing $pi_X ( op("supp") ( f ) )$ and $pi_Y ( op("supp") ( f ) )$, there exists $F in cal(P)$ such that $norm(F - f)_("sup") < epsilon.alt$ and
  $op("supp") ( F ) subset.eq U times V$.

]<uniform-approximation-for-functions-on-product-spaces-with-compact-support>
#proof[
  $macron(U) times macron(V)$ is a compact Hausdorff space. It
  follows easily from the Stone-Weierstrass theorem that
  $
    cal(Q):=op("span"){ g times.circle h mid(|) g in C ( macron(U) ) \, h in C ( macron(V) ) }
  $
  is dense in $C ( macron(U) times macron(V) )$. In particular, since $f in C ( macron(U) times macron(V) )$, there is
  an element
  $
    G =sum_(k=1)^n g_k times.circle h_k in cal(Q),quad g_k in C ( macron(U) ) \, h_k in C ( macron(V) )
  $
  such that
  $
    sup_((x,y) in macron(U) times macron(V)) abs(G(x,y) - f(x,y)) < epsilon.alt.
  $
  Also, by Urysohn's lemma there exist $phi.alt in C_c (U, [0,1])$ and
  $psi in C_c (V, [0,1])$ such that $phi.alt = 1$ on
  $pi_X ( op("supp") ( f ) )$ and $psi = 1$ on
  $pi_Y ( op("supp") ( f ) )$. Thus if we define
  $
    F(x,y) = cases(
      phi.alt(x)psi(y)G(x,y)=display(limits(sum))_(k=1)^k g_k (x)phi.alt(x) h_k (y)psi(y) \, & quad z in macron(U) times macron(V)\,, ,
      0 \, & quad "otherwise"\,
    )
  $
  we have $F in cal(P)$ and
  $
    op("supp") ( F ) subset.eq op("supp")(phi.alt) times op("supp") (psi) subset.eq U times V.
  $
  To show $norm(F - f)_("sup") < epsilon.alt$, first note that
  $
    op("supp")(f) subset.eq pi_X ( op("supp") ( f ) ) times pi_Y ( op("supp") ( f ) ) subset.eq U times V.
  $
  From $phi.alt|_(pi_X ( op("supp") ( f ) ))=1$ and $psi|_(pi_Y ( op("supp") ( f ) ))=1$ we see $(phi.alt times.circle psi)|_(op("supp")(f))=1$. If $(x, y) in op("supp")(f)$, then we have
  $
    abs(F(x,y) - f(x,y)) = abs(G(x,y) - f(x,y))< epsilon.alt.
  $
  If $(x, y) in.not op("supp")(f)$, then we have $f(x,y)=0$ and
  $
    abs(F(x,y) - f(x,y)) = abs(F(x,y))<=abs(G(x,y))=abs(G(x,y)-f(x,y))< epsilon.alt.
  $
  Thus, we conclude that $norm(F - f)_("sup") < epsilon.alt$.
]

#proposition[
  Suppose $X$ and $Y$ are locally compact Hausdorff spaces. The following statements hold:

  + Every $f in C_c ( X times Y )$ is $cal(B)_X times.circle cal(B)_Y$-measurable.

  + If $mu$ and $nu$ are Radon measures on $X$ and $Y$, then $C_c ( X times Y ) subset.eq L^1 ( mu times_max nu )$, and

  $
    integral_(X times Y) f dif ( mu times_max nu ) = integral_Y integral_X f dif mu dif nu = integral_X integral_Y f dif nu dif mu, quad forall f in C_c ( X times Y )
  $
]<fubini-tonelli-for-radon-measures-and-compactly-supported-functions>
#proof[
  + Supposef $g in C_c ( X )$ and $h in C_c ( Y )$. We have $g times.circle h := (g compose pi_X) (h compose pi_Y)$, where
    $
      pi_X: X times Y & --> X, \
                (x,y) & mapsto.long x
    $
    is $(cal(B)_X times.circle cal(B)_Y)\/cal(B)_X$-measurable, and
    $
      pi_Y: X times Y & --> Y, \
                (x,y) & mapsto.long y
    $
    is $(cal(B)_X times.circle cal(B)_Y)\/cal(B)_Y$-measurable. Since $g$ and $h$ are continuous, $g compose pi_X$ and $h compose pi_Y$ are $cal(B)_X times.circle cal(B)_Y$-measurable, which implies $g times.circle h$ is $cal(B)_X times.circle cal(B)_Y$-measurable. Thus any function in
    $
      cal(P):=op("span"){ g times.circle h in C_c ( X times.circle Y )mid(|) g in C_c ( X ) \, h in C_c ( Y ) }
    $
    is $cal(B)_X times.circle cal(B)_Y$-measurable. Since pointwise limits of measurable functions are measurable, by @uniform-approximation-for-functions-on-product-spaces-with-compact-support, $f in C_c ( X times Y )$ is $cal(B)_X times.circle cal(B)_Y$-measurable.

  + Every $f in C_c ( X times Y )$ is bounded and supported on a compact set $K subset.eq X times Y$. Since
    $
      (mu times_max nu) (K) <= (mu times_max nu)(pi_X (K) times pi_Y (K))= mu (pi_X (K)) nu (pi_Y (K)) < + oo,
    $
    we have
    $
      integral_(X times Y) |f| dif ( mu times_max nu )<= norm(f)_("sup") (mu times_max nu)(K) < + oo.
    $
    which implies $f in L^1 ( mu times_max nu )$. Fubini's theorem holds for such $f$ even if $mu$ and $nu$ are not $sigma$-finite because one can replace $mu$ and $nu$ by the finite measures $mu|_(pi_X ( op("supp")(f)))$ and $nu|_(pi_Y ( op("supp")(f)))$.
]


#definition[Radon Product of Radon Measures][
  Let $X$ and $Y$ be locally compact Hausdorff spaces, and let $mu$ and $nu$ be Radon measures on $X$ and $Y$ respectively. According to @fubini-tonelli-for-radon-measures-and-compactly-supported-functions,
  $
    I: C_c ( X times Y ) & --> CC \
                       f & mapsto.long integral_(X times Y) f dif ( mu times_max nu )
  $
  is a positive linear functional on $C_c ( X times Y )$. By the #link(<riesz-markov-kakutani-representation-theorem-for-radon-measure>)[Riesz-Markov-Kakutani representation theorem], there exists a unique Radon measure $mu hat(times) nu$ on $(X times Y , cal(B) (X times Y))$ such that
  $
    I(f) = integral_(X times Y) f dif ( mu times_max nu ) = integral_(X times Y) f dif ( mu hat(times) nu ) , quad forall f in C_c ( X times Y )
  $
  $mu hat(times) nu$ is called the *Radon product* of $mu$ and $nu$.
]

#theorem[Fubini-Tonelli Theorem for Radon Products][
  Let $mu$ and $nu$ be
  $sigma$-finite Radon measures on $X$ and $Y$, and let $f:X times Y & --> CC$ be a $cal(B)(X times Y)$-measurable function. Then
  $
    f(x,dot):X & --> CC \
             y & arrow.long.bar f(x,y)
  $
  and
  $
    f(dot, y):Y & --> CC \
              x & arrow.long.bar f(x,y)
  $
  are Borel
  measurable for every $x$ and $y$.

  + If $f gt.eq 0$, then
    $
      g:X & --> CC \
        x & mapsto.long integral_Y f(x,y) dif nu(y)
    $
    and
    $
      h:Y & --> CC \
        y & mapsto.long integral_X f(x,y) dif mu(x)
    $
    are Borel measurable on $X$ and $Y$.

  + If $f in L^1 ( mu hat(times) nu )$, then

    - $f(x,dot) in L^1 ( nu )$ for a.e. $x$,

    - $f(dot, y) in L^1 ( mu )$ for a.e. $y$,

    - $ g:X & --> CC \
        x & mapsto.long integral_Y f(x,y) dif nu(y) $ is in $L^1 ( mu )$.

    - $ h:Y & --> CC \
        y & mapsto.long integral_X f(x,y) dif mu(x) $ is in $L^1 ( nu )$.

  In both cases, we have
  $
    integral_(X times Y) f dif ( mu hat(times) nu ) =integral_Y integral_X f dif mu dif nu = integral_X integral_Y f dif nu dif mu
  $
]<fubini-tonelli-theorem-for-radon-products>

#definition[Measure Algebra][
  Let $G$ be a locally compact Hausdorff topological group and $cal(B) (G)$ be the Borel $sigma$-algebra on $G$. Let $M_("Rad")(X; CC)$ be the set of complex Radon measures on $G$. Then $M_("Rad")(X; CC)$ is a unital Banach algebra with respect to the convolution operation as multiplication and the total variation norm. $M_("Rad")(X; CC)$ is called the #strong[measure algebra] of $G$. The mulitiplicative identity is the Dirac measure $delta_1$ at the identity element of $G$
  $
    delta_1 (A) = upright(bold(1))_A (1) = cases(
      1\, & quad 1 in A\,, ,
      0\, & quad 1 in.not A .
    )
  $
]
#example[
  Let $G$ be a locally compact Hausdorff topological group and $mu$ be a left Haar measure on $G$. Then through the injection
  $
    L^1(G,mu) & --> M_("Rad")(X; CC) \
            f & arrow.long.bar f d mu
  $
  $L^1(G,mu)$ is isometrically isomorphic to a Banach subalgebra of $M_("Rad")(X; CC)$. If $f,g in L^1(G,mu)$, then the convolution of $f dif mu$, $h dif mu$ is again absolutely continuous w.r.t. $mu$, and we have
  $
    (f dif mu) * (h dif mu) = (f * h) dif mu ,
  $
  where
  $
    f * h: G & --> CC, \
           x & arrow.bar.long integral_G f(y) h(y^(-1) x) dif mu(y).
  $
  is the convolution of $f$ and $h$ defined in @L1G-as-cstar-algebra.
]





== Signed Measure <signed-measures>
#definition[Signed Measure][
  Given a measurable space $(Omega , cal(F))$, a set function $mu : cal(F) arrow.r ( - oo , + oo \]$ or $mu : cal(F) arrow.r \[ - oo , + oo )$ is called a #strong[signed measure] if

  + $mu (diameter) = 0$;

  + $sigma$-additivity: for any countable collection ${ A_i }_(i = 1)^oo$ of pairwise disjoint sets in $cal(F)$,
  $
    mu (union.big_(n = 1)^oo A_n) = sum_(n = 1)^oo mu (A_n) .
  $
]
#definition[Finite Signed Measure][
  A signed measure $mu$ on measurable space $(Omega , cal(F))$ is #strong[finite] if $mu (cal(F)) in (- oo , + oo)$.
]<finite-signed-measure>

#example[
  Let $(Omega , cal(F) , mu)$ be a measure space, let $f$ belong to $L^1 (Omega , cal(F) , mu)$, and define a function $nu$ on $cal(F)$ by $nu (A) = integral_A f d mu$. Then the linearity of the integral and the dominated convergence theorem imply that $nu$ is a signed measure on $(Omega , cal(F))$. Note that such a signed measure is the difference of the positive measures $nu_1$ and $nu_2$ defined by $nu_1 (A) = integral_A f^(+) d mu$ and $nu_2 (A) = integral_A f^(-) d mu$.
]
#definition[Positive Set][
  Let $(Omega , cal(F))$ be a measurable space and $mu$ be a signed measure on it.

  + $P$ is a #strong[positive set] for $mu$, or equivalently $P$ is a #strong[$mu$-positive set];, if for every $E in cal(F)$ such that $E subset.eq P$, one has $mu (E) gt.eq 0$.

  + $N$ is a #strong[negative set] for $mu$, or equivalently $N$ is a #strong[$mu$-negative set];, if for every $E in cal(F)$ such that $E subset.eq N$, one has $mu (E) lt.eq 0$.

]
#theorem[Hahn Decomposition Theorem][
  Let $(Omega , cal(F))$ be a measurable space, and let $mu$ be a signed measure on $(Omega , cal(F)) .$ Then there are disjoint subsets $P$ and $N$ of $Omega$ such that $P$ is a positive set for $mu , N$ is a negative set for $mu$, and $Omega = P union N$. Let
  $
    mu^(+) : cal(F) & --> [0 , oo] , \
                  A & arrow.r.bar.long mu (A inter P)
  $
  be the #strong[positive part] of $mu$ and
  $
    mu^(-) : cal(F) & --> [0 , oo] , \
                  A & arrow.r.bar.long - mu (A inter N)
  $
  be the #strong[negative part] of $mu$. Then $mu$ is the difference of two measures, that is $ mu = mu^(+) - mu^(-) , $ at least one of which is finite.

]

#definition[Variation of a Signed Measure][
  The #strong[variation] of the signed measure $mu$ is the measure $lr(|mu|)$ defined by $lr(|mu|) = mu^(+) + mu^(-)$.
]
It is easy to check that
$
  lr(|mu (A)|) lt.eq lr(|mu|) (A) , quad forall A in cal(F) .
$

#definition[Absolutely Continuous][
  Let $(Omega , cal(F))$ be a measurable space, and let $mu$ and $nu$ be signed measures on $(Omega , cal(F))$. Then $nu$ is #strong[absolutely continuous] with respect to $mu$ if for all $A in cal(F)$, $ mu (A) = 0 arrow.r.double.long nu (A) = 0 . $ One usually writes $nu lt.double mu$ to indicate that $nu$ is absolutely continuous with respect to $mu$.
]
#definition[Concentrated on a Measurable Set][
  Let $(Omega , cal(F))$ be a measurable space and $E in cal(F)$.

  + A measure $mu$ on $(Omega , cal(F))$ is #strong[concentrated on] $E$ if $mu (E^c) = 0 .$

  + A signed or complex measure $mu$ on $(Omega , cal(F))$ is #strong[concentrated on] $E$ if the variation $lr(|mu|)$ of $mu$ is concentrated on $E$, or equivalently, if each $cal(F)$-measurable subset $A$ of $E^c$ satisfies $mu (A) = 0$.
]
#definition[Mutually Singular][
  Suppose that $mu$ and $nu$ are measures (or signed measures) on $(Omega , cal(F))$. Then $mu$ and $nu$ are #strong[mutually singular] if there is an $cal(F)$-measurable set $E$ such that $mu$ is concentrated on $E$ and $nu$ is concentrated on $E^c$.
]
One usually writes $mu perp nu$ to indicate that $mu$ and $nu$ are mutually singular.

#theorem[Lebesgue Decomposition Theorem][
  Let $(Omega , cal(F))$ be a measurable space.

  + Let $mu$ be a measure on $(Omega , cal(F))$, and let $nu$ be a $sigma$-finite measure on $(Omega , cal(F))$. Then there are unique measures $nu_a$ and $nu_s$ on $(Omega , cal(F))$ such that
    #block[
      #set enum(numbering: "(a)", indent: 0em)
      + $nu_a lt.double mu$,

      + $nu_s perp mu$,

      + $nu = nu_a + nu_s$.
    ]
    In this case, $nu_a$ and $nu_s$ are $sigma$-finite measures and called the absolutely continuous and singular parts of $nu$.

  + Let $mu$ be a measure on $(Omega , cal(F))$, and let $nu$ be a finite signed measure on $(Omega , cal(F))$. Then there are unique finite signed measures $nu_a$ and $nu_s$ on $(Omega , cal(F))$ such that
    #block[
      #set enum(numbering: "(a)", indent: 0em)
      + $nu_a lt.double mu$,

      + $nu_s perp mu$,

      + $nu = nu_a + nu_s$.
    ]
]

#theorem[Radon-Nikodym Theorem][
  Let $(Omega , cal(F))$ be a measurable space.

  + Let $mu$ and $nu$ be $sigma$-finite measures on $(Omega , cal(F))$. If $v lt.double mu$, then there is an $cal(F)$-measurable function $g : Omega arrow.r$ $\[ 0 , + oo )$ such that $nu (A) = integral_A g dif mu$ holds for each $A in cal(F)$. The function $g$ is unique up to $mu$-almost everywhere equality.

  + Let $mu$ be a $sigma$-finite measure on $(Omega , cal(F))$, and let $nu$ be a finite signed measure on $(Omega , cal(F))$. If $nu lt.double mu$, then there exists unique $g in L^1 (Omega , cal(F) , mu)$ and satisfies $nu (A) = integral_A g dif mu$ for each $A in cal(F)$.
]

== Complex Measure <complex-measure>
#definition[Complex Measure][
  Given a measurable space $(Omega , cal(F))$, a map function $mu : cal(F) arrow.r bb(C)$ is called a #strong[complex measure] if

  + $mu (diameter) = 0$;

  + $sigma$-additivity: for any countable collection ${ A_i }_(i = 1)^oo$ of pairwise disjoint sets in $cal(F)$, $ mu (union.big_(n = 1)^oo A_n) = sum_(n = 1)^oo mu (A_n) . $

]
#definition[Real Part and Imaginary Part of a Complex Measure][
  Let $mu$ be a complex measure on $(Omega , cal(F))$. The #strong[real part] of $mu$, denoted by $op("Re") (mu)$, is defined by $ op("Re") (mu) (A) = op("Re") (mu (A)) , quad forall A in cal(F) . $ The #strong[imaginary part] of $mu$, denoted by $upright(I m) (mu)$, is defined by $ upright(I m) (mu) (A) = upright(I m) (mu (A)) , quad forall A in cal(F) . $ Then both $op("Re") (mu)$ and $upright(I m) (mu)$ are finite signed measures on $(Omega , cal(F))$.

]
#proposition[Unique Decomposition of Complex Measures][
  Let $mu$ be a complex measure on $(Omega , cal(F))$. Then

  + Every complex measure $mu$ decomposes as $ mu = op("Re") (mu) + i #h(0em) upright(I m) (mu) . $

  + The decomposition is unique, meaning that if $ mu = mu_1 + i mu_2 $ where $mu_1$ and $mu_2$ are finite signed measures on $(Omega , cal(F))$, then
    $
      mu_1 = op("Re") (mu) , quad mu_2 = op("Im") (mu) .
    $
]
#proposition[
  Let $mu_1$ and $mu_2$ be finite signed measures on $(Omega , cal(F))$. Then $ mu = mu_1 + i mu_2 $ is a complex measure on $(Omega , cal(F))$.
]
#definition[Variation of a Complex Measure][
  Let $mu$ be a complex measure on $(Omega , cal(F))$. The #strong[variation] of $mu$, denoted by $lr(|mu|)$, is a finite measure on $(Omega , cal(F))$ defined by
  $
    lr(|mu|) (A) := sup {sum_(k = 1)^n abs(mu (A_k)): n in bb(Z)_(gt.eq 1), med A_1 , dots.h , A_n in cal(F) , med A = union.sq.big_(k = 1)^n A_k} .
  $


]
#proposition[Polar Decomposition of Complex Measures][
  Let $mu$ be a complex measure on $(Omega , cal(F))$. Then there exists a measurable function $f : Omega arrow.r bb(C)$ such that $lr(|f|) = 1$ and
  $
    mu (A) = integral_A f thin dif lr(|mu|) , quad forall A in cal(F) .
  $
]
#proof[
  See Rudin's book (Real and complex analysis, p124, theorem 6.12).

]
#proposition[
  Let $mu$ be a complex measure on $(Omega , cal(F))$. Then
  + $
      lr(|op("Re") (mu)|) lt.eq lr(|mu|) , quad lr(|upright(I m) (mu)|) lt.eq lr(|mu|) .
    $
  + For any $f in L^1(abs(mu))$,
    $
      abs(integral_Omega f dif mu) <= integral_Omega abs(f) dif abs(mu)
    $

]
#proof[
  Using the polar decomposition of complex measures, there exists a measurable function $h : Omega arrow.r bb(C)$ such that $lr(|h|) = 1$ and
  $
    mu (A) = integral_A h dif lr(|mu|) , quad forall A in cal(F) .
  $
  + Note we have
    $
      op("Re") (mu) (A) = op("Re") (mu (A)) = op("Re") (integral_A h dif lr(|mu|)) = integral_A op("Re") (h) dif lr(|mu|) .
    $
    Therefore,
    $
      lr(|op("Re") (mu)|) (A) & = integral_A lr(|op("Re") (h)|) dif lr(|mu|) lt.eq integral_A lr(|h|) dif lr(|mu|) = lr(|mu|) (A) .
    $

  + For any $f in L^1(abs(mu))$,
    $
      abs(integral_Omega f dif mu) = abs(integral_Omega f h dif abs(mu))<= integral_Omega abs(f h) dif abs(mu)= integral_Omega abs(f) dif abs(mu).
    $

]

#pagebreak()

= Topological Vector Spaces <topological-vector-spaces>

== Basic Notions



#definition[Topological Vector Space][
  A #strong[topological vector space] is a vector space $X$ over a topological field $𝕜$ equipped with a topology such that
  + the addition $+:X times X -> X$ is a continuous map,

  + the scalar multiplication $dot:𝕜 times X->X$ is a continuous map.
]
We often write TVS for topological vector space.

#definition[Category of Topological Vector Spaces][
  The #strong[category of topological $𝕜$-vector spaces] is the category defined as follows:

  - Objects: topological $𝕜$-vector spaces,

  - Morphisms: continuous linear maps.

  This category is denoted by $sans("TVS")_𝕜$ or $𝕜"-"sans("TopVect")$.

  #index_math(display: [$𝕜"-"sans("TopVect")$], "k-TopVect")
]

Let $X$ be a topological vector space over a topological field $𝕜$. Then $X$ is a topological group with respect to the addition operation. And the topology on $X$ is completely determined by any neighborhood basis at 0.

#proposition[Topological Field Induces Topological Vector Space][
  Let $𝕜$ be a topological field and $V$ be a (merely algebraic) $𝕜$-vector space. Suppose
  $
    phi: V -->^(tilde) product_(i in I) 𝕜
  $
  is a $k$-linear isomorphism. Then we can use $phi$ to define a topology on $V$ such that $U subset.eq V$ is open if and only if $phi(U)$ is open in $product_(i in I) 𝕜$. Then $V$ is a topological vector space.
]


#definition[Absorb][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space and $A$, $B$ be two subsets of $X$. We say $A$ #strong[absorb] $B$ if there exists a real number $r>0$ such that for any scalar $lambda in 𝕜$ with $|lambda| > r$, we have
  $
    B subset.eq lambda A= {lambda x mid(|) x in A}.
  $
]

#definition[Absorbing Set][
  A subset $A$ of a vector space $V$ is called an #strong[absorbing set] if $A$ absorbs ${x}$ for every $x in V$. That is, for every $x in V$, there exists a real number $r>0$ such that for any scalar $lambda in 𝕜$ with $|lambda| > r$, we have $x in lambda A$.
]


#definition[von Neumann Bounded Set][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. A subset $S$ of $X$ is called a #strong[von Neumann bounded set] if $S$ is absorbed by every neighborhood of $0$.
]<von-neumann-bounded-set>




=== Locally Convex Topological Vector Spaces

#definition[Balanced Set][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. A subset $A$ of $X$ is said to be #strong[balanced] if for every scalar $lambda in 𝕜$ with $|lambda| <= 1$, we have
  $
    lambda A = {lambda x mid(|) x in A} subset.eq A.
  $
]<balanced-set>



#definition[Bounded Linear Operator][
  Let $X$ and $Y$ be topological vector spaces over $𝕜 = bb(R) upright("or") bb(C)$. A #strong[bounded linear operator] from $X$ to $Y$ is a linear map $T:X -> Y$ that maps von Neumann bounded subsets of $X$ to von Neumann bounded subsets of $Y$.
]


#definition[Locally Convex Topological Vector Space][
  A topological vector space is called #strong[locally convex] if it has a neighborhood basis at $0$ consisting of balanced convex sets.
]
#remark[
  The category of locally convex topological vector spaces $sans("LCTVS")_𝕜$ is the full subcategory of $sans("TVS")_𝕜$ consisting of locally convex topological vector spaces.
]
#proposition[][
  Suppose that $V$ is a topological vector space. If $cal(B)$ is a collection of convex, #link(<balanced-set>)[balanced], and absorbing subsets of $V$, then the set of all positive scalar multiples of finite intersections of sets in $cal(B)$ forms a neighborhood basis at $0$. Thus $cal(B)$ defines a topology $tau$ on $V$. Furthermore, $(V, tau)$ is a locally convex topological vector space.
]<topology-of-locally-convex-tvs-determined-by-neighborhood-basis>

#definition[Seminorm][
  Given a vector space $X$ over $𝕜 = bb(R) upright("or") bb(C)$. A *seminorm* on $X$ is a mapping $p : X arrow.r bb(R)$ which satisfies the following conditions:

  + (absolute homogeneity): $forall x in X , forall lambda in 𝕜$, $p(lambda x)= abs(lambda) p(x)$,

  + (triangle inequality): $forall x , y in X$, $p(x + y) lt.eq p(x) + p(y)$.
]

#remark[
  We can show nonnegativity: $forall x in X$, $p(x) gt.eq 0$ and $p(x)=0$.
]

#definition[Seminorm-induced Pseudometric][
  Let $X$ be a vector space over $𝕜 = bb(R) upright("or") bb(C)$ and $p:X -> RR$ be a seminorm on $X$. The #strong[seminorm-induced pseudometric] on $X$ is the function
  $
    d(x,y) = p(x-y),quad forall x,y in X.
  $
  The topology induced by this pseudometric is called the seminorm-induced topology on $X$.
]


#definition[Seminorm-induced Topology][
  Let $X$ be a vector space over $𝕜 = bb(R) upright("or") bb(C)$ and $(p_alpha)_(alpha in A)$ be a family of seminorms on $X$. The #strong[seminorm-induced topology] on $X$ is the initial topology with respect to the family of seminorms $(p_alpha)_(alpha in A)$, i.e. the weakest topology on $X$ such that all seminorms $p_alpha:X -> RR$ are continuous.
]

#lemma[][
  Let $X$ be a vector space over $𝕜 = bb(R) upright("or") bb(C)$ and $p$ is a family of seminorms on $X$. Then
  + For any $x_0 in X$ and any $epsilon>0$,
    $
      B(x_0,epsilon) := {x in X mid(|) p (x-x_0) < epsilon}
    $
    is a convex subset of $X$.
  + For any $epsilon>0$,
    $
      B(0,epsilon) := {x in X mid(|) p (x) < epsilon}
    $
    is a balanced, and absorbing subset of $X$.
]
#proof[
  + Convexity: For any $x_1, x_2 in B(x_0,epsilon)$, for any $t in [0,1]$, we have
    $
      p(t x_1 + (1-t)x_2 - x_0) & = p(t (x_1 - x_0) + (1-t)(x_2 - x_0)) \
                                & <= t p(x_1 - x_0) + (1-t)p(x_2 - x_0) \
                                & < t epsilon + (1-t)epsilon \
                                & = epsilon.
    $

  + - Balancedness: For any $lambda in 𝕜$ with $|lambda| <= 1$, we have
      $
        p(lambda x) & = |lambda| p(x) \
                    & <= p(x) \
                    & < epsilon,
      $
      which implies $lambda x in B(0,epsilon)$.

    - Absorbingness: For any $x in X$, we can take $r = p(x) / epsilon$. Then for any $lambda in 𝕜$ with $|lambda| > r$, we have
      $
        p(1/lambda x) & = abs(1/lambda) p(x) \
                      & < p(x)/r \
                      & = epsilon.
      $
      which implies $1/lambda x in B(0,epsilon)$. Thus $x=lambda (1/lambda x) in lambda B(0,epsilon)$.
]

#proposition[Properties of Seminorm-induced Topology][
  Let $X$ be a vector space over $𝕜 = bb(R) upright("or") bb(C)$ and $(p_alpha)_(alpha in A)$ be a family of seminorms on $X$. Then

  + The topology on $X$ induced by $(p_alpha)_(alpha in A)$ is a locally convex topology.

  + If $p:X -> RR$ be a seminorm on $X$. Then $p$ is continuous with respect to the seminorm-induced topology on $X$.

  + If $p:X -> RR$ be a seminorm on $X$. The topology on $X$ induced by $p$ is the topology induced by the canonical pseudometric
    $
      d(x,y) = p(x-y) ,quad forall x,y in X.
    $
]





#definition[Seminormable space][
  A topological vector space is called #strong[seminormable] if the topology of the space is induced from a single seminorm.
]



A locally convex topological vector space has a bounded neighborhood of 0 if and only if its topology can be defined by a single seminorm.

#proposition[Properties of Seminormable Spaces][
  + A locally convex TVS is seminormable if and only if 0 has a #link(<von-neumann-bounded-set>)[bounded] neighborhood.

  + Any locally convex TVS with topology induced by a finite family of seminorms is seminormable.

  + If a Hausdorff locally convex TVS is seminormable, and the topology is induced from a single seminorm $p$, then $p$ is a norm.
]

=== Fréchet Space

#definition[Fréchet Space][
  A #strong[Fréchet space] is a complete metrizable locally convex TVS.
]

#proposition[][
  A locally convex TVS is a Fréchet space if and only if it is metrizable by a complete translation-invariant metric.
]

#example[Weighted Sequence Space][
  Let $W_op("seq")$ #index_math(display: [$W_op("seq")$], "W_seq")be the linear space of all sequences of complex numbers. Then $W_op("seq")$ is a Fréchet space with the metric
  $
    d(x,y) = sum_(n=1)^oo 1 / (2^n) (|x_n - y_n|) / (1+|x_n-y_n|).
  $
  The convergence in this metric is equivalent to the convergence of each coordinate, i.e.
  $
    x^((k))=(x^((k))_1, x^((k))_2, x^((k))_3, dots.c ) --> x=(x_1,x_2,x_3,dots.c )
  $
  if and only if $x^((k))_n --> x_n$ for all $n in ZZ_(>=1)$.
]
#proof[
  First we show that $d$ is a metric. It is easy to see that $d$ is symmetric and positive definite. We need to show that $d$ satisfies the triangle inequality. Note the function $t |-> t/(1+t)$ is increasing on $[0,oo)$. For any $x,y,z in W_op("seq")$, we have
  $
    d(x,y) & = sum_(n=1)^oo 1 / (2^n) (|x_n - y_n|) / (1+|x_n-y_n|) \
           & = sum_(n=1)^oo 1 / (2^n) (|x_n - z_n|+|z_n-y_n|) / (1+|x_n - z_n|+|z_n-y_n|) \
           & <= sum_(n=1)^oo 1 / (2^n) (|x_n - z_n|) / (1+|x_n-z_n|) + sum_(n=1)^oo 1 / (2^n) (|z_n - y_n|) / (1+|z_n-y_n|) \
           & = d(x,z) + d(z,y).
  $
  Next we show the equivalence of convergence. Suppose $lim_(n->oo) d(x^((k)),x) = 0$. Now fix $n in ZZ_(>=1)$. Then for any $epsilon > 0$, there exists $N in ZZ_(>=1)$ such that for all $k >= N$,
  $
    d(x^((k)),x) < 1 / (2^n) epsilon / (1+epsilon).
  $
  Thus by the monotonicity of the function $t |-> t/(1+t)$, we have
  $
    & 1 / (2^n) (|x^((k))_n - x_n|) / (1+|x^((k))_n-x_n|)<=d(x^((k)),x)< 1 / (2^n) epsilon / (1+epsilon)==> |x^((k))_n - x_n| < epsilon,
  $
  which implies $lim_(k->oo) x^((k))_n = x_n$.

  Conversely, suppose $lim_(k->oo) x^((k))_n = x_n$ for all $n in ZZ_(>=1)$. For any $epsilon > 0$, there exists $M in ZZ_(>=1)$ such that for all $n > M$,
  $
    sum_(m=n)^(oo) 1 / 2^m < epsilon.
  $

  For each $n in [1,M] inter ZZ$, pick $N_n in ZZ_(>=1)$ so that for all $k>= N_n$, $|x^((k))_n - x_n|<epsilon$. Let $N=max {M,N_1,dots.c,N_M}$. Note
  $
    t / (1+t)<=t,quad forall t in RR_(>=0).
  $
  For any $k >= N$,
  $
    d(x^((k)),x) &= sum_(n=1)^oo 1 / (2^n) (|x^((k))_n - x_n|) / (1+|x^((k))_n-x_n|)\
    &= sum_(n=1)^N 1 / (2^n) (|x^((k))_n - x_n|) / (1+|x^((k))_n-x_n|)+sum_(n=N+1)^oo 1 / (2^n) (|x^((k))_n - x_n|) / (1+|x^((k))_n-x_n|)\
    &<= sum_(n=1)^N 1 / (2^n) |x^((k))_n - x_n| + sum_(n=N+1)^oo 1 / (2^n) \
    &< sum_(n=1)^N epsilon / (2^n) + epsilon \
    &< 2 epsilon.
  $
  This implies $lim_(k->oo) d(x^((k)),x) = 0$. Thus the convergence in the metric $d$ is equivalent to the convergence of each coordinate.

  Finally, to prove completeness, let $(x^((k)))_(k>=1)$ be a Cauchy sequence in $d$. Then for any $epsilon>0$ and for each fixed $n$, there exists $M$ such that for all $j,l>= M$,
  $
    d(x^((l)),x^((j))) < 1 / (2^n) epsilon / (1+epsilon).
  $
  Since
  $
    1 / (2^n) (|x^((l))_n - x^((j))_n|) / (1+|x^((l))_n-x^((j))_n|) <= d(x^((l)),x^((j))) < 1 / (2^n) epsilon / (1+epsilon)==> |x^((l))_n - x^((j))_n| < epsilon,
  $
  we deduce that $(x^((k))_n)_(k>=1)$ is Cauchy in $CC$, hence converges to some $x_n$. Define $x=(x_n)$. The equivalence above yields
  $
    lim_(k->oo) d(x^((k)),x) = 0.
  $
  Therefore $W_op("seq")$ is complete. Combined with metrizability by $d$ and translation invariance, this shows $W_op("seq")$ is a Fréchet space.
]


== Continuous Dual Space

#definition[Non-degenerate Bilinear Form][
  Let $X$ and $Y$ be vector spaces over a field $𝕜$. A #strong[non-degenerate bilinear form] on $X times Y$ is a bilinear map $b:X times Y -> 𝕜$ satisfying the following two separation axioms:

  + $b(x,dot) = 0 ==> x = 0$, that is, $b(x,y) = 0$ for all $y in Y$ $==>$ $x = 0$,

  + $b(dot,y) = 0 ==> y = 0$, that is, $b(x,y) = 0$ for all $x in X$ $==>$ $y = 0$.
]

#definition[Dual Pairing][
  A #strong[dual pairing] over a field $bb(k)$ is a triple $(X, Y, b)$ where $X,Y$ is a $bb(k)$-vector space, and $b:X times Y -> bb(k)$ is a bilinear map which is non-degenerate.
]

#definition[Weak Topology with respect to a Pairing][
  Let $X$ and $Y$ be topological vector spaces over a field $bb(k)$ and $(X, Y, b)$ be a dual pairing. The #strong[weak topology on $X$] is the weakest topology on $X$ such that for any $y in Y$, the functional
  $
    X & --> bb(k) \
    x & arrow.long.bar b(x,y)
  $
  is continuous. The weak topology on $X$ is denoted by $tau(X, Y, b)$.

  Similarly, the #strong[weak topology on $Y$] is the weakest topology on $Y$ such that for any $x in X$, the functional
  $
    Y & --> bb(k) \
    y & arrow.long.bar b(x,y)
  $
  is continuous. The weak topology on $Y$ is denoted by $tau(Y, X, b)$.
]

#proposition[Weak Topology can be Induced by a Family of Seminorms][
  Let $(X,Y,b)$ be a dual pairing. Then $(X,tau(X, Y, b))$ is a locally convex TVS and the weak topology on $X$ is determined by a family of seminorms $(p_y)_(y in Y)$ defined by
  $
    p_y: X & --> RR \
         x & arrow.long.bar |b(x,y)|.
  $
]<weak-topology-can-be-induced-by-a-family-of-seminorms>
#proof[
  First we show that for any $y in Y$, $p_y$ is a seminorm.

  + Triangle inequality. For any $x_1, x_2 in X$, we have
    $
      p_y(x_1+x_2)=abs(b(x_1 + x_2, y)) = abs(b(x_1, y) + b(x_2, y)) <= |b(x_1, y)| + abs(b(x_2, y)) = p_y (x_1) + p_y (x_2).
    $

  + Absolute homogeneity. For any $x in X$ and $lambda in 𝕜$, we have
    $
      p_y (lambda x) = abs(b(lambda x, y)) = abs(lambda b(x, y)) = abs(lambda) abs(b(x, y)) = abs(lambda) p_y (x).
    $

  + Nonnegativity. For any $x in X$, we have
    $
      p_y (x) = abs(b(x, y)) >= 0.
    $

  Then we show that the weak topology on $X$ is determined by the family of seminorms $(p_y)_(y in Y)$.
]

#definition[Continuous Dual Space][
  Suppose $kk = RR "or" CC$. Let $X$ be a topological $kk$-vector space. The #strong[continuous dual space] or *topological dual space* of $X$ is the set of all continuous linear functionals $X-> bb(k)$, denoted by $topdual(X)$.
]<continuous-dual-space>

#definition[Weak and Weak$zws^*$ Topologies][
  Let $X$ be a topological vector space over a field $𝕜= RR "or" CC$. Then $(X',X, angle.l dot, dot angle.r)$ where
  $
    angle.l dot, dot angle.r : X' times X & -> 𝕜 \
                                    (f,x) & arrow.long.bar angle.l f, x angle.r = f(x)
  $
  is called the *canonical pairing* of $X$.

  - The *weak$zws^*$ topology on $X'$* is $tau(X', X, angle.l dot, dot angle.r)$, which is the weakest topology on $X'$ such that for any $x in X$, the functional
    $
      angle.l dot, x angle.r:X' & --> kk \
                              f & arrow.long.bar f(x)
    $
    is continuous. That is, the weak$zws^*$ topology is the initial topology on $X'$ with respect to $(angle.l dot, x angle.r)_(x in X)$, i.e. the pointwise convergence topology on $X'$.

    More explicitly, the weak$zws^*$ topology on $X'$ is the topology generated by the collection of sets
    $
      {angle.l dot, x angle.r^(-1)(U) in 2^X' mid(|) U "is open in" kk "and" x in X}.
    $

  - The *weak topology on $X'$* is $tau(X', X'', angle.l dot, dot angle.r)$, which is the weakest topology on $X'$ such that for any $v in X''$, the functional
    $
      angle.l v, dot angle.r:X' & --> bb(k) \
                              f & arrow.long.bar v(f)
    $
    is continuous.

    More explicitly, the weak topology on $X'$ is the topology generated by the collection of sets
    $
      {angle.l v, dot angle.r^(-1)(U) in 2^X' mid(|) U "is open in" bb(k) "and" v in X''}.
    $
]<weak-topology-and-weak-star-topology>

#proposition[Equivalent Characterization of Weak$zws^*$ Topology][
  Let $X$ be a topological vector space over a field $𝕜$. Then the following topologies on $X'$ coincide

  #set enum(numbering: enum_numbering)

  + #enum-label(<weak-topology-characterization:weak-topology>) The #link(<weak-topology-and-weak-star-topology>)[weak$zws^*$ topology] on $X'$.

  + #enum-label(<weak-topology-characterization:product-topology>) The subspace topology induced by $kk^X$ which is endowed with product topology.

  + #enum-label(<weak-topology-characterization:seminorm>) The topology induced by a family of seminorms $(op("ev")_x)_(x in X)$ defined by
    $
      op("ev")_x: X' & --> kk \
                   f & arrow.long.bar abs(f(x)).
    $
]<weak-topology-characterization>
#proof[
  The equality of @weak-topology-characterization:weak-topology and @weak-topology-characterization:product-topology follows the equivalent characterization of pointwise convergence topology. The equality of @weak-topology-characterization:weak-topology and @weak-topology-characterization:seminorm follows from @weak-topology-can-be-induced-by-a-family-of-seminorms.
]


#definition[Weak Convergence][
  Let $X$ be a topological vector space over a field $𝕜$. A net $(x_lambda)$ *converges weakly* to an element $x in X$ if $(x_lambda)$ converges to $x$ in the weak topology of $X$.
]

#proposition[Equivalent Characterization of Weak Convergence][
  Let $X$ be a topological vector space over a field $𝕜$. A net $(x_lambda)$ converges weakly to an element $x in X$ if and only if for every $T in X'$, the net $(T(x_lambda))$ converges to $T(x)$ in $𝕜$.
]
#definition[Weak$zws^*$ Convergence][
  Let $X$ be a topological vector space over a field $𝕜$. A net $(T_lambda)$ in $X'$ *converges weak$zws^*$* to an element $T in X'$ if $(T_lambda)$ converges to $T$ in the weak$zws^*$ topology of $X'$.
]

#proposition[Equivalent Characterization of Weak$zws^*$ Convergence][
  Let $X$ be a topological vector space over a field $𝕜$. Then the following statements are equivalent.


  + A net $(T_lambda)$ in $X'$ converges weak$zws^*$ to an element $T in X'$.

  + For every $x in X$, the net $(T_lambda (x))$ converges to $T(x)$ in $𝕜$.
  Weak$zws^*$ convergence coincides with the pointwise convergence of linear functionals.
]

#proposition[][
  If $X$ is a Hausdorff TVS, then the continuous dual space of $X$ is identical to the continuous dual space of the completion of $X$.
]

#definition[Strong Topology on the Dual Space][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. The #strong[strong topology] on the continuous dual space $X'$ of $X$ is the topology generated by the family of seminorms
  $
    norm(f)_A = sup_(x in A) |f(x)|
  $
  for all bounded subsets $A$ of $X$.
]


#proposition[Weak$zws^*$ Topology is Hausdorff][
  Let $X$ be a topological vector space over $𝕜= RR "or" CC$. The weak$zws^*$ topology on $X'$ is Tychonoff, and accordingly Hausdorff.
]<hausdorffness-of-weak-star-topology>
#proof[
  By @weak-topology-characterization, the weak$zws^*$ topology is the subspace topology induced by $kk^X$ which is endowed with product topology. The property of being Tychonoff is preserved under taking product topology and subspace topology. Since the topology on $kk$ is Tychonoff, the weak$zws^*$ topology on $X'$ is also Tychonoff, and accordingly Hausdorff.
]

== Space of Functions

=== Locally Integrable Functions

#definition[Locally Integrable Functions][
  Let $U$ be an open subset of $bb(R)^d$. A Lebesgue measurable function $f:U -> bb(C)$ is called #strong[locally integrable] if for every compact subset $K subset.eq U$, the Lebesgue integral
  $
    integral_K |f(x)| dif x
  $
  is finite. The set of all locally integrable functions on $U$ is a complete metrizable TVS, denoted by
  $
    L^1_("loc")(U)= {f:U -> bb(C) mid(|) f "is Lebesgue measurable and "f|_K in L^1(K) "for all compact "K subset.eq U}.
  $
  #index_math(display: [$L^1_("loc")(U)$], "L^1_loc(U)")
]

#proposition[][
  Let $U$ be an open subset of $bb(R)^d$. Then $L^p (U)$ is a subspace of $L^1_("loc")(U)$ for all $1 <= p <= oo$.
]


#proposition[$L^1_("loc")(U)$ is the Space of Densities of Absolutely Continuous Measures][
  A function $f:U -> bb(C)$ is locally integrable if and only if $f$ is the density of an absolutely continuous measure on $U$.
]
#proof[
  Let $f:U -> bb(C)$ be a locally integrable function. Then for every compact subset $K subset.eq U$, the Lebesgue integral
  $
    integral_K |f(x)| dif x
  $
  is finite. Define a measure $mu$ on $U$ by
  $
    mu(A) = integral_A f(x) dif x
  $
  for all Lebesgue measurable sets $A subset.eq U$. Then $mu$ is an absolutely continuous measure with density $f$.

  Conversely, let $mu$ be an absolutely continuous measure on $U$ with density $f$. Then for every compact subset $K subset.eq U$, the Lebesgue integral
  $
    integral_K |f(x)| dif x
  $
  is finite. Thus $f$ is locally integrable.
]



=== Test Functions

Recall that if ${p_i}_(i in I)$ is a family of seminorms on a vector space $X$, then *the topology generated by ${p_i}_(i in I)$* is the topology generated by the collection of sets
$
  {B(x_0,epsilon)_(i) in 2^X mid(|) i in I , x_0 in X, epsilon in RR_(>0)},
$
where
$
  B(x_0,epsilon)_(i) ={x in X mid(|) p_i (x-x_0) < epsilon}
$
is the open ball centered at $f$ with radius $epsilon$ with respect to the seminorm $p_i$.




#definition[Spaces of $C^k$-differentiable Functions on Open Sets][
  Let $U$ be an non-empty open subset of $bb(R)^d$. Suppose $k in ZZ_(>=0)union {oo}$. The #strong[space of $C^k$-continuous functions] $C^k (U)$ #index_math(display: [$C^k (U)$], "C^k (U)") is the topological vector space consisting of all $k$-times continuously differentiable functions on $U$. For any non-empty compact subset of $K$ of $U$, any integer $m in ZZ$ with $0<=m<=k$ and any multi-index $alpha in ZZ_(>=0)^n$ with length $|alpha|<=m$, we can define seminorms
  $
    p_(alpha , K,1)(f) & =sup_(x in K) |partial^alpha f(x)| \
        p_(m , K,2)(f) & =sup_(|alpha| <= m) p_(alpha , K,1)(f) \
        p_(m , K,3)(f) & =sup_(x in K\ |alpha| <= m) |partial^alpha f(x)| \
        p_(m , K,4)(f) & =sup_(x in K) ( sum_(abs(alpha)<=m) abs(partial^alpha f(x)))
  $
  on $C^k (U)$. Each of the following families of seminorms
  $
    & {p_(alpha , K,1) mid(|)K subset.eq U "is compact" , alpha in ZZ_(>=0)^n "satisfies" |alpha|<=k} \
    & {p_(m , K,j) mid(|) K subset.eq U "is compact" ,m in ZZ_(>=0) "satisfies" m<=k}, quad j in {2,3,4}
  $
  generates the same topology on $C^k (U)$, which makes $C^k (U)$ a locally convex TVS.
]


#proposition[Properties of $C^k (U)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$. Then the following properties hold for the space of $C^k$-differentiable functions $C^k (U)$:

  + $C^k (U)$ is a locally convex Fréchet space that is not normable.

]

#definition[Spaces of $C^k$-differentiable Functions on Compact Sets][
  Let $U$ be an non-empty open subset of $bb(R)^d$ and $K$ be a compact subset of $U$. The #strong[space of $C^k$-continuous functions on $K$] is the subspace of $C^k (U)$ consisting of all functions with support in $K$. We denote it by $C^k (K)$
  $
    C^k (K) = {f in C^k (U) mid(|) op("supp")(f) subset.eq K}.
  $
]


#proposition[Properties of $C^k (K)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$ and $K$ be a compact subset of $U$. Then the following properties hold for $C^k (K)$:

  + $C^k (K)$ is closed subspace of the Fréchet space $C^k (U)$. Thus $C^k (K)$ is also a Fréchet space.

  + If $k$ is finite, then $C^k (K)$ is a Banach space, with the norm
    $
      ||f||_(C^k (K)) = sup_(|alpha|<=k) sup_(x in K) |partial^alpha f(x)|
    $
    or the following norm equivalent to it
    $
      ||f||_(C^k (K))^' = sup_(x in K) sum_(j=0)^k |D^j f(x)|
    $
    Furthermore, $C^2 (K)$ is a Hilbert space.
  + If $C^(oo)(K)eq.not {0}$, then $C^k (K)$ is not normable.

]

#definition[Space of Test Functions $C^(oo)_c (U)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[space of test functions] $C^(oo)_c (U)$ #index_math(display: [$C^(oo)_c (U)$], "C^(oo)_c(U)") is the topological vector space consisting of all smooth functions on $U$ with compact support. Suppose $cal(K)={K_j}_(j in J)$ is a collection of compact subsets of $U$ such that
  + $U = union.big_(j in J) K_j$,
  + For any $K_(j_1) , K_(j_2) in cal(K)$, there exists a compact subset $K_(j_3) in cal(K)$ such that $K_(j_1) union K_(j_2) subset.eq K_(j_3)$.
  For any $K in cal(K)$, endow $C^(oo) (K)$ with the subspace topology induced by the topology on $C^(oo) (U)$. Then
  $
    {V subset.eq C^(oo)_c (U) mid(|) V "is convex," V inter C^(oo) (K) "is a neighborhood of" 0 "in" C^(oo) (K) "for all" K in cal(K)} ,
  $
  is a collection of convex, balanced, and absorbing subsets of $C^(oo)_c (U)$, which defines a topology on $C^(oo)_c (U)$ according to @topology-of-locally-convex-tvs-determined-by-neighborhood-basis, called the *canonical LF-topology*.
]
#remark[
  For any compact subset $K,L$ of $U$ with $K subset.eq L$, the inclusion map $op("ext")_(K subset.eq L):C^(oo) (L) arrow.hook C^(oo) (K)$ is a closed topological embedding, where
  $
    op("ext")_(K arrow.hook L)(f)= bold(1)_(f in C^(oo) (K)) f,quad forall f in C^(oo) (K)
  $
  is the trivial extension of $f$ to $L$.

  $C_c^(oo)(U)$ can also be defined as the colimit
  $
    C_c^(oo)(U) = injlim_(K in cal(K)) C^(oo)(K).
  $
  The universal property of $C_c^(oo)(U)$ is that for any locally convex TVS $X$ and any family of continuous linear maps $(T_j:C^(oo)(K_j) -> X)_(j in J)$, there exists a unique continuous linear map $tilde(T):C^(oo)_c (U) -> X$ such that the following diagram commutes
  #commutative_diagram(
    $
      &X&\
      & C^(oo)_c (U) edge("u", #left, tilde(T), "-->")&\
      C^(oo)(K_i)edge("ru", #right, op("ext")_(K_i arrow.hook U), ->)edge("ruu", T_(i), ->) edge("rr", #right, op("ext")_(K_i arrow.hook K_j), ->)&& C^(oo)(K_j) edge("lu", #left, op("ext")_(K_j arrow.hook U), ->)edge("luu", T_j, ->)
    $,
  )
  As a set, $C^(oo)_c (U)=union.big_(j in J) C^(oo)(K_j)$ is the union of all $C^(oo)(K_j)$ with $K_j in cal(K)$.
  The topology on $C^(oo)_c (U)$ is the finest locally convex topology that makes all of the inclusion maps $op("ext")_(K_j subset.eq U):C^(oo) (K_j) arrow.hook C_c^(oo) (U)$ continuous.
]

#proposition[Properties of $C_c^(oo) (U)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$. Then the following properties hold for the space of test functions $C^(oo)_c (U)$:

  + $C^(oo)_c (U)$ is a complete Hausdorff locally convex TVS that is not metrizable.

  + The space $C^(oo)_c (U)$ is a reflexive nuclear Montel space.

  + The LF-topology on $C^(oo)_c (U)$ is the strictly finer than the subspace topology induced by the inclusion map $C^(oo)_c (U) arrow.hook C^(oo) (U)$.

  + A sequence $(f_i)_(i in I)$ in $C^(oo)_c (U)$ converges to $f in C^(oo)_c (U)$ if and only if there exists a compact subset $K subset.eq U$ such that

    - $f_i in C^(oo) (K)$ for all $i in I$,

    - $f in C^(oo) (K)$,

    - $(f_i)_(i in I)$ converges to $f$ in the topology of $C^(oo) (K)$,

    or equivalently,

    - $union.big_(i in I) op("supp")(f_i) subset.eq K$,

    - For each multi-index $alpha$, the sequence $(partial^alpha f_i)_(i in I)$ converges to $partial^alpha f$ uniformly on $K$.

  + $C^(oo)_c (RR^d)$ is separable but not first-countable.

  + The inclusion map $C^(oo)_c (RR^d) arrow.hook L^p (RR^d)$ is continuous for all $0< p <= oo$.

  + The multiplication map $C^(oo)_c (RR^d) times C^(oo)_c (RR^d) -> C^(oo)_c (RR^d)$ is continuous.
]


=== Continuous Functions with Compact Support


#definition[Positive Linear Functional][
  Let $bb(k) = bb(R) "or" bb(C)$ and $X$ be a locally compact Hausdorff space. A linear functional $T:C_c (X; bb(k)) -> bb(k)$ is called *positive* if for any $f in C_c (X; bb(k))$ with $f(X) subset.eq [0,oo)$, we have $T(f) subset.eq [0,oo)$.
]

For any complex-valued functions $f:X ->CC$ and $g:X ->CC$, we use the notation $f <= g$ to mean that $f(X) subset.eq RR$, $g(X) subset.eq RR$ and
$
  f(x) <= g(x), quad forall x in X.
$

#proposition[Monotonicity of Positive Linear Functionals][
  Let $bb(k) = bb(R) "or" bb(C)$ and $X$ be a locally compact Hausdorff space. Suppose $T$ is a positive linear functional in $C_c (X; bb(k))'$. For any $f,g in C_c (X; bb(k))$ with $f <=g$, we have
  $
    T(f) <= T(g).
  $
]<monotonicity-of-positive-linear-functionals>

#proof[
  Since $f(X) subset.eq [0,oo)$ and $g(X) subset.eq [0,oo)$ and $f(x) <= g(x)$ for all $x in X$, we have $(g-f)(X) subset.eq [0,oo)$. The positivity of $T$ implies that
  $
    T(g) - T(f) = T(g-f) >= 0.
  $
  Hence $T(g) >= T(f)$.
]

#definition[Space of Continuous Functions with Compact Support][
  Let $bb(k) = bb(R) "or" bb(C)$ and $X$ be a locally compact Hausdorff space. The #strong[space of continuous functions with compact support] on $X$ is the topological vector space consisting of all continuous functions $f: X -> bb(k)$ with compact support, denoted by $C_c (X; bb(k))$.#index_math(display: [$C_c (X; bb(k))$], "C_c(X;k)")

]

For any open subsets $U$ of $bb(R)^d$, The inclusion map $iota:C^(oo)_c (U) arrow.hook C_c (U)$ is a continuous injection whose image is dense in $C_c (U)$. So the transpose map $iota^*:C_c (U)' -> C^(oo)_c (U)'$ is also a continuous injection.

#lemma[][
  If $z in CC$ is a complex number, then there exists a complex number $lambda$ such that $abs(lambda)=1$ and
  $
    abs(z) = op(op("Re"))(lambda z).
  $
]<complex-number-modulus-lemma>
#proof[
  We can write $z = abs(z) e^(i theta)$ for some $theta in [0, 2pi)$. Take $lambda = e^(-i theta)$. Then we have
  $
    op(op("Re"))(lambda z)=op(op("Re"))(e^(-i theta) abs(z) e^(i theta)) = op(op("Re"))(abs(z)) = abs(z).
  $
]

#proposition[][
  Let $bb(k)=RR "or" bb(C)$. Suppose $T$ is a positive linear functional in $C_c (X; bb(k))'$. Then for each
  compact $K subset.eq X$, there is a constant $M_K > 0$ such that
  $
    abs(T(f)) <= M_K norm(f)_oo
  $
  for all
  $f in C_c (X; bb(k))$ such that $op("supp") (f) subset.eq K$.
]
#proof[
  - $bb(k)=RR$. Given any compact set $K subset.eq X$, there exists $phi.alt_K in$ $C_c ( X, [0 , 1 ] )$ such that $phi.alt_K = 1$ on $K$ (by Urysohn's lemma). If $f in C_c (X; RR)$ is a real-valued function with $op("supp") (f)subset.eq K$, we have $abs(f) lt.eq norm(f)_oo phi.alt_K$, that is,
    $
      -norm(f)_oo phi.alt_K <= f <=norm(f)_oo phi.alt_K
    $
    By @monotonicity-of-positive-linear-functionals, we have
    $
      - norm(f)_oo T ( phi.alt_K )<= T( f ) <=norm(f)_oo T ( phi.alt_K )
    $
    so that $abs(T(f))lt.eq T ( phi.alt_K ) norm(f)_oo$. Taking $M_K = T( phi.alt_K )$ gives the desired inequality.

  - $bb(k)=CC$. If $f in C_c (X; CC)$ is a complex-valued function with $op("supp") (f)subset.eq K$, then by @complex-number-modulus-lemma we can write
    $
      |T(f)| = op(op("Re"))(lambda T(f))
    $
    for some $lambda in CC$ with $|lambda|=1$. Then we have
    $
      |T(f)| = op(op("Re"))(lambda T(f)) = op(op("Re"))( T( lambda f))= T(op(op("Re"))( lambda f))<= T( |f| )
    $
    Note $T|_(C_c (X;RR)) in C_c (X;RR)'$ is a positive linear functional, and $abs(f) in C_c (X;RR)$ satisfies $op("supp") (abs(f)) =op("supp") (f)subset.eq K$. By the previous case, there exists a constant $M_K > 0$ such that
    $
      |T(abs(f))| <= M_K norm(abs(f))_oo = M_K norm(f)_oo.
    $
    Thus we get
    $
      |T(f)| <= T( |f| )<= M_K norm(f)_oo.
    $

]

If $mu$ is a Borel measure on $X$ such that $mu ( K ) < oo$ for every
compact $K subset X$, then clearly $C_c ( X ) subset L^1 ( mu )$, so
the map $f mapsto integral f d mu$ is a positive linear functional on
$C_c ( X )$. The principal result of this section is that every
positive linear functional on $C_c ( X )$ arises in this fashion;
moreover, one can impose some additional regularity to ensure the uniqueness of
the measure $mu$.

#theorem[Riesz-Markov-Kakutani Representation Theorem][
  Let $X$ be a locally compact Hausdorff space and $T:C_c (X;bb(k))->bb(k)$ be a positive linear functional on $C_c (X;bb(k))$. Then there exists a unique Radon measure $mu$ on $(X,cal(B)(X))$ such that

  $
    T(f) = integral_X f dif mu ,quad forall f in C_c (X;bb(k))
  $

  Moreover, we have

  + If $U$ is an open subset of $X$, then
    $
      mu(U) = sup{ T(f) mid(|) f in C_c (X;bb(k)) , 0 <= f <= 1, op("supp")(f) subset.eq U}.
    $

  + If $K$ is a compact subset of $X$, then
    $
      mu(K) = inf{ T(f) mid(|) f in C_c (X;bb(k)), f >= bb(1)_K}.
    $
]<riesz-markov-kakutani-representation-theorem-for-radon-measure>
#remark[
  Any positive linear functional $T in C_c (RR^d)^'$ can be represented as
  $
    T(f) = integral_(RR^d) f dif mu
  $
  for some Radon measure $mu$ on $RR^d$.
]


By the Riesz-Markov-Kakutani representation theorem, the space $C_c^0 (X)'$ can be identified with the space of Radon measures on $X$.

One particularly important class of Radon measures are those that are induced locally integrable functions. There is a bijective correspondence between locally integrable functions $f$ on $X$ and linear functionals $T_f$ on $C_c^0 (X)$ defined by
$
  T_f (g) = integral_X g f dif x,quad forall g in C_c^(oo) (X).
$

If $f$ and $g$ are locally integrable functions on $X$, then $T_f=T_g$ if and only if $f=g$ almost everywhere.

=== Continuous Functions Vanishing at Infinity

#definition[Space of Continuous Functions Vanishing at Infinity][
  Let $bb(k) = bb(R) "or" bb(C)$ and $X$ be a locally compact Hausdorff space. The #strong[space of continuous functions vanishing at infinity] on $X$ is the topological vector space consisting of all continuous functions $f:X -> bb(k)$ such that for every $epsilon > 0$, there exists a compact subset $K subset.eq X$ such that for all $x in X - K$, we have $|f(x)| < epsilon$. We denote this space by $C_0 (X; bb(k))$. #index_math(display: [$C_0 (X; bb(k))$], "C_0(X;k)")
]

#lemma[][ If $X$ is an locally compact Hausdorff space and $K subset.eq U subset.eq X$
  where $K$ is compact and $U$ is open, there exists a precompact open $V$
  such that $K subset.eq V subset.eq overline(V) subset.eq U$.
]<precompact-open-subset>
#proof[
  For each $x in K$ we can choose a compact
  neighborhood $N_x$ of $x$ with $N_x subset U$. Then ${N_x^o}_(x in K)$
  is an open cover of $K$, so there is a finite subcover
  ${N_(x_j)^o}_(j=1)^n$. Let $V = union.big_(j=1)^n N_(x_j)^o$; then $K subset.eq V$
  and
  $ overline(V) = union.big_(j=1)^n N_(x_j) $ is compact and contained in $U$.
]
#lemma[Urysohn's Lemma, Locally Compact Version][
  If $X$ is an locally compact Hausdorff space and $K subset.eq U subset.eq X$ where $K$ is compact and $U$ is open, there
  exists $f in C ( X , [ 0 , 1 ] )$ such that $f = 1$ on $K$ and
  $f = 0$ outside a compact subset of $U$.
]
#proof[
  Let $V$ be as in @precompact-open-subset. Then $overline(V)$ is normal, so by Urysohn's lemma there exists
  $f in C ( overline(V) , [ 0 , 1 ] )$ such that $f = 1$ on $K$ and
  $f = 0$ on $partial V$. We extend $f$ to $X$ by setting $f = 0$ on
  $overline(V)^complement$. Suppose that $E subset.eq [ 0 , 1 ]$ is closed. If
  $0 in.not E$ we have
  $f^(- 1) ( E ) = ( f|_overline(V) )^(-1) ( E )$, and if
  $0 in E$ we have
  $
    f^(- 1) ( E ) = (f|_overline(V) )^(-1) ( E ) union overline(V)^complement = (f|_overline(V))^(- 1) ( E ) union V^complement
  $
  since $( f|_overline(V) )^(- 1) ( E ) supset.eq partial V$. In
  either case, $f^(- 1) ( E )$ is closed, so $f$ is continuous.
]
#proposition[$C_0(X)$ is the Uniform Closure of $C_c (X)$][
  Let $X$ be a locally compact Hausdorff space and $C(X)$ be the space of all continuous functions on $X$ endowed with the supremum norm $||dot||_oo$
  $
    norm(f)_oo = sup_(x in X) abs(f(x)).
  $
  Then the space $C_0 (X)$ is the closure of $C_c (X)$ in $C(X)$, where both $C_c (X)$ and $C_0 (X)$ are endowed with the subspace topology induced by the supremum norm on $C(X)$.
]
#proof[
  If $(f_n)_(n >=1)$ is a sequence in $C_c ( X )$ that converges
  uniformly to $f in C ( X )$, for each $epsilon.alt > 0$ there exists
  $n in ZZ_(>=1)$ such that $norm(f_n - f)_oo< epsilon.alt$. Then
  $abs(f(x))< epsilon.alt$ if $x in.not op("supp")(f_n)$, so
  $f in C_0( X )$. Conversely, if $f in C_0 ( X )$, for $n in ZZ_(>=1)$
  let
  $
    K_n = {x : abs(f(x)) gt.eq 1/n}.
  $
  Then $K_n$ is compact,
  so by Theorem 4.32 there exists $g_n in C_c ( X )$ with
  $0 lt.eq g_n lt.eq 1$ and $g_n = 1$ on $K_n$. Let $f_n = g_n f$. Then
  $f_n in C_c ( X )$ and $norm(f_n - f)_oo lt.eq 1/n$, so $f_n arrow.r f$
  uniformly as $n -> oo$.
]

#proposition[][
  If $I in C_0(X; RR)^'$, there exist positive functionals $I^+ , I^-in C_0(X; RR)^'$ such that $I = I^+ - I^-$.


]
#proof[
  Fix some $I in C_0(X; RR)^'$. If $f in C_0(X;[0, oo))$, we define

  $
    I^+: C_0(X;[0, oo)) & --> RR \
                      f & arrow.bar.long sup {I(g) mid(|) g in C_0(X; RR), 0 <= g <= f}.
  $

  Since $abs(I(g)) <= norm(I) norm(g)_oo <= norm(I) norm(f)_oo$ for $0 <= g <= f$, and $I(0)=0$, we have $0 <= I^+(f) <= norm(I) norm(f)_oo$. We claim that $I^+$ can be extended to a linear functional in $C_0(X; RR)^'$.

  Obviously $I^+(c f) = c I^+(f)$ for any $c >= 0$. Also, whenever $0 <= g_1 <= f_1$ and $0 <= g_2 <= f_2$ we have $0 <= g_1 + g_2 <= f_1 + f_2$, so that $I^+(f_1 + f_2) >= I(g_1) + I(g_2)$, and it follows that $I^+(f_1 + f_2) >= I^+(f_1) + I^+(f_2)$. On the other hand, if $0 <= g <= f_1 + f_2$, let $g_1 = min(g, f_1)$ and $g_2 = g - g_1$. Then $0 <= g_1 <= f_1$ and $0 <= g_2 <= f_2$, so $I(g) = I(g_1) + I(g_2) <= I^+(f_1) + I^+(f_2)$; therefore $I^+(f_1 + f_2) <= I^+(f_1) + I^+(f_2)$. In short, $I^+(f_1 + f_2) = I^+(f_1) + I^+(f_2)$.

  Now, if $f in C_0(X; RR)$, then its positive and negative parts $f^+$ and $f^-$ are in $C_0(X; [0, oo))$, and we define $I^+(f) = I^+(f^+) - I^+(f^-)$. If also $f = g - h$ where $g, h >= 0$, then $g + f^- = h + f^+$, whence $I^+(g) + I^+(f^-) = I^+(h) + I^+(f^+)$. Thus $I^+(f) = I^+(g) - I^+(h)$, and it follows easily  that $I^+$ is linear on $C_0(X; RR)$. Moreover,

  $ abs(I^+(f)) <= max(I^+(f^+), I^+(f^-)) <= norm(I) max(norm(f^+)_oo, norm(f^-)_oo) = norm(I) norm(f)_oo, $

  so that $norm(I^+) <= norm(I)$.

  Finally, let $I^- = I^+ - I$. Then $I^- in C_0(X; RR)^'$, and it is immediate from the definition of $I^+$ that $I^+$ and $I^-$ are positive.
]

#lemma[][
  Any functinal $I in C_0(X, CC)^'$ is uniquely determined by its restriction  to $C_0(X, RR)$.
]
#proof[
  Let $I in C_0(X, CC)^'$ be a $CC$-linear functional, and let $J:= I|_(C_0(X, RR))$ be its restriction. Every $f in C_0(X, CC)$ can be decompose as
  $
    f = u + i v,
  $
  where $u=op(op("Re"))(f) in C_0(X; RR)$ and $v=op("Im")(f) in C_0(X; RR)$. By complex linearity of $I$, we have
  $
    I(f) = I(u + i v)= I(u) + i I(v)=J(u) + i J(v) = J(op(op("Re"))(f)) + i J(op("Im")(f)), quad forall f in C_0(X, CC).
  $
  This shows that $I$ is uniquely determined by $J= I|_(C_0(X, RR))$.
]



#theorem[Riesz-Markov-Kakutani Representation Theorem][
  Let $X$ be a locally compact Hausdorff space. Given any $mu in M_("Rad")(X; CC)$, we can define a continuous linear functional
  $
    I_mu: C_0(X; CC) & --> CC \
                   f & arrow.bar.long integral_X f dif mu.
  $
  Then the map
  $
    Phi: M_("Rad")(X; CC) & --> C_0(X; CC)' \
                       mu & arrow.bar.long I_mu
  $
  is an isometric isomorphism.
]<riesz-markov-kakutani-representation-theorem-for-complex-radon-measure>

== Space of Distributions

#definition[Space of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[space of distributions] $D'(U)$ is the continuous dual space of the space of test functions $C^(oo)_c (U)$. $D'(U)$ is endowed with the strong dual topology, which makes $D'(U)$ a locally convex TVS.
]



#definition[Weak$zws^*$ Topology on the Space of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[weak$zws^*$ topology] on the space of distributions $D'(U)$ is the weakest topology on $D'(U)$ such that for any $f in C^(oo)_c (U)$, the functional
  $
    D'(U) & --> bb(k) \
        T & arrow.long.bar T(f)
  $
  is continuous.
]

#proposition[Equivalent Characterizations of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$. If $T:C^(oo)_c (U) ->bb(k)$ is a linear functional on $C^(oo)_c (U)$, then the following statements are equivalent:
  + $T$ is a distribution.

  + $T$ is continuous.

  + $T$ is continuous at $0$.

  + $T$ is uniformly continuous.

  + $T$ is sequentially continuous at $0$. That is, for any sequence $(f_n)_(n in NN)$ in $C^(oo)_c (U)$ that converges to $0$, the sequence $(T(f_n))_(n in NN)$ converges to $0$ in $bb(k)$.

  + $ker T$ is a closed subspace of $C^(oo)_c (U)$.

  + For every compact subset $K subset.eq U$, there exists a constant $C>0$ and $M in ZZ_(>=0)$ such that for all $f in C^(oo)(K)$,
  $
    |T(f)| <= C sup_(x in K\ |alpha|<=M) |partial^alpha f(x)|,
  $

  + For every compact subset $K subset.eq U$, there exists $k in ZZ_(>=0)$ such that for all $f in C^(oo)(K)$,
    $
      abs(T(f)) lt.tilde norm(f)_(C^(k)(K))
    $
    where $||dot||_(C^(k)(K))$ is a norm of the Banach space $C^(k)(K)$.

  + For every compact subset $K subset.eq U$ and any sequence $(f_n)_(n=1)^(oo)$ in $C^(oo)(K)$, if the sequence $(partial^alpha f_n)_(n=1)^(oo)$ converges to $0$ uniformly on $K$ for any multi-index $alpha in ZZ_(>=0)^d$, then the sequence $(T(f_n))_(n=1)^(oo)$ converges to $0$ in $bb(k)$.
]

#proposition[Properties of $D'(U)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$. Then the following properties hold for the space of distributions $D'(U)$:
  + $D'(U)$ is a complete Hausdorff nuclear space that is not metrizable.

  + $D'(U)$ is locally convex bornological space. Specifically, a linear map from $D'(U)$ into another locally convex TVS is continuous if and only if it is sequentially continuous at $0$.

]


#proposition[Equivalent Characterization of Convergence of Sequence of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$ and $(T_n)_(n=1)^(oo)$ be a sequence in $D'(U)$. Then the following statements are equivalent:

  + The sequence $(T_k)_(n=1)^(oo)$ converges to $T in D'(U)$ in the strong dual topology.

  + The sequence $(T_k)_(n=1)^(oo)$ converges to $T in D'(U)$ in the weak$zws^*$ topology.

  + For every $f in C^(oo)_c (U)$, the sequence $(T_n (f))_(i=1)^(oo)$ converges to $T(f)$ in $bb(k)$.
]


== Vector-Valued Integrals

#definition[Weakly Integrable][
  Suppose $(X,Sigma, mu)$ is a measure space and $Y$ is a locally convex topological vector space over $𝕜 = bb(R) upright("or") bb(C)$. A function $f:X -> Y$ is said to be *weakly integrable* if for any $phi in Y'$, we have
  $
    phi compose f in L^1 (X, Sigma, mu).
  $
  In this case, if there is a vector $y in Y$ such that for any $phi in Y'$,
  $
    integral_X phi compose f dif mu = phi (y),quad "or equivalently"quad integral_X angle.l phi ,f(x) angle.r dif mu(x) = angle.l phi , y angle.r,
  $
  then we say that $y$ is the *integral* of $f$ over $X$ and denote it by
  $
    integral_X f dif mu := y.
  $
]
#remark[
  If the integral of $f$ exists, then it is unique. Assume there are two vectors $y_1, y_2 in Y$ such that for any $phi in Y'$, we have
  $
    phi(y_1) = integral_X phi compose f dif mu = phi(y_2) ==>phi(y_1 - y_2) = 0.
  $
  Suppose $y_1 eq.not y_2$. Then $y_1 - y_2 != 0$. Since $Y$ is locally convex, we know continuous linear functionals separate points. So we can find $psi in Y'$ with $psi(y_1 - y_2) != 0$, contradicting
  $
    phi(y_1 - y_2) = 0, quad forall phi in Y'.
  $
  Hence $y_1 = y_2$.
]

#proposition[Integrals Commute with Bounded Linear Operators][
  Let $(X,Sigma, mu)$ be a measure space and $Y,Z$ be locally convex topological vector spaces over $𝕜 = bb(R) upright("or") bb(C)$. Suppose $f:X -> Y$ is weakly integrable and the integral $integral_X f dif mu$ exists. Let $T: Y-> Z$ be a bounded linear operator. Then

  - The function $T compose f:X -> Z$ is weakly integrable.

  - The integral of $T compose f$ exists and is given by
  $
    integral_X T compose f dif mu = T(integral_X f dif mu).
  $
]
#proof[
  Given any $phi.alt in Z'$, since $T$ is coutinous, we have $phi.alt compose T in Y'$. Since $f:X->Y$ is weakly integrable, we have
  $
    phi.alt compose (T compose f)=(phi.alt compose T) compose f in L^1 (X, Sigma, mu),
  $
  which implies that $T compose f$ is weakly integrable. Furthermore, define
  $
    z:=T(integral_X f dif mu).
  $
  For any $phi.alt in Z'$, we have
  $
    phi.alt(z) = phi.alt(T(integral_X f dif mu)) = (phi.alt compose T)(integral_X f dif mu) = integral_X (phi.alt compose T) compose f dif mu = integral_X phi.alt compose (T compose f) dif mu.
  $
  Thus the integral of $T compose f$ exists and is equal to $z$.

]

#proposition[][
  Let $X$ be a locally compact Hausdorff space and $mu$ be a Radon measure on $X$. Let $Y$ be a Fréchet space over $𝕜 = bb(R) upright("or") bb(C)$. Suppose $f:X -> Y$ is a continuous function with compact support. Then

  - $f$ is weakly integrable.#h(1fr)

  - The integral $integral_X f dif mu$ exists and
    $
      integral_X f dif mu in overline(op("span")_𝕜 (f(X))) .
    $

  - If $Y$ is a Banach space, then
    $
      norm(integral_X f dif mu)_(Y) <= integral_X norm(f(x))_(Y) dif mu(x).
    $

]<continous-compactly-supported-functions-are-weakly-integrable>

#proposition[][
  Let $X$ be a locally compact Hausdorff space and $mu$ be a Radon measure on $X$. Let $Y$ be a Banach space over $𝕜 = bb(R) upright("or") bb(C)$. Suppose $g in L^1(X, scr(B)(X), mu)$ is a $𝕜$-valued function, and $f:X -> Y$ is bounded continuous function. Then

  + $g f$ is weakly integrable.#h(1fr)

  + The integral $integral_X g f dif mu$ exists and
    $
      integral_X g f dif mu in overline(op("span")_𝕜 (f(X))) .
    $

  +
    $
      norm(integral_X g f dif mu)_(Y) <= sup_(x in X)norm(f(x)) integral_X |g| dif mu.
    $
]
#proof[
  + Given any $phi in Y'$, since $f:X -> Y$ is bounded and continuous, $phi compose f in L^(oo)(X, scr(B)(X), mu)$ is a bounded measurable function. Note $g in L^1(X, scr(B)(X), mu)$, we have
    $
      phi compose (g f) = g (phi compose f) in L^1 (X, scr(B)(X), mu),
    $
    which implies $g f$ is weakly integrable.

  + Since $mu$ is a Radon measure, there is a sequence $(g_n)_(n=1)^(oo)$ in $C_c (X)$ such that
    $
      lim_(n arrow.r oo) integral_X |g_n - g| dif mu = 0.
    $
    Thus by @continous-compactly-supported-functions-are-weakly-integrable we have
    $
      norm(integral_X g_m f dif mu-integral_X g_n f dif mu)_(Y)&=norm(integral_X (g_m - g_n) f dif mu)_(Y) \
      &<= integral_X norm((g_m (x) - g_n (x) )f(x))_Y dif mu(x) \
      &= integral_X abs(g_m (x) - g_n (x))norm(f(x))_Y dif mu(x) \
      &<= sup_(x in X) norm(f(x))_Y integral_X |g_m (x) - g_n (x)| dif mu(x) --> 0
    $
    as $m,n arrow.r oo$. This implies that the sequence $(integral_X g_n f dif mu)_(n=1)^(oo)$ is Cauchy in $Y$. Since $Y$ is complete, $(integral_X g_n f dif mu)_(n=1)^(oo)$ is convergent and we can denote the limit of this sequence by $y$
    $
      y:=lim_(n->oo) integral_X g_n f dif mu.
    $
    Then for any $phi in Y'$, we have
    $
      phi(y) & = phi(lim_(n->oo) integral_X g_n f dif mu) \
             & = lim_(n->oo) phi(integral_X g_n f dif mu) \
             & = lim_(n->oo) integral_X phi compose (g_n f) dif mu \
             & = lim_(n->oo) integral_X g_n (phi compose f) dif mu
    $
    Note as $n arrow.r oo$, we have
    $
      abs(integral_X g_n (phi compose f) dif mu - integral_X g (phi compose f) dif mu)<= integral_X abs((g_n -g)(phi compose f)) dif mu <= C integral_X |g_n - g| dif mu -> 0.
    $
    Thus we get
    $
      phi(y) = lim_(n->oo) integral_X g_n (phi compose f) dif mu = integral_X g (phi compose f) dif mu= integral_X phi compose (g f) dif mu.
    $
    Then the integral of $g f$ exists and is given by
    $
      integral_X g f dif mu = lim_(n->oo) integral_X g_n f dif mu.
    $
    Since $g_n f$ is a continuous function with compact support, by @continous-compactly-supported-functions-are-weakly-integrable we have
    $
      integral_X g_n f dif mu in overline(op("span")_𝕜 (f(X))) .
    $

  + Continue from the previous step. By @continous-compactly-supported-functions-are-weakly-integrable we have
    $
      norm(integral_X g_n f dif mu)_(Y) <= integral_X abs(g_n (x)) norm(f(x))_Y dif mu(x)<= sup_(x in X) norm(f(x))_Y integral_X abs(g_n) dif mu.
    $
    Taking limit as $n arrow.r oo$, we get
    $
      norm(integral_X g f dif mu)_(Y) <= sup_(x in X)norm(f(x))_Y integral_X |g| dif mu.
    $
]


#pagebreak()

= Normed Spaces <metric-spaces-and-normed-spaces>


== Normed Spaces <normed-spaces>
=== Basic notions <basic-notions-1>
#definition[Normed Space][
  Given a vector space $X$ over $𝕜 = bb(R) upright("or") bb(C)$. A *norm* on $X$ is a mapping $bar.v.double dot.op bar.v.double : X arrow.r bb(R)$ which satisfies the following conditions:

  + (positive definiteness): $forall x in X ,||x|| gt.eq 0$ and $||x|| = 0 arrow.l.r.double x = 0$,

  + (absolute homogeneity): $forall x in X , forall lambda in 𝕜 , ||lambda x||= lr(|lambda|) norm(x)$,

  + (triangle inequality): $forall x , y in X , ||x + y|| lt.eq ||x|| + ||y||$.

  A #strong[normed vector space] or a #strong[normed space] is a pair $(X , bar.v.double dot.op bar.v.double)$ where $X$ is a $𝕜$-vector space and $bar.v.double dot.op bar.v.double$ is a norm on $X$.
]


#proposition[][
  Let $lr((X , bar.v.double dot.op bar.v.double))$ be a normed space.

  + $bar.v.double dot.op bar.v.double : X arrow.r bb(R)$ is continuous, namely #h(1fr)
    $
      lim_(n arrow.r oo) x_n = x ==> lim_(n -> oo) ||x_n|| = ||x|| ,
    $

  + The addition and multiplication on $X$ is continuous, namely
    $
      lim_(n arrow.r oo) x_n = x , lim_(n arrow.r oo) y_n = y , lim_(n arrow.r oo) lambda_n = lambda arrow.r.double.long lim_(n arrow.r oo) x_n + lambda_n y_n = x + lambda y .
    $
  + Normed space is a Hausdorff locally convex TVS.
]

#proposition[Restriction of Norm to Subspace is Norm][
  Let $lr((X , bar.v.double dot.op bar.v.double))$ be a normed space and $Y$ be a subspace of $X$. Define $bar.v.double dot.op bar.v.double_Y$ as the restriction of the map $bar.v.double dot.op bar.v.double:X-> RR$ to $Y$. Then $lr((Y , bar.v.double dot.op bar.v.double_Y))$ is a normed space. And we call $lr((Y , bar.v.double dot.op bar.v.double_Y))$ the #strong[sub normed space] of $lr((X , bar.v.double dot.op bar.v.double))$.
]
#proof[
  We only need to check the three conditions of the normed space for $Y$.

  + (positive definiteness): $forall y in Y , ||y||_Y = ||y|| >= 0$ and $||y||_Y = 0 <==> ||y|| = 0 <==> y = 0$.

  + (absolute homogeneity): $forall y in Y , forall lambda in 𝕜 , ||lambda y||_Y = ||lambda y|| = lambda||y|| = lambda||y||_Y$.

  + (triangle inequality): $forall y_1 , y_2 in Y , norm(y_1 + y_2)_Y = norm(y_1 + y_2)<= ||y_1|| + ||y_2|| = ||y_1||_Y + ||y_2||_Y$.
]

#proposition[Topology of Sub Normed Space is Subspace Topology][
  Let $lr((X , bar.v.double dot.op bar.v.double))$ be a normed space and $Y$ be a subspace of $X$. Then the topology induced by the norm $bar.v.double dot.op bar.v.double_Y$ on $Y$ is the same as the subspace topology induced by the norm $bar.v.double dot.op bar.v.double$ on $X$.
]
#proof[
  The topology induced by the norm $bar.v.double dot.op bar.v.double_Y$ on $Y$ is the same as the subspace topology induced by the norm $bar.v.double dot.op bar.v.double$ on $X$.
]

#definition[Absolute Convergence][
  A series $limits(sum)_(n=1)^(oo) x_n$ in a normed space $X$ is said to be *absolutely convergent* if the series $limits(sum)_(n=1)^(oo) ||x_n||$ converges in $bb(R)$.
]

#proposition[Properties of $d(x,S)$][
  Let $X$ be a normed space over $𝕜 = bb(R) upright("or") bb(C)$. Suppose $S subset.eq X$ is a subset of $X$ and $x in X$. Let
  $
    d(x, S)= inf_(y in S) ||x-y||
  $
  be the distance from $x$ to $S$.

  + _Translation Invariance_: $d(x, S + y) = d(x - y, S)$ for all $x, y in X$.

  + _Convexity_: if $S$ is convex, then $x|-> d(x,S)$ is convex.

  + If and only if $S$ is a linear subspace of $X$, $x|-> d(x,S)$ is a seminorm on $X$. That is,
    - Absolute homogeneity: $d(lambda x, S) = |lambda| d(x, S)$ for all $x in X$ and $lambda in 𝕜$.

    - Subadditivity: $d(x+y, S) <= d(x, S) + d(y, S)$ for all $x, y in X$.
]

#definition[Quotient Norm][
  Let $X$ be a normed space and $N$ be a closed linear subspace of $X$. The *quotient norm* on the quotient space $X\/N$ is defined as
  $
    norm(x+N)_(X\/N) = inf_(z in N) norm(x-z)=d(x,N)
  $
  And $(X\/N , norm(x+N)_(X\/N))$ is a normed space, called the *quotient normed space*.
]<quotient_norm>
#remark[
  First we show that the quotient norm is well-defined. Given $x_1, x_2 in X$ such that $x_1 + N = x_2 + N$, we have $x_1 - x_2 in N$. Therefore,
  $
    norm(x_1 + N)_(X\/N) = inf_(z in N) norm(x_1 - z)= inf_(z in N) norm(x_2+x_1 -x_2- z) = inf_(z' in N) norm(x_2 - z') = norm(x_2 + N)_(X\/N).
  $
  For any $x in X$, we have $norm(x+N)_(X\/N) <= norm(x-0) = norm(x)$. So the quotient norm is finite.

  + (positive definiteness): for any $x in X$, since $N$ is a closed,
    $
      norm(x+N)_(X\/N) = 0 <==> d(x,N) = 0 <==> x in N <==> x+N = N.
    $

  + (absolute homogeneity): for any $x in X$, $lambda in 𝕜^(times)$,
    $
      norm(lambda (x+N))_(X\/N) = inf_(z in N) norm(lambda x - lambda z) = |lambda| inf_(z in N) norm(x - z) = |lambda| norm(x+N)_(X\/N).
    $

  + (triangle inequality): for any $x_1, x_2 in X$,
    $
      norm(x_1 + x_2 + N)_(X\/N) & = inf_(z in N) norm(x_1 + x_2 - z) \
                                 & = inf_(z_1,z_2 in N) norm(x_1 + x_2 - (z_1+z_2)) \
                                 & <= inf_(z_1,z_2 in N) norm(x_1 - z_1) + norm(x_2 - z_2) \
                                 & = inf_(z_1 in N) norm(x_1 - z_1) + inf_(z_2 in N) norm(x_2 - z_2) \
                                 & = norm(x_1 + N)_(X\/N) + norm(x_2 + N)_(X\/N).
    $
]




== Bounded Linear Operators <bounded-linear-operators>
#definition[Bounded Linear Operator][
  Let $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$ be normed spaces over $𝕜 = RR upright("or") CC$ and $T:X -> Y$ be a linear map. We say $T$ is a #strong[bounded linear operator] if $T$ is a bounded linear operator between topological vector spaces $X$ and $Y$.

]

#proposition[Equivalent Characterization of Bounded Linear Operator][
  Let $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$ be normed spaces over $𝕜 = RR upright("or") CC$ and $T:X -> Y$ be a linear map. Then the following statements are equivalent:

  + $T$ is a bounded linear operator.

  + there exists a real number $M>0$ such that for all $x in X$,
  $
    norm(T(x))_Y <= M norm(x)_X.
  $

  + $T$ is continuous.
]

#definition[Operator Norm][
  Let $T:X -> Y$ be a bounded linear operator between normed spaces $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$. The #strong[operator norm] of $T$ is defined as
  $
    norm(T)_(op("op")) = inf lr({ c>=0 : norm(T x)_Y <= c norm(x)_X " for all" x in X}).
  $
]<operator_norm>

#proposition[Equivalent Definition of Operator Norm][
  Let $T:X -> Y$ be a bounded linear operator between normed spaces $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$. Then the operator norm of $T$ can be equivalently defined as
  $
    norm(T)_(op("op")) & = inf lr({ c>=0 : norm(T x)_Y <= c norm(x)_X " for all" x in X}) \
                       & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X <= 1}) \
                       & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X < 1}) \
                       & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X in {0, 1}}) \
  $
  Furthermore, if we assume $dim X>=1$, then we have
  $
    norm(T)_(op("op")) & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X = 1}) \
                       & = sup lr({ norm(T x)_Y/norm(x)_X : x in X "and" x eq.not 0}).
  $
]

#example[Spaces of Bounded Linear Operators $B(X,Y)$][
  Let $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$ be normed spaces over $𝕜 = RR upright("or") CC$. Let $B(X,Y)$ be the set of all bounded linear operator from $X$ to $Y$. Then $B(X,Y)$ is a normed space with the #link(<operator_norm>)[operator norm]
  $
    norm(T)_(op("op")) = sup_(x in X \ norm(x)_X<=1) norm(T x)_Y .
  $
  - $B(X,Y)$ is a #link(<banach-space>)[Banach space] if and only if $Y$ is a Banach space.

  - If $X=Y$, then $B(X, X)$ is a Banach algebra under composition.

  - If $X$ is a Hilbert space, then $B(X, X)$ is a $C^*$-algebra.
]<spaces-of-bounded-linear-operators>


#definition[Norm Topology on $B(X)$][
  Let $X$ be a normed space. The #strong[norm topology] on the space of bounded linear operators $B(X)$ is the topology induced by the operator norm
  $
    norm(T)_(op("op")) = sup_(x in X \ norm(x)<=1) norm(T x).
  $
  According to @spaces-of-bounded-linear-operators, the space $B(X)$ is a Banach algebra with respect to this norm.
]


#definition[Strong Operator Topology on $B(X)$][
  Let $X$ be a normed space. Then given any $x in X$, we can define a seminorm
  $
    p_x: B(X) & --> [0, oo) \
            T & arrow.long.bar norm(T x).
  $

  The *strong operator topology* on the space of bounded linear operators $B(X)$ is the topology induced by the family of seminorms
  $
    { p_x | x in X}.
  $

  The space $B(X)$ is a locally convex TVS with respect to this topology.
]

#definition[Weak Operator Topology on $B(X)$][
  Let $X$ be a normed space. Then given any $x in X, phi.alt in X'$, we can define a seminorm
  $
    p_(x,phi.alt): B(X) & --> [0, oo) \
                      T & arrow.long.bar abs(phi.alt(T x)).
  $
  The *weak operator topology* on the space of bounded linear operators $B(X)$ is the topology induced by the family of seminorms
  $
    { p_(x, phi.alt ) | x in X, phi.alt in X'}.
  $
  The space $B(X)$ is a locally convex TVS with respect to this topology.
]
#remark[
  If $X$ is a Hilbert space, then we can identify $X'$ with $X$ and define a seminorm
  $
    p_(x,y): B(X) & --> [0, oo) \
                T & arrow.long.bar abs(lr(angle.l T x, y angle.r)).
  $
  for any $x, y in X$. The *weak operator topology* on the space of bounded linear operators $B(X)$ is the topology induced by the family of seminorms
  $
    { p_(x,y) | x, y in X}.
  $
]

#definition[Linear Isometry][
  Given two normed vector spaces $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$, a linear map $T:X -> Y$ is called a *linear isometry* if it preserves the norm, that is,
  $
    norm(T x)_Y = norm(x)_X, quad forall x in X.
  $
]<linear-isometry>

== Continous Dual Space <continuous-dual-space>

#definition[Strong Dual Space][
  Let $(X,bar.v.double dot.op bar.v.double)$ be a normed space over $𝕜 = RR upright("or") CC$. The #strong[strong dual space] of $X$ is the Banach space $X'=B(X,𝕜)$ with the operator norm
  $
    norm(f)_(op("op")) = sup_(norm(x)<=1 ) |f(x)|, quad forall f in X'.
  $
]
#theorem[Banach-Alaoglu Theorem][
  Let $(X,bar.v.double dot.op bar.v.double)$ be a normed space over $𝕜 = bb(R) upright("or") bb(C)$. Then the closed unit ball
  $
    overline(B)_1 = {f in X' : ||f||_(op("op"))= sup_(norm(x)<=1) abs(f(x)) <= 1}
  $
  is compact in $X'$ with respect to the the weak topology.
]<banach-alaoglu-theorem>


#pagebreak()

= Banach Spaces <banach-spaces>
== Basic Notions
#definition[Banach Space][
  A normed space is called a *Banach space* if it is a complete metric space with respect to the metric induced by the norm.
]<banach-space>

#proposition[Closed Subspace of Banach Space forms Banach Space][
  Let $lr((X , bar.v.double dot.op bar.v.double))$ be a Banach space and $Y$ be a linear subspace of $X$. Then $lr((Y , bar.v.double dot.op bar.v.double_Y))$ is a Banach space if and only if $Y$ is closed in $X$.
]
#proof[
  A subspace $X$ of a complete metric space $X$ is complete iff the $Y$ is closed in $X$. If $Y$ is closed in $X$, then $Y$ is complete. If $Y$ is complete, then $Y$ is closed in $X$.
]

=== $L^p$ spaces <lp-spaces>
$L^p$ spaces $thin lr((1 lt.eq p lt.eq oo))$ are Banach spaces defined on some measure space $lr((Omega , cal(F) , mu))$.

#definition[Linear Space $cal(L)^p (Omega , cal(F) , mu)$][
  Let $(Omega, cal(F), mu)$ be a measure space and $0 < p <= infinity$. Suppose
  $
    bar.v.double dot.op bar.v.double_p : {f:Omega -> CC mid(|) f upright("is measurable")} --> lr([0 , oo])
  $
  is a map defined as
  $
    norm(f)_p := cases(
      (integral_Omega abs(f)^p dif mu)^(min{1/p, 1})\, & quad 0 < p < infinity,
      , #h(0em)
      inf thin {M: abs(f) < M "a.e."}\, &quad p = infinity
    )
  $
  Then
  $
    cal(L)^p (Omega, cal(F), mu) := {f:Omega -> CC mid(|) norm(f)_p < infinity}
  $
  is a linear space. $bar.v.double dot.op bar.v.double_p$ is a seminorm on $cal(L)^p (Omega, cal(F), mu)$.]

#definition[Banach Space $L^p (Omega , cal(F) , mu)$][
  Let $(Omega , cal(F) , mu)$ be a measure space and $1 lt.eq p lt.eq oo$.
  Then
  $
    cal(N) := {f mid(|) f = 0 upright("a.e.")} = ker lr((bar.v.double dot.op bar.v.double_p)).
  $
  is a subspace of $cal(L)^p (Omega , cal(F) , mu)$ and
  $ L^p (Omega , cal(F) , mu) := cal(L)^p (Omega , cal(F) , mu) \/ cal(N) $
  is a Banach space with the norm
  $ bar.v.double dot.op bar.v.double_p : L^p (Omega , cal(F) , mu) & arrow.r \[ 0 , oo ) , \
                                                      f + cal(N) & arrow.r.bar ||f||_p . $ For
  simplicity, we can identify $f$ with its equivalence class $f + cal(N)$.

]<Banach-spaces-Lp>
#theorem[Hölder's Inequality][
  Let $(Omega , Sigma , mu)$ be a measure space and let
  $p , q in [1 , oo]$ with $1 / p + 1 / q = 1$. Then for all measurable
  real- or complex-valued functions $f$ and $g$ on $Omega$,
  $
    ||f g||_1 lt.eq ||f||_p ||g||_q
  $
  The numbers $p$ and $q$ above are said to be *Hölder conjugates* of each
  other.

  If, in addition, $p , q in (1 , oo)$ and $f in L^p (Omega , Sigma , mu)$
  and $g in L^q (Omega , Sigma , mu)$, then Hölder's inequality becomes an
  equality if and only if $lr(|f|)^p$ and $lr(|g|)^q$ are linearly
  dependent in $L^1 (Omega , Sigma , mu)$, meaning that there exist real
  numbers $alpha , beta gt.eq 0$, not both of them zero, such that
  $alpha lr(|f|)^p = beta lr(|g|)^q$ $mu$-almost everywhere.

]

#corollary[
  Let $(Omega , Sigma , mu)$ be a measure space and let $p , q, r in [1 , oo]$.

  + Suppose that $1 / p + 1 / q = 1/r$, $f in L^p (Omega , Sigma , mu)$ and $g in L^q (Omega , Sigma , mu)$. Then the product $f g$ is in $L^r (Omega , Sigma , mu)$ and
    $
      norm(f g)_r <= norm(f)_p norm(g)_q.
    $

  + Suppose that $1 / p + 1 / q + 1 / r = 1$. If $f in L^p (Omega , Sigma , mu)$ and $g in L^q (Omega , Sigma , mu)$, $h in L^r (Omega , Sigma , mu)$, then the product $f g h$ is in $L^1 (Omega , Sigma , mu)$ and
    $
      norm(f g h)_1 <= norm(f)_p norm(g)_q norm(h)_r.
    $
]


For classical functional analysis, we mainly focus on the following two types of $L^p$ spaces.

#example[$L^p lr((E))$ spaces ][
  The first type is defined on some sub measure space $E$ of the Lebesgue measure space $lr((bb(R)^n , cal(M) , mu_(cal(M))))$, written as $L^p lr((E))$ spaces. In this case, the underlying set of $L^p lr((E))$ consists all measurable functions $f$ such that $||f||_p < oo$ where
  $
    bar.v.double dot.op bar.v.double_p : {f:E->CC mid(|) f upright("is measurable")} --> lr([0 , oo])
  $
  is a map defined as
  $
    norm(f)_p ≔ cases(
      (integral_E |f|^p dif x)^(1/p)\, & quad 1 <= p < infinity \
      , #h(0em)
      inf thin lr({M: |f| <= M "a.e."})\,& quad p = infinity
    )
  $
  The norm of $L^p lr((E))$ is just the restriction of $bar.v.double dot.op bar.v.double_p$ to the underlying set of $L^p lr((E))$. Strictly speaking, measurable functions in $L^p lr((E))$ should quotient out the equivalent relation $=^(a.e.)$.
]

#example[$ell^p$ spaces][
  The second type is defined on $lr((bb(N) , 2^(bb(N)) , mu_c))$ where $2^(bb(N))$ is the power set of $bb(N)$ and $mu_c$ is the counting measure
  $
    mu_c lr((A)) = cases(
      delim: "{",
      lr(|A|) & upright(" if ") A upright(" is finite")\,,
      , oo & upright(" if ") A upright(" is infinite").
    )
  $
  $L^p lr((bb(N) , cal(P) lr((bb(N))) , mu_c))$ are often written as $ell^p$. In this case, the underlying set of $ell^p$ consists all real number sequences $x = lr((x_1 , x_2 , dots.h.c))$ such that $||x||_p < oo$ where $bar.v.double dot.op bar.v.double_p : bb(R)^(bb(N)) arrow.r lr([0 , oo])$ is defined as $ ||x||_p := cases(
    delim: "{",
    lr((thin sum_(i = 1)^oo lr(|x_i|)^p d x))^(1 / p)\, & quad 1 lt.eq p < oo,
    , #h(0em) limits(sup)_(i gt.eq 1) thin lr(|x_i|)\,
    & quad p = oo .,
  ) $
] <ellp-spaces>


#proposition[Absolutely Convergent Series is Unconditionally Convergent][
  Let $X$ be a Banach space and $(x_k)_(k=1)^n$ be a sequence in $X$. If the series $limits(sum)_(k=1)^(oo) x_k$ is absolutely convergent, then it is unconditionally convergent.
]
#proof[
  If the series $limits(sum)_(k=1)^(oo) x_k$ is absolutely convergent, then the series $limits(sum)_(k=1)^(oo) ||x_k||$ is convergent in $bb(R)$. Since convergence in $bb(R)$ is Cauchy sequence, the sequence of partial sums $S_n=limits(sum)_(k=1)^(n) ||x_k||$ is a Cauchy sequence. Therefore, for any $epsilon > 0$, there exists $N in ZZ_(>=0)$ such that for all $n >= m > N$,
  $
    |S_n - S_m| < epsilon.
  $
  Let $T_n=limits(sum)_(k=1)^(n) x_k$. Then for any $epsilon > 0$, there exists $N in ZZ_(>=0)$ such that for all $n >= m > N$,
  $
    norm(T_n - T_m) = norm(limits(sum)_(k=m+1)^n x_k) <= sum_(k=m+1)^n norm(x_k) =|S_n - S_m|< epsilon.
  $
  This means the sequence $(T_n)_(n=1)^(oo)$ is a Cauchy sequence. Since $X$ is a Banach space, $(T_n)_(n=1)^(oo)$ is convergent.

  To show the series $limits(sum)_(k=1)^(oo) x_k$ is unconditionally convergent, we need to show that for any bijection $sigma: ZZ_(>=1)-->^(tilde) ZZ_(>=1)$, the series $limits(sum)_(k=1)^(oo^(#v(1.3em))) x_(sigma(k))$ is convergent and its limit is the same as the limit of the original series. // Hack: #v(1.3em) is used to adjust the vertical spacing between oo and the exponent.

  Given $epsilon > 0$, there exists $N in ZZ_(>=1)$ such that for all $n > N$, we have
  $
    sum_(k=N+1)^oo norm(x_k) < epsilon / 2
  $
  and
  $
    norm(limits(sum)_(k=1)^(N) x_(k) - limits(sum)_(k=1)^(oo) x_k) < epsilon / 2.
  $
  Suppose $M$ is an integer such that ${1, 2, dots, N} subset.eq {sigma(1), sigma(2), dots, sigma(M)}$. Then
  $
    norm(limits(sum)_(k=1)^(M) x_(sigma(k)) - limits(sum)_(k=1)^(N) x_k) &=norm(sum_(k in {sigma(1), dots, sigma(M)}-{1, dots, N}) x_k) \
    &<= sum_(k in {sigma(1), dots, sigma(M)}-{1, dots, N}) norm(x_k)\
    & <= sum_(k=N+1)^oo norm(x_k) \
    & < epsilon / 2.
  $
  Note for any $n > M$, we still have ${1, 2, dots, N} subset.eq {sigma(1), sigma(2), dots, sigma(n)}$. Therefore, for any $n > M$, we have
  $
    norm(limits(sum)_(k=1)^(n) x_(sigma(k)) - limits(sum)_(k=1)^(oo) x_k) <= norm(limits(sum)_(k=1)^(n) x_(sigma(k)) - limits(sum)_(k=1)^(N) x_k)+ norm(limits(sum)_(k=1)^(N) x_k - limits(sum)_(k=1)^(oo) x_k) < epsilon / 2 + epsilon / 2 = epsilon.
  $
  This proves the series $limits(sum)_(k=1)^(oo) x_(sigma(k))$ is convergent and its limit is the same as the limit of the original series.
]

#proposition[Comparison Test for Series][
  Let $X$ be a Banach space and $(x_k)_(k=1)^(oo)$ be a sequence in $X$. If there exists a sequence $(a_k)_(k=1)^(oo)$ of nonnegative real numbers such that
  $
    norm(x_k) <= a_k, quad forall k in ZZ_(>=1),
  $
  and the series $limits(sum)_(k=1)^(oo) a_k$ converges, then the series $limits(sum)_(k=1)^(oo) x_k$ is absolutely convergent.
]<Banach-spaces-comparison-test>
#proof[
  Applying the comparison test for series of nonnegative real numbers, we see $limits(sum)_(k=1)^(oo) norm(x_k)$ is convergent. Therefore, the series $limits(sum)_(k=1)^(oo) x_k$ is absolutely convergent.
]




== Main Theorems

#theorem[Open Mapping Theorem][
  Let $X$ and $Y$ be Banach spaces and $T:X -> Y$ be a surjective bounded linear operator. Then $T$ is an open map.
]

#theorem[Closed Graph Theorem][
  Let $X$ and $Y$ be Banach spaces and $T:X -> Y$ be a linear map. Then the following are equivalent:

  + $T$ is continuous

  + the graph of $T$ #h(1fr)
    $
      Gamma(T) := {(x , T(x)) mid(|) x in X}
    $
    is closed in $X times Y$.
]


#theorem[Uniform Boundedness Principle][
  Let $X$ be a Banach space and $Y$ be a normed space. Let $F$ be a family of bounded linear operators $T:X -> Y$. If for every $x in X$, the set $lr({T(x) mid(|) T in F})$ is bounded in $Y$
  $
    sup_(T in F) norm(T(x))_Y < oo ,
  $
  then the family $F$ is uniformly bounded
  $
    sup_(T in F) norm(T)_(B(X,Y)) < oo.
  $
]

#theorem[Hahn-Banach Theorem][
  Let $bb(k)=RR" or "CC$. Suppose $X$ is a $bb(k)$-vector space and $Y$ is a subspace of $X$. If $p:X -> RR$ is a seminorm on $X$ and $f:Y -> bb(k)$ is a linear functional on $Y$ such that
  $
    |f(y)| <= p(y), quad forall y in Y,
  $
  then there exists a linear functional $F:X -> bb(k)$ such that
  $
      F(y) & = f(y), quad forall y in Y, \
    |F(x)| & <= p(x), quad forall x in X.
  $
]

#pagebreak()

= Hilbert space <hilbert-spaces>
== Basic Notions
#definition[Hilbert Space][
  A #strong[Hilbert space] is a complete real or complex inner product space.
]

=== $L^2$ spaces

#definition[Complex $L^2$ space][
  Let $(Omega , cal(F) , mu)$ be a measure space. On the complex Banach space #link(<Banach-spaces-Lp>)[$L^2 (Omega , cal(F) , mu)$], we can define an complex inner product as
  $
    angle.l f \, g angle.r = integral_Omega f thin overline(g) dif mu
  $
  for any complex-valued functions $f,g in L^2 (Omega , cal(F) , mu)$.
]

== Basic Constructions
=== Direct Sums <direct-sums>
#definition[Direct Sum of Hilbert Spaces][
  Let $(H_alpha)_(alpha in A)$ be a family of Hilbert spaces indexed by some index set $A$. The *direct sum* of the family $(H_alpha)_(alpha in A)$ is the vector space
  $
    H := {(x_alpha)_(alpha in A) in product_(alpha in A) H_alpha mid(|) sum_(alpha in A) norm(x_alpha)_(H_alpha)^2 < oo}
  $
  equipped with the inner product
  $
    angle.l x \, y angle.r = sum_(alpha in A) angle.l x_alpha \, y_alpha angle.r_(H_alpha), quad forall x , y in H,
  $
  where $x = (x_alpha)_(alpha in A)$ and $y = (y_alpha)_(alpha in A)$ are elements of $H$ with $x_alpha , y_alpha in H_alpha$ for each $alpha in A$.
  The direct sum $H$ is a Hilbert space with respect to this inner product.
]

== Orthogonal Projection
#proposition[][
  Let $H$ be a Hilbert space and $M subset.eq H$ be a closed convex subset of $H$. Then for any $x in H$, there exists a unique $x_0 in M$ such that
  $
    norm(x - x_0)_H = inf_(y in M) norm(x - y)_H.
  $
]
#proof[
  Denote $d:=inf_(y in M) norm(x - y)_H$.
  - *Existence*: For any $x in H$, we can find a sequence $(y_n)_(n=1)^(oo)$ in $M$ such that
    $
      lim_(n-> oo) norm(x - y_n)_H = d.
    $
    Next we show that the sequence $(y_n)_(n=1)^(oo)$ is Cauchy. By parallelogram law, we have
    $
      norm((y_m - x )+ (y_n - x))_H^2 + norm(y_m - y_n)_H^2 = 2 norm(y_m - x)_H^2 + 2 norm(y_n- x)_H^2 ,
    $
    which implies
    $
      norm(y_m - y_n)_H^2 & = 2 norm(y_m - x)_H^2 + 2 norm(y_n - x)_H^2 - norm((y_m - x )+ (y_n - x))_H^2 \
                          & = 2 norm(y_m - x)_H^2 + 2 norm(y_n - x)_H^2 - 4 norm((y_m+y_n)/2 - x)_H^2 .
    $
    Since $M$ is convex, we have
    $
      (y_m + y_n)/2 in M ==> norm((y_m+y_n)/2 - x)_H^2>= d.
    $
    Therefore, we have
    $
      norm(y_m - y_n)_H^2 <= 2 norm(y_m - x)_H^2 + 2 norm(y_n - x)_H^2 - 4 d^2.
    $
    For any $epsilon > 0$, there exists $N in ZZ_(>=1)$ such that for all $n> N$,
    $
      abs(norm(y_n - x)_H^2 - d^2) < epsilon^2 / 4.
    $
    In particular, for all $m, n > N$, we have
    $
      norm(y_m - x)_H^2 <= d^2 + epsilon^2 / 4, quad norm(y_n - x)_H^2 <= d^2 + epsilon^2 / 4.
    $
    Thus we get
    $
      norm(y_m - y_n)_H^2 <= 2 (d^2 + epsilon^2 / 4) + 2 (d^2 + epsilon^2 / 4) - 4 d^2 = epsilon^2==> norm(y_m - y_n)_H <= epsilon,
    $
    which shows that $(y_n)_(n=1)^(oo)$ is a Cauchy sequence. Since $H$ is complete, $(y_n)_(n=1)^(oo)$ is convergent. Take
    $
      x_0 = lim_(n-> oo) y_n
    $
    Since $M$ is closed, we have $x_0 in M$ and
    $
      norm(x - x_0)_H = lim_(n-> oo) norm(x - y_n)_H = d.
    $

  - *Uniqueness*: Suppose there exists another point $x_1 in M$ such that
    $
      norm(x - x_1)_H = norm(x - x_0)_H = d.
    $
    Again by the parallelogram law, we have
    $
      norm(x_0 - x_1)_H^2<= 2 norm(x_0 - x)_H^2 + 2 norm(x_1 - x)_H^2 - 4d^2=0.
    $
    This implies $x_0 = x_1$.
]
#lemma[][
  Let $H$ be a Hilbert space and $M subset.eq H$ be a closed subspace of $H$. Suppose $x in H$ and $x_0 in M$ are such that
  $
    norm(x - x_0)_H = inf_(y in M) norm(x - y)_H.
  $
  Then we have
  $
    ( x - x_0 ) perp M.
  $
]<orthogonal-decomposition-lemma>
#proposition[Orthogonal Decomposition Theorem][
  Let $H$ be a Hilbert space. Let $M$ be a closed linear subspace of $H$. Then we have
  $
    H = M plus.circle M^perp.
  $
]
#proof[
  For any $x in H$, we can find a unique $x_0 in M$ such that
  $
    norm(x - x_0)_H = inf_(y in M) norm(x - y)_H.
  $
  By @orthogonal-decomposition-lemma, we have $(x - x_0) perp M$. Therefore, we can write
  $
    x = x_0 + (x - x_0).
  $
  Since $M$ is closed, we have $x_0 in M$ and $x - x_0 in M^perp$. This shows that every element of $H$ can be written as a sum of an element in $M$ and an element in $M^perp$.

  Suppose there exists another decomposition
  $
    x= x_0 + (x - x_0)= y + z
  $
  where $y in M$ and $z in M^perp$. On the one hand, we have $y - x_0 in M$. On the other hand, we have
  $
    y - x_0 = (x-x_0) - z in M^perp.
  $
  Thus there must be $y-x_0=0$. This implies $y=x_0$ and $z=x-x_0$. This shows that the decomposition is unique.

]

#proposition[][
  Let $H$ be a Hilbert space and $M$ be a linear subspace of $H$. Then we have

  + $E^(perp perp) = overline(E)$. If $E$ is closed, then $E^(perp perp)=E$.

  + $E$ is dense in $H$ if and only if $E^perp = {0}$.
]<orthogonal-complementation-properties>


== Adjoint Operator



#proposition[][
  Let $H$ be an inner product space over $𝕜 = RR upright("or") CC$. Then for any $y in H$, the map
  $
    f:=angle.l dot , y angle.r : H & --> CC \
                                 x & --> angle.l x \, y angle.r
  $
  is a bounded linear functional on $H$. And we have $norm(f)_(op("op")) = norm(y)_H$.
]<inner-product-as-functional>


#proof[
  By the definition of inner product, we see that $f$ is linear. For any $x in H$, we have
  $
    |f(x)| = |angle.l x \, y angle.r| <= norm(x)_H norm(y)_H.
  $
  Therefore, $f$ is a bounded linear functional on $H$ and $norm(f)_(op("op")) <= norm(y)_H$.

  - If $y=0$, then $f(x)=0$ for all $x in H$, so $norm(f)_(op("op")) = 0 = norm(y)_H$.

  - If $y eq.not 0$, then we can take $y_0=y/norm(y)_H$. So we have $norm(y_0)_H = 1$ and
    $
      abs(f(y_0))=1/norm(y)_H abs(f(y)) =1/norm(y)_H angle.l y\, y angle.r= norm(y)_H,
    $
    which implies $norm(f)_(op("op")) >= norm(y)_H$. Therefore, we have $norm(f)_(op("op")) = norm(y)_H$.

]

If $H$ is a Hilbert space, then the converse
of the above proposition holds, which is known as the Riesz representation theorem.

#theorem[Riesz Representation Theorem][
  Let $H$ be a Hilbert space over $𝕜 = RR upright("or") CC$. Then for any bounded linear functional $f:H -> 𝕜$, there exists a unique $y in H$ such that
  $
    f(x) = angle.l x \, y angle.r, quad forall x in H.
  $
  Furthermore, we have $norm(f)_(op("op")) = norm(y)_H$.
]<riesz-representation-theorem>
#proof[
  Let $f$ be a bounded linear functional on $H$. If $f=0$, then we can take $y=0$ and the theorem holds trivially. If $f eq.not 0$, let $M = ker (f)$ be the kernel of $f$. Then $M$ is a closed subspace of $H$. By @orthogonal-decomposition-lemma, we have
  $
    H = M plus.circle M^perp.
  $
  Since $f eq.not 0$, we have $M=ker f eq.not H$, which implies $M$ is not dense in $H$. By @orthogonal-complementation-properties, we have $M^perp eq.not {0}$. Therefore, we can choose a $z in M^perp$ such that $norm(z)_H = 1$. Since $M inter M^perp={0}$, we see $z in.not M$ and accordingly $f(z) eq.not 0$. Now we can take
  $
    y = overline(f(z)) z in M^perp.
  $
  Note for any $x in H$,
  $
    f(f(x)/f(z) z -x)= f(x)/f(z) f(z) - f(x) = 0==> f(x)/f(z) z -x in M.
  $
  We can check that for any $x in H$,
  $
    f(x) & = f(x) angle.l z \, z angle.r \
         & = f(x)/f(z) f(z ) angle.l z \, z angle.r \
         & = lr(angle.l f(x)/f(z) z \, overline(f(z)) z angle.r) \
         & = lr(angle.l f(x)/f(z) z -x \, y angle.r) +lr(angle.l x \, y angle.r) \
         & = angle.l x \, y angle.r.
  $
  To show the uniqueness of $y$, suppose there exists another $y' in H$ such that
  $
    f(x) = angle.l x \, y' angle.r, quad forall x in H.
  $
  Then we have
  $
    angle.l x \, y - y' angle.r = f(x) - f(x) = 0, quad forall x in H.
  $
  This means $y - y'=0$ and therefore $y = y'$.
  Finally, by @inner-product-as-functional, we have $norm(f)_(op("op")) = norm(y)_H$.
]

#definition[Adjoint Operator][
  Let $X$ and $Y$ be Hilbert spaces and $T:X -> Y$ be a bounded linear operator. For any $y in Y$, the map
  $
    angle.l T (dot) \, y angle.r:X & -->CC \
                                 x & --> angle.l T x \, y angle.r
  $
  is a bounded linear functional on $X$. By the #link(<riesz-representation-theorem>)[Riesz representation theorem], there exists a unique $T^* y in X$ such that
  $
    angle.l T x \, y angle.r = angle.l x \, T^* y angle.r, quad forall x in X.
  $
  This gives a map
  $
    T^* : Y & --> X \
          y & --> T^* y
  $
  which is a bounded linear operator. We call $T^*$ the #strong[adjoint] of $T$.

]

#pagebreak()

= Banach Algebras <banach-algebras>
== Banach Algebras <basic-notions-2>

#definition[Banach Algebra][
  Suppose $𝕜 = RR upright("or") CC$. A #strong[Banach algebra] over $𝕜$ is an (not necessarily unital) associative $𝕜$-algebra $A$ equipped with a norm $bar.v.double dot.op bar.v.double$ such that $(A , bar.v.double dot.op bar.v.double)$ is a #link(<banach-spaces>)[Banach space] and the multiplication is continuous, namely
  $
    norm(x y) lt.eq norm(x) norm(y) ,quad forall x , y in A .
  $
]
#remark[
  When we mention a Banach algebra without specifying the scalar field $𝕜$, we implicitly assume $𝕜=CC$. If a more general field is considered, we explicitly state that $A$ is a $𝕜$-Banach algebra or a Banach algebra over $𝕜$.
]

#definition[Banach Algebra Homomorphism][
  Let $A$ and $B$ be $𝕜$-Banach algebras. A #strong[Banach algebra homomorphism] from $A$ to $B$ is a $𝕜$-linear map $T:A -> B$ such that

  + $T(x y) = T(x) T(y)$ for all $x , y in A$,

  + $T$ is continuous.
]


#definition[Unital Banach Algebra][
  A $𝕜$-Banach algebra $A$ is called a #strong[unital Banach algebra] if $A$ as an algebra has a multiplication unit element $1_A$ and $||1_A|| = 1$.
]

#definition[Unital Banach Algebra Homomorphism][
  Let $A$ and $B$ be unital $𝕜$-Banach algebras. A #strong[unital Banach algebra homomorphism] from $A$ to $B$ is a $𝕜$-linear map $T:A -> B$ such that
  + $T(x y) = T(x) T(y)$ for all $x , y in A$,

  + $T(1_A) = 1_B$,

  + $T$ is continuous.
]


#definition[Commutative Banach Algebra][
  A $𝕜$-Banach algebra $A$ is called a #strong[commutative Banach algebra] if $A$ as an algebra is commutative.
]

#definition[Sub Banach Algebra][
  Let $A$ be a $𝕜$-Banach algebra. A #strong[sub Banach algebra] of $A$ is a subspace $B$ of $A$ that is also a Banach algebra with respect to the norm inherited from $A$.
]

#definition[Quotient Banach Algebra][
  Let $(A, bar.v.double dot.op bar.v.double_A)$ be a $𝕜$-Banach algebra and $N$ be a closed ideal of $A$. Suppose
  $(A\/N, bar.v.double dot.op bar.v.double_(A\/N))$ is the quotient algebra equipped with #link(<quotient_norm>)[quotient norm]. Then $(A\/N, bar.v.double dot.op bar.v.double_(A\/N))$ is a $𝕜$-Banach algebra, called the *quotient Banach algebra* of $A$ by $N$.
]
#remark[
  For any $x,y in A$, we have
  $
    norm(x y + N)_(A\/N) & = inf_(z in N) norm(z-x y) \
                         & = inf_( z' + x y in N) norm(z') \
                         & =inf_( z' in -x y +N) norm(z') \
                         & =inf_( -z' in x y +N) norm(-z') \
                         & =inf_( z in x y +N) norm(z) \
                         & =inf_(u in x+N\ v in y+N) norm(u v) \
                         & <= inf_(u in x+N\ v in y+N) norm(u) norm(v) \
                         & = inf_(u in x+N) norm(u) inf_(v in y+N) norm(v) \
                         & = norm(x+N)_(A\/N) norm(y+N)_(A\/N).
  $
]

#example[Bounded Linear Operators as Banach Algebra][
  Let $(X,bar.v.double dot.op bar.v.double)$ be a Banach space over $𝕜$. The set of all bounded linear operators on $X$ is a Banach algebra $B(X)$ with respect to the operator norm
  $
    norm(T)_(B(X)) = sup lr({norm(T x) : x in X "and" norm(x) <= 1}).
  $
]


#lemma[Invertibility of $1-x$][
  Let $(A, bar.v.double dot.op bar.v.double)$ be a unital $𝕜$-Banach algebra and $x in A$. If $norm(x)<1$, then $x$ is invertible and
  $
    (1_A - x)^(-1) = sum_(n=0)^(oo) x^n.
  $
]<Banach-spaces-invertibility-1-x>
#proof[
  From $norm(x)<1$ we have
  $
    sum_(n=0)^(oo) norm(x)^n = 1 / (1-norm(x)) < oo.
  $
  For any $n in ZZ_(>=0)$, we have $norm(x^n) <= norm(x)^n$. Thus by #link(<Banach-spaces-comparison-test>)[comparison test for series], the series $limits(sum)_(n=0)^(oo) x^n$ is absolutely convergent. Note
  $
    lim_(n arrow.r oo) norm(x^n) <= lim_(n arrow.r oo) norm(x)^n = 0 ==> lim_(n arrow.r oo) x^n = 0.
  $
  So we have
  $
    (1_A - x) (sum_(n=0)^(oo) x^n) = lim_(n arrow.r oo) (1_A - x) (sum_(k=0)^(n) x^k) = lim_(n arrow.r oo) (1_A - x^(n+1)) = 1_A,
  $
  which proves the lemma.
]
#corollary[Neumann Series][
  Let $A$ be a unital $𝕜$-Banach algebra and $x in A$.

  + Suppose $lambda in CC$ and $abs(lambda)>norm(x)$. Then $lambda 1_A - x$ is invertible and
    $
      (lambda 1_A - x)^(-1) = sum_(n=0)^(oo) 1 / lambda^(n+1) x^n.
    $
  + Suppose $x in A^(times)$, $y in A$ and $norm(y)<norm(x^(-1))^(-1)$. Then $x - y$ is invertible and
    $
      (x - y)^(-1) = x^(-1)sum_(n=0)^(oo) (y x^(-1))^n.
    $
]<neumann-series>
#proof[
  + By the @Banach-spaces-invertibility-1-x, since
    $
      norm(1/lambda x) = 1 / abs(lambda) norm(x) < 1,
    $
    we have
    $
      (1_A - 1 / lambda x)^(-1) = limits(sum)_(n=0)^(oo) (1 / lambda x)^n.
    $
    Multiplying both sides by $1/lambda$ gives the result.

  + By the @Banach-spaces-invertibility-1-x, since
    $
      norm(y x^(-1)) <= norm(y) norm(x^(-1)) < 1,
    $
    we have
    $
      (1_A - y x^(-1))^(-1) = limits(sum)_(n=0)^(oo) (y x^(-1))^n.
    $
    Left multiplying both sides by $x^(-1)$ and we get
    $
      x^(-1)(1_A - y x^(-1))^(-1)=((1_A - y x^(-1))x)^(-1)=(x - y)^(-1) = x^(-1) limits(sum)_(n=0)^(oo) (y x^(-1))^n.
    $
]

#proposition[Unit Group of Unital Banach Algebra is Open][
  Let $A$ be a unital $𝕜$-Banach algebra.

  + If $x in A^(times)$, $y in A$ and $norm(y) <= 1/2 norm(x^(-1))^(-1)$, then
    $
      norm((x - y)^(-1)-x^(-1)) <= 2 norm(x^(-1))^2 norm(y) .
    $

  + $A^(times)$ is open in $A$.

  + The map
    $
      eta:A^(times) & -->A^(times) \
                  x & --> x^(-1)
    $
    is a homeomorphism.
]<Banach-spaces-unit-group-is-open>
#proof[
  + According to the @neumann-series, since $norm(y) <= 1/2 norm(x^(-1))^(-1)<norm(x^(-1))^(-1)$, we have
    $
      (x - y)^(-1) = x^(-1) limits(sum)_(n=0)^(oo) (y x^(-1))^n.
    $
    So we can write
    $
      norm((x - y)^(-1)-x^(-1)) & =norm(x^(-1) limits(sum)_(n=0)^(oo) (y x^(-1))^n-x^(-1)) \
                                & = norm(x^(-1) limits(sum)_(n=1)^(oo) (y x^(-1))^n) \
                                & <= norm(x^(-1)) limits(sum)_(n=1)^(oo) (norm(y) norm(x^(-1)))^n \
                                & <= norm(x^(-1))^2 norm(y)limits(sum)_(n=1)^(oo) (norm(y) norm(x^(-1)))^(n-1) \
                                & <= norm(x^(-1))^2 norm(y)limits(sum)_(n=1)^(oo) 1 / 2^(n-1) \
                                & <= 2 norm(x^(-1))^2 norm(y).
    $

  + Suppose $x in A^(times)$. For any $z in A$ such that $norm(z-x) < 1/2 norm(x^(-1))^(-1)$, let $y = x - z$. Then we have
    $
      norm(y) < 1 / 2 norm(x^(-1))^(-1)<norm(x^(-1))^(-1).
    $
    According to the @neumann-series, $x-y$ is invertible, which means $z=x-y in A^(times)$. Thus $B(x , 1/2 norm(x^(-1))^(-1)) subset.eq A^(times)$ is an open neighborhood of $x$. This implies $A^(times)$ is open in $A$.

  + The map $eta$ is injective since $x^(-1) = y^(-1)$ implies $x = y$. Since $eta$ is also surjective, it is a bijection. To show continuity of $eta$, consider a point $x in A^(times)$ and a sequence $(x_n)_(n=1)^(oo)$ in $A^(times)$ such that $x_n arrow x$. We need to show $x_n^(-1) arrow x^(-1)$ in $A$. For sufficiently large $n$, we have $norm(x_n - x) < 1/2 norm(x^(-1))^(-1)$. From (i) we obtain
    $
      norm(x_n^(-1) - x^(-1))=norm((x-(x-x_n))^(-1) - x^(-1)) <= 2 norm(x^(-1))^2 norm(x_n - x) .
    $
    This shows $x_n^(-1) arrow x^(-1)$ in $A$.
]

#definition[Spectrum of an Element in Banach algebra][
  Let $A$ be a unital Banach algebra and $x in A$. The #strong[spectrum] of $x$ is defined as
  $
    sigma(x) = {lambda in bb(k) : lambda 1_A - x in.not A^(times)}.
  $
]


#proposition[Properties of Spectrum ][
  Let $A$ be a unital Banach algebra and $x in A$.

  + $sigma(x)$ is a compact subset of the disc
    $
      overline(B (0 , ||x||)) = {lambda in bb(k) med : med abs(lambda) <= norm(x)}.
    $

  + $sigma(x)$ is non-empty.
]

#definition[Spectral Radius][
  Let $A$ be a unital Banach algebra and $x in A$. The #strong[spectral radius] of $x$ is defined as
  $
    rho(x) = sup lr({abs(lambda) : lambda in sigma(x)}) .
  $
]
#proposition[Spectral Radius Theorem][
  Let $A$ be a unital Banach algebra and $x in A$. Then
  $
    rho(x) = lim_(n arrow.r oo) norm(x^n)^(1 / n).
  $
]
#definition[Unital Banach Division Algebra][
  A unital Banach algebra $A$ is called a #strong[unital Banach division algebra] if every nonzero element of $A$ is invertible, namely $A^(times) = A - {0}$.
]
#theorem[Gelfand-Mazur Theorem][
  Let $A$ be a unital Banach division algebra, then $A$ is isomorphic to $CC$.
]<gelfand-mazur-theorem>


== $upright(C)^*$-Algebras <cstar-algebras>

#definition[Involutive Ring][
  An #strong[involutive rng] is a rng $R$ equipped with a involution $* : R -> R$ which is a anti-automorphism of order $2$, namely
  $
    (x + y)^* = x^* + y^* ,quad (x y)^* = y^* x^* ,quad (x^*)^* = x ,quad forall x , y in R .
  $
  An *involutive ring* is a involutive rng $R$ with a multiplicative identity $1$.
]

In an involutive ring we have $1^*=1$.

#definition[$*$-Algebra][
  Let $R$ be a commutative involutive ring with involution $overline(#hide($z$))#h(0.2em):R->R$. A #strong[$*$-algebra] over $R$ is a (not necessarily unital) associative $R$-algebra $A$ equipped with a involution $* : A -> A$ such that $(A, *)$ is a involutive ring and satisfies the following compatibility conditions
  $
    (r x)^* = overline(r) x^* ,quad forall r in R , x in A .
  $

]


#definition[$*$-homomorphism][
  Let $A$ and $B$ be $*$-algebras over a involutive ring $R$. A #strong[$*$-homomorphism] from $A$ to $B$ is a $R$-algebra homomorphism $phi:A -> B$ such that
  $
    phi(x^*) = phi(x)^* ,quad forall x in A .
  $
]


#definition[$upright(C)^*$-Algebra][
  Suppose $𝕜 = RR upright("or") CC$. A #strong[$upright(C)^*$-algebra] is a Banach $*$-algebra $A$ over $bb(k)$ such that
  $
    norm(x^* x) = norm(x)^2 ,quad forall x in A .
  $
]
#proposition[Properties of $*$-Algebra][
  Let $A$ be a $*$-algebra over a involutive ring $R$. Then the following properties hold:

  + The involution $*:A->A$ is isometric: $norm(x^*) = norm(x)$ for all $x in A$.
]
#proof[
  + Note #h(1fr)
    $
      norm(x)^2 = norm(x^* x) <= norm(x^*) norm(x) ==> norm(x) <= norm(x^*) .
    $
    Thus we have $norm(x^*) <= norm((x^*)^*) =norm(x)$.
]

#example[$C_0(X)$ for Locally Compact Hausdorff Space $X$][
  Let $X$ be a locally compact Hausdorff space. The set of all continuous complex-valued functions on $X$ vanishing at infinity is denoted by $C_0(X)$. It is a commutative $upright(C)^*$-algebra with respect to the supremum norm
  $
    norm(f)_sup = sup_(x in X) |f(x)|.
  $
  and pointwise multiplication. The involution is defined as the complex conjugation $overline(#hide($z$))#h(0.2em):f |-> overline(f)$.

  $C_0(X)$ is unital if and only if $X$ is compact. In this case, the constant function $1$ is the unit element. And we have $C_0(X) = C(X)$.
]<C_0-as-C-star-algebra>

#example[Bounded Linear Operators on a Complex Hilbert Space][
  Let $H$ be a complex Hilbert space. The set of all bounded linear operators on $H$ is a $upright(C)^*$-algebra is denoted by $B(H)$
  with respect to the operator norm and the adjoint operation.
]

=== Group Algebra $L^1(G)$


Define *left translation*
$
  L_y: op("Hom")_(sans("Set"))(X,Y) & --> op("Hom")_(sans("Set"))(X,Y) \
                                  f & mapsto.long (x mapsto.long f(y^(-1)x))
$
and *right translation*
$
  R_y: op("Hom")_(sans("Set"))(X,Y) & --> op("Hom")_(sans("Set"))(X,Y) \
                                  f & mapsto.long (x mapsto.long f(x y))
$
If $G$ is a group, then
$
  L:G & --> op("Aut")_(sans("Set"))(op("Hom")_(sans("Set"))(G,Y)) \
    y & mapsto.long L_y
$
and
$
  R:G & --> op("Aut")_(sans("Set"))(op("Hom")_(sans("Set"))(G,Y)) \
    y & mapsto.long R_y
$
are group homomorphisms.

#definition[Left Uniformly Continuous][
  If $G$ is a topological group, then a function $f:G -> CC$ is called #strong[left uniformly continuous] if
  $
    lim_(y->1_G) norm(L_y f - f)_"sup" = 0.
  $
  $f:G -> CC$ is called #strong[right uniformly continuous] if
  $
    lim_(y->1_G) norm(R_y f - f)_"sup" = 0.
  $
]
#proposition[][
  If $G$ is a topological group and $f in C_c (G)$, then $f$ is both left and right uniformly continuous.
]
#example[$L^1$ Group Algebra $L^1(G)$ for LCH Topological Group $G$][
  Let $G$ be a locally compact Hausdorff topological group and $mu$ be a Haar measure on $G$. The set of all integrable complex-valued functions on $G$ is denoted by $L^1(G, mu)$. Given $f, h in L^1(G, mu)$, define the *convolution* of $f$ and $h$ as
  $
    f * h: G & --> CC \
           x & arrow.bar.long integral_G f(y) h(y^(-1) x) dif mu(y).
  $

  Then we have

  + $
      norm(f * h)_1 <= norm(f)_1 norm(h)_1,quad forall f , h in L^1(G, mu).
    $

  + $L^1(G, mu)$ is a Banach $*$-algebra, called the *$L^1$ Group Algebra* of $G$, where the multiplication is given by the convolution operation, the norm is the $L^1$ norm, and the involution is given by
    $
      f^*(x) = Delta(x^(-1)) overline(f(x^(-1))), quad forall x in G.
    $

  +
    $
      L^1(G, mu) "is a unital Banach algebra" <==> G "is discrete".
    $

  +
    $
      L^1(G, mu) "is commutative" <==> G "is abelian".
    $
]<L1G-as-cstar-algebra>
#proof[
  First we need to show $f * h$ is well-defined for $mu$-almost every $x in G$. Define a $cal(B)(G times G)$-measurable function
  $
    F: G times G & --> [0, +oo] \
          (x, y) & arrow.bar.long abs(f(y) h(y^(-1) x)).
  $
  By #link(<fubini-tonelli-theorem-for-radon-products>)[Tonelli's theorem],
  $
    H: G & --> [0, +oo] \
       x & arrow.bar.long integral_G F(x, y) dif mu(y)
  $
  is a $cal(B)(G)$-measurable function and we have
  $
    integral_G H(x) dif mu(x) & = integral_G integral_G abs(f(y) h(y^(-1) x)) dif mu(y) dif mu(x) \
                              & = integral_G integral_G abs(f(y) h(y^(-1) x)) dif mu(x) dif mu(y) \
                              & = integral_G abs(f(y)) (integral_G abs(h(y^(-1) x)) dif mu(x)) dif mu(y) \
                              & = integral_G abs(f(y)) (integral_G abs(h(z)) dif mu(z)) dif mu(y) quad (z:= y^(-1) x) \
                              & = norm(f)_1 norm(h)_1<oo,
  $
  which implies $H in L^1(G,mu)$. Therefore, for $mu$-almost every $x in G$, we have
  $
    H(x)< oo ==> (f * h)(x) = integral_G f(y) h(y^(-1) x) dif mu(y) < oo.
  $

  + $
      norm(f * h)_1 & = integral_G abs((f * h)(x)) dif mu(x) \
                    & = integral_G abs(integral_G f(y) h(y^(-1) x) dif mu(y)) dif mu(x) \
                    & <= integral_G integral_G abs(f(y) h(y^(-1) x)) dif mu(y) dif mu(x) \
                    & = norm(f)_1 norm(h)_1.
    $

  + Associativity. Given any $f,h,k in L^1(G,mu)$,
    $
      ((f * h) * k )(x) & = integral_G (f * h)(y) k(y^(-1) x) dif mu(y) \
                        & = integral_G (integral_G f(z) h(z^(-1) y) k(y^(-1) x) dif mu(z)) dif mu(y) \
                        & = integral_G f(z)(integral_G h(z^(-1) y) k(y^(-1) x)dif mu(y)) dif mu(z) \
                        & =integral_G f(z) (integral_G h(t) k(t^(-1)z^(-1) x) dif mu(t)) dif mu(z) quad (t:=z^(-1)y) \
                        & = integral_G f(z) (h*k)(y^(-1) x) dif mu(z) \
                        & = (f*(h*k))(x).
    $

  + If $G$ is discrete, then the Haar measure $mu$ is counting measure up to a constant. In this case, define the point-mass $delta_(1_G):G->CC$ as
    $
      delta_(1_G) (x) = cases(
        1 & "if" x = 1_G, \
        0 & "if" x eq.not 1_G.
      )
    $
    Then for any $f in L^1(G, mu)$ and $x in G$, we have
    $
      (f * delta_(1_G))(x) & = integral_G f(y) delta_(1_G)(y^(-1) x) dif mu(y) \
                           & = sum_(y in G) f(y) delta_(1_G)(y^(-1) x) \
                           & = sum_(y in G) f(y) bold(1)_(y = x) \
                           & = f(x)
    $
    and
    $
      (delta_(1_G) * f)(x) & = integral_G delta_(1_G)(y) f(y^(-1) x) dif mu(y) \
                           & = sum_(y in G) delta_(1_G)(y) f(y^(-1) x) \
                           & = sum_(y in G) bold(1)_(y = 1_G) f(y^(-1) x) \
                           & = f(x).
    $
    This means $delta_(1_G)$ is the unity of $L^1(G, mu)$.
]

#proposition[
  Suppose $1 lt.eq p lt.eq oo \, f in L^1 ( G )$, and
  $g in L^p ( G )$. Let $mu$ be a Haar measure on $G$. Then

  + The integrals
    $
      integral_G f ( y ) g (y^(-1)x) dif mu(y)
    $
    converge absolutely for $mu$-almost every $x$, and we have $f * g in L^p ( G )$ and
    $
      norm(f * g)_p lt.eq norm(f)_1 norm(g)_p.
    $

  + If $G$ is unimodular,  we have $g * f in L^p ( G )$ and
    $
      norm(g * f)_p lt.eq norm(f)_1 norm(g)_p.
    $

  + If $f$ has compact support, we have $g * f in L^p ( G )$.
]
#proof[
  + We apply Minkowski's inequality to obtain

    $
      norm(f * g)_p =norm(integral_G f ( y ) L_y g ( dot.op ) dif mu(y))_p lt.eq integral_G abs(f(y)) norm(L_y g)_p dif mu(y) = norm(f)_1 norm(g)_p
    $

    since the $L^p$ norm is left-invariant. (The a.e. convergence of the integral for $f * g$ is implicit in this.)

  + If $G$ is unimodular, we apply Minkowski's inequality to 
    $
      (g * f)(x) = integral_G g(y) f(y) g(x y^(-1)) dif mu(y)
    $
    ,

    $
      norm(g * f)_p = norm(integral R_(y^(- 1)) g ( dot.op ) f ( y ) dif y)_p lt.eq integral norm(R_(y^(- 1)) g)_p abs(f ( y )) dif y = norm(g)_p norm(f)_1
    $

    which proves (b). If $K = "supp" f$ is compact, a similar argument works in the non-unimodular case:

    $
      norm(g * f)_p & = norm(integral R_(y^(- 1)) g ( dot.op ) f ( y ) Delta (y^(- 1)) dif y)_p \
                    & lt.eq integral_G norm(R_(y^(- 1)) g)_p abs(f ( y )) Delta (y^(- 1)) dif y \
                    & = norm(g)_p integral_K abs(f ( y )) Delta ( y )^(( 1 \/ p ) - 1) dif y \
                    & lt.eq C norm(g)_p norm(f)_1
    $

    where $C = sup_K Delta ( y )^(( 1 \/ p ) - 1)$.
]

#proposition[
  Suppose $G$ is unimodular. If $f in L^p ( G )$ and $g in L^q ( G )$
  where $1 < p \, q < oo$ and $p^(- 1) + q^(- 1) = 1$, then
  $f * g in C_0 ( G )$ and
  $norm(f*g)_(upright("sup")) lt.eq norm(f)_p norm(g)_q$.
]
#proof[
  The fact that
  $abs((f * g) ( x )) lt.eq norm(f)_p norm(g)_q$
  for all $x in G$ follows from Hölder's inequality and the invariance of
  Haar integrals under translations and inversions. If
  $f \, g in C_c ( G )$, it is easy to check that
  $f * g in C_c ( G )$. But $C_c ( G )$ is dense in $L^p ( G )$,
  and if
  $
    f_n arrow.long^(L^p) f,quad g_n arrow.long^(L^q) g
  $
  then
  $f_n * g_n arrow.r f * g$ and $g_n * f_n arrow.r g * f$ uniformly;
  the result follows.
]

== Gelfand Theory

#definition[Spectrum of a Commutative Unital Banach Algebra][
  Let $A$ be a commutative unital Banach algebra. A *multiplicative
    functional* on $A$ is a nonzero Banach algebra homomorphism $h:A -> CC$. The set of all multiplicative functionals on $A$ is called the *spectrum* of $A$ and is denoted by $sigma(A)$. If not specified, $sigma(A)$ is always equipped with the subspace topology as a subset of the continuous dual space $A'$ endowed with the weak$zws^*$ topology.
]

#proposition[][
  Let $A$ be a commutative unital Banach algebra and $h in sigma(A)$. Then we have

  + $h(1_A) = 1$.

  + $h$ is surjective.

  + If $x in A^(times)$, then $h(x) in CC^(times)$.

  + For any $x in A$, $abs(h(x)) <= norm(x)$. So the operator norm of $h$
    $
      norm(h)_(op("op"))=sup_(x in A \ norm(x) <= 1) abs(h(x)) <= 1.
    $
]<properties-of-multiplicative-functionals>
#proof[
  + Since $h eq.not 0$, there exists $x in A$ such that $h(x) eq.not 0$. Then $h(x) = h(1_A x) = h(1_A) h(x)$. So we have $h(1_A) = 1$.

  + For any $lambda in CC$, $h(lambda 1_A) = lambda h(1_A) = lambda$. So $h$ is surjective.

  + If $x in A^(times)$, then $h(x^(-1))h(x)=h(x^(-1) x)=h(1_A)=1$. So we have $h(x)in CC^(times)$.

  + Suppose there exists $a in A$ such that $|h(a)| > norm(a)$. According to @neumann-series, $h(a)1_A - a$ is invertible. Then by (ii) we have
    $
      h(h(a)1_A - a) = h(a)h(1_A) - h(a) = h(a) - h(a) = 0 in CC^(times),
    $
    which is a contradiction.
]

#proposition[Spectrum is Compact Hausdorff][
  Let $A$ be a commutative unital Banach algebra. Then $sigma(A)$ is a compact Hausdorff space.
]<compact-hausdorffness-of-spectrum>
#proof[
  Let $B$ be the closed unit ball of $(A', bar.v.double dot.op bar.v.double)$ where $bar.v.double dot.op bar.v.double$ is the operator norm. By the #link(<banach-alaoglu-theorem>)[Banach-Alaoglu theorem], $B$ is compact with respect to the weak$zws^*$ topology. According to the @properties-of-multiplicative-functionals, $sigma(A)$ is a subset of $B$. We need to show $sigma(A)$ is closed in $B$. Let $(h_n)_(n>=1)$ be a sequence in $sigma(A)$ such that
  $
    h_n -->^("w"^*) h
  $
  in $B$. For any $x , y in A$, we have
  $
    h(x y) = lim_(n arrow.r oo) h_n (x y) = lim_(n arrow.r oo) h_n (x) h_n (y) = h(x) h(y).
  $
  This implies $h in sigma(A)$. So $sigma(A)$ is a closed subset of $B$. Since closed subset of compact space is compact, $sigma(A)$ is compact. The Hausdorff property of $sigma(A)$ is inherited from $A'$, which is Hausdorff by @hausdorffness-of-weak-star-topology.
]

#proposition[Proper Ideals of Commutative Unital Banach Algebra][
  Let $A$ be a commutative unital Banach algebra and $frak(a)$ be a proper ideal of $A$.
  Then we have

  + $frak(a) inter A^(times) = emptyset$.

  + $overline(frak(a))$ is a proper ideal of $A$.

  + If $frak(a)$ is a maximal ideal, then $frak(a)$ is closed.
]<Banach-algebras-proper-ideals>
#proof[
  + This is a standard fact of ring theory.

  + According to standard fact of topological ring theory, $overline(frak(a))$ is a ideal of $A$. By @Banach-spaces-unit-group-is-open, $A-A^(times)$ is closed in $A$. Since $frak(a) subset.eq A-A^(times)$, we have $overline(frak(a)) subset.eq A-A^(times)$. So $overline(frak(a))$ is a proper ideal of $A$.

  + Suppose $frak(a)$ is a maximal ideal. By (ii) $overline(frak(a))$ is a proper ideal contains $frak(a)$. By the maximality of $frak(a)$, there must be $overline(frak(a)) = frak(a)$. So $frak(a)$ is closed.
]

#proposition[][
  Let $A$ be a commutative unital Banach algebra and $h in sigma(A)$. Then
  $
    ker: sigma(A) & --> op("MaxSpec")(A) \
                h & arrow.bar.long ker h = {h in sigma(A) mid(|) h(x) = 0}
  $
  is bijection.
]<bijection-between-spectrum-and-maximal-spectrum>
#proof[
  First we show $ker h$ is a maximal ideal of $A$. Since $h$ is a surjective ring homomorphism, by the first isomorphism theorem, $A \/ ker tilde.equiv h(A)=CC$. So $ker h$ is a maximal ideal of $A$.

  Next we show $ker$ is injective. Suppose $ker h_1 = ker h_2$ for some $h_1 , h_2 in sigma(A)$. Note that for any $x in A$,
  $
    h_1(x- h_1(x) 1_A) = h_1(x) - h_1(x) h_1(1_A) = 0.
  $
  So we get $x - h_1(x) 1_A in ker h_1= ker h_2$. Since $h_2(x - h_1(x) 1_A) = 0$, we have
  $
    h_2(x)=h_2(x - h_1(x) 1_A + h_1(x) 1_A) = h_1(x) h_2(1_A) = h_1(x).
  $
  This shows $ker$ is injective.

  Finally we show $ker$ is surjective. Let $frak(a)$ be a maximal ideal of $A$. By @Banach-algebras-proper-ideals, $frak(a)$ is closed. Therefore, $A \/ frak(a)$ is a Banach field. By the #link(<gelfand-mazur-theorem>)[Gelfand-Mazur theorem], $A \/ frak(a) equiv CC$. So there exists a isomorphism $psi : A \/ frak(a) ->^(tilde) CC$. Suppose $pi: A -> A \/ frak(a)$ is the canonical projection. Then $h = psi compose pi$ is a multiplicative functional on $A$ such that $ker h = frak(a)$.
]



#definition[Gelfand Transform][
  Let $A$ be a commutative unital Banach algebra. The #strong[Gelfand transform] of $A$ is the unital Banach algebra homomorphism
  $
    Gamma_A:A & -->C(sigma(A)) \
            x & arrow.bar.long (hat(x):h arrow.bar.long h(x))
  $
  where $C(sigma(A))$ is the set of all continuous complex-valued functions on $sigma(A)$.
]
#remark[
  According to the @compact-hausdorffness-of-spectrum, $sigma(A)$ is a compact Hausdorff space. From @C_0-as-C-star-algebra we see $C(sigma(A))$ is a unital Banach algebra with respect to the supremum norm
  $
    norm(v)_sup = sup_(h in sigma(A)) |v(h)|, quad forall v in C(sigma(A)).
  $
  Now we can check that $Gamma_A$ is a unital Banach algebra homomorphism.

  + $Gamma_A$ preserves the multiplication: for any $x , y in A$ and $h in sigma(A)$, we have
    $
      (hat(x y))(h) = h(x y) = h(x) h(y) = hat(x)(h) hat(y)(h).
    $
    So $Gamma_A (x y)=hat(x y) = hat(x) hat(y)=Gamma_A (x)Gamma_A (y)$.

  + $Gamma_A$ preserves the unital element: for any $h in sigma(A)$, we have
    $
      hat(1_A)(h) = h(1_A) = 1.
    $
    So $Gamma_A (1_A) = hat(1_A)=1_(C(sigma(A)))$.

  + $Gamma_A$ is bounded: for any $x in A$ and $h in sigma(A)$, we have
    $
      |hat(x)(h)| = |h(x)| <= norm(x).
    $
    So for any $x in A$, we have $norm(hat(x))_(sup) <= norm(x)$, which implies
    $
      norm(Gamma_A)_(op("op")) = sup_(x in A \
      norm(x)_(A)<=1 ) norm(hat(x))_(sup) <= 1.
    $

  + $Gamma_A$ is $CC$-linear: for any $x , y in A$, $lambda in CC$ and $h in sigma(A)$, we have
    $
      (hat(lambda x + y))(h) = h(lambda x + y) = lambda h(x) + h(y) = lambda hat(x)(h) + hat(y)(h).
    $
    So $Gamma_A (lambda x + y) = lambda Gamma_A (x) + Gamma_A (y)$.
]

#proposition[Properties of Gelfand Transform][
  Let $A$ be a commutative unital Banach algebra and $x in A$. Then we have

  + $x in A^(times)$ if and only if $hat(x)$ never vanishes on $sigma(A)$.

  + $op("im") hat(x) = sigma(x)$.

  + $norm(hat(x))_(sup) = rho(x) <= norm(x)$.
]
#proof[
  + Since
    $
      x in.not A^(times) & <==> x in frak(m) "for some" frak(m) in op("MaxSpec")(A)\
      & <==> x in ker h "for some" h in sigma(A) quad "(by" #ref(<bijection-between-spectrum-and-maximal-spectrum>)")"\
      & <==> h(x)=0 "for some" h in sigma(A) \
      & <==> hat(x)(h)=0 "for some" h in sigma(A),
    $
    we see $x in A^(times)$ $<==>$ $hat(x)$ never vanishes on $sigma(A)$.

  + From (i) we have
    $
      lambda in sigma(x) & <==> lambda 1_A - x in.not A^(times) \
                         & <==> h(lambda 1_A - x) = 0 "for some" h in sigma(A) \
                         & <==> lambda - h(x) = 0 "for some" h in sigma(A) \
                         & <==> lambda = hat(x)(h) "for some" h in sigma(A) \
                         & <==> lambda in op("im") hat(x).
    $

  + According to the definition of spectral radius, utilizing the fact that $op("im") hat(x) = sigma(x)$, we have
    $
      rho(x) = sup_(lambda in sigma(x)) abs(lambda) = sup_(lambda in op("im") hat(x)) abs(lambda) = sup_(h in sigma(A)) abs(hat(x)(h))
      = norm(hat(x))_(sup).
    $
]

#proposition[][
  Suppose $G$ is a discrete group and $mu$ be the counting measure on $G$. Define
  $
    delta_g:G & -->CC \
            a & arrow.bar.long cases(
                  gap: #0.5em,
                  1 & "if" x = g\,,
                  0 & "if" x eq.not g.
                )
  $
  Then

  + For any $f in L^1(G)$, the support of $f$

    $
      op("supp") f= {g in G mid(|) f(g) eq.not 0}
    $
    is countable and we can define
    $
      sum_(g in G) f(g) := sum_(g in op("supp") f) f(g)
    $
    This is well-defined because the summation order of absolutely convergent series does not matter.

  + ${delta_g}_(g in G)$ spans a dense subspace of $L^1(G)$.

  + $sigma(L^1(G))$ is an abelian group we have the following topological group isomorphism
    $
      Phi:sigma(L^1(G)) & --> op("Hom")_(Grp)(G,CC^(times)) \
                      h & arrow.bar.long (g arrow.bar.long h(delta_g)),
    $
    where $op("Hom")_(Grp)(G,CC^(times))$ is endowed with pointwise multiplication and pointwise convergence topology, that is, the initial topology with respect to the evaluation maps $(op("ev")_g)_(g in G)$ which are defined as
    $
      op("ev")_g:op("Hom")_(Grp)(G,CC^(times)) & -->CC^(times) \
                                           chi & arrow.bar.long chi(g).
    $

  + The Gelfand transform on $L^1(G)$ is given by
    $
           Gamma:L^1(G) & -->C(sigma(L^1(G))) \
      f=(f(g))_(g in G) & arrow.bar.long (hat(x): h arrow.bar.long sum_(n in G) f(g) h(delta_g)).
    $

]
#proof[
  + Let $mu$ be the counting measure on $G$. Given any $f in L^1(G)$, define
    $
      A_n:= {g in G mid(|) abs(f(g)) >= 1 / n}.
    $
    If $A_n$ is infinite, then we have $mu(A_n)=oo$ and
    $
      integral_(G) |f| dif mu >= integral_(A_n) |f| dif mu >= 1 / n mu(A_n) = oo,
    $
    contradicting $f in L^1(G)$. So $A_n$ is finite for all $n in ZZ_(>=1)$. This implies $op("supp") f = limits(union.big)_(n in ZZ_(>=1)) A_n$ is countable.

  + For any $f in L^1(G)$ and $epsilon > 0$, we can assume the support of $f$ is $op("supp") f = {g_n}_(n in ZZ_(>=1))$. Define $E_n={g_1,g_2,...,g_n}$, $G_n=op("supp") f-E_n$. Note that
    $
      f(a) - sum_(n=1)^(N) f(g_n) delta_(g_n)(a)= cases(
        gap: #0.9em,
        0 & " if" a in E_N,
        f(a) & " otherwise"
      ) quad = f(a)bold(1)_(G_N)(a).
    $
    As $N -> oo$, we have
    $
      norm(f - sum_(n=1)^(N) f(g_n) delta_(g_n))_(L^1(G)) = integral_(G) abs(f(a)bold(1)_(G_N)(a)) dif mu(a) = integral_(G_N) abs(f(a)) dif mu(a) --> 0.
    $

  + First we need to show $chi_h: g |-> h(delta_g)$ is a group homomorphism. Note
    $
      delta_(g_1) * delta_(g_2)(a)= sum_(x in G) delta_(g_1)(x) delta_(g_2)(x^(-1) a) = delta_(g_2)(g_1^(-1)a) = bold(1)_(g_1^(-1)a = g_2) = delta_(g_1 g_2)(a).
    $
    For any $g_1,g_2 in G$, we have
    $
      chi_h (g_1 g_2) = h(delta_(g_1 g_2)) = h(delta_(g_1)* delta_(g_2)) = h(delta_(g_1)) h(delta_(g_2)) = chi_h (g_1) chi_h (g_2).
    $
    Since $delta_(g) in L^1(G)^times$ for all $g in G$, by @properties-of-multiplicative-functionals we have $h(delta_(g)) in CC^times$. Thus $Phi(h)=chi_h in op("Hom")_(Grp)(G,CC^times)$.

    Next we show $Phi$ preserves multiplication. For any $h_1 , h_2 in sigma(L^1(G))$, we have
    $
      (Phi(h_1) Phi(h_2))(g) & = (chi_(h_1) chi_(h_2))(g) \
                             & = chi_(h_1)(g) chi_(h_2)(g) \
                             & = h_1(delta_g) h_2(delta_g) \
                             & = (h_1 h_2)(delta_g) \
                             & = Phi(h_1 h_2)(g).
    $
    To show $Phi$ is injective, suppose $h_1 , h_2 in sigma(L^1(G))$ such that $Phi(h_1) = Phi(h_2)$. Then for any $g in G$, we have
    $
      h_1(delta_g) = h_2(delta_g).
    $
    Since ${delta_g}_(g in G)$ spans a dense subspace of $L^1(G)$ and $h_1 , h_2$ are continuous, we have $h_1 = h_2$.

    Then we show $Phi$ is surjective. Let $chi in op("Hom")_(Grp)(G,CC^times)$. Define
    $
      h: L^1(G) & -->CC \
              f & arrow.bar.long sum_(g in G) f(g) chi(g).
    $
    This is a multiplicative functional: for any $f_1, f_2 in L^1(G)$, we have
    $
      h(f_1 * f_2) & = sum_(g in G) (f_1 * f_2)(g) chi(g) \
                   & = sum_(g in G) sum_(x in G) f_1(x) f_2(x^(-1) g) chi(g) \
                   & = sum_(x in G) sum_(y in x^(-1)G) f_1(x) f_2(y) chi(x y) quad("let" x^(-1) g=y) \
                   & =(sum_(x in G) f_1(x) chi(x))(sum_(y in G) f_2(y) chi(y)) \
                   & = h(f_1) h(f_2).
    $
    So $h in sigma(L^1(G))$. For any $f in L^1(G)$ and $g in G$, we have
    $
      (Phi(h))(g)=h(delta_g) = sum_(x in G) delta_g (x) chi(x) = chi(g).
    $
    So $Phi(h) = chi$. This shows $Phi$ is surjective.

    Finally we show $Phi$ is continuous. For any net $(h_i)_(i in I)$ in $sigma(L^1(G))$ such that $h_i --> h$ in $sigma(L^1(G))$, we need to show $Phi(h_i) --> Phi(h)$ in $op("Hom")_(Grp)(G,CC^times)$. For any $g in G$, we have
    $
      abs((Phi(h_i) - Phi(h))(g)) = |chi_(h_i)(g) - chi_h(g)| = |h_i (delta_g) - h (delta_g)| --> 0.
    $
    This shows $Phi$ is continuous. We still need to show
    $
      Phi^(-1):op("Hom")_(Grp)(G,CC^times) & -->sigma(L^1(G)) \
                                       chi & arrow.bar.long (f arrow.bar.long sum_(g in G) f(g) chi(g))
    $

    is continuous. For any net $(chi_i)_(i in I)$ in $op("Hom")_(Grp)(G,CC^times)$ such that $chi_i --> chi$ in $op("Hom")_(Grp)(G,CC^times)$, we need to show $Phi^(-1)(chi_i) --> Phi^(-1)(chi)$ in $sigma(L^1(G))$. For any $f in L^1(G)$, we have
    $
      abs(Phi^(-1)(chi_i)(f) - Phi^(-1)(chi)(f)) & = abs(sum_(g in G) f(g) chi_i (g) - sum_(g in G) f(g) chi(g)) \
                                                 & = abs(sum_(g in G) f(g) (chi_i (g) - chi(g))) \
                                                 & <= norm(f) norm(chi_i - chi)_(op("op")) --> 0.
    $
    This shows $Phi^(-1)$ is continuous.
]

