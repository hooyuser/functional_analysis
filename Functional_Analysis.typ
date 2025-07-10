
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/cetz:0.4.0"
#import "@local/math-notes:0.3.0": *
#import "@preview/xarrow:0.3.1": xarrow

#show: math_notes.with(title: [Functional Analysis])


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

#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)

= Topological Vector Spaces <topological-vector-spaces>
== Basic notions
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
                                & < t epsilon + (1-t)epsilon            \
                                & = epsilon.
    $

  + - Balancedness: For any $lambda in 𝕜$ with $|lambda| <= 1$, we have
      $
        p(lambda x) & = |lambda| p(x) \
                    & <= p(x)         \
                    & < epsilon,
      $
      which implies $lambda x in B(0,epsilon)$.

    - Absorbingness: For any $x in X$, we can take $r = p(x) / epsilon$. Then for any $lambda in 𝕜$ with $|lambda| > r$, we have
      $
        p(1/lambda x) & = abs(1/lambda) p(x) \
                      & < p(x)/r             \
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
  Let $W_op("seq")$ be the linear space of all sequences of complex numbers. Then $W_op("seq")$ is a Fréchet space with the metric
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
    d(x,y) & = sum_(n=1)^oo 1 / (2^n) (|x_n - y_n|) / (1+|x_n-y_n|)                                                         \
           & = sum_(n=1)^oo 1 / (2^n) (|x_n - z_n|+|z_n-y_n|) / (1+|x_n - z_n|+|z_n-y_n|)                                   \
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
    X & --> bb(k)             \
    x & arrow.long.bar b(x,y)
  $
  is continuous. The weak topology on $X$ is denoted by $tau(X, Y, b)$.

  Similarly, the #strong[weak topology on $Y$] is the weakest topology on $Y$ such that for any $x in X$, the functional
  $
    Y & --> bb(k)             \
    y & arrow.long.bar b(x,y)
  $
  is continuous. The weak topology on $Y$ is denoted by $tau(Y, X, b)$.
]

#proposition[Weak Topology can be Induced by a Family of Seminorms][
  Let $(X,Y,b)$ be a dual pairing. Then $(X,tau(X, Y, b))$ is a locally convex TVS and the weak topology on $X$ is determined by a family of seminorms $(p_y)_(y in Y)$ defined by
  $
    p_y: X & --> RR                   \
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
    angle.l dot, dot angle.r : X' times X & -> 𝕜                                       \
                                    (f,x) & arrow.long.bar angle.l f, x angle.r = f(x)
  $
  is called the *canonical pairing* of $X$.

  - The *weak$zws^*$ topology on $X'$* is $tau(X', X, angle.l dot, dot angle.r)$, which is the weakest topology on $X'$ such that for any $x in X$, the functional
    $
      angle.l dot, x angle.r:X' & --> kk              \
                              f & arrow.long.bar f(x)
    $
    is continuous. That is, the weak$zws^*$ topology is the initial topology on $X'$ with respect to $(angle.l dot, x angle.r)_(x in X)$, i.e. the pointwise convergence topology on $X'$.

    More explicitly, the weak$zws^*$ topology on $X'$ is the topology generated by the collection of sets
    $
      {angle.l dot, x angle.r^(-1)(U) in 2^X' mid(|) U "is open in" kk "and" x in X}.
    $

  - The *weak topology on $X'$* is $tau(X', X'', angle.l dot, dot angle.r)$, which is the weakest topology on $X'$ such that for any $v in X''$, the functional
    $
      angle.l v, dot angle.r:X' & --> bb(k)           \
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
      op("ev")_x: X' & --> kk                    \
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

== Locally Integrable Functions

#definition[Locally Integrable Functions][
  Let $U$ be an open subset of $bb(R)^d$. A Lebesgue measurable function $f:U -> bb(C)$ is called #strong[locally integrable] if for every compact subset $K subset.eq U$, the Lebesgue integral
  $
    integral_K |f(x)| dif x
  $
  is finite. The set of all locally integrable functions on $U$ is a complete metrizable TVS, denoted by
  $
    L^1_("loc")(U)= {f:U -> bb(C) mid(|) f "is Lebesgue measurable and "f|_K in L^1(K) "for all compact "K subset.eq U}.
  $
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



== Spaces of Test Functions

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
  Let $U$ be an non-empty open subset of $bb(R)^d$. Suppose $k in ZZ_(>=0)union {oo}$. The #strong[space of $C^k$-continuous functions] $C^k (U)$ is the topological vector space consisting of all $k$-times continuously differentiable functions on $U$. For any non-empty compact subset of $K$ of $U$, any integer $m in ZZ$ with $0<=m<=k$ and any multi-index $alpha in ZZ_(>=0)^n$ with length $|alpha|<=m$, we can define seminorms
  $
    p_(alpha , K,1)(f) & =sup_(x in K) |partial^alpha f(x)|                  \
        p_(m , K,2)(f) & =sup_(|beta| <= m) p_(alpha , K,1)(f)               \
        p_(m , K,3)(f) & =sup_(x in K\ |beta| <= m) |partial^alpha f(x)|     \
        p_(m , K,4)(f) & =sup_(x in K) (sum_(|beta|<=m) |partial^beta f(x)|)
  $
  on $C^k (U)$. Each of the following families of seminorms
  $
    & {p_(alpha , K,1) mid(|)K subset.eq U "is compact" , alpha in ZZ_(>=0)^n "satisfies" |alpha|<=k}    \
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
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[space of test functions] $C^(oo)_c (U)$ is the topological vector space consisting of all smooth functions on $U$ with compact support. Suppose $cal(K)={K_j}_(j in J)$ is a collection of compact subsets of $U$ such that
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


== Space of Distributions

#definition[Space of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[space of distributions] $D'(U)$ is the continuous dual space of the space of test functions $C^(oo)_c (U)$. $D'(U)$ is endowed with the strong dual topology, which makes $D'(U)$ a locally convex TVS.
]



#definition[Weak$zws^*$ Topology on the Space of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[weak$zws^*$ topology] on the space of distributions $D'(U)$ is the weakest topology on $D'(U)$ such that for any $f in C^(oo)_c (U)$, the functional
  $
    D'(U) & --> bb(k)           \
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


== Space of Continuous Functions with Compact Support
For any open subsets $U$ of $bb(R)^d$, The inclusion map $iota:C^(oo)_c (U) arrow.hook C^(0)_c (U)$ is a continuous injection whose image is dense in $C^(0)_c (U)$. So the transpose map $iota^*:C^(0)_c (U)' -> C^(oo)_c (U)'$ is also a continuous injection.


#theorem[Riesz–Markov–Kakutani Representation Theorem][
  Let $X$ be a locally compact Hausdorff space and $T$ is a positive linear functional on $C_c^0 (X)$, the space of continuous functions with compact support on $X$. Then there exists a unique positive Borel measure $mu$ on $(X,cal(B)(X),mu)$ such that
  + for all $f in C_c^0 (X)$,#h(1fr)
    $
      T(f) = integral_X f dif mu
    $

  + $mu(K)<oo$ for all compact subsets $K$ of $X$.

  + If $B$ is an open subset of $X$, or $B$ is a Borel set with $mu(B)<oo$, then
    $
      mu(B) = sup{ mu(K) mid(|) K "is compact and" K subset.eq B}.
    $

  + If $B$ is a Borel set, then
    $
      mu(B) = inf{ mu(U) mid(|) U "is open and" B subset.eq U}.
    $
  If all open sets in $X$ are $σ$-compact, then the measure $mu$ is a Radon measure.

]
#remark[
  $RR^d$ is $sigma$-compact. So any positive linear functional $T in C_c^0 (RR^d)^*$ can be represented as
  $
    T(f) = integral_(RR^d) f dif mu
  $
  for some Radon measure $mu$ on $RR^d$.
]


By the Riesz–Markov–Kakutani representation theorem, the space $C_c^0 (X)'$ can be identified with the space of Radon measures on $X$.

One particularly important class of Radon measures are those that are induced locally integrable functions. There is a bijective correspondence between locally integrable functions $f$ on $X$ and linear functionals $T_f$ on $C_c^0 (X)$ defined by
$
  T_f (g) = integral_X g f dif x,quad forall g in C_c^(oo) (X).
$

If $f$ and $g$ are locally integrable functions on $X$, then $T_f=T_g$ if and only if $f=g$ almost everywhere.

== Vector-Valued Integrals

#definition[Weakly Integrable][
  Suppose $(X,Sigma, mu)$ is a measure space and $Y$ is a locally convex topological vector space over $𝕜 = bb(R) upright("or") bb(C)$. A function $f:X -> Y$ is said to be *weakly integrable* if for any $phi in Y'$, we have
  $
    phi compose f in L^1 (X, Sigma, mu).
  $
  In this case, if there is a vector $y in Y$ such that for any $phi in Y'$,
  $
    integral_X phi compose f dif mu = phi (y),
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

]

#proposition[][
  Let $X$ be a locally compact Hausdorff space and $mu$ be a Radon measure on $X$. Let $Y$ be a Banach space over $𝕜 = bb(R) upright("or") bb(C)$. Suppose $g in L^1(X, scr(B)(X), mu)$ is a $𝕜$-valued function, and $f:X -> Y$ is bounded continuous function. Then

  - $g f$ is weakly integrable.#h(1fr)

  - The integral $integral_X g f dif mu$ exists and
    $
      integral_X g f dif mu in overline(op("span")_𝕜 (f(X))) .
    $

  - 
   $
    norm(integral_X g f dif mu)_(Y) <= sup_(x in X)norm(f(x)) integral_X |g| dif mu.
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

  + Translation Invariance: $d(x, S + y) = d(x - y, S)$ for all $x, y in X$.

  + Convexity: if $S$ is convex, then $x|-> d(x,S)$ is convex.

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
      norm(x_1 + x_2 + N)_(X\/N) & = inf_(z in N) norm(x_1 + x_2 - z)                                \
                                 & = inf_(z_1,z_2 in N) norm(x_1 + x_2 - (z_1+z_2))                  \
                                 & <= inf_(z_1,z_2 in N) norm(x_1 - z_1) + norm(x_2 - z_2)           \
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
                       & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X <= 1})           \
                       & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X < 1})            \
                       & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X in {0, 1}})      \
  $
  Furthermore, if we assume $dim X>=1$, then we have
  $
    norm(T)_(op("op")) & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X = 1})         \
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
    p_x: B(X) & -> [0, oo)     \
            T & --> norm(T x).
  $

  The *strong operator topology* on the space of bounded linear operators $B(X)$ is the topology induced by the family of seminorms
  $
    { p_x | x in X}.
  $

  The space $B(X)$ is a locally convex TVS with respect to this topology.
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
  $ bar.v.double dot.op bar.v.double_p : L^p (Omega , cal(F) , mu) & arrow.r \[ 0 , oo \) , \
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
  and $g in L^q (Omega , Sigma , mu)$, then Hölder’s inequality becomes an
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
      F(y) & = f(y), quad forall y in Y,  \
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
    f:=angle.l dot , y angle.r : H & --> CC                     \
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
    f(x) & = f(x) angle.l z \, z angle.r                                         \
         & = f(x)/f(z) f(z ) angle.l z \, z angle.r                              \
         & = lr(angle.l f(x)/f(z) z \, overline(f(z)) z angle.r)                 \
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
    angle.l T (dot) \, y angle.r:X & -->CC                        \
                                 x & --> angle.l T x \, y angle.r
  $
  is a bounded linear functional on $X$. By the #link(<riesz-representation-theorem>)[Riesz representation theorem], there exists a unique $T^* y in X$ such that
  $
    angle.l T x \, y angle.r = angle.l x \, T^* y angle.r, quad forall x in X.
  $
  This gives a map
  $
    T^* : Y & --> X     \
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
    norm(x y + N)_(A\/N) & = inf_(z in N) norm(z-x y)                      \
                         & = inf_( z' + x y in N) norm(z')                 \
                         & =inf_( z' in -x y +N) norm(z')                  \
                         & =inf_( -z' in x y +N) norm(-z')                 \
                         & =inf_( z in x y +N) norm(z)                     \
                         & =inf_(u in x+N\ v in y+N) norm(u v)             \
                         & <= inf_(u in x+N\ v in y+N) norm(u) norm(v)     \
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



#example[$L^1(G)$ for Locally Compact Hausdorff Topological Group $G$][
  Let $G$ be a locally compact Hausdorff topological group and $mu$ be a Haar measure on $G$. The set of all integrable complex-valued functions on $G$ is denoted by $L^1(G, mu)$. It is a commutative Banach algebra with respect to the convolution product
  $
    (f * h)(x) = integral_G f(y) h(y^(-1) x) dif mu(y).
  $
  $L^1(G, mu)$ is a unital Banach algebra if and only if $G$ is discrete.
]
#proof[
  If $G$ is discrete, then the Haar measure $mu$ is counting measure up to a constant. In this case, define the point-mass $delta_(1_G):G->CC$ as
  $
    delta_(1_G) (x) = cases(
      1 & "if" x = 1_G, \
      0 & "if" x eq.not 1_G.
    )
  $
  Then for any $f in L^1(G, mu)$ and $x in G$, we have
  $
    (f * delta_(1_G))(x) & = integral_G f(y) delta_(1_G)(y^(-1) x) dif mu(y) \
                         & = sum_(y in G) f(y) delta_(1_G)(y^(-1) x)         \
                         & = sum_(y in G) f(y) bold(1)_(y = x)               \
                         & = f(x)
  $
  and
  $
    (delta_(1_G) * f)(x) & = integral_G delta_(1_G)(y) f(y^(-1) x) dif mu(y) \
                         & = sum_(y in G) delta_(1_G)(y) f(y^(-1) x)         \
                         & = sum_(y in G) bold(1)_(y = 1_G) f(y^(-1) x)      \
                         & = f(x).
  $
  This means $delta_(1_G)$ is the unity of $L^1(G, mu)$.
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
      norm((x - y)^(-1)-x^(-1)) & =norm(x^(-1) limits(sum)_(n=0)^(oo) (y x^(-1))^n-x^(-1))                     \
                                & = norm(x^(-1) limits(sum)_(n=1)^(oo) (y x^(-1))^n)                           \
                                & <= norm(x^(-1)) limits(sum)_(n=1)^(oo) (norm(y) norm(x^(-1)))^n              \
                                & <= norm(x^(-1))^2 norm(y)limits(sum)_(n=1)^(oo) (norm(y) norm(x^(-1)))^(n-1) \
                                & <= norm(x^(-1))^2 norm(y)limits(sum)_(n=1)^(oo) 1 / 2^(n-1)                  \
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
  Let $H$ be a complex Hilbert space. The set of all bounded linear operators on $H$ is a $upright(C)^*$-algebra is denoted by $B(H)$.
  with respect to the operator norm and the adjoint operation.
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
    ker: sigma(A) & --> op("MaxSpec")(A)                                   \
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
    Gamma_A:A & -->C(sigma(A))                                \
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
      lambda in sigma(x) & <==> lambda 1_A - x in.not A^(times)                \
                         & <==> h(lambda 1_A - x) = 0 "for some" h in sigma(A) \
                         & <==> lambda - h(x) = 0 "for some" h in sigma(A)     \
                         & <==> lambda = hat(x)(h) "for some" h in sigma(A)    \
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
      Phi:sigma(L^1(G)) & --> op("Hom")_(Grp)(G,CC^(times))             \
                      h & arrow.bar.long (g arrow.bar.long h(delta_g)),
    $
    where $op("Hom")_(Grp)(G,CC^(times))$ is endowed with pointwise multiplication and pointwise convergence topology, that is, the initial topology with respect to the evaluation maps $(op("ev")_g)_(g in G)$ which are defined as
    $
      op("ev")_g:op("Hom")_(Grp)(G,CC^(times)) & -->CC^(times)          \
                                           chi & arrow.bar.long chi(g).
    $

  + The Gelfand transform on $L^1(G)$ is given by
    $
           Gamma:L^1(G) & -->C(sigma(L^1(G)))                                                     \
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
      (Phi(h_1) Phi(h_2))(g) & = (chi_(h_1) chi_(h_2))(g)  \
                             & = chi_(h_1)(g) chi_(h_2)(g) \
                             & = h_1(delta_g) h_2(delta_g) \
                             & = (h_1 h_2)(delta_g)        \
                             & = Phi(h_1 h_2)(g).
    $
    To show $Phi$ is injective, suppose $h_1 , h_2 in sigma(L^1(G))$ such that $Phi(h_1) = Phi(h_2)$. Then for any $g in G$, we have
    $
      h_1(delta_g) = h_2(delta_g).
    $
    Since ${delta_g}_(g in G)$ spans a dense subspace of $L^1(G)$ and $h_1 , h_2$ are continuous, we have $h_1 = h_2$.

    Then we show $Phi$ is surjective. Let $chi in op("Hom")_(Grp)(G,CC^times)$. Define
    $
      h: L^1(G) & -->CC                                    \
              f & arrow.bar.long sum_(g in G) f(g) chi(g).
    $
    This is a multiplicative functional: for any $f_1, f_2 in L^1(G)$, we have
    $
      h(f_1 * f_2) & = sum_(g in G) (f_1 * f_2)(g) chi(g)                                            \
                   & = sum_(g in G) sum_(x in G) f_1(x) f_2(x^(-1) g) chi(g)                         \
                   & = sum_(x in G) sum_(y in x^(-1)G) f_1(x) f_2(y) chi(x y) quad("let" x^(-1) g=y) \
                   & =(sum_(x in G) f_1(x) chi(x))(sum_(y in G) f_2(y) chi(y))                       \
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
      Phi^(-1):op("Hom")_(Grp)(G,CC^times) & -->sigma(L^1(G))                                           \
                                       chi & arrow.bar.long (f arrow.bar.long sum_(g in G) f(g) chi(g))
    $

    is continuous. For any net $(chi_i)_(i in I)$ in $op("Hom")_(Grp)(G,CC^times)$ such that $chi_i --> chi$ in $op("Hom")_(Grp)(G,CC^times)$, we need to show $Phi^(-1)(chi_i) --> Phi^(-1)(chi)$ in $sigma(L^1(G))$. For any $f in L^1(G)$, we have
    $
      abs(Phi^(-1)(chi_i)(f) - Phi^(-1)(chi)(f)) &= abs(sum_(g in G) f(g) chi_i (g) - sum_(g in G) f(g) chi(g)) \
      &= abs(sum_(g in G) f(g) (chi_i (g) - chi(g))) <= norm(f) norm(chi_i - chi)_(op("op")) --> 0.
    $
    This shows $Phi^(-1)$ is continuous.
]

