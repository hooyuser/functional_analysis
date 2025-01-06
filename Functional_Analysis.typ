
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/cetz:0.3.1"
#import "@local/math-notes:0.1.0": *
#import "@preview/xarrow:0.3.1": xarrow

#show: math_notes.with(title: [Functional Analysis])


#let injlim = $limits(limits(lim)_(xarrow(#v(-50em), width: #1.8em)))$
#let projlim = $limits(limits(lim)_(xarrow(sym:arrow.l.long, #v(-50em), width: #1.8em)))$



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


#proposition()[Topological Field Induces Topological Vector Space][
  Let $𝕜$ be a topological field and $V$ be a (merely algebraic) $𝕜$-vector space. Suppose
  $
    phi: V -->^(tilde) product_(i in I) 𝕜
  $
  is a $k$-linear isomorphism. Then we can use $phi$ to define a topology on $V$ such that $U subset.eq V$ is open if and only if $phi(U)$ is open in $product_(i in I) 𝕜$. Then $V$ is a topological vector space.
]

#definition[Balanced Set][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. A subset $A$ of $X$ is said to be #strong[balanced] if for every scalar $lambda in 𝕜$ with $|lambda| <= 1$, we have
  $
    lambda A = {lambda x mid(|) x in A} subset.eq A.
  $
]

#definition[Absorb][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space and $A$, $B$ be two subsets of $X$. We say $A$ #strong[absorb] $B$ if there exists a real number $r>0$ such that for any scalar $lambda  in 𝕜$ with $|lambda| > r$, we have
  $
    B subset.eq lambda A= {lambda x mid(|) x in A}.
  $
]

#definition[Absorbing Set][
  A subset $A$ of a vector space $V$ is called an #strong[absorbing set] if $A$ absorbs ${x}$ for every $x in V$. That is, for every $x in V$, there exists a real number $r>0$ such that for any scalar $lambda in 𝕜$ with $|lambda| > r$, we have $x in lambda A$.

]

#definition[von Neumann Bounded Set][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. A subset $S$ of $X$ is called a #strong[von Neumann bounded set] if $S$ is absorbed by every neighborhood of $0$.
]

A locally convex topological vector space has a bounded neighborhood of 0 if and only if its topology can be defined by a single seminorm.

#definition[Bounded Linear Operator][
  Let $X$ and $Y$ be topological vector spaces over $𝕜 = bb(R) upright("or") bb(C)$. A #strong[bounded linear operator] from $X$ to $Y$ is a linear map $T:X -> Y$ that maps von Neumann bounded subsets of $X$ to von Neumann bounded subsets of $Y$.
]


#definition[Locally Convex Topological Vector Space][
  A topological vector space is called #strong[locally convex ] if it has a neighborhood basis at $0$ consisting of balanced convex sets.
]
The category of locally convex topological vector spaces $sans("LCTVS")_𝕜$ is the full subcategory of $sans("TVS")_𝕜$ consisting of locally convex topological vector spaces.
#proposition[][
  Suppose that $V$ is a topological vector space. If $cal(B)$ is a collection of convex, balanced, and absorbing subsets of $V$, then the set of all positive scalar multiples of finite intersections of sets in $cal(B)$ forms a neighborhood basis at $0$. Thus $cal(B)$ defines a topology $tau$ on $V$. Furthermore, $(V, tau)$ is a locally convex topological vector space.
]<topology-of-locally-convex-tvs-determined-by-neighborhood-basis>

#definition[Fréchet Space][
  A #strong[Fréchet space] is a  complete metrizable locally convex TVS.
]

#proposition[][
  A locally convex TVS is a Fréchet space if and only if it is metrizable by a complete translation-invariant metric.
]

#definition[Seminormable space][
  A topological vector space is called #strong[seminormable] if the topology of the space is induced from a single seminorm. 
]

#proposition[Properties of Seminormable Spaces][
  + A locally convex TVS is seminormable if and only if 0 has a bounded neighborhood.

  + Any locally convex TVS with topology induced by a finite family of seminorms is seminormable. 

  + If a Hausdorff locally convex TVS is seminormable, and the topology is induced from a single seminorm $p$, then $p$ is a norm.
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
    X &--> bb(k) \
    x & arrow.long.bar b(x,y)
  $
  is continuous. The weak topology on $X$ is denoted by $tau(X,Y,b)$.

  Similarly, the #strong[weak topology on $Y$] is the weakest topology on $Y$ such that for any $x in X$, the functional
  $
    Y &--> bb(k) \
    y & arrow.long.bar b(x,y)
  $
  is continuous. The weak topology on $Y$ is denoted by $tau(Y,X,b)$.
]

#proposition[][
  Let $(X,Y,b)$ be a dual pairing. Then $(X,tau(X,Y,b))$ is a locally convex TVS and the weak topology on $X$ is determined by a family of seminorms $(p_y)_(y in Y)$ where
  $
    p_y: X &--> RR \
    x & arrow.long.bar |b(x,y)|.
  $
]
#proof[
  First we show that for any $y in Y$, $p_y$ is a seminorm. 

  + Triangle inequality. For any $x_1, x_2 in X$, we have 
    $
    p_y(x_1+x_2)=abs(b(x_1 +  x_2, y)) = abs(b(x_1, y) +  b(x_2, y)) <= |b(x_1, y)| + abs(b(x_2, y)) = p_y (x_1) + p_y (x_2).
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
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. The #strong[continuous dual space] of $X$ is the set of all continuous linear functionals $X-> bb(k)$.
]

#definition[Weak and Weak$zws^*$ Topologies][
  Let $X$ be a topological vector space over a field $𝕜$. Then $(X',X, angle.l dot, dot angle.r)$ where
  $
    angle.l dot, dot angle.r : X' times X &-> 𝕜 \
    (T,f) & arrow.long.bar  angle.l T, f angle.r = T(f)
  $
  is called the *canonical pairing* of $X$. 
  
  The *weak topology on $X$* is the weakest topology on $X$ such that for any $T in X'$, the functional $T:X -> bb(k)$ is continuous. More explicitly, the weak topology on $X$ is the topology generated by the collection of sets
  $
    {T^(-1)(U) in 2^X mid(|) U "is open in" bb(k) "and" T in X'},
  $
   
  The *weak$zws^*$ topology on $X'$* is the weakest topology on $X'$ such that for any $x in X$, the functional 
  $
  angle.l dot, x angle.r:X' &--> bb(k)\
  T &arrow.long.bar T(x)
  $
  is continuous. More explicitly, the weak$zws^*$ topology on $X$ is the topology generated by the collection of sets
  $
    {angle.l dot, x angle.r^(-1)(U) in 2^X' mid(|) U "is open in" bb(k) "and" x in X}.
  $
  
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

#definition[Weak Topology on the Dual Space][
  Suppose $𝕜 = RR "or" CC$. Let $X$ be a topological $𝕜$-vector space. The #strong[weak topology] on the continuous dual space $X'$ of $X$ is the topology generated by the family of seminorms
  $
    norm(f)_x = |f(x)|
  $
  for all $x in X$.
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


#definition[Seminorm-induced Topology][
  Let $X$ be a vector space and $p:X -> RR$ be a seminorm on $X$. The #strong[seminorm-induced topology] on $X$ is the topology induced by the canonical pseudometric
  $
    d(x,y) = p(x-y) ,quad forall x,y in X.
  $
]

#definition[Spaces of $C^k$-differentiable Functions on Open Sets][
  Let $U$ be an non-empty open subset of $bb(R)^d$. Suppose $k in ZZ_(>=0)union {oo}$. The #strong[space of $C^k$-continuous functions] $C^k (U)$ is the topological vector space consisting of all $k$-times continuously differentiable functions on $U$. For any non-empty compact subset of $K$ of $U$, any integer $m in ZZ$ with $0<=m<=k$ and any multi-index $alpha in ZZ_(>=0)^n$ with length $|alpha|<=m$, we can define seminorms
  $
    p_(alpha , K,1)(f)&=sup_(x in K) |partial^alpha f(x)|\
    p_(m , K,2)(f)&=sup_(|beta| <= m) p_(alpha , K,1)(f)\
    p_(m , K,3)(f)&=sup_(x in K\ |beta| <= m) |partial^alpha f(x)|\
    p_(m , K,4)(f)&=sup_(x in K) (sum_(|beta|<=m) |partial^beta f(x)|)
  $
  on $C^k (U)$. Each of the following families of seminorms
  $
    &{p_(alpha , K,1) mid(|)K subset.eq U "is compact" , alpha in ZZ_(>=0)^n "satisfies" |alpha|<=k}\
    &{p_(m , K,j) mid(|) K subset.eq U "is compact" ,m in ZZ_(>=0) "satisfies" m<=k}, quad j in {2,3,4}
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
  $RR^d$ is $sigma$-compact. So any positive linear functional  $T in C_c^0 (RR^d)^*$ can be represented as 
  $
    T(f) = integral_(RR^d) f dif mu
  $
  for some Radon measure $mu$ on $RR^d$.
]

#definition[Space of Test Functions $C^(oo)_c (U)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$. The #strong[space of test functions] $C^(oo)_c (U)$ is the topological vector space consisting of all smooth functions on $U$ with compact support. Suppose $cal(K)={K_j}_(j in J)$ is a collection of compact subsets of $U$ such that
  + $U = union.big_(j in J) K_j$,
  + For any $K_(j_1) , K_(j_2) in cal(K)$, there exists a compact subset $K_(j_3) in cal(K)$ such that $K_(j_1) union K_(j_2) subset.eq K_(j_3)$.
  For any $K in cal(K)$, endow $C^(oo) (K)$ with the subspace topology induced by the topology on $C^(oo) (U)$. Then
  $
    {V subset.eq C^(oo)_c (U) mid(|) V "is convex," V sect C^(oo) (K) "is a neighborhood of" 0 "in" C^(oo) (K) "for all" K in cal(K)} ,
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
  #commutative_diagram($
    &X&\
    & C^(oo)_c (U) edge("u",#left,tilde(T), "-->")&\
    C^(oo)(K_i)edge("ru",#right, op("ext")_(K_i arrow.hook U),->)edge("ruu",T_(i),->) edge("rr",#right, op("ext")_(K_i arrow.hook K_j),->)&& C^(oo)(K_j) edge("lu",#left,op("ext")_(K_j arrow.hook U),->)edge("luu",T_j,->)
  $)
  As a set, $C^(oo)_c (U)=union.big _(j in J) C^(oo)(K_j)$ is the union of all $C^(oo)(K_j)$ with $K_j in cal(K)$.
  The topology on $C^(oo)_c (U)$ is the finest locally convex topology that makes all of the inclusion maps $op("ext")_(K_j subset.eq U):C^(oo) (K_j) arrow.hook C_c^(oo) (U)$ continuous.
]

#proposition[Properties of $C_c^(oo) (U)$][
  Let $U$ be an non-empty open subset of $bb(R)^d$. Then the following properties hold for the space of test functions $C^(oo)_c (U)$:

  + $C^(oo)_c (U)$ is a complete Hausdorff locally convex TVS that is  not metrizable.

  + The space $C^(oo)_c (U)$ is a reflexive  nuclear Montel space.

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
    D'(U) &--> bb(k) \
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
  + $D'(U)$ is a complete  Hausdorff nuclear space that is not metrizable.

  + $D'(U)$ is locally convex bornological space. Specifically, a linear map from $D'(U)$ into another locally convex TVS is continuous if and only if it is sequentially continuous at $0$.

]


#proposition[Equivalent Characterization of Convergence of Sequence of Distributions][
  Let $U$ be an non-empty open subset of $bb(R)^d$ and $(T_n)_(n=1)^(oo)$ be a sequence in $D'(U)$. Then the following statements are equivalent:

  + The sequence $(T_k)_(n=1)^(oo)$ converges to $T in D'(U)$ in the strong dual topology.

  + The sequence $(T_k)_(n=1)^(oo)$ converges to $T in D'(U)$ in the weak$zws^*$ topology.

  + For every $f in C^(oo)_c (U)$, the sequence $(T_n (f))_(i=1)^(oo)$ converges to $T(f)$ in $bb(k)$.
]


#pagebreak()

= Normed Spaces <metric-spaces-and-normed-spaces>


== Normed Spaces <normed-spaces>
=== Basic notions <basic-notions-1>
#definition[Normed Space][
  Given a vector space $X$ over $𝕜 = bb(R) upright("or") bb(C)$. A *norm* on $X$ is a mapping $bar.v.double dot.op bar.v.double : X arrow.r bb(R)$ which satisfies the following conditions:

  + (positive definiteness): $forall x in X ,||x|| gt.eq 0$ and $||x|| = 0 arrow.l.r.double x = 0$,

  + (absolute homogeneity): $forall x in X ,  forall lambda in 𝕜 , ||lambda x||= lr(|lambda|) norm(x)$,

  + (triangle inequality): $forall x , y in X ,  ||x + y|| lt.eq ||x|| + ||y||$.

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

  + (absolute homogeneity): $forall y in Y ,  forall lambda in 𝕜 , ||lambda y||_Y = ||lambda y|| = lambda||y|| = lambda||y||_Y$.

  + (triangle inequality): $forall y_1 , y_2 in Y ,  norm(y_1 + y_2)_Y = norm(y_1 + y_2)<= ||y_1|| + ||y_2|| = ||y_1||_Y + ||y_2||_Y$.
]

#proposition[Topology of Sub Normed Space is Subspace Topology][
  Let $lr((X , bar.v.double dot.op bar.v.double))$ be a normed space and $Y$ be a subspace of $X$. Then the topology induced by the norm $bar.v.double dot.op bar.v.double_Y$ on $Y$ is the same as the subspace topology induced by the norm $bar.v.double dot.op bar.v.double$ on $X$.
]
#proof[
  The topology induced by the norm $bar.v.double dot.op bar.v.double_Y$ on $Y$ is the same as the subspace topology induced by the norm $bar.v.double dot.op bar.v.double$ on $X$.
]
=== Bounded Linear Operators <bounded-linear-operators>
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


Let $T:X -> Y$ be a bounded linear operator between normed spaces $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$. We use $B(X,Y)$ to denote the vector space of all bounded linear operators from $X$ to $Y$.


#definition[Operator Norm][
  Let $T:X -> Y$ be a bounded linear operator between normed spaces $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$. The #strong[operator norm] of $T$ is defined as
  $
    norm(T)_(B(X,Y)) = inf lr({ c>=0  : norm(T x)_Y <= c norm(x)_X " for all" x in X}).
  $
  It is a norm on the vector space $B(X,Y)$.
]

#proposition[Equivalent Definition of Operator Norm][
  Let $T:X -> Y$ be a bounded linear operator between normed spaces $(X,bar.v.double dot.op bar.v.double_X)$ and $(Y,bar.v.double dot.op bar.v.double_Y)$. Then the operator norm of $T$ can be equivalently defined as
  $
    norm(T) &= inf lr({ c>=0  : norm(T x)_Y <= c norm(x)_X " for all" x in X})\
    & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X <= 1})\
    & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X < 1})\
    & = sup lr({ norm(T x)_Y : x in X "and" norm(x)_X in {0, 1}})\
  $
  Furthermore, if we assume $dim X>=1$, then we have
  $
    norm(T) &= sup lr({ norm(T x)_Y : x in X "and" norm(x)_X = 1})\
    &= sup lr({ norm(T x)_Y/norm(x)_X : x in X  "and" x eq.not 0}).
  $
]

#pagebreak()

= Banach Spaces <banach-spaces>
== Basic Notions
#definition[Banach Space][
  A normed space is called a #strong[Banach space] if it is a complete metric space with respect to the metric induced by the norm.
]

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
    (integral_Omega abs(f)^p dif mu)^(min{1/p, 1})\, &quad 0 < p < infinity,
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
  $
    bar.v.double dot.op bar.v.double_p : L^p (Omega , cal(F) , mu) & arrow.r \[ 0 , oo \) ,\
    f + cal(N) & arrow.r.bar ||f||_p .
  $ For
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

For classical functional analysis, we mainly focus on the following two types of $L^p$ spaces.

#example[$L^p lr((E))$ spaces ][
  The first type is defined on some sub measure space $E$ of the Lebesgue measure space $lr((bb(R)^n , cal(M) , mu_(cal(M))))$, written as $L^p lr((E))$ spaces. In this case, the underlying set of $L^p lr((E))$ consists all measurable functions $f$ such that $||f||_p < oo$ where
  $
    bar.v.double dot.op bar.v.double_p : {f:E->CC mid(|) f upright("is measurable")} --> lr([0 , oo])
  $
  is a map defined as
  $
    norm(f)_p ≔ cases(
      (integral_E |f|^p dif x)^(1/p)\,& quad 1 <= p < infinity \
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
    lr(|A|)& upright(" if ") A upright(" is finite")\, ,
    , oo   & upright(" if ") A upright(" is infinite").
  )
  $
  $L^p lr((bb(N) , cal(P) lr((bb(N))) , mu_c))$ are often written as $ell^p$. In this case, the underlying set of $ell^p$ consists all real number sequences $x = lr((x_1 , x_2 , dots.h.c))$ such that $||x||_p < oo$ where $bar.v.double dot.op bar.v.double_p : bb(R)^(bb(N)) arrow.r lr([0 , oo])$ is defined as $ ||x||_p := cases(
  delim: "{",
  lr((thin sum_(i = 1)^oo lr(|x_i|)^p d x))^(1 / p)\,
    & quad 1 lt.eq p < oo,
  , #h(0em) limits(sup)_(i gt.eq 1) thin lr(|x_i|)\,
    & quad p = oo .,

) $
] <ellp-spaces>

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

== Adjoint Operator
#definition[Adjoint Operator][
  Let $X$ and $Y$ be Hilbert spaces and $T:X -> Y$ be a bounded linear operator. For any $y in Y$, the map
  $
    angle.l T (dot) \, y angle.r:X&-->CC\
    x &--> angle.l T x \, y angle.r
  $
  is a bounded linear functional on $X$. By the Riesz representation theorem, there exists a unique $T^* y in X$ such that
  $
    angle.l T x \, y angle.r = angle.l x \, T^* y angle.r, quad forall x in X.
  $
  This gives a map
  $
    T^* : Y &--> X\
    y &--> T^* y
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

#definition[Unital Banach Algebra][
  A Banach algebra $A$ is called a #strong[unital Banach algebra] if $A$ as an algebra has a multiplication unit element $1_A$ and $||1_A|| = 1$.
]

#definition[Commutative Banach Algebra][
  A Banach algebra $A$ is called a #strong[commutative Banach algebra] if $A$ as an algebra is commutative.
]

#definition[Sub Banach Algebra][
  Let $A$ be a Banach algebra. A #strong[sub Banach algebra] of $A$ is a subspace $B$ of $A$ that is also a Banach algebra with respect to the norm inherited from $A$.
]

#example[Bounded Linear Operators as Banach Algebra][
  Let $X$ be a Banach space. The set of all bounded linear operators on $X$ is a Banach algebra with respect to the operator norm.
]



#example[$L^1(G)$ for Locally Compact Hausdorff Topological Group $G$][
  Let $G$ be a locally compact Hausdorff topological group and $mu$ be a Haar measure on $G$. The set of all integrable complex-valued functions on $G$ is denoted by $L^1(G, mu)$. It is a commutative Banach algebra with respect to the convolution product
  $
    (f * h)(x) = integral_G f(y) h(y^(-1) x) dif mu(y).
  $
]

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
    norm(f) = sup_(x in X) |f(x)|.
  $
  and pointwise multiplication. The involution is defined as the complex conjugation $overline(#hide($z$))#h(0.2em):f |-> overline(f)$.

  $C_0(X)$ is unital if and only if $X$ is compact. In this case, the constant function $1$ is the unit element. And we have $C_0(X) = C(X)$.
]

#example[Bounded Linear Operators on a complex Hilbert Space][
  Let $H$ be a complex Hilbert space. The set of all bounded linear operators on $H$ is a $upright(C)^*$-algebra is denoted by $B(H)$.
  with respect to the operator norm and the adjoint operation.
]


#pagebreak()

= Appendix <appendix>
