As $P$ is defined as a subset of positive rational numbers, $\overleftarrow{\mathbb{R}}_+^\infty$ corresponds only to non-negative numbers, and as we do not ask $P$ to be inhabited, $\overleftarrow{\mathbb{R}}_+^\infty$ contains a point $+\infty$ (corresponding to $P = \emptyset$). The topology on $\overleftarrow{\mathbb{R}}_+^\infty$ is the topology of upper semi-continuity i.e. the basic open sublocales are the $[0, q]$ for $q$ a rational (or real) number.

2.5.4. On a topological space (or more generally in a Grothendieck topos) Dedekind real numbers correspond to continuous functions to $\mathbb{R}$, whereas points of $\overleftarrow{\mathbb{R}}_+^\infty$ correspond to non negative upper semi-continuous (possibly infinite) functions. This explains why Dedekind reals are called “continuous” real numbers, and why points of $\overleftarrow{\mathbb{R}}_+^\infty$ can be called upper semi-continuous real numbers.

## 2.6 $[X, \mathbb{R}]$ is locally positive

The goal of this subsection is to show that, when $X$ is a compact regular locale, the locale $[X, \mathbb{R}]$ is locally positive (and hence also $[X, \mathbb{C}] \simeq [X, \mathbb{R}]^2$).

If $U$ and $V$ are two open sublocales of $X$ we write $U \ll V$ if $U$ is way below $V$, i.e. if when $V \leqslant \bigvee_{i \in I} U_i$ then there exists a finite subset $J \subset I$ such that $U \leqslant \bigvee_{j \in J} U_j$. We write $U \prec V$ when $U$ is rather below $V$, i.e. when $V \vee \neg U = X$, where $\neg U$ is the biggest open sublocale disjoint from $U$. A locale $X$ is regular when $\forall V \in \mathcal{O}(X)$, $V = \bigvee_{U \prec V} U$. In a compact regular locale the two relations $\prec$ and $\ll$ are equivalent.

In [10] one can find a description of the geometric theory classified by $[X, \mathbb{R}]$. This description shows that the open sublocales of the form $(U, q, q') = \{f | U \ll f^*([q, q'])\}^5$ for $U$ an open sublocale of $X$ and $q, q'$ two rational numbers form a pre-basis of the topology of $[X, \mathbb{R}]$.

As:

$$U \ll f^*([q, q']) \Leftrightarrow (U \ll f^*([q, +\infty])) \wedge (U \ll f^*([-\infty, q'])),$$

$[X, \mathbb{R}]$ has a basis of open sublocales of the form

$$B = \left( \bigwedge_{i=1}^n (U_i, u_i, -) \right) \wedge \left( \bigwedge_{j=1}^m (V_j, v_j, +) \right), \quad (1)$$

where $U_i$ and $V_i$ are open sublocales of $X$, $u_i$ and $v_i$ are rational numbers, $(U_i, u_i, -)$ denotes $\{f | U \ll f^*([-\infty, u_i])\}$ and $(V_j, v_j, +)$ denotes $\{f | V_j \ll f^*([v_j, +\infty])\}$.

$^5$Of course, we do not mean the set of points $f$ of $[X, \mathbb{R}]$ satisfying this properties, but the open sublocale classifying such functions $f$.

14