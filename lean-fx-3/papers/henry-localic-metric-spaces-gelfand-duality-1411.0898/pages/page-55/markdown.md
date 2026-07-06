where $D_q$ denotes the open disc of radius $q$ in $\mathbb{C}$, and $[X \ll f^*D_q]$ denotes the basic open which classifies the $f$ such that $X \ll f^*D_q$.

# **Proof :**

$[X, \mathbb{C}]$ is indeed locally positive by 2.6.5. For the rest, we recall that Hyland gave in [10] a description of the theory classified by $[X, Y]$ in terms of the basic propositions $[U \ll f^*V]$ for $U \in \mathcal{O}(X)$ and $V \in \mathcal{O}(Y)$. From this description, we immediately obtain that:

$$\bigvee_{q' < q} B_{q'} 0 = B_q 0;$$ $$\bigvee_n B_n 0 = [X, \mathbb{C}].$$

Also, as 0 is the point corresponding to the function constant equal to 0, one has indeed $0 \in B_q 0$.

Hence the $B_q 0$ indeed define a function $\|\cdot\| : [X, \mathbb{C}] \to \overleftarrow{\mathbb{R}_+^\infty}$ such that $\|0\| = 0$, and such that $\bigvee_n B_n 0 = [X, \mathbb{C}]$.

All the algebraic axioms (including the triangular inequality) are checked on generalized point exactly as one does for classical points in the usual (constructive) case.

A basic open $[U \ll f^*V]$ (for $U$ positive) contains 0 if $U \ll \bigvee_{0 \in V} X$, but this implies that there exists a finite set $F$ included in $\{0 \in V\}$ such that $U \leqslant \bigvee_{f \in F} X$. A finite set is inhabited or empty, hence either $F$ is empty and $U = \emptyset$ or $F$ is inhabited and $0 \in V$. In the first case $[U \ll f^*V] = [X, \mathbb{C}]$ contains all the $B_q 0$. In the second case one has a $q$ such that $D_q \ll V$ and hence $0 \in B_q 0 = [X \ll f^*(D_q)] \leqslant [U \ll f^*(V)]$ which proves that the $B_q 0$ form a basis of neighborhood of 0, and hence $[X, \mathbb{C}]$ is a Banach locale.

□

4.2.3. We now want to construct the spectrum of a $C^*$ locale. We will start by defining the locale $\text{Fn } \mathcal{H}$ of linear forms of norm smaller than 1 on a Banach locale $\mathcal{H}$ (the spectrum being the space of characters, it will be a sublocale of this locale). It generalizes the locale $\text{Fn } E$ constructed in [16] and [6].

**Proposition :** *Let $\mathcal{H}$ be a Banach locale. There exists a sublocale $\text{Fn } \mathcal{H} \subset [\mathcal{H}, \mathbb{C}]_1$ which classifies the linear forms of norm smaller or equal to one on $\mathcal{H}$. If $\mathcal{C}$ is a unital commutative $C^*$ locale, then there exists a sublocale $\text{Spec } \mathcal{C} \subset [\mathcal{C}, \mathbb{C}]_1$ which classifies characters of $\mathcal{C}$.*

# **Proof :**

One can for example define the locale $\text{Fn } \mathcal{H}$ as the intersection of the equalizer of the following two diagrams:

$$[\mathcal{H}, \mathbb{C}]_1 \Rightarrow [D_1 \times \mathcal{H}, \mathbb{C}]_1$$

where $D_1$ denotes the open unit ball in $\mathbb{C}$ and the two maps are the maps defined on generalized elements by: $f \mapsto ((\lambda, x) \mapsto \lambda f(x))$ and $f \mapsto ((\lambda, x) \mapsto f(\lambda x))$, and where the distance on $D_1 \times \mathcal{H}$ is the max distance.

55