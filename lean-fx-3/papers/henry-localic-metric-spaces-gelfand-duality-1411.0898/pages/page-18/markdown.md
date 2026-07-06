2.6.5. Combining all these results we obtain:

**Theorem :** If $X$ is a compact regular locale, then a basic sublocale $B$ of $[X, \mathbb{R}]$, is admissible if and only it is positive. In particular, $[X, \mathbb{R}]$ is locally positive and the admissible basic sublocales form a basis of positive open sublocales.

# **Proof :**

It suffices to apply Lemma 2.3.4 with $b_i$ the basic open sublocales and $w_i$ the propositions “$b_i$ is admissible”. Proposition 2.6.3 shows that $w_i$ implies $b_i > \emptyset$ and 2.6.4 is exactly the second condition. $\square$

2.6.6. We also obtain the following

**Proposition :** Let $X$ be a compact regular locale, $X$ is completely regular if and only if $[X, \mathbb{R}]$ is weakly spatial.

# **Proof :**

If $X$ is completely regular, then 2.6.3 shows that each admissible has a point. But by 2.6.5 they form a basis of positive open, hence this proves that points of $[X, \mathbb{R}]$ are dense. Conversely, if $[X, \mathbb{R}]$ is weakly spatial and $U, V$ are two open sublocales of $X$ such that $U \prec V$, then there exists $W$ such that $U \prec W \prec V$ and the basic open:

$$
B = (U, 0, -) \wedge (\neg W, 1, +)
$$

is admissible because $\neg U \vee \neg\neg W \geqslant \neg U \vee W = X$. Hence it is positive and hence it has a point. But a point of $B$ is a function from $X$ to $\mathbb{R}$ such that $f$ is negative on $U$ and greater than one on $\neg W$. As $\neg W \vee V = X$ the function $f$ shows that $U$ is “completely below $V$”, and this proves that $X$ is completely regular. $\square$

## 3 Constructive theory of metric locales

### 3.1 Pre-metric locale

As our major concern is the study of localic Banach spaces, we will only consider metrics on a locale which are defined by a distance function. However, it should be noted that the point 9 of the series of propositions given in 3.1.4 shows that one can specify a distance by giving the diameter $\delta(U)$ of each open sublocale $U$, and the classical theory$^7$ which can be found for example in the chapter XI of [17] suggests that a definition by diameters should also be possible.

7Which has not been done constructively yet as far the author knows.

18