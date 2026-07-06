2.2. THE COMPLICIAL MODEL

This defines a cosimplicial object in $\operatorname{End}(\mathrm{mPsh}(\Delta))$, which evaluated on $\emptyset$, provides a cosimplicial object in $\mathrm{mPsh}(\Delta)$:

$$
\begin{array}{l}
\Delta \rightarrow \mathrm{mPsh}(\Delta) \\
n \mapsto [n]_{\circ} := [0] \stackrel{co}{\star} (...([0] \stackrel{co}{\star} [0])).
\end{array}
$$

Eventually, we set $([n]_t)_{\circ} := \tau_{n-1}^i ([n]_{\circ})$. We then have defined a functor:

$$
(\_)_{\circ} : t\Delta \rightarrow \mathrm{mPsh}(\Delta).
$$

## 2.2.4 Street nerve

We recall that $(0, \omega)$-categories are defined in section 1.1.1. The Gray operations on $(0, \omega)$-categories - $_\otimes [1]$, $_\star 1$, $1 \stackrel{co}{\star} \_-$ are defined in section 1.2.3.

In [Str87], Street defines a cosimplicial object in $(0, \omega)$-cat, that associates to $n$, the $n^{th}$ *oriental* $O_n$. The original construction of this object is complicated, but Ara and Maltsiniotis have shown that it can be easily defined using Gray operations. Indeed, in [AM20, Corollaire 7.10], these authors construct an isomorphism

$$
O_n \cong \overbrace{1 \star \ldots \star 1}^{n+1}
$$

natural in $n$.

We can extend the functor $O_ : \Delta \rightarrow (0, \omega)$-cat to $t\Delta$ by defining

$$
(O_n)_t := \tau_{n-1}^i (O_n).
$$

By extention by colimit, this induces a functor

$$
\mathrm{R} : \mathrm{tPsh}(\Delta) \rightarrow (0, \omega)\text{-cat}.
$$

As explained in example 11 of [Ver06], R preserves the Gray tensor product, and so also the suspension, the wedge, the Gray cone and the Gray o-cone. Moreover, [Ver08a, Theorem 249] states that this functor sends complicial horn inclusions and complicial thinness extensions to isomorphisms. It obviously also sends saturation extensions to isomorphisms. This functor then sends every weak equivalences to isomorphisms, and then lifts to a colimit preserving functor $\mathrm{R} : \mathrm{mPsh}(\Delta) \rightarrow (0, \omega)$-cat and induces an adjoint pair:

$$
\mathrm{R} : \mathrm{mPsh}(\Delta) \xleftrightarrow{\perp} (0, \omega)\text{-cat} : \mathrm{N}
$$

We now recall two fundamental results of strictification:

85