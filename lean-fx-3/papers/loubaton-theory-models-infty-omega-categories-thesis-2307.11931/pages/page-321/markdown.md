6.1. UNIVALENCE

induces by the one of theorem 5.1.3.24. When nothing is specified, the morphism $C^{\flat} \to \mathbf{F}h_0^{[C,1]}$ will always corresponds to this square.

**6.1.2.3.** Let $C$ be an $(\infty, \omega)$-category. We define the simplicial marked $(\infty, \omega)$-category $C_{/}$ and the simplicial arrow of marked $(\infty, \omega)$-categories $\mathbf{F}h_{/}^{C}$ whose value on an integer $n$ is given by the following pullback

$$
\begin{array}{ccc}
(C_{/})_{n} & \longrightarrow & (C^{\sharp})^{[n+1]^{\sharp}} \\
(\mathbf{F}h_{/})_{n} \downarrow & & \downarrow \\
(\mathrm{N}_{(\omega,1)} C)_{n}^{\flat} \times C^{\sharp} & \longrightarrow & (C^{\sharp})^{[n]^{\sharp}} \times (C^{\sharp})^{\{n+1\}}
\end{array}
$$

and where the functoriality in $n$ is induced by the universal property of pullback. Unfolding the definition, on all integer $n$, the canonical morphism $(C_{/})_{n} \to C^{\sharp}$ corresponds to the morphism

$$
\coprod_{x_0, \dots, x_n: C_0} \hom_C^{\flat}(x_0, \dots, x_n) \times \mathbf{F}h_{x_n}^{C}
$$

and is then a left cartesian fibration according to theorem 5.2.3.3.

**6.1.2.4.** Let $E$ be an object of $(\infty, \omega, 1)$-cat$_{/\mathrm{N}_{(\omega,1)} C}$ corresponding to an arrow $X \to \mathrm{N}_{(\omega,1)} C$. The *Grothendieck construction* of $E$, is the object of $(\infty, \omega)$-cat$_{\mathrm{m}/C^{\sharp}}$ defined by the formula

$$
\int_C E := \operatorname{colim}_n (X^{\flat} \times_{(\mathrm{N}_{(\omega,1)} C)^{\flat}} \mathbf{F}h_{/})_{n}.
$$

As the Grothendieck construction is by definition a colimit of left cartesian fibrations, the theorem 5.2.3.3 implies that it is also a left cartesian fibration. The Grothendieck construction then defines a functor

$$
\int_C : (\infty, \omega, 1)\text{-cat}_{/\mathrm{N}_{(\omega,1)} C} \to \mathrm{LCart}(C^{\sharp}).
$$

Unfolding the definition, if $E$ is a left fibration, $\int_C E$ is the colimit of a simplicial diagram whose value on $n$ is:

$$
\coprod_{x_0, \dots, x_n: C_0} X(x_0) \times \hom_C^{\flat}(x_0, \dots, x_n) \times \mathbf{F}h_{x_n}^{C}
$$

**Example 6.1.2.5.** Let $E$ be an object of $\mathrm{LFib}(\mathrm{N}_{(\omega,1)}[a,1])$ corresponding to a morphism $X \to \mathrm{N}_{(\omega,1)}([a,1])$. According to proposition 6.1.1.12, this object corresponds to a morphism $X(0) \times a \to X(1)$. The arrow $\int_{[a,1]} E$ corresponds to the colimit of the following diagram:

$$
E(0)^{\flat} \times \mathbf{F}h_0^{[a,1]} \longleftarrow E(0)^{\flat} \times a^{\flat} \longrightarrow E(1)^{\flat}
$$

311