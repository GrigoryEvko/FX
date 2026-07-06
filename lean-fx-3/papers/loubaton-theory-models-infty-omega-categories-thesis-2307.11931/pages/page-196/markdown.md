CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

**4.2.1.6.** A $(\infty, \omega)$-category is a W-local $\infty$-presheaf $C \in \mathrm{Psh}^{\infty}(\Theta)$. We then define

$$(\infty, \omega)\text{-cat} := \mathrm{Psh}^{\infty}(\Theta)_{\mathrm{W}}.$$

Proposition 4.2.1.5 implies that $(\infty, \omega)$-cat identifies itself with the full sub $(\infty, 1)$-category of $\mathrm{Psh}^{\infty}(\Delta[\Theta])$ of M-local objects:

$$(\infty, \omega)\text{-cat} \sim \mathrm{Psh}^{\infty}(\Delta[\Theta])_{\mathrm{M}}.$$

We recall that the sets of morphisms W and M are respectively defined in paragraphs 1.1.2.14 and 1.1.2.15.

**4.2.1.7.** We denote by $\pi_0 : \mathrm{Psh}^{\infty}(\Theta) \to \mathrm{Psh}(\Theta)$ the functor sending an $\infty$-presheaf $X$ onto the presheaf

$$\pi_0 X : a \mapsto \pi_0(X_a)$$

This functor admits a fully faithful right adjoint: $\mathrm{N} : \mathrm{Psh}(\Theta) \to \mathrm{Psh}^{\infty}(\Theta)$. As $\pi_0$ preserves W, it induces an adjoint pair:

$$\pi_0 : (\infty, \omega)\text{-cat} \underset{\longleftarrow}{\overset{\perp}{\longrightarrow}} (0, \omega)\text{-cat} : \mathrm{N}$$

where the right adjoint N is fully faithful. Every $(0, \omega)$-category can then be seen as an $(\infty, \omega)$-category and we will call *strict* the $(\infty, \omega)$-categories lying in the image of this functor.

The inclusion $\Delta \to \Theta$ induces by extention by colimit a functor $\mathrm{Psh}^{\infty}(\Delta) \to \mathrm{Psh}^{\infty}(\Theta)$. Passing to the localization, this induces a fully faithful inclusion $(\infty, 1)$-cat $\to (\infty, \omega)$-cat.

The inclusion $\{[0]\} \to \Theta$ induces by extention by colimit a functor $\infty\text{-grd} \to \mathrm{Psh}^{\infty}(\Theta)$. Passing to the localization, this induces a fully faithful inclusion $\infty\text{-grd} \to (\infty, \omega)$-cat. The $(\infty, \omega)$-categories lying in the image of this functors will be also called $\infty$-*groupoids*.

**4.2.1.8.** A $n$-cell of an $(\infty, \omega)$-category is a morphism $\mathbf{D}_n \to C$. If $C$ is an $(\infty, \omega)$-category, we denote by $C_n$ the value of $C$ on $\mathbf{D}_n$.

**Proposition 4.2.1.9.** *Let $C, D$ be two $(\infty, \omega)$-categories, and $f : C \to D$ any map. The morphism $f$ is an equivalence if and only if for any $n$, the induced morphism $f_n : C_n \to D_n$ is an equivalence.*

*Proof.* This is a necessary condition. For the converse, let $f$ be a morphism fulfilling this condition. To show that $f$ is an equivalence, we have to show that for any globular sum $a$, $f_a : C_a \to D_a$ is an equivalence. This is true as

$$f_a : C_a \to D_a \sim \lim_{n \in \mathrm{Sp}_a} f_n : C_n \to D_n.$$

$\square$

186