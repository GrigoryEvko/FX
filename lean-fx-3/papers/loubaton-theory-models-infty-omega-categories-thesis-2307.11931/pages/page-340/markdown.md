CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**Corollary 6.1.3.33.** Let $n$ be an integer, $I$ a $\mathbf{V}$-small marked $(\infty, \omega)$-category, and $A$ an $(\infty, \omega)$-category. We denote by $I^{\sharp}$ the marked $(\infty, \omega)$-category obtained from $I$ by marking all cells, and $\iota : I \to I^{\sharp}$ the induced morphism. There is an equivalence, natural in $[n] : \Delta^{op}$ and $I : (\infty, \omega)\text{-cat}_{\mathrm{m}}^{op}$, between functors

$$f : I \otimes [n]^{\sharp} \to \underline{\mathrm{Hom}}(A, \underline{\omega})$$

and sequences

$$(\iota \times A^{\sharp})^{*} \int_{I^{\natural} \times A} f_{0} \to \dots \to (\iota \times A^{\sharp})^{*} \int_{I^{\natural} \times A} f_{n}$$

where for any $k \leq n$, $f_{k}$ is the functor $I^{\natural} \times A \to \underline{\omega}$ induced by $(I \otimes \{k\}) \times A^{\sharp} \to (I \otimes [n]^{\sharp}) \times A^{\sharp} \to \underline{\omega}^{\sharp}$.

Proof. This is a direct application of the last corollary and the equivalence $(I \otimes [n]^{\sharp}) \times A^{\sharp} \sim (I \times A^{\sharp}) \otimes [n]^{\sharp}$ given in proposition 5.1.2.3. $\square$

**Corollary 6.1.3.34.** Let $I$ be a $\mathbf{V}$-small marked $(\infty, \omega)$-category, $A$ an $(\infty, \omega)$-category, and $g$ an object of $\underline{\mathrm{Hom}}(A, \underline{\omega})$. We denote by $I^{\sharp}$ the marked $(\infty, \omega)$-category obtained from $I$ by marking all cells, and $\iota : I \to I^{\sharp}$ the induced morphism. There is an equivalence, natural in $I : (\infty, \omega)\text{-cat}_{\mathrm{m}}^{op}$, between functors

$$f : I \to \underline{\mathrm{Hom}}(A, \underline{\omega})_{g/}^{\sharp}$$

and arrows:

$$I \times \int_{A} g \to (\iota \times A^{\sharp})^{*} \int_{I^{\natural} \times A} \tilde{f}$$

where $\tilde{f} : I^{\natural} \times A \to \underline{\omega}$ is the functor corresponding to $I^{\natural} \to \underline{\mathrm{Hom}}(A, \underline{\omega})_{g/} \to \underline{\mathrm{Hom}}(A, \underline{\omega})$.

Proof. We once again have a cocartesian square

$$\begin{array}{c} I \otimes \{0\} \longrightarrow I \otimes [1]^{\sharp} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \longrightarrow 1 \stackrel{\infty}{\star} I \end{array}$$

As $\tau_{0}\mathrm{LCart}(\_)$ sends colimits to limits, this is a consequence of the last corollary and the equivalence $(I \otimes [1]^{\sharp}) \times A^{\sharp} \sim (I \times A^{\sharp}) \otimes [1]^{\sharp}$ given in proposition 5.1.2.3. $\square$

### 6.1.4 $(\infty, \omega)$-Functorial Grothendieck construction

**6.1.4.1.** For $I$ a marked $(\infty, \omega)$-category and $A$ an $(\infty, \omega)$-category, we define the $(\infty, \omega)$-category $\underline{\mathrm{Hom}}_{\ominus}(I, A)$, whose value on a globular sum $a$, is given by

$$\mathrm{Hom}(a, \underline{\mathrm{Hom}}_{\ominus}(I, A)) := \mathrm{Hom}(I \ominus a^{\sharp}, A^{\sharp})$$

The section is devoted to the proof of the following theorem:

330