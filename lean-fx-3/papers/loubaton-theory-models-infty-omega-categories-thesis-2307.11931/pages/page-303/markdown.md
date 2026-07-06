5.2. CARTESIAN FIBRATIONS

is fully faithful. By right cancellation and using the fact that fully faithful functors are stable by limits, it is sufficient to show that for any $k < n$,

$$\mathbf{R}\pi_{[b_k,1]}^*: \tau_0\mathrm{LCart}^c(I) \to \tau_0\mathrm{LCart}^c(I \times [b_k,1]^b)$$

is fully faithful. Moreover, for any such $k$, we have a commutative square

$$\begin{array}{ccc} \tau_0\mathrm{LCart}^c(I) & \xrightarrow{\mathbf{R}\pi_{[b_k,1]}^*} & \tau_0\mathrm{LCart}^c(I \times [b_k,1]^b) \\ \downarrow & & \downarrow \\ \tau_0(\infty,\omega)\text{-}\mathrm{cat}_{\mathrm{m}/I} & \xrightarrow{\pi_{[b_k,1]}^*} & \tau_0(\infty,\omega)\text{-}\mathrm{cat}_{\mathrm{m}/I \times [b_k,1]^b} \end{array}$$

whose vertical morphisms are fully faithful by construction. The results the follows from lemma 5.2.5.4 by right cancellation.

The second assertion is demonstrated similarly.

5.2.5.6. For an $(\infty,\omega)$-category $A$ and a globular sum $a$, we define $\mathrm{LCart}(A^\sharp; a)$ as the full sub $(\infty,1)$-category of $\mathrm{LCart}^c(A^\sharp \times a^b)$ whose objects are of shape $E \times id_a^b$ for $E$ an object of $\mathrm{LCart}(A^\sharp)$. The proposition 5.2.5.5 implies that the canonical morphism

$$\tau_0\mathrm{LCart}(A^\sharp) \to \tau_0\mathrm{LCart}(A^\sharp; a)$$

is an equivalence of $\infty$-groupoid. We define $\underline{\mathrm{LCart}}(A^\sharp)$ as the $\mathbf{W}$-small $(\infty,\omega)$-category whose value on $[a,n]$ is given by:

$$\underline{\mathrm{LCart}}(A^\sharp)([a,n]) := \mathrm{Hom}([n], \mathrm{LCart}(A^\sharp; a)).$$

For a marked $(\infty,\omega)$-category $I$ and a globular sum $a$, we define similarly $\mathrm{LCart}^c(I; a)$ as the full sub $(\infty,1)$-category of $\mathrm{LCart}^c(I \times a^b)$ whose objects are of shape $E \times id_a^b$ for $E$ an object of $\mathrm{LCart}^c(I)$. The proposition 5.2.5.5 implies that the canonical morphism

$$\tau_0\mathrm{LCart}^c(I) \to \tau_0\mathrm{LCart}^c(I; a)$$

is an equivalence of $\infty$-groupoid. We define $\underline{\mathrm{LCart}}^c(I)$ as the $\mathbf{W}$-small $(\infty,\omega)$-category whose value on $[a,n]$ is given by:

$$\underline{\mathrm{LCart}}^c(I)([a,n]) := \mathrm{Hom}([n], \mathrm{LCart}^c(I; a)).$$

These two definitions are compatible as we have an equivalence between $\underline{\mathrm{LCart}}^c(A^\sharp)$ and $\underline{\mathrm{LCart}}(A^\sharp)$.

293