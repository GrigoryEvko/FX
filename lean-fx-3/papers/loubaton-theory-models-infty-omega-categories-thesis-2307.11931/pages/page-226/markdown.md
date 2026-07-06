CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

Proof. It is obvious that $\{0\} \to [1]$ is a left 1-Gray deformation retract and $\{1\} \to [1]$ is a right 1-Gray deformation retract. A repeated application of 4.3.2.11 proves the assertion. □

Proposition 4.3.2.13. Let $a$ be a globular sum of dimension $(n+1)$. We denote by $s_n(a)$ and $t_n(a)$ the globular sum defined in paragraph 1.1.2.12.

If $n$ is even, $s_n(a) \to a$ is a left $n$-Gray deformation retract and $t_n(a) \to a$ is a right $n$-Gray deformation retract, and if $n$ is odd, $s_n(a) \to a$ is a right $n$-Gray deformation retract and $t_n(a) \to a$ is a left $n$-Gray deformation retract.

Proof. This is a direct consequence of proposition 4.3.2.12 and 4.3.2.5 as $s_n(a) \to a$ is a composition of pushouts of $i_n^- : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$. The other assertion is proved similarly. □

### 4.3.3 Gray operations and strict objects

Recall that we have an adjunction

$$\pi_0 : (\infty, \omega)\text{-cat} \xrightarrow{\perp} (0, \omega)\text{-cat} : \mathrm{N}$$

An $(\infty, \omega)$-category lying in the image of the nerve functor $\mathrm{N}$ is called strict. As explained in example 11 of [Ver06], $\pi_0$ preserves Gray tensor product, and so also the suspension, the Gray cone, and the Gray o-cone.

The strict categories play an important role as they allow us to make explicit calculations. In particular, it will be very useful to know which cocontinuous functors preserve them.

Proposition 4.3.3.1. An $(\infty, \omega)$-category $C$ is strict if and only if $C_0$ is a set and for any pair of objects $x, y$, $\hom_C(x, y)$ is strict.

Proof. By definition, an $(\infty, \omega)$-category is strict if and only if, for any globular sum $[\mathbf{b}, n]$, $\operatorname{Hom}([\mathbf{b}, n], C)$ is a set. However, as $C$ is W-local, we have an equivalence between $\operatorname{Hom}([\mathbf{b}, n], C)$ and

$$\coprod_{x_0, x_1, \dots, x_n \in C_0} \operatorname{Hom}(b_1, \hom_C(x_0, x_1)) \times \dots \times \operatorname{Hom}(b_n, \hom_C(x_{n-1}, x_n))$$

As all the objects of the previous expression are set by hypothesis, and as the inclusion of set into $\infty$-groupoid is stable under coproduct and product, $\operatorname{Hom}([b, n], C)$ is a set. □

Proposition 4.3.3.2. If $C$ is a strict $(\infty, \omega)$-category, so is $[C, 1]$.

Proof. There is an obvious equivalence $[\mathrm{N}_{\_,} 1] \sim \mathrm{N}_{[\_,} 1]$ which directly implies the result. □

216