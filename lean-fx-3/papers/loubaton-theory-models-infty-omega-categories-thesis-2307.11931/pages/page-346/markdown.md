CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

**Lemma 6.1.4.12.** *There is an equivalence*

$$\tau_0(\mathrm{LCart}((I \ominus [b, n]^\sharp)^\sharp) \sim \mathrm{Hom}([n], \mathrm{LCart}^c(I; b))$$

*natural in $I : (\infty, \omega)$-cat$_\mathrm{m}^{op}$, $b : \Theta^{op}$ and $[n] : \Delta^{op}$.*

*Proof.* This is a direct consequence of lemmas 6.1.4.10 and 6.1.4.11.

*Proof of theorem 6.1.4.2.* Lemma 6.1.4.12 provides an natural equivalence

$$\tau_0(\mathrm{LCart}((I \ominus [b, n]^\sharp)^\sharp) \sim \mathrm{Hom}([n], \mathrm{LCart}^c(I; b))$$

that preserves smallness.

## 6.2 Yoneda lemma and applications

### 6.2.1 Yoneda lemma

**6.2.1.1.** An $(\infty, \omega)$-category $C$ is *locally* **U-small** if for any pair of objects $x$ and $y$, $\mathrm{hom}_C(x, y)$ is **U-small**.

**Example 6.2.1.2.** For all **U-small** $(\infty, \omega)$-category $A$, the corollary 6.1.4.3 provides an equivalence

$$\mathrm{hom}_{\underline{\mathrm{Hom}}(A, \underline{\omega})}(f, g) \sim \mathrm{Map}(\int_A f, \int_A g)$$

As $\int_A f$ and $\int_A g$ are **U-small** left cartesian fibrations over a **U-small** basis, their codomains are **U-small** and $\mathrm{Map}(\int_A f, \int_A g)$ is then **U-small**. The $(\infty, \omega)$-category $\underline{\mathrm{Hom}}(A, \underline{\omega})$ is then locally **U-small**.

We can generalize this example as follow:

**Proposition 6.2.1.3.** *Let $A$ be a **U-small** $(\infty, \omega)$-category, and $C$ is a locally **U-small** $(\infty, \omega)$-category. The $(\infty, \omega)$-category $\underline{\mathrm{Hom}}(A, C)$ is locally **U-small**.*

*Proof.* We have to check that for any globular sum $b$, the morphism

$$\mathrm{Hom}(A \times [b, 1], C) \to \mathrm{Hom}(A \times (\{0\} \amalg \{1\}), C)$$

has **U-small** fibers. As $A$, seen as an $\infty$-presheaves on $\Theta$, is a **U-small** colimit of representables, we can reduce to the case where $A \in \Theta$. As $C$ is local with respect to Segal extensions, and as the cartesian product conserves them, we can reduce to the case where $A$ is of shape $[a, 1]$ for $a$ a globular sum. We now fix a morphism $f : [a, 1] \times (\{0\} \amalg \{1\}) \to C$.

336