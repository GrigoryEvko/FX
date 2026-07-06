1.2. GRAY OPERATIONS

**Proposition 1.2.1.18.** *An $\omega$-category $C$ that admits a basis is an $(0, \omega)$-category.*

*Proof.* Let $C$ be an $\omega$-category that admits a basis $E$. Suppose that there exists a non trivial $n$-cell $\alpha$ that admits an inverse $\beta$. We then have $[\alpha]_n + [\beta]_n = [\alpha \circ_{n-1} \beta]_n = 0$. As $\lambda C$ is free, we have $[\alpha]_n = 0$. This implies the equality $[e]_n = 0$ for any element $e \in E$ of dimension $n$ that appears in a decomposition of $\alpha$. This is obviously in contradiction with the fact that $\{[e]_{d(e)}\}_{e \in E}$ is a basis of the augmented directed complex $\lambda C$. $\square$

**Definition 1.2.1.19.** A basis $E$ of an $(0, \omega)$-category is :

(1) *Loop free* when $\{[e]_{d(e)}\}_{e \in E}$ is.
(2) *Atomic* when $[d_n^+ e]_n \wedge [d_n^- e]_n = 0$ for any $e \in E$ and any natural number $n$ strictly smaller than the dimension of $e$.

**Proposition 1.2.1.20.** *If a loop free basis $E$ is atomic then $\{[e]\}_{e \in E}$ is unitary.*

*Proof.* This is [Ste04, proposition 4.6]. $\square$

**Example 1.2.1.21.** For any integer $n$, $\mathbf{D}_n$ and $[n]$ admit a loop free and atomic basis. More generally, [AM20, proposition 4.13] states that any globular sum admits a loop free and atomic basis.

**1.2.1.22.** Proposition 1.23 of [AGOR23] states that if an $(0, \omega)$-category admits a loop-free and atomic basis, it is unique. We then define the category $(0, \omega)$-cat$_B$ as the full subcategory of $\omega$-cat composed of $(0, \omega)$-categories admitting an atomic and loop-free basis.

**Theorem 1.2.1.23** (Steiner). *Once restricted to $(0, \omega)$-cat$_B$ and ADC$_B$, the adjunction*

$$\lambda : \omega\text{-cat} \xrightarrow[\downarrow]{\perp} \text{ADC} : \nu$$

*becomes an adjoint equivalence, i.e. :*

$$\lambda|_{(0,\omega)\text{-cat}_B} \circ \nu|_{\text{ADC}_B} \cong id|_{\text{ADC}_B} \qquad id|_{(0,\omega)\text{-cat}_B} \cong \nu|_{\text{ADC}_B} \circ \lambda|_{(0,\omega)\text{-cat}_B}$$

*Proof.* See [Ste04, theorem 5.11]. $\square$

If $K$ is an augmented directed complex admitting a unitary and loop-free basis $B$, then the $(0, \omega)$-category $\nu K$ admits an atomic and loop-free basis given by the set $\langle B \rangle := \{\langle b \rangle, b \in B\}$. Conversely if an $(0, \omega)$-category $C$ admits an atomic and loop-free basis $E$, then the augmented directed complex $\lambda C$ admits a unitary and loop-free basis given by the family of sets $[E_n] := \{[e]_{d(e)}, e \in E_n\}$. The isomorphisms

$$\lambda \nu K \cong K \quad \text{and} \quad C \cong \nu \lambda C$$

45