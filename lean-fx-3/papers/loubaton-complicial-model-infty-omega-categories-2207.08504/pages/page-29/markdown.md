1.2. GRAY OPERATIONS

Definition 1.2.1.19. A basis $E$ of an $(0, \omega)$-category is :

(1) Loop free when $\{[e]_{d(e)}\}_{e \in E}$ is.
(2) Atomic when $[d_n^+ e]_n \wedge [d_n^- e]_n = 0$ for any $e \in E$ and any natural number $n$ strictly smaller than the dimension of $e$.

Proposition 1.2.1.20. If a loop free basis $E$ is atomic then $\{[e]\}_{e \in E}$ is unitary.

Proof. This is [Ste04, proposition 4.6].

Example 1.2.1.21. For any integer $n$, $\mathbf{D}_n$ and $[n]$ admit a loop free and atomic basis. More generally, [AM20, proposition 4.13] states that any globular sum admits a loop free and atomic basis.

Definition 1.2.1.22. Proposition 1.23 of [AGOR23] states that if an $(0, \omega)$-category admits a loop-free and atomic basis, it is unique. We then define the category $(0, \omega)$-cat$_\mathrm{B}$ as the full subcategory of $\omega$-cat composed of $(0, \omega)$-categories admitting an atomic and loop-free basis.

Theorem 1.2.1.23 (Steiner). Once restricted to $(0, \omega)$-cat$_\mathrm{B}$ and ADC$_\mathrm{B}$, the adjunction

$$\lambda : \omega\text{-cat} \xrightarrow{\perp} \mathrm{ADC} : \nu$$

becomes an adjoint equivalence, i.e. :

$$\lambda_{|(0, \omega)\text{-cat}_\mathrm{B}} \circ \nu_{|\mathrm{ADC}_\mathrm{B}} \cong id_{|\mathrm{ADC}_\mathrm{B}} \qquad id_{|(0, \omega)\text{-cat}_\mathrm{B}} \cong \nu_{|\mathrm{ADC}_\mathrm{B}} \circ \lambda_{|(0, \omega)\text{-cat}_\mathrm{B}}$$

Proof. See [Ste04, theorem 5.11].

Remark 1.2.1.24. If $K$ is an augmented directed complex admitting a unitary and loop-free basis $B$, then the $(0, \omega)$-category $\nu K$ admits an atomic and loop-free basis given by the set $\langle B \rangle := \{\langle b \rangle, b \in B\}$. Conversely if an $(0, \omega)$-category $C$ admits an atomic and loop-free basis $E$, then the augmented directed complex $\lambda C$ admits a unitary and loop-free basis given by the family of sets $[E_n] := \{[e]_{d(e)}, e \in E_n\}$. The isomorphisms

$$\lambda \nu K \cong K \quad \text{and} \quad C \cong \nu \lambda C$$

induce isomorphisms:

$$[\langle B \rangle] \cong B \quad \text{and} \quad E \cong \langle [E] \rangle.$$

Definition 1.2.1.25. Let $f : M \to N$ be a morphism between two augmented directed complexes admitting unitary and loop-free bases $B_M$ and $B_N$. The morphism $f$ is quasi-rigid if for any $n$, and any $b \in (B_M)_n$,

$$f_n(b) \neq 0 \Rightarrow f_n(b) \in B_N \text{ and } \nu(f)\langle b \rangle = \langle f_n(b) \rangle.$$

Theorem 1.2.1.26. Suppose given a commutative square in ADC$_\mathrm{B}$

$$\begin{array}{c} K \xrightarrow{k^0} M_1 \\ k^0 \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ M_0 \xrightarrow{l^0} M \end{array}$$

and such that all morphisms are quasi-rigid. Let $B_K$, $B_{M_0}$, $B_{M_1}$, $B_M$ be the bases of $K$, $M_0$, $M_1$, $M$.

29