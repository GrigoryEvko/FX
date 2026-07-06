Proof. We need to chase through the series of equivalences in the proof of Proposition 3.20 the image of $id: \underline{\mathrm{End}}(U) \to \underline{\mathrm{End}}(U)$ in $\mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^{\underline{\mathrm{End}}(U)})$.

The first step of this series of equivalences

$$\mathrm{Map}_{\mathbf{Mnd}_{\mathcal{C}}}(T, \underline{\mathrm{End}}(U)) \simeq \mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C})^{T}$$

sends the identity of $\underline{\mathrm{End}}(U)$ to the canonical action of $\underline{\mathrm{End}}(U)$ on $U$ (see Remark 3.18), essentially by definition of this action. The map to $\mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^{T})$ is then essentially just the isomorphism $\mathrm{Fun}(\mathcal{D}, \mathcal{C}^{\underline{\mathrm{End}}(U)}) \simeq \mathrm{Fun}(\mathcal{D}, \mathcal{C})^{\underline{\mathrm{End}}(U)}$, hence the result.

$\square$

A right adjoint functor $U: \mathcal{E} \to \mathcal{C}$ is said to be monadic if the unit of adjunction $\mathcal{E} \to \mathcal{C}^{\underline{\mathrm{End}}(U)}$ is an equivalence.

Theorem 4.7.3.5 of [16] is an $\infty$-categorical version of the Barr-Beck theorem. It states that a right adjoint functor $U: \mathcal{E} \to \mathcal{C}$ is monadic if and only it is conservative and for every simplicial object in $\mathcal{E}$ whose image by $U$ is split has a colimit which is preserved by $U$.

Given that forgetful functors of the form $\mathcal{C}^{T} \to \mathcal{C}$ themselves satisfy all these conditions, this shows that the adjunction of Proposition 3.20 is an idempotent, and identifies the category $\mathbf{Mnd}_{\mathcal{C}}$ of monads on a category $\mathcal{C}$ with the opposite of the category of monadic right adjoint functor $\mathcal{E} \to \mathcal{C}$, seen as a full subcategory of $(\mathbf{Cat}_{\infty})_{/\mathcal{C}}$. In particular, one deduces:

**Theorem 3.22.** For any $\infty$-category $\mathcal{C}$, the functor

$$\begin{array}{c c c} (\mathbf{Mnd}_{\mathcal{C}})^{op} & \to & (\mathbf{Cat}_{\infty})_{/\mathcal{C}} \\ T & \mapsto & \mathcal{C}^{T} \end{array}$$

is fully faithful and identifies $(\mathbf{Mnd}_{\mathcal{C}})^{op}$ with $\mathbf{RMd}_{\mathcal{C}}$ the reflective full subcategory of $(\mathbf{Cat}_{\infty})_{/\mathcal{C}}$ of monadic right adjoint functors.

This result was alluded to in Remark 4.7.3.8 of [16], but wasn't proven.

We finish with a consequence of Lurie's Barr-Beck theorem that will be useful in a few places:

**Proposition 3.23.** Given a (homotopy) pullback square of $\infty$-categories:

23