2.4. GLOBULAR EQUIVALENCES

Corollary 2.4.2.11. Let p be a map between complicial sets. Then p is a weak equivalence if and only if it is fully faithfull and essentially surjective.

Proof. If p is a weak equivalence, it is then fully faithfull and essentially surjective. Conversely, suppose p is fully faithfull and essentially surjective. The morphism π₀(X) → π₀(Y) is fully faithfull and essentially surjective, and then an equivalence of category. For (a, b) a pair of 0-cells, we have equalities:

$$\begin{array}{c} \pi_{1}(a, b, X) = \pi_{0}(X(a, b)) \\ \pi_{1}p \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \pi_{1}(pa, pb, Y) = \pi_{0}(Y(pa, pb)). \end{array}$$

The morphism π₁(a, b, p) is then an equivalence of categories. For (s, t) a pair of parallel arrows of dimension > 1, if we denote by a and b the 0-source and the 0-target of s and t, we have a diagram:

$$\begin{array}{c} \pi_{n}(s, t, X) = \pi_{n-1}(s, t, X(a, b)) \\ \pi_{n}p \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \pi_{n}(pa, pb, Y) = \pi_{n-1}(s, t, Y(pa, pb)). \end{array}$$

The morphism πₙ(a, b, p) is then an equivalence of categories. The morphism p is then a D-equivalence, and according to 2.4.2.9, a weak equivalence.

### 2.4.3 A criterion to be a weakly invertible transformation

The purpose of this section is to show the following proposition:

Proposition 2.4.3.1. Let i : mPsh(Δ) → mPsh(Δ) and j : mPsh(Δ) → mPsh(Δ) be two left Quillen functors and ψ : i → j a natural transformation. If ψ(Dₙ) : i(Dₙ) → j(Dₙ) is a weak equivalence for any n, then ψ(X) : i(X) → j(X) is a weak equivalence for any X.

For the remaining of this section, we fix two left Quillen functors i, j and a natural transformation ψ : i → j satisfying the previous hypothesis. We denote by Nᵢ and Nⱼ the right adjoints of i and j.

Lemma 2.4.3.2. Morphisms ψ(∂Dₙ) : i(∂Dₙ) → j(∂Dₙ) are weak equivalences.

Proof. We proceed by induction on n. The case n = 0 is trivial. Suppose then the result true at the stage n - 1. Remark then that ∂Dₙ is the colimit and the homotopy colimit of the span

$$\mathbf{D}_{n-1} \leftarrow \partial \mathbf{D}_{n-1} \rightarrow \mathbf{D}_{n-1}$$

As i and j are left Quillen functors, the induction hypothesis implies that ψ(∂Dₙ) : i(∂Dₙ) → j(∂Dₙ) is a weak equivalence.

Lemma 2.4.3.3. Morphisms ψ((Dₙ)ₜ) : i((Dₙ)ₜ) → j((Dₙ)ₜ) are weak equivalences.

Proof. There is a diagram:

$$\begin{array}{c} i_{!}\mathbf{D}_{n-1} \xrightarrow[\sim]{\psi(\mathbf{D}_{n})} j_{!}\mathbf{D}_{n-1} \\ i_{!}(i_{n}^{-}) \downarrow \sim \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ i_{!}(\mathbf{D}_{n})_{t} \xrightarrow[\psi((\mathbf{D}_{n})_{t})]{} j_{!}(\mathbf{D}_{n})_{t} \end{array}$$

By two out of three, this shows that ψ((Dₙ)ₜ) is a weak equivalence.

91