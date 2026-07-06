2.4. GLOBULAR EQUIVALENCES

Corollary 2.4.2.11. Let p be a map between complicial sets. Then p is a weak equivalence if and only if it is fully faithfull and essentially surjective.

Proof. If p is a weak equivalence, it is then fully faithfull and essentially surjective. Conversely, suppose p is fully faithfull and essentially surjective. The morphism π₀(X) → π₀(Y) is fully faithfull and essentially surjective, and then an equivalence of category. For (a, b) a pair of 0-cells, we have equalities:

$$\pi_1(a, b, X) \xlongequal{\quad} \pi_0(X(a, b))$$

$$\pi_1 p \downarrow \qquad \qquad \qquad \qquad \downarrow \pi_0 p(a, b)$$

$$\pi_1(pa, pb, Y) \xlongequal{\quad} \pi_0(Y(pa, pb)).$$

The morphism π₁(a, b, p) is then an equivalence of categories. For (s, t) a pair of parallel arrows of dimension > 1, if we denote by a and b the 0-source and the 0-target of s and t, we have a diagram:

$$\pi_n(s, t, X) \xlongequal{\quad} \pi_{n-1}(s, t, X(a, b))$$

$$\pi_n p \downarrow \qquad \qquad \qquad \qquad \downarrow \pi_{n-1}(s, t, p(a, b))$$

$$\pi_n(pa, pb, Y) \xlongequal{\quad} \pi_{n-1}(s, t, Y(pa, pb)).$$

The morphism πₙ(a, b, p) is then an equivalence of categories. The morphism p is then a D-equivalence, and according to 2.4.2.9, a weak equivalence. □

### 2.4.3 A criterion to be a weakly invertible transformation

The purpose of this section is to show the following proposition:

Proposition 2.4.3.1. Let i : mPsh(Δ) → mPsh(Δ) and j : mPsh(Δ) → mPsh(Δ) be two left Quillen functors and ψ : i → j a natural transformation. If ψ(Dₙ) : i(Dₙ) → j(Dₙ) is a weak equivalence for any n, then ψ(X) : i(X) → j(X) is a weak equivalence for any X.

For the remaining of this section, we fix two left Quillen functors i, j and a natural transformation ψ : i → j satisfying the previous hypothesis. We denote by Nᵢ and Nⱼ the right adjoints of i and j.

Lemma 2.4.3.2. Morphisms ψ(∂Dₙ) : i(∂Dₙ) → j(∂Dₙ) are weak equivalences.

Proof. We proceed by induction on n. The case n = 0 is trivial. Suppose then the result true at the stage n − 1. Remark then that ∂Dₙ is the colimit and the homotopy colimit of the span

$$\mathbf{D}_{n-1} \leftarrow \partial \mathbf{D}_{n-1} \rightarrow \mathbf{D}_{n-1}$$

101