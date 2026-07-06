A.8.3. Universe of equivariant fibrations. To further restrict to universes of equivariant fibrations, we introduce a another predicate on elements of $\mathcal{U}_S$.

Definition A.8.5 (universe.core.LocalEquivariance$\sqrt{}$). Fix $S = \mathsf{I}^n$ and let $A : (\mathcal{U}_S)^S$. Per Definition A.8.4, we have $\mathsf{open}_S \pi_2 A : \mathsf{LocalFill}_S A$. For each $\sigma$ in $\Sigma_n$, we also have $\mathsf{open}_S \pi_2 (A\sigma) : \mathsf{LocalFill}_S (A\sigma)$. We say $A$ is equivariant when for each $\sigma$ in $\Sigma_n$, we have

$$\mathsf{open}_S \pi_2 A (\sigma r_0) a_0 a (\sigma r_1) = \mathsf{open}_S \pi_2 (A\sigma) r_0 a_0 (a\sigma) r_1$$

for all $r_0 : S$, $a_0 : A (\sigma r_0)$, partial sections $a : (\Pi_{r:S} A r)^+$ compatible with $a_0$, and $r_1 : S$.

We write $\mathsf{Equivariant}_S A$ for the type of proofs that $A$ is equivariant.

Definition A.8.6 (universe.core.$\mathcal{U}$). Given $A : \mathcal{V}$, we define the type of equivariant fibration structures on $A$ by

$$\mathsf{Fib} A := \prod_{n:\mathbb{N}} \sum_{F: \sqrt[n]{\mathsf{LocalFill}_n} A} \prod_{\sigma:\Sigma_n} \sqrt[n]{\mathsf{Equivariant}_n} (A, F).$$

The universe of equivariant fibrations is then $\mathcal{U} := \sum_{A:\mathcal{V}} \mathsf{Fib} A$.

Proposition A.8.7 (universe.core). We have for each $\Gamma : \flat\mathcal{V}$ an isomorphism

$$\flat(\mathsf{Elem} \Gamma (\mathsf{Fib} \circ A)) \cong \flat(\mathsf{Fill} \Gamma A) \tag{A.8.8}$$

and therefore an isomorphism between global families $\Gamma \to \mathcal{U}$ and global $\mathcal{V}$-small equivariant fibrations over $\Gamma$.

The existence of such a predicate $\mathsf{Fib}$ corresponds to the local representability of equivariant fibrations (Lemma 5.3.3): for a family $A$ over $\Gamma$, the family $\mathsf{Fib} \circ A$ over $\Gamma$ corresponds to the representing morphism $\psi_\pi$ for the projection $\pi: \Gamma.A \to \Gamma$. In the external development, local representability of equivariant fibrations is derived from local representability of fibrations in cubical species (Lemma 4.4.3), which uses the tininess of the symmetric interval (Lemma 4.2.7) and thus, like the construction here, ultimately depends on the tininess of the cubes $\mathsf{I}^n$.

A.8.4. Fibrancy of the universe (universe.fibrant). As with the other type formers, we construct a fibrancy structure on the universe by generalizing the definition of Angiuli et al. [ABCHFL21, §2.12] from $\mathsf{I}$ to $\mathsf{I}^n$ and checking that this satisfies the equivariance equation. The construction relies on the Glue types mentioned in Section A.7. The corresponding argument in the external development is in 3.6, based on the same definition of Angiuli et al.; there it is conducted in cubical species and then transferred to cubical sets in Proposition 5.3.10.

When we have a larger universe $\mathcal{V}_1$ with $\mathcal{V} : \mathcal{V}_1$, we can repeat the definitions above to define a predicate $\mathsf{Fib}_1$ and universe of $\mathcal{V}_1$-small fibrations $\mathcal{U}_1 := \sum_{A:\mathcal{V}} \mathsf{Fib}_1 A$; the fibrancy of $\mathcal{V}$ then implies that $\mathcal{U}_1$ contains a code for $\mathcal{U}$. More generally, a hierarchy of universes $\mathcal{V}_n$ in the extensional type theory gives rise to a corresponding hierarchy of universes $\mathcal{U}_n$ in the homotopical interpretation.

A.8.5. Type formers (universe.type-former). Using the closure properties of the operation $\mathsf{Fill}$ established in Sections A.6 and A.7 and the bijection (A.8.8), we can build operations of types

$$\begin{array}{l} \Pi_{A:\mathcal{V}}\Pi_{B:A\to\mathcal{V}}\mathsf{Fib} A \to (\Pi_{a:A}\mathsf{Fib} (B a)) \to \mathsf{Fib} (\Pi_{A}B) \\ \Pi_{A:\mathcal{V}}\Pi_{B:A\to\mathcal{V}}\mathsf{Fib} A \to (\Pi_{a:A}\mathsf{Fib} (B a)) \to \mathsf{Fib} (\Sigma_{A}B) \\ \Pi_{A:\mathcal{V}}\Pi_{a_0:A}\Pi_{a_1:A}\mathsf{Fib} A \to \mathsf{Fib} (\mathsf{Path} A a_0 a_1). \end{array} \tag{A.8.9}$$

From these, we deduce that $\mathcal{U}$ is closed under $\Pi$-types, $\Sigma$-types, and $\mathsf{Path}$-types. We also have an alternative, isomorphic definition of the judgments of the homotopical interpretation: we can interpret types over $\Gamma$ as maps $\Gamma \to \mathcal{U}$ rather than as families over $\Gamma$ with equivariant filling structures. Because the type formers can then be defined pointwise by the operators shown in (A.8.9), the laws for computing substitutions such as mentioned in Remark A.6.6 become automatic;

82