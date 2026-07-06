52

E. Cavallo and C. Sattler

Finally, we exploit the fact that $i^*$ preserves the operations of saturation by monomorphisms to transfer the induction principle on the Reedy monic presheaves of PSh(R) given by Theorem 5.27 to PSh(C).

Theorem 5.47 Let $\mathbf{R}$ be elegant relative to $i: \mathbf{C} \to \mathbf{R}$. Let $\mathcal{P} \subseteq \mathrm{PSh}(\mathbf{C})$ be a class of objects such that

- for any $r \in \mathbf{R}$ and $H \leq \operatorname{Aut}_{\mathbf{R}}(r)$, we have $N_i r / N_i H \in \mathcal{P}$;
- $\mathcal{P}$ is saturated by monomorphisms.

Then $\mathcal{P}$ contains every presheaf in PSh(C).

Proof As a left and right adjoint, $i^*$ preserves colimits and monomorphisms. The class $(i^*)^{-1}\mathcal{P}$ of $X \in \mathrm{PSh}(\mathbf{R})$ such that $i^*X \in \mathcal{P}$ is thus saturated by monomorphisms. By our first assumption and the fact that $i^*$ preserves colimits, we have $\mathscr{L}r / H \in (i^*)^{-1}\mathcal{P}$ for every $r \in \mathbf{R}$ and $H \leq \operatorname{Aut}_{\mathbf{R}}(r)$. By Theorem 5.27 and Lemma 5.42, we thus have $i_*X \in (i^*)^{-1}\mathcal{P}$ for all $X \in \mathrm{PSh}(\mathbf{C})$. Hence $X \cong i^*i_*X \in \mathcal{P}$ for all $X \in \mathrm{PSh}(\mathbf{C})$. ■

## 6 Reedy structures on categories of finite algebras

### 6.1 Finite algebras

Per Section 4, $\square_\nu$ and its idempotent completion can be regarded as full subcategories of the category $\mathbf{SLat}_{\mathrm{fin}}$ of finite semilattices. Any category of finite algebras of a Lawvere theory carries a natural Reedy structure: the degree of an object is its cardinality, and the lowering and raising maps are given by the (surjective, mono) factorization system. Here we observe that this Reedy structure is pre-elegant and characterize its elegant core in the case where free finitely-generated algebras are finite. As a corollary, the embedding $\square_\nu \to \mathbf{SLat}_{\mathrm{fin}}$ and its restriction $\square_\nu \to \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ to inhabited algebras are relatively elegant.

For this section, we fix a Lawvere theory $\mathbf{T}$. We recall a few basic properties of its category of algebras.

Proposition 6.1 (ARV10, Corollary 3.5) A morphism $f$ in $\operatorname{Alg}(\mathbf{T})$ is regular epic if and only $Uf$ is surjective. ■

Proposition 6.2 (ARV10, Corollary 3.7) Any morphism in $\operatorname{Alg}(\mathbf{T})$ factors as a regular epi followed by a mono. ■

Write $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}} \to$ and $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{\mathrm{inh}}$ for the full subcategories of $\operatorname{Alg}(\mathbf{T})$ consisting of algebras with finite and finite inhabited underlying sets respectively. When we write $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{(\mathrm{inh})}$ below, the relevant statement or proof applies to both of these.

Corollary 6.3 The (surjective, mono) factorization system restricts to a Reedy structure on $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{(\mathrm{inh})}$ with degree map given by cardinality. ■

2025/10/16 00:43