Relative Elegance and Cartesian Cubes with One Connection

35

Proposition 4.38 (essentially BD86, Theorem 1) Given an idempotent completion $i: \mathbf{C} \to \overline{\mathbf{C}}$, the induced substitution functor $i^*: \mathrm{PSh}(\overline{\mathbf{C}}) \to \mathrm{PSh}(\mathbf{C})$ is an equivalence of categories.

We can describe the idempotent completion of $\square_{\vee}$ concretely as a full subcategory of SLat.

Definition 4.39 Write $\overline{\square}_{\vee}$ for the full subcategory of SLat consisting of finite inhabited distributive lattices. This subcategory contains all of $\square_{\vee}$; we write $\blacksquare: \square_{\vee} \to \overline{\square}_{\vee}$ for the inclusion.

Remark 4.40 Any finite inhabited lattice is bounded, with $\top$ and $\bot$ obtained as the join and meet of all elements respectively. Moreover, a finite lattice is distributive if and only if it is a Heyting algebra, i.e., supports an implication operator $\Rightarrow$. Note however that we do not require the morphisms of $\overline{\square}_{\vee}$ to preserve $\wedge, \bot, \top$, or $\Rightarrow$, only binary (i.e., non-empty finite) joins.

We show that $\blacksquare: \square_{\vee} \to \overline{\square}_{\vee}$ is an idempotent completion using the following observations of Horn and Kimura.

Proposition 4.41 (HK71, Theorem 1.1) A morphism in SLat is epic if and only it is surjective.

Proposition 4.42 (HK71, Corollaries 2.9 and 5.4) Recall that an object in a category is injective if maps into it extend along monomorphisms, and dually projective if maps out of it lift along epimorphisms. A finite semilattice $A \in \mathrm{SLat}_{\mathrm{fin}}$ is

- injective if and only if $A$ is a distributive lattice;
- projective if and only if $1 \star A$ is a distributive lattice.

Corollary 4.43 $\overline{\square}_{\vee}$ is closed under retracts in SLat.

Proof A retract of an inhabited finite semilattice is clearly inhabited and finite, and the class of injective objects is closed under retracts in any category.

Corollary 4.44 $\overline{\square}_{\vee}$ is idempotent complete.

Proof Note that SLat is idempotent complete because it has limits. The claim follows from this using Corollary 4.43.

Lemma 4.45 Any $A \in \overline{\square}_{\vee}$ is a retract of $[1]^n$ for some $n \in \mathbb{N}$.

Proof For any $A \in \overline{\square}_{\vee}$, we have a poset map $p: 1 \star UA \to A$ sending $\bot$ to $\bot$ and $a \in UA$ to $a$. Per Proposition 4.7, this induces a surjective semilattice map $p^\dagger: [1]^{UA} \to A$. This is epic by Proposition 4.41. As $A$ is distributive, so too is $1 \star A$, so $A$ is projective. Thus, the identity on $A$ factors through $p^\dagger$, exhibiting $A$ as a retract of $[1]^{UA}$.

2025/10/16 00:43