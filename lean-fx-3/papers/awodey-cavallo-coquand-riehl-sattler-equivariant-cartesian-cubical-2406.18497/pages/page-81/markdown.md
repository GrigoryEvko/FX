proven in Proposition 5.3.8. Mirroring the forward direction of Proposition 3.5.5, this uses realignment for the universe of equivariantly fibrant types (fibration.realignment), which is deduced from realignment for the universe of the extensional type theory (axiom.realignment) and relative acyclicity of equivariant filling structures (fibration.realignment.realignFibStr); compare Proposition 2.3.5.

A.8. Tiny interval and universes. To interpret (univalent) universes, we follow Licata, Orton, Pitts, and Spitters [LOPS18] and work in an extension of extensional type theory by a modal type operator $\flat$. For the purposes of this summary, it suffices to understand the motivating semantics in cubical sets: if $A$ is a presheaf, then $\flat A$ is the constant presheaf of global sections of $A$. We refer to the documentation of the formalization for a precise description of this setting. We will sometimes refer to an element of $\flat A$ as a “global element of $A$”. In particular, we read $\flat \mathcal{V}$ as the type of external small presheaves. We leave the inclusion $\flat A \to A$ implicit in the following.

The use of this modality is to express internally that the interval is tiny, i.e. that exponentiation by the interval $(-)^\upharpoonright$ has a right adjoint root functor $\sqrt[-]{\upharpoonright}$ on (external) presheaves, as used in the proof of Lemma 4.2.7. Specifically, we require as an axiom a functorial operator $\sqrt[-]{\upharpoonright} : \flat \mathcal{V} \to \flat \mathcal{V}$ and an isomorphism

$$\flat(A^\upharpoonright \to B) \cong \flat(A \to \sqrt[\upharpoonright]{B})$$

natural in $A, B : \flat \mathcal{V}$, exhibiting $\sqrt[-]{\upharpoonright$ as right adjoint to exponentiation $(-)^\upharpoonright$ (axiom.tiny). The restriction to global types is necessary for this axiom to be consistent [LOPS18, Theorem 5.1]. By iterating, we also have a right adjoint $\sqrt[\upharpoonright]{}: \flat \mathcal{V} \to \flat \mathcal{V}$ to exponentiation by each cube $S = \upharpoonright^n$.

A.8.1. Dependent right adjoints (tiny.dependent). To construct the universe, it is useful to observe that each right adjoint $\sqrt[\upharpoonright]{}$ induces a dependent right adjoint (spelled out in [CHS19, Lemma 2.2]; see also Birkedal et al. [BCMMPS20] and [LOPS18, §5]). Note the appearance of similar structure in Lemma 2.1.16 of the external development, which is likewise used to construct universes.

Briefly, for each $\Gamma : \flat \mathcal{V}$ and global type family $B : \flat(\Gamma^S \to \mathcal{V})$ we have a family $\sqrt[\upharpoonright]{B}$ over $\Gamma$ and an isomorphism between dependent function types

$$\mathsf{shut}_S : \flat(\mathsf{Elem} \ \Gamma^S \ B) \cong \flat(\mathsf{Elem} \ \Gamma \ \sqrt[\upharpoonright]{B}) : \mathsf{open}_S$$

which is natural in $\Gamma$ and $B$ in an appropriate sense.

Remark A.8.1. Riley [Ril24] describes a type theory with a primitive dependent right adjoint of this kind and shows that this structure suffices to carry out the [LOPS18] universe construction without relying on a $\flat$ modality [Ril24, §5]. We use the same style of argument below; although our dependent right adjoint is not primitive, it remains a convenient abstraction, especially in the equivariant case where the universe construction is more involved than in [LOPS18].

A.8.2. Universe of non-equivariant fibrations. We now transpose the family $\mathsf{LocalFill}_S : \flat(\mathcal{V}^S \to \mathcal{V})$ from Definition A.5.1 to obtain $\sqrt[\upharpoonright]{\mathsf{LocalFill}_S}$ over $\mathcal{V}$ with the property that for any global family $A : \flat(\Gamma \to \mathcal{V})$ we have

$$\flat(\mathsf{Elem} \ \Gamma \ (\ \sqrt[\upharpoonright]{\mathsf{LocalFill}_S} \circ A)) \cong \flat(\mathsf{Elem} \ \Gamma^S \ (\mathsf{LocalFill}_S \circ A^S)) = \flat(\mathsf{Fill}_S \ A). \tag{A.8.2}$$

Definition A.8.3. Define $\mathcal{U}_S := \Sigma_{A:\mathcal{V}} \sqrt[\upharpoonright]{\mathsf{LocalFill}_S} \ A$.

From (A.8.2), we have an isomorphism for $\Gamma : \flat \mathcal{V}$ between global families $\Gamma \to \mathcal{U}_S$ and global $\mathcal{V}$-small families over $\Gamma$ paired with $S$-filling structures. Note that the type $\mathcal{U}_\upharpoonright$ is exactly the universe defined in [LOPS18].

Definition A.8.4. Leaving the first projection $\pi_1 : \mathcal{U}_S \to \mathcal{V}$ implicit, we transpose the projection $\pi_2 : \Pi_{A:\mathcal{U}_S} \sqrt[\upharpoonright]{\mathsf{LocalFill}_S} \ A$ to yield a map $\mathsf{open}_S \ \pi_2 : \Pi_{A:(\mathcal{U}_S)^S} \mathsf{LocalFill}_S \ A$ that associates a local filling structure to every $S$-cell in the universe.

81