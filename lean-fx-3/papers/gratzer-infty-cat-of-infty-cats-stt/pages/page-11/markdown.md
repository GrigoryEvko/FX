The ∞-category of ∞-categories in simplicial type theory

Once more using univalence, we are reduced to b-annotated equation between maps of families over C (i.e. C → Σ_{A,B:U} B^A):

$$\lambda c. \pi_0 : \prod_{c:C} (\sum_{f:\pi_F^{-1}(c)} \alpha^{-1}(f)) \to \pi_F^{-1}(c)$$

$$\lambda c. (-, c) : \prod_{c:C} h(0, c) \to h(1, c)$$

Since ⟨b | I → Cat^C⟩ embeds into ⟨b | C → Σ_{A,B:U} B^A⟩ by directed univalence, Proposition 2.8 ensures this fiber over (E, F, π_F) is a proposition. The same analysis shows that it is inhabited iff π_F ∘ α and π_E are cocartesian and α is a map of cocartesian families. □

Corollary 6.5. The map U : (C → Cat) → Cat/C is an embedding.

In fact, in light of our identification of the fibers of U we may also characterize when a functor lifts along it. This is, in essence, the universal property of Cocart(C) mentioned earlier:

Corollary 6.6 (Straightening–unstraightening). If D :_b U is a category, a map f :_b D → Cat/C lifts along U to Cat^C if and only if

- (1) for each d :_b D, the functor f(d) is a cocartesian family.
- (2) for each d :_b I → D, the functor induced by f ∘ d : I → Cat/C is a cocartesian functor between the cocartesian families.

## 7 Examples

We have thus far focused on the construction of Cat and verifying its essential properties and so we close by discussing some of the new examples and category theory unlocked by Cat. For reasons of space, we content ourselves with only sketching several examples.

### 7.1 Subcategories of Cat

We begin by noting that since every covariant family is cocartesian, there is a unique map from the base of the universal covariant family S to the base of the universal cocartesian family Cat. This is the inclusion of groupoids into categories.

Lemma 7.1. The map i : S → Cat is fully faithful and possesses both left and right adjoints: |−| + i + (−)^∞.

PROOF SKETCH. The second half of this statements follows from Lemma 2.13. In particular, we use this lemma to extend the point-wise assignments of X :_b Cat ↦ ⟨b | X⟩ : S and X :_b Cat ↦ ○_grpd X : S to functors Cat → S. The fact that i is fully faithful is then immediate from Axiom 5: if X is a groupoid then the unit X → ⟨b | i(X)⟩ is an equivalence. It is a standard argument that a unit being invertible implies the left adjoint is fully faithful. □

Many other interesting categories exist as full subcategories of Cat. For instance, we may isolate univalent 1-categories as the full subcategory of Cat [10, §7] given by the following predicate:

$$\text{is1Cat} : (\flat \mid \text{Cat}) \to \text{HProp}$$

$$\text{is1Cat}(C) = \prod_{a,b:\flat,C} \text{isSet}(\hom_C(a, b))$$

Similar definitions immediately yield (n, 1)-categories for all n. Notably, by restricting to n = −1 we obtain the category of partial orders and, restricting further to linear partial orders, the simplex category Δ ⇔ Cat. In fact, the same argument as was used to S ⇔ Cat allows us to prove the following:

Lemma 7.2. The inclusion of Cat_n ⇔ Cat is a right adjoint.

PROOF SKETCH. One adapts Lemma 7.1 to use the modality nullifying the maps Λ_1^2 → Λ^2, B → 1, and ∂Δ^(n+2) → Δ^(n+2). □

Towards algebraic K-theory. For a small example of how these ingredients might be combined to build a useful and important construction in higher category theory, we turn our attention to monoidal categories. Let us write [n] for the element of Δ realizing the linear order {0 ≤ ··· ≤ n}. Using Corollary 5.5, we define ρ_n^1 : hom([1], [n]) which sends 0 ≤ 1 to {i ≤ i + 1} ⊆ [n].

Definition 7.3. A monoidal category C^⊗ : Cat^⟨op|Δ⟩ is a functor where (ρ_n^1, …, ρ_n^n) : C^⊗([n]) → C^⊗([1]) × ··· × C^⊗([1]) is an equivalence for all n.

Replacing Cat by S in the above gives the definition of an E_1-monoid: a homotopy-coherent monoid [10, §7].

Definition 7.4. The category of monoidal categories MCat is the full subcategory of ⟨op | Δ⟩ → Cat spanned by monoidal categories.

We readily adapt this definition to (1) the category of E_1-monoids Mon as a subcategory of S^⟨op|Δ⟩ and to (2) the category of monoidal 1-categories MCat_1 as a subcategory of Cat_1^⟨op|Δ⟩.

As both (−)^∞ : Cat → S and the inclusion Cat_1 → Cat are right adjoints, they preserve finite products and therefore post-composing by these maps induces functors MCat → Mon and MCat_1 → MCat. We note next that—viewing Mon as a subcategory of S^⟨op|Δ⟩—we may take the colimit of M : Mon to obtain a space lim M. In fact, this space is canonically pointed: the initial object in Mon is the functor const 1 and lim const 1 = 1. Finally, regarding the loop-space functor as a map Ω : S_* → S_* we define k to be the following chain of functors:

$$k : \text{MCat}_1 \to \text{MCat} \to \text{Mon} \to S_* \to S_*$$

We may now define the simplest form of algebraic K-theory:

Definition 7.5 (Quillen). The ith K-group of a monoidal 1-category C^⊗ is the ith homotopy group K_i(C^⊗) = π_i(k(C^⊗)).

Notably, with Cat to hand all of these definitions are quite conceptual and automatically functorial. We emphasize that this is only a first step towards realizing K-theory. We leave it to future work to show e.g., that modules over a ring are a monoidal category.

### 7.2 The structure homomorphism principle

To give a different class of examples involving Cat, we turn to the structure homomorphism principle. This is the directed enhancement of HoTT's structure identity principle. This principle states that by taking ordinary type-theoretic definitions of objects in a certain category but using Cat or S instead of U, we obtain the correct synthetic category with the expected homomorphisms.

For a simplest example of this phenomena:

Lemma 7.6. The type Σ_{A:Cat} A is the lax slice 1 ∮ Cat i.e. its objects are pointed categories (C, c) and when (C, c), (D, d) :_b Σ_{A:Cat} A morphisms hom((C, c), (D, d)) consist of functions f : C → D together with a morphism hom(f(c), d).

PROOF. As Σ_{A:Cat} A is the total space of the cocartesian family Cat → U, it is a category. The characterization of objects is immediate from Proposition 2.8. For morphisms, we use Corollary 5.5