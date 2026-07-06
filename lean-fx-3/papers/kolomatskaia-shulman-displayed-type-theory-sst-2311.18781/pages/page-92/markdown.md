We similarly construct 3 by induction on H (the domain of α). The case when H is empty is trivial. Otherwise, we inductively have θ^α\{h\} : Θ^H' → Θ^H\{h\}, and to extend the codomain to Θ^H it suffices to give a term in context Γ^I | Θ^H' of type

$$\begin{array}{l} \mathrm{B}^{\mathrm{x}}[\theta^{\beta_{\mathrm{h}}}][\theta^{\alpha\backslash\{h\}}] \equiv \mathrm{B}^{\mathrm{x}}[\theta^{\beta_{\mathrm{h}}} \circ \theta^{\alpha\backslash\{h\}}] \\ \equiv \mathrm{B}^{\mathrm{x}}[\theta^{\beta_{\alpha\{h\}}}]. \end{array}$$

For this we can pick b^α{h}, using 5 inductively. Functoriality follows from the inductive assumption of functoriality in 5.

For 4, note that the slice category I/x is a sieve in I containing x. Then it suffices to define B^x in the case of I/x, since it can then be weakened to I using 6. In this case we have I/x = (I/x \ {x}) ⊕ ∂_x, so the last variable in Γ^I/x is A_x : Θ^∂_x → Type_ℓ. Thus, we can define Γ^I/x | y : Θ^∂_x ⊢_sm B^x to be Γ^I/x\{x}, A_x : Θ^∂_x → Type_ℓ | y : Θ^∂_x ⊢_sm A_x y.

For 5, it suffices to deal with the case when h is the last element in the ordering of H, since otherwise we can weaken from the sub-presheaf of all elements ≤ h to all of H, using 3 for the inclusion of this sub-presheaf. But in this case, the last variable in Θ^H is a_h : B^x[θ^h], so we can take b^h ≡ a_h. Functoriality follows immediately, as does stability under weakening from initial segments for all the data.

Finally, for 6 we induct on I. For a sieve in I ⊕ H there are two possibilities: it could be J or J ⊕ H for some sieve J in I, depending on whether it contains the new object *. (Of course, if it contains *, it must also contain all objects y such that H(y) ≠ ∅, which is to say that H must be left Kan extended from J.) In these two cases, we define

$$\begin{array}{l} \Gamma^{\mathrm{J}, \mathrm{I} \oplus \mathrm{H}} \equiv (\Gamma^{\mathrm{J}, \mathrm{I}}, A_{\star} : \Theta^{\mathrm{H}} \rightarrow \text{Type}_{\ell}) \\ \Gamma^{\mathrm{J} \oplus \mathrm{H}, \mathrm{I} \oplus \mathrm{H}} \equiv \Gamma^{\mathrm{J}, \mathrm{I}} \quad \text{weakened to } \Gamma^{\mathrm{J} \oplus \mathrm{H}}. \end{array}$$

This completes the construction of the classifying context. Note in particular that a consequence of 3 is that re-ordering the elements of a presheaf H modifies Θ^H only up to isomorphism.

4.5.5.3 The classifying context is classifying. To show this, we first construct a 'universal' diagram over Γ^I. Specifically, in any category with families, we construct simultaneously:

1. For each ordered direct category I, a Reedy type B of shape I and level ℓ over Γ^I in the sense of [KL21, Definition 3.22].
2. For each ordered presheaf H on I, the object Θ^H is the canonical H-weighted limit of B constructed by the 'master lemma' of [KL21, Lemma 3.11]. (In particular, therefore, Θ^∂_x is the matching object of B at x.)
3. The maps θ^α are the functorial action of these limits.
4. The type Γ^I | Θ^χ_ν ⊢_sm B^x is the object B(x) with its fibration to the matching object M_x B = Θ^∂_x.
5. The elements b^x are the projections from the weighted limit Θ^H.

92