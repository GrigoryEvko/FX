5:24

E. CAVALLO AND R. HARPER

Vol. 17:4

We see that tt and t are related by R: we have λ$^{\sharp}$...t ∈ R⟨tt, t⟩. Likewise, we have λ$^{\sharp}$...f ∈ R⟨ff, f⟩. We apply k at the two gel terms corresponding to these witnesses of the relation.

$$k(\text{Gel}_x(\text{bool}, A, R))(\text{gel}_x(\text{tt}, t, \lambda^{\sharp}...t))(\text{gel}_x(\text{ff}, f, \lambda^{\sharp}...f)) \in \text{Gel}_x(\text{bool}, A, R)$$

If we substitute 0 for x, each Gel and gel term reduces to its first term argument, leaving k(bool)(tt)(ff), which is Gk. Likewise, if we substitute 1, we get kAtf. When we bind x and project the relation witness from this term, we therefore wind up with the following.

$$\text{ungel}(x.k(\text{Gel}_x(\text{bool}, A, R))(\text{gel}_x(\text{tt}, t, \lambda^{\sharp}...t))(\text{gel}_x(\text{ff}, f, \lambda^{\sharp}...f))) \in R\langle Gk, kAtf \rangle$$

By definition of R, this is exactly our goal: a path from F(Gk)Atf to kAtf. By function extensionality, we get a term in Path$_{\mathbb{B}}$(F(Gk), k).

This argument follows the shape of a classical parametricity proof: we define a relation, apply a function to related arguments (here represented by gel terms), and conclude that the outputs are also related (via ungel). We can apply similar arguments to characterize other Church encodings. For example, we can show that the type (A:U) → A → (A → A) → A is isomorphic to the natural numbers; in that case, we would also use extent to construct a bridge in the function type.

Note that because the system is predicative, it does not appear possible to simply define inductive types using Church encodings. In the absence of a primitive boolean type in U, B can only eliminate into small types (that is, types in the universe U). When there is a primitive boolean type, however, B inherits its properties: we can define functions from B into large type by induction by factoring through the map B → bool.

The picture gets more complex when we consider Church encodings that are parameterized over “external” types, such as the following encoding of the coproduct.

$$A + B \stackrel{?}{\simeq} (C:\mathcal{U}) \to (A \to C) \to (B \to C) \to C$$

A classical proof would rely on the identity extension lemma [Rey83], which implies in particular that the relational interpretation of a closed type (A or B here) is the identity relation. This is not the case in BCM-style internal parametricity. In particular, the principle fails for the universe: the types Bridge$_{\mathcal{U}}$(A, B) and Path$_{\mathcal{U}}$(A, B) are not the same, as one is isomorphic to A × B → U and the other is isomorphic to A ≃ B.

If we focus our attention on small types, we will see that any concrete type A we can think of will satisfy Bridge$_{A}$(a, b) ≃ Path$_{A}$(a, b) for all a, b : A; however, there is no way to prove for an arbitrary A. We say that types that do satisfy this principle are bridge-discrete. We can show that the universe of bridge-discreteness types is well-behaved and closed under most type formers.

3.2. Bridge-discrete types. In any type, we have a canonical map from paths to bridges induced by coercion. A type is bridge-discrete when this map is an isomorphism.

Definition 3.2. For A type and M, N ∈ A, define loosen$_{A}$ ∈ Path$_{A}$(M, N) → Bridge$_{A}$(M, N) by loosen$_{A}$ := λp.coe$^{0→1}_{x.Bridge$_{A}$(p@0,p@x)}$(λ$^{\sharp}$...p@0).

Remark 3.3. For any M ∈ A, loosen$_{A}$ takes the reflexive path on M to the reflexive bridge on A: we have λ$^{\sharp}$y.coe$^{y→1}_{x.Bridge$_{A}$(M,M)}$(λ$^{\sharp}$...M) ∈ Path$_{\text{Bridge}_A(M,M)}$(loosen$_{A}$(λ$^{\sharp}$...M), λ$^{\sharp}$...M).