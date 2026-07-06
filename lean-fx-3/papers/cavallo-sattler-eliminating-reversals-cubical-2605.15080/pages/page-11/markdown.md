E. Cavallo and C. Sattler

11

former can be shown to be univalent. Following Cohen et al. [12], Angiuli et al. implement univalence using so-called glue types [2, §2.11]; Angiuli, Favonia, and Harper's V-types are an alternative solution [3, §5.6].

First, we define equivalences [39, Definition 4.4.1] using path types. Over A : Ty, define isContr(A) := Σa₀:A. Πa₁:A. a₀ ∼^A a₁ : Ty. Over ([A B : Ty], f : A → B), define isEquiv(f) := Πb : B.isContr(Σa : A. f(a) ∼ b) : Ty. Finally, over (A B : Ty), define the type of equivalences (A ≃ B) := Σf : A → B. isEquiv(f). The Glue type former takes a type A, a cofibration P, and a partial type T and equivalence e : T ≃ A defined when P holds. Its output is a total type that reduces to T when P holds.

Glue : (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃ A) ⇒ Ty
_ : (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃ A, P) ⇒ Glue(A, P, T, e) ≡ T : Ty

We now abbreviate Φ_Glue = (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃ A). The Glue type has an introduction form glue and an elimination form unglue. Each reduces when P holds, and we have computation and uniqueness equations.

glue : ([Φ_Glue], a : A, t : [P] → T, [P → e.l(t) ≡ a : A]) ⇒ Glue(A, P, T, e)
_ : ([Φ_Glue], a : A, t : [P] → T, [P → e.l(t) ≡ a : A], P) ⇒ glue(a, t) ≡ t : T
unglue : ([Φ_Glue], g : Glue(A, P, T, e)) ⇒ A
_ : ([Φ_Glue], g : Glue(A, P, T, e), P) ⇒ unglue(g) ≡ e.l(g) : A
_ : ([Φ_Glue], a : A, t : [P] → T, [P → e.l(t) ≡ a : A]) ⇒ unglue(glue(a, t)) ≡ a : A
_ : ([Φ_Glue], g : Glue(A, P, T, e)) ⇒ g ≡ glue(unglue(g), g) : Glue(A, P, T, e)

The eliminator unglue can be shown to be an equivalence Glue(A, P, T, e) ≃ A that reduces to e when P holds. Univalence is derived using an instance where P is (i ≈ 0 ∪ i ≈ 1) for some i : ∥; see Cohen et al. [12, §7.2] or Angiuli et al. [2, §2.12].

### 3.3.5 Universe

We include one universe: a type U whose elements are regarded as types via a decoding function El.

U : Ty El : (A : U) ⇒ Ty

We often leave the coercion El from U to types implicit. For a universe to be useful, it should be closed under type formers such as Σ and Π; for it to be univalent, it should be closed under Glue. We refer to Uemura [37, Example 4.6.11] for an example formulation of these closure conditions, but we omit cases for type formers in the universe in our proofs: handling them always amounts to repeating the construction used for the type formers outside of the universe.

### 3.3.6 Higher inductive types

We include suspension types [39, §6.5] as a representative example of an HIT. See [13, 9] for general descriptions of HITs in cubical type theory. We specify the formation and introduction forms as follows:

Susp : (A : Ty) ⇒ Ty north, south : [A : Ty] ⇒ Susp(A)
merid : ([A : Ty], a : A) ⇒ north ∼^Susp(A) south