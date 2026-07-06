8:14

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

lowChurchBool : (∀ (X : Type) → X → X → X) ≈ Bool
lowChurchBool = isoToEquiv (iso chToBool boolToCh (λ { true → refl ; false → refl })
    λ k → funExt λ A → funExt λ t → funExt λ f → param-prf k A t f)
where
    boolToCh : Bool → (∀ (X : Type) → X → X → X)
    boolToCh true X xt xf = xt
    boolToCh false X xt xf = xf

    chToBool : (∀ (X : Type) → X → X → X) → Bool
    chToBool k = k Bool true false

module CH-inverse-cond (k : ∀ (X : Type) → X → X → X) (A : Type) (t f : A) where
    R : Bool → A → Type
    R = λ b a → (boolToCh b A t f) ≡ a
    k-Gelx : (@tick x : Bl) → Gel Bool A R x → Gel Bool A R x → Gel Bool A R x
    k-Gelx x = k (Gel Bool A R x)
    k-Gelx-gel-gel : (@tick x : Bl) → Gel Bool A R x
    k-Gelx-gel-gel x = k-Gelx x (gel true t (refl) x) ((gel false f (refl) x))
    asBdg : BridgeP (λ x → Gel Bool A R x) (k Bool true false) (k A t f)
    asBdg x = k-Gelx-gel-gel x
    param-prf : R (k Bool true false) (k A t f)
    param-prf = ungel [R = R] λ x → asBdg x
open CH-inverse-cond

Fig. 2. A low-level proof of a free theorem.

to the available low-level parametricity primitives. This is unsurprising since, after all, those primitives have been added precisely for that purpose.

Such a low-level proof of a free theorem in Agda --bridges appears in Fig. 2. The lowChurchBool theorem asserts that Bool admits a Church encoding, i.e., that this equivalence holds: \((X:\text{Type})\to X\to X\to X\simeq\) Bool. It is a faithful reproduction of the proof appearing in [Cavallo and Harper 2021]. We provide a high-level description of the proof and refer to the latter for more detailed explanations. To build an equivalence, it is sufficient to provide two maps and two inverse conditions. This is the content of the isoToEquiv lemma. The two candidate inverses are defined in a where block below and are called boolToCh and chToBool. The first inverse condition can simply be proven by induction. Using function extensionality, the second inverse condition asks that for every \(k:(X:\text{Type})\to X\to X\to X\), this equality holds boolToCh(chToBool \(k\)) \(A t f\equiv k A t f\). Note that the universal quantification on \(k\) appears inside the system (with an Agda \(\Pi\)-type). The logic of Agda --cubical alone would not be sufficient to warrant this result (see Section 1). Therefore the internal parametricity of Agda --bridges must be used. All calls to parametricity primitives are isolated in a separate module called CH-inverse-cond. The last lemma of this module param-prf implies the second inverse condition.

We observe that such low-level proofs suffer from several defects. First, the user of Agda --bridges wanting to reproduce this style of proofs must have a good familiarity with the parametricity primitives provided by Agda --bridges, including their inner workings. But these primitives use advanced or non-standard type-theoretic notions like freshness and capturing. This makes for hard and non user-friendly proofs. Second these proofs lack compositionality. Indeed, we have proved in Fig. 2 a free theorem param-prf about polymorphic programs of type \( T = (X : \text{Type}) \to X \to X \to X \). We expect other free theorems to hold at this type and it is unclear at first glance if param-prf could be reused to achieve that. In fact we even would like to be able to reuse the

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.