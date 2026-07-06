CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Lemma 1.2.5.7. Let C be a (0,ω)-category such that there exists a diagram F : I → Θ⁺ with ι(C) being the colimit of F. Let a be an element of Θ. The canonical morphism ι(C) ⊗ a → ι(C ⊗ a) is an isomorphism.

Proof. The lemma 1.2.5.5 implies that the natural transformation F(i) ⊗ b → F(i) is cartesian. As a consequence, for any i, the square

$$\begin{array}{c} F(i) \otimes a \longrightarrow (\operatorname{colim}_I F) \otimes a \cong \iota(C) \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ F(i) \longrightarrow \operatorname{colim}_I F \cong \iota(C) \end{array}$$

is cartesian.

Now, to show the desired result, we have to demonstrate that the Θ-set ι(C) ⊗ a already has a structure of (∞,ω)-category, i.e. that it is W-local. It is sufficient to show that for all f : X → Y in W, any square

$$\begin{array}{c} X \longrightarrow \iota(C) \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \\ Y \longrightarrow \iota(C) \end{array}$$

admits a unique lift. Indeed, as ι(C) is an (0,ω)-category, it is W-local, and this will imply that ι(C) ⊗ a also is. Suppose then given such a square. As every codomain of morphism of W is representable, there exists a (not necessarily unique) element i of I, such that the bottom morphism factors as Y → F(i) → ι(C). The previous square then factors as

$$\begin{array}{c} X \longrightarrow F(i) \otimes a \longrightarrow \iota(C) \otimes a \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \\ Y \longrightarrow F(i) \longrightarrow \iota(C) \end{array}$$

where the right square is a pullback. The middle vertical morphism is W-local because it's domain and codomain are, and this concludes the proof.

Lemma 1.2.5.8. Given (a)ᵢ≤ₙ and b elements of Θ, we have

$$\iota((a_0 \times \dots \times a_n \otimes b) \cong (a_0 \times \dots \times a_n) \otimes b$$

Proof. This is a direct consequence of lemmas 1.2.5.6 and 1.2.5.7

Lemma 1.2.5.9. Let A, B, C be three presheaves on Θ. We have a canonical morphism

$$A \otimes (B \otimes C) \to (A \times B) \otimes C$$

Proof. It is sufficient to demonstrate the result when A, B and D are representable. In this case the lemma 1.2.5.8 implies that (A × B) ⊗ C is in the image of ι. By adjunction, the desired comparaison morphism is induced by

$$\iota(A \otimes (B \otimes C)) \cong \iota(A) \otimes (\iota(B) \otimes \iota(C))) \cong (\iota(A) \otimes \iota(B)) \otimes \iota(X) \to (\iota(A) \times \iota(B)) \otimes \iota(C)$$

54