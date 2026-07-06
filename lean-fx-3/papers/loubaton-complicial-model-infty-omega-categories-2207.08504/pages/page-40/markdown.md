CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Proof. We denote by Υ the full subcategory of Δ/D whose objects are morphisms f : [n] → D such that Sp[n] → [n] → D factors through the Θ-set C ∪ x.

Given f : [n] → D in Υ, we denote by Λ^Υ[n] the subobject of [n] composed of all i ∈ Δ/[n] such that fi factors through C ∪ x. We can proceed as in lemma 1.2.2.23 to show that the canonical morphism Λ^Υ[n] → [n] is in W̅₁.

Now, remark that the category Υ inherits from Δ/D a structure of Reedy elegant category. The two functors

$$\begin{array}{c c c c c c} \Upsilon & \to & \mathrm{Psh}(\Delta) & \Upsilon & \to & \mathrm{Psh}(\Delta) \\ [n] \to D & \mapsto & \Lambda^\Upsilon[n] & [n] \to D & \mapsto & [n] \end{array}$$

are Reedy cofibrant (definition 1.1.3.1). As the colimit of the first one is C ∪ x and the colimit of the second one is D, this concludes the proof.

proof of theorem 1.2.2.1. If n = 0, this is straightforward, and if n = 2, it follows from proposition 1.2.2.25.

It then remains to prove the case n = 1. Let S be the set of generators of C of dimension 2. A repeated application of proposition 1.2.2.25 and the stability by pushout and transfinite composition of W̅₂ implies that the two vertical morphisms of the following square are in W̅₂:

$$\begin{array}{c} \tau_1 C \cup x \cup_{y \in S} y \longrightarrow \tau_1 D \cup_{y \in S} y \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ C \cup x \longrightarrow D \end{array}$$

Moreover, the proposition 1.2.2.26 implies that the canonical morphism

$$\tau_1 C \cup x \to \tau_1 D$$

is in W̅₂, and so is the top horizontal morphism of the previous square. By stability of left cancellation of W̅₂, this concludes the proof.

### 1.2.3 Gray operations on augmented directed complexes

We follow Steiner ([Ste04]) and Ara-Maltsiniotis ([AM20]) for the definitions and first properties of Gray operations on augmented directed complexes.

Definition 1.2.3.1. Let (K, K*, e) and (L, L*, f) be two augmented directed complexes. We define the Gray tensor product of (K, K*, e) and (L, L*, f) as the augmented directed complex

$$(K, K^*, e) \otimes (L, L^*, f) := (K \otimes L, (K \otimes L)^*, e \otimes f)$$

where

- K ⊗ L is the chain complex whose value on n is:

$$(K \otimes L)_n := \oplus_{k+l=n} K_k \otimes L_l$$

and the differential is the unique graded group morphism fulfilling:

$$\partial(x \otimes y) := \partial x \otimes y + (-1)^{|x|} x \otimes \partial y$$

where we set the convention ∂x := 0 if |x| = 0.

40