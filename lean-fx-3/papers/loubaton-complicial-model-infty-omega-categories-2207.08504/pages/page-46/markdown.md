CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

- The augmentations e are the unique morphism fulfilling

$$e(\{0\}) = e(\{1\}) = e(\{2\}) = 1.$$

**Proposition 1.2.3.14.** Let A be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexes [A, 1] ∨ [1] and [1] ∨ [A, 1] have no non-trivial automorphisms.

Proof. The proof is similar to the one of proposition 1.2.3.12 and we leave it to the reader.

**Definition 1.2.3.15.** There are two canonical morphisms

$$\nabla : \Sigma K \to \Sigma K \vee [1] \qquad \nabla : \Sigma K \to [1] \vee \Sigma K$$

that are the unique ones fulfilling

$$\nabla(\{0\}) := \{0\} \quad \nabla(\{1\}) := \{2\} \quad \nabla([x, 1]) := \left\{ \begin{array}{ll} [x, 1] + e_1 & \text{if } |x| = 0 \\ [x, 1] & \text{if } |x| > 0 \end{array} \right.$$

When we write ΣK → ΣK ∨ [1] and ΣK → [1] ∨ ΣK and nothing more is specified, it will always mean that we considered the morphisms ∇.

**Proposition 1.2.3.16.** Let K be an augmented directed complex. There is a natural transformation between the colimit of the following diagram

$$[1] \vee [K, 1] \longleftarrow [K \otimes \{0\}, 1] \longrightarrow [K \otimes [1], 1] \longleftarrow [K \otimes \{1\}, 1] \longrightarrow [K, 1] \vee [1]$$

and [K, 1] ⊗ [1].

Proof. The cone is induced by morphisms

$$\begin{array}{c} [1] \vee [K, 1] \to [K, 1] \otimes [1] \\ (\text{resp. } [K, 1] \vee [1] \to [K, 1] \otimes [1]) \end{array}$$

sending an element x in the basis of [1] to {0} ⊗ x (resp. {1} ⊗ x), an element y in the basis of [K, 1] to y ⊗ {1} (resp. y ⊗ {0}), and by the morphism

$$f : [K \otimes [1], 1] \to [K, 1] \otimes [1]$$

defined by the formula

$$f([x \otimes y, 1]) := [x, 1] \otimes y$$

for x in the basis of K and y in the basis of [1]. We leave it to the reader to check the compatibilities of this three morphisms.

### 1.2.4 Gray operations on (0, ω)-categories

We follow Ara-Maltsiniotis [AM20] for the definitions and first properties of Gray operations on (0, ω)-categories. Originally, these authors work with ω-categories, and not with (0, ω)-categories. However, this modification does not affect proof, and we then allow ourselves to use their results in our framework.

46