28:4

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

- formulate an algorithm based on poset maps for solving problems with the “Dedekind” and “De Morgan” contortions, thereby making these computationally hard problems more tractable (§4),
- formulate an algorithm based on constraint satisfaction programming for solving problems using Kan filling (§5), and
- provide a practical Haskell implementation of our algorithms and exhibit its effectiveness on a selection of theorems and lemmas taken from libraries for Cubical Agda (§6).

This paper extends [DCM24], which only considered Dedekind contortions, by generalising our framework to work with any kind contortion theory that is considered in the literature (cartesian [AFH18, ABC+21, ACC+26], disjunctive [CS25], Dedekind [Awo26] and De Morgan [CCHM18, VMA19]). We give additional complexity results for these newly arisen problems and extend our efficient representation of Dedekind contortions to De Morgan contortions. Furthermore, we spell out the proof that finding Kan filling is undecidable, which was only sketched in [DCM24]. Making precise the reduction from the word problem for groups to Kan filling requires a considerable amount of care. Lastly, we have rectified an error in the definition of our language given in [DCM24]; see Remark 2.14 below.

## 2. FILLING CUBES IN CUBICAL TYPE THEORIES

Cubical type theories are complex systems. Besides path types, one has the usual type formers of type theory—dependent functions, products, inductive types, etc.—not to mention univalence and HITs. To make automation tractable, we restrict attention to a fragment including only basic operations on cubical cells in a single type.³

Rather than use path types to encode cubical cells, as one does in a fully-featured cubical type theory, we take cells as a primitive notion. A cell is a term parameterised by one or more dimension variables, which we think of as ranging in the interval [0, 1]; intuitively, a cell of type A in n variables is a function [0, 1]ⁿ → A. Contexts are lists of cells each of which can have a specified boundary. For example, an entry p(i) : [i = 0 ↦ a | i = 1 ↦ b] specifies a 1-dimensional cell p varying in i ∈ [0, 1] such that p(0) = a and p(1) = b, i.e., a path from a to b. In general, an entry in a context has the form q(Ψ) : [φ] where Ψ is a list of variables and φ is a list of values at faces (i = 0 and i = 1 in the example above). A cell hypothesis is thus a judgemental analogue of a hypothesis of extension type à la Riehl and Shulman [RS17, §2.2].

The problems we aim to solve are boundary problems: given a context of cells Γ, a list of dimension variables Ψ, and a boundary φ, can we use the cells in Γ to build a cell varying in Ψ with boundary φ? We write such a problem as “Γ | Ψ ⊢ ? : [φ]”. For example, if we want to prove that paths are invertible, then we could pose the boundary problem

$$a : [ ], b : [ ], p(i) : [ i = 0 \mapsto a \mid i = 1 \mapsto b ] \mid j \vdash ? : [ j = 0 \mapsto b \mid j = 1 \mapsto a ] \quad (2.1)$$

Here Γ has three cells: points a and b, and a path p. Our goal is a path from b to a, written as a function of j ∈ [0, 1] with fixed endpoints. We allow leaving the boundary of cells partially or completely unspecified, so that we can formulate the same problem more compactly as

$$p(i) : [ ] \mid j \vdash ? : [ j = 0 \mapsto p(1) \mid j = 1 \mapsto p(0) ] \quad (2.2)$$

³This is similar to the fragments of type theory used to axiomatise higher structures such as weak ω-groupoids in e.g. [Bru16, Appendix A] and [FM17].