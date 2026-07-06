27:2

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

While this flexibility allows MTT to accommodate many interesting calculi, it becomes proportionally more challenging to prove metatheoretic results about MTT. In particular, the rich substitution structure inherited from the mode theory can introduce subtle equations between terms. The proof that the crisp induction principles can be reconstructed in MTT [GKNB21, Theorem 10.4], for instance, exemplifies this and hinges on many such calculations. In fact, the metatheoretic results established by Gratzer et al. [GKNB20a] (soundness and canonicity) are results on closed terms in MTT, allowing their proofs to avoid the majority of the substitution apparatus.

Crucially, it remained open whether MTT admitted a normalization algorithm and, consequently, whether type checking was decidable. Even in the presence of a normalization algorithm MTT cannot admit an unconditional type checking algorithm: it is not only necessary to have a decision procedure for terms in the language, but also for modalities and 2-cells as both appear in terms for MTT.

In this paper we show the best possible result holds: MTT admits an unconditional normalization algorithm and conversion of normal forms is decidable if conversion is decidable in the mode theory.¹ As corollaries, we show that type constructors in MTT are always injective and that type checking is decidable when the mode theory is decidable.²

1.2. Normalization-by-evaluation. A normalization algorithm must begin by defining normal forms. Their precise formulation depends on the situation but they always satisfy two crucial properties. First, the equality of normal forms $u = v$ is clearly decidable—often no more than structural equality—and there is a function $\mathbf{dec}(u)$ decoding a normal form to a term of the same type.

Relative to a notion of normal form, a normalization algorithm sends a term $\Gamma \vdash M : A$ to a normal form $\mathbf{nf}_{\Gamma}(M, A)$ such that $(\mathbf{nf}_{\Gamma}(-, A), \mathbf{dec}(-))$ lifts to an isomorphism between equivalence classes of terms of $A$ and normal forms [Abe13]. Typically one breaks the condition that $(\mathbf{nf}_{\Gamma}(-, A), \mathbf{dec}(-))$ forms an isomorphism into three conditions:

(1) Completeness: if $\Gamma \vdash M = N : A$ then $\mathbf{nf}_{\Gamma}(M, A) = \mathbf{nf}_{\Gamma}(N, A)$.
(2) Soundness: $\Gamma \vdash \mathbf{dec}(\mathbf{nf}_{\Gamma}(M, A)) = M : A$.
(3) Idempotence: $u = \mathbf{nf}_{\Gamma}(\mathbf{dec}(u), A)$.

Remark 1.1. We warn the reader that this terminology is not entirely standard. Various sources use the opposite conventions of soundness and completeness [AK16, AK17]. Such sources often refer to the final condition as stability.

Proving normalization is an involved affair. Traditionally, one begins by fixing a strongly normalizing confluent rewriting system presenting the equational theory of the type theory. The normal forms are then exactly the terms of the theory which cannot be further reduced. This approach does not scale, however, to type theories with type-directed equations such as the unicity principles of dependent sums and the unit type. These equations defy attempts to present them in a rewriting system and require type-directed algorithms.

The preeminent type-directed technique for normalization is normalization-by-evaluation (NbE) [Abe13]. Proving that an NbE algorithm works, however, is an extremely intricate affair involving a variety of complex constructions. After the algorithm is defined, the

¹The converse is almost, but not quite, true. Decidability of conversion for normal forms implies that the 1- and 2-cells of the mode theory have decidable equality, as these appear in normal forms.

²This requirement is potentially nontrivial e.g., the word problem for groups is known to be undecidable and is subsumed by the problem for 2-categories.