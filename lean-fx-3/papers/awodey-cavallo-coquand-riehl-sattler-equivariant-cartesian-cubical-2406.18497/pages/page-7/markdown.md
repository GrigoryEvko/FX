$\mathsf{H} \to \mathsf{cSet}^2$ sending the object to $\vec{0}: 1 \xrightarrow{\sim} I^n$ and $\sigma \in H$ to

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \\ \vec{0} \updownarrow & & \vec{0} \updownarrow \\ I^n & \xrightarrow{\sigma} & I^n \end{array}$$

now *does* lift to a diagram of trivial cofibration coalgebras; its colimit exhibits the point $\vec{0}: 1 \to I^n_H$ as a trivial cofibration, making $I^n_H$ contractible.

These observations led us to a construction of the generating categories of cofibrations and trivial cofibrations for the equivariant model structure in Summer 2019. While we felt confident that these categories were canonical—since we had arrived at their definition simultaneously through two different constructions, one category theoretic and one type theoretic—the corresponding model structure felt somewhat ad hoc, not fitting into known paradigms for constructions of model categorical models of homotopy type theory. A few years later, we realized that the equivariant premodel structure could be transferred from a premodel structure on the category $\mathsf{cSet}^2$ of *cubical species* (i.e., symmetric sequences of cubical sets), where there exists a canonical equivariant interval object $\mathbb{I} = (I^n)_{n \geq 1}$. There the generating cofibrations and trivial cofibrations fit into a known paradigm where the latter are defined from the former using the generic point of the interval $\mathbb{I}$ (as in [ABCHFL21; CMS20; Awo26]).$^{5}$

1.6. **Results.** Our results are summarized by the following theorem.

**Theorem 1.6.1.** *There is a constructively definable model of HoTT in cartesian cubical sets with an associated constructively definable Quillen model structure that is classically Quillen equivalent to the Kan–Quillen model structure on simplicial sets.*

By *associated Quillen model structure*, we mean as in §1.3 a model structure whose fibrations are the retracts of context extensions of the model of HoTT and whose trivial fibrations are the retracts of context extensions by contractible types.

By a *model of HoTT* we mean a model of Martin-Löf type theory validating the univalence axiom, and by *model of Martin-Löf type theory* we mean a natural model [Awo18b] equipped with $\Pi$-types, $\Sigma$-types, identity types, and universes closed under these. More precisely, what we construct is a *natural pseudo-model* in the sense of Shulman [Shu19, §A] with weakly stable equivalents of this structure (a weakly stable class of $\Pi$-types, etc.); one can then apply Lumsdaine and Warren's *left adjoint splitting* coherence construction [LW15; Awo18b; Shu19, §A] to obtain a natural model with strictly stable structure. Concretely, our category of contexts is the category $\mathsf{cSet}$ of cartesian cubical sets, and the natural pseudo-model specifying the types and terms is the *notion of fibred structure* encoding the equivariant fibrations (Lemma 5.3.3). The interpretation of type formers is as follows.

- Weakly stable $\Sigma$-types and identity types arise immediately from the model structure (see, e.g., [LW15, §4.2]). $\Sigma$-types are interpreted by composition of fibration algebras, while the identity type on $A \to \Gamma$ is interpreted by the (trivial cofibration, fibration) factorization of its diagonal $A \to A \times_\Gamma A$ (as in [AW09]).
- Weakly stable $\Pi$-types come from the *Frobenius condition* [BG12, 3.3.3; GS17], that is the closure of fibrations under pushforward along fibrations, which is verified in Proposition 5.3.2.
- Universes are interpreted by classifiers for the notions of fibred structure encoding $\kappa$-small equivariant fibrations for sufficiently large inaccessible cardinals $\kappa$ (Proposition 5.3.7). Importantly,

$^{5}$Interestingly, while the equivariant premodel structure is lifted along a right adjoint, the constant functor $\Delta: \mathsf{cSet} \to \mathsf{cSet}^2$, the model structure itself is not: the fibrations and trivial fibrations are created by $\Delta$, but the weak equivalences between non-fibrant objects are not.

7