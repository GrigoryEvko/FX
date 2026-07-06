27:4

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

Carrying out a normalization-by-gluing proof, therefore, turns the classical approach on its head. Originally one defined the normalization algorithm then showed it to be sound, complete, and idempotent. When carrying out the proof by gluing, the algorithm is not defined up front. Instead, one carefully constructs a gluing category $\mathbf{Gl}(F)$ built on a functor out of the category of contexts of the initial model $\mathcal{I}$. Concretely, this is the category of syntactic contexts and simultaneous substitutions between them up to definitional equality. The heart of the argument then breaks down into three steps:

(1) We show that $\mathbf{Gl}(F)$ supports a particular model of type theory $\mathcal{G}$.
(2) We define a *reify* operation which sends terms from $\mathcal{G}$ to normal forms.
(3) We show that the projection $\pi_0$ induces a morphism of models $\mathcal{G} \longrightarrow \mathcal{I}$ and that for a given term $x$ in $\mathcal{G}$ reifying $x$ yields a normal form for $\pi_0(x)$.

In particular, types in $\mathcal{G}$ will be chosen such that they consist of a type from the initial model along with a proof-relevant predicate carving out those terms which have (suitably hereditary) normal forms. A term in this model is then a term from the syntactic model together with a witness for the proof-relevant predicate associated with the type.

The first step and the universal property of the initial model produces a morphism of models $i : \mathcal{I} \longrightarrow \mathcal{G}$ and the second step ensures that $\pi_0 \circ i = \mathsf{id}$. Remarkably, this already defines a sound and complete normalization algorithm. The algorithm simply takes a syntactic term $M : A$, regards it as an element of the initial model, and then reifies $i(M)$ to obtain the normal form. Moreover, because $\pi_0 \circ i = \mathsf{id}$ we conclude that this yields a normal form for the supplied $M$.

To a coarse approximation, the construction of $\mathcal{G}$ and reification specifies the normalization algorithm and proves its soundness in a single step. The attentive reader will notice, however, that the completeness requirement from Section 1.2 seems to be absent from this new story. In fact, in this approach completeness is automatic and no proof is required. Indeed, terms and types within the initial model are realized by equivalences classes of syntactic terms and types taken up to definitional equality. Accordingly, the morphism $i$—and therefore the normalization algorithm—cannot distinguish between definitional equal terms.

One might suspect that working with equivalence classes of terms when defining $\mathcal{G}$ simply causes the burden to shift so that—while there is no need to prove completeness separately—the work of such a proof is spread throughout the construction of $\mathcal{G}$. In fact the opposite is the case: working with terms up to definitional equality substantially simplifies the construction of $\mathcal{G}$. Connectives in type theory only have universal properties up to definitional equality. Only when working with equivalences classes therefore, can we use these universal properties and benefit from existing results. For instance, we shall see that our construction of dependent products in our gluing model is essentially mechanical.

The gluing approach yields other unexpected advantages. Recall that $\mathbf{Gl}(F)$ intuitively consists of *proof-relevant* predicates. This proof relevance is crucial to an elegant treatment of universes in the model [Coq19]. We are able to define the predicate associated with an element of a universe to consist not only of an appropriate normal form but to also contain the data of the type it encodes within the model. In proof-irrelevant settings, universes were a frequent source of difficulty which necessitated laborious techniques to encode [All87].

1.4. **Synthetic Tait computability.** Using gluing to prove normalization is certainly an improvement over 'free-hand' proofs of normalization-by-evaluation, but the picture is not as