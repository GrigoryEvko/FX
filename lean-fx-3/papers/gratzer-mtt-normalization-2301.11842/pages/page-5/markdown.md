Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:5

rosy as it may first appear. Models of type theory are subject to a variety of strict equations (see Item 3 on page 4) which often force external constructions, where naturality obligations can be prohibitive. Worse, the passage between mathematics internal to the gluing category and external constructions is difficult and the boundary frequently raises mismatches.

We follow Sterling and Harper [SH21] and adopt a synthetic approach to gluing. We begin with two crucial observations. First, while models of type theory are strangely behaved objects, one can often embed a model into a presheaf topos and thereby work in an extremely rich setting. Second, when gluing together presheaf topoi along a nice functor $\mathbf{Gl}(F : \mathbf{PSh}(\mathcal{C}) \longrightarrow \mathbf{PSh}(\mathcal{D}))$, the result is another presheaf topos and the internal language of this topos contains lex idempotent monads $(\bigcirc, \bullet)$ allowing one to recover both $\mathbf{PSh}(\mathcal{C})$ and $\mathbf{PSh}(\mathcal{D})$.

Sterling and collaborators have then shown that it is possible to work exclusively within the internal language of $\mathbf{Gl}(F)$ to construct the normalization model and have termed this approach synthetic Tait computability (STC). Experience has shown that working internally simplifies constructions involved in the gluing model, making it practical to prove metatheorems for even extremely complex type theories like cubical type theory [SH21, SA21, Ste21, GB22, SH22].

Proofs using STC construct the model within $\mathbf{Gl}(F)$ by defining a sequence of constants within the internal language. Accordingly, the heart of the normalization proof is realized by a series of programming exercises in extensional type theory. This alone does not remove the strict equations that cause trouble with typical gluing proofs but it does provide a systematic approach to handling them. Concretely, within an STC proof, all the required strict equations have a particular form: for some type operator in the object theory, we are given an element $\mathsf{op} : \bigcirc \mathsf{Ty}$ corresponding to the operator in the syntactic model, and we must extend this to an element of $\mathsf{Ty}$. Within the internal language, the two components of this problem (the element of $\mathsf{Ty}$ and the proof that it extends $\mathsf{op}$) can be represented by an element of the following dependent sum:³

$$\sum_{A:\mathsf{Ty}} x \leftarrow \mathsf{op}; \bigcirc (A = x)$$

The second component in particular represents the aforementioned strict equation. In practice, it is easy to obtain an element of $\mathsf{Ty}$ which extends $\mathsf{op}$ up to isomorphism i.e. an element of the following type:

$$\sum_{A:\mathsf{Ty}} x \leftarrow \mathsf{op}; \bigcirc (\mathsf{Tm}(A) \cong \mathsf{Tm}(x))$$

Remarkably, this proves to be enough. The internal language of $\mathbf{Gl}(F)$ supports a strictification axiom [OP18] which provides a section to the canonical projection from the first type to the second. We are therefore able to construct various connectives which agree only up to isomorphism with their syntactic counterparts and correct them to construct the model. For instance, a dependent product is determined by a universal property and it is possible to construct a type in $\mathbf{Gl}(F)$ with this property by virtue of general categorical theorems. However, the result will only satisfy the required equation up to isomorphism. The strictification axiom allows STC proofs to benefit from the general categorical result without resorting to unfolding the construction supplied by the abstract argument.

³Here we have used standard syntactic sugar to represent the monadic operations of $\bigcirc$.