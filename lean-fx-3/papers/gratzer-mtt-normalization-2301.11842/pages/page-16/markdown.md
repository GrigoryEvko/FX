27:16

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

The collection of natural isomorphisms $\alpha_\mu$ satisfy a number of coherence conditions forcing them to behave as expected with respect to composition and identity in $\mathcal{M}$ as well as to force them to be natural with respect to 2-cells in $\mathcal{M}$. Fortunately, these higher conditions will not generally factor into what follows, so we refer the reader to Johnson and Yau [JY20] where this notion is detailed under the name *strong transformation*.

Note that $F(m)$ and $G(m)$ are both LCC and equipped with universes closed under various connectives. The next part of Definition 3.8 requires that $\alpha_\mu$ respects this additional structure. Finally, since $F(\mu)$ and $G(\mu)$ are both right adjoints, one can ask whether there is a natural isomorphism witnessing $\alpha_m \circ F_!(\mu) = G_!(\mu) \circ \alpha_n$. The final requirement—that $\alpha_\mu$ satisfy the Beck-Chevalley condition—essentially states that there is such a natural isomorphism and that it is canonically induced from $\alpha_\mu$. In particular, this ensures that transposing a morphism along $F_!(\mu) \dashv F(\mu)$ and then applying $\alpha_m$ produces the same result as applying $\alpha_n$ and transposing along $G_!(\mu) \dashv G(\mu)$.

A morphism of MTT cosmoi is both more and less restrictive than a morphism of MTT models. While a morphism of models need not induce an LCC functor between the relevant presheaf categories, a morphism of cosmoi is not required to strictly preserve context extension or the choice of terminal context. It so happens that the only map of consequence in this paper is locally cartesian closed, so the additional structure of morphisms of cosmoi poses no issue. Not requiring the strict preservation of context extension and dropping the representability requirements from MTT cosmoi, however, ensures that cosmoi are far easier to construct.

Merely defining a normalization cosmos $\mathcal{G}$ and projection $\pi : \mathcal{G} \longrightarrow \mathcal{S}$, however, is not enough to prove normalization; we also need a section to $\pi$. In the category of models, this section would exist as a consequence of initiality, but $\mathcal{S}$ is not initial in the category of MTT cosmoi.$^6$ Accordingly, we cannot easily obtain a section of a map into $\mathcal{S}$ and in fact sections rarely exist. Any such map, however, is essentially surjective on definable terms e.g., for any syntactic context $\Gamma$ there exists some object in $X : G(m)$ along with $\alpha : \pi(X) \cong \mathbf{y}(\Gamma)$. Similar statements hold for terms, types, etc. While these choices need not assemble into a morphism of cosmoi, such piecemeal liftings suffice for the normalization algorithm in Section 6.

**Theorem 3.9.** *Fix an MTT cosmos $G$ and $\pi : G \longrightarrow \mathcal{S}$.*

(1) *For $\Gamma \propto \otimes m$, there exists $[\![\Gamma]\!] : G(m)$ and a canonical isomorphism $\alpha_\Gamma : \mathbf{y}(\Gamma) \cong \pi([\![\Gamma]\!])$.*
(2) *For every $\Gamma \vdash A \otimes m$, there exists $[\![A]\!] : [\![\Gamma]\!] \longrightarrow \mathcal{T}_m$ such that $\pi([\![A]\!] \circ \alpha_\Gamma = [\![A]\!]$.*
(3) *For every $\Gamma \vdash M : A \otimes m$, there exists $[\![M]\!] : [\![\Gamma]\!] \longrightarrow \mathcal{T}_m^*$ lying over $[\![A]\!]$ such that $\pi([\![M]\!] \circ \alpha_\Gamma = [\![M]\!]$.*

*Here $[\![\Gamma]\!]$ is the isomorphism induced by the Yoneda lemma. Moreover, each lift $[\![\Gamma]\!]$ respects definitional equality.*

**Remark 3.10.** While we have proven this result quite generally, we will apply it only in the special case where $\pi$ is a 2-natural transformation between strict 2-functors and required isomorphisms of left adjoints are likewise identities. The reader may accordingly safely ignore these coherences when reading the proof without consequence.

**Remark 3.11.** Both Theorem 3.4 and 3.9 are categorical abstractions of *rule induction*. Indeed, 3.4 is used to prove 3.9—via the construction of an appropriate displayed

$^6$2-monad theory [KPT99, GS20] yields an initial cosmos $\mathcal{I}$ but we work with $\mathcal{S}$ because—unlike $\mathcal{I}$—it is known to adequately represent syntax.