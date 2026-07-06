Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:39

two separate proofs of normalization; one through both an untyped PER model similar to Gratzer et al. [GSB19a] and one using a gluing model. Their gluing proof is closely related to the argument above. For instance, their theory of unified substitutions and modal transformations corresponds to a specialization of MTT's substitution calculus to one modality and, accordingly, their category of renamings offers a strict presentation of the category of renamings described above. Their proof, however, is done using external constructions on the gluing category which may make it difficult to scale to either multiple modalities or dependent types.

**Synthetic Tait computability.** The introduction of representable map categories [Uem19] and LCCCs [GS20] for modeling the syntax of (non-modal) type theory offered an alternative approach. Crucially, they show that syntax can be given a universal property among structured categories with better behavior than CwFs. Sterling and collaborators [SH21, SA21, Ste21] have built on this idea and introduced synthetic Tait computability to prove syntactic metatheorems via gluing together LCCCs rather than CwFs. Unlike other approaches to gluing, STC generalizes well to a multimodal setting and by extending STC to MSTC normalization for MTT becomes tractable.

**MTT as a metalanguage.** In a parallel line of work, Bocquet et al. [BKS21] have also used MTT as a metalanguage in the construction of models of type theory. They, however, do not work with a modal object type theory and instead use MTT to internalize a functor $F$ rather than working internally to $\mathbf{G}\mathbf{l}(F)$. As a result, while both proofs use MTT modalities, the modalities used by op. cit. are encoded in our proof by fibered lex monads $(\bigcirc, \bullet)$ which prove easier to manipulate.

## 9. CONCLUSIONS AND FUTURE WORK

We prove normalization for MTT (Theorem 6.4) and thereby reduce the decidability of conversion and type checking to the decidability of equality of the underlying mode theory (Corollaries 6.6 and 6.10). In addition, we deduce a number of corollaries from normalization itself, including the injectivity of type constructors and canonicity (Corollaries 6.9 and 6.11).

By working constructively, we have obtained an effective procedure for normalization. This, along with our results on type checking, open the door to a theoretically-sound implementation of MTT generic in the mode theory. In the future, we intend to develop a bidirectional syntax for MTT and implement it. Stassen et al. [SGB22] have made promising initial steps in this direction for *poset-enriched* mode theories.

## ACKNOWLEDGMENTS

I am thankful for discussions with Carlo Angiuli, Martin Bidlingmaier, Lars Birkedal, Thierry Coquand, Alex Kavvos, Christian Sattler, and Jonathan Sterling. I am also grateful to the careful reading and comments provided by the reviewers of this paper. The author was supported in part by a Villum Investigator grant (no. 25804), Center for Basic Research in Program Verification (CPV), from the VILLUM Foundation.