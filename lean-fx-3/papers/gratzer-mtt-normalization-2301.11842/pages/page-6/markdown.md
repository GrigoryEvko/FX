27:6

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

1.4.1. *Synthetic Tait computability for MTT*. Unlike Martin-Löf type theory or cubical type theory, a model of MTT is not a single category equipped with additional structure. Rather, a model is a network of categories, each supporting their own individual model of type theory which are then connected by various adjoints and natural transformations. The internal language of any of these categories is insufficient to construct the gluing model, so it is necessary to generalize from working in the extensional type theory of a topos to working in all topoi simultaneously using extensional MTT. Each topos then comes equipped with the structure of STC: a pair of lex monads and a strictification axiom. We prove that this mode-local structure is respected by the MTT modalities between topoi and call the resulting language *multimodal synthetic Tait computability*. The smooth interaction between MTT modalities and the lex monads ○ and ● ensures that the key techniques of STC proofs can be generalized to multimodal STC.

With this machinery, we are able to give a concise and conceptual construction of the gluing model and extract the first normalization algorithm for multimodal type theory. In practice, this internal proof is necessary; removing the simplifying assumption on substitutions used in the canonicity proof given by Gratzer et al. [GKNB21] is already nearly intractable.

1.5. **Contributions**. We contribute a normalization algorithm for MTT equipped with the full suite of connectives: dependent sums, products, booleans, intensional identity types, a universe, and modal types. In addition to the usual corollaries of normalization (decidability of type checking, injectivity of type constructors, etc.), this sharpens the canonicity result of Gratzer et al. [GKNB20a]. This algorithm applies to any choice of mode theory and therefore simultaneously establishes normalization results for many specialized modal calculi.

In order to prove this result, we advance modern gluing techniques to apply to modal type theories and demonstrate that extensional MTT itself is a suitable metalanguage for carrying out the proof of normalization-by-gluing. We further argue that these techniques scale by extending the proof to a version of MTT supplemented with crisp induction principles and deduce that e.g., normalization continues to hold.

Section 2 gives a brief tutorial on MTT and introduces normal forms for this type theory. In Section 3, we discuss the models of MTT and relax the definition of a model of MTT to obtain *MTT cosmoi*. We prove that the syntactic cosmos enjoys a privileged position among MTT cosmoi (Theorem 3.9). Section 4 introduces *multimodal synthetic Tait computability* and shows that gluing together a network of topoi results in a model of extensional MTT equipped with STC structure in each mode (Theorem 4.17). Finally, in Section 5 we construct the normalization cosmos (Theorem 5.12) and extract the normalization function in Section 6 (Theorem 6.4). Section 7 discusses an extension of this proof to support crisp induction.

## 2. A PRIMER ON MTT

We collect the key ideas of MTT [GKNB21]. First, as mentioned in Section 1, MTT is parametrized by a mode theory: a strict 2-category $\mathcal{M}$ whose objects are modes, morphisms are modalities, and 2-cells are natural transformations between modalities. Henceforth, we will work with MTT over a fixed mode theory $\mathcal{M}$.

MTT plays two distinct roles in this paper. First, it is the object theory under consideration and the subject of our normalization theorem. However, as the proof of normalization uses MTT as an internal language to construct the normalization model MTT is also used as a metalanguage. These two different uses invite two very distinct perspectives on the