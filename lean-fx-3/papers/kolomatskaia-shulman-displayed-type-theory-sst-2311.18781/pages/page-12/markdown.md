## 2 Syntax

As suggested in the introduction, dTT is based on a modal type theory roughly in the style of [GKNB21, GCK+22], with two modes, one for discrete types and one for (augmented semi-)simplicial types. It then adds a notion of 'display' at the simplicial mode that partially internalises unary parametricity.

In addition, the general form of display, which is needed to state the computation rules for simple display, incorporates dependence on an arbitrary telescope (i.e. context extension). Thus, we also have to include a calculus of telescopes in the theory.5 The fully general calculus of telescopes and display involves a lot of operations, but in syntax and in most models they are all definable from a smaller number of primitives.

This section is organised as follows. In section 2.1 we define the mode theory, which is a 2-category describing the structure of the modal operators. Then in section 2.2 we give the rules for the underlying modal type theory, with modalities but not display.

In section 2.3 we introduce the most basic notions of the telescope calculus: telescopes, partial substitutions (elements of telescopes), and types and terms dependent on a specified telescope (which we call 'meta-abstractions'). These basic notions suffice to give the rules for display, defined mutually with a similar but non-indexed operation on telescopes that we call décalage, in section 2.4.

The remaining two sections introduce further operations that are all essentially 'definable' in terms of the previous ones. This is not strictly true at the level of algebraic syntax, where telescopes are just an additional sort of a generalised algebraic theory. But in a model where telescopes are defined to be finite lists of types — which is an option in any model, both the free syntactic model and in semantic models arising from categories — the laws satisfied by these operations characterise them uniquely. Specifically, in section 2.5 we introduce meta-abstracted telescopes, telescope concatenation, and Π-telescopes, and then in section 2.6 we introduce display for telescopes, and décalage for dependent telescopes. These operations will be used in section 3 to formulate displayed coinductive types, including the type of semi-simplicial types.

### 2.1 THE MODE THEORY

We begin with a modal type theory based on the following 2-category ℳ:

- there are two modes (objects), dm for discrete and sm for simplicial
- there are five nonidentity morphisms, forming hom-posets:

$$\begin{array}{lll} \mathcal{M}(\mathrm{dm}, \mathrm{dm}) = \{1_{\mathrm{dm}}\} & \mathcal{M}(\mathrm{dm}, \mathrm{sm}) = \{\triangle\} \\ \mathcal{M}(\mathrm{sm}, \mathrm{dm}) = \{\square \leqslant \diamond\} & \mathcal{M}(\mathrm{sm}, \mathrm{sm}) = \{\triangle\square \leqslant 1_{\mathrm{sm}} \leqslant \triangle\diamond\} \end{array}$$

5It would probably be possible to collapse this to dependence on a single type, using Σ-types instead of telescope extension, as in [ACKS24], but this would be unaesthetic and less practical for implementation.

12