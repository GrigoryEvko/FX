# Chapter 15

## Programming in cohesive parametric type theory

Having established a basic suite of rules governing the modal context operators and modal types, we now apply the theory. As described in Chapter 13, our overarching goal is to show that the free theorems that hold of terms defined in the parametric mode can be used to obtain results in the pointwise mode.

We begin in Section 15.1 with a few lemmas for conveniently reasoning about the discrete embedding type Disc. In Section 15.2 we return to the example of Church booleans from Section 10.1: we show that any pointwise Church boolean that arises from a parametric Church boolean is “true” or “false”. Section 15.3 revisits the concept of bridge-discreteness introduced in Section 10.3; we show in particular that types of the form $\text{Disc}(A)$ are bridge-discrete. Finally, Section 15.4 shows that we can apply our characterization of parametrically polymorphic functions between smash products from Section 10.5 to obtain algebraic laws and coherences for the pointwise smash product.

### 15.1 Properties of the discrete embedding

Before getting into concrete examples, it is useful to derive a few basic properties of the discrete type, which plays the central role in transferring parametricity results.

First, in addition to the ordinary discrete eliminator, the presence of the codiscrete type allows us to derive an eliminator for inhabiting *pointwise* families indexed by a modal hypothesis ($\text{dsc} \mid d : \text{Disc}(A)$) of discrete type. This is analogous to Shulman’s derivation of “crisp $b$-induction” [Shu18, Lemma 5.1] in his own cohesive type theory; our modal hypotheses under dsc play the role of his crisp hypotheses, while Disc-types play the role of $b$-types.

265