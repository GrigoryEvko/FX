We want to lift g to FX, which is to say we want to give

$$\Gamma, \text{ \textasymp } \Delta \square \mid (v : \Upsilon) \vdash_{\text{sm}} h \, v : A \, (\zeta \, v)$$

$$\Gamma, \text{ \textasymp } \Delta \square \mid (v : \Upsilon), (b : \mathcal{B} \, \phi \, (h \, x)) \vdash_{\text{sm}} t \, v \, b : X^d \langle \, \zeta \, v \, , \, \sigma \, (h \, (\zeta \, v) \, (g \, v)) \, b \, \rangle \, (g \, v)$$

But such an h is exactly part of the structure of Y, while we can define

$$t \, v \, b \equiv g^d \, v \, (\tau \, v \, b).$$

The final equation in the structure of Y is precisely what is necessary to make this well-typed. The functoriality condition is immediate from the functoriality of d.

Thus Y is a generalised F̄-coalgebra, and hence it admits a unique generalised F̄-coalgebra morphism to the terminal F̄-coalgebra C. This is a map Y → (Φ | X) over ζ, which is precisely the right type of corec. And by lemma 4.53, the fact that it is a generalised F̄-coalgebra map precisely gives it the correct computation rules.

### 4.5.5 Correctness of semi-simplicial types

Finally, we will justify our universal characterization of SST semantically. Specifically, we will show that when SST is constructed as a displayed coinductive type as in section 4.5.2, in a model with ω-limits, it does in fact yield a 'classifier' of Reedy fibrant semi-simplicial types in the classical sense.

We begin by constructing such a classifier category-theoretically, and then show that this construction coincides with the one obtained from section 4.5.2. We will assume some familiarity with the classical notions of Reedy fibrant diagrams as in [KL21]. For all of this section, we fix a particular universe level ℓ.

#### 4.5.5.1 Ordered direct categories. Our category-theoretic construction of diagram classifiers works for presheaves over any 'direct category' (i.e. diagrams on any 'inverse category').

Definition 4.55. A direct category is a category such that the relation 'there is a nonidentity arrow from x to y' on its objects is well-founded. A sieve in a (direct) category is a full subcategory J such that if f : y → x and x ∈ J, then y ∈ J. An ordered direct category is a finite direct category together with (1) a total ordering on its objects such that if f : x → y then x ⩽ y, and (2) such that for all objects x, the set of arrows with codomain x has a linear order such that f ∘ g ⩽ f for any composable f, g (hence in particular l_x is the greatest element).

An ordered presheaf on a direct category is a finite presheaf together with a linear order on the finite set ∑_{x∈I} H(x) such that H(f)(h) < h whenever the left-hand side makes sense.

An ordered direct category is equivalently the opposite of a (finite) 'ordered inverse category' in the sense of [KL21, Definition 3.17], together with a suitable total ordering on its objects (we require this so that the order of variables in the classifying context is specified). Similarly, an ordered presheaf is a 'finite extension' ∅ ↪ H in the sense of [KL21, Definition 3.10].

90