Logical Methods in Computer Science
Volume 19, Issue 2, 2023, pp. 1:1–1:54
https://lmcs.episciences.org/

Submitted Jul. 10, 2021
Published Apr. 05, 2023

# LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

MICHAEL SHULMAN

University of San Diego
e-mail address: shulman@sandiego.edu

ABSTRACT. We define and study LNL polycategories, which abstract the judgmental structure of classical linear logic with exponentials. Many existing structures can be represented as LNL polycategories, including LNL adjunctions, linear exponential comonads, LNL multicategories, IL-indexed categories, linearly distributive categories with storage, commutative and strong monads, CBPV-structures, models of polarized calculi, Freyd-categories, and skew multicategories, as well as ordinary cartesian, symmetric, and planar multicategories and monoidal categories, symmetric polycategories, and linearly distributive and *-autonomous categories. To study such classes of structures uniformly, we define a notion of LNL doctrine, such that each of these classes of structures can be identified with the algebras for some such doctrine. We show that free algebras for LNL doctrines can be presented by a sequent calculus, and that every morphism of doctrines induces an adjunction between their 2-categories of algebras.

# CONTENTS

|  1. Introduction | 2  |
| --- | --- |
|  2. LNL polycategories | 4  |
|  3. Relation to the literature | 14  |
|  4. Unifying universality | 23  |
|  5. Doctrines and sketches | 33  |
|  6. Sorted doctrines | 36  |
|  7. The doctrinal completion of a sketch | 41  |
|  8. The sequent calculus of a doctrine | 43  |
|  9. Adjunctions induced by doctrine maps | 49  |
|  Acknowledgments | 51  |
|  References | 51  |

Key words and phrases: linear logic, exponential modality, polycategory, multicategory, doctrine, sequent calculus.

This material is based on research sponsored by The United States Air Force Research Laboratory under agreement numbers FA9550-15-1-0053 and FA9550-21-1-0009.

LOGICAL METHODS
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-19(2:1)2023

© M. Shulman
Creative Commons

1:2

M. SHULMAN

Vol. 19:2

## 1. INTRODUCTION

When presenting logics and type theories, it is generally useful to separate the *structural* rules, such as exchange, weakening, contraction, identity, and cut, from the *logical* rules governing particular connectives. This separation of concerns can be reflected in categorical semantics by starting with a kind of *multicategory* [Lam69, Her00, Lei04] or *polycategory* [Sza75] encapsulating the structural rules, in which we can formulate universal properties of objects that correspond to the connectives.

A multicategory is like a category, but allows the domain of a morphism to be a finite list of objects; a polycategory allows both the domain and codomain to be such a list. Such morphisms correspond respectively to intuitionistic sequents $A_1, \dots, A_m \vdash B$ and classical sequents $A_1, \dots, A_m \vdash B_1, \dots, B_n$. One can then formulate universal properties for “tensor products” as representing objects for such morphisms, generalizing the classical characterization of the tensor product of vector spaces as a representing object for multilinear maps.

The choice of structural rules in a logic is reflected by an action on the morphisms of a multi- or polycategory that modifies the elements in the domain or codomain lists. For instance, the exchange rule is reflected by an operation taking any morphism $(\Gamma, A, B, \Delta) \rightarrow C$ to a morphism $(\Gamma, B, A, \Delta) \rightarrow C$. This leads to different kinds of multi- and polycategory, such as the following.

- Cartesian multicategories (a.k.a. abstract clones) correspond to intuitionistic nonlinear logic, with all structural rules. A cartesian multicategory with enough representing objects is equivalent to a cartesian monoidal category or a cartesian closed category.
- Symmetric multicategories correspond to intuitionistic multiplicative-additive linear logic, with exchange but no weakening or contraction. A symmetric multicategory with enough representing objects is equivalent to a symmetric monoidal category, possibly closed.
- Symmetric polycategories correspond to classical multiplicative-additive linear logic. A symmetric polycategory with enough representing objects is equivalent to a linearly distributive category or a *-autonomous category.

Multicategories and polycategories also have advantages from a purely category-theoretic standpoint. They can simplify coherence problems, since operations defined by universal properties generally do not require explicit coherence axioms. They can also enable the unification of different-looking structures in a larger context; for instance, monoidal categories and closed categories can both be represented as multicategories [Her00, Man12], and the Chu and Dialectica constructions are both instances of one polycategorical operation [Shu20].

It seems, however, that no polycategorical structure exists in the literature to correspond to *classical* linear logic *with exponentials*. Structured categories with exponential modalities have certainly been studied, such as LNL adjunctions [Ben95] and linearly distributive categories with storage [BCS96]. And a multicategorical version, corresponding to *intuitionistic* linear logic with exponentials, is suggested in [HT21]. But the polycategorical case appears to be missing.

In this paper we fill this gap by defining *LNL polycategories*. An LNL polycategory has two classes of objects, called *linear* and *nonlinear*. The linear objects form a symmetric polycategory, while the nonlinear objects form a cartesian multicategory, and there are additional morphisms relating the two classes of objects, enabling a description of the modalities ! and ? by universal properties. This can be regarded as a semantic counterpart of

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:3

split-context presentations of linear logic, such as [Ben95, Bar96, Wad94] in the intuitionistic case and [Gir93] in the classical one.

Like their syntactic counterpart of full classical linear logic, LNL polycategories are an extremely rich structure. In addition to LNL adjunctions and linearly distributive categories with storage, they include cartesian multicategories (if all objects are nonlinear), symmetric polycategories (if all objects are linear), symmetric multicategories (if all objects are linear and all codomains are unary), and CBPV structures (if all linear codomains are unary and all linear domains are subunary). Thus, any structured category that can be represented by any of these multi- or polycategorical notions can also be regarded as an LNL polycategory.

This suggests that LNL polycategories should provide a unifying context to compare different kinds of structured category, and to study the correspondence between logic and category. To facilitate this, we define a notion of *LNL doctrine* $\mathbb{D}$, whose “algebras” (which we call $\mathbb{D}$-categories) are LNL polycategories satisfying certain object and arity restrictions and in which objects having certain universal properties exist. Inspired by [Her04, LSR17, BZ20], we express these universal properties *fibrationally*: an LNL doctrine $\mathbb{D}$ is an LNL polycategory $|\mathbb{D}|$ equipped with a collection of distinguished “cones”, and a $\mathbb{D}$-category is an LNL polycategory $\mathcal{P}$ equipped with a functor $\mathcal{P} \rightarrow |\mathbb{D}|$ admitting a “cartesian” lift for each distinguished cone. We also incorporate a “well-sortedness” condition that allows a restriction to Kleisli adjunctions if desired. In this way, we can represent all of the following kinds of structured category, and many more, as the algebras for LNL doctrines:

- • Cartesian multicategories, symmetric multicategories, symmetric polycategories, LNL multicategories, and skew multicategories.
- • Symmetric monoidal categories, closed symmetric monoidal categories, and symmetric closed categories.
- • Cartesian monoidal categories and cartesian closed categories.
- • Cartesian monoidal categories with a commutative strong monad.
- • Symmetric monoidal categories with a strong monad.
- • CBPV adjunction models, EEC+ models, and ECBV models.
- • Freyd-categories and Freyd-multicategories.
- • Linearly distributive categories and \*-autonomous categories.
- • LNL adjunctions, possibly closed or \*-autonomous.
- • Symmetric monoidal categories with a linear exponential comonad, linearly distributive categories with storage, and \*-autonomous categories with storage.
- • Any of the above with any specified family of limits and/or colimits.

We also argue that LNL doctrines provide a unifying context to study substructural logics, and to compare the corresponding kinds of monoidal category. Specifically, we will use a well-known iterative category-theoretic construction, known as the *small object argument*, to present the *free* $\mathbb{D}$-category $\hat{S}_{\mathbb{D}}$ generated by an input datum $\mathcal{S}$ that we call a $\mathbb{D}$-sketch. This has the following two consequences.

Firstly, from this construction we can extract a syntactic sequent calculus that also presents free $\mathbb{D}$-categories. The iterative small object argument corresponds naturally to the inductive definition of sequent calculus derivations. The structural rules arise since each stage is an LNL polycategory, while the logical rules are inserted by iterative pushouts that enforce the existence of objects with universal properties. Thus, there is a precise correspondence between the syntactic and semantic versions of the separation of concerns between structural and logical rules.

1:4

M. SHULMAN

Vol. 19:2

Secondly, we use the free $\mathbb{D}$-category on a sketch to show that any morphism of doctrines $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ induces a pseudo 2-adjunction between $\mathbb{D}_1$-categories and $\mathbb{D}_2$-categories. That is, any $\mathbb{D}_2$-category $\mathcal{T}$ has an underlying $\mathbb{D}_1$-category $\mathfrak{F}^*\mathcal{T}$, and any $\mathbb{D}_1$-category $\mathcal{S}$ generates a free $\mathbb{D}_2$-category $\mathfrak{F}_*\mathcal{S}$. Thus, LNL doctrines also supply a uniform way to relate different sorts of monoidal category, potentially with exponential monads and comonads.

## 2. LNL POLYCATEGORIES

The different kinds of multicategories mentioned in Section 1, corresponding to logics with different structural rules, are all instances of a well-developed theory of “generalized multicategories” parametrized by a monad on a bicategory or double category of spans or profunctors.$^1$ This theory was used for instance in [HT21] to begin defining an analogue of LNL polycategories for intuitionistic linear logic (see our discussion of “LNL multicategories” below). LNL polycategories ought to be an instance of a similar theory of “generalized polycategories”, but unfortunately, no such general theory has been formulated yet (though [Gar08] provides strong evidence for its existence). Thus, in this paper we simply give the definitions explicitly.

**Definition 2.1.** A **linear-nonlinear (LNL) polycategory $\mathcal{P}$** consists of:

- (i) A set of **nonlinear objects**, which we denote by letters near the end of the Roman alphabet such as $X, Y, Z$. We denote finite lists of nonlinear objects by the Greek letters $\Theta, \Upsilon$. If $(X_1, \dots, X_m)$ is such a list and $\sigma: \{1, \dots, n\} \to \{1, \dots, m\}$ is a function, we write $\sigma: (X_1, \dots, X_m) \to (X_{\sigma 1}, \dots, X_{\sigma n})$ and call it a **structural map**.
- (ii) For each $\Theta, X$, a **nonlinear hom-set $\mathcal{P}(\Theta; X)$** containing **nonlinear morphisms**, with a functorial action by any structural map $\sigma: \Theta \to \Upsilon$:

$$(-)^\sigma: \mathcal{P}(\Upsilon; X) \to \mathcal{P}(\Theta; X).$$

- (iii) Compositions and identities for the nonlinear hom-sets

$$\circ_X: \mathcal{P}(\Theta_1, X, \Theta_2; Y) \times \mathcal{P}(\Upsilon; X) \to \mathcal{P}(\Theta_1, \Upsilon, \Theta_2; Y) \quad 1_X \in \mathcal{P}(X; X)$$

satisfying the multicategory axioms and equivariant for the structural actions.

- (iv) A set of **linear objects**, which we denote by letters near the beginning of the Roman alphabet such as $A, B, C$. We denote finite lists of linear objects by the Greek letters $\Gamma, \Delta$. If $(A_1, \dots, A_n)$ is such a list and $\tau: \{1, \dots, n\} \xrightarrow{\sim} \{1, \dots, n\}$ is a permutation, we write $\tau: (A_1, \dots, A_n) \xrightarrow{\sim} (A_{\sigma 1}, \dots, A_{\sigma n})$ and call it a **structural permutation**.
- (v) For each $\Theta$ and $\Gamma, \Delta$, a **linear hom-set $\mathcal{P}(\Theta \mid \Gamma; \Delta)$** containing **linear morphisms**, with a functorial action by a structural map $\sigma: \Theta' \to \Theta$ and structural permutations $\tau: \Gamma' \to \Gamma$ and $\rho: \Delta \to \Delta'$:

$$^\rho(-)^{\sigma|\tau}: \mathcal{P}(\Theta \mid \Gamma; \Delta) \to \mathcal{P}(\Theta' \mid \Gamma'; \Delta').$$

- (vi) For each $A$ an identity morphism $1_A \in \mathcal{P}(\mid A; A)$.

- (vii) Composition morphisms

$$\begin{aligned} \circ_A: \mathcal{P}(\Theta \mid \Gamma_1, A, \Gamma_2; \Delta) \times \mathcal{P}(\Theta' \mid \Gamma'; \Delta'_1, A, \Delta'_2) \\ \longrightarrow \mathcal{P}(\Theta, \Theta' \mid \Gamma_1, \Gamma', \Gamma_2; \Delta'_1, \Delta, \Delta'_2) \\ \circ_X: \mathcal{P}(\Theta_1, X, \Theta_2 \mid \Gamma; \Delta) \times \mathcal{P}(\Upsilon; X) \longrightarrow \mathcal{P}(\Theta_1, \Upsilon, \Theta_2 \mid \Gamma; \Delta) \end{aligned}$$

$^1$See [CS10] for a general framework, building on much prior work cited therein.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:5

that are associative, unital, and equivariant in all reasonable ways. (Note that by equivariance, all the compositions are uniquely determined by those in which $\Theta_2, \Gamma_2, \Delta'_2$ are empty.)

**Definition 2.2.** A **functor** $H : \mathcal{P} \to \mathcal{Q}$ between LNL polycategories consists of functions between their linear and nonlinear objects and morphisms, preserving domains, codomains, structural actions, identities, and composites. A **transformation** $\alpha : H \Rightarrow K : \mathcal{P} \to \mathcal{Q}$ between functors consists of:

- (i) For each nonlinear object $X$ of $\mathcal{P}$, a nonlinear morphism $\alpha_X \in \mathcal{Q}(HX; KX)$.
- (ii) For each linear object $A$ of $\mathcal{P}$, a linear morphism $\alpha_A \in \mathcal{Q}(|HA; KA)$.
- (iii) For each nonlinear $f \in \mathcal{P}(\Theta; Y)$, we have $\alpha_Y \circ Hf = Kf \circ (\alpha_\Theta)^2$.
- (iv) For each linear $f \in \mathcal{P}(\Theta \mid \Gamma; \Delta)$, we have $(\alpha_\Delta) \circ Hf = Kf \circ (\alpha_\Theta \mid \alpha_\Gamma)$.

This defines a strict 2-category LNLPoly.

LNL polycategories are such a rich structure that they include many better-known structures as special cases. (The reader unfamiliar with any of the structures mentioned below is free to take the asserted characterization as a definition.)

- **Symmetric polycategories** can be identified with LNL polycategories having no nonlinear objects (and hence no nonlinear morphisms). These model the judgmental structure of classical multiplicative-additive linear logic.
- **Symmetric multicategories** can be identified with LNL polycategories having no nonlinear objects and in which all (linear) morphisms are *co-unary*, i.e. have a codomain of length 1. These model the judgmental structure of intuitionistic multiplicative-additive linear logic.
- Even more degenerately, ordinary **categories** can be identified with LNL polycategories having no nonlinear objects and in which all (linear) morphisms are both unary and co-unary.
- **Cartesian multicategories** can be identified with LNL polycategories having no linear objects and no linear morphisms (here the former does not quite imply the latter, as there are homsets $\mathcal{P}(\Theta \mid ;)$). These model the judgmental structure of intuitionistic (nonlinear) logic.
- By an **LNL multicategory** we will mean an LNL polycategory in which all linear morphisms are co-unary. These model the judgmental structure of intuitionistic linear logic (with exponentials); they do not quite appear in the literature, though a structure like them is the goal of [HT21] (see Example 3.10).

**Remark 2.3.** In fact, each of the above five subcategories is a slice category LNLPoly/$\mathcal{S}$ for some subterminal object $\mathcal{S}$. The terminal object of LNLPoly has one linear object, one nonlinear object, and all hom-sets singletons; thus a subterminal object has at most one object of each sort and each hom-set a subsingleton.

The slice category LNLPoly/$\mathcal{S}$ over a subterminal is thus the full subcategory of LNLPoly consisting of those objects $\mathcal{P}$ whose unique map to the terminal object factors through $\mathcal{S}$. This means that $\mathcal{P}$ has only objects of the sorts that $\mathcal{S}$ does, and only morphisms of the arity and co-arity that $\mathcal{S}$ does.

For example, let SYMPOLY be the subterminal object with one linear object, no nonlinear objects, and all linear homsets singletons. Then LNLPoly/SYMPOLY consists of LNL

$^2$Here if $\Theta = (X_1, \ldots, X_n)$ then $Kf \circ (\alpha_\Theta)$ denotes $(\cdots (Kf \circ_{X_1} \alpha_{X_1}) \circ_{X_2} \alpha_{X_2} \cdots) \circ_{X_n} \alpha_{X_n}$, and similarly elsewhere.

1:6

M. SHULMAN

Vol. 19:2

polycategories with no nonlinear objects, i.e. symmetric polycategories. We can argue similarly for the following suggestively-named subterminals:

- SYMMULTI, which has one linear object, no nonlinear objects, co-unary linear homsets singletons, and others empty.
- CAT, which has one linear object, no nonlinear objects, and only the identity morphism.
- CARTMULTI, which has one nonlinear object, no linear objects, all nonlinear homsets singletons, and all linear homsets empty.
- LNLMULTI, which has one linear object, one nonlinear object, all nonlinear homsets and co-unary linear homsets singletons, and others empty.

For consistency, we may write the terminal object of LNLPoly as LNLPOLY.

We will consider other slices of LNLPoly later in the paper. For ease of reference, Table 3 on page 54 summarizes the definitions of all the small LNL polycategories over which we slice.

The slice category over any subterminal object $\mathcal{S}$ is coreflective, with coreflector $(-) \times \mathcal{S}$. Thus, all five of these subcategories are coreflective. In particular, any LNL polycategory $\mathcal{P}$ has an underlying symmetric polycategory, which we denote $\mathcal{P}^{\mathrm{L}}$, and an underlying cartesian multicategory, which we denote $\mathcal{P}^{\mathrm{NL}}$.

**Remark 2.4.** With a little more work, we can also represent *planar* (i.e. non-symmetric) multicategories inside LNLPoly. Specifically, any planar multicategory $\mathcal{M}$ freely generates a symmetric multicategory $\Sigma\mathcal{M}$, which has the same objects as $\mathcal{M}$, and such that a morphism in $\Sigma\mathcal{M}(\Gamma; B)$ is a pair $(f, \sigma)$ where $f \in \mathcal{M}(\Gamma'; B)$ and $\sigma : \Gamma \xrightarrow{\sim} \Gamma'$ is a structural permutation. The functor $\Sigma$ thus defined from planar multicategories to symmetric multicategories (or to LNL polycategories) is faithful but not full: the morphisms in its image are those that preserve the permutations $\sigma$. But we can enforce this condition by restriction to a suitable slice.

Let PLMULTI be the image under $\Sigma$ of the terminal planar multicategory; thus it has one (linear) object, and its morphisms with arity $n$ and co-arity 1 are labeled by permutations of $n$ objects. Then each $\Sigma\mathcal{M}$ comes with a canonical projection to PLMULTI that records the permutations $\sigma$, and a morphism $\Sigma\mathcal{M} \to \Sigma\mathcal{M}'$ is in the image of $\Sigma$ precisely when it commutes with these projections. Thus, the category of planar multicategories is equivalent to the slice category of the category of symmetric multicategories, and hence also of LNLPoly, over PLMULTI. Note that unlike the slices considered in Remark 2.3, PLMULTI is not subterminal, corresponding to the fact that $\Sigma$ is not full.

**Remark 2.5.** An analogous construction is *not* possible for planar *polycategories*; freely adding symmetric actions to a planar polycategory does not yield a symmetric one, as not all composites are definable [Kos05, Example 1.3]. Informally, the gap between planar and symmetric is wider in the classical case than in the intuitionistic one. This is one reason that in this paper we focus on the symmetric case.

**Remark 2.6.** As pointed out by a referee, it is natural to also wonder about *cyclic* multicategories [GK95, CGR14, HRY19, DCH21]. These behave very differently, because their cyclic action mixes domains and codomains — generally with an involution applied to the objects — thereby enabling them to represent morphisms with codomains of arbitrary arity as well. Hence, as shown in [Shu20, §7], cyclic *symmetric* multicategories are almost equivalent to symmetric *polycategories* with strict duals (“*-polycategories” [Hyl02]). The situation with cyclic *planar* multicategories is less clear, but they seem likely to be related

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:7

to planar polycategories, and hence would suffer from problems akin to those in described in Remark 2.5.

**Remark 2.7.** As noted in Section 1, LNL polycategories are a semantic counterpart of “split-context” syntaxes such as [Ben95, Bar96, Gir93]. It may thus be surprising that although we are modeling *classical* linear logic, we have nevertheless only split the *left-hand* context, as is done in *intuitionistic* linear syntaxes such as [Ben95, Bar96], rather than splitting both contexts as in [Gir93]. There are two reasons for this.

The first is that it is simpler and sufficient. As we will see below, even with only one split context we can still characterize *both* modalities ! and ? by universal properties. This is a polycategorical version of the observation that to model classical linear logic it suffices to have an LNL adjunction (which models intuitionistic linear logic) whose linear category is \*-autonomous; there is no need to add a second nonlinear category. Moreover, most natural examples have this form anyway.

By the way, note that the apparent asymmetry in splitting the left-hand context, rather than the right-hand one, is really just an artifact of notation. We could equally well write $\mathcal{P}(\Theta \mid \Gamma ; \Delta)$ as $\mathcal{P}(\Gamma ; \Delta \mid \Theta)$, reversing the direction of the nonlinear morphisms so they form a “co-cartesian co-multicategory”. But splitting the left-hand context is more intuitive and remains closer to the natural examples.

The second reason is that “doubly-split” LNL polycategories, at least for one definition of such, are actually a special case of singly-split ones. Let DBLSPLIT be the LNL polycategory with one linear object, two nonlinear objects, and all homsets singletons. Then an object of the slice category LNLPoly/DBLSPLIT is an LNL polycategory equipped with a partition of its nonlinear objects into two subsets, which we may call the “left-hand objects” and the “right-hand objects”. Accordingly, if $\Theta$ consists of left-hand objects and $\Upsilon$ of right-hand objects, we can choose to denote the linear homset $\mathcal{P}(\Theta, \Upsilon \mid \Gamma ; \Delta)$ by $\mathcal{P}(\Theta \mid \Gamma ; \Delta \mid \Upsilon)$. Similarly, if $\Upsilon$ consists of right-hand objects and $Z$ is a right-hand object, we can write the nonlinear homset $\mathcal{P}(\Upsilon ; Z)$ as $\mathcal{P}(Z ; \Upsilon)$, thereby regarding the right-hand objects as forming a co-cartesian co-multicategory, which acts on the linear homsets $\mathcal{P}(\Theta \mid \Gamma ; \Delta \mid \Upsilon)$ on the right.

The only possibly-surprising thing about this notion of “doubly-split LNL polycategory” is that we also have “mixed nonlinear homsets” $\mathcal{P}(\Theta, \Upsilon ; X)$ (which might perhaps be better written $\mathcal{P}(\Theta ; X ; \Upsilon)$) where $\Theta$ consists of left-hand objects, $\Upsilon$ of right-hand objects, and $X$ could be of either sort. However, such mixed morphisms arise naturally as the result of weakening a “pure” nonlinear morphism of either handedness by objects of the other handedness, and once we have these there is no reason there couldn’t be other morphisms of the same sort as well (see, for instance, Proposition 3.18).

Note also that there is a morphism to DBLSPLIT from the terminal object LNLPOLY (in fact, two of them), so that our category LNLPoly is also equivalent to a slice category of this category LNLPoly/DBLSPLIT of doubly-split LNL polycategories. Thus, formally we could take either one as the primitive notion and define the other in terms of it. We have chosen the singly-split notion as primitive, since it is, as noted above, simpler and sufficient.

We will see some more examples of LNL polycategories in Section 3, but first we define the basic universal properties that appear therein. Inspired by [BZ20], we say that a morphism $\psi$ in an LNL polycategory containing an object $R$ (linear or nonlinear) in its domain or codomain is *universal in $R$* if composing along $R$ induces bijections on homsets of all

1:8

M. SHULMAN

Vol. 19:2

possible types. For the five possible combination of types for $\psi$ and $R$, this specializes to the following.

**Definition 2.8.** Let $X$ be a nonlinear object and $A$ a linear object.

- A nonlinear morphism $\psi \in \mathcal{P}(\Theta; X)$ is **universal in** $X$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta', X; Y) \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta; Y)$$

$$\mathcal{P}(\Theta', X \mid \Gamma; \Delta) \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta \mid \Gamma; \Delta).$$

- A nonlinear morphism $\psi \in \mathcal{P}(\Theta, X; Y)$ is **universal in** $X$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta'; X) \xrightarrow{\sim} \mathcal{P}(\Theta, \Theta'; Y).$$

- A linear morphism $\psi \in \mathcal{P}(\Theta, X \mid \Gamma; \Delta)$ is **universal in** $X$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta'; X) \xrightarrow{\sim} \mathcal{P}(\Theta, \Theta' \mid \Gamma; \Delta).$$

- A linear morphism $\psi \in \mathcal{P}(\Theta \mid \Gamma; \Delta, A)$ is **universal in** $A$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta' \mid \Gamma', A; \Delta') \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta \mid \Gamma', \Gamma; \Delta', \Delta).$$

- A linear morphism $\psi \in \mathcal{P}(\Theta \mid \Gamma, A; \Delta)$ is **universal in** $A$ if composing with $\psi$ induces bijections

$$\mathcal{P}(\Theta' \mid \Gamma'; \Delta', A) \xrightarrow{\sim} \mathcal{P}(\Theta', \Theta \mid \Gamma', \Gamma; \Delta', \Delta).$$

A functor is said to **preserve** a certain kind of universal morphism if it takes any such morphism to a similarly universal morphism.

Universal morphisms are unique up to unique isomorphism:

**Proposition 2.9.** If $\psi \in \mathcal{P}(\Theta \mid \Gamma; \Delta, A)$ and $\psi' \in \mathcal{P}(\Theta \mid \Gamma; \Delta, A')$ are universal in $A$ and $A'$ respectively, then there is a unique isomorphism $\phi: A \cong A'$ such that $\phi \circ_A \psi = \psi'$; and similarly for other kinds of universal morphism.

*Proof.* As usual, $\phi$ is determined by applying the universal property of $\psi$ to $\psi'$, and conversely for its inverse. $\square$

We now explore the most important cases of universality, starting with versions of the polycategorical representability conditions from [CS97, BZ20]. For clarity and conciseness, we indicate the object in which a universal morphism is universal by underlining it, e.g. $\psi \in \mathcal{P}(\Theta \mid \Gamma, \underline{A}; \Delta)$.

**Definition 2.10.** Let $A, B$ be linear objects in an LNL polycategory $\mathcal{P}$.

- A **tensor product** of $A, B$ is a universal morphism $\psi \in \mathcal{P}(\mid A, B; \underline{A \otimes B})$.

- A **cotensor product** of $A, B$ is a universal morphism $\psi \in \mathcal{P}(\mid \underline{A \otimes B}; A, B)$.

- A **unit** $\mathbb{1}$ is a universal morphism $\psi \in \mathcal{P}(\mid; \mathbb{1})$.

- A **counit** $\perp$ is a universal morphism $\psi \in \mathcal{P}(\mid \perp;)$.

- A **dual** of $A$ is a universal morphism $\psi \in \mathcal{P}(\mid A, \underline{A^*};)$.

We say that $\mathcal{P}$ "has $\otimes$" if any $A, B$ have a tensor product, and so on.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:9

A dual is equivalently a universal morphism $\psi \in \mathcal{P}(|; A, \underline{A}^*)$; see e.g. [BZ20].

These universal properties specialize in the case $\Theta = \emptyset$ to the like-named ones in the symmetric polycategory $\mathcal{P}^{\mathrm{L}}$. Thus, as shown in [CS97, BZ20], if an LNL polycategory has all $\otimes, \Im, \mathbb{1}, \perp$ then $\mathcal{P}^{\mathrm{L}}$ is a **linearly distributive category**, and if it also has all $(\cdot)^*$ then $\mathcal{P}^{\mathrm{L}}$ is **\*-autonomous** [Bar79, Bar91, CS97].

We similarly have tensors and units of *nonlinear* objects, but these turn out to coincide with cartesian *products*, by the following folklore analogue of the equivalence between positive and negative presentations of product types in structural logic.

**Proposition 2.11.** *The following are equivalent for objects $X, Y$ and $X \times Y$ of an LNL polycategory.*

(i) *There is a universal morphism $\psi \in \mathcal{P}(X, Y; \underline{X \times Y})$. In other words, composing with $\psi$ induces bijections*

$$\begin{aligned} \mathcal{P}(\Theta, X \times Y; Z) &\xrightarrow{\sim} \mathcal{P}(\Theta, X, Y; Z) \\ \mathcal{P}(\Theta, X \times Y \mid \Gamma; \Delta) &\xrightarrow{\sim} \mathcal{P}(\Theta, X, Y \mid \Gamma; \Delta). \end{aligned}$$

(ii) *There is a morphism $\psi \in \mathcal{P}(X, Y; X \times Y)$ inducing bijections*

$$\mathcal{P}(\Theta, X \times Y; Z) \xrightarrow{\sim} \mathcal{P}(\Theta, X, Y; Z)$$

(iii) *There are $\pi_1 \in \mathcal{P}(X \times Y; X)$ and $\pi_2 \in \mathcal{P}(X \times Y; Y)$ inducing bijections*

$$\mathcal{P}(\Theta; X \times Y) \xrightarrow{\sim} \mathcal{P}(\Theta; X) \times \mathcal{P}(\Theta; Y).$$

(iv) *There are morphisms $\psi \in \mathcal{P}(X, Y; X \times Y)$ and $\pi_1 \in \mathcal{P}(X \times Y; X)$ and $\pi_2 \in \mathcal{P}(X \times Y; Y)$ such that the composites*

$$\begin{aligned} (X, Y) \xrightarrow{\psi} X \times Y \xrightarrow{\pi_1} X & (X, Y) \xrightarrow{\psi} X \times Y \xrightarrow{\pi_2} Y \\ (X \times Y, X \times Y) \xrightarrow{(\pi_1, \pi_2)} (X, Y) \xrightarrow{\psi} X \times Y \end{aligned}$$

*are the image of identities under structural maps.*

*Proof.* Of course (i) implies (ii), so it suffices to prove that (ii) and (iii) each imply (iv) and that (iv) implies (i) and (iii).

Assuming (ii), let $\pi_1: X \times Y \to X$ be the image of $1_X$ under the composite

$$\mathcal{P}(X; X) \to \mathcal{P}(X, Y; X) \xrightarrow{\sim} \mathcal{P}(X \times Y; X),$$

of a structural map and the universal property of (ii), and similarly for $\pi_2$. The equations in (iv) hold by the universal property.

Assuming (iii), $\psi: (X, Y) \to X \times Y$ is the image of $(1_X, 1_Y)$ under the composite

$$\mathcal{P}(X; X) \times \mathcal{P}(Y; Y) \to \mathcal{P}(X, Y; X) \times \mathcal{P}(X, Y; Y) \to \mathcal{P}(X, Y; X \times Y)$$

of structural maps with the universal property of (iii). Again, the equations in (iv) hold by the universal property.

Conversely, assuming (iv), the right-to-left directions of (i) are composing with $(\pi_1, \pi_2)$ and a structural map, while the right-to-left direction of (iii) is composing with $\psi$ and a structural map. These are inverses by the equations in (iv). $\square$

1:10

M. SHULMAN

Vol. 19:2

We will refer to such an $X \times Y$ as a **product** of $X$ and $Y$. There is an analogue for nullary products and terminal nonlinear objects, denoted 1 (not to be confused with the linear $\mathbb{1}$). By Proposition 2.11(iii), if all $\times, 1$ exist then $\mathcal{P}^{\mathrm{NL}}$ is a **cartesian monoidal category**. Note that these are essentially facts about cartesian multicategories, which extend automatically to an LNL polycategory $\mathcal{P}$ from $\mathcal{P}^{\mathrm{NL}}$.

**Corollary 2.12.** *Any functor of LNL polycategories preserves nonlinear products and terminal objects.*

*Proof.* The equations in Proposition 2.11(iv) are preserved by any functor. $\square$

**Remark 2.13.** If we changed notation as suggested in Remark 2.7 to regard the nonlinear objects (or the “right-hand” ones) as instead forming a co-cartesian co-multicategory, then the identical operations $\times$ and 1 would instead behave like a coproduct and an initial object (and hence would be better denoted $+$ and $\varnothing$).

We now consider the **exponential modalities** (a.k.a. **storage modalities**) that relate linear and nonlinear objects.

**Definition 2.14.** Let $X$ be a nonlinear object and $A$ a linear one.

- An **F-modality** is a universal morphism $\psi \in \mathcal{P}(X \mid \mathsf{FX})$.
- A **U-modality** is a universal morphism $\psi \in \mathcal{P}(\underline{\mathsf{UA}} \mid \mathsf{A})$.
- An $\mathsf{\perp}$-**modality** is a universal morphism $\psi \in \mathcal{P}(X \mid \mathsf{\perp}X;)$.
- A $\mathsf{\cap}$-**modality** is a universal morphism $\psi \in \mathcal{P}(\underline{\mathsf{UA}} \mid A;)$.

Thus, the exponential modalities are characterized by natural bijections

$$\begin{aligned} \mathcal{P}(\Theta, X \mid \Gamma; \Delta) &\cong \mathcal{P}(\Theta \mid \Gamma, \mathsf{FX}; \Delta) & \mathcal{P}(\Theta \mid \mathsf{A}) &\cong \mathcal{P}(\Theta; \mathsf{UA}) \\ \mathcal{P}(\Theta, X \mid \Gamma; \Delta) &\cong \mathcal{P}(\Theta \mid \Gamma; \Delta, \mathsf{\perp}X) & \mathcal{P}(\Theta \mid A;) &\cong \mathcal{P}(\Theta; \mathsf{\cap}A). \end{aligned}$$

Note that $\mathsf{F}$ and $\mathsf{U}$ are covariant, while $\mathsf{\perp}$ and $\mathsf{\cap}$ are contravariant. We will see below that these are adjoint in pairs, $\mathsf{F} \dashv \mathsf{U}$ and $\mathsf{\cap} \dashv \mathsf{\perp}$, and induce the usual comonad $! = \mathsf{FU}$ and monad $? = \mathsf{\perp}\mathsf{\cap}$.

We can also consider internal-homs of various sorts.

**Definition 2.15.** Let $X, Y$ be nonlinear objects and $A, B$ be linear objects.

- A **linear hom** is a universal morphism $\psi \in \mathcal{P}(\mid A \multimap B, A; B)$.
- A **linear co-hom** is a universal morphism $\psi \in \mathcal{P}(\mid B; B \triangleleft A, A)$.
- A **nonlinear hom** is a universal morphism $\psi \in \mathcal{P}(X \multimap Y, X; Y)$.
- A **mixed hom** is one of the following:$^3$
  - a universal morphism $\psi \in \mathcal{P}(X \mid X \multimap B; B)$.
  - a universal morphism $\psi \in \mathcal{P}(A \multimap B \mid A; B)$.
  - a universal morphism $\psi \in \mathcal{P}(X \multimap B, X \mid \mathsf{B})$.

$^3$As notational mnemonics, the arrowhead in $\to, \to, \to$ indicates the domain object is nonlinear, the open circle in $\multimap, \to$ indicates the codomain object and hom-object are both linear, and the closed circle in $\to, \to$ indicates the codomain object is linear but the hom-object is nonlinear.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:11

Thus, these various kinds of homs are characterized by bijections

$$\mathcal{P}(\Theta \mid \Gamma, A; \Delta, B) \cong \mathcal{P}(\Theta \mid \Gamma; \Delta, A \multimap B)$$

$$\mathcal{P}(\Theta \mid \Gamma, B; \Delta, A) \cong \mathcal{P}(\Theta \mid \Gamma, B \triangleleft A; \Delta)$$

$$\mathcal{P}(\Theta, X; Y) \cong \mathcal{P}(\Theta; X \to Y)$$

$$\mathcal{P}(\Theta, X \mid \Gamma; \Delta, B) \cong \mathcal{P}(\Theta \mid \Gamma; \Delta, X \multimap B)$$

$$\mathcal{P}(\Theta \mid A; B) \cong \mathcal{P}(\Theta; A \multimap B)$$

$$\mathcal{P}(\Theta, X \mid ; B) \cong \mathcal{P}(\Theta; X \multimap B).$$

In particular:

- If $\otimes, \mathbb{1}, \multimap$ exist then the monoidal structure $\otimes$ on $\mathcal{P}^{\mathrm{L}}$ is closed.
- If $\mathfrak{A}, \bot, \triangleleft$ exist then the monoidal structure $\mathfrak{A}$ on $\mathcal{P}^{\mathrm{L}}$ is coclosed.
- If $\times, 1, \to$ exist then $\mathcal{P}^{\mathrm{NL}}$ is cartesian closed.

The mixed homs suggest analogous **mixed tensor products**, such as universal morphisms $\psi \in \mathcal{P}(X \mid A; \underline{X \rtimes A})$, or $\psi \in \mathcal{P}(X, Y \mid ; \underline{X \boxtimes Y})$. However, lest we start to feel the zoo of universal properties is too large, we note that the more exotic sorts can be constructed from the simpler ones in the following sense.

**Proposition 2.16.** *If $\psi$ is universal in $R$, while $\phi$ contains $R$ in its domain or codomain and is universal in a different object $S$, then $\psi \circ_R \phi$ is universal in $S$.*

*Proof.* There are a number of different versions of this statement depending on the types of $R, S, \psi, \phi$ and whether the objects occur in domain or codomain, but they all reduce to "the composite of bijections is a bijection". See Proposition 4.10 for a more rigorous proof. $\square$

One instance of this is the associativity of tensors: given universal morphisms

$$\psi_1 \in \mathcal{P}(\mid A, B; \underline{A \otimes B}) \quad \psi_3 \in \mathcal{P}(\mid A \otimes B, C; \underline{(A \otimes B) \otimes C})$$

$$\psi_2 \in \mathcal{P}(\mid B, C; \underline{B \otimes C}) \quad \psi_4 \in \mathcal{P}(\mid A, B \otimes C; \underline{A \otimes (B \otimes C)})$$

the two composites

$$\psi_3 \circ_{A \otimes B} \psi_1 \in \mathcal{P}(\mid A, B, C; \underline{(A \otimes B) \otimes C})$$

$$\psi_4 \circ_{B \otimes C} \psi_2 \in \mathcal{P}(\mid A, B, C; \underline{A \otimes (B \otimes C)})$$

are both universal, hence by Proposition 2.9 there is an induced isomorphism

$$(A \otimes B) \otimes C \cong A \otimes (B \otimes C).$$

This is how $(\otimes, \mathbb{1})$ is shown to be a monoidal structure, and similarly for $(\mathfrak{A}, \bot)$ and (if we like) $(\times, 1)$.

Another familiar instance is that in a $*$-autonomous category, linear homs can be defined in terms of duals and cotensors if these exist. Given universal morphisms

$$\psi_1 \in \mathcal{P}(\mid \underline{A^*}, A;) \quad \psi_2 \in \mathcal{P}(\mid \underline{A^* \mathfrak{A} B}; A^*, B)$$

their composite $\psi_1 \circ_{A^*} \psi_2 \in \mathcal{P}(\mid \underline{A^* \mathfrak{A} B}, A; B)$ is universal in $A^* \mathfrak{A} B$, exhibiting it as $A \multimap B$. Similarly, we have $B \triangleleft A = A^* \otimes B$, and De Morgan duality:

$$A \mathfrak{A} B = (A^* \otimes B^*)^* \quad \bot = \mathbb{1}^* \quad \nexists X = (\mathsf{F}X)^* \quad \cap A = \mathsf{U}(A^*)$$

1:12

M. SHULMAN

Vol. 19:2

In particular, $\mathcal{P}^{\mathrm{L}}$ is $*$-autonomous as soon as $\mathcal{P}$ has $\otimes, \mathbb{1}, (\cdot)^{*}$. And as in a $*$-autonomous category, duals can be constructed by homming into the counit:

$$A^{*} = A \multimap \bot.$$

Less familiar instances of Proposition 2.16 relate the modalities to the tensors and homs, particularly the mixed ones: we have

$$\begin{array}{l} X \multimap B = \mathsf{F}X \multimap B \quad X \rtimes A = \mathsf{F}X \otimes A \\ A \multimap B = \mathsf{U}(A \multimap B) \quad X \boxtimes Y = \mathsf{F}(X \times Y) \\ X \multimap B = \mathsf{U}(\mathsf{F}X \multimap B) \quad X \boxtimes Y = \mathsf{F}X \otimes \mathsf{F}Y \\ X \multimap B = X \to \mathsf{U}B \quad \mathbb{1} = \mathsf{F}1 \\ \mathsf{U}A = \mathbb{1} \multimap A \quad \mathsf{F}X = X \rtimes \mathbb{1} \\ \mathsf{U}A = 1 \multimap A \quad \mathsf{F}X = X \boxtimes 1 \end{array}$$

whenever all the operations on the right-hand side exist. In particular, since both $\mathsf{F}(X \times Y)$ and $\mathsf{F}X \otimes \mathsf{F}Y$ have the universal property of $X \boxtimes Y$, they are isomorphic if they both exist. (This is, of course, closely related to Seely's characterization of the modality $!$; see Remark 3.6.) Thus, if $\otimes, \mathbb{1}, \times, 1, \mathsf{F}$ exist then $\mathsf{F}$ is a strong monoidal functor. Similarly, if both $\mathsf{U}(\mathsf{F}X \multimap B)$ and $X \to \mathsf{U}B$ exist they are isomorphic (which is related to Girard's embedding of nonlinear logic in linear logic); if $\lrcorner(X \times Y)$ and $\lrcorner X \rtimes \lrcorner Y$ exist they are isomorphic; and so on.

**Remark 2.17.** As a trivial instance, a unary co-unary linear morphism, i.e. one of the form $\psi \in \mathcal{P}(\mid A; B)$, is universal if and only if it is an isomorphism (and similarly in the nonlinear case). Thus, Proposition 2.16 also implies that universal morphisms are stable under composition with isomorphisms, conversely to Proposition 2.9.

We can also consider limits and colimits in LNL polycategories. In general, we require a **limit** of a diagram of linear or nonlinear objects (and unary co-unary morphisms) to induce bijections on all hom-sets where it appears in the codomain, and similarly for a **colimit** whenever it appears in the domain. (In the case of products and coproducts, this definition appears in [Pas04].) The simplest case of this is that a limit of nonlinear objects satisfies

$$\mathcal{P}(\Theta; \lim_i X_i) \cong \lim_i \mathcal{P}(\Theta; X_i), \tag{2.1}$$

generalizing Proposition 2.11(iii) and reducing to an ordinary limit in the cartesian monoidal $\mathcal{P}^{\mathrm{NL}}$ if $\times, 1$ exist. However, a colimit of nonlinear objects satisfies both

$$\mathcal{P}(\Theta, \operatorname{colim}_i X_i; Y) \cong \lim_i \mathcal{P}(\Theta, X_i; Y) \tag{2.2}$$

$$\mathcal{P}(\Theta, \operatorname{colim}_i X_i \mid \Gamma; \Delta) \cong \lim_i \mathcal{P}(\Theta, X_i \mid \Gamma; \Delta) \tag{2.3}$$

induced by the same universal cocone. This implies that the colimit is

- (i) preserved in each variable by $\times$, insofar as $\times$ exists;
- (ii) sent by $\mathsf{F}$ to a colimit in $\mathcal{P}^{\mathrm{L}}$ that is preserved in each variable by $\otimes$, insofar as $\mathsf{F}, \otimes$ exist; and
- (iii) sent by $\lrcorner$ to a limit in $\mathcal{P}^{\mathrm{L}}$ that is preserved in each variable by $\Re$, insofar as $\lrcorner, \Re$ exist.

Moreover, if all $\times, \mathsf{F}, \lrcorner, \otimes, \Re$ exist, then a colimit in the ordinary category $\mathcal{P}^{\mathrm{NL}}$ is a colimit in $\mathcal{P}$ if and only if it is preserved in these ways.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:13

Similarly, a colimit of linear objects satisfies

$$\mathcal{P}(\Theta \mid \Gamma, \operatorname{colim}_i A_i; \Delta) \cong \lim_i \mathcal{P}(\Theta \mid \Gamma, A_i; \Delta) \quad (2.4)$$

which implies that it is preserved by $\otimes$ in each variable and sent by $\cap$ to a limit in $\mathcal{P}^{\mathrm{NL}}$, insofar as $\otimes, \cap$ exist. If all $\otimes, \mathfrak{A}, \bot, \mathsf{F}$ exist, then a colimit in the ordinary category $\mathcal{P}^{\mathrm{L}}$ is a colimit in $\mathcal{P}$ if and only if it is preserved by $\otimes$. Dually, a limit of linear objects satisfies

$$\mathcal{P}(\Theta \mid \Gamma; \Delta, \lim_i A_i) \cong \lim_i \mathcal{P}(\Theta \mid \Gamma; \Delta, A_i) \quad (2.5)$$

which implies that it is preserved by $\mathfrak{A}$ in each variable and sent by $\cup$ to a limit in $\mathcal{P}^{\mathrm{NL}}$, insofar as $\mathfrak{A}, \cup$ exist. And if all $\mathfrak{A}, \otimes, \mathbb{1}, \mathsf{F}$ exist, a colimit in $\mathcal{P}^{\mathrm{L}}$ is a colimit in $\mathcal{P}$ if and only if it is preserved by $\mathfrak{A}$. Note also that $\otimes$ preserves all colimits if $\multimap$ exists, $\mathsf{F}$ preserves all colimits if $\cup$ exists, and so on.

We will write $X+Y$ for the coproduct of nonlinear objects and $\varnothing$ for the initial nonlinear object, and we denote finite products and coproducts of linear objects with Girard's notation for the linear logic additive connectives: $A \& B$ for the product, $A \oplus B$ for the coproduct, $\top$ for the terminal object, and $0$ for the initial object. Thus the above preservation properties state that

$$\begin{array}{ll} X \times (Y+Z) \cong (X \times Y) + (X \times Z) & X \times \varnothing \cong \varnothing \\ \mathsf{F}(X+Y) \cong \mathsf{F}X \oplus \mathsf{F}Y & \mathsf{F}\varnothing \cong 0 \\ \exists(X+Y) \cong \exists X \& \exists Y & \exists\varnothing \cong \top \\ A \otimes (B \oplus C) \cong (A \otimes B) \oplus (A \otimes C) & A \otimes 0 \cong 0 \\ \cap(A \oplus B) \cong \cap A \times \cap B & \cap 0 \cong 1 \\ A\mathfrak{A}(B \& C) \cong (A\mathfrak{A}B) \& (A\mathfrak{A}C) & A\mathfrak{A}\top \cong \top \\ \cup(A \& B) \cong \cup A \times \cup B & \cup\top \cong 1 \end{array}$$

If we specialize the above universal properties to symmetric polycategories, symmetric multicategories, cartesian multicategories, or LNL multicategories, there are three possible results. Some universal properties make sense unmodified, such as $\otimes, \mathfrak{A}$ in polycategories or $\times, \rightarrow$ in cartesian multicategories. Others make no sense at all, such as $\mathfrak{A}, \bot$ in LNL multicategories or $\mathsf{F}, \cup$ in symmetric polycategories.

A third group can only have a restricted universal property. Specifically, limits and colimits in a symmetric multicategory or LNL multicategory can only induce bijections of hom-sets with unary codomain: instead of (2.3)–(2.5) we assert only

$$\begin{array}{ll} \mathcal{P}(\Theta, \operatorname{colim}_i X_i \mid \Gamma; B) & \cong \lim_i \mathcal{P}(\Theta, X_i \mid \Gamma; B) \\ \mathcal{P}(\Theta \mid \Gamma, \operatorname{colim}_i A_i; B) & \cong \lim_i \mathcal{P}(\Theta \mid \Gamma, A_i; B) \\ \mathcal{P}(\Theta \mid \Gamma; \lim_i A_i) & \cong \lim_i \mathcal{P}(\Theta \mid \Gamma; A_i). \end{array}$$

Since the left- and right-hand sides of (2.3)–(2.5) have the same codomain arity, these apparently-weaker universal properties are equivalent to (2.3)–(2.5) for limits and colimits over *nonempty* domain categories. But the limit of the empty diagram of copies of the empty set is no longer empty, so an initial or terminal object in an LNL multicategory $\mathcal{E}$ (in the above sense) need not be initial or terminal in $\mathcal{E}$ *qua* LNL polycategory.

In fact, an LNL multicategory *cannot* have a terminal linear object, or an initial linear or nonlinear object, in the LNL-polycategorical sense. For example, if $\top$ is a terminal linear object, we must have $\mathcal{P}(\Theta \mid \Gamma; \Delta, \top) = 1$ for *all* $\Delta$, whereas in an LNL multicategory we

1:14

M. SHULMAN

Vol. 19:2

|   | Unmodified | Nonsensical | Modified  |
| --- | --- | --- | --- |
|  polycategories | ⊗, 1, 𝒱, ⊥, (·)*, →, ◁, &, ⊕, ⊤, 0 | ×, 1, →, F, U, ⊥, ∩, +, ∅ |   |
|  symm. multi. | ⊗, 1, →, &, ⊕ | 𝒱, ⊥, (·)*, ◁, ×, 1, →, F, U, ⊥, ∩, +, ∅ | ⊤, 0  |
|  cart. multi. | ×, 1, →, +, ∅ | ⊗, 1, 𝒱, ⊥, (·)*, →, ◁, F, U, ⊥, ∩, &, ⊕, ⊤, 0 |   |
|  LNL multi. | ×, 1, →, ⊗, 1, →, &, ⊕, F, U | 𝒱, ⊥, (·)*, ◁, ⊥, ∩ | ⊤, 0  |

TABLE 1. Universal properties in subcategories

have $\mathcal{P}(\Theta \mid \Gamma; \Delta, \top) = \emptyset$ if $|\Delta| > 0$. This is already the case for ordinary multicategories and polycategories.

The categorization of universal properties in these four subcategories into these three groups is shown in Table 1.

### 3. RELATION TO THE LITERATURE

By our observations in Section 2, the following categorical structures can be identified with certain LNL polycategories:

- Symmetric monoidal categories.
- Symmetric monoidal categories with any desired limits, and any desired colimits that are preserved in each variable by the tensor product.
- Closed symmetric monoidal categories, with any desired limits and colimits (the latter automatically preserved by the tensor product, due to closedness).
- Cartesian monoidal categories.
- Cartesian monoidal categories with any desired limits, and any desired colimits that are preserved in each variable by the cartesian product.
- Cartesian closed categories, with any desired limits and colimits.
- Symmetric linearly distributive categories.
- Symmetric linearly distributive categories with any desired colimits that are preserved in each variable by the tensor product, and any desired limits that are preserved in each variable by the cotensor product.
- (Symmetric) *-autonomous categories, with any desired limits and colimits.

The “strong” morphisms between these structures (those that preserve all the asserted categorical structure up to coherent isomorphisms) can also be identified with functors of LNL polycategories that preserve the relevant universal properties, and similarly for the transformations. In other words, the standard 2-categories of the above structures are equivalent to locally full sub-2-categories of LNLPoly.

We now add the modalities, starting with the “intuitionistic” case of LNL multicategories. These are designed to model split-context intuitionistic linear logic syntaxes such as [Ben95, Bar96], without necessarily assuming that any connectives exist. But if enough connectives do exist, they reduce to a better-known notion of model for intuitionistic multiplicative-exponential linear logic:

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:15

**Proposition 3.1.** *An LNL multicategory in which the modality F exists is uniquely determined by a functor of symmetric multicategories*

$$\mathsf{F} : \mathcal{P}^{\mathrm{NL}} \to \mathcal{P}^{\mathrm{L}}$$

*where $\mathcal{P}^{\mathrm{NL}}$ is a cartesian multicategory and $\mathcal{P}^{\mathrm{L}}$ a symmetric one. Moreover:*

- (i) *The modality U also exists if and only if the functor F has a right adjoint (in the 2-category of symmetric multicategories).*
- (ii) *If $\times, 1, \otimes, \mathbb{1}$ exist, then F is equivalently a strong symmetric monoidal functor from a cartesian monoidal category to a symmetric monoidal one.*
- (iii) *Thus, an LNL multicategory with $\times, 1, \otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$ is equivalently an **LNL adjunction** [Ben95, Mel09]: a symmetric monoidal adjunction from a cartesian monoidal category to a symmetric monoidal one.*

*Proof.* Given the modality $\mathsf{F}$, we make it a functor by composing with $(Y \mid) \to \mathsf{F}Y$ and applying its universal property:

$$\mathcal{P}(X_1, \dots, X_n; Y) \to \mathcal{P}(X_1, \dots, X_n \mid ; \mathsf{F}Y) \xrightarrow{\sim} \mathcal{P}(\mid \mathsf{F}X_1, \dots, \mathsf{F}X_n; \mathsf{F}Y).$$

Conversely, given a functor $\mathsf{F}$, we define the general linear hom-sets by

$$\mathcal{P}(X_1, \dots, X_n \mid \Gamma; B) = \mathcal{P}^{\mathrm{L}}(\mathsf{F}X_1, \dots, \mathsf{F}X_n, \Gamma; B).$$

Thus, the universal property of $\mathsf{F}$ holds by definition. Statement (i) is then a multicategorical version of the standard equivalence between adjunctions defined with bijections of hom-sets and with unit and counit. We have already noted (ii), and (iii) follows immediately. $\square$

**Remark 3.2.** Benton [Ben95] assumed $\mathcal{P}^{\mathrm{NL}}$ cartesian *closed* and $\mathcal{P}^{\mathrm{L}}$ symmetric monoidal *closed*, but later authors such as [Mel09] have observed that this is unnecessary for the bare definition. If both categories are closed we will speak of a **closed LNL adjunction**.

Since left adjoints preserve colimits and right adjoints preserve limits, the following structures also form locally full sub-2-categories of LNLPoly:

- LNL adjunctions.
- LNL adjunctions with any desired limits and colimits in either category, such that colimits are preserved by the product or tensor product in each variable.
- Closed LNL adjunctions, with any desired limits and colimits in either category.

The notion of LNL adjunction does depend on having both $\otimes$ and $\times$, whereas LNL multicategories can specify the correct behavior of $\mathsf{F}$ and $\mathsf{U}$ even if $\otimes, \times$ may not exist. As evidence for this correctness, we note that $\times, 1$ are not necessary for the induced comonad on $\mathcal{P}^{\mathrm{L}}$ to coincide with a structure also existing in the literature.

**Proposition 3.3.** *If $\mathcal{P}$ is an LNL multicategory with $\otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$, the symmetric monoidal category $\mathcal{P}^{\mathrm{L}}$ admits a **linear exponential comonad** [BBdPH92, HS03], i.e. it is a **linear category** in the sense of [Ben95].*

*Proof.* Let $!$ be the comonad $\mathsf{FU}$. To give the map $!A \otimes !B \to !(A \otimes B)$, we act on the $\otimes$-universal morphism $(\mid A, B) \to A \otimes B$ as follows. The two noninvertible maps are composition with the U-universal morphisms $(\mathsf{U}A \mid) \to A$ and $(\mathsf{U}B \mid) \to B$ and with the

1:16

M. SHULMAN

Vol. 19:2

F-universal morphism $(\mathsf{U}(A \otimes B) \mid) \to \mathsf{FU}(A \otimes B)$:

$$\begin{aligned} \mathcal{P}(\mid A, B; A \otimes B) &\to \mathcal{P}(\mathsf{U}A, \mathsf{U}B \mid; A \otimes B) \\ &\xrightarrow{\sim} \mathcal{P}(\mathsf{U}A, \mathsf{U}B; \mathsf{U}(A \otimes B)) \\ &\to \mathcal{P}(\mathsf{U}A, \mathsf{U}B \mid; \mathsf{FU}(A \otimes B)) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \mathsf{FU}A, \mathsf{FU}B; \mathsf{FU}(A \otimes B)) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \mathsf{FU}A \otimes \mathsf{FU}B; \mathsf{FU}(A \otimes B)). \end{aligned}$$

Similarly, to give the map $\mathsf{I}A \to \mathsf{I}A \otimes \mathsf{I}A$ we act on the $\otimes$-universal morphism $(\mathsf{I}A, \mathsf{I}A) \to \mathsf{I}A \otimes \mathsf{I}A$ as follows. The two noninvertible maps are composition with the F-universal morphism $(\mathsf{U}A \mid) \to \mathsf{FU}A = \mathsf{I}A$ and a structural map.

$$\begin{aligned} \mathcal{P}(\mid \mathsf{I}A, \mathsf{I}A; \mathsf{I}A \otimes \mathsf{I}A) &= \mathcal{P}(\mid \mathsf{FU}A, \mathsf{FU}A; \mathsf{I}A \otimes \mathsf{I}A) \\ &\to \mathcal{P}(\mathsf{U}A, \mathsf{U}A \mid; \mathsf{I}A \otimes \mathsf{I}A) \\ &\to \mathcal{P}(\mathsf{U}A \mid; \mathsf{I}A \otimes \mathsf{I}A) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \mathsf{FU}A; \mathsf{I}A \otimes \mathsf{I}A). \end{aligned}$$

The nullary cases are similar, and the axioms follow by universal properties.

This implication for LNL adjunctions was observed in [Ben95, §2.2.1]; LNL multicategories give a way to state and prove it even in the absence of $\times, 1$. Conversely:

**Proposition 3.4.** *The Eilenberg–Moore adjunction of any linear exponential comonad $\mathsf{I}$ determines an LNL multicategory with $\times, 1, \otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$, whose underlying linear exponential comonad recovers the given $\mathsf{I}$.*

*Proof.* Such an Eilenberg–Moore adjunction is an LNL adjunction (see [Ben95, §2.2.2] and [Mel09, §7]), hence an LNL multicategory with $\times, 1, \otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$.

Moreover, since *any subset of objects of a multicategory determines a sub-multicategory* (in stark contrast to the situation for monoidal categories), we still obtain an LNL multicategory with $\otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$ if we restrict to any subset of the $\mathsf{I}$-coalgebras containing the cofree ones. The smallest choice, of course, consists of exactly the cofree coalgebras, so we have:

**Corollary 3.5.** *The Kleisli adjunction of any linear exponential comonad $\mathsf{I}$ determines an LNL multicategory with $\otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$, whose underlying linear exponential comonad recovers the given $\mathsf{I}$.*

**Remark 3.6.** To include the Kleisli adjunction in the case when both categories are required to be monoidal, one has to assume that cofree coalgebras are closed under products. This follows for instance if the original monoidal category has products [Ben95, §2.2.3], in which case we recover the notion of **Seely comonad**, characterized by $\mathsf{I}A \otimes \mathsf{I}B \cong \mathsf{I}(A \& B)$. But LNL polycategories allow us to include the Kleisli case even when $\mathsf{I}$ doesn't exist.

There are also intermediate choices between the Eilenberg–Moore category (all coalgebras) and Kleisli category (cofree coalgebras), such as the category of finite products of cofree coalgebras (if $\mathcal{L}$ has finite products), or category of exponentiable coalgebras (if $\mathcal{L}$ is closed monoidal), as discussed in [Ben95, §2.2.2].

Here is another situation that LNL polycategories allow us to treat more generally.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:17

Example 3.7. Let $\mathcal{E}$ be a symmetric multicategory; we can enhance it to an LNL multicategory with $\mathsf{F}$ by taking the nonlinear objects to be the commutative comonoids in $\mathcal{E}$. It may not be immediately obvious how to define a comonoid in a multicategory that lacks $\otimes$, but it is possible: $C$ is a comonoid when it is equipped with operations

$$\mathcal{E}(\Theta_1, C, C, \Theta_2; B) \to \mathcal{E}(\Theta_1, C, \Theta_2; B)$$

$$\mathcal{E}(\Theta_1, \Theta_2; B) \to \mathcal{E}(\Theta_1, C, \Theta_2; B)$$

that are associative, unital, and appropriately natural and equivariant. Such cocommutative comonoids form a cartesian multicategory with a forgetful multicategory functor to $\mathcal{E}$, so by Proposition 3.1 it yields an LNL multicategory.

If $\mathcal{E}$ is symmetric monoidal, then cocommutative comonoids form a cartesian monoidal category, so this LNL multicategory has $\times, 1, \otimes, \mathbb{1}, \mathsf{F}$. Thus, if $\mathsf{F}$ has a right adjoint $\mathsf{U}$, i.e. if cofree cocommutative comonoids exist, then it is an LNL adjunction, known as a Lafont category [Laf88] or a free exponential modality [MTT18]. But we get an LNL multicategory even without these assumptions.

In general, given a category with a linear exponential comonad, we prefer to regard it as an LNL multicategory via the Kleisli construction rather than the Eilenberg–Moore construction. The reason for this is the following folklore observation, showing that Kleisli adjunctions can be detected by a purely intrinsic condition:

Lemma 3.8. An adjunction $F: \mathcal{A} \rightleftarrows \mathcal{B}: G$ is equivalent to the Kleisli adjunction of the monad $GF$ if and only if its left adjoint $F$ is essentially surjective on objects, and isomorphic to that Kleisli adjunction if and only if $F$ is bijective on objects.

Proof. The “only if” direction is clear, so suppose $F$ is essentially surjective on objects, and let $F_T: \mathcal{A} \rightleftarrows \mathcal{A}_T: G_T$ be the Kleisli adjunction of the monad $T = GF$. Thus the objects of $\mathcal{A}_T$ are formal copies “$A_T$” of the objects $A \in \mathcal{A}$, with $\mathcal{A}_T(A_T, B_T) = \mathcal{A}(A, TB)$. There is a unique comparison functor $H: \mathcal{A}_T \to \mathcal{B}$ defined by $H(A_T) = FA$, which is essentially surjective on objects since $F$ is (and bijective on objects if $F$ is). But it is also fully faithful, since $\mathcal{B}(FA, FB) \cong \mathcal{A}(A, GFB) = \mathcal{A}(A, TB) = \mathcal{A}_T(A_T, B_T)$; hence it is an equivalence.

Thus, applying the Kleisli construction, we have the following locally full sub-2-categories of LNLPoly:

- Symmetric monoidal categories with linear exponential comonad. This includes Seely comonads (if the category has finite products) and Lafont comonads (if cofree cocommutative comonoids exist).
- Symmetric monoidal categories with linear exponential comonad and any desired limits and any desired colimits preserved by the tensor product in each variable.
- Closed symmetric monoidal categories with linear exponential comonad and any desired limits and colimits.

In each case the “strong” morphisms, corresponding to functors of LNL multicategories that preserve (among other things) the exponential modalities $\mathsf{F}, \mathsf{U}$, are those that preserve the comonad up to coherent isomorphism: $F(!A) \cong !(FA)$.

Note that all of these LNL polycategories have the following property.

Definition 3.9. An LNL polycategory is of Kleisli type if it is equipped with a choice of $\mathsf{U}$ that is bijective on objects.

1:18

M. SHULMAN

Vol. 19:2

LNL multicategories of Kleisli type correspond to syntaxes for intuitionistic linear logic that have only one class of type, such as [Bar96, Has05], rather than two syntactic classes for “linear types” and “nonlinear types”.

Example 3.10. We conjecture that the Linear Non-Linear multicategories suggested by [HT21] are equivalent to LNL multicategories of Kleisli type. In addition, the IL-indexed categories of [MdPR00] are equivalent to LNL multicategories of Kleisli type having ⊗, 1, &, ⊤, →, and → (our → being written “→”).

We can also attempt to induce an LNL multicategory from a monad on a cartesian monoidal category or multicategory. In fact this is quite easy: the 2-category of symmetric multicategories has Eilenberg–Moore objects, so any monad T therein on a multicategory E induces an adjunction of multicategories  \( E \rightleftharpoons E^{T} \) . If E is cartesian, by Proposition 3.1 this yields an LNL multicategory with F, U. The interesting thing is that if E is representable, hence a (cartesian) monoidal category, then a symmetric-multicategory-monad on it is the same as a lax symmetric monoidal monad, and hence by [Koc72] the same as a commutative strong monad.

Proposition 3.11. Any commutative strong monad T on a cartesian monoidal category E induces an LNL multicategory P having F, U, ×, 1, 1, where  \( P^{NL} = E \)  and the  \( P^{L} \)  is the symmetric multicategory of T-algebras. Moreover:

(i) If \(\mathcal{E}\) is cartesian closed with equalizers, then \(\mathcal{P}\) has \(\rightarrow\), \(\rightharpoonup\).
(ii) If \(\mathcal{E}\) and \(T\) are such that the category of \(T\)-algebras has coequalizers (e.g. \(\mathcal{E}\) is locally presentable and \(T\) is accessible, or \(\mathcal{E}\) is cartesian closed with reflexive coequalizers preserved by \(T\)) then \(\mathcal{P}\) also has \(\otimes\), and thus is an LNL adjunction.

Proof. We have already observed the first statement, except for noting that  \( 1 = T1 \) . Statements (i) and (ii) follow by results in the literature [Koc71, Sea13]. ☐

Of course, we can also restrict to any full sub-multicategory of the Eilenberg–Moore category, such as the Kleisli category, and still have an LNL multicategory. As in the comonad case, when given a commutative strong monad on a cartesian monoidal category we generally regard it as an LNL multicategory via the Kleisli construction; thus we have the following locally full sub-2-categories of LNLPoly:

- Cartesian monoidal categories with a commutative strong monad.
- Cartesian monoidal categories with a commutative strong monad and any desired limits and any desired colimits preserved by the product in each variable.
- Cartesian closed categories with a commutative strong monad and any desired limits and colimits.

A non-commutative monad T on a cartesian monoidal category E does not induce a multicategory structure on its Eilenberg–Moore category  \( E^{T} \) . However, as long as T is a strong monad, we can still combine E with  \( E^{T} \)  to produce an LNL multicategory, albeit a rather degenerate one. Specifically, if A and B are T-algebras and X is an object of E, we can define an X-indexed family of algebra maps  \( A \to B \)  to be a morphism  \( f : X \times A \to B \)  such that the following diagram commutes:

\[
\begin{array}{c} X \times T A \longrightarrow T (X \times A) \xrightarrow {T f} T B \\ \Big \downarrow \\ X \times A \xrightarrow [ f ]{} B \end{array}
\]

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:19

in which the map $X \times TA \rightarrow T(X \times A)$ is the monad strength.

**Proposition 3.12.** *Any strong monad $T$ on a cartesian monoidal category $\mathcal{E}$ induces an LNL multicategory $\mathcal{P}$ with $\mathcal{P}^{\mathrm{NL}} = \mathcal{E}$, whose linear objects are the $T$-algebras, with*

$$\begin{aligned} \mathcal{P}(\Theta \mid ; A) &= \mathcal{E}(\Theta; A) \\ \mathcal{P}(\Theta \mid A; B) &= \{(\times \Theta)\text{-indexed families of algebra maps } A \rightarrow B\} \end{aligned}$$

*and all other linear homsets empty.*

(Here by $\times \Theta$ we mean the cartesian product of all the objects in $\Theta$, or the terminal object if $\Theta$ is empty.)

This LNL multicategory is **linearly subunary**, i.e. all its linear morphisms have linear codomain of length 1 (since it is an LNL multicategory) and linear domain of length $\leq 1$. It has $\times, 1, \cup$, and also an $\mathsf{F}$ with a weaker universal property:

$$\mathcal{P}(\Theta, X \mid ; B) \cong \mathcal{P}(\Theta \mid \mathsf{F}X; B). \tag{3.1}$$

This is similar to the restriction on $\top, 0$ in multicategories from Section 2. It implies there is a $\mathbb{1}$ (namely $\mathsf{F}1$) with a similarly restricted universal property. Conversely, from $\times$ and a restricted $\mathbb{1}$, we can construct a restricted $\mathsf{F}$ as $\mathsf{F}X = X \times \mathbb{1}$.

These LNL multicategories provide semantics for “call-by-push-value” [Lev03] and related theories. In this case, they are usually described as *enriched adjunctions*, analogously to the definition of LNL adjunctions as *monoidal* adjunctions. To explain this, recall that if $\mathcal{E}$ is cartesian monoidal, its Yoneda embedding $\mathcal{E} \hookrightarrow [\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$ is fully faithful and preserves products; thus any $\mathcal{E}$-enriched category can be regarded as an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched one. In addition, $\mathcal{E}$ itself is always $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched, with hom-presheaves $\underline{\mathcal{E}}(A, B)(X) = \mathcal{E}(X \times A, B)$.

**Proposition 3.13.** *A linearly subunary LNL multicategory with $\times, 1$ is uniquely determined by a **CBPV pre-structure** [Lev03]: a cartesian monoidal category $\mathcal{E}$, a category $\mathcal{L}$ enriched over $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$, and an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched functor $R : \mathcal{L} \rightarrow [\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$. Moreover:*

- (i) *The modality $\cup$ exists if and only if $R$ lands inside $\mathcal{E}$.*
- (ii) *If $\cup$ exists, then $\mathsf{F}$ exists with restricted universal property (3.1) if and only if $R : \mathcal{L} \rightarrow \mathcal{E}$ has an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched left adjoint.*
- (iii) *The hom-objects of $\mathcal{L}$ lie in $\mathcal{E}$ if and only if $\rightarrow$ exists.*
- (iv) *$\mathcal{L}$ has $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched powers by representables if and only if $\rightarrow$ exists.*
- (v) *$\mathcal{L}$ has $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched copowers by representables if and only if $\times$ exists.*
- (vi) *$\mathcal{L}$ has $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched finite products if and only if $\mathcal{&}, \top$ exist with a restricted universal property respecting the arity restrictions.*
- (vii) *$\mathcal{E}$ is distributive [CLW93] and the hom-presheaves of $\mathcal{L}$ preserve finite coproducts if and only if $+, \emptyset$ exist with a restricted universal property.*

*Proof.* Of course, $\mathcal{E}$ corresponds to $\mathcal{P}^{\mathrm{NL}}$, which is cartesian monoidal if and only if $\times, 1$ exist. The arity restrictions then ensure that the linear hom-sets are uniquely determined by those of the form $\mathcal{P}(X \mid A; B)$ and $\mathcal{P}(X \mid ; B)$. The former assemble into an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched category $\mathcal{L}$, and the latter into the functor $R$.

To say that $R$ lands in $\mathcal{E}$ is to say that each functor $X \mapsto \mathcal{P}(X \mid ; B)$ is representable, which is to say that $\cup$ exists. Given this, (3.1) says exactly that $\mathsf{F}$ is an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched left adjoint of $\cup$. The other claims follow by similar comparisons of universal properties. $\square$

1:20

M. SHULMAN

Vol. 19:2

**Corollary 3.14.** *A linearly subunary LNL multicategory with ×, 1, ∪, →, →, ×, and restricted F (or equivalently 1) is equivalent to a cartesian monoidal category E, a E-enriched category L with powers and copowers, and an object 1 ∈ L.*

*Proof.* Proposition 3.13 implies exactly this characterization except that instead of 1 we have a E-enriched adjunction F : E ⇔ L : ∪. But this is uniquely determined by F1 ≅ 1, since FX ≅ X × 1 and UA ≅ 1 → A.

As before, the arity restrictions can be enforced by slicing: if CBPV ∈ LNLPoly is the subterminal with one nonlinear object, one linear object, all nonlinear homsets and co-unary subunary linear homsets singletons, and others empty, then the linearly subunary LNL multicategories constitute the slice LNLPoly/CBPV. By adding appropriate combinations of universal properties, we obtain various related structures in the literature. Thus we have the following locally full sub-2-categories of LNLPoly:

- CBPV pre-structures, as in Proposition 3.13.
- **CBPV adjunction models** or **EC+ models** [EMS12], which are CBPV pre-structures having ∪, →, and F, +, ∅, &, ⊤ with restricted universal properties.
- **EEC+ models** [EMS12], which are EC+ models having also →, →, × as well as ⊕, 0 with restricted universal properties. Thus they are structures as in Corollary 3.14 where E and L both have finite products and coproducts.
- **MLJₚⁿ models** [CFMM16], which are CBPV pre-structures having only ∪, →, and restricted F.
- **LJₚⁿ models**, which are MLJₚⁿ models having also restricted +, ∅, &, ⊤.
- **ECBV models** [MS14], which are linearly *unary* LNL multicategories (that is, all linear morphisms have linear domain *and* codomain of length exactly 1) having ×, 1, →, ×, but no F or ∪. Of course, this arity restriction is given by slicing over a different object ECBV.

We now consider the “classical” case: LNL polycategories that are not co-unary.

**Proposition 3.15.** *An LNL polycategory in which the modality F exists is uniquely determined by a functor of symmetric multicategories*

$$\mathsf{F} : \mathcal{P}^{\mathrm{NL}} \to \mathrm{SYMMULTI}^*(\mathcal{P}^{\mathrm{L}})$$

where $\mathcal{P}^{\mathrm{NL}}$ is a cartesian multicategory, $\mathcal{P}^{\mathrm{L}}$ a symmetric polycategory, and SYMMULTI* denotes the underlying symmetric multicategory of a symmetric polycategory. Also:

(i) *The modality ∪ also exists if and only if the functor F has a right adjoint*

$$\mathrm{SYMMULTI}^*(\mathcal{P}^{\mathrm{L}}) \to \mathcal{P}^{\mathrm{NL}}$$

*in the 2-category of symmetric multicategories.*

(ii) *If ×, 1, ⊗, 1, ∇, ⊥ exist, then F is equivalently a strong symmetric monoidal functor from a cartesian monoidal category to (the ⊗ monoidal structure of) a symmetric linearly distributive one.*

(iii) *Thus, an LNL polycategory with ×, 1, ⊗, 1, ∇, ⊥, F, ∪ is equivalently an LNL adjunction M ⇔ L in which L is linearly distributive. Moreover, it also has (·)* if and only if L is *-autonomous.*

*Proof.* As in Proposition 3.1, we make the modality F in an LNL polycategory into a functor using its universal property; while given a functor as above we define the general linear homsets by

$$\mathcal{P}(X_1, \dots, X_n \mid \Gamma; \Delta) = \mathcal{P}^{\mathrm{L}}(\mathsf{F}X_1, \dots, \mathsf{F}X_n, \Gamma; \Delta)$$

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:21

so that the universal property of $\mathsf{F}$ holds by definition. The rest is also similar to Proposition 3.1, using the result of [CS97] that a symmetric polycategory with $\otimes, \mathbb{1}, \mathfrak{A}, \bot$ is equivalently a symmetric linearly distributive category. The universal property of $\mathsf{F}$ relative to linear morphisms with arbitrary codomain ensures that it is uniquely determined by its action on underlying multicategories, while $\mathsf{U}$ knows nothing about the non-co-unary morphisms at all. $\square$

Note that since $\sqcup$ and $\cap$ can be defined in terms of $\mathsf{F}, \mathsf{U}, (\cdot)^*$ by $\sqcup X = (\mathsf{F}X)^*$ and $\cap A = \mathsf{U}(A^*)$, an LNL adjunction with $\mathcal{L}$ *-autonomous also has $\sqcup, \cap$. Thus, we have the following locally full sub-2-categories of LNLPoly:

- **Linearly distributive LNL adjunctions** and **-autonomous LNL adjunctions**, defined as in Proposition 3.15(iii).
- Linearly distributive LNL adjunctions with any desired limits and colimits in either category, subject to the restrictions that colimits must be preserved by the product or tensor product in each variable, and limits in the linearly distributive category must be preserved by the cotensor product in each variable.
- *-autonomous closed LNL adjunctions with any desired limits and colimits in either category.

On the other hand, if we add $\sqcup$ and $\cap$ *without* $(\cdot)^*$, the induced structure on $\mathcal{L}$ is also one that appears in the literature:

**Proposition 3.16.** *If $\mathcal{P}$ is an LNL polycategory with $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{F}, \mathsf{U}, \sqcup, \cap$, then $\mathcal{P}^{\mathsf{L}}$ is a (symmetric) linearly distributive category with storage [BCS96].*

*Proof.* Note that any LNL polycategory $\mathcal{P}$ has an underlying LNL multicategory $\text{LNLMULTI}^*(\mathcal{P})$ containing all the objects, all the nonlinear morphisms, but only the co-unary linear morphisms. It also has a **linear opposite** $\mathcal{P}^{\text{L-op}}$ in which the nonlinear morphisms are the same, but $\mathcal{P}^{\text{L-op}}(\Theta \mid \Gamma; \Delta) = \mathcal{P}(\Theta \mid \Delta; \Gamma)$.

Thus, applying Proposition 3.3 to $\text{LNLMULTI}^*(\mathcal{P})$ and $\text{LNLMULTI}^*(\mathcal{P}^{\text{L-op}})$, we obtain a linear exponential comonad $! = \mathsf{FU}$ and a linear exponential monad $? = \sqcup, \cap$, so it remains only to show that $?$ is a $!$-strong monad and dually. We obtain the morphism $?A \otimes !B \rightarrow ?(A \otimes !B)$ by acting on the $\cap$-universal morphism of $(\cap(A \otimes \mathsf{FUB}) \mid) \rightarrow A \otimes \mathsf{FUB}$ as follows.

$$\begin{aligned} \mathcal{P}(\cap(A \otimes \mathsf{FUB}) \mid A \otimes \mathsf{FUB};) &\xrightarrow{\sim} \mathcal{P}(\cap(A \otimes \mathsf{FUB}) \mid A, \mathsf{FUB};) \\ &\xrightarrow{\sim} \mathcal{P}(\cap(A \otimes \mathsf{FUB}), \mathsf{UB} \mid A;) \\ &\xrightarrow{\sim} \mathcal{P}(\cap(A \otimes \mathsf{FUB}), \mathsf{UB}; \cap A) \\ &\rightarrow \mathcal{P}(\cap(A \otimes \mathsf{FUB}), \mathsf{UB} \mid \sqcup A;) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \sqcup A, \mathsf{FUB}; \sqcup(A \otimes \mathsf{FUB})) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \sqcup A \otimes \mathsf{FUB}; \sqcup(A \otimes \mathsf{FUB})) \\ &= \mathcal{P}(\mid ?A \otimes !B; ?(A \otimes !B)). \end{aligned}$$

The noninvertible map above is composition with the $\sqcup$-universal $(\cap A \mid \sqcup A) \rightarrow ()$. It is straightforward to check the axioms. (This is like the proof in [BCS96, §3.1] that proof nets with storage boxes form a linearly distributive category with storage.) $\square$

The converse of Proposition 3.16 is subtler. If $\mathcal{L}$ is a symmetric linearly distributive category with storage, it is in particular a symmetric monoidal category (under $\otimes, \mathbb{1}$) with a

1:22

M. SHULMAN

Vol. 19:2

linear exponential comonad !. Therefore, it gives rise to an LNL adjunction $\mathcal{M} \rightleftarrows \mathcal{L}$ as above, where $\mathcal{M}$ is the Eilenberg–Moore category of the comonad !. Hence, by Proposition 3.15, any subcategory of this $\mathcal{M}$ (such as the Kleisli category) yields an LNL polycategory $\mathcal{P}$ with $\mathcal{P}^{\mathrm{L}} = \mathcal{L}$ and having $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{F}, \mathsf{U}$. Similarly, any subcategory of the opposite of the Eilenberg–Moore category of the monad ? yields an LNL polycategory $\mathcal{P}$ with $\mathcal{P}^{\mathrm{L}} = \mathcal{L}$ and having $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{F}, \mathsf{U}$.

If $\mathcal{L}$ has duals, hence is $*$-autonomous, then by [BCS96, Proposition 5.1] the modalities ! and ? are dual, in that $?A \cong (!(A^*))^*$. This implies that their Eilenberg–Moore and Kleisli categories are dual to each other, by equivalences that lie over the self-duality $(\cdot)^*$; hence these two LNL polycategories coincide and are a $*$-autonomous LNL adjunction that induces the given ! and ?. However, if $\mathcal{L}$ does not have duals, then the Eilenberg–Moore categories of ! and ? need not be dual:

**Example 3.17.** Let $\mathcal{L}$ be a distributive lattice that is not a Boolean algebra. As in [CS97], we can regard $\mathcal{L}$ as a linearly distributive category with $\otimes = \wedge$ and $\mathfrak{A} = \vee$. Since $\wedge$ is the cartesian product and $\vee$ the cartesian coproduct, we can equip $\mathcal{L}$ with storage modalities ! and ? that are both just the identity. (Thanks to Robin Cockett for pointing out this example.) The Eilenberg–Moore categories of this ! and ? are then both just $\mathcal{L}$ itself, which may not be self-dual.

In fact this $\mathcal{L}$ cannot occur as $\mathcal{P}^{\mathrm{L}}$ for *any* LNL polycategory $\mathcal{P}$ with $\mathsf{F}, \mathsf{U}, \mathsf{F}, \mathsf{U}$ such that its (identity) modalities ! and ? are recovered as $\mathsf{FU}$ and $\mathsf{FU}$ respectively. To see this, note that for any nonlinear object $X$ in an LNL polycategory, if $\mathsf{FX}$ and $\mathsf{FX}$ both exist, then they are dual to each other. Thus, if $\mathsf{F}, \mathsf{F}$ both exist, then any object of the form $\mathsf{FX}$ or $\mathsf{FX}$ has a dual — and hence if $! = \mathsf{FU}$ is the identity, then *every* object has a dual. But this would imply that $\mathcal{L}$ is a Boolean algebra.

Thus, if we want to embed a general linearly distributive category with storage into an LNL polycategory, we have to give up on having all $\mathsf{F}, \mathsf{U}, \mathsf{F}, \mathsf{U}$. But we can get away with something slightly less:

**Proposition 3.18.** *A linearly distributive category $\mathcal{L}$ admits storage modalities if and only if it can occur as $\mathcal{P}^{\mathrm{L}}$ for an LNL polycategory $\mathcal{P}$ having $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{U}, \mathsf{U}$ along with $\mathsf{F}$ defined on the image of $\mathsf{U}$ and $\mathsf{F}$ defined on the image of $\mathsf{U}$.*

*Proof.* For “if”, just note that the proof of Proposition 3.16 uses only this weaker hypothesis. For “only if”, let $\mathcal{L}$ be a symmetric linearly distributive category with storage, and define an LNL polycategory $\mathcal{L}_{!,?}$ as follows. Its linear objects are the objects of $\mathcal{L}$, while its nonlinear objects consist of two copies of the objects of $\mathcal{L}$ denoted $A^!$ and $A^?$. Its homsets are defined by:

$$\begin{aligned} \mathcal{L}_{!,?}(A^!, \dots, A^!, p, B^?, \dots, B^?_q \mid C_1, \dots, C_m; D_1, \dots, D_n) \\ = \mathcal{L}(!A_1 \otimes \dots \otimes !A_p \otimes C_1 \otimes \dots \otimes C_m, ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} D_1 \mathfrak{A} \dots \mathfrak{A} D_n) \\ \mathcal{L}_{!,?}(A^!, \dots, A^!, p, B^?, \dots, B^?_q; C!) = \mathcal{L}(!A_1 \otimes \dots \otimes !A_p, ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} C) \\ \mathcal{L}_{!,?}(A^!, \dots, A^!, p, B^?, \dots, B^?_q; C^?) = \mathcal{L}(!A_1 \otimes \dots \otimes !A_p \otimes C, ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q) \end{aligned}$$

In particular, we have

$$\begin{aligned} \mathcal{L}_{!,?}(A^!; C!) &= \mathcal{L}(!A, C) & \mathcal{L}_{!,?}(A^!; C^?) &= \mathcal{L}(!A \otimes C, \bot) \\ \mathcal{L}_{!,?}(B^?; C^?) &= \mathcal{L}(C, ?B) & \mathcal{L}_{!,?}(B^?; C!) &= \mathcal{L}(\mathbb{1}, ?B \mathfrak{A} C). \end{aligned}$$

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:23

That is, the category of nonlinear objects and unary morphisms consists of a copy of the Kleisli category of ! (the objects $A^!$) and a copy of the opposite of the Kleisli category of ? (the objects $B^?$), with the morphisms between the two defined in a twisted way using the linearly distributive structure.

Composition of two linear morphisms is defined just as in the ordinary symmetric polycategory underlying $\mathcal{L}$. To compose a nonlinear morphism with either a linear or nonlinear morphism, we make use of the “generalized Kleisli lift”: given

$$f : !A_1 \otimes \dots \otimes !A_p \longrightarrow ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} C$$

we can construct the composite

$$\begin{array}{l} !A_1 \otimes \dots \otimes !A_p \rightarrow !!A_1 \otimes \dots \otimes !!A_p \\ \quad \rightarrow !(!A_1 \otimes \dots \otimes !A_p) \\ \quad \xrightarrow{!}f \quad !(?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} C) \\ \quad \rightarrow ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} !C \end{array}$$

where the first map is composed of the comultiplications $!A_i \to !!A_i$ of !, the second map is the lax monoidal structure of !, the third in $!f$, and the fourth is $q$ applications of the strength $!(?B \mathfrak{A} C) \to ?B \mathfrak{A} !C$. By first applying this construction to a nonlinear morphism with codomain $C^!$, or the dual construction to one with codomain $C^?$, we can then compose it along this object with any other morphism as usual in the underlying polycategory of $\mathcal{L}$.

Of course this LNL polycategory has $\otimes, \mathbb{1}, \mathfrak{A}, \bot$. By construction it has $\cup A = A^!$ and $\cap A = A^?$, and partially defined $\mathsf{F}A^! = !A$ and $\bot A^? = ?A$. Note that this is very similar to the proof in [BCS96, §3.2] that proof nets with storage are sound for linearly distributive categories with storage.

This “double Kleisli category” construction is functorial, and lands inside the slice category LNLPoly/DBLSPLIT from Remark 2.7. In terms of this slice, we can describe the restricted domains of $\mathsf{F}$ and $\bot$ by saying that $\mathsf{F}$ is defined on left-hand objects and $\bot$ on right-hand ones.

Moreover, if $\mathcal{L}$ is $*$-autonomous, then $A^? \cong (A^*)^!$ in $(\mathcal{L}_{!,?})^{\mathrm{NL}}$. Thus in this case $\mathcal{L}_{!,?}$ is equivalent (though not isomorphic) to the Kleisli adjunction of ! and also to the Kleisli adjunction of ?.

This gives us the following locally full sub-2-categories of LNLPoly:

- Linearly distributive categories with storage.
- $*$-autonomous categories with storage.
- Linearly distributive or $*$-autonomous categories with storage, any desired colimits preserved by the tensor product in each variable, and any desired limits preserved by the cotensor product in each variable.

# 4. UNIFYING UNIVERSALITY

In defining LNL doctrines, we will want to work generally with classes of universal arrows and colimits in LNL polycategories. Unfortunately, the different kinds of objects and morphisms in an LNL polycategory make such a general treatment quite cumbersome. For instance, we already saw in Section 2 that there are formally five different kinds of “universal morphism” in an LNL polycategory, which has the consequence that a fully formal proof

1:24

M. SHULMAN

Vol. 19:2

of Proposition 2.16 (universal morphisms compose) would have on the order of 25 different cases to consider.⁴ Similarly, there are four different kinds of limits and colimits, and so on. Duality doesn't simplify the situation significantly either, since an LNL polycategory has no "opposite" that reverses the nonlinear morphisms. Nevertheless, there is a clear intuition that this technical multiplicity is in some sense "inessential": all the cases behave similarly. In this section we give an alternative definition of LNL polycategories that enables us to formally unify these cases.

Given a set of objects partitioned into linear and nonlinear ones, by a **signed object** we mean an object together with an element of $\{-, +\}$, written $R^+$ or $R^-$, where $R$ is a (linear or nonlinear) object. We denote general signed objects by letters towards the middle of the Roman alphabet such as $K, L, M, \dots$, and lists of signed objects by the Greek letters $\Phi, \Psi$. If $K$ is a signed object we write $K^\bullet$ for the result of flipping its sign: $(R^+)^\bullet = R^-$ and $(R^-)^\bullet = R^+$.

**Definition 4.1.** A list of signed objects is **admissible** if

- (i) it contains at most one positive nonlinear object, and
- (ii) if it does contain one such, then it contains no linear objects.

**Lemma 4.2.** *If $(\Phi, K)$ and $(K^\bullet, \Psi)$ are admissible, so is $(\Phi, \Psi)$.*

*Proof.* If a positive nonlinear object $X^+$ appears in $\Phi$, then $K$ and all other objects in $\Phi$ must be negative nonlinear. Hence $K^\bullet$ is positive nonlinear, so all objects in $\Psi$ are also negative nonlinear. We can argue similarly if $\Psi$ contains $X^+$. $\square$

By a **structural map** we mean a morphism $\sigma : (K_1, \dots, K_m) \to (K_{\sigma 1}, \dots, K_{\sigma n})$ where $(K_1, \dots, K_m)$ is a list of signed objects and $\sigma : \{1, \dots, n\} \to \{1, \dots, m\}$ is a function with the property that for any $j$ with $1 \le j \le m$, if $|\sigma^{-1}(j)| \ne 1$ then $K_j$ is negative and nonlinear.

**Definition 4.3.** An **entries-only LNL polycategory** $\mathcal{P}$ consists of:

- A set of **objects** partitioned into linear and nonlinear ones.
- For any admissible list of signed objects $(K_1, \dots, K_n)$, a hom-set $\mathcal{P}(K_1, \dots, K_n)$, with functorial actions $\mathcal{P}(\Psi) \to \mathcal{P}(\Phi)$ by structural maps $\sigma : \Phi \to \Psi$.
- For any object $R$ (linear or nonlinear), an identity $1_R \in \mathcal{P}(R^-, R^+)$.
- Whenever $(\Phi, K)$ and $(K^\bullet, \Psi)$ are admissible, a composition map

$$\circ_K : \mathcal{P}(K^\bullet, \Psi) \times \mathcal{P}(\Phi, K) \to \mathcal{P}(\Phi, \Psi)$$

that is associative, unital, and equivariant with respect to the structural actions and permutations that swap the two inputs.

A **functor** between entries-only LNL polycategories consists of functions between their linear and nonlinear objects and morphisms, preserving entries, structural actions, identities, and composites.

**Proposition 4.4.** *The category of entries-only LNL polycategory is equivalent to that of LNL polycategories.*

⁴Not exactly 25, of course, since some pairs of universal morphisms will not be composable.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:25

Proof. By structural permutations, the hom-sets of an entries-only LNL polycategory are uniquely determined (up to isomorphism) by those of the form

$$\mathcal{P}(X_1^-, \dots, X_m^-, Y^+)$$

$$\mathcal{P}(X_1^-, \dots, X_m^-, A_1^-, \dots, A_n^-, B_1^+, \dots, B_p^+)$$

for nonlinear objects $X_i, Y$ and linear objects $A_j, B_k$. We can identify these with the hom-sets

$$\mathcal{P}(X_1, \dots, X_m; Y)$$

$$\mathcal{P}(X_1, \dots, X_m \mid A_1, \dots, A_n; B_1, \dots, B_p)$$

in an ordinary LNL polycategory, and the identities, compositions, and structural actions correspond.

Of course, the 2-categorical structure of LNLPoly that we defined in Section 2 can also be transported across this equivalence. A transformation between functors of entries-only LNL polycategories thus has components $\alpha_X \in \mathcal{Q}((HX)^-, (KX)^+)$ and $\alpha_A \in \mathcal{Q}((HA)^-, (KA)^+)$ satisfying suitable axioms.

Henceforth, we will pass freely back and forth between the two definitions, using whichever notation for homsets is more convenient. We can now define a general notion of universal morphism that encompasses all five cases described in Section 2.

**Definition 4.5.** A morphism $f \in \mathcal{P}(\Phi, K)$ in an entries-only LNL polycategory is **universal in** $K$ if for any list of signed objects $\Psi$ such that $(K^\bullet, \Psi)$ is admissible, the composition map $(-\circ_K f): \mathcal{P}(K^\bullet, \Psi) \to \mathcal{P}(\Phi, \Psi)$ is bijective, i.e. for any $h \in \mathcal{P}(\Phi, \Psi)$ there exists a unique $g \in \mathcal{P}(K^\bullet, \Psi)$ such that $g \circ_K f = h$.

In fact, following [Her04, LSR17, BZ20], it is useful to generalize from *universal* morphisms in one multi- or poly-category to *cartesian* ones relative to a functor.

**Definition 4.6.** Given a functor $\pi: \mathcal{P} \to \mathcal{Q}$ of entries-only LNL polycategories, a morphism $f \in \mathcal{P}(\Phi, K)$ is **$\pi$-cartesian in** $K$ if for any list of signed objects $\Psi$ of $\mathcal{P}$ such that $(K^\bullet, \Psi)$ is admissible, the following square is a pullback:

$$\begin{array}{ccc} \mathcal{P}(K^\bullet, \Psi) & \xrightarrow{-\circ_K f} & \mathcal{P}(\Phi, \Psi) \\ \pi \downarrow & & \downarrow \pi \\ \mathcal{Q}(\pi K^\bullet, \pi \Psi) & \xrightarrow{-\circ_{(\pi K)}(\pi f)} & \mathcal{Q}(\pi \Phi, \pi \Psi) \end{array} \tag{4.1}$$

In other words, for any $h \in \mathcal{P}(\Phi, \Psi)$ and $\ell \in \mathcal{Q}(\pi K^\bullet, \pi \Psi)$ such that $\ell \circ_{\pi K} \pi f = \pi h$, there exists a unique $g \in \mathcal{P}(K^\bullet, \Psi)$ such that $g \circ_K f = h$ and $\pi g = \ell$.

Note that if $\mathcal{Q}$ is terminal, both sets on the bottom row of (4.1) are singletons; so the square is a pullback just when the morphism on top is a bijection. Thus, $f$ is universal in $K$ precisely when it is $\pi$-cartesian in $K$ for the unique functor $\pi: \mathcal{P} \to \text{LNLPOLY}$ to the terminal object.

Cartesian morphisms specialize to various notions in the literature:

- For symmetric multicategories, cartesian morphisms with $K$ positive specialize to the "strongly cocartesian" morphisms of [Her04, Remarks 2.2(1)].
- For cartesian multicategories, cartesian morphisms specialize to the cartesian and opcartesian morphisms of [LSR17].

1:26

M. SHULMAN

Vol. 19:2

- For symmetric polycategories, cartesian morphisms specialize to the cartesian and opcartesian morphisms of [BZ20].
- For categories, cartesian morphisms specialize to the traditional notion of cartesian and opcartesian morphism.

Example 4.7. Cartesian morphisms can express restricted universal properties. For instance, in Definition 4.6 let $\mathcal{Q} = \text{CBPV}$, and let $f \in \mathcal{P}(X^-, A^+)$ for a nonlinear $X$ and linear $A$, with vertex $K = A^+$. Then the hom-set $\mathcal{Q}(\pi K^\bullet, \pi \Psi)$ is empty unless $\Psi$ contains exactly one positive linear object and the rest nonlinear. Thus, $f$ is cartesian just when it exhibits $A$ as $\mathsf{F}X$ with the universal property of (3.1).

Example 4.8. Cartesian morphisms can also express adjunctions that behave similarly to $\mathsf{F} \dashv \mathsf{U}$ but stay inside the linear or nonlinear world. For instance, let SMADJ be the LNL multicategory with two objects $\mathsf{P}, \mathsf{N}$, both linear, a unique morphism $\Gamma \to \mathsf{P}$ when $\Gamma$ consists entirely of $\mathsf{P}$'s, and a unique morphism $\Gamma \to \mathsf{N}$ for any $\Gamma$. Then an object $\mathcal{P}$ of LNLPoly/SMADJ is a symmetric multicategory with a partition of its objects into "positive" and "negative" ones, such that any morphism with a negative object in its domain has a negative codomain. Suppose in addition that

- For any positive object $A$, there is a negative object $B$ and a morphism $A \to B$ that is cartesian in $B$ over the unique morphism $\mathsf{P} \to \mathsf{N}$ in SMADJ.
- For any negative object $B$, there is a positive object $A$ and a morphism $A \to B$ that is cartesian in $A$ over the unique morphism $\mathsf{P} \to \mathsf{N}$ in SMADJ.

By an argument like that of Proposition 3.1, such a $\mathcal{P}$ is uniquely determined by an adjunction of symmetric multicategories. Further cartesian liftings can specialize this to an adjunction of symmetric monoidal categories, with strong left adjoint and lax right adjoint.

Example 4.9. As an even simpler example, let ADJ have two linear objects $\mathsf{p}, \mathsf{N}$ and only one nonidentity morphism $\mathsf{P} \to \mathsf{N}$. Then an object of LNLPoly/ADJ is an ordinary category with its objects partitioned into positive and negative ones, such that there are no morphisms from a negative object to a positive one. Such a category is precisely the "collage" of a profunctor between the categories $\mathcal{P}$ and $\mathcal{N}$ of positive and negative objects. If all cartesian liftings of the morphism $\mathsf{P} \to \mathsf{N}$ exist in one direction, then the profunctor is representable by a functor $\mathcal{P} \to \mathcal{N}$; if they exist in the other direction, it is representable by a functor $\mathcal{N} \to \mathcal{P}$; and if both exist, it is representable by an adjunction $\mathcal{P} \rightleftarrows \mathcal{N}$.

As an example of the value of the entries-only framework, we can now prove (a generalization of) Proposition 2.16 without a division into 25-odd cases:

Proposition 4.10. Given $\pi : \mathcal{P} \to \mathcal{Q}$, if $f \in \mathcal{P}(\Phi_1, K)$ is $\pi$-cartesian in $K$ and $g \in \mathcal{P}(K^\bullet, \Phi_2, L)$ is $\pi$-cartesian in $L$, then their composite $g \circ_K f \in \mathcal{P}(\Phi_1, \Phi_2, L)$ is $\pi$-cartesian in $L$.

Proof. In the following diagram:

$$\begin{array}{c} \mathcal{P}(L^\bullet, \Psi) \xrightarrow{-\circ_{L}g} \mathcal{P}(K^\bullet, \Phi_2, \Psi) \xrightarrow{-\circ_K f} \mathcal{P}(\Phi_1, \Phi_2, \Psi) \\ \pi \downarrow \qquad \qquad \qquad \pi \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{Q}(\pi L^\bullet, \pi \Psi) \xrightarrow{-\circ_{(\pi L)}(\pi g)} \mathcal{Q}(\pi K^\bullet, \pi \Phi_2, \pi \Psi) \xrightarrow{-\circ_{(\pi K)}(\pi f)} \mathcal{Q}(\pi \Phi_1, \pi \Phi_2, \pi \Psi) \end{array}$$

both squares are pullbacks since $f$ and $g$ are $\pi$-cartesian, hence so is the rectangle.

□

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:27

|  Subterminal S | Universal properties | Equivalent structure  |
| --- | --- | --- |
|  LNLPOLY | \( \times, 1, \rightarrow, \otimes, \mathbb{1}, (\cdot)^{*}, F, U \) | *-autonomous closed LNL adjunction  |
|  LNLMULTI | \( \times, 1, \rightarrow, \otimes, \mathbb{1}, \multimap, F, U \) | closed LNL adjunction  |
|  SYMPOLY | \( \otimes, \mathbb{1}, (\cdot)^{*} \) | *-autonomous category  |
|  SYMMULTI | \( \otimes, \mathbb{1}, \multimap \) | closed symmetric monoidal category  |
|  CARTMULTI | \( \times, 1, \rightarrow \) | cartesian closed category  |
|  CBPV | \( \times, 1, \rightarrow, \multimap, \multimap, \times, \mathbb{1}^{\dagger}, F^{\dagger}, U \) | structure of Corollary 3.14  |

\( ^{\dagger} \)  with restricted universal property.

TABLE 2. Bifibrations over subterminals

Following [LSR17, BZ20], we define:

Definition 4.11. A functor \(\pi : \mathcal{P} \to \mathcal{Q}\) is a bifibration if for any list \(\Phi\) of signed objects in \(\mathcal{P}\) and any morphism \(g \in \mathcal{Q}(\pi \Phi, L)\) there exists a \(\pi\)-cartesian morphism \(f \in \mathcal{P}(\Phi, K)\) such that \(\pi(f) = g\).

When \(\mathcal{Q}\) is one of our distinguished subterminal objects (including the terminal object LNLPOLY), bifibrations \(\pi : \mathcal{P} \to \mathcal{Q}\) reduce to more familiar structures:

Theorem 4.12. For each row in Table 2, with subterminal object S listed in the first column, the following structures are equivalent:

(i) A bifibration \(\pi : \mathcal{P} \to \mathcal{S}\).
(ii) An object of LNLPoly/S with the universal properties in the second column.
(iii) The categorical structure indicated in the third column.

Proof. Clearly (i)⇒(ii), while (ii)⇔(iii) follows from Section 3. The remaining direction (ii)⇒(i) is similar to the universal characterization of *-autonomous categories in [BZ20]. By ×Θ, ⊗Γ, or ∂Δ we mean the result of combining all the objects in a list with the given binary operation; if the list contains only one object the result is that object (in which case the binary operation doesn't even need to exist), while if the list is empty the result is the corresponding nullary operation 1, 1, or ⊥. Now we construct the five possible types of morphism universal in X or A as follows:

- For \(\psi \in \mathcal{P}(\Theta ;X)\) we take \(X = \times \Theta\).
- For \(\psi \in \mathcal{P}(\Theta, X; Y)\) we take \(X = \times \Theta \to Y\).
- For \(\psi \in \mathcal{P}(\Theta, X \mid \Gamma; \Delta)\) we take \(X = \times \Theta \to (\bigotimes \Gamma \to \mathcal{X} \Delta)\).
- For \(\psi \in \mathcal{P}(\Theta \mid \Gamma ;\Delta ,A)\) we take \(A = \times \Theta \rtimes \bigotimes (\Gamma ,\Delta^{*})\)
- For \(\psi \in \mathcal{P}(\Theta \mid \Gamma, A; \Delta)\) we take \(A = \times \Theta \to \mathcal{X}(\Gamma^{*}, \Delta)\).

We leave it to the reader to check that whenever a particular type of universal morphism exists in one of our subterminals S, the requisite universal operations are among those assumed by (ii) or can be constructed from them. (When S = CBPV, we discussed the restricted universal property of F in Example 4.7.)

Definition 4.13. If Q is a fixed object such as those in Table 2 (or more generally Table 3), we refer to an object  \( P \in LNLPoly/Q \)  as birepresentable if the map  \( \pi : P \to Q \)  is a bifibration.

1:28

M. SHULMAN

Vol. 19:2

For instance, a birepresentable LNL polycategory is a *-autonomous closed LNL adjunction, a birepresentable symmetric polycategory is a *-autonomous category, a birepresentable cartesian multicategory is a cartesian closed category, and so on.⁵

Similarly, we can define a general notion of limit that encompasses all four cases. In fact, we can define a general notion that encompasses both universal morphisms and (weighted) limits and colimits!

Definition 4.14. An abstract cone is a small entries-only LNL polycategory $\mathcal{C}$ equipped with a specified signed object $K$ called the vertex, such that $\mathcal{C}(\Phi)$ is empty if $\Phi$ contains any copies of $K^{\bullet}$ or contains more than one copy of $K$, except that $\mathcal{C}(K^{\bullet}, K) = \{1_K\}$. Nonidentity morphisms containing $K$ (necessarily exactly once) are called abstract projections, while morphisms not containing $K$ are called abstract transitions. Note that no two abstract projections can be composable. The reduct of an abstract cone is its sub-LNL-polycategory obtained by removing the underlying object of $K$, its identity morphism, and all the abstract projections; we denote this by $\partial\mathcal{C}$.

An expansion of an abstract cone $\mathcal{C}$ is determined by a finite number of new objects (each linear or nonlinear) and a sign for each of them, yielding a signed list $\Psi$, such that $(K^{\bullet}, \Psi)$ is admissible (where $K$ is the vertex of $\mathcal{C}$). The expansion itself is an entries-only LNL polycategory denoted $\mathcal{C}_{/\Psi}$ (which is not itself an abstract cone) obtained by adding the new objects to $\mathcal{C}$ along with one new morphism $\widetilde{f} \in \mathcal{C}_{/\Psi}(\Phi, \Psi)$ for each abstract projection $f \in \mathcal{C}(\Phi, K)$, called the expanders, and an additional new morphism $\chi \in \mathcal{C}_{/\Psi}(K^{\bullet}, \Psi)$ called the factorization. Composition is defined by $\chi \circ_K f = \widetilde{f}$, and by $\widetilde{f} \circ g = \widetilde{f \circ g}$ when $g$ is an abstract transition. The corresponding pre-expansion is the sub-LNL-polycategory $\partial(\mathcal{C}_{/\Psi}) \subseteq \mathcal{C}_{/\Psi}$ obtained by omitting the morphism $\chi$. Note that we have inclusions

$$\partial\mathcal{C} \subseteq \mathcal{C} \subseteq \partial(\mathcal{C}_{/\Psi}) \subseteq \mathcal{C}_{/\Psi}.$$

Definition 4.15. By a concrete cone we mean a functor whose domain is an abstract cone. Let $\pi : \mathcal{P} \to \mathcal{Q}$ a functor of (entries-only) LNL polycategories, and $G : \mathcal{C} \to \mathcal{P}$ a concrete cone. We say that $G$ is $\pi$-extremal if for any expansion $\mathcal{C}_{/\Psi}$ of $\mathcal{C}$, any commutative square as shown below such that the composite $\mathcal{C} \to \partial(\mathcal{C}_{/\Psi}) \to \mathcal{P}$ is $G$ has a unique diagonal filler.

![img-0.jpeg](img-0.jpeg)

If $\mathcal{Q} = \text{LNLPOLY}$ is terminal, instead of $\pi$-extremal we say that $G$ is universal.

We will be primarily interested in two important classes of abstract cones, which show respectively that the notion of extremal cone includes both cartesian/universal morphisms and limits and colimits. Here is the first.

⁵In the literature, sometimes “representable” means only that “covariant” universal arrows exist, e.g. a “representable symmetric multicategory” is a not-necessarily-closed symmetric monoidal category. But other times it means that all universal arrows exist, e.g. a “representable polycategory” is a *-autonomous category. Our “birepresentable”, in analogy to “bifibration”, avoids ambiguity.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:29

Definition 4.16. Let $\Phi$ be a finite list of abstract objects and let $K$ be an additional abstract object, such that $K$ and each object of $\Phi$ is either linear or nonlinear and has a chosen sign. Let $\mathcal{C}art_{\Phi/K}$ be the LNL polycategory whose objects are those of $\Phi$ and $K$ and having precisely one nonidentity morphism $f \in \mathcal{C}art_{\Phi/K}(\Phi, K)$. This is an abstract cone with vertex $K$; we call it the **abstract cartesianness cone** determined by $\Phi$ and $K$.

Observe that a concrete cone $G : \mathcal{C}art_{\Phi/K} \to \mathcal{P}$ is determined by a single morphism $Gf \in \mathcal{P}(G\Phi, GK)$.

Proposition 4.17. For any $\phi : \mathcal{P} \to \mathcal{Q}$, a concrete cone $G : \mathcal{C}art_{\Phi/K} \to \mathcal{P}$ is $\pi$-extremal if and only if $Gf$ is $\pi$-cartesian in $K$.

Proof. Because there is exactly one abstract projection $f$ in $\mathcal{C}art_{\Phi/K}$, an extension of a functor $G : \mathcal{C} \to \mathcal{P}$ to some pre-expansion $\partial((\mathcal{C}art_{\Phi/K})_{/\Psi})$ is uniquely determined by a list of signed objects $\Psi$ in $\mathcal{P}$ such that $(GK^{\bullet}, \Psi)$ is admissible, together with a morphism $\widetilde{f} \in \mathcal{P}(G\Phi, \Psi)$. A further extension of this to the expansion $(\mathcal{C}art_{\Phi/K})_{/\Psi}$ consists of a morphism $\chi \in \mathcal{P}(GK^{\bullet}, \Psi)$ such that $\chi \circ Gf = \widetilde{f}$. Applying these characterizations to $\mathcal{Q}$ as well, we see that $G$ is $\pi$-extremal if and only if

For any list of signed objects $\Psi$ in $\mathcal{P}$ such that $(GK^{\bullet}, \Psi)$ is admissible, any morphism $\widetilde{f} \in \mathcal{P}(G\Phi, \Psi)$, and any morphism $\xi \in \mathcal{Q}(\pi GK^{\bullet}, \pi\Psi)$ such that $\xi \circ \pi Gf = \pi\widetilde{f}$, there exists a unique morphism $\chi \in \mathcal{P}(GK^{\bullet}, \Psi)$ such that $\chi \circ Gf = \widetilde{f}$ and $\pi(\chi) = \xi$.

However, this is also exactly what it means for (4.1) (with $f$ replaced by $Gf$) to be a pullback of sets, which is the definition of when $Gf$ is $\pi$-cartesian in $K$. $\square$

Our second important class of abstract cones is the following.

Definition 4.18. Let $\mathcal{A}$ be an ordinary small category, and let $\mathcal{A}^{\triangleright}$ denote the result of adjoining a new terminal object $T$. If we make $\mathcal{A}^{\triangleright}$ an LNL polycategory by declaring all objects to be linear, it becomes an abstract cone with vertex $T^{+}$. We denote this by $\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}}$ and call it the **abstract linear colimit cone** determined by $\mathcal{A}$.

Dually, if $\mathcal{A}^{\circ}$ denotes the result of adjoining a new initial object $I$, then with all objects linear it yields an abstract cone with vertex $I^{-}$. We denote this by $\mathcal{L}im_{\mathcal{A}}^{\mathrm{L}}$ and call it an **abstract linear limit cone**.

Similarly, by declaring all the objects to be nonlinear, we obtain **abstract nonlinear colimit cones** $\mathcal{C}olim_{\mathcal{A}}^{\mathrm{NL}}$ and **abstract nonlinear limit cones** $\mathcal{L}im_{\mathcal{A}}^{\mathrm{NL}}$.

Observe that a concrete cone $G : \mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P}$ is determined by a cocone under a $\mathcal{A}$-shaped diagram in the category of linear objects of $\mathcal{P}$, and similarly in the other cases.

# Proposition 4.19.

(i) A concrete cone \( G: \mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a colimit, in the strong sense of (2.4).
(ii) A concrete cone \( G: \mathcal{L}im_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a limit, in the strong sense of (2.5).
(iii) A concrete cone \( G: \mathcal{C}olim_{\mathcal{A}}^{\mathrm{NL}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a colimit, in the strong sense of (2.2)-(2.3).
(iv) A concrete cone \( G: \mathcal{L}im_{\mathcal{A}}^{\mathrm{NL}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a limit in the sense of (2.1).

1:30

M. SHULMAN

Vol. 19:2

*Proof.* We prove (i); the others are analogous. Because the vertex $T^+$ of $\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}}$ is linear and positive, $(T^-, \Psi)$ is admissible just when $\Psi$ contains no positive nonlinear objects. An extension of $G : \mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P}$ to some pre-expansion $\partial((\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}})_{/\Psi})$ thus consists of a list $\Theta$ of nonlinear objects of $\mathcal{P}$, lists $\Gamma$ and $\Delta$ of linear objects of $\mathcal{P}$, and a morphism $\bar{f}_i \in \mathcal{P}(\Theta \mid \Gamma, GA_i; \Delta)$ for each object $A_i \in \mathcal{A}$, such that $\bar{f}_i \circ Gg = \bar{f}_j$ for each morphism $g : A_j \to A_i$ in $\mathcal{A}$. This is precisely an element of $\lim_i \mathcal{P}(\Theta \mid \Gamma, A_i; \Delta)$, the right-hand side of (2.4).

A further extension to the expansion $(\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}})_{/\Psi}$ is then determined by a morphism $\chi \in \mathcal{P}(\Theta \mid \Gamma, GT; \Delta)$ such that $\chi \circ_{GT} f_i = \bar{f}_i$ for all $A_i \in \mathcal{A}$. To say that there is a unique such morphism is thus precisely to say that the natural map from left-to-right in (2.4) is a bijection. $\square$

**Definition 4.20.** If $H : \mathcal{C} \to \mathcal{Q}$ is a concrete cone, we say that $\pi : \mathcal{P} \to \mathcal{Q}$ **has extremal lifts of $H$** if for any lift $G : \partial \mathcal{C} \to \mathcal{P}$ of the reduct of $\mathcal{C}$ to $\mathcal{P}$, there exists a compatible lift of $H$ that is $\pi$-extremal:

$$\begin{array}{ccc} \partial \mathcal{C} & \xrightarrow[G]{G} & \mathcal{P} \\ \downarrow & \xrightarrow{\pi\text{-ext}} & \downarrow\pi \\ \mathcal{C} & \xrightarrow[H]{} & \mathcal{Q} \end{array}$$

**Example 4.21.** By Proposition 4.17, $\pi$ is a bifibration if and only if it has extremal lifts of all the abstract cartesianness cones from Definition 4.16.

**Definition 4.22.** We say that an LNL polycategory is **bicomplete** if its unique map to the terminal object has extremal lifts of all concrete cones for the abstract limit and colimit cones from Definition 4.18 (where $\mathcal{A}$ is small).

By Proposition 4.19, bicompleteness is equivalent to having all small limits and colimits of both kinds of objects, in the sense described in Section 2.

As pointed out by a referee, the generalization of Definition 4.22 to a relative notion over an arbitrary base $\mathcal{Q}$ is a little subtle: there are at least two natural-seeming possibilities.

**Definition 4.23.** Let $\pi : \mathcal{P} \to \mathcal{Q}$ be a functor of LNL polycategories.

- (i) We say $\pi$ is **relatively bicomplete** if it has extremal lifts of all concrete cones $H : \mathcal{C} \to \mathcal{Q}$ where $\mathcal{C}$ is one of the abstract cones from Definition 4.18 (where $\mathcal{A}$ is small).
- (ii) We say $\pi$ is **fiberwise bicomplete** if it has extremal lifts only of such cones that have the additional property that $H$ factors through the terminal object (equivalently, its image contains only identity maps).

The two coincide in the “absolute” case when $\mathcal{Q}$ is terminal, or more generally when it satisfies the following condition.

**Proposition 4.24.** *If $\mathcal{Q}$ contains no nonidentity unary co-unary morphisms between two objects of the same sort (linear or nonlinear), then a functor $\pi : \mathcal{P} \to \mathcal{Q}$ is relatively bicomplete if and only if it is fiberwise bicomplete. In particular, this is the case when $\mathcal{Q}$ is subterminal.* $\square$

**Example 4.25.** As noted in Section 2, an LNL multicategory cannot have a terminal linear object or an initial linear or nonlinear object when considered as an LNL polycategory. However, while a concrete cone $G : \mathcal{C} \to \mathcal{P}$ of such a shape in an LNL multicategory cannot be

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:31

universal, it can be $\pi$-extremal for the unique functor $\pi : \mathcal{P} \to \text{LNLMULTI}$ (see Remark 2.3). This yields the correct “modified” notion of initial and terminal object in an LNL multicategory as discussed in Section 2, since not all expansions of this cone factor through LNLMULTI. Since LNLMULTI is subterminal, Proposition 4.24 applies to LNL multicategories, so there is no ambiguity in the correct notion of “bicomplete LNL multicategory”.

Similarly, we obtain the correct notions of limit and colimit for symmetric polycategories, cartesian multicategories, symmetric multicategories, and CBPV pre-structures. The non-subterminals from Remarks 2.4 and 2.7 also satisfy the condition of Proposition 4.24, so there is no ambiguity in their correct notion of bicompleteness either.

The potential difference between relative and fiberwise bicompleteness can be attributed to the fact that Definitions 4.16 and 4.18 overlap. Specifically, the abstract cartesianness cone $\mathcal{C}art_{\Phi/K}$ when $\Phi$ is a single object of the same sort and opposite sign as $K$ coincides with an abstract limit or colimit cone where $\mathcal{A}$ is the terminal category. In the absolute case, this is a universal unary co-unary morphism between objects of the same sort, as in Remark 2.17, or equivalently a limit or colimit of a single object, which is trivial. But if $\pi : \mathcal{P} \to \mathcal{Q}$ has extremal lifts for these unary co-unary cones, then its underlying ordinary functors between categories of linear and nonlinear objects are each both a fibration and opfibration, in the classical Grothendieck sense.

**Example 4.26.** The non-subterminal $\mathcal{Q} = \text{SMADJ}$ from Example 4.8 contains a nonidentity morphism $\mathcal{P} \to \mathbb{N}$ between linear objects. Thus, while a fiberwise bicomplete object of LNLPoly/SMADJ contains only limits and colimits of positive and negative objects individually, a relatively bicomplete one also includes the cartesian lifts mentioned in Example 4.8 that make it an adjunction of symmetric multicategories.

Since these adjoint functors relating positive and negative objects are analogous to the exponential modalities relating linear and nonlinear objects, and do not intuitively look like a sort of “limit”, it is natural to view them as belonging to birepresentability and *not* to “completeness”. As pointed out by the referee, this argues for fiberwise bicompleteness as the correct notion of “bicompleteness” for general base objects $\mathcal{Q}$.

Our general notion of “extremal cone” also includes examples that don’t fall into either Definition 4.16 or Definition 4.18. However, our main purpose in introducing it is to give a common language to talk about these two examples. To this end, we note that together these two examples suffice to reconstruct all extremal cones.

**Theorem 4.27.** *For any functor $\pi : \mathcal{P} \to \mathcal{Q}$ of LNL polycategories, the following are equivalent.*

- (i) $\mathcal{P}$ has an extremal lift of any concrete cone $H : \mathcal{C} \to \mathcal{Q}$ (with $\mathcal{C}$ small).
- (ii) $\mathcal{P}$ is a relatively bicomplete bifibration.
- (iii) $\mathcal{P}$ is a fiberwise bicomplete bifibration.

*Proof.* Example 4.21 and Definition 4.22 show that (i)$\Rightarrow$(ii), and clearly (ii)$\Rightarrow$(iii). So let us assume (iii), and let $H : \mathcal{C} \to \mathcal{Q}$ be a cone and $G : \partial\mathcal{C} \to \mathcal{P}$ a lift of its reduct to $\mathcal{P}$. For any abstract projection $f \in \mathcal{C}(\Phi, K)$, let $\tilde{f} \in \mathcal{P}(G\Phi, K_f)$ be $\pi$-extremal in $K_f$ and such that $\pi(\tilde{f}) = H(f)$ and hence $\pi(K_f) = H(K)$, where the sign and linearity of $K_f$ are the same as that of $K$. Such a morphism exists because $\pi$ is a bifibration.

Now for any abstract transition $g \in \mathcal{C}(\Psi, L)$ and any abstract projection $f \in \mathcal{C}(L^\bullet, \Phi, K)$ that it is composable with, producing an abstract projection $f \circ_L g \in \mathcal{C}(\Psi, \Phi, K)$, the

1:32

M. SHULMAN

Vol. 19:2

![img-1.jpeg](img-1.jpeg)

FIGURE 1. Diagram for Proposition 4.30

composite $\widetilde{f} \circ Gg \in \mathcal{P}(G\Psi, G\Phi, K_f)$ satisfies

$$\pi(\widetilde{f} \circ Gg) = \pi(\widetilde{f}) \circ \pi(Gg) = H(f) \circ H(g) = H(f \circ g).$$

Thus, by the universal property of $\widetilde{f \circ_L g} \in \mathcal{P}(G\Psi, G\Phi, K_{f \circ_L g})$ it induces a unique morphism $\widetilde{g} \in \mathcal{P}(K_{f \circ_L g}^\bullet, K_f)$ such that $\pi(\widetilde{g}) = 1_K$.

Now these objects $K_f$ and morphisms $\widetilde{g}$ form a small diagram of objects of $\mathcal{P}$ (linear or nonlinear according as $K$ is such) lying in the fiber over $K$. In particular, therefore, the image of this diagram under $\pi$ admits a specified cone (if $K$ is negative) or cocone (if $K$ is positive) with vertex $H(K)$, consisting entirely of identity maps. Thus, since $\pi$ is fiberwise bicomplete, this cone of identity maps has a $\pi$-extremal lift. Composing the projections of this lift with the morphisms $\widetilde{f}$ yields a $\pi$-extremal concrete cone $\mathcal{C} \to \mathcal{P}$ extending $G$ and lifting $H$.

Of course, there are analogous results in which set-theoretic size of the limits and colimits and of the abstract cones are limited in chosen ways. We also have a version of Proposition 2.9 and its converse.

**Proposition 4.28.** Given $\pi : \mathcal{P} \to \mathcal{Q}$ and an abstract cone $\mathcal{C}$ with vertex $K$, if $F, G : \mathcal{C} \to \mathcal{P}$ coincide on the reduct $\partial\mathcal{C}$ and are both $\pi$-extremal, then there is a unique isomorphism $\phi : F(K) \cong G(K)$ such that $\pi(\phi)$ is an identity and such that $\phi \circ_K F(f) = G(f)$ for all abstract projections $f$ in $\mathcal{C}$.

Given $\pi : \mathcal{P} \to \mathcal{Q}$, an abstract cone $\mathcal{C}$ with vertex $K$, a concrete cone $G : \mathcal{C} \to \mathcal{P}$, and an isomorphism $\phi : G(K) \cong K'$, there is a concrete cone $G_\phi : \mathcal{C} \to \mathcal{P}$ that agrees with $G$ on the reduct $\partial\mathcal{C}$, sends the vertex to $K'$, and the abstract projections $f$ to $G_\phi(f) = \phi \circ G(f)$.

**Proposition 4.29.** If in the above construction $G$ is $\pi$-extremal, so is $G_\phi$.

And a composition property for functors:

**Proposition 4.30.** Suppose $\pi_1 : \mathcal{P}_1 \to \mathcal{P}_2$ and $\pi_2 : \mathcal{P}_2 \to \mathcal{P}_3$, and a concrete cone $G : \mathcal{C} \to \mathcal{P}_1$. If $G$ is $\pi_1$-extremal and $\pi_1 G$ is $\pi_2$-extremal, then $G$ is $\pi_2 \pi_1$-extremal.

Proof. In the diagram in Figure 1, to find a unique lift in the rectangle, we first find a unique lower diagonal lift and then a unique upper one.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:33

## 5. DOCTRINES AND SKETCHES

In Section 3 we encountered a long list of categorical structures that form locally full sub-2-categories of LNLPoly. In this section and the next we will define a general class of such sub-2-categories, which we call (sorted, LNL) doctrines. Inspecting the examples in Section 3, we see that each is characterized by three kinds of data:

- (i) Restrictions on the kinds of objects (e.g. no nonlinear objects) and the arities of morphisms (e.g. all linear morphisms are co-unary). We have already remarked that these restrictions can be detected by slicing LNLPoly over subterminals such as SYMMULTI, CBPV, etc. More generally, we can equip the objects or morphisms with structure by slicing over a non-subterminal object, such as PLMULTI, DBLSPLIT, and SMADJ in Remarks 2.4 and 2.7 and Example 4.8.
- (ii) Existence of universal cones, for all cones in some family (e.g. existence of tensors, internal-homs, modalities, or limits or colimits). Sometimes the universal property of these cones has to be restricted to respect the allowed arities of morphisms, which corresponds to asking for cartesian lifts over the base objects in (i).
- (iii) Requirements that certain adjunctions are of some “Kleisli type”, hence determined by a monad, a comonad, or both.

In this section we define LNL doctrines, which encapsulate (i) and (ii). In the next section we extend these to “sorted doctrines” that incorporate (iii) as well.

Definition 5.1. An LNL doctrine $\mathbb{D}$ is an LNL polycategory $|\mathbb{D}|$ equipped with a family of concrete cones $G : \mathcal{C} \to |\mathbb{D}|$, called the $\mathbb{D}$-cones. We say $\mathbb{D}$ is small if $|\mathbb{D}|$ is small and the family of cones is also small.

Given such a doctrine, a $\mathbb{D}$-category is an LNL polycategory $\mathcal{P}$ equipped with a functor $\pi : \mathcal{P} \to |\mathbb{D}|$ that has extremal lifts of all $\mathbb{D}$-cones:

![img-2.jpeg](img-2.jpeg)

A $\mathbb{D}$-functor between $\mathbb{D}$-categories is a morphism in LNLPoly/$|\mathbb{D}|$ that preserves $\pi$-extremal lifts of $\mathbb{D}$-cones, and a $\mathbb{D}$-transformation between $\mathbb{D}$-functors is a 2-cell in LNLPoly/$|\mathbb{D}|$. This defines a locally full sub-2-category $\mathbb{D}$-Cat $\subseteq$ LNLPoly.

Example 5.2. Let $|\mathbb{D}| =$ LNLPOLY be terminal, and let the $\mathbb{D}$-cones contain one representative from each isomorphism class of cones$^6$ constructed in Definition 4.16. Then by Theorem 4.12, a $\mathbb{D}$-category is a birepresentable LNL polycategory.

Similarly, if $|\mathbb{D}| =$ LNLPOLY and the $\mathbb{D}$-cones contain one representative of each isomorphism class of cones, by Theorem 4.27 a $\mathbb{D}$-category is a bicomplete birepresentable LNL polycategory. (Note that this doctrine is not small.) We can include more restricted classes of limits as well by combining the cones from Definition 4.16 with some of those from Definition 4.18; e.g. there is a (small) doctrine for birepresentable LNL polycategories with finite products and coproducts (additives).

Example 5.3. Taking $|\mathbb{D}|$ to be one of the subterminals SYMPOLY, SYMMULTI, CARTMULTI, CAT, and LNLMULTI from Remark 2.3, we can equip it with a family of cones that specify

$^6$An isomorphism of abstract cones is an isomorphism of LNL polycategories that preserves the vertices.

1:34

M. SHULMAN

Vol. 19:2

desired universal morphisms and/or limits and colimits with the appropriately restricted universal properties for the corresponding subclass of LNL polycategories, which as noted in Theorem 4.12 and Example 4.25 can be characterized by saying that certain cones are $\pi$-extremal rather than globally universal. For instance, there is a doctrine $\mathbb{D}$ with $|\mathbb{D}| = \text{SYMMULTI}$ for which the $\mathbb{D}$-categories are bicomplete closed symmetric monoidal categories; another doctrine with $|\mathbb{D}| = \text{SYMMULTI}$ for which the $\mathbb{D}$-categories are symmetric monoidal categories (not necessarily closed or bicomplete); a doctrine with $|\mathbb{D}| = \text{LNLMULTI}$ for which the $\mathbb{D}$-categories are LNL adjunctions; and so on. Similarly, taking $|\mathbb{D}| = \text{CBPV}$ or ECBV as in Proposition 3.13 and Theorem 4.12, we have doctrines for CBPV adjunction models, EEC+ models, and ECBV models.

Non-subterminal examples can incorporate further adjunctions. For instance, based on Example 4.8 we can formulate a doctrine for symmetric monoidal adjunctions. By combining this idea with arity restrictions as in Proposition 3.13 (CBPV structures), we obtain doctrines for models of polarized linear calculi as in [CFMM16]:

Example 5.4. Let LINPOL be the LNL multicategory with two objects P, N, both linear, a unique morphism $\Gamma \to \mathbb{P}$ when $\Gamma$ consists entirely of P's, and a unique morphism $\Gamma \to \mathbb{N}$ when $\Gamma$ contains no more than one N. If we equip it with the single-projection cones $(\mathbb{P}, \mathbb{P}) \to \underline{\mathbb{P}}$ and $(\cdot) \to \underline{\mathbb{P}}$ (with vertex underlined), we obtain a doctrine whose categories consist of a symmetric monoidal category $\mathcal{E}$, a category $\mathcal{L}$ enriched over the Day convolution monoidal structure on $[\mathcal{E}^{\text{op}}, \text{Set}]$, and an $[\mathcal{E}^{\text{op}}, \text{Set}]$-enriched functor $R : \mathcal{L} \to [\mathcal{E}^{\text{op}}, \text{Set}]$. As in Proposition 3.13, by adding the following cones we enforce additional universal properties:

- (i) From $\underline{\mathbb{P}} \to \mathbb{N}$ we make $R$ land inside $\mathcal{E}$.
- (ii) From $\mathbb{P} \to \underline{\mathbb{N}}$ we give $R : \mathcal{L} \to \mathcal{E}$ a left adjoint.
- (iii) From $(\underline{\mathbb{P}}, \mathbb{N}) \to \mathbb{N}$ we make $\mathcal{L}$ enriched over $\mathcal{E}$.
- (iv) From $(\mathbb{P}, \underline{\mathbb{N}}) \to \mathbb{N}$ we give $\mathcal{L}$ powers by representables.
- (v) From $(\mathbb{P}, \mathbb{N}) \to \underline{\mathbb{N}}$ we give $\mathcal{L}$ copowers by representables.

In particular, with items (i), (ii) and (iv) we obtain a doctrine for the $\mathbf{IMLL}_p^\eta$ models of [CFMM16]. And if we additionally include cones for $\oplus, 0$ of positive objects and $\&, \top$ of negative ones, we obtain their $\mathbf{IMALL}_p^\eta$ models.

Now let LNLPOL have two linear objects P, N and one nonlinear object X, with all nonlinear homsets singletons, a unique morphism $(\Theta \mid \Gamma) \to \mathbb{P}$ if $\Gamma$ consists entirely of P's, and a unique morphism $(\Theta \mid \Gamma) \to \mathbb{N}$ when $\Gamma$ contains no more than one N. With the above cones for an $\mathbf{IMLL}_p^\eta$ model, cones for $\times, 1$, and also the morphisms $\underline{\mathbb{X}} \to \mathbb{P}$ and $\mathbb{X} \to \underline{\mathbb{P}}$ representing a U defined on positive objects and an F valued in positive objects, this yields a doctrine for the $\mathbf{IMELL}_p^\eta$ models of [CFMM16]. Adding $\oplus, 0$ of positive objects, $\&, \top$ of negative ones, plus $+, \varnothing$, we obtain $\mathbf{IMLL}_p^\eta$ models.

Note that the morphisms in $\mathbb{D}$-Cat preserve the specified universal properties up to canonical isomorphism. This is 2-categorically correct, but means that $\mathbb{D}$-Cat is not well-endowed with strict limits and colimits. Thus, following the philosophy of homotopy theory, we embed it in a larger but better-behaved category.

Definition 5.5. Given an LNL doctrine $\mathbb{D}$, a $\mathbb{D}$-sketch is an LNL polycategory $\mathcal{P}$ together with a functor $\pi : \mathcal{P} \to |\mathbb{D}|$, and for each $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$ a set (perhaps empty) of lifts

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:35

of $G$ to $\mathcal{P}$ that we call **proto-extremal**:

$$\left\{ \begin{array}{c} \mathcal{P} \\ \mathcal{C} \xrightarrow[G]{} |\mathbb{D}| \end{array} \right\}.$$

A **morphism of $\mathbb{D}$-sketches** is a functor in LNLPoly/$|\mathbb{D}|$ that preserves proto-extremal cones; a **transformation** is an arbitrary 2-cell in LNLPoly/$|\mathbb{D}|$. This defines a 2-category $\mathbb{D}$-Sketch.

A $\mathbb{D}$-sketch is **realized** if every proto-extremal cone is in fact $\pi$-extremal. It is **saturated** if whenever $H : \mathcal{C} \to \mathcal{P}$ is proto-extremal, where $K$ is the vertex of $\mathcal{C}$, and $\phi : H(K) \cong K'$ is an isomorphism in $\mathcal{P}$ such that $\pi(\phi)$ is an identity, the cone $H_\phi : \mathcal{C} \to \mathcal{P}$ constructed before Proposition 4.29 is also proto-extremal. It is **precomplete** if for any $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$, any lift of its reduct $\partial\mathcal{C} \hookrightarrow \mathcal{C} \to |\mathbb{D}|$ to $\mathcal{P}$ can be extended to a proto-extremal cone:

$$\begin{array}{c} \partial\mathcal{C} \longrightarrow \mathcal{P} \\ \downarrow \quad \exists \quad \nearrow \quad \downarrow \pi \\ \mathcal{C} \xrightarrow[G]{} |\mathbb{D}| \end{array}$$

Finally, it is (**$\mathbb{D}$-**)complete** if it is realized, saturated, and precomplete.

**Proposition 5.6.** *The 2-category of $\mathbb{D}$-complete sketches is equivalent, as a strict 2-category, to the 2-category $\mathbb{D}$-Cat of $\mathbb{D}$-categories.*

*Proof.* We regard a $\mathbb{D}$-category as a sketch by designating every $\pi$-extremal lift of a $\mathbb{D}$-cone as proto-extremal. This defines a 2-functor $\mathbb{D}$-Cat $\to \mathbb{D}$-Sketch, which lands inside the $\mathbb{D}$-complete sketches (using Proposition 4.29) and is an isomorphism on hom-categories. Moreover, precompleteness and realization make any $\mathbb{D}$-complete sketch into a $\mathbb{D}$-category, while in the presence of these properties saturation is equivalent (using Proposition 4.28) to saying that all $\pi$-extremal lifts of $\mathbb{D}$-cones are proto-extremal; hence the functor is essentially surjective as well. $\square$

$\mathbb{D}$-Sketch is a complete and cocomplete strict 2-category, with limits and colimits created in LNLPoly. If $\mathbb{D}$ is small, $\mathbb{D}$-Sketch is even locally presentable. It is also better-endowed with adjunctions, particularly ones arising from doctrine morphisms.

**Definition 5.7.** Let $\mathbb{D}_1, \mathbb{D}_2$ be LNL doctrines. A **doctrine map $\mathfrak{F} : \mathbb{D}_1 \to \mathbb{D}_2$** is a functor $|\mathfrak{F}| : |\mathbb{D}_1| \to |\mathbb{D}_2|$ together with, for each $\mathbb{D}_1$-cone $G : \mathcal{C} \to |\mathbb{D}_1|$, a $\mathbb{D}_2$-cone $\mathcal{C}_{\mathfrak{F}} \to |\mathbb{D}_2|$ and an isomorphism of abstract cones $\mathcal{C} \cong \mathcal{C}_{\mathfrak{F}}$ (preserving the vertex) making the evident square commute.

**Proposition 5.8.** *Any doctrine map $\mathfrak{F} : \mathbb{D}_1 \to \mathbb{D}_2$ induces a strict 2-adjunction (i.e. an adjunction of Cat-enriched categories)*

$$\mathfrak{F}_* : \mathbb{D}_1\text{-Sketch} \rightleftarrows \mathbb{D}_2\text{-Sketch} : \mathfrak{F}^*.$$

*Proof.* We have a 2-adjunction

$$\mathfrak{F}_* : \text{LNLPoly}/|\mathbb{D}_1| \rightleftarrows \text{LNLPoly}/|\mathbb{D}_2| : \mathfrak{F}^*$$

1:36

M. SHULMAN

Vol. 19:2

given by composition with $|\mathfrak{F}|$ and pullback along it, so it suffices to lift this to sketches. For the right adjoint $\mathfrak{F}^*$, we define a lift $\mathcal{C} \to \mathfrak{F}^*\mathcal{P}$ of some $\mathbb{D}_1$-cone $\mathcal{C} \to |\mathbb{D}_1|$ to be proto-extremal if the composite $\mathcal{C}_{\mathfrak{F}} \cong \mathcal{C} \to \mathfrak{F}^*\mathcal{P} \to \mathcal{P}$ is proto-extremal:

![img-3.jpeg](img-3.jpeg)

For the left adjoint $\mathfrak{F}_*$, we define a lift $\mathcal{D} \to \mathfrak{F}_*\mathcal{P}$ of some $\mathbb{D}_2$-cone $\mathcal{D} \to |\mathbb{D}_2|$ to be proto-extremal if the latter $\mathbb{D}_2$-cone is the $F$-image of some $\mathbb{D}_1$-cone $\mathcal{C} \to |\mathbb{D}_1|$ and there is a proto-extremal lift $\mathcal{C} \to \mathcal{P}$ making the evident diagram commute:

![img-4.jpeg](img-4.jpeg)

It is straightforward to check that these constructions lift the 2-adjunction.

We really want an analogous adjunction $\mathbb{D}_1$-Cat $\rightleftarrows \mathbb{D}_2$-Cat, but this can only be expected to be a pseudo 2-adjunction, satisfying its universal property up to equivalence.$^7$ We will construct this in Section 9, using the above strict 2-adjunction.

## 6. SORTED DOCTRINES

In Section 3 we chose to represent monads and comonads as their Kleisli adjunction rather than their Eilenberg–Moore adjunction (or any other), due to Lemma 3.8. Thus, to impose the third kind of “Kleisli type” condition mentioned in Section 5, it suffices to assert essential-surjectivity properties for some of the modalities.

**Definition 6.1.** An **arrow-type abstract cone** is determined by two signed objects $K, L$ (each linear or nonlinear). Its vertex is $K$, and its only nonidentity morphism is an abstract projection in $\mathcal{C}(L, K)$.

If a cone belonging to a doctrine $\mathbb{D}$ is arrow-type determined by $K, L$, then by choosing extremal lifts, any $\mathbb{D}$-category can be equipped with a functor from the fiber over $L$ to the fiber over $K$. This functor is contravariant if $K$ and $L$ have the same sign and covariant if they have different signs. Of the cones from Definition 4.16 representing the basic universal properties from Section 2, $\mathsf{F}, \mathsf{U}, \mathsf{J}, \mathsf{\Pi}, (\cdot)^*$ are arrow-type.

**Definition 6.2.** A **sorted LNL doctrine** is an LNL doctrine $\mathbb{D}$ together with:

$^7$A pseudo 2-adjunction is traditionally called a “biadjunction”, but this seems inadvisable here since we are using the prefix “bi-” with a different connotation in “bifibration” and “bicomplete”.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:37

(i) A partition of the objects of $|\mathbb{D}|$ (which we call **sorts**) into **primitive sorts** and **derived sorts**.
(ii) For each derived sort $R$, there is exactly one $\mathbb{D}$-cone $G_R : \mathcal{C}_R \to |\mathbb{D}|$ whose concrete vertex $G(K)$ is $R^-$ or $R^+$, and this is an arrow-type cone whose other vertex $G(L)$ is a primitive sort. We call it the **sorting cone** for $R$.

**Definition 6.3.** Let $\mathbb{D}$ be a sorted doctrine and $\pi : \mathcal{S} \to |\mathbb{D}|$ a $\mathbb{D}$-sketch.

- $\mathcal{S}$ is **well-sorted** if for every derived sort $R$ and every object $\widetilde{R} \in \pi^{-1}(R)$, there exists a proto-extremal lift of $G_R$ that maps the vertex to $\widetilde{R}$.
- $\mathcal{S}$ is **strictly well-sorted** if for every derived sort $R$ with corresponding primitive sort $S$, there is a specified bijection between the objects of $\pi^{-1}(R)$ and $\pi^{-1}(S)$ and, for each $\widetilde{R}$ and $\widetilde{S}$ that correspond under this bijection, a specified proto-extremal lift of $G_R$ with entries $\widetilde{R}$ and $\widetilde{S}$.

We write $\mathbb{D}$-sCat for the 2-category of well-sorted $\mathbb{D}$-complete sketches ($\mathbb{D}$-categories).

Thus a $\mathbb{D}$-category is well-sorted if and only if the functor $\pi^{-1}(S) \to \pi^{-1}(R)$ induced by each sorting cone is essentially surjective on objects, and strictly well-sorted if a particular choice of this functor has been made that is bijective on objects. We are “really” interested in the strictly well-sorted sketches, but the non-strictly well-sorted ones are more convenient to work with technically. Fortunately we have the following:

**Proposition 6.4.** *For a sorted doctrine $\mathbb{D}$, every well-sorted $\mathbb{D}$-category is equivalent in $\mathbb{D}$-Sketch to a strictly well-sorted one.*

*Proof.* If $\pi : \mathcal{S} \to |\mathbb{D}|$ is well-sorted, for each derived sort $R$ with corresponding primitive sort $S$ we have an essentially surjective functor $\pi^{-1}(S) \to \pi^{-1}(R)$. Thus, we can replace $\pi^{-1}(R)$ by an equivalent category whose objects are those of $\pi^{-1}(S)$, making the functor bijective on objects. These equivalences on fibers extend to an equivalence of $\mathbb{D}$-categories. $\square$

Thus, $\mathbb{D}$-sCat is equivalent (as a bicategory) to its full sub-2-category of strictly well-sorted $\mathbb{D}$-categories.

**Example 6.5.** Any LNL doctrine can be made sorted with all sorts primitive, so that all $\mathbb{D}$-sketches are (vacuously) strictly well-sorted.

**Example 6.6.** Let $\mathbb{D}$ be any doctrine for which $|\mathbb{D}|$ has exactly one nonlinear object $\mathbf{x}$ and one linear object $\mathbf{A}$, such as LNLMULTI or the terminal object LNLPOLY. Suppose furthermore that the only $\mathbb{D}$-cone with vertex $\mathbf{x}^\pm$ is an arrow-type cone with vertex $\mathbf{x}^-$ and abstract projection in $\mathcal{C}(\mathbf{A}^+, \mathbf{x}^-)$ (that is, a U-cone). Then we can make $\mathbb{D}$ a sorted doctrine where $\mathbf{A}$ is primitive, $\mathbf{x}$ is derived, and this cone is the sorting cone.

We call this a **Kleisli sorted** doctrine. Then a $\mathbb{D}$-category is strictly well-sorted just when it is of Kleisli type (Definition 3.9). If $\mathbb{D}$ also contains $\mathsf{F}$, then by Lemma 3.8 this is equivalent to its being the Kleisli adjunction of the comonad $! = \mathsf{FU}$. Thus, the 2-category of symmetric monoidal categories with a linear exponential comonad, and its variants with internal-homs and/or limits and colimits, are equivalent to $\mathbb{D}$-sCat for some sorted LNL doctrine $\mathbb{D}$. Similarly, by taking an $\mathsf{F}$-cone as sorting we can represent cartesian monoidal categories with a commutative strong monad.

**Example 6.7.** Let $\mathbb{D}$ be the sorted doctrine defined as follows. We take $|\mathbb{D}| = \text{DBLSPLIT}$, as in Remark 2.7; thus a functor $\pi : \mathcal{P} \to |\mathbb{D}|$ partitions the nonlinear objects of $\mathcal{P}$ into left-hand and right-hand ones. We equip $\mathbb{D}$ with cones for $\otimes, \mathbb{1}, \mathcal{A}, \bot$, as well as $\mathsf{F}$ defined on

1:38

M. SHULMAN

Vol. 19:2

left-hand objects, U taking values in left-hand objects, ⊥ defined on right-hand objects, and ∩ taking values in right-hand objects. And we take the U and ∩ cones as sorting. Then a D-category is strictly well-sorted just when it has a choice of U and ∩ that are bijective onto the left-hand and right-hand objects respectively. A straightforward extension of Lemma 3.8 now shows that this is the same as its being the double-Kleisli adjunction of Proposition 3.18 constructed from the linearly distributive category with storage $\mathcal{P}^{\mathrm{L}}$. Thus, the 2-categories of linearly distributive or $*$-autonomous categories with storage, and their variants with limits and colimits, are equivalent to D -sCat for some sorted LNL doctrine D.

Example 6.8. By making one of the sorts in SMADJ (Example 4.8) derived from the other, we obtain sorted doctrines for lax symmetric monoidal monads or comonads.

Example 6.9. Recall the LNL multicategory LINPOL from Example 5.4. We now rechristen it SYMSKEW, calling its two linear objects L and T; thus there is a unique morphism $\Gamma \to \mathrm{L}$ when $\Gamma$ consists entirely of L's, and a unique morphism $\Gamma \to \mathrm{T}$ when $\Gamma$ contains no more than one T. We make this a sorted doctrine D with T primitive, L derived, sorting cone $\mathrm{L} \to \mathrm{T}$ (with vertex L), and no other cones.

A strictly well-sorted D-category is determined by the objects over T and the morphisms with target over T. Every object over L is the image of one over T by a functor that we may either leave implicit or denote G. We call a morphism over $\Gamma \to \mathrm{T}$ loose if $\Gamma$ consists entirely of L's; thus the loose homsets are of the form $\mathcal{P}(\mathsf{GA}_1, \ldots, \mathsf{GA}_n; B)$. We call a morphism over $\Gamma \to \mathrm{T}$ tight if $\Gamma$ contains a T; these tight homsets are uniquely determined by those where the first element of $\Gamma$ is T, i.e. of the form $\mathcal{P}(A_1, \mathsf{GA}_2, \ldots, \mathsf{GA}_n; B)$. This yields a doctrine for the symmetric skew multicategories of [BL20, §5]; the morphism j from tight to loose morphisms:

$$\mathcal{P}(A_1, \mathsf{GA}_2, \ldots, \mathsf{GA}_n; B) \to \mathcal{P}(\mathsf{GA}_1, \mathsf{GA}_2, \ldots, \mathsf{GA}_n; B)$$

is given by composition with the universal arrow $\mathsf{GA}_1 \to A_1$ over the sorting cone.

In a skew multicategory regarded as an LNL polycategory over SYMSKEW, a tight unit 1 (with restricted universal property) is a "left universal nullary map classifier". Similarly, for objects A and B over T, with corresponding objects GA and GB over L, a tensor product $A \otimes \mathsf{GB}$ (which also lies over T) is a "left universal tight binary map classifier" (see [BL18, §4.4]); and a hom $\mathsf{GA} \to B$ (also lying over T) corresponds to the notion of "closedness" from [BL18, §4.5]. Thus, by [BL18, BL20], we have sorted LNL doctrines for (symmetric) skew monoidal categories and (symmetric) skew closed categories. In particular, the "noninvertible associator" of a skew monoidal category is represented as a comparison map

$$(A \otimes \mathsf{GB}) \otimes \mathsf{GC} \longrightarrow A \otimes \mathsf{G}(B \otimes \mathsf{GC})$$

whose noninvertibility is unsurprising due to the different placements of G. (However, a symmetric closed skew-monoidal category is not a bifibration over SYMSKEW; it lacks some universal properties, such as a tensor product of two loose objects.)

Example 6.10. Let D be the sorted doctrine with $|\mathbb{D}| = \mathrm{CBPV}$, with a single cone for F that is sorting. Thus, a strictly well-sorted D-category is a linearly subunary LNL multicategory with an F satisfying a restricted universal property, and such that F is bijective from the nonlinear objects to the linear ones. Thus, it consists of a cartesian multicategory together with additional linear homsets

$$\mathcal{P}(X_1, \ldots, X_n \mid ; \mathsf{FZ}). \tag{6.1}$$

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:39

This information uniquely determines the other linear homsets by the F-isomorphism:

$$\mathcal{P}(X_1, \dots, X_n \mid \mathsf{F}Y; \mathsf{F}Z) \cong \mathcal{P}(X_1, \dots, X_n, Y \mid ; \mathsf{F}Z).$$

However, passing back along these isomorphisms yields multicategorical composition operations on the linear homsets (6.1):

$$\begin{aligned} \mathcal{P}(\Upsilon, X \mid ; \mathsf{F}Y) \times \mathcal{P}(\Theta \mid ; \mathsf{F}X) &\cong \mathcal{P}(\Upsilon \mid \mathsf{F}X; \mathsf{F}Y) \times \mathcal{P}(\Theta \mid ; \mathsf{F}X) \\ &\to \mathcal{P}(\Upsilon, \Theta \mid ; \mathsf{F}Y). \end{aligned}$$

This composition treats the universal morphisms $\chi \in \mathcal{P}(X \mid ; \mathsf{F}X)$ as identities. Moreover, naturality of the F-isomorphisms implies that these operations are associative in the limited sense that the two composite functions

$$\mathcal{P}(\Theta_3, Y \mid ; \mathsf{F}Z) \times \mathcal{P}(\Theta_2, X \mid ; \mathsf{F}Y) \times \mathcal{P}(\Theta_1 \mid ; \mathsf{F}X) \to \mathcal{P}(\Theta_3, \Theta_2, \Theta_1 \mid ; \mathsf{F}Z)$$

are equal. However, because of the restricted universal property of $\mathsf{F}$, nothing forces the two composite functions

$$\mathcal{P}(\Theta_3, X, Y \mid ; \mathsf{F}Z) \times \mathcal{P}(\Theta_2 \mid ; \mathsf{F}Y) \times \mathcal{P}(\Theta_1 \mid ; \mathsf{F}X) \Rightarrow \mathcal{P}(\Theta_3, \Theta_2, \Theta_1 \mid ; \mathsf{F}Z) \quad (6.2)$$

to be equal, as they would be if the homsets (6.1) formed a (cartesian) multicategory. This means the linear homsets (6.1) have the structure of a *cartesian pre-multicategory* in the sense of [SL13].

Finally, composing with the universal morphism $\chi \in \mathcal{P}(X \mid ; \mathsf{F}X)$ provides a function

$$\mathcal{P}(\Theta; X) \to \mathcal{P}(\Theta \mid ; \mathsf{F}X)$$

that respects the cartesian actions, identities, and compositions. Moreover, the linear morphisms in the image of this map are *central*, meaning that the two morphisms (6.2) are equal if one of the morphisms into $\mathsf{F}X$ or $\mathsf{F}Y$ is in this image. Thus, we conclude that a strictly well-sorted $\mathbb{D}$-category can be identified with a *cartesian Freyd multicategory* in the sense of [SL13]: a cartesian multicategory $\mathcal{V}$ of “values”, a cartesian pre-multicategory $\mathcal{C}$ of “computations”, and an identity-on-objects functor $\text{return} : \mathcal{V} \to \mathcal{C}$ that preserves centrality. (I am indebted to Max New for this observation.)

A similar doctrine with $|\mathbb{D}| = \text{SYMSKEW}$ yields symmetric Freyd multicategories. However, I don’t believe there is a sorted doctrine such that the strictly well-sorted $\mathbb{D}$-categories can be identified with bare (cartesian or symmetric) pre-multicategories. We can “remove” the extra information of the nonlinear morphisms by requiring either that the only nonlinear morphisms are projections, or that the nonlinear morphisms coincide with the central linear ones; but neither of these conditions is enforceable doctrinally. (Similarly, a *duploid* [MM13] is an adjunction of ordinary categories with certain restrictions: adjunctions can be modeled doctrinally over the base ADJ from Example 4.9, but the duploid conditions are not doctrinal.)

A nonlinear product $X \times Y$ in a cartesian Freyd multicategory is the same as a *tensor* in the sense of [SL13]: a (pre)multicategorical tensor in $\mathcal{V}$ that is preserved by return. As shown in [SL13, §8], a cartesian Freyd multicategory with all such tensors (and units) is equivalent to a Freyd-category in the sense of [PT99]: a cartesian monoidal category $\mathcal{V}$, a symmetric premonoidal category [PR97] $\mathcal{C}$, and an identity-on-objects symmetric premonoidal functor $\text{return} : \mathcal{V} \to \mathcal{C}$ that preserves centrality. (Alternatively, one can use the characterization of Freyd-categories from [Lev04], which is akin to those of CBPV structures in Proposition 3.13.)

1:40

M. SHULMAN

Vol. 19:2

Similarly, a nonlinear coproduct $X + Y$ in a cartesian Freyd multicategory is the same as a *sum* in the sense of [SL13]. Finally, a cartesian Freyd multicategory has *function spaces* in the sense of [SL13, §6] if and only if it has our mixed homs $\rightarrow$. The latter means that for any nonlinear object $X$ and linear object $\mathsf{F}Y$, there is a nonlinear object $X \rightarrow \mathsf{F}Y$, with a universal linear morphism $\chi \in \mathcal{P}(X \rightarrow \mathsf{F}Y, X \mid ; \mathsf{F}Y)$ inducing a bijection

$$\mathcal{P}(\Theta, X \mid ; \mathsf{F}Y) \cong \mathcal{P}(\Theta; X \rightarrow \mathsf{F}Y)$$

between computations and values, as in [SL13, (4)].

Unlike $\mathbb{D}$-completeness, well-sortedness is a *coreflective* property.

**Proposition 6.11.** *For any sorted doctrine $\mathbb{D}$, the 2-category of well-sorted $\mathbb{D}$-sketches is coreflective in $\mathbb{D}$-Sketch, and the coreflector preserves $\mathbb{D}$-completeness.*

*Proof.* The coreflection of a $\mathbb{D}$-sketch $\mathcal{S}$ is its full sub-LNL-polycategory $\mathcal{S}'$ containing all objects of $\mathcal{S}$ that lie over primitive sorts, and precisely those objects lying over derived sorts that are the vertex of a proto-extremal lift of the sorting cone. Its proto-extremal cones are precisely those of $\mathcal{S}$ that land in this subcategory.

If $\mathcal{S}$ is $\mathbb{D}$-complete, $\mathcal{S}'$ is clearly still realized and saturated. To see that $\mathcal{S}'$ is also still precomplete, note that by construction it still has proto-universal lifts of the sorting cones. But by definition, any non-sorting $\mathbb{D}$-cone must have a *primitive* vertex, and therefore the proto-universal lifts of such cones in $\mathcal{S}$ still lie in $\mathcal{S}'$. $\square$

**Example 6.12.** Over a Kleisli sorted doctrine, the well-sorted coreflection of an LNL adjunction is the Kleisli adjunction of its comonad. Similarly, over the doctrine of linearly distributive categories with storage from Example 6.7, the well-sorted coreflection of a linearly distributive LNL adjunction (Proposition 3.15(iii)) is the double-Kleisli adjunction of its induced monad/comonad pair (Proposition 3.18).

Finally, we remark on what it takes for a doctrine map to preserve well-sortedness.

**Definition 6.13.** Let $\mathbb{D}_1$ and $\mathbb{D}_2$ be sorted doctrines. A doctrine map $\mathfrak{F} : \mathbb{D}_1 \rightarrow \mathbb{D}_2$ is **sorted** if it preserves primitive sorts, derived sorts, and sorting cones, and moreover for any derived sort $R$ of $\mathbb{D}_1$, any sorting $\mathbb{D}_2$-cone with vertex $F(R)$ is the image of some sorting $\mathbb{D}_1$-cone with vertex $R$.

**Proposition 6.14.** *If $\mathfrak{F} : \mathbb{D}_1 \rightarrow \mathbb{D}_2$ is a sorted doctrine map, then $\mathfrak{F}_*$ and $\mathfrak{F}^*$ from Proposition 5.8 preserve well-sortedness.*

*Proof.* For $\mathfrak{F}_*$, let $\pi : \mathcal{S} \rightarrow |\mathbb{D}_1|$ be a well-sorted $\mathbb{D}_1$-sketch, let $R$ be a derived $\mathbb{D}_2$-sort, and let $S \in (F\pi)^{-1}(R)$. Then $\pi(S)$ is a derived $\mathbb{D}_1$-sort. So since $\mathcal{S}$ is well-sorted, there is a proto-extremal lift of its sorting cone $G_R$ that maps the vertex to $S$. But by assumption, $FG_R$ is the sorting $\mathbb{D}_2$-cone of $F(R)$, while by definition this lift of it is also proto-extremal in $\mathfrak{F}_*(\mathcal{S})$. Thus, $\mathfrak{F}_*(\mathcal{S})$ is well-sorted.

For $\mathfrak{F}^*$, let $\pi : \mathcal{S} \rightarrow |\mathbb{D}_2|$ be a well-sorted $\mathbb{D}_2$-sketch and $R$ a derived $\mathbb{D}_1$-sort. An object of $\mathfrak{F}^*(\mathcal{S})$ over $R$ is an object $S \in \pi^{-1}(F(R))$. Since $F(R)$ is a derived $\mathbb{D}_2$-sort and $\mathcal{S}$ is well-sorted, there is a proto-extremal lift of its sorting cone $G_{F(R)}$ that maps the vertex to $S$. By assumption, $G_{F(R)}$ is the image of the sorting $\mathbb{D}_1$-cone $G_R$, and this proto-extremal lift of $G_{F(R)}$ induces a proto-extremal lift of $G_R$ to $\mathfrak{F}^*(\mathcal{S})$ mapping the vertex to $S$. Thus, $\mathfrak{F}^*(\mathcal{S})$ is well-sorted. $\square$

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:41

## 7. THE DOCTRINAL COMPLETION OF A SKETCH

We will now show that any $\mathbb{D}$-sketch can be completed to a $\mathbb{D}$-category in a universal way. Recall (see e.g. [AR94]) that an object $\mathcal{P}$ of a category is said to be **injective** with respect to a set of morphisms $\mathcal{I}$ if for any morphism $\mathcal{A} \to \mathcal{B}$ in $\mathcal{I}$, any morphism $\mathcal{A} \to \mathcal{P}$ can be extended to $\mathcal{B}$ (not necessarily uniquely):

![img-5.jpeg](img-5.jpeg)

The class of all $\mathcal{I}$-injective objects is called a **small-injectivity class** (“small-” since $\mathcal{I}$ is a set rather than a proper class). If we require the extensions to be *unique*, we obtain the related notions of **orthogonal** object and **small-orthogonality class**. In a category with pushouts, $\mathcal{P}$ is orthogonal to $\mathcal{A} \to \mathcal{B}$ if and only if it is injective with respect to $\mathcal{A} \to \mathcal{B}$ and its codiagonal $\mathcal{B} +_{\mathcal{A}}\mathcal{B} \to \mathcal{B}$; thus every small-orthogonality class is also a small-injectivity class.

**Theorem 7.1.** *If $\mathbb{D}$ is small, then the $\mathbb{D}$-complete sketches are a small-injectivity class in $\mathbb{D}$-Sketch.*

*Proof.* Given any $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$, we regard it as a $\mathbb{D}$-sketch in which the only proto-extremal cone is $G$ itself. We also regard its reduct as a $\mathbb{D}$-sketch via the composite $\partial\mathcal{C} \hookrightarrow \mathcal{C} \to |\mathbb{D}|$, with no proto-extremal cones at all. Then a $\mathbb{D}$-sketch $\mathcal{P}$ is precomplete if and only if it is injective to the inclusions of $\mathbb{D}$-sketches $\partial\mathcal{C} \hookrightarrow \mathcal{C}$.

Similarly, given any $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$, any expansion of it (Definition 4.14), and any extension of $G$ to $G_{\Psi} : \mathcal{C}_{/\Psi} \to |\mathbb{D}|$, we regard $\mathcal{C}_{/\Psi}$ and its corresponding pre-expansion $\partial(\mathcal{C}_{/\Psi})$ as $\mathbb{D}$-sketches via $G_{\Psi}$ and its restriction to $\partial(\mathcal{C}_{/\Psi})$, in which the only proto-extremal cone is $G$. Then a $\mathbb{D}$-sketch $\mathcal{P}$ is realized if and only if it is *orthogonal* to the set of inclusions of $\mathbb{D}$-sketches $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$, indexed over all $G$, $\Psi$, and $G_{\Psi}$.

Finally, given an abstract cone $\mathcal{C}$ with vertex $K$, let $\mathcal{C}_{\cong}$ denote the LNL polycategory that is $\mathcal{C}$ with an additional signed object $K'$ isomorphic to $K$. There is a fold map $\mathcal{C}_{\cong} \to \mathcal{C}$ that collapses $K$ and $K'$ both to $K$, which has two sections $s, s' : \mathcal{C} \to \mathcal{C}_{\cong}$ sending $K$ to $K$ and $K'$ respectively. If $G : \mathcal{C} \to \mathbb{D}$ is a $\mathbb{D}$-cone, we can regard $\mathcal{C}_{\cong}$ as a $\mathbb{D}$-sketch via the composite $\mathcal{C}_{\cong} \to \mathcal{C} \to |\mathbb{D}|$, in which both $s$ and $s'$ are proto-extremal. We can also regard it as a $\mathbb{D}$-sketch in which only $s$ is proto-extremal; we denote this sketch by $\mathcal{C}'_{\cong}$. Then a $\mathbb{D}$-sketch is saturated if and only if it is injective with respect to the set of inclusions of $\mathbb{D}$-sketches $\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong}$.

Let $\mathcal{I}_{\mathbb{D}}$ denote the set of all the morphisms

$$\partial\mathcal{C} \hookrightarrow \mathcal{C} \qquad \partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$$

$$\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong} \qquad \mathcal{C}_{/\Psi} +_{\partial(\mathcal{C}_{/\Psi})} \mathcal{C}_{/\Psi} \to \mathcal{C}_{/\Psi}$$

as $\mathcal{C}$ ranges over the $\mathbb{D}$-cones. Then a sketch is $\mathbb{D}$-complete if and only if it is injective with respect to $\mathcal{I}_{\mathbb{D}}$. $\square$

**Remark 7.2.** The proof shows that realized $\mathbb{D}$-sketches are actually a small-orthogonality class. Saturated $\mathbb{D}$-sketches are also a small-orthogonality class, since the inclusions $\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong}$ are epimorphic (being the identity on underlying LNL polycategories).

1:42

M. SHULMAN

Vol. 19:2

**Corollary 7.3.** *If $\mathbb{D}$ is small, then every $\mathbb{D}$-sketch $\mathcal{S}$ has a weak $\mathbb{D}$-reflection, i.e. a map $\mathcal{S} \to \tilde{\mathcal{S}}_{\mathbb{D}}$ such that $\tilde{\mathcal{S}}_{\mathbb{D}}$ is $\mathbb{D}$-complete and any map from $\mathcal{S}$ to a $\mathbb{D}$-complete sketch factors through $\tilde{\mathcal{S}}_{\mathbb{D}}$.*

*Proof.* This is a standard construction applying to any small-injectivity class, known as Quillen's small object argument; see e.g. [Hov99, 2.1.14] or [Hir03, 10.5.16] or [Rie14, 12.2.2]. Let $\mathcal{S}_0 = \mathcal{S}$. Given $\mathcal{S}_n$, define inductively $\mathcal{S}_{n+1}$ as the pushout

$$\begin{array}{ccc} \coprod_{\iota, u} \mathcal{A}_\iota & \longrightarrow & \mathcal{S}_n \\ \downarrow & \sqcap & \downarrow \\ \coprod_{\iota, u} \mathcal{B}_\iota & \longrightarrow & \mathcal{S}_{n+1} \end{array}$$

where the coproducts are over all $\iota : \mathcal{A} \to \mathcal{B}$ in the generating set $\mathcal{I}_{\mathbb{D}}$ and all $u : \mathcal{A} \to \mathcal{S}_n$. Continue the iteration into transfinite ordinals $n$ by taking colimits at limit stages. Then since $\mathbb{D}$-Sketch is locally presentable, there is a sufficiently large ordinal $\kappa$ such that any map $\mathcal{A} \to \mathcal{S}_\kappa$, for any $i : \mathcal{A} \to \mathcal{B}$, factors through $\mathcal{S}_n$ for some $n < \kappa$, and hence extends to $\mathcal{B}$ through $\mathcal{S}_{n+1}$. Thus, if we define $\tilde{\mathcal{S}}_{\mathbb{D}} = \mathcal{S}_\kappa$, it is $\mathbb{D}$-complete. Moreover, given a $\mathbb{D}$-complete sketch $\mathcal{T}$, we can extend a map $\mathcal{S} \to \mathcal{T}$ to each stage $\mathcal{S}_n$ inductively, using the completeness of $\mathcal{T}$ at successor stages. $\square$

The factorization $\tilde{\mathcal{S}}_{\mathbb{D}} \to \mathcal{T}$ constructed in Corollary 7.3 is not in general unique, but we will show that it is unique up to unique isomorphism.

There is an additional wrinkle, however: if $\mathbb{D}$ contains operations such as $-\circ, (\cdot)^*$ that are contravariant in some arguments, then $\mathbb{D}$-completion cannot be expected to behave well with respect to *noninvertible* 2-cells. Thus we have to formulate its universal property with respect to $\mathbb{D}$-Sketch$_g$, where $\mathcal{K}_g$ denotes the underlying (2,1)-category of a 2-category $\mathcal{K}$, containing only the invertible 2-cells.

**Theorem 7.4.** *For any small LNL doctrine $\mathbb{D}$ and $\mathbb{D}$-sketch $\mathcal{S}$, there is a $\mathbb{D}$-complete sketch $\tilde{\mathcal{S}}_{\mathbb{D}}$ and a map $\mathcal{S} \to \tilde{\mathcal{S}}_{\mathbb{D}}$ such that for any $\mathbb{D}$-complete sketch $\mathcal{P}$, the precomposition functor $\mathbb{D}$-Sketch$_g(\tilde{\mathcal{S}}_{\mathbb{D}}, \mathcal{P}) \to \mathbb{D}$-Sketch$_g(\mathcal{S}, \mathcal{P})$ is a surjective equivalence of categories. In particular, the sub-2-category of $\mathbb{D}$-complete sketches in $\mathbb{D}$-Sketch$_g$ (which, recall, is equivalent to $\mathbb{D}$-Cat$_g$) is pseudo-reflective.*

*Proof.* In Corollary 7.3, $\tilde{\mathcal{S}}_{\mathbb{D}}$ was constructed as a transfinite composite of pushouts of the generators. Since surjective equivalences are closed under pullbacks and inverse transfinite composites, it suffices (see e.g. [Hov99, 4.2.4]) to show that for any $\mathbb{D}$-complete sketch $\pi : \mathcal{P} \to |\mathbb{D}|$ and any morphism $\iota : \mathcal{A} \to \mathcal{B}$ in $\mathcal{I}_{\mathbb{D}}$, the induced map $\mathbb{D}$-Sketch$_g(\mathcal{B}, \mathcal{P}) \to \mathbb{D}$-Sketch$_g(\mathcal{A}, \mathcal{P})$ is a surjective equivalence. Since it is always surjective on objects, it remains to prove that it is fully faithful. Referring to the construction of $\mathcal{I}_{\mathbb{D}}$, there are four cases we need to consider.

When $\iota$ is an inclusion $\partial \mathcal{C} \hookrightarrow \mathcal{C}$ for some $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$, we must show that given two $\pi$-extremal lifts $H, K : \mathcal{C} \to \mathcal{P}$ of $G$, any isomorphism $\alpha : H' \cong K'$ between their reducts $H', K' : \partial \mathcal{C} \to \mathcal{P}$ can be uniquely extended to a compatible isomorphism $H \cong K$. By composing the transitions of $K$ with the components of $\alpha$ and their inverses (depending on the sign of the relevant signed object), we obtain the data for a pre-expansion of $H$ by a single object, namely the vertex of $K$. Thus, extremality of $H$ induces a map between the

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:43

vertices of $H$ and $K$ (with direction depending on the sign of that vertex). Similarly, we obtain a map in the other direction, and the two are inverses.

When $\iota$ is an inclusion $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$, we must show that given two expansions $H, K : \mathcal{C}_{/\Psi} \to \mathcal{P}$ of $\pi$-extremal lifts, any isomorphism $\alpha : H' \cong K'$ between their corresponding pre-expansions $H', K' : \partial(\mathcal{C}_{/\Psi}) \to \mathcal{P}$ is also an isomorphism $H \cong K$. Since the inclusion $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$ is bijective on objects, this is just an extra naturality condition with respect to the factorization morphism. But the two sides of this desired naturality square each fit into an expansion of $H$ whose expanders are those of $K$ composed with components of $\alpha$ or their inverses; hence they are equal.

Finally, when $\iota$ is a codiagonal $\mathcal{C}_{/\Psi} +_{\partial(\mathcal{C}_{/\Psi})} \mathcal{C}_{/\Psi} \to \mathcal{C}_{/\Psi}$ or an inclusion $\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong}$, full-faithfulness is automatic since these $\iota$'s are bijective on objects and full. $\square$

**Proposition 7.5.** *For any sorted doctrine $\mathbb{D}$ and any well-sorted $\mathbb{D}$-sketch $\mathcal{S}$, the completion $\widehat{\mathcal{S}}_{\mathbb{D}}$ is also well-sorted.*

*Proof.* Let $\mathcal{S}$ be well-sorted, and let $(\widehat{\mathcal{S}}_{\mathbb{D}})' \to \widehat{\mathcal{S}}_{\mathbb{D}}$ be the well-sorted coreflection of $\widehat{\mathcal{S}}_{\mathbb{D}}$. Since $\mathcal{S}$ is well-sorted, the map $\mathcal{S} \to \widehat{\mathcal{S}}_{\mathbb{D}}$ factors through $(\widehat{\mathcal{S}}_{\mathbb{D}})'$. But by Proposition 6.11, $(\widehat{\mathcal{S}}_{\mathbb{D}})'$ is $\mathbb{D}$-complete, so the universal property of $\widehat{\mathcal{S}}_{\mathbb{D}}$ induces a map $\widehat{\mathcal{S}}_{\mathbb{D}} \to (\widehat{\mathcal{S}}_{\mathbb{D}})'$ that is a section of the coreflection, up to isomorphism. This implies that $\widehat{\mathcal{S}}_{\mathbb{D}}$ is also well-sorted. $\square$

## 8. THE SEQUENT CALCULUS OF A DOCTRINE

Let $\mathbb{D}$ be an LNL doctrine and $\mathcal{S}$ an LNL polycategory with a map $\pi : \mathcal{S} \to |\mathbb{D}|$, which we regard as a $\mathbb{D}$-sketch with no proto-extremal cones. Then Theorem 7.4 implies that $\mathcal{S}$ generates a free $\mathbb{D}$-category $\widehat{\mathcal{S}}_{\mathbb{D}}$. We now extract a sequent calculus that presents such free $\mathbb{D}$-categories from the proof of Theorem 7.4.

For simplicity, for now we suppose that $\mathbb{D}$ is unsorted, $|\mathbb{D}|$ is subterminal, and all the cones of $\mathbb{D}$ are *discrete* (have no nonidentity abstract transitions) and also *finite*. This restriction on cones includes cones for universal morphisms, as in Definition 4.16, and also for finite products and coproducts, as in Definition 4.18. These are the primary universal properties that are traditionally considered in logic. Under these assumptions, we can replace the construction of Corollary 7.3 by the following simplified version.

- (i) First perform the small object argument starting at $\mathcal{S}_0 = \mathcal{S}$, using only the inclusions $\partial\mathcal{C} \hookrightarrow \mathcal{C}$ for $\mathbb{D}$-cones $\mathcal{C}$, and when $n > 0$ restricting the coproduct to include only the morphisms $u : \partial\mathcal{C} \to \mathcal{S}_n$ that do not factor through $\mathcal{S}_{n-1}$. After a countable iteration, this produces a precomplete sketch $\mathcal{S}_\omega$.
- (ii) Next perform the small object argument starting at $\mathcal{S}_\omega$, using only the inclusions $\partial(\mathcal{C}_{/\Psi}) \hookrightarrow \mathcal{C}_{/\Psi}$ and their codiagonals $\mathcal{C}_{/\Psi} +_{\partial(\mathcal{C}_{/\Psi})} \mathcal{C}_{/\Psi} \to \mathcal{C}_{/\Psi}$. After a further countable iteration, this produces a realized sketch $\mathcal{S}_{\omega+\omega}$. Moreover, since these inclusions and codiagonals are bijective on objects and each $\partial\mathcal{C}$ is discrete, $\mathcal{S}_{\omega+\omega}$ is still precomplete.
- (iii) Finally, perform one step of the small object argument using the map $\mathcal{C}'_{\cong} \hookrightarrow \mathcal{C}_{\cong}$. This is sufficient to produce a saturated sketch $\widehat{\mathcal{S}}_{\mathbb{D}} = \mathcal{S}_{\omega+\omega+1}$, which is still precomplete and realized, and hence $\mathbb{D}$-complete.

In particular, these changes make the argument completely constructive. (The negation in (i) may not seem constructive, but the inclusion of $\mathcal{S}_{n-1}$ into $\mathcal{S}_n$ is decidable on objects because each $\partial\mathcal{C} \hookrightarrow \mathcal{C}$ is.)

1:44

M. SHULMAN

Vol. 19:2

\[
\frac {A \in \mathcal {S} ^ {\tau}}{A \text {type} ^ {\tau}} \qquad \frac {\mathcal {C} \text {a} \mathbb {D} \text {-cone} \qquad \partial \mathcal {C} = \{r _ {1} ^ {\tau_ {1}} , \ldots , r _ {n} ^ {\tau_ {n}} \} \qquad R _ {1} \text {type} ^ {\tau_ {1}} \qquad \cdots \qquad R _ {n} \text {type} ^ {\tau_ {n}}}{\bigodot_ {\mathcal {C}} [ R _ {1} , \ldots , R _ {n} ] \text {type} ^ {\tau_ {\mathcal {C}}}}
\]

(A) Type-forming rules

\[
\frac {R \text {type} ^ {\tau}}{\vdash R ^ {-} , R ^ {+}} \qquad \frac {\vdash \Phi , K \qquad \vdash K ^ {\bullet} , \Psi}{\vdash \Phi , \Psi} \qquad \frac {\vdash \Psi \qquad \sigma : \Phi \to \Psi \text {a structural map}}{\vdash \Phi}
\]

(B) Structural rules

\[
\frac {f \in \mathcal {S} (\Phi)}{\vdash \Phi}
\]

(c) Generator rule

\[
\begin{array}{c} \mathcal {C} \text {a} \mathbb {D} \text {-cone with vertex} r ^ {\varepsilon} \qquad \partial \mathcal {C} = \{r _ {1} ^ {\tau_ {1}}, \ldots , r _ {n} ^ {\tau_ {n}} \} \\ R _ {1} \text {type} ^ {\tau_ {1}} \qquad \dots \qquad R _ {n} \text {type} ^ {\tau_ {n}} \qquad f \in \mathcal {C} (r _ {i _ {1}} ^ {\varepsilon_ {1}}, \ldots , r _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, r ^ {\varepsilon}) \text {an abstract projection} \\ \hline \vdash R _ {i _ {1}} ^ {\varepsilon_ {1}}, \ldots , R _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, \bigodot_ {\mathcal {C}} [ R _ {1}, \ldots , R _ {n} ] ^ {\varepsilon} \end{array}
\]

(D) Noninvertible logical rule

\[
\begin{array}{l} \mathcal {C} \text {   a   } \mathbb {D} \text {-cone with vertex   } r ^ {\varepsilon} \text {   of   class   } \tau_ {\mathcal {C}} \qquad \partial \mathcal {C} = \{r _ {1} ^ {\tau_ {1}}, \ldots , r _ {n} ^ {\tau_ {n}} \} \\ R _ {1} \text {type} ^ {\tau_ {1}} \quad \dots \quad R _ {n} \text {type} ^ {\tau_ {n}} \quad S _ {1} \text {type} ^ {\sigma_ {1}} \quad \dots \quad S _ {m} \text {type} ^ {\sigma_ {m}} \\ | \mathbb {D} | (\tau_ {\mathcal {C}} ^ {- \varepsilon}, \sigma_ {1} ^ {\eta_ {1}}, \dots , \sigma_ {m} ^ {\eta_ {m}}) \neq \emptyset \\ \left\{\vdash R _ {i _ {1}} ^ {\varepsilon_ {1}}, \dots , R _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, S _ {1} ^ {\eta_ {1}}, \dots , S _ {m} ^ {\eta_ {m}} \right\} _ {f \in \mathcal {C} (r _ {i _ {1}} ^ {\varepsilon_ {1}}, \dots , r _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, r ^ {\varepsilon}) \text {an abstract projection}} \\ \vdash \bigodot_ {\mathcal {C}} [ R _ {1}, \dots , R _ {n} ] ^ {- \varepsilon}, S _ {1} ^ {\eta_ {1}}, \dots , S _ {m} ^ {\eta_ {m}} \\ \end{array}
\]

(E) Invertible logical rule

FIGURE 2. LNL Sequent calculus

We can now describe \(\widehat{\mathcal{S}}_{\mathbb{D}}\) using a sequent calculus, defined formally in Figure 2. There are two classes of types, linear and nonlinear, written \(A\) type\(^{\mathrm{L}}\) and \(X\) type\(^{\mathrm{NL}}\). Generically, we write \(R\) type\(^{\tau}\) for an arbitrary class \(\tau \in \{\mathrm{L},\mathrm{NL}\}\). The first rule in Figure 2a says that every object of \(\mathcal{S}\) determines a type of the appropriate class.

By assumption, the reduct \(\partial \mathcal{C}\) of each \(\mathbb{D}\)-cone is a discrete LNL polycategory with finitely many objects. We assume the objects of each \(\partial \mathcal{C}\) are ordered as \(\{r_1^{\tau_1},\ldots ,r_n^{\tau_n}\}\), the notation meaning that \(r_i\) is of class \(\tau_{i}\), and the vertex \(k\) of class \(\tau_{\mathcal{C}}\). The second rule in Figure 2a says that every such cone induces an operation on types. The notation \(\bigodot_{\mathcal{C}}[R_1,\dots ,R_n]\) is chosen to be generic over the cone \(\mathcal{C}\), but for particular choices of \(\mathcal{C}\) we use the notations of Section 2, e.g. \(A\otimes B\), \(\mathsf{F}X\), \(X\times A\), \(A\& B\), etc.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:45

**Proposition 8.1.** *There is a bijection between the valid judgments $R \text{ type}^{\tau}$ and the $\tau$-objects of $\tilde{S}_{\mathbb{D}}$.*

*Proof.* Define the *height* of $R \text{ type}^{\tau}$ recursively: the height of an object of $\mathcal{S}$ is zero, while that of $\bigodot_{\mathcal{C}}[R_1, \ldots, R_n]$ is one more than the maximum height of $R_1, \ldots, R_n$. (If $n = 0$, the height of $\bigodot_{\mathcal{C}}[]$ is 1.) I claim that there is a bijection between the valid judgments $R \text{ type}^{\tau}$ of height $\le n$ and the $\tau$-objects of $\mathcal{S}_n$. This is true for $n = 0$. The objects of $\mathcal{S}_{n+1}$ are those of $\mathcal{S}_n$ plus a new vertex for each $u : \partial\mathcal{C} \to \mathcal{S}_n$ not factoring through $\mathcal{S}_{n-1}$. But the latter are the applications of the $\bigodot_{\mathcal{C}}$-rule with at least one premise of height $n$, hence whose conclusion has height $n + 1$. $\square$

We denote the sequents in entries-only style as $\vdash \Phi$, where $\Phi$ is an admissible list of signed types, defined analogously to the semantic case in Section 4. The structural rules are shown in Figure 2b. The first is the identity rule and the second is the cut rule. The third incorporates exchange for all types, plus contraction and weakening for nonlinear types, as in Section 4. Similarly, the generator rule in Figure 2c says that every morphism of $\mathcal{S}$ induces a derivation of a sequent.

We may write $\Theta \mid \Gamma \vdash \Delta$ for $\vdash \Theta^-, \Gamma^-, \Delta^+$, and $\Theta \vdash X$ for $\vdash \Theta^-, X^+$. In this notation, the identity and cut rules multifurcate into linear and nonlinear versions:

$$\begin{array}{l} \frac{A \text{ type}^{\text{L}}}{\cdot \mid A \vdash A} \qquad \frac{X \text{ type}^{\text{NL}}}{X \vdash X} \qquad \frac{\Upsilon \vdash X \qquad \Theta, X \vdash Y}{\Theta, \Upsilon \vdash Y} \\ \frac{\Theta' \mid \Gamma' \vdash \Delta', A \qquad \Theta \mid \Gamma, A \vdash \Delta}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta, \Delta'} \qquad \frac{\Upsilon \vdash X \qquad \Theta, X \mid \Gamma \vdash \Delta}{\Theta, \Upsilon \mid \Gamma \vdash \Delta}. \end{array}$$

We divide the logical rules into *invertible* (right rules for negative types and left rules for positive types) and *noninvertible* (left rules for negative types and right rules for positive types). The generic noninvertible rule is in Figure 2d. Here $\varepsilon$ and the $\varepsilon_j$'s are signs $+, -$. For instance, if $\mathcal{C}$ is the cone for $\otimes$, with objects $a, b$ and vertex $c$, there is one abstract projection $f \in \mathcal{C}(a^-, b^-, c^+)$ and the rule becomes

$$\frac{A \text{ type}^{\text{L}} \qquad B \text{ type}^{\text{L}}}{\cdot \mid A, B \vdash A \otimes B}.$$

If $\mathcal{C}$ is the cone for $\&$, with objects $a, b$ and vertex $c$, there are two abstract projections $f \in \mathcal{C}(a^+, c^-)$ and $g \in \mathcal{C}(b^+, c^-)$, and the rule becomes two:

$$\frac{A \text{ type}^{\text{L}} \qquad B \text{ type}^{\text{L}}}{\cdot \mid A \& B \vdash A} \qquad \frac{A \text{ type}^{\text{L}} \qquad B \text{ type}^{\text{L}}}{\cdot \mid A \& B \vdash B}.$$

The rules for the modalities are

$$\frac{X \text{ type}^{\text{NL}}}{X \mid \cdot \vdash \mathsf{F}X} \qquad \frac{A \text{ type}^{\text{L}}}{\mathsf{U}A \mid \cdot \vdash A} \qquad \frac{X \text{ type}^{\text{NL}}}{X \mid \not\perp X \vdash \cdot} \qquad \frac{A \text{ type}^{\text{L}}}{\cap A \mid A \vdash \cdot}$$

Unlike noninvertible rules in most common sequent calculi, ours does not build in a cut. But we can always apply a cut afterwards, since the latter is primitive in our system. (We leave cut-elimination for future study.) Since the modalities are the most novel aspect of this calculus, we list their derived cut-containing rules:

$$\frac{\Theta \vdash X}{\Theta \mid \cdot \vdash \mathsf{F}X} \qquad \frac{\Theta \mid \Gamma, A \vdash \Delta}{\Theta, \mathsf{U}A \mid \Gamma \vdash \Delta} \qquad \frac{\Theta \vdash X}{\Theta \mid \not\perp X \vdash \cdot} \qquad \frac{\Theta \mid \Gamma \vdash \Delta, A}{\Theta, \cap A \mid \Gamma \vdash \Delta}.$$

1:46

M. SHULMAN

Vol. 19:2

If $|\mathbb{D}| = \text{LNLMULTI}$, so $\Delta$ is a singleton, these rules for $\mathsf{F}$ and $\mathsf{U}$ specialize to the noninvertible rules of [Ben95]. If instead $|\mathbb{D}| = \text{CBPV}$, so $\Delta$ is a singleton and $\Gamma$ is empty, we obtain the rules of [Lev03].

**Proposition 8.2.** *There is a surjection from the derivations of $\vdash \Phi$ using only the structural, generator, and noninvertible rules to the hom-set $\mathcal{S}_{\omega}(\Phi)$.*

*Proof.* Such a function is defined by induction on derivations: the structural rules use that $\mathcal{S}_{\omega}$ is an LNL polycategory, the generator rule uses the functor $\mathcal{S} \to \mathcal{S}_{\omega}$, and the noninvertible rule uses the images of abstract projections under the proto-extremal cones of $\mathcal{S}_{\omega}$, which exist (by construction, in fact uniquely) since it is precomplete. We show inductively that it is surjective onto morphisms in $\mathcal{S}_{n}$.

For $n = 0$ this follows from the generator rule. Since $\mathcal{S}_{n+1}$ is a pushout, its morphisms are generated by the operations in an LNL polycategory (identities, composition, and structural actions) from those of $\mathcal{S}_{n}$ and those of the cones $\mathcal{C}$. The latter arise from the noninvertible rules, while the LNL polycategory operations are reflected by the structural rules.

Finally, the generic invertible rule is shown in figure Figure 2e, where $-\varepsilon$ reverses a sign. The requirement $|\mathbb{D}|(\tau_{\mathcal{C}}^{-\varepsilon}, \sigma_{1}^{\eta_{1}}, \ldots, \sigma_{m}^{\eta_{m}}) \neq \emptyset$ ensures that we do not produce sequents not allowed by $|\mathbb{D}|$, e.g. the universal properties of limits and colimits are restricted as necessary in an LNL multicategory. (Recall we are assuming $|\mathbb{D}|$ to be subterminal, so its nonempty homsets are singletons.)

For instance, if $\mathcal{C}$ is the cone for $\otimes$ as above, the rule becomes

$$\frac{\vdash A^{-}, B^{-}, \Psi}{\vdash (A \otimes B)^{-}, \Psi} = \frac{\Theta \mid \Gamma, A, B \vdash \Delta}{\Theta \mid \Gamma, A \otimes B \vdash \Delta}$$

while if $\mathcal{C}$ is the cone for $\&$ as above, the rule becomes

$$\frac{\vdash A^{+}, \Psi \quad \vdash B^{+}, \Psi}{\vdash (A \& B)^{+}, \Psi} = \frac{\Theta \mid \Gamma \vdash \Delta, A \quad \Theta \mid \Gamma \vdash \Delta, B}{\Theta \mid \Gamma \vdash \Delta, A \& B}.$$

Similarly, the rules for other common connectives such as $-\circ, \oplus, \mathbb{1}, \bot, \mathcal{X}, \times, \to, 1$ specialize to the usual ones for classical or intuitionistic multiplicative-additive linear logic or intuitionistic nonlinear logic.

For the modalities, the invertible rules are:

$$\frac{\Theta, X \mid \Gamma \vdash \Delta}{\Theta \mid \Gamma, \mathsf{F}X \vdash \Delta} \qquad \frac{\Theta \mid \cdot \vdash A}{\Theta \vdash \mathsf{U}A} \qquad \frac{\Theta, X \mid \Gamma \vdash \Delta}{\Theta \mid \Gamma \vdash \Delta, \bot X} \qquad \frac{\Theta \mid A \vdash \cdot}{\Theta \vdash \cap A}$$

As before, if $|\mathbb{D}| = \text{LNLMULTI}$ or $|\mathbb{D}| = \text{CBPV}$, these rules for $\mathsf{F}$ and $\mathsf{U}$ specialize to those of [Ben95] or [Lev03] respectively. Similarly, the rules for $\bullet$ and $\rtimes$, with appropriate cuts added:

$$\frac{\Theta \vdash A \bullet B \quad \Theta' \mid \Gamma \vdash A}{\Theta, \Theta' \mid \Gamma \vdash B} \qquad \frac{\Theta \mid A \vdash B}{\Theta \vdash A \bullet B}$$

$$\frac{\Theta \vdash X \quad \Theta' \mid \Gamma \vdash A}{\Theta, \Theta' \mid \Gamma \vdash X \rtimes A} \qquad \frac{\Theta \mid \Gamma \vdash X \rtimes A \quad \Theta', X \mid \Gamma', A \vdash \Delta}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta}$$

specialize when $|\mathbb{D}| = \text{ECBV}$ (so $\Gamma$ is a singleton and $\Gamma' = \emptyset$) to those of [MS14] (modulo changes of notation, and additive maintenance for the nonlinear context).

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:47

**Proposition 8.3.** *There is a surjection from derivations of* $\vdash \Phi$, *in the full sequent calculus of Figure 2, to the hom-set* $\widehat{\mathcal{S}}_{\mathbb{D}}(\Phi)$.

*Proof.* As before, the function is defined inductively on derivations, with the invertible logical rule resulting from realizedness. Also as before, we prove surjectivity onto $\mathcal{S}_{\omega+n}$ by induction. The base case $\mathcal{S}_{\omega}$ is Proposition 8.2; while the morphisms of $\mathcal{S}_{\omega+n+1}$ are generated by the LNL polycategory operations (structural rules) from those of $\mathcal{S}_{\omega+n}$ and the factorizations in each $\mathcal{C}_{/\Psi}$ (invertible logical rules). $\square$

The equivalence relation on derivations of $\vdash \Phi$ whose quotient is $\widehat{\mathcal{S}}_{\mathbb{D}}(\Phi)$ can also be described syntactically. It is generated by the composition operation of $\mathcal{S}$, the structural axioms of an LNL polycategory, the principal “$\beta$-reduction” rule that reduces a cut of the form

$$\frac{\dots \quad f \in \mathcal{C}(r_{i_1}^{\varepsilon_1}, \dots, r_{i_\ell}^{\varepsilon_\ell}, r^\varepsilon) \text{ abs. proj.}}{\vdash R_{i_1}^{\varepsilon_1}, \dots, R_{i_\ell}^{\varepsilon_\ell}, \bigodot_{\mathcal{C}}[R_1, \dots, R_n]^{\varepsilon}} \quad \frac{\dots \quad \{\vdash R_{i_1}^{\varepsilon_1}, \dots, R_{i_\ell}^{\varepsilon_\ell}, \Psi\}_{f \text{ abs. proj.}}}{\vdash \bigodot_{\mathcal{C}}[R_1, \dots, R_n]^{-\varepsilon}, \Psi}$$
$$\vdash R_{i_1}^{\varepsilon_1}, \dots, R_{i_\ell}^{\varepsilon_\ell}, \Psi$$

to the derivation of $\vdash R_{i_1}^{\varepsilon_1}, \dots, R_{i_\ell}^{\varepsilon_\ell}, \Psi$ on the right that is indexed by the specific abstract projection $f$ specified on the left, and the “$\eta$-conversion” rule that two derivations of $\vdash \bigodot_{\mathcal{C}}[R_1, \dots, R_n]^{-\varepsilon}, S_1^{\eta_1}, \dots, S_m^{\eta_m}$ are equal if they become equal upon cutting with the noninvertible rule $\vdash R_{i_1}^{\varepsilon_1}, \dots, R_{i_\ell}^{\varepsilon_\ell}, \bigodot_{\mathcal{C}}[R_1, \dots, R_n]^{\varepsilon}$.

**Remark 8.4.** We have constructed $\widehat{\mathcal{S}}_{\mathbb{D}}$ by a categorical iterative procedure, and then shown that we can extract a sequent calculus from this construction. As pointed out by a referee, we could also have specified the sequent calculus first and then used it to construct the free $\mathbb{D}$-completion $\widehat{\mathcal{S}}_{\mathbb{D}}$. We regard the *equivalence* between the two as the most interesting observation. It is ultimately a matter of personal preference which side of the equivalence one prefers to start from, although the categorical approach does have the advantage of quotienting the morphisms by the appropriate equivalence relation automatically.

We have described this sequent calculus for a restricted class of doctrines, to reduce the syntactic bureaucracy. However, analogous calculi can be formulated for any doctrine, with the following modifications.

If $\mathbb{D}$ contains infinite cones, its sequent calculus has infinitely many rules, some with infinitely many premises. This is hard to implement, of course, but mathematically unproblematic. If $\mathbb{D}$ contains non-discrete cones, the type-formation rules have sequents and equalities of sequents as premises. Thus both judgments and their equalities are mutually inductive, as in a dependent type theory.

If $|\mathbb{D}|$ is not subterminal, then the syntactic classes of types must be indexed by objects of $|\mathbb{D}|$, and the sequents must likewise be indexed by morphisms of $|\mathbb{D}|$. The result is a “fibrational” calculus similar to that of [LSR17], though without 2-cells in the “mode theory” $|\mathbb{D}|$. For instance, if $|\mathbb{D}| = \text{PLMULTI}$ as in Remark 2.4, each sequent is labeled by a permutation of its context; this essentially serves to neuter the exchange rule, leading to a variant of ordered logic. Similarly, if $|\mathbb{D}| = \text{LINPOL}$ or LNLPOL as in Example 5.4, each linear type is labeled as positive or negative.

Finally, if $\mathbb{D}$ is sorted and $\mathcal{S}$ lies only over primitive sorts, we can omit the syntactic classes of types corresponding to derived sorts, or equivalently consider the action of sorting cones to be an implicit coercion. In addition, in this case usually some of the sequents will

1:48

M. SHULMAN

Vol. 19:2

be redundant, corresponding to hom-sets that are always canonically isomorphic to some other hom-sets, and can be omitted from the syntax.

For example, a Kleisli sorted doctrine with $|\mathbb{D}| = \text{LNLMULTI}$ yields split-context calculi for intuitionistic linear logic like those of [Bar96, Wad94], with only one class of types that can appear in both parts of the context. Types in the nonlinear part have an implicit application of $\mathsf{U}$, so it makes sense to change notation and write $\mathsf{FA}$ as $!A$. Moreover, since $\mathcal{P}(\Theta; \mathsf{UA}) \cong \mathcal{P}(\Theta \mid ; A)$, the nonlinear morphisms are determined by the linear ones; thus we can dispense with the nonlinear sequents entirely, essentially defining them by the invertible rule for $\mathsf{U}$. The remaining logical rules for the exponentials then become:

$$\frac{\Theta \mid \cdot \vdash A}{\Theta \mid \cdot \vdash !A} \qquad \frac{\Theta, A \mid \Gamma \vdash \Delta}{\Theta \mid \Gamma, !A \vdash \Delta} \qquad \frac{\Theta \mid \Gamma, A \vdash \Delta}{\Theta, A \mid \Gamma \vdash \Delta}$$

The first two appear verbatim in [Bar96, Wad94], while the third is admissible [Bar96, Lemma 2.5]. The cut rule that mixes linear and nonlinear sequents also has to be restated in this notation, alongside the one for purely linear sequents:

$$\frac{\Theta' \mid \Gamma' \vdash \Delta', A \quad \Theta \mid \Gamma, A \vdash \Delta}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta, \Delta'} \qquad \frac{\Upsilon \mid \cdot \vdash A \quad \Theta, A \mid \Gamma \vdash \Delta}{\Theta, \Upsilon \mid \Gamma \vdash \Delta}.$$

These cut rules both appear in [Bar96, Lemma 3.1] (“Linear Cut” and “Intuitionistic Cut”) and in [Wad94] (“Cut” and the derivable “Cut-Int”).

Something similar happens in [EMS12] with $|\mathbb{D}| = \text{CBPV}$, although in this case the computation types are merely *included* in the value types by an implicit $\mathsf{U}$, rather than identified with them. This includes the above rules for $!A$ (meaning $\mathsf{FA}$) with $\Gamma = \emptyset$, and the (arity-restricted, cut-including) rules for $\to\circ$ (their “$\to$”):

$$\frac{\Theta \vdash X \quad \Theta' \mid \Gamma \vdash X \to\circ B}{\Theta, \Theta' \mid \Gamma \vdash B} \qquad \frac{\Theta, X \mid \Gamma \vdash B}{\Theta \mid \Gamma \vdash X \to\circ B}.$$

Likewise, for Example 6.9 with $|\mathbb{D}| = \text{SYMSKEW}$, the rules for restricted $\otimes$ and $\to\circ$ (with one tight input — the “stoup” — and the other loose) specialize to those of [UVZ18, UVZ20, Vel21, UVW22].

As a final example, in the double-Kleisli sorted doctrine of Example 6.7, we can write the sequents as $\Theta \mid \Gamma \vdash \Delta \mid \Upsilon$, where $\Theta$ and $\Upsilon$ consist of types lying over the “left-hand” and “right-hand” derived sorts respectively. Types in $\Theta$ have an implicit $\mathsf{U}$ and types in $\Upsilon$ have an implicit $\Pi$, so we write $\mathsf{F}$ and $\mathsf{J}$ as $!$ and $?$ respectively. Again we can define the nonlinear sequents by the invertible rules for $\mathsf{U}$ and $\Pi$ — although when translating a nonlinear sequent $\Theta, \Upsilon \vdash A$ in this way, we have to pay attention to whether $A$ is being regarded as a left-hand type or a right-hand type: in the former case the sequent becomes $\Theta \mid \cdot \vdash A \mid \Upsilon$, while in the latter case it becomes $\Theta \mid A \vdash \cdot \mid \Upsilon$ (due to the different universal properties of $\mathsf{U}$ and $\Pi$). The remaining logical rules then become:

$$\frac{\Theta \mid \cdot \vdash A \mid \Upsilon}{\Theta \mid \cdot \vdash !A \mid \Upsilon} \qquad \frac{\Theta, A \mid \Gamma \vdash \Delta \mid \Upsilon}{\Theta \mid \Gamma, !A \vdash \Delta \mid \Upsilon} \qquad \frac{\Theta \mid \Gamma, A \vdash \Delta \mid \Upsilon}{\Theta, A \mid \Gamma \vdash \Delta \mid \Upsilon}$$
$$\frac{\Theta \mid A \vdash \cdot \mid \Upsilon}{\Theta \mid ?A \vdash \cdot \mid \Upsilon} \qquad \frac{\Theta \mid \Gamma \vdash \Delta \mid \Upsilon, A}{\Theta \mid \Gamma \vdash \Delta, ?A \mid \Upsilon} \qquad \frac{\Theta \mid \Gamma \vdash \Delta, A \mid \Upsilon}{\Theta \mid \Gamma \vdash \Delta \mid \Upsilon, A}$$

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:49

and the cut rules multifurcate further into:

$$\frac{\Theta' \mid \Gamma' \vdash \Delta', A \mid \Upsilon' \quad \Theta \mid \Gamma, A \vdash \Delta \mid \Upsilon}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta, \Delta' \mid \Upsilon, \Upsilon'}$$

$$\frac{\Theta' \mid \cdot \vdash A \mid \Upsilon' \quad \Theta, A \mid \Gamma \vdash \Delta \mid \Upsilon}{\Theta, \Theta' \mid \Gamma \vdash \Delta \mid \Upsilon, \Upsilon'} \quad \frac{\Theta' \mid A \vdash \cdot \mid \Upsilon' \quad \Theta \mid \Gamma \vdash \Delta \mid \Upsilon, A}{\Theta, \Theta' \mid \Gamma \vdash \Delta \mid \Upsilon, \Upsilon'}.$$

These are all precisely the relevant logical and structural rules of [Gir93].

## 9. ADJUNCTIONS INDUCED BY DOCTRINE MAPS

Our last goal is to show that a doctrine map $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ induces a pseudo 2-adjunction relating $\mathbb{D}_1$-categories to $\mathbb{D}_2$-categories, combining the adjunctions from Proposition 5.8 and Theorem 7.4.

**Theorem 9.1.** *For any morphism $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ of small doctrines, there is an induced pseudo 2-adjunction*

$$\widehat{\mathfrak{F}}_*: \mathbb{D}_1\text{-Cat}_g \rightleftarrows \mathbb{D}_2\text{-Cat}_g: \widehat{\mathfrak{F}}^*.$$

*Proof.* Identifying $\mathbb{D}_i$-categories with $\mathbb{D}_i$-complete sketches, we define $\widehat{\mathfrak{F}}^*$ to be the $\mathfrak{F}^*$ from Proposition 5.8 restricted to $\mathbb{D}_2$-complete inputs. This takes values in $\mathbb{D}_1$-complete sketches because the $\mathfrak{F}_*$ from Proposition 5.8 maps $\mathcal{I}_{\mathbb{D}_1}$ into $\mathcal{I}_{\mathbb{D}_2}$, up to isomorphism. Now we can define $\widehat{\mathfrak{F}}_*(\mathcal{S}) = (\widehat{\mathfrak{F}_*\mathcal{S}})_{\mathbb{D}_2}$, and compute

$$\begin{aligned} \mathbb{D}_2\text{-Cat}_g(\widehat{\mathfrak{F}}_*(\mathcal{S}), \mathcal{T}) &= \mathbb{D}_2\text{-Cat}_g(\widehat{(\mathfrak{F}_*\mathcal{S})}_{\mathbb{D}_2}, \mathcal{T}) \simeq \mathbb{D}_2\text{-Sketch}_g(\mathfrak{F}_*\mathcal{S}, \mathcal{T}) \\ &\cong \mathbb{D}_1\text{-Sketch}_g(\mathcal{S}, \mathfrak{F}^*\mathcal{T}) \cong \mathbb{D}_1\text{-Cat}_g(\mathcal{S}, \widehat{\mathfrak{F}}^*\mathcal{T}). \end{aligned}$$

**Theorem 9.2.** *For any sorted map $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ of small sorted doctrines, there is an induced pseudo 2-adjunction*

$$\widetilde{\mathfrak{F}}_*: \mathbb{D}_1\text{-sCat}_g \rightleftarrows \mathbb{D}_2\text{-sCat}_g: \widetilde{\mathfrak{F}}^*.$$

*Proof.* It suffices to show that both functors in Theorem 9.1 preserve well-sortedness. For $\widehat{\mathfrak{F}}^* = \mathfrak{F}^*$ this follows from Proposition 6.14. For $\widehat{\mathfrak{F}}_*$, let $\mathcal{S}$ be a well-sorted $\mathbb{D}_1$-complete sketch. By Proposition 6.14, $\mathfrak{F}_*(\mathcal{S})$ is a well-sorted (incomplete) $\mathbb{D}_2$-sketch; thus by Proposition 7.5, $\widehat{\mathfrak{F}}_*(\mathcal{S}) = (\widehat{\mathfrak{F}_*\mathcal{S}})_{\mathbb{D}_2}$ is also well-sorted.

**Remark 9.3.** If $\mathbb{D}_2$ (hence also $\mathbb{D}_1$) contains only "totally covariant" operations, then Theorems 9.1 and 9.2 extend to pseudo 2-adjunctions $\mathbb{D}_1\text{-Cat} \rightleftarrows \mathbb{D}_2\text{-Cat}$ and $\mathbb{D}_1\text{-sCat} \rightleftarrows \mathbb{D}_2\text{-sCat}$ including the noninvertible 2-cells.

We conclude with examples. In fact, nearly all the obvious forgetful functors between classes of LNL polycategories discussed in Section 3 are of the form $\widehat{\mathfrak{F}}^*$ for some (sorted) doctrine map $\mathfrak{F}$, and therefore have left pseudo-adjoints.

To start with, we consider maps between doctrines that have no cones. These induce $\widehat{\mathfrak{F}}^*$ functors including the following.

- The underlying LNL multicategory of an LNL polycategory.
- The underlying cartesian multicategory, and the underlying symmetric polycategory, of an LNL multicategory or LNL polycategory.

1:50

M. SHULMAN

Vol. 19:2

- The underlying symmetric multicategory of a symmetric polycategory, LNL multicategory, or LNL polycategory.

Thus, all of these forgetful functors have left pseudo-adjoints, which extend to non-invertible 2-cells as in Remark 9.3.

By adding appropriate cones to the doctrines, we obtain more $\hat{\mathfrak{F}}^*$ functors, such as the following. In each case we must check that the putative doctrine map actually preserves the specified cones. This basically means that every specified kind of universal property in the domain doctrine is also specified in the codomain, which is essentially just the assertion that the forgetful functor in question exists.

- The underlying symmetric monoidal category of a linearly distributive category.
- The underlying closed symmetric monoidal category of a $*$-autonomous category. To represent this using a doctrine morphism, we need to explicitly include a $\rightarrow$-cone in the doctrine for $*$-autonomous categories (to be the image of the $\rightarrow$-cone in the doctrine for closed symmetric monoidal categories). Since internal-homs can be derived from duals, and hence are automatically preserved by $*$-autonomous functors, this yields an equivalent 2-category of $\mathbb{D}$-categories.
- The underlying linearly distributive category of a $*$-autonomous category. As in the previous example, for this we need to include redundant $\Upsilon$- and $\perp$-cones in the doctrine for $*$-autonomous categories.
- The underlying symmetric monoidal category, and the underlying cartesian monoidal category, of an LNL adjunction.
- The underlying $*$-autonomous category, and the underlying cartesian monoidal category, of a $*$-autonomous LNL adjunction.
- The underlying CBPV pre-structure of an LNL adjunction, the underlying EEC+ model of a closed LNL adjunction with products and coproducts, and so on.

Thus, all of these forgetful functors have left pseudo-adjoints as well. Those with no contravariant operations (such as $\rightarrow$ and $(\cdot)^*$) extend to non-invertible 2-cells as in Remark 9.3. We can also add any desired limits and colimits to these doctrines.

Finally, we consider sorted maps of doctrines containing some derived sorts. In the simplest case, the domain doctrine has all sorts primitive, in which case a doctrine map is sorted just when it maps every sort to a primitive one. This yields $\hat{\mathfrak{F}}^*$ functors such as the following.

- The underlying (closed) symmetric monoidal category of a (closed) symmetric monoidal category with a linear exponential comonad.
- The underlying linearly distributive category of a linearly distributive category with storage.
- The underlying (symmetric) multicategory of a (symmetric) skew multicategory.

If the domain has primitive sorts, we have to check the rest of Definition 6.13. This yields $\hat{\mathfrak{F}}^*$ functors such as the following, all with left pseudo-adjoints.

- The underlying symmetric monoidal category with linear exponential comonad of a linearly distributive category with storage. Here the unique derived (nonlinear) sort in the domain maps to the derived nonlinear sort of left-hand objects in the codomain (see Example 6.7).
- The underlying linearly distributive category with storage of a $*$-autonomous category with storage.

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:51

- The underlying (symmetric) skew monoidal category of a lax (symmetric) monoidal comonad, as in [Szl12, Definition 7.4] or [Vel21, Example 2]. Here the underlying functor of the doctrine map SYMSKEW → SMADJ is defined by L → P and T → N, where SMADJ has P derived and N primitive.

# ACKNOWLEDGMENTS

I would like to thank Robin Cockett, Max New, Paul Blain Levy, Noam Zeilberger, Christine Tasson, and Martin Hyland for helpful conversations and comments, and Nicolas Blanco for a careful reading and very helpful suggestions. I would also like to thank the referees for very helpful suggestions.

# REFERENCES

[AR94] Jiří Adámek and Jiří Rosický. Locally presentable and accessible categories, volume 189 of London Mathematical Society Lecture Note Series. Cambridge University Press, Cambridge, 1994. (Cited on p. 41)
[Bar79] Michael Barr. *-autonomous categories*, volume 752 of Lecture Notes in Mathematics. Springer, 1979. (Cited on p. 9)
[Bar91] Michael Barr. *-autonomous categories and linear logic. Mathematical Structures in Computer Science, 1(2):159–178, 1991. doi:10.1017/S0960129500001274. (Cited on p. 9)
[Bar96] Andrew Barlow. Dual intuitionistic linear logic. Technical report, University of Edinburgh, LFCS Report Series, 1996. (Cited on pp. 3, 7, 14, 18, and 48)
[BBdPH92] Nick Benton, Gavin Bierman, Valeria de Paiva, and Martin Hyland. Term assignment for intuitionistic linear logic. Technical Report 262, University of Cambridge Computer Laboratory, 1992. (Cited on p. 15)
[BCS96] R. F. Blute, J. R. B. Cockett, and R. A. G. Seely, ! and ? — storage as tensorial strength. Mathematical Structures in Computer Science, 6(4):313–351, 1996. doi:10.1017/S0960129500001055. (Cited on pp. 2, 21, 22, and 23)
[Ben95] P. N. Benton. A mixed linear and non-linear logic: Proofs, terms and models. In Leszek Pacholski and Jerzy Tiuryn, editors, Computer Science Logic, pages 121–135. Springer Berlin Heidelberg, 1995. (Cited on pp. 2, 3, 7, 14, 15, 16, and 46)
[BL18] John Bourke and Stephen Lack. Skew monoidal categories and skew multicategories. Journal of Algebra, 506:237–266, 2018. doi:10.1016/j.jalgebra.2018.02.039. (Cited on p. 38)
[BL20] John Bourke and Stephen Lack. Braided skew monoidal categories. Theory and Applications of Categories, 35(2):19–63, 2020. (Cited on p. 38)
[BZ20] Nicolas Blanco and Noam Zeilberger. Bifibrations of polycategories and classical linear logic. Mathematical Foundations of Programming Semantics (MFPS), 2020. (Cited on pp. 3, 7, 8, 9, 25, 26, and 27)
[CFMM16] Pierre-Louis Curien, Marcelo Fiore, and Guillaume Munch-Maccagnoni. A theory of effects and resources: Adjunction models and polarised calculi. SIGPLAN Not., 51(1):44–56, January 2016. doi:10.1145/2914770.2837652. (Cited on pp. 20 and 34)
[CGR14] Eugenia Cheng, Nick Gurski, and Emily Riehl. Cyclic multicategories, multivariable adjunctions and mates. Journal of K-Theory, 13(2):337–396, 2014. doi:10.1017/is013012007jkt250. (Cited on p. 6)
[CLW93] Aurelio Carboni, Stephen Lack, and R.F.C. Walters. Introduction to extensive and distributive categories. J. Pure Appl. Algebra, 84(2):145–158, 1993. (Cited on p. 19)
[CS97] Robin Cockett and Robert Seely. Weakly distributive categories. Journal of Pure and Applied Algebra, 114(2):133–173, 1997. Corrected version available at https://www.math.mcgill.ca/rags/linear/wdc-fix.pdf. (Cited on pp. 8, 9, 21, and 22)
[CS10] G.S.H. Cruttwell and Michael Shulman. A unified framework for generalized multicategories. Theory Appl. Categ., 24:580–655, 2010. arXiv:0907.2460. (Cited on p. 4)

1:52

M. SHULMAN

Vol. 19:2

[DCH21] Gabriel C. Drummond-Cole and Philip Hackney. Dwyer-Kan homotopy theory for cyclic operads. Proceedings of the Edinburgh Mathematical Society, 64(1):29-58, 2021. arxiv:1809.06322. doi:10.1017/S0013091520000267. (Cited on p. 6)
[EMS12] Jeff Egger, Rasmus Ejlers Møgelberg, and Alex Simpson. The enriched effect calculus: syntax and semantics. Journal of Logic and Computation, 24(3):615-654, 06 2012. doi:10.1093/logcom/exs025. (Cited on pp. 20 and 48)
[Gar08] Richard Garner. Polycategories via pseudo-distributive laws. Adv. Math., 218(3):781-827, 2008. (Cited on p. 4)
[Gir93] Jean-Yves Girard. On the unity of logic. Annals of Pure and Applied Logic, 59(3):201-217, 1993. doi:10.1016/0168-0072(93)90093-S. (Cited on pp. 3, 7, and 49)
[GK95] E. Getzler and M. M. Kapranov. Cyclic operads and cyclic homology. In Geometry, topology, & physics, Conf. Proc. Lecture Notes Geom. Topology, IV, pages 167-201. Int. Press, Cambridge, MA, 1995. (Cited on p. 6)
[Has05] Masahito Hasegawa. Classical linear logic of implications. Mathematical. Structures in Comp. Sci., 15(2):323-342, April 2005. doi:10.1017/S0960129504004621. (Cited on p. 18)
[Her00] Claudio Hermida. Representable multicategories. Adv. Math., 151(2):164-225, 2000. (Cited on p. 2)
[Her04] Claudio Hermida. Vibrations for abstract multicategories. Fields Institute Communications, 07 2004. doi:10.1090/fic/043/11. (Cited on pp. 3 and 25)
[Hir03] Philip S. Hirschhorn. Model Categories and their Localizations, volume 99 of Mathematical Surveys and Monographs. American Mathematical Society, 2003. (Cited on p. 42)
[Hov99] Mark Hovey. Model Categories, volume 63 of Mathematical Surveys and Monographs. American Mathematical Society, 1999. (Cited on p. 42)
[HRY19] Philip Hackney, Marcy Robertson, and Donald Yau. Higher cyclic operads. Algebraic & Geometric Topology, 19:863-940, 2019. (Cited on p. 6)
[HS03] Martin Hyland and Andrea Schalk. Glueing and orthogonality for models of linear logic. Theoretical Computer Science, 294(1):183-231, 2003. Category Theory and Computer Science. doi:10.1016/S0304-3975(01)00241-9. (Cited on p. 15)
[HT21] Martin Hyland and Christine Tasson. The linear-non-linear substitution 2-monad. In David I. Spivak and Jamie Vicary, editors, Proceedings of the 3rd Annual International Applied Category Theory Conference 2020, Cambridge, USA, 6-10th July 2020, volume 333 of Electronic Proceedings in Theoretical Computer Science, pages 215-229. Open Publishing Association, 2021. arXiv:2005.09559. doi:10.4204/EPTCS.333.15. (Cited on pp. 2, 4, 5, and 18)
[Hyl02] J.M.E. Hyland. Proof theory in the abstract. Annals of Pure and Applied Logic, 114:43-78, 2002. (Cited on p. 6)
[Koc71] Anders Kock. Closed categories generated by commutative monads. J. Austral. Math. Soc., 12:405-424, 1971. (Cited on p. 18)
[Koc72] Anders Kock. Strong functors and monoidal monads. Arch. Math. (Basel), 23:113-120, 1972. (Cited on p. 18)
[Kos05] Jürgen Koslowski. A monadic approach to polycategories. Theory Appl. Categ., 14:No. 7, 125-156 (electronic), 2005. (Cited on p. 6)
[Laf88] Yves Lafont. Logiques, catégories & machines: implantation de langages de programmation guidée par la logique catégorique. PhD thesis, Paris 7, 1988. (Cited on p. 17)
[Lam69] Joachim Lambek. Deductive systems and categories. II. Standard constructions and closed categories. In Category Theory, Homology Theory and their Applications, I (Battelle Institute Conference, Seattle, Wash., 1968, Vol. One), pages 76-122. Springer, Berlin, 1969. (Cited on p. 2)
[Lei04] Tom Leinster. Higher operads, higher categories, volume 298 of London Mathematical Society Lecture Note Series. Cambridge University Press, Cambridge, 2004. (Cited on p. 2)
[Lev03] Paul Blain Levy. Adjunction models for call-by-push-value with stacks. Electronic Notes in Theoretical Computer Science, 69:248-271, 2003. CTCS'02, Category Theory and Computer Science. doi:10.1016/S1571-0661(04)80568-1. (Cited on pp. 19 and 46)
[Lev04] Paul Blain Levy. Call-By-Push-Value: A Functional/Imperative Synthesis (Semantics Structures in Computation, V. 2). Kluwer Academic Publishers, USA, 2004. (Cited on p. 39)

Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:53

[LSR17] Daniel R. Licata, Michael Shulman, and Mitchell Riley. A fibrational framework for substructural and modal logics. Formal Structures for Computation and Deduction, 2017. (Cited on pp. 3, 25, 27, and 47)
[Man12] Oleksandr Manzyuk. Closed categories vs. closed multicategories. Theory and Applications of Categories, 26(5):132–175, 2012. (Cited on p. 2)
[MdPR00] Maria Emilia Maietti, Valeria de Paiva, and Eike Ritter. Categorical models for intuitionistic and linear type theory. In Jerzy Tiuryn, editor, Foundations of Software Science and Computation Structures, pages 223–237. Springer Berlin Heidelberg, 2000. (Cited on p. 18)
[Mel09] Paul-André Mellès. Categorical semantics of linear logic. In Interactive Models of Computation and Program Behaviour, Panoramas et Synthèses 27, Société Mathématique de France, pages 1–196, 2009. (Cited on pp. 15 and 16)
[MM13] Guillaume Munch-Maccagnoni. Syntax and Models of a non-Associative Composition of Programs and Proofs. Theses, Université Paris-Diderot - Paris VII, December 2013. (Cited on p. 39)
[MS14] Rasmus Ejlers Møgelberg and Sam Staton. Linear usage of state. Logical Methods in Computer Science, Volume 10, Issue 1, March 2014. doi:10.2168/LMCS-10(1:17)2014. (Cited on pp. 20 and 46)
[MTT18] Paul-André Mellès, Nicolas Tabareau, and Christine Tasson. An explicit formula for the free exponential modality of linear logic. Mathematical Structures in Computer Science, 28(7):1253–1286, 2018. doi:10.1017/S0960129516000426. (Cited on p. 17)
[Pas04] Craig Antonio Pastro. ΣΠ-polycategories, additive linear logic, and process semantics. Master’s thesis, University of Calgary, 2004. arXiv:math/0312422. (Cited on p. 12)
[PR97] John Power and Edmund Robinson. Premonoidal categories and notions of computation. Math. Structures Comput. Sci., 7(5):453–468, 1997. Logic, domains, and programming languages (Darmstadt, 1995). doi:10.1017/S0960129597002375. (Cited on p. 39)
[PT99] John Power and Hayo Thielecke. Closed Freyd- and κ-categories. In Jiří Wiedermann, Peter van Emde Boas, and Mogens Nielsen, editors, Automata, Languages and Programming, pages 625–634, Berlin, Heidelberg, 1999. Springer Berlin Heidelberg. (Cited on p. 39)
[Rie14] Emily Riehl. Categorical homotopy theory, volume 24 of New mathematical monographs. Cambridge University Press, 2014. (Cited on p. 42)
[Sea13] Gavin J. Seal. Tensors, monads, and actions. Theory and Applications of Categories, 28(15):403–434, 2013. (Cited on p. 18)
[Shu20] Michael Shulman. The 2-Chu-Dialectica construction and the polycategory of multivariable adjunctions. Theory Appl. Categ., 35(4):89–136, 2020. arXiv:1806.06082. (Cited on pp. 2 and 6)
[SL13] Sam Staton and Paul Blain Levy. Universal properties of impure programming languages. SIGPLAN Not., 48(1):179–192, jan 2013. doi:10.1145/2480359.2429091. (Cited on pp. 39 and 40)
[Sza75] M.E. Szabo. Polycategories. Communications in Algebra, 3(8):663–689, 1975. doi:10.1080/00927877508822067. (Cited on p. 2)
[Szl12] Kornél Szlachányi. Skew-monoidal categories and bialgebroids. Advances in Mathematics, 231:1694–1730, 01 2012. doi:10.1016/j.aim.2012.06.027. (Cited on p. 51)
[UVW22] Tarmo Uustalu, Niccolò Veltri, and Cheng-Syuan Wan. Proof theory of skew non-commutative MILL. Electronic Proceedings in Theoretical Computer Science, 358:118–135, 2022. arXiv:2204.06727. (Cited on p. 48)
[UVZ18] Tarmo Uustalu, Niccolò Veltri, and Noam Zeilberger. The sequent calculus of skew monoidal categories. Electronic Notes in Theoretical Computer Science, 341:345–370, 2018. Proceedings of MFPS XXXIV. arXiv:2003.05213. doi:10.1016/j.entcs.2018.11.017. (Cited on p. 48)
[UVZ20] T. Uustalu, N. Veltri, and N. Zeilberger. Deductive systems and coherence for skew prounital closed categories. In Proceedings of the Fifteenth Workshop on Logical Frameworks and Meta-Languages: Theory and Practice, 2020. arXiv:2101.03809. (Cited on p. 48)
[Vel21] Niccolò Veltri. Coherence via focusing for symmetric skew monoidal categories. In Alexandra Silva, Renata Wassermann, and Ruy de Queiroz, editors, Logic, Language, Information, and Computation. WoLLIC 2021., pages 184–200, Cham, 2021. Springer International Publishing. (Cited on pp. 48 and 51)
[Wad94] Philip Wadler. A syntax for linear logic. In Mathematical Foundations of Programming Semantics, pages 513–529, Berlin, Heidelberg, 1994. Springer. (Cited on pp. 3 and 48)

This work is licensed under the Creative Commons Attribution License. To view a copy of this license, visit https://creativecommons.org/licenses/by/4.0/ or send a letter to Creative Commons, 171 Second St, Suite 300, San Francisco, CA 94105, USA, or Eisenacher Strasse 2, 10777 Berlin, Germany

1:54

M. SHULMAN

Vol. 19:2

|  Name | Reference | Definition  |
| --- | --- | --- |
|  LNLPOLY | Remark 2.3 | one linear object, one nonlinear object, all homsets singletons.  |
|  LNLMULTI | Remark 2.3 | one linear object, one nonlinear object, all nonlinear homsets and co-unary linear homsets singletons.  |
|  SYMPOLY | Remark 2.3 | one linear object, no nonlinear objects, and all linear homsets singletons.  |
|  SYMMULTI | Remark 2.3 | one linear object, no nonlinear objects, co-unary linear homsets singletons, and others empty.  |
|  CARTMULTI | Remark 2.3 | one nonlinear object, no linear objects, all nonlinear homsets singletons, and all linear homsets empty.  |
|  CAT | Remark 2.3 | one linear object, no nonlinear objects, and only the identity morphism.  |
|  PLMULTI | Remark 2.4 | one linear object, and morphisms with arity $n$ and co-arity 1 labeled by permutations of $n$ objects.  |
|  DBLSPLIT | Remark 2.7 | one linear object, two nonlinear objects, and all homsets singletons.  |
|  CBPV | after Corollary 3.14 | one nonlinear object, one linear object, all nonlinear homsets and subunary co-unary linear homsets singletons, and others empty.  |
|  ECBV | after Corollary 3.14 | one nonlinear object, one linear object, all nonlinear homsets and unary co-unary linear homsets singletons, and others empty.  |
|  SMADJ | Example 4.8 | two linear objects $P, N$, a unique morphism $\Gamma \rightarrow P$ when $\Gamma$ consists entirely of $P$'s, and a unique morphism $\Gamma \rightarrow N$ for any $\Gamma$.  |
|  ADJ | Example 4.9 | two linear objects $P, N$, a unique nonidentity morphism $P \rightarrow N$.  |
|  LINPOL | Example 5.4 | two linear objects $P, N$, a unique morphism $\Gamma \rightarrow P$ when $\Gamma$ consists entirely of $P$'s, and a unique morphism $\Gamma \rightarrow N$ when $\Gamma$ contains no more than one $N$.  |
|  SYMSKEW | Example 6.9 | same as LINPOL.  |
|  LNLPOL | Example 5.4 | two linear objects $P, N$, one nonlinear object $X$, all nonlinear homsets singletons, a unique morphism $(\Theta \mid \Gamma) \rightarrow P$ if $\Gamma$ consists entirely of $P$'s, and a unique morphism $(\Theta \mid \Gamma) \rightarrow N$ when $\Gamma$ contains no more than one $N$.  |

TABLE 3. Subterminal and other small LNL polycategories