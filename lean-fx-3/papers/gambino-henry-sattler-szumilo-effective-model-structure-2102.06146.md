arXiv:2102.06146v3 [math.CT] 9 Nov 2022

# The effective model structure and $\infty$-groupoid objects

Nicola Gambino

Simon Henry

Christian Sattler

Karol Szumiło

November 11, 2022*

## Abstract

For a category $\mathcal{E}$ with finite limits and well-behaved countable coproducts, we construct a model structure, called the effective model structure, on the category of simplicial objects in $\mathcal{E}$, generalising the Kan–Quillen model structure on simplicial sets. We then prove that the effective model structure is left and right proper and satisfies descent in the sense of Rezk. As a consequence, we obtain that the associated $\infty$-category has finite limits, colimits satisfying descent, and is locally Cartesian closed when $\mathcal{E}$ is, but is not a higher topos in general. We also characterise the $\infty$-category presented by the effective model structure, showing that it is the full sub-category of presheaves on $\mathcal{E}$ spanned by Kan complexes in $\mathcal{E}$, a result that suggests a close analogy with the theory of exact completions.

## Introduction

**Context and motivation.** Over the past two decades, there has been an explosion of interest in the connections between model categories and higher categories [Cis20, GK17, JT07, Lur09, Rez01, Szu17]. This line of research led to the reformulation of significant parts of modern homotopy theory in terms of higher category theory, the development of higher topos theory [TV05, Lur09] and is of great importance for Homotopy Type Theory and the Univalent Foundations programme [AW09, BM18b, GK17, KL12, Shu19]. Central to these developments are model structures on categories of simplicial objects, i.e., functor categories of the form $\mathfrak{s}\mathcal{E} = [\Delta^{\mathrm{op}}, \mathcal{E}]$, where $\mathcal{E}$ is a category, as considered in [Qui67, Section II.4], [GJ99, Chapter II], [CH02, Theorem 6.3] and [Hör21]. In particular, the category of simplicial sets equipped with the Kan–Quillen model structure [Qui67] can be understood as a presentation of the $\infty$-category of spaces, while categories of simplicial presheaves and sheaves (i.e., simplicial objects in a Grothendieck topos) equipped with the Rezk model structure [Rez10] and the Joyal–Jardine model structure [Bro73, Joy84, Jar96] can be seen as presentations of $\infty$-toposes and their hypercompletions, respectively [DHI04, Lur09].

The main contribution of this paper is to construct a new model structure, which we call the *effective model structure*, on categories of simplicial objects $\mathfrak{s}\mathcal{E}$, assuming that $\mathcal{E}$ is merely a countably lextensive category, i.e., a category with finite limits and countable coproducts, where the latter are required to be van Kampen colimits [CLW93, Rez10]. The effective model structure is

*This version of the paper reflects the one published in *Forum of Mathematics, Sigma* (2022), Vol. 10:e34 1–59, submitted 9 March 2021, revised 19 January 2022, accepted 7 February 2022, available here. Two additional minor topos have been fixed.

2020 Mathematics Subject Classification: 18N40 (primary), 18N60, 55U10.

1

defined so that when $\mathcal{E} = \text{Set}$, we recover the Kan–Quillen model structure on simplicial sets [Qui67]. We also prove several results on the effective model structure and its associated $\infty$-category, which we discuss below.

The initial motivation for this work was the desire to establish whether our earlier work on the constructive Kan–Quillen model structure [Hen19, GS17, GSS19, Sat17] could be developed further so as to obtain a new model structure on categories of simplicial sheaves. Indeed, in [Hen19, GSS19] we worked with simplicial sets without using the law of excluded middle and the axiom of choice, thus opening the possibility of replacing them with simplicial objects in a Grothendieck topos. As we explored this idea, we realised that the resulting argument admitted not only a clean presentation in terms of enriched weak factorisation systems [Rie14, Chapter 13], but also a vast generalisation.

In fact, the existence of the effective model structure may be a surprise to some readers, since assuming $\mathcal{E}$ to be countably lextensive is significantly weaker than assuming it to be a Grothendieck topos and covers many more examples (such as the category of countable sets and the category of schemes). In particular, our arguments do not require the existence of all small colimits, (local) Cartesian closure and local presentability, which are ubiquitous in the known constructions of model structures.

One reason for the interest in the effective model structure is that, when $\mathcal{E}$ is a Grothendieck topos, the effective model structure on $\mathfrak{s}\mathcal{E}$ differs from the known model structures on simplicial sheaves and provides the first example of a peculiar combination of higher categorical structure. Indeed, the associated $\infty$-category has finite limits, colimits that satisfy descent and is locally Cartesian closed, but is neither a higher Grothendieck topos [Lur09] nor a higher elementary topos in the sense of [Shu17, Ras18], since its 0-truncation does not always have a subobject classifier (see Example 11.8). In this case, the effective model structure satisfies most of the axioms for a model topos [Rez10], but is not combinatorial. One key point here is that the effective model structure is not cofibrantly generated in the usual sense, but only in an enriched sense. The relation between the effective model structure and other model structures on categories of simplicial objects is discussed further in Remark 9.10.

This situation can be understood by analogy with the theory of exact completions in ordinary category theory [CV98]. There, it is known that the exact completion of a (Grothendieck) topos need not be a (Grothendieck) topos [Men03]. Indeed, we believe that the effective model structure will provide a starting point for the development of a homotopical counterpart of the theory of exact completions. As a first step in this direction, we prove that the $\infty$-category associated to the effective model structure on $\mathfrak{s}\mathcal{E}$ is the full subcategory of the $\infty$-category of presheaves on $\mathcal{E}$ spanned by Kan complexes in $\mathcal{E}$, mirroring a corresponding description of the exact completion of $\mathcal{E}$ in [HT96]. We also make a conjecture (Conjecture 13.2) on the relation between the effective model structure and $\infty$-categorical exact completions, which we leave for future work. In the long term, we hope that our work could be useful for the definition of a higher categorical version of the effective topos [Hyl82], which can be described as an exact completion [Car95].

Finally, our results may be of interest also in Homotopy Type Theory, since they help to clarify how the simplicial model of Univalent Foundations [KL12], in which types are interpreted as Kan complexes, is related to the setoid model of type theory [Hof97], in which types are interpreted as types equipped with an equivalence relation, by showing how not only the latter [EP17] but also the former is related to the theory of exact completions. Furthermore, we expect that the effective model structure may lead to new models of Homotopy Type Theory, another topic that we leave for future research.

**Main results.** In order to outline our main results, let us briefly describe the effective model

2

structure, whose fibrant objects are to be thought of as Kan complexes, or $\infty$-groupoids, in $\mathcal{E}$. In order to describe the fibrations of the effective model structure, recall that, for $E \in \mathcal{E}$, we have a functor

$$\operatorname{Hom}_{\mathfrak{sSet}}(E, -): \mathfrak{s}\mathcal{E} \rightarrow \mathfrak{sSet} \quad (*)$$

sending $X \in \mathfrak{s}\mathcal{E}$ to the simplicial set defined by $\operatorname{Hom}_{\mathfrak{sSet}}(E, X)_n = \operatorname{Hom}(E, X_n)$, for $[n] \in \Delta$. We can then define a map in $\mathfrak{s}\mathcal{E}$ to be a fibration in $\mathfrak{s}\mathcal{E}$ if its image under the functor in $(*)$ is a Kan fibration in $\mathfrak{sSet}$ for every $E \in \mathcal{E}$. Trivial fibrations are defined analogously. Our main results are the following:

- Theorem 9.9, asserting the existence of the effective model structure, whose fibrations and trivial fibrations are defined as above;
- Proposition 10.4 and Corollary 12.18, asserting that the effective model structure is right and left proper, respectively, and Proposition 10.1, showing that homotopy colimits in $\mathfrak{s}\mathcal{E}$ satisfy descent;
- Theorem 10.3 asserting that the $\infty$-category $\operatorname{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ associated to the effective model structure has finite limits and $\alpha$-small colimits satisfying descent when $\mathcal{E}$ is $\alpha$-lextensive, and Theorem 10.5, showing that $\operatorname{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ is also locally Cartesian closed when $\mathcal{E}$ is so.
- Theorem 13.1, characterising the $\infty$-category associated to the effective model structure.

Along the way, we prove several other results of independent interest. For example, we characterise completely the cofibrations of the effective model structure, which do not coincide with all monomorphisms (Theorem 4.6) and we compare the effective model structure with model structures studied in relation to Elmendorf's Theorem (Theorem 11.7).

**Novel aspects.** This paper differs significantly from our work in [Hen19, GSS19, Sat17] in both scope and technical aspects. Regarding scope, apart from generalising the existence of the model structure from the case $\mathcal{E} = \mathsf{Set}$ to that of a general countably lextensive category $\mathcal{E}$, here we discuss a number of topics that are not even mentioned for the case $\mathcal{E} = \mathsf{Set}$ in our earlier work, such as the structure and characterisation of the $\infty$-category associated to the effective model structure, the discussion of descent and the connections with Elmendorf's theorem.

Regarding the technical aspects, even if the general strategy for proving the existence of the effective model structure is inspired from the case $\mathcal{E} = \mathsf{Set}$ in [GSS19], several new ideas are necessary to implement it to the general case, as we explain below. This strategy involves in three steps. First, we introduce the notions of a (trivial) fibration in $\mathfrak{s}\mathcal{E}$ as above and establish the existence of a fibration category structure on the category of Kan complexes (assuming in fact only that $\mathcal{E}$ has finite limits). Secondly, we construct the two weak factorisation systems of the model structure, one given by cofibrations and trivial fibrations and one given by trivial cofibrations and fibrations. Thirdly, we show that weak equivalences (as determined by the two weak factorisation systems) satisfy 2-out-of-3 by proving the so-called Equivalence Extension Property (Proposition 8.3).

In order to realise this plan, we prove several results that are not necessary for $\mathcal{E} = \mathsf{Set}$. We mention only the key ones. First, we develop a new version of the enriched small object argument (Theorem 3.14), which does not require existence of all colimits. In order to achieve it, we analyse the colimits required for our applications and prove that they exist in a countably lextensive category, exploiting crucially that some of the maps involved are complemented monomorphisms. Secondly, we show that the fibration category structure, where fibrations are defined as above,

3

agrees with the weak factorisation systems, defined in terms of enriched lifting properties (Proposition 4.1). Thirdly, we obtain a characterisation of cofibrations in categories of simplicial objects (Theorem 4.6), which requires a new, purely categorical, argument that is entirely different to the one used in [Hen19, GSS19, Sat17]. Finally, new ideas are required in the proof of the Equivalence Extension Property (Proposition 8.3). For this, we need to construct explicitly dependent products (i.e., pushforward) functors along cofibrations (Theorem 6.5), which are not guaranteed to exist since $\mathcal{E}$ is not assumed to be locally Cartesian closed. The existence of these pushforward functors may be considered as a pleasant surprise since they are essential for our argument and no exponentials are assumed to be present in $\mathcal{E}$.

The existence of the effective model structure is independent from that of the constructive Kan–Quillen model structure on simplicial sets [GSS19, Hen19]. Actually, the use of enriched category theory here, especially for expressing stronger versions of the lifting properties usually phrased in terms of mere existence of diagonal fillers, makes explicit some of the informal conventions adopted in [GSS19, Hen19] when treating the case $\mathcal{E} = \text{Set}$. Also, the proofs in [GSS19, Hen19] make use of structure on $\text{Set}$ that is not available in a countably lextensive category and therefore cannot be interpreted as taking place in the so-called internal logic of $\mathcal{E}$ [Joh02, Section D1.3]. Even when $\mathcal{E}$ is a Grothendieck topos, carrying out the proofs in the internal language of $\mathcal{E}$ [MLM92, Chapter 6] would not make explicit the structure under consideration, thus making it more difficult for the results to be accessible and applicable.

**Outline of the paper.** The paper is organised in four parts. The first, including only Section 1, establishes the fibration category structure. The second, including Sections 2, 3 and 4, introduces the two weak factorisation systems, having first developed an appropriate version of the small object argument. The third, including Sections 5, 6, 7, 8 and 9, establishes the existence of the effective model structure, by constructing pushforward functors and establishing the Frobenius and Equivalence Extension Property. The fourth, including Sections 10, 11, 12 and 13, proves the key properties of the effective model structure, namely descent and properness, their $\infty$-categorical counterparts, and characterises its associated $\infty$-category. Throughout the paper, we omit the proofs that can be carried out with minor modifications from [Hen19, GSS19], but include the ones that require new ideas.

**Remark.** The material in this paper is developed within ZFC set theory. Some of the material, however, can be developed also in a constructive setting (see footnotes and Appendix A for details).

**Acknowledgements.** We are grateful to André Joyal for questions and discussions, which in particular led to Theorem 13.1, and to Dan Christensen and Denis-Charles Cisinski for comments on an earlier version of the paper. Nicola Gambino and Karol Szumilo gratefully acknowledge that this material is based upon work supported by the US Air Force Office for Scientific Research under awards number FA8655-13-1-3038 and FA9550-21-1-0007. Nicola Gambino was also supported by EPSRC under grant EP/V002325/1. Simon Henry was partially supported by an NSERC Discovery Grant. Christian Sattler was supported by Swedish Research Council grant 2019-03765.

## 1 Kan fibrations

This section develops some simplicial homotopy theory in a category $\mathcal{E}$ with finite limits. The category of simplicial objects in $\mathcal{E}$ is defined by letting

$$\mathfrak{s}\mathcal{E} =_{\text{def}} [\Delta^{\text{op}}, \mathcal{E}].$$

4

In Definition 1.3 we introduce the notion of a fibration in $\mathfrak{s}\mathcal{E}$ with which we shall work throughout the paper. This notion is defined using the enrichment of $\mathfrak{s}\mathcal{E}$ in $\mathfrak{s}\text{Set}$ and generalises that of a Kan fibration in $\mathfrak{s}\text{Set}$. The main result of this section, Theorem 1.7, establishes a structure of a fibration category on the category of fibrant objects in $\mathfrak{s}\mathcal{E}$. For applications throughout the paper, we also establish a fiberwise version of this fibration category in Theorem 1.9. We also introduce the notion of a *pointwise weak equivalence* (Definition 1.6), which provides the weak equivalences of these fibration categories. In the subsequent sections we will extend these results to obtain the effective model structure on $\mathfrak{s}\mathcal{E}$, under the stronger assumption that $\mathcal{E}$ is countably lextensive. The weak equivalences of the effective model structure will not be the pointwise weak equivalences in general, although the two notions will coincide for maps between fibrant objects.

Let us recall how the category $\mathfrak{s}\mathcal{E}$ is enriched over $\mathfrak{s}\text{Set}$ with respect to the Cartesian monoidal structure. For a finite simplicial set $K$ and $X \in \mathfrak{s}\mathcal{E}$, we define $K \pitchfork X \in \mathfrak{s}\mathcal{E}$ via the end formula

$$(K \pitchfork X)_m =_{\text{def}} \int_{[n] \in \Delta} X_n^{(K \times \Delta[m])_n}. \quad (1.1)$$

For $X, Y \in \mathfrak{s}\mathcal{E}$, the simplicial hom-object is then defined by letting$^1$

$$\text{Hom}_{\mathfrak{s}\text{Set}}(X, Y)_m =_{\text{def}} \text{Hom}_{\text{Set}}(X, \Delta[m] \pitchfork Y). \quad (1.2)$$

This makes $\mathfrak{s}\mathcal{E}$ into a $\mathfrak{s}\text{Set}$-enriched category so that the formula in (1.1) gives the cotensor (over finite simplicial sets) with respect to the enrichment. Without further assumptions on $\mathcal{E}$, $\mathfrak{s}\mathcal{E}$ does not admit all cotensors or tensors over simplicial sets. We often identify an object $E \in \mathcal{E}$ with the constant simplicial object with value $E$. For example, for $E \in \mathcal{E}$ and $Y \in \mathfrak{s}\mathcal{E}$ we write $\text{Hom}_{\mathfrak{s}\text{Set}}(E, Y)$. Note that

$$\text{Hom}_{\mathfrak{s}\text{Set}}(E, Y)_m = \text{Hom}_{\text{Set}}(E, Y_m),$$

$$\text{Hom}_{\mathfrak{s}\text{Set}}(E, K \pitchfork Y) = K \pitchfork \text{Hom}_{\mathfrak{s}\text{Set}}(E, Y).$$

The $\mathfrak{s}\text{Set}$-enrichment allows us to define a notion of a homotopy between morphisms of $\mathfrak{s}\mathcal{E}$. Given maps $f_0, f_1: X \rightarrow Y$ in $\mathfrak{s}\mathcal{E}$ (or one of its slice categories), a *homotopy* $H$ from $f_0$ to $f_1$, written $H: f_0 \sim f_1$, is a map

$$H: X \rightarrow \Delta[1] \pitchfork Y \quad (1.3)$$

that restricts to $f_0$ on $\{0\} \rightarrow \Delta[1]$ and to $f_1$ on $\{1\} \rightarrow \Delta[1]$. It is *constant* if it factors through the canonical map $\Delta[0] \pitchfork Y \rightarrow \Delta[1] \pitchfork Y$, in which case $f_0 = f_1$. Note that we can regard $H$ as a map $\Delta[1] \rightarrow \text{Hom}_{\mathfrak{s}\text{Set}}(X, Y)$. This generalises the usual notion of homotopy in simplicial sets. For each $E \in \mathcal{E}$, the functor $\text{Hom}_{\mathfrak{s}\text{Set}}(E, -)$ preserves homotopies because it preserves the cotensor with $\Delta[1]$.

We need some definitions to introduce the notions of a Kan fibration and trivial Kan fibration in $\mathfrak{s}\mathcal{E}$. For a finite simplicial set $K$, we define the *evaluation functor* $\text{ev}_K: \mathfrak{s}\mathcal{E} \rightarrow \mathcal{E}$ via the end formula

$$\text{ev}_K(X) = X(K) =_{\text{def}} \int_{[n] \in \Delta} X_n^{K_n}. \quad (1.4)$$

We will usually write $X(K)$ rather than $\text{ev}_K(X)$ for brevity. However, in some situations the notation $\text{ev}_K(X)$ will be more convenient, see the definition of pullback evaluation below. The end above exists since, by the finiteness of $K$, it can be constructed from finite limits. For example, $X(\Delta[n]) = X_n$ and $X(\Lambda^k[2]) = X_1 \times_{X_0} X_1$. Also note that $X(K) = (K \pitchfork X)_0$ and $X(K \times \Delta[m]) = (K \pitchfork X)_m$.

$^1$Here and in the following we use subscripts to indicate to which category the hom-objects under consideration belong.

5

**Remark 1.1.** There are two alternative ways of viewing the evaluation functor. First, since $\mathcal{E}$ has finite limits, we can consider $X(K)$ as the value on $K$ of the right Kan extension of $X: \Delta^{\text{op}} \to \mathcal{E}$ along the inclusion of $\Delta$ into the category of finite simplicial sets. Secondly, seeing $\mathcal{E}$ as a Set-enriched category, we can view $X(K)$ as a weighted limit, namely the limit of $X$, viewed as a diagram in $\mathcal{E}$, weighted by $K$, viewed as a diagram in Set. Both of these observations show that $X(K)$ is contravariantly functorial in $K$.

We write $\widehat{\text{ev}}$ for the *pullback evaluation* functor, which is the result of applying the so-called Leibniz construction [RV14] to the two-variable functor $\text{ev}$, i.e., the functor sending a map $i: A \to B$ between finite simplicial sets and a morphism $f: X \to Y$ of $\mathfrak{s}\mathcal{E}$ to

$$\widehat{\text{ev}}_i(f): \text{ev}_A(X) \to \text{ev}_B(X) \times_{\text{ev}_B(Y)} \text{ev}_A(Y) \text{ in } \mathcal{E} \\ \text{also written as } \widehat{\text{ev}}_i(f): X(A) \to X(B) \times_{Y(B)} Y(A). \tag{1.5}$$

**Remark 1.2.** We adopt the convention of prefixing with 'pullback' (or 'pushout') the name of a two-variable functor to indicate the result of applying the Leibniz construction to it. So for example, we shall say pushout product for what is also referred to as Leibniz product or corner product.

We use standard notation for the sets of boundary inclusions and horn inclusions,

$$I_{\mathfrak{sSet}} = \{\partial \Delta[n] \to \Delta[n] \mid n \geq 0\} \text{ and } J_{\mathfrak{sSet}} = \{\Lambda^k[n] \to \Delta[n] \mid n \geq k \geq 0, n > 0\}. \tag{1.6}$$

**Definition 1.3.** We say that a morphism in $\mathfrak{s}\mathcal{E}$ is

- a *trivial Kan fibration* if its pullback evaluations with all maps in $I_{\mathfrak{sSet}}$ are split epimorphisms;
- a *Kan fibration* if its pullback evaluations with all maps in $J_{\mathfrak{sSet}}$ are split epimorphisms.

Explicitly, a map $f: X \to Y$ in $\mathfrak{s}\mathcal{E}$ is a Kan fibration if the morphism

$$X(\Delta[n]) \to X(\Lambda^k[n]) \times_{Y(\Lambda^k[n])} Y(\Delta[n])$$

in $\mathcal{E}$ has a section, for all $n \geq k \geq 0$ and $n > 0$. For $Y = 1$, this means that the morphism

$$X(\Delta[n]) \to X(\Lambda^k[n])$$

has a section, for all $n \geq k \geq 0$ and $n > 0$, in which case we say that $X$ is a *Kan complex*. Note that for $\mathcal{E} = \text{Set}$, these definitions reduce to the standard notions of a Kan fibration, trivial Kan fibration and a Kan complex in simplicial sets. In the following, we shall frequently write *fibration*, *trivial fibration* and *fibrant object*, as we do not consider other notions of fibrations.

Although we have not yet introduced cofibrations and trivial cofibrations in $\mathfrak{s}\mathcal{E}$, we can use the standard classes of cofibrations and trivial cofibrations in $\mathfrak{sSet}$, which are the saturations of the generating sets $I_{\mathfrak{sSet}}$ and $J_{\mathfrak{sSet}}$, respectively.

The next proposition characterises fibrations and trivial fibrations by reducing them to the corresponding notions in $\mathfrak{sSet}$ in terms of the $\mathfrak{sSet}$-enrichment of $\mathfrak{s}\mathcal{E}$, defined in (1.2).

**Proposition 1.4.** *Let $f: X \to Y$ be a map in $\mathfrak{s}\mathcal{E}$. Then $f$ is a (trivial) fibration if and only if, for all $E \in \mathcal{E}$, the map*

$$\text{Hom}_{\mathfrak{sSet}}(E, f): \text{Hom}_{\mathfrak{sSet}}(E, X) \to \text{Hom}_{\mathfrak{sSet}}(E, Y)$$

*is a (trivial) fibration in $\mathfrak{sSet}$.*

6

Proof. Note that the functors $X(-): \mathfrak{sSet}^{\mathrm{op}} \to \mathcal{E}$ and $\operatorname{Hom}_{\mathfrak{sSet}}(-, X): \mathcal{E}^{\mathrm{op}} \to \mathfrak{sSet}$ are contravariantly adjoint. Thus for all maps $i: A \to B$ between finite simplicial sets there is a bijective correspondence between the lifting problems

![img-0.jpeg](img-0.jpeg)

![img-1.jpeg](img-1.jpeg)

the latter of which is equivalent to the morphism on the right being a split epimorphism (by setting $E = X(A) \times_{Y(A)} Y(B)$).

If $i: A \to B$ is a map of finite simplicial sets and $p: X \to Y$ is a morphism of $\mathfrak{sE}$, then we define the pullback cotensor of $i$ and $p$ (cf. Remark 1.2) as the induced morphism

$$i \widehat{\cap} p: B \cap X \to (A \cap X) \times_{A \cap Y} (B \cap X).$$

# Lemma 1.5.

(i) The pullback cotensor in \(\mathfrak{sE}\) of a cofibration between finite simplicial sets and a fibration is a fibration. If the given cofibration or fibration is trivial, then the result is a trivial fibration.
(ii) Fibrations and trivial fibrations in \(\mathfrak{sE}\) are closed under composition, pullback, and retract.
(iii) Let \( f \colon X \to Y \) and \( g \colon Y \to Z \) be morphisms of \( \mathfrak{sE} \). If \( f \colon X \to Y \) and \( gf \colon X \to Z \) are trivial fibrations, then so is \( g \colon Y \to Z \).

Proof. All the statements are proved in the same way: they hold for simplicial sets (see, e.g., [Qui67, Theorem II.3.3]) and transfer to $\mathfrak{sE}$ using Proposition 1.4. Note that transferring (i) from $\mathfrak{sSet}$ to $\mathfrak{sE}$ relies on the fact that $\operatorname{Hom}_{\mathfrak{sSet}}(E, -)$ preserves pullbacks and cotensors and hence pullback cotensors.

Definition 1.6. Let $f: X \to Y$ in $\mathfrak{sE}$. We say that $f$ is a pointwise weak equivalence if

$$\operatorname{Hom}_{\mathfrak{sSet}}(E, f): \operatorname{Hom}_{\mathfrak{sSet}}(E, X) \to \operatorname{Hom}_{\mathfrak{sSet}}(E, Y)$$

is a weak equivalence in $\mathfrak{sSet}$ for all $E \in \mathcal{E}$.

For the next theorem, we use the definition of a fibration category as stated in [GSS19, Section 1.6].

Theorem 1.7. Let $\mathcal{E}$ be category with finite limits. Then pointwise weak equivalences, Kan fibrations and trivial Kan fibrations equip the category of Kan complexes in $\mathfrak{sE}$ with the structure of a fibration category.

Proof. Trivial fibrations are exactly the fibrations that are weak equivalences because this holds in $\mathfrak{sSet}$. We need to verify the following axioms.

Constructively, part (i) is true in $\mathfrak{sSet}$ by [GSS19, Corollary 1.3.4], part (ii) is evident and part (iii) is [GSS19, Lemma 1.3.6].

7

(F1) $\mathfrak{s}\mathcal{E}$ has a terminal object and all objects are fibrant, which follows directly from the definitions.

(F2) Pullbacks along fibrations exist because $\mathcal{E}$ (and hence $\mathfrak{s}\mathcal{E}$) has all finite limits. Moreover, fibrations and acyclic fibrations are closed under pullback by point (ii) of Lemma 1.5.

(F3) Every morphism factors as a weak equivalence followed by a fibration. By [Bro73, p. 421, Factorization lemma] it suffices to construct a path object, i.e., a factorisation of the diagonal $X \rightarrow X \times X$. Such factorisation is given by the cotensor $X \rightarrow \Delta[1] \pitchfork X \rightarrow X \times X$. Applying $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, -)$ to this factorisation gives

$$\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \rightarrow \Delta[1] \pitchfork \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \rightarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \times \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$$

which is a well known factorisation of the diagonal of $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$ into a weak equivalence followed by a fibration in $\mathfrak{s}\text{Set}$ (since $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$ is a Kan complex by Proposition 1.4). See, e.g., [GJ99, p. 43]. Hence $X \rightarrow \Delta[1] \pitchfork X \rightarrow X \times X$ is also such factorisation in $\mathfrak{s}\mathcal{E}$.

(F4) Weak equivalences satisfy 2-out-of-6, which follows since this property holds in $\mathfrak{s}\text{Set}$. $\square$

In view of our development in Section 8, we generalise Theorem 1.7 to the case of a slice of $\mathfrak{s}\mathcal{E}$ over a simplicial object $X$, which we write $\mathfrak{s}\mathcal{E} \downarrow X$. We then define $\mathfrak{s}\mathcal{E} \downarrow X$ to be the full subcategory of $\mathfrak{s}\mathcal{E} \downarrow X$ spanned by the fibrations over $X$.

First of all, let us recall that the enrichment of $\mathfrak{s}\mathcal{E}$ in simplicial sets, including the cotensor with finite simplicial sets, descends to its slices. For $(A, f), (B, g) \in \mathfrak{s}\mathcal{E} \downarrow X$, the hom-object $\operatorname{Hom}_{\mathfrak{s}\text{Set}}((A, f), (B, g))$ is the pullback of $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(A, B)$ along the map $f: 1 \rightarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(A, X)$. The cotensor of $(A, f) \in \mathfrak{s}\mathcal{E} \downarrow X$ by a finite simplicial set $K$ is the pullback of $K \pitchfork A$ along the map $X \rightarrow K \pitchfork X$ (using the fact that the monoidal unit in $\mathfrak{s}\text{Set}$ is the terminal object). As before, for each $E$, the functor $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, -): \mathfrak{s}\mathcal{E} \downarrow X \rightarrow \mathfrak{s}\text{Set} \downarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$ preserves these cotensors.

**Lemma 1.8.** *Let $X \in \mathfrak{s}\mathcal{E}$. The pullback cotensor properties in part (i) of Lemma 1.5 hold in $\mathfrak{s}\mathcal{E} \downarrow X$ as well.*

*Proof.* This follows from their validity in $\mathfrak{s}\mathcal{E}$, i.e., part (i) of Lemma 1.5 and the stability of fibrations and trivial fibration under pullback, i.e., part (ii) of Lemma 1.5. $\square$

**Theorem 1.9.** *Let $X \in \mathfrak{s}\mathcal{E}$. Then pointwise weak equivalences, fibrations and trivial fibrations equip the category $\mathfrak{s}\mathcal{E} \downarrow X$ with the structure of a fibration category.*

*Proof.* All axioms are verified by the same argument as in the proof of Theorem 1.7. For (F3), we use Lemma 1.8 which is a fiberwise version of part (i) of Lemma 1.5 used in the proof of Theorem 1.7. $\square$

We conclude this section with a basic observation on homotopy equivalences.

**Proposition 1.10.** *Homotopy equivalences in $\mathfrak{s}\mathcal{E}$ (and in particular, in $\mathfrak{s}\mathcal{E} \downarrow X$ for all $X \in \mathfrak{s}\mathcal{E}$) are pointwise weak equivalences.*

*Proof.* The functors $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, -)$ preserve homotopies and hence also homotopy equivalences. Thus the conclusion follows from the fact that homotopy equivalences are weak equivalences in $\mathfrak{s}\text{Set}$. $\square$

8

## 2 Lextensive categories and complemented inclusions

This section, Section 3 and Section 4 constitute the second part of the paper, whose ultimate goal is to construct two weak factorisation systems on $\mathfrak{s}\mathcal{E}$, whose right classes of maps are the fibrations and trivial fibrations of Section 1, assuming that $\mathfrak{s}\mathcal{E}$ is a countably lextensive category. This section recalls some basic facts about lextensive categories. Throughout it, we consider a fixed category with finite limits $\mathcal{E}$ and study diagrams in $\mathcal{E}$ indexed by a category $D$. When convenient, we will regard cones under such diagrams as diagrams over the category $D^{\triangleright}$, obtained by adding a new terminal object $\star$ to $D$. We start by recalling the general notion of van Kampen colimit [Lur09, Rez10] in our setting.

**Definition 2.1.** Let $Y_{\bullet}: D \rightarrow \mathcal{E}$ be a diagram and assume $Y_{\star} = \operatorname{colim}_{d \in D} Y_d$ is its colimit in $\mathcal{E}$. We say that $Y_{\star}$ is

- (i) *universal*, if it is preserved by pullbacks, i.e., if for every map $X_{\star} \rightarrow Y_{\star}$, $X_{\star}$ is the colimit of the induced diagram $X_d = X_{\star} \times_{Y_{\star}} Y_d$.
- (ii) *effective*, if given a Cartesian natural transformation $X \rightarrow Y$, the diagram $X$ has a colimit $X_{\star}$, and all the squares

![img-2.jpeg](img-2.jpeg)

are pullback squares, i.e., the extended natural transformation over $D^{\triangleright}$ is also Cartesian.

- (iii) *van Kampen*, if it is both universal and effective.

**Lemma 2.2.** A colimit $Y_{\star} = \operatorname{colim}_{d \in D} Y_d$ in $\mathcal{E}$ is van Kampen if and only if it is preserved by the pseudo-functor $\mathcal{E}^{\mathrm{op}} \rightarrow \mathrm{Cat}$ sending each $X \in \mathcal{E}$ to the slice category $\mathcal{E} \downarrow X$ (with morphisms acting by pullbacks). In other words, the slice category $\mathcal{E} \downarrow Y_{\star}$ is the pseudo-limit $\lim_{d \in D} (\mathcal{E} \downarrow Y_d)$.

*Proof.* Pullback along the structure morphisms of $Y_{\star}$ induces a functor $P: \mathcal{E} \downarrow Y_{\star} \rightarrow \lim_d (\mathcal{E} \downarrow Y_d)$. We need to show that this functor is an equivalence if and only if the colimit of $Y_{\bullet}$ is a van Kampen colimit.

An object of $\lim_d (\mathcal{E} \downarrow Y_d)$ can be identified with a Cartesian transformation $X \rightarrow Y$. If colimits of diagrams Cartesian over $Y_{\bullet}$ exist, then taking the colimit yields a left adjoint to the functor above:

$$\operatorname{colim}: \lim_d (\mathcal{E} \downarrow Y_d) \leftrightarrows \mathcal{E} \downarrow Y_{\star}: P.$$

Conversely, we claim that if $P$ has a left adjoint, then the left adjoint computes the colimits of diagrams that are Cartesian over $Y_{\bullet}$. Indeed, assume that the pullback functor $P: \mathcal{E} \downarrow Y_{\star} \rightarrow \lim_d (\mathcal{E} \downarrow Y_d)$ has a left adjoint $X_{\bullet} \mapsto X_{\star}$, and let $Z$ be an arbitrary object of $\mathcal{E}$. A map $X_{\star} \rightarrow Z$ in $\mathcal{E}$ is the same as a map $X_{\star} \rightarrow Z \times Y_{\star}$ in $\mathcal{E} \downarrow Y_{\star}$, which by the adjunction formula is the same as a natural transformation $X_d \rightarrow Z \times Y_d$ over $Y_{\bullet}$, but this is exactly the same as a natural transformation $X_d \rightarrow Z$ in $\mathcal{E}$, and hence this shows that $X_{\star}$ is the colimit of $X_d$.

Now, $Y_{\star}$ is universal if and only if the counit of this adjunction is an isomorphism and it is effective if and only if the unit is an isomorphism. Hence, the colimit $Y_{\star}$ of $Y_{\bullet}$ is van Kampen if and only if the pullback functor described above has a left adjoint such that the unit and counit of the adjunction are isomorphisms, i.e., if and only if it is an equivalence. $\square$

9

For example, an initial object 0 is always vacuously effective and it is universal if and only if it is strict, i.e., if there is a morphism $X \to 0$, then $X$ is initial itself. Instead, a coproduct $Y_\star = \coprod_d Y_d$ is van Kampen if and only if it is universal and disjoint, i.e., $Y_d \times_{Y_\star} Y_{d'}$ is initial for $d \neq d'$. This can be seen inspecting the proof of [CLW93, Proposition 2.14].

**Lemma 2.3.** Let $D$ be a small category. Let $Y_\bullet: C \to \mathcal{E}^D$ be a diagram such that $Y_\bullet(d)$ admits a van Kampen colimit in $\mathcal{E}$ for all $d \in D$. Then $Y_\bullet$ has a van Kampen colimit in $\mathcal{E}^D$.

Proof. If each $d \in D$, $\operatorname{colim}_{c \in C} Y_c(d)$ exists in $\mathcal{E}$, then it is functorial in $d$ and it is a colimit in $\mathcal{E}^D$. In particular, an object over $\operatorname{colim}_c Y_c$ is a $D$-indexed diagram $X(d) \to \operatorname{colim}_C Y_c(d)$, which as these colimits are all van Kampen is the same as a $(C \times D)$-indexed diagram $X_c(d) \to Y_c(d)$ which is Cartesian in the $C$-direction, which in turn is the same as a $C$-indexed diagram $X_\bullet \in \mathcal{E}^D$ which is Cartesian over $Y_\bullet$, hence proving the lemma. $\square$

We now recall the definition of various kinds of lextensive categories [CLW93].

**Definition 2.4.** Let $\mathcal{E}$ be a category with finite limits. For a regular cardinal $\alpha$, we say that $\mathcal{E}$ is $\alpha$-lextensive if $\alpha$-coproducts exist and are van Kampen colimits. Furthermore, we say that $\mathcal{E}$ is

- (i) lextensive if it is $\omega$-lextensive, i.e., finite coproducts exist and are van Kampen colimits,
- (ii) countably lextensive if it is $\omega_1$-lextensive, i.e., countable coproducts exist and are van Kampen colimits,
- (iii) completely lextensive if it is $\alpha$-lextensive for all $\alpha$, i.e., all small coproducts exist and are van Kampen colimits.

**Example 2.5.** There are numerous examples of lextensive categories.

- (i) Any presheaf category is completely lextensive. In particular, for any group $G$ the category of $G$-sets is countably lextensive.
- (ii) More generally, any Grothendieck topos is completely lextensive. In fact, Giraud's theorem characterises Grothendieck toposes as the locally presentable categories in which coproducts and (in an appropriate sense) quotients by equivalence relations are van Kampen colimits.
- (iii) The category of topological spaces is completely lextensive. The same is true for many of its subcategories such as categories of Hausdorff spaces, compactly generated spaces, weakly Hausdorff compactly generated spaces, etc.
- (iv) The category of affine schemes is lextensive, the category of schemes is completely lextensive.
- (v) The category of countable sets is countably lextensive.
- (vi) A category with finite limits $\mathcal{E}$ has the free coproduct completion which can be constructed as the category $\mathsf{Fam}\,\mathcal{E}$ of families of objects in $\mathcal{E}$. Explicitly, an object is pair $(S, (X_s)_{s \in S})$ where $S$ is a set and $(X_s)_{s \in S}$ is an $S$-indexed family of objects of $\mathcal{E}$. A morphism $(S, (X_s)) \to (S', (X'_{s'}))$ consists of a function $f: S \to S'$ and morphisms $X_s \to X'_{f(s)}$ for all $s \in S$. $\mathsf{Fam}\,\mathcal{E}$ is completely lextensive. The $\alpha$-coproduct completion, $\mathsf{Fam}_\alpha\,\mathcal{E}$, obtained by restricting to $\alpha$-small families, is an $\alpha$-lextensive category.

10

For $S \in \mathsf{Set}$ and $X \in \mathcal{E}$, we write $S \cdot X$ for the tensor of $X$ with $S$, when it exists. If $\mathcal{E}$ has countable coproducts, then this tensor exists for countable $S$ and can be defined as

$$S \cdot X = \prod_{s \in S} X. \quad (2.1)$$

The global sections functor $\mathcal{E}(1, -): \mathcal{E} \rightarrow \mathsf{Set}$ has a partial left adjoint, defined by mapping a countable set $S$ to

$$\underline{S} =_{\text{def}} S \cdot 1 = \prod_{s \in S} 1. \quad (2.2)$$

We extend this notation to diagram categories in a levelwise fashion: if $\mathcal{E}$ has countable coproducts and $D$ a small category, then the levelwise global sections functor $\mathcal{E}^D \rightarrow \mathsf{Set}^D$ has a partial left adjoint, sending a levelwise countable diagram $K \in \mathsf{Set}^D$ to $\underline{K} \in \mathcal{E}^D$, which is defined by levelwise application of $S \mapsto \underline{S}$. These functors will be used frequently in the paper. For example, we will use them in Section 4 to transfer the sets of boundary inclusions and horn inclusions in (1.6) from $\mathsf{sSet}$ to $\mathsf{sE}$, so as to obtain generating sets for weak factorisation systems in $\mathsf{sE}$. We establish some of their basic properties in the next lemmas.

**Lemma 2.6.** *If $\mathcal{E}$ is countably lextensive, then for every countable set $S$ and $X \in \mathcal{E}$, we have $\underline{S} \times X \cong S \cdot X$, naturally in $S$.*

*Proof.* Since $\mathcal{E}$ is countably lextensive, it is countably distributive. Thus, product with $X$ preserves countable coproducts, in particular tensors with countable sets. This reduces the claim to the natural isomorphism $1 \times X \cong X$. $\square$

The next lemma will be used, sometimes implicitly, in Section 4.

**Lemma 2.7.** *If $\mathcal{E}$ is countably lextensive, then the functor $S \mapsto \underline{S}$ from countable sets to $\mathcal{E}$ preserves finite limits.*

*Proof.* The functor $S \mapsto \underline{S}$ preserves terminal objects by definition. It also preserves pullbacks. Indeed, every pullback diagram of (countable) sets decomposes as a (countable) coproduct of product diagrams. These products are preserved since products preserve countable coproducts in each variable by lextensivity. $\square$

The next lemma will be applied in Section 6.

**Lemma 2.8.** *Let $\mathcal{E}$ be an $\alpha$-lextensive category. If $D$ is a small category and $S: D \rightarrow \mathsf{Set}$ is a functor which takes values in $\alpha$-small sets, then there is an equivalence of categories*

$$\mathcal{E}^D \downarrow \underline{S} \simeq \mathcal{E}^{D \downarrow S}$$

*where $D \downarrow S$ denotes the category of elements of $S$.*

*Proof.* The proof is similar to that of Lemma 2.2. There is a functor $\mathcal{E}^{D \downarrow S} \rightarrow \mathcal{E}^D \downarrow \underline{S}$ which sends a functor $F: D \downarrow S \rightarrow \mathcal{E}$ to the functor $V: D \rightarrow \mathcal{E}$ defined by:

$$V(d) = \prod_{s \in S(d)} F(d, s).$$

11

It comes with an obvious map to $\underline{S}$, which was defined as $\underline{S}(d) = \coprod_{s \in S(d)} 1$. This functor has a right adjoint $\mathcal{E}^D \downarrow \underline{S} \to \mathcal{E}^{D \downarrow S}$ sending a functor $V: D \to \mathcal{E}$ with a natural transformation $V \to \underline{S}$ to the functor $F: D \downarrow S \to \mathcal{E}$ where $F(d, s)$ is defined as the following pullback:

![img-3.jpeg](img-3.jpeg)

These two adjoints functor are equivalences. Indeed, the counit of this adjunction is an isomorphism by universality of coproducts and the unit is an isomorphism by effectivity of coproducts. $\square$

We now turn our attention to the class of complemented inclusions. These will be useful for construction of certain colimits whose existence is not immediately obvious in lextensive categories and, especially, in their diagram categories. First of all, recall that a morphism $i: A \to B$ in $\mathcal{E}$ is a *complemented inclusion* if it has a *complement*, i.e., a morphism $j: C \to B$ such that $i$ and $j$ exhibit $B$ as a coproduct of $A$ and $C$ in $\mathcal{E}$. In other words, $i$ is isomorphic to the coproduct inclusion $A \to A \sqcup C$. We will often say simply that $C$ is a complement of $A$. The notation $A \rightsquigarrow B$ will be sometimes used to indicate complemented inclusions. Note that complemented inclusions are sometimes (e.g., in our previous work [GSS19, Hen19]) called *decidable inclusions* in reference to the notion of decidability in constructive logic.

#### Lemma 2.9.

- (i) *If $\mathcal{E}$ is lextensive, then the pushout of a complemented inclusion along any morphism exists and is again a complemented inclusion. Moreover, such pushouts are preserved by functors (and pseudo-functors) that preserve finite coproducts and thus are van Kampen colimits.*
- (ii) *If $\mathcal{E}$ is countably lextensive, then the colimit of a sequence of complemented inclusions exists and is again a complemented inclusion. Moreover, such colimits are preserved by functors (and pseudo-functors) that preserve countable coproducts and thus are van Kampen colimits.*

*Proof.* If $i: A \to B$ is a complemented inclusion with complement $C$, then the pushout of $i$ along $A \to D$ is $C \sqcup D$. Similarly, if $i_k: A_k \to A_{k+1}$ are complemented inclusions with complements $C_{k+1}$, then $\operatorname{colim}_k A_k$ is $\coprod_k C_k$ (where $C_0 = A_0$). The claims on preservation by functors then follow immediately.

These presentations of colimits as coproducts remain when we consider $\mathcal{E}$ as a bicategory. Recall from Lemma 2.2 that a colimit is van Kampen exactly if it is preserved by a certain pseudo-functor. Since (finite or countable) coproducts are assumed van Kampen, so are the presented colimits. $\square$

#### Lemma 2.10. Assume $\mathcal{E}$ is lextensive.

- (i) *complemented subobjects in $\mathcal{E}$ are closed under finite unions.*
- (ii) *complemented inclusions in $\mathcal{E}$ are closed under finite limits, i.e., if $X \to Y$ is a natural transformation between finite diagrams in $\mathcal{E}$ that is a levelwise complemented inclusion, then so is the induced morphism $\lim X \to \lim Y$.*

*Proof.* The proof of [GSS19, Lemma 1.1.4] applies verbatim. $\square$

12

**Lemma 2.11.** *Assume that $\mathcal{E}$ is countably lextensive. Then the full subcategory of $[\omega, \mathcal{E}]$ consisting of sequences of complemented inclusions has finite limits which are preserved by the colimit functor (sending each sequence to its colimit in $\mathcal{E}$).*

*Proof.* First note that the category of sequences of complemented inclusions has finite limits by part (ii) of Lemma 2.10. Moreover, part (ii) of Lemma 2.9 implies that colimits of such sequences exist. It suffices to show that this colimit functor preserves terminal objects and pullbacks. Terminal objects are preserved since $\omega$ is a connected category (it has an initial object). For the case of pullbacks, we consider a span $A \rightarrow C \leftarrow B$ of sequences of complemented inclusions. We need to show that the map

$$\operatorname{colim}_{k \in \omega} A_k \times_{C_k} B_k \rightarrow \operatorname{colim} A \times_{\operatorname{colim} C} \operatorname{colim} B$$

is invertible. We decompose this map into three factors:

$$\begin{array}{ccc} \operatorname{colim}_{k \in \omega} A_k \times_{C_k} B_k & \longrightarrow & \operatorname{colim} A \times_{\operatorname{colim} C} \operatorname{colim} B. \\ \downarrow & & \uparrow \\ \operatorname{colim}_{k \in \omega} A_k \times_{\operatorname{colim} C} B_k & \longrightarrow & \operatorname{colim}_{i,j \in \omega} A_i \times_{\operatorname{colim} C} B_j \end{array}$$

The left map is invertible even before taking colimits because $C_k \rightarrow \operatorname{colim} C$ is a monomorphism. The bottom map is invertible because the diagonal functor $\omega \rightarrow \omega \times \omega$ is final (it has a left adjoint). The right map is invertible by universality of the van Kampen colimits $\operatorname{colim} A$ and $\operatorname{colim} B$ (part (ii) of Lemma 2.9). $\square$

Let $D$ be a small category. We say that a morphism $\varphi: F \rightarrow G$ in $\mathcal{E}^D$, is a *levelwise complemented inclusion* if its components $\varphi_d: F_d \rightarrow G_d$, for $d \in D$, are complemented inclusions in $\mathcal{E}$. Note that this is considerably less restrictive than asking for $\varphi$ to be a complemented inclusion in $\mathcal{E}^D$.

**Corollary 2.12.** *Let $D$ be a small category.*

- (i) *If $\mathcal{E}$ is lextensive, then pushouts along levelwise complemented inclusions exist, are computed levelwise and are van Kampen colimits in $\mathcal{E}^D$.*
- (ii) *If $\mathcal{E}$ is countably lextensive, then colimits of sequences of levelwise complemented inclusions exist, are computed levelwise and are van Kampen colimits in $\mathcal{E}^D$.*

*Proof.* This follows immediately from Lemmas 2.3 and 2.9. $\square$

**Lemma 2.13.** *Let $D$ be a small category. If $\mathcal{E}$ is lextensive, then the pushout products of levelwise complemented inclusions in $\mathcal{E}^D$ with arbitrary morphisms exist. Moreover, the pushouts involved are van Kampen.*

*Proof.* By universality of coproducts, levelwise complemented inclusions are closed under pullbacks. Thus a pushout computing a pushout product with a levelwise complemented inclusion is a pushout along a levelwise complemented inclusion. They are van Kampen by Corollary 2.12. $\square$

The following statement will be needed in Section 4 to prove Lemma 4.5.

13

**Lemma 2.14.** *Let $\mathcal{C}$ be a category, $P$ a poset with binary meets, $X \in \mathcal{C}$ an object and*

$$A = (A_p \hookrightarrow X \mid p \in P)$$

*a diagram of subobjects of $X$ closed under intersection, i.e., such that $A_p \cap A_q = A_{p \cap q}$. Then if $A$ has a van Kampen colimit, the colimit is also a subobject of $X$.*

*Proof.* We assume that $\operatorname{colim}_{p \in P} A_p$ exists and is a van Kampen colimit, and we show that the diagonal map $\operatorname{colim}_{p \in P} A_p \rightarrow F = (\operatorname{colim}_{p \in P} A_p) \times_X (\operatorname{colim}_{p \in P} A_p)$ is an isomorphism. First, we form pullbacks:

![img-4.jpeg](img-4.jpeg)

Using that the colimits are van Kampen, we have that $F = \operatorname{colim}_p F_p$ and $F_p = \operatorname{colim}_q A_q \cap A_p$ and hence $F = \operatorname{colim}_{p,q} A_p \cap A_q$ with the two maps $F \rightarrow \operatorname{colim}_p A_p$ being induced by the maps $A_p \cap A_q \rightarrow A_p$ and $A_p \cap A_q \rightarrow A_q$. We conclude by observing that $\operatorname{colim}_p (A_p \cap A_q) = A_q$. Indeed the map $P \rightarrow (\downarrow q)$ that send $p \in P$ to $p \cap q$ is right adjoint to the inclusion of $(\downarrow q)$ to $P$, so it is a final functor. It hence follows that

$$\operatorname{colim}_{p \in P} A_{p \cap q} = \operatorname{colim}_{p \in q} A_p = A_q$$

So this implies that $F = \operatorname{colim}_q A_q$, with the projection map $F \rightarrow \operatorname{colim}_q A_q$ being the identity, hence proving that $\operatorname{colim}_q A_q \rightarrow X$ is a monomorphism. $\square$

We prove a statement relating van Kampen colimits and the pullback evaluation $\widehat{\operatorname{ev}}$ functor, defined in (1.5). This statement will be needed in Section 8.

**Lemma 2.15.** *Let $D$ be a small category. Let $Y: C \rightarrow [D^{\operatorname{op}}, \mathcal{E}]$ be a diagram with levelwise van Kampen colimit $\operatorname{colim} Y$. Let $p: X \rightarrow Y$ be a Cartesian transformation, which we regard as a $C$-indexed diagram of arrows in $[D^{\operatorname{op}}, \mathcal{E}]$.*

*Let $q: A \rightarrow B$ be a map in $[D^{\operatorname{op}}, \operatorname{Set}]$ with $B$ representable such that $[D^{\operatorname{op}}, \mathcal{E}]$ supports evaluation at $A$. Then $\widehat{\operatorname{ev}}_q$ (valued in arrows of $\mathcal{E}$) preserves the colimit of $p$, the resulting colimit is computed separately on source and target, and all maps of the colimit cocone are pullback squares.*

*Proof.* First note that by levelwise effectivity of $\operatorname{colim} Y$, we obtain $\operatorname{colim} X$ (and hence $\operatorname{colim} p$). The square $p_c \rightarrow \operatorname{colim} p$ is a pullback for all $c \in C$.

Consider the functor $F$ sending an arrow $M \rightarrow N$ in $[D^{\operatorname{op}}, \mathcal{E}]$ to the sequence of arrows

$$M(B) \longrightarrow M(A) \times_{N(A)} N(B) \longrightarrow N(B).$$

The first arrow is the pullback evaluation at $q$ of $M \rightarrow N$. Evaluation preserves limits, in particular pullbacks. By pullback pasting, the action of $F$ on a map of arrows that is a pullback is a pasting of pullback squares.

14

Let us inspect the action of $F$ on the colimit cocone of $p$. It will suffice to show that it results in objectwise colimit cocones. Since the maps of the colimit cocone of $p$ are pullback squares, we obtain pastings of pullback squares upon applying $F$. Recall that $\mathrm{ev}_B$ is computed by evaluation at the object representing $B$. So by assumption, $(\mathrm{colim}\,Y)(B) = \mathrm{ev}_B(\mathrm{colim}\,Y)$ is colimit of $\mathrm{ev}_B \circ Y$ and van Kampen. The claim follows by universality of this van Kampen colimit. $\square$

### 3 An enriched small object argument

The goal of this section is to develop a version of the small object argument that allows us to construct weak factorisation systems on the category of simplicial objects $\mathfrak{s}\mathcal{E}$, where $\mathcal{E}$ is a countably lextensive category. In view of our application to both simplicial objects in Section 4 and semisimplicial objects in Section 12, we develop our small object argument for diagram categories $\mathcal{E}^D$ in general. Importantly, our weak factorisation systems are *enriched*, in the sense of [Rie14]. We will be constructing $\mathrm{Psh}\,\mathcal{E}$-enriched weak factorisation systems on $\mathcal{E}^D$, where $\mathrm{Psh}\,\mathcal{E}$ denotes the category of presheaves over $\mathcal{E}$. This is because the category of diagrams $\mathcal{E}^D$ is not necessarily $\mathcal{E}$-enriched, but it is $\mathrm{Psh}\,\mathcal{E}$-enriched, as we now recall.

For $E \in \mathcal{E}$ and $X \in \mathcal{E}^D$, we define $E \times X \in \mathcal{E}^D$ by letting

$$(E \times X)_d =_{\mathrm{def}} E \times X_d. \quad (3.1)$$

Given $X, Y \in \mathcal{E}^D$, we then define the hom-object $\mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(X, Y) \in \mathrm{Psh}\,\mathcal{E}$ by letting:

$$\begin{array}{rcl} \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(X, Y) & : & \mathcal{E}^{\mathrm{op}} \to \mathrm{Set} \\ & : & E \mapsto \mathrm{Hom}_{\mathrm{Set}}(E \times X, Y) \end{array}$$

This makes $\mathcal{E}^D$ into a $\mathrm{Psh}\,\mathcal{E}$-enriched category, so that the formula in (3.1) provides the tensor of $E \in \mathrm{Psh}\,\mathcal{E}$ and $X \in \mathcal{E}^D$ with respect to this enrichment. When the presheaf is representable, the representing object is denoted by $\mathrm{Hom}_{\mathcal{E}}(X, Y)$.

Using the enrichment, we can define an internal version of the familiar lifting problems involved in the definition of a weak factorisation systems. For morphisms $i: A \to B$ and $p: X \to Y$ in $\mathcal{E}^D$, we define the *presheaf of lifting problems* of $i$ against $p$ by letting

$$\mathrm{Prob}_{\mathrm{Psh}\,\mathcal{E}}(i, p) =_{\mathrm{def}} \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(A, X) \times_{\mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(A, Y)} \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(B, Y).$$

When the relevant hom-objects are representable, then so is $\mathrm{Prob}_{\mathrm{Psh}\,\mathcal{E}}(i, p)$. In this case, we write $\mathrm{Prob}_{\mathcal{E}}(i, p)$ for its representing object and call it the *object of lifting problems* of $i$ against $p$. Note that the induced pullback hom of $i$ and $p$ (cf. Remark 1.2) has the form

$$\widehat{\mathrm{Hom}}_{\mathrm{Psh}\,\mathcal{E}}(i, p) : \mathrm{Hom}_{\mathrm{Psh}\,\mathcal{E}}(B, X) \to \mathrm{Prob}_{\mathrm{Psh}\,\mathcal{E}}(i, p) \quad (3.2)$$

Again, if the objects are representable, we have also an induced pullback hom in $\mathcal{E}$, which has the form

$$\widehat{\mathrm{Hom}}_{\mathcal{E}}(i, p) : \mathrm{Hom}_{\mathcal{E}}(B, X) \to \mathrm{Prob}_{\mathcal{E}}(i, p). \quad (3.3)$$

We are ready to define the $\mathrm{Psh}\,\mathcal{E}$-enriched counterparts of the standard lifting properties.

**Definition 3.1.** Let $i: A \to B$ and $p: X \to Y$ be morphisms of $\mathcal{E}^D$.

- We say that $i$ has the $\mathrm{Psh}\,\mathcal{E}$-enriched *left lifting property* with respect to $p$ and that $p$ has the $\mathrm{Psh}\,\mathcal{E}$-enriched *right lifting property* with respect to $i$ if the induced pullback hom in (3.2) is a split epimorphism in $\mathrm{Psh}\,\mathcal{E}$.

15

- We say that $i$ has the $\mathcal{E}$-enriched left lifting property with respect to $p$ and that $p$ has the $\mathcal{E}$-enriched right lifting property with respect to $i$ if the induced pullback hom in (3.3) exists and is a split epimorphism in $\mathcal{E}$.

Since the Yoneda embedding is fully faithful and preserves pullbacks, as soon as all relevant $\mathcal{E}$-valued hom-objects exist, the $\text{Psh}\,\mathcal{E}$-enriched left lifting property and $\mathcal{E}$-enriched left lifting property are equivalent and $\text{Prob}_{\text{Psh}\,\mathcal{E}}(i,p)$ is represented by $\text{Prob}_{\mathcal{E}}(i,p)$.

In both $\text{Psh}\,\mathcal{E}$ and $\mathcal{E}$, the class of split epimorphisms is the right class of a weak factorization system, with left class given by complemented inclusions. As such, it enjoys a number of standard closure properties. Our notions of enriched lifting property are defined from this class via the pullback hom. Because of this, the classes of maps defined below by an $\text{Psh}\,\mathcal{E}$-enriched lifting property will inherit corresponding closure properties. For example, split epimorphisms are closed under retracts. Thus, classes of maps defined by an $\text{Psh}\,\mathcal{E}$-enriched lifting property are closed under retracts.

As is usual, we extend the terminology of enriched lifting properties from maps to classes of maps on either side by universal quantification.

**Definition 3.2.** Let $I = \{i : A_i \to B_i\}$ be a set of morphisms of $\mathcal{E}^D$.

- An (enriched) $I$-fibration is a morphism with the enriched right lifting property with respect to $I$.
- An (enriched) $I$-cofibration is a morphism with the enriched left lifting property with respect to $I$-fibrations.

When the left map of a $\text{Psh}\,\mathcal{E}$-enriched lifting problem comes from $\text{Set}^D$ via levelwise application of the operation in (2.2), we may simplify the lifting problem (assuming some technical conditions hold). Indeed, the pullback hom (3.3) reduces to a pullback evaluation. We record this in the next couple of statements, which are phrased using $D^{\text{op}}$ instead of $D$ in order to exploit the language of representable functors. We make use of the evaluation functor $\text{ev}_K : [D^{\text{op}}, \mathcal{E}] \to \mathcal{E}$ defined for finite colimits $K$ of representables by letting:

$$\text{ev}_K(X) = \int_{d \in D^{\text{op}}} X_d^{K_d}.$$

This generalises the evaluation functor defined in Eq. (1.4), which is the case $D = \Delta$. As in Remark 1.1, we may equivalently view $\text{ev}_K(X)$ as the $K$-weighted limit of $X$, which implies that $\text{ev}$ is a (partial) two-variable functor.

**Lemma 3.3.** Let $K \in [D^{\text{op}}, \text{Set}]$ be levelwise countable.

(i) There is an isomorphism $(E \times \underline{K})_d \cong K_d \cdot E$ natural in $K$, $E \in \mathcal{E}$, and $d \in D$.
(ii) Assume that $K$ is a finite colimit of representables. Then the hom-presheaf $\text{Hom}_{\text{Psh}\,\mathcal{E}}(\underline{K}, X)$ is representable for $X \in [D^{\text{op}}, \mathcal{E}]$ and we have an isomorphism $\text{Hom}_{\mathcal{E}}(\underline{K}, X) \cong \text{ev}_K(X)$, natural in $K$ and $X \in [D^{\text{op}}, \mathcal{E}]$.

*Proof.* Part (i) follows from Lemma 2.6. For part (ii), part (i) implies that $\text{Hom}_{\text{Psh}\,\mathcal{E}}(\underline{K}, X)$ is naturally isomorphic to the $\mathcal{E}$-presheaf $E \mapsto \text{Hom}_{\text{Set}}(d \mapsto K_d \cdot E, X)$. A representing object for it is by definition the $K$-weighted limit of $X$, i.e., $\text{ev}_K(X)$. This exists in our setting for $K$ a finite colimit of representables. $\square$

16

**Proposition 3.4.** Let $i: A \to B$ be a map in $[D^{\text{op}}, \text{Set}]$ between objects that are levelwise countable and finite colimits of representables and let $p: X \to Y$ be a map in $[D^{\text{op}}, \mathcal{E}]$. Then the following are equivalent:

- (i) $\underline{i}: \underline{A} \to \underline{B}$ has the $\mathcal{E}$-enriched left lifting property with respect to $p$,
- (ii) the pullback evaluation $\widehat{\text{ev}}_i(p)$ is a split epimorphism in $\mathcal{E}$.

*Proof.* This is an immediate consequence of part (ii) of Lemma 3.3. $\square$

Proposition 3.4 will be used in Section 4 to relate (trivial) Kan fibrations in $\mathfrak{s}\mathcal{E}$ in the sense of Definition 1.3 with fibrations in the sense of Definition 3.2 with respect to the images in $\mathfrak{s}\mathcal{E}$ of horn inclusions (boundary inclusions, respectively) under the operation $(-): \text{Set} \to \mathcal{E}$.

We now turn our attention to $\text{Psh}\mathcal{E}$-enriched weak factorisation systems.

**Definition 3.5.** A $\text{Psh}\mathcal{E}$-enriched weak factorisation system on $\mathcal{E}^D$ is a pair $(\mathcal{L}, \mathcal{R})$ of classes of morphisms of $\mathcal{E}^D$ such that:

- a morphism belongs to $\mathcal{L}$ if and only if it has the $\text{Psh}\mathcal{E}$-enriched left lifting property with respect to $\mathcal{R}$;
- a morphism belongs to $\mathcal{R}$ if and only if it has the $\text{Psh}\mathcal{E}$-enriched right lifting property with respect to $\mathcal{L}$;
- every morphism of $\mathcal{E}^D$ factors as an $\mathcal{L}$-morphism followed by an $\mathcal{R}$-morphism.

The classes $\mathcal{L}$ and $\mathcal{R}$ in the above definition are closed under retract as they are characterized by $\text{Psh}\mathcal{E}$-enriched lifting properties.

We will abbreviate “$\text{Psh}\mathcal{E}$-enriched lifting property” to “enriched lifting property”, but we will be explicit about cases where it coincides with the $\mathcal{E}$-enriched lifting property.

**Lemma 3.6.** Let $(\mathcal{L}, \mathcal{R})$ be an enriched weak factorisation system.

- (i) A morphism is in $\mathcal{L}$ if and only if it has the ordinary left lifting property with respect to $\mathcal{R}$.
- (ii) A morphism is in $\mathcal{R}$ if and only if it has the ordinary right lifting property with respect to $\mathcal{L}$.

In particular, $(\mathcal{L}, \mathcal{R})$ is also an ordinary weak factorisation system.

*Proof.* For (i), a morphism of $\mathcal{L}$ has the ordinary left lifting property with respect to $\mathcal{R}$ by evaluating the hom-presheaves at $1 \in \mathcal{E}$. Conversely, a morphism with the ordinary lifting property admits a lift against the second factor of its $(\mathcal{L}, \mathcal{R})$-factorisation, thus making it into a retract of the first factor (cf. also the proof of Proposition 3.17). The conclusion follows since $\mathcal{L}$ is closed under retracts. Part (ii) follows by duality. $\square$

We will fix a set $I$ and study a version of the small object argument that produces an enriched weak factorisation system of $I$-cofibrations and $I$-fibrations under suitable assumptions.

17

**Definition 3.7.** Let $i: A \to B$ and $p: X \to Y$ be morphisms of $\mathcal{E}^D$. Assume that we have a factorisation

![img-5.jpeg](img-5.jpeg)

We say that $p$ satisfies the $X'$-partial enriched right lifting property with respect to $i$ if there is a lift in the diagram

![img-6.jpeg](img-6.jpeg)

Such partial lifting properties are a crucial ingredient of the small object argument, but they are only tractable when $i$ is a levelwise complemented inclusion. This is thanks to the next two lemmas, where we use the tensor defined in (3.1).

**Lemma 3.8.** *Levelwise complemented inclusions in $\mathcal{E}^D$ are closed under:*

- (i) $E \times -$ for all $E \in \mathcal{E}$;
- (ii) *countable coproducts*;
- (iii) *pushouts along arbitrary morphisms*;
- (iv) *sequential colimits*;
- (v) *retracts*.

*Moreover, the colimits of parts (ii), (iii) and (iv) are preserved by $E \times -$ for all $E \in \mathcal{E}$.*

*Proof.* The functor $E \times -$ and all the colimits mentioned are computed levelwise in $\mathcal{E}$, so the results boil down to the fact that complemented inclusions in $\mathcal{E}$ are stable under all these constructions. Stability under $E \times -$ follows from distributivity of product over coproduct in complemented categories: if $A \to A \sqcup B$ is a complemented inclusion, then its image under $E \times -$ is $E \times A \to (E \times A) \sqcup (E \times B)$ and is a complemented inclusion. The case of a countable coproduct is also clear: if $A_k \to A_k \sqcup B_k$ is a family of complemented inclusions, then their coproduct can be written as $\coprod A_k \to (\coprod A_k) \sqcup (\coprod B_k)$. Stability under pushout and sequential composition follows from Lemma 2.9. The fact that they are preserved by $E \times -$ follows from Lemma 2.9. The case of retracts can be deduced from the stability under limits proved in Lemma 2.10 as retracts can be seen as limits. $\square$

**Lemma 3.9.** *Let $p: X \to Y$ be a map in $\mathcal{E}^D$ and $\mathcal{L}$ a class of levelwise complemented inclusions in $\mathcal{E}^D$ that have the enriched left lifting property with respect to $p$. Then $\mathcal{L}$ is closed under the following operations:*

- (i) *tensors by objects of $\mathcal{E}$*,
- (ii) *countable coproducts*,

18

(iii) *pushouts*,
(iv) *colimits of sequences*,
(v) *retracts*.

*Proof.* For $X \in \mathcal{E}^D$, the functor $\operatorname{Hom}_{\operatorname{Psh}\mathcal{E}}(-, X)$ is not necessarily an adjoint. However, since split epimorphisms are closed under limits dual to the colimits listed above, it is sufficient to verify that it carries these colimits to limits. (In the case of tensors this means that $\operatorname{Hom}_{\operatorname{Psh}\mathcal{E}}(F \times A, X) \cong \operatorname{Hom}_{\operatorname{Psh}\mathcal{E}}(A, X)^{\mathcal{E}(-, F)}$ for all $F \in \mathcal{E}$.) This follows directly from these colimits being preserved by the tensors as recorded in Lemma 3.8. $\square$

**Definition 3.10.** Let $A \in \mathcal{E}^D$. We say that $A$ is *finite* if the following hold:

(i) $\operatorname{Hom}_{\mathcal{E}}(A, X)$ exists for every $X \in \mathcal{E}^D$;
(ii) $\operatorname{Hom}_{\mathcal{E}}(A, -)$ preserves colimits of sequences of levelwise complemented inclusions;
(iii) $\operatorname{Hom}_{\mathcal{E}}(A, -)$ sends levelwise complemented inclusions to complemented inclusions.

The next lemma provides a supply of finite objects. For its statement, recall the functor $S \mapsto \underline{S}$ from Section 2. As Lemma 3.3, it is formulated using $D^{\mathrm{op}}$ instead of $D$ for convenience.

**Lemma 3.11.** *Let $D$ be a locally countable category and assume that presheaf $A \in \operatorname{Psh} D$ is a finite colimit of representables. Then $\underline{A} \in [D^{\mathrm{op}}, \mathcal{E}]$ is finite.*

*Proof.* First, note that since $D$ is locally countable, $A$ is levelwise countable and thus $\underline{A}$ exists. By part (ii) of Lemma 3.3, $\operatorname{Hom}_{\mathcal{E}}(\underline{A}, -)$ exists and is given by $\operatorname{ev}_A$ (evaluation at $A$). Call $X \in \operatorname{Psh} D$ $\mathcal{E}$-finite if it satisfies the conditions of Definition 3.10 with $\operatorname{Hom}_{\mathcal{E}}(X, -)$ replaced by $\operatorname{ev}_X$. Our goal then is to show that $A$ is $\mathcal{E}$-finite. This follows from the following observations:

- Representables are $\mathcal{E}$-finite. For this, recall that evaluation at a representable is given by evaluation at the representing object. Part (ii) uses part (ii) of Corollary 2.12 to see that the colimit is computed levelwise.
- $\mathcal{E}$-finite presheaves are closed under finite colimits. For this, we use that the partial two-variable functor $\operatorname{ev}$ sends colimits in its first argument to limits. Part (i) holds since $\mathcal{E}$ has finite limits. Part (ii) holds since finite limits preserve colimits of sequences of complemented inclusions in $\mathcal{E}$ (Lemma 2.11). Part (iii) holds since complemented inclusions in $\mathcal{E}$ are closed under finite limits (part (ii) of Lemma 2.10). $\square$

The hypothesis of finiteness is used in the next result, where we use the notion of an $I$-fibration in the sense of Definition 3.2.

**Lemma 3.12.** *Assume that the domains and codomains of morphisms of $I$ are finite. Let $Y \in \mathcal{E}^D$ and $(X_k \to X_{k+1} \mid k \in \mathbb{N})$ be a sequence of morphisms in $\mathcal{E}^D \downarrow Y$. If every $X_k \to X_{k+1}$ is a levelwise complemented inclusion and each $p_k: X_k \to Y$ has $X_{k+1}$-partial enriched right lifting property with respect to $I$, then $\operatorname{colim}_k X_k \to Y$ is an $I$-fibration.*

19

Proof. Fix a morphism $i: A \to B$ of $I$. Since $A$ and $B$ are finite, the given partial enriched lifting properties are $\mathcal{E}$-enriched. Moreover, since $X_k \to X_{k+1}$ is a levelwise complemented inclusion, Lemma 2.10 implies that $\mathrm{Prob}_{\mathcal{E}}(i, p_k) \to \mathrm{Prob}_{\mathcal{E}}(i, p_{k+1})$ is a complemented inclusion.

Proceeding by induction with respect to $k$, we can pick lifts

![img-7.jpeg](img-7.jpeg)

that are natural in $k$. Indeed, since $\mathrm{Prob}_{\mathcal{E}}(i, p_{k-1}) \to \mathrm{Prob}_{\mathcal{E}}(i, p_k)$ is a complemented inclusion, we can construct a compatible lift by assembling a previously constructed lift on $\mathrm{Prob}_{\mathcal{E}}(i, p_{k-1})$ with a given lift on its complement. Since $A$ and $B$ are finite, we have

$$\underset{k}{\operatorname{colim}} \operatorname{Hom}_{\mathcal{E}}(B, X_k) = \operatorname{Hom}_{\mathcal{E}}(B, \underset{k}{\operatorname{colim}} X_k)$$

and

$$\begin{aligned} \underset{k}{\operatorname{colim}} \operatorname{Prob}_{\mathcal{E}}(i, p_k) &= \underset{k}{\operatorname{colim}} \left( \operatorname{Hom}_{\mathcal{E}}(A, X_k) \times_{\operatorname{Hom}_{\mathcal{E}}(A, Y)} \operatorname{Hom}_{\mathcal{E}}(B, Y) \right) \\ &= \left( \underset{k}{\operatorname{colim}} \operatorname{Hom}_{\mathcal{E}}(A, X_k) \right) \times_{\operatorname{Hom}_{\mathcal{E}}(A, Y)} \operatorname{Hom}_{\mathcal{E}}(B, Y) \\ &= \operatorname{Hom}_{\mathcal{E}}(A, \underset{k}{\operatorname{colim}} X_k) \times_{\operatorname{Hom}_{\mathcal{E}}(A, Y)} \operatorname{Hom}_{\mathcal{E}}(B, Y) \\ &= \operatorname{Prob}_{\mathcal{E}}(i, \underset{k}{\operatorname{colim}} p_k), \end{aligned}$$

the latter by universality of sequential colimits of complemented inclusions in $\mathcal{E}$ (Lemma 2.9). Thus we obtain a diagram

![img-8.jpeg](img-8.jpeg)

where the bottom map is an identity, i.e., these lifts form a section that exhibits $\operatorname{colim}_k X_k \to Y$ as an $I$-fibration.

The following lemma isolates a simpler version of the inductive step in the construction of lifts in Lemma 3.12. It is needed in Section 8.

Lemma 3.13. Let

![img-9.jpeg](img-9.jpeg)

20

be a pullback square in $\mathcal{E}^D$ with $A \to B$ a levelwise complemented inclusion. Let $i: U \to V$ be a map in $\mathcal{E}^D$ between finite objects such that $\widehat{\mathrm{Hom}}_{\mathcal{E}}(i, p)$ and $\widehat{\mathrm{Hom}}_{\mathcal{E}}(i, q)$ have sections. Then, for any section $s$ of $\widehat{\mathrm{Hom}}_{\mathcal{E}}(i, p)$, there is a section $t$ of $\widehat{\mathrm{Hom}}_{\mathcal{E}}(i, q)$ such that the diagram

$$\begin{array}{c} \operatorname{Hom}_{\mathcal{E}}(V, X) \longrightarrow \operatorname{Hom}_{\mathcal{E}}(V, Y) \\ \widehat{\operatorname{Hom}}_{\mathcal{E}}(i, p) \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{Prob}_{\mathcal{E}}(i, p) \longrightarrow \operatorname{Prob}_{\mathcal{E}}(i, q). \end{array}$$

forms a morphism of retracts.

Proof. The map $\operatorname{Prob}_{\mathcal{E}}(i, p) \to \operatorname{Prob}_{\mathcal{E}}(i, q)$ is a complemented inclusion by Lemma 2.10. We construct $t$ by using $s$ on $\operatorname{Prob}_{\mathcal{E}}(i, p)$ and a given section on its complement. $\square$

**Theorem 3.14** (Enriched small object argument). Let $I = (i: A_i \to B_i \mid i \in I)$ be a countable set of levelwise complemented inclusions between finite objects of $\mathcal{E}^D$. Then $I$-cofibrations and $I$-fibrations form an enriched weak factorisation system in $\mathcal{E}^D$.

Proof. For a morphism $p_0: X_0 \to Y$ we form a sequence $X_0 \to X_1 \to X_2 \to \ldots$ in $\mathcal{E} \downarrow Y$ by iteratively taking pushouts

$$\begin{array}{c} \coprod_{i \in I} \operatorname{Prob}_{\mathcal{E}}(i, p_k) \times A_i \longrightarrow X_k \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{i \in I} \operatorname{Prob}_{\mathcal{E}}(i, p_k) \times B_i \longrightarrow X_{k+1} \\ \longrightarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad Y. \end{array}$$

The adjoint transpose of $\operatorname{Prob}(i, p_k) \times B_i \to X_{k+1}$ witnesses the $X_{k+1}$-partial enriched right lifting property of $p_k$ with respect to $i$. Moreover, by Lemma 3.8, $X_k \to X_{k+1}$ is a levelwise complemented inclusion. Thus Lemma 3.12 applies and shows that $\operatorname{colim}_k X_k \to Y$ is an $I$-fibration. Using Lemma 3.9, we show that $X_0 \to \operatorname{colim}_k X_k$ is an $I$-cofibration. $\square$

**Remark 3.15.** Essentially the the same argument used to prove Theorem 3.14 can be used to prove a more general statement. Namely, instead of $\mathcal{E}^D$ we consider an $\mathcal{E}$-module $\mathcal{C}$, i.e., a category equipped with a tensor functor $- \times =: \mathcal{E} \times \mathcal{C} \to \mathcal{C}$ that is associative in the sense that the functor $\mathcal{E} \to \operatorname{End}\mathcal{C}$, given by $E \mapsto (E \times -)$, is monoidal (with respect to the Cartesian product on $\mathcal{E}$ and functor composition on $\operatorname{End}\mathcal{C}$). Then $\mathcal{C}$ carries a $\operatorname{Psh}\mathcal{E}$-enrichment defined in the same way as the one on $\mathcal{E}^J$ which yields notions of an enriched lifting property and an enriched weak factorisation system. The complication lies in the fact that the definition of levelwise complemented inclusions is not available in $\mathcal{C}$. However, if we assume that $\mathcal{C}$ is equipped with a class of morphisms $\mathcal{D}$ satisfying the conclusion of Lemma 3.8, then the proof of Theorem 3.14 applies without changes. (Note that in this case the notion of finiteness in $\mathcal{C}$ depends on the choice of $\mathcal{D}$.) Examples of categories that can be endowed with such structure include the categories of internal categories in $\mathcal{E}$, internal groupoids in $\mathcal{E}$ and marked simplicial objects in $\mathcal{E}$.

21

We conclude this section by introducing the notion of a cell complex and establish a few results that will be useful later.

**Definition 3.16.** For a family of maps $I = (i: A_i \to B_i \mid i \in I)$, an $\mathcal{E}$-enriched $I$-cell complex is a morphism of $\mathcal{E}^D$ that is a sequential colimit of maps $X \to Y$ arising as pushouts

![img-10.jpeg](img-10.jpeg)

for some family $(E_i)_{i \in I}$ of objects of $E$.

Below, we simply speak of an $I$-cell complex for brevity.

**Proposition 3.17.** *Under the hypotheses of Theorem 3.14, a morphism of $\mathcal{E}^D$ is an $I$-cofibration if and only if it is a codomain retract of an $I$-cell complex. In particular, every $I$-cofibration is a levelwise complemented inclusion.*

*Proof.* A retract of an $I$-cell complex is an $I$-cofibration by Lemma 3.9. It is furthermore a levelwise complemented inclusion by Lemma 3.8. Conversely, let $X \to Y$ be an $I$-cofibration and consider the factorisation $X \to X' \to Y$ defined in the proof of Theorem 3.14. Then $X \to X'$ is an $I$-cell complex by construction. Moreover, $X \to Y$ has the $\text{Psh } \mathcal{E}$-enriched left lifting property with respect to $X' \to Y$ and, in particular, it has the ordinary left lifting property (by evaluating the hom-presheaves at the terminal object). Thus there is a lift in the diagram

![img-11.jpeg](img-11.jpeg)

which exhibits $X \to Y$ as a codomain retract of $X \to X'$.

**Lemma 3.18.** *In the setting of Theorem 3.14, the following hold.*

- (i) *Consider a countable family of maps $f_k$ in the arrow category of $\mathcal{E}^D$. If $f_k$ is an $I$-fibration for all $k$, then so is the coproduct $\coprod_k f$. When $\mathcal{E}$ is $\alpha$-lextensive, the same holds for $\alpha$-coproducts.*
- (ii) *Consider a span $f_0 \leftarrow f_{01} \rightarrow f_1$ in the arrow category of $\mathcal{E}^D$. Assume that both legs form pullback squares and that $f_{01} \rightarrow f_0$ is a levelwise complemented inclusion on codomains. If $f_k$ is an $I$-fibration for $k = 0, 1, 01$, then so is the pushout colim $f$.*
- (iii) *Consider a sequential diagram $f_0 \rightarrow f_1 \rightarrow \dots$ in the arrow category of $\mathcal{E}^D$. Assume that the maps $f_k \rightarrow f_{k+1}$ form pullback squares and are levelwise complemented inclusions on codomains. If $f_k$ is an $I$-fibration for all $i$, then so is colim $f$.*

22

*Proof.* In all three parts, the colimit colim $f$ exists and is computed separately on sources and targets where they form van Kampen colimits by Corollary 2.12. Let $C$ denote the shape of the diagram (which varies over the parts). We check that colim $f$ is an $I$-fibration using Proposition 3.4. For each $i \in I$, given a section of $\widehat{\mathrm{ev}}_i(f_c)$ for $c \in C$, we have to construct a section of $\widehat{\mathrm{ev}}_i(\mathrm{colim}\,f)$. Using Lemma 2.15 and functoriality of colimits, it suffices to construct a family of section of $\widehat{\mathrm{ev}}_i(f_c)$ that is natural in $c \in C$.

For part (i), the naturality is vacuous. For part (ii), we pull the section of $\widehat{\mathrm{ev}}_i(f_1)$ back to a section of $\widehat{\mathrm{ev}}_i(f_{01})$ and then use Lemma 3.13 to replace the section of $\widehat{\mathrm{ev}}_i(f_0)$ by one that coheres with the one of $\widehat{\mathrm{ev}}_i(f_{01})$. For part (iii), we recurse on $k$ and use Lemma 3.13 to replace the given section of $\widehat{\mathrm{ev}}_i(f_{k+1})$ by one that coheres with the one of $\widehat{\mathrm{ev}}_i(f_k)$. In all three cases, the sections form a $D$-shaped natural transformation as required. $\square$

We consider the application functor app: $[\mathcal{C}, \mathcal{D}] \times \mathcal{C} \rightarrow \mathcal{D}$ and record some commonly used facts about pushout applications in the following statement. We regard the pushout application of a natural transformation $[\mathcal{C}, \mathcal{D}]$ to an arrow in $\mathcal{C}$ to be defined if the pushout in the evident commuting square exists. Recall that the pushout application is the induced arrow from the pushout corner.

**Lemma 3.19.** *Let $u: X \rightarrow Y$ be a map in $[\mathcal{C}, \mathcal{D}]$. Then pushout application $\widehat{\mathrm{app}}(u, -): \mathcal{C}^{[1]} \rightarrow \mathcal{D}^{[1]}$ forms a partial functor with the following properties.*

- (i) *Let $c: I \rightarrow \mathcal{C}^{[1]}$ be a diagram of arrows with levelwise colimit (i.e., a colimit that is computed separately on sources and targets in $\mathcal{C}$). If $X$ and $Y$ preserve this levelwise colimit and $\widehat{\mathrm{app}}(u, -)$ is defined on all values of $c$, then $\widehat{\mathrm{app}}(u, -)$ preserves the levelwise colimit of $c$.*
- (ii) *Let $f \rightarrow g$ be a morphism in $\mathcal{C}^{[1]}$ that is a pushout square. If $X$ and $Y$ preserve this pushout and $\widehat{\mathrm{app}}(u, -)$ is defined on $f$ and $g$, then $\widehat{\mathrm{app}}(u, f) \rightarrow \widehat{\mathrm{app}}(u, g)$ is a pushout square.*
- (iii) *For an ordinal $\alpha$, let $A_0 \rightarrow A_1 \rightarrow \dots \rightarrow A_\alpha$ be an $\alpha$-composition in $\mathcal{C}$. If this $\alpha$-composition is preserved by $X$ and $Y$ and $\widehat{\mathrm{app}}(u, -)$ is defined on $A_\beta \rightarrow A_{\beta'}$ for $\beta \leq \beta' \leq \alpha$, then $\widehat{\mathrm{app}}(u, -)$ preserves the given the $\alpha$-composition and the resulting step map at $\beta < \alpha$ is a pushout of $\widehat{\mathrm{app}}(u, -)$ applied to $A_\beta \rightarrow A_{\beta+1}$.*

*Proof.* This is folklore technique in abstract homotopy theory. Similar proofs (in a slightly different context) can be found in [RV14, Sections 4 and 5], in particular [RV14, Lemma 4.8] for part (i) and [RV14, Lemma 5.7] for parts (ii) and (iii). $\square$

**Lemma 3.20.** *Let $F, G: \mathcal{E}^D \rightarrow \mathcal{E}^{D'}$ be two functors that preserves levelwise complemented maps, their pushouts and their sequential compositions. We assume that $F$ and $G$ are equipped with isomorphisms*

$$F(E \times X) \cong E \times F(X) \qquad G(E \times X) \cong E \times G(X)$$

*natural in $E \in \mathcal{E}$ and $X \in \mathcal{E}^D$ (respectively, $X \in \mathcal{E}^{D'}$) and let $\lambda: F \rightarrow G$ be a natural transformation compatible with these isomorphisms. Let $I_D \subseteq (\mathcal{E}^D)^{[1]}$ and $I_{D'} \subseteq (\mathcal{E}^{D'})^{[1]}$ be countable sets of arrows satisfying the conditions of Theorem 3.14. If for each $i \in I_D$, the pushout application $\widehat{\mathrm{app}}(\lambda, i)$ is an $I_{D'}$-cofibration, then for each $I_D$-cofibration $i$, the pushout application $\widehat{\mathrm{app}}(\lambda, i)$ is an $I_{D'}$-cofibration.*

23

*Proof.* First, because of Lemma 3.8, all $I_D$-cofibrations are levelwise complemented inclusions, so their image under $F$ are again levelwise complemented inclusions and hence pushouts along them exist. This shows that $\widehat{\mathrm{app}}(\lambda, i)$ always exists when $i$ is an $I_D$-cofibration.

By Proposition 3.17, a general a $I_D$-cofibration is a retract of a sequential composite of pushouts of countable coproducts of the form $E \times A \rightarrow E \times B$ for a map $A \rightarrow B$ in $I_D$ and $E \in \mathcal{E}$. A map $E \times i: E \times A \rightarrow E \times B$ is sent by $\widehat{\mathrm{app}}(\lambda, -)$ to the map $E \times \widehat{\mathrm{app}}(\lambda, i)$, so as we are assuming that for each $i \in I_D$ the map $\widehat{\mathrm{app}}(\lambda, i)$ is an $I_{D'}$-cofibration, it follows that the map of the form $E \times i$ are also sent to $I_{D'}$-cofibration.

Using Lemma 3.19 one concludes that any transfinite composition of pushouts of maps of the form $E \times i$ for $i \in I_D$ is also sent by $\widehat{\mathrm{app}}(\lambda, -)$ to a $I_{D'}$-cofibration. Finally, as $\widehat{\mathrm{app}}(\lambda, -)$ is a functor it preserves retract, and so retracts of such maps are also sent to $I_{D'}$-cofibration, and this concludes the proof as any $I_D$-cofibration is a retract of such a transfinite composition of pushouts. $\square$

**Proposition 3.21.** *Let $j: X \rightarrow Y$ be a morphism of $\mathcal{E}^D$. Under the hypothesis of Theorem 3.14, if $i \times j$ is an $I$-cofibration for all $i \in I$, then $f \times j$ is an $I$-cofibration for all $I$-cofibrations $f$.*

*Proof.* We apply Lemma 3.20 to the natural transformation $- \times j: - \times X \rightarrow - \times Y$ of endofunctors on $\mathcal{E}^D$. Let us check the needed preservation properties of the endofunctor $- \times Z$ on $\mathcal{E}^D$ for $Z \in \mathcal{E}$. Preservation of levelwise complemented inclusions follows from preservation of complemented inclusions in $\mathcal{E}$ under product with a fixed object (a consequence of lextensivity). Preservation of the relevant colimits involving levelwise complemented inclusions is an instance of Corollary 2.12. Preservation of tensors with objects of $\mathcal{E}$ reduces to associativity and commutativity of products in $\mathcal{E}$; this is natural, so the map $- \times j: - \times X \rightarrow - \times Y$ respects the witnessing isomorphism as appropriate. $\square$

## 4 The two weak factorisation systems

In this section we consider a countably lextensive category $\mathcal{E}$. We construct two weak factorisation systems on the category $\mathfrak{s}\mathcal{E}$ of simplicial objects in $\mathcal{E}$ that will be proven to form a model structure in Section 9. Our main goal is to describe the resulting cofibrations in Theorem 4.6 which relies on identification of one of the factorisation systems as a Reedy factorisation system (Proposition 4.3). In our setting, the category $\mathfrak{s}\mathcal{E}$ has relatively few colimits and consequently much of this section is committed to discussion of the Reedy theory under these weak hypotheses.

We will use the enriched small object argument of Theorem 3.14 with the generating sets obtained by applying the partial functor of (2.2) to the sets of boundary inclusions and horn inclusions in (1.6), i.e.,

$$I_{\mathfrak{s}\mathcal{E}} = \{ \underline{\partial \Delta[n]} \rightarrow \underline{\Delta[n]} \mid n \geq 0 \} \text{ and } J_{\mathfrak{s}\mathcal{E}} = \{ \underline{\Lambda^k[n]} \rightarrow \underline{\Delta[n]} \mid n \geq k \geq 0, n > 0 \}.$$

We will refer to $\underline{\Delta[n]}$ as a simplex in $\mathfrak{s}\mathcal{E}$ and similarly for boundaries and horns. We say that a map in $\mathfrak{s}\mathcal{E}$ is a *cofibration* if it is a $I_{\mathfrak{s}\mathcal{E}}$-cofibration and that it is a *trivial cofibration* if it is a $J_{\mathfrak{s}\mathcal{E}}$-cofibration. Moreover, we note that notions of (Kan) fibrations and trivial (Kan) fibrations as introduced in Definition 1.3 coincide with the notions of $J_{\mathfrak{s}\mathcal{E}}$-fibrations and $I_{\mathfrak{s}\mathcal{E}}$-fibration.

**Proposition 4.1.** *Let $f: X \rightarrow Y$ be a map in $\mathfrak{s}\mathcal{E}$.*

- (i) $f$ is a *fibration* if and only if it is a $J_{\mathfrak{s}\mathcal{E}}$-fibration;
- (ii) $f$ is a *trivial fibration* if and only if it is a $I_{\mathfrak{s}\mathcal{E}}$-fibration.

24

Proof. By Proposition 3.4, the condition of Definition 1.3 for $f$ being a (trivial) Kan fibration is equivalent to the $\mathcal{E}$-enriched right lifting property of $f$ with respect to $J_{\mathfrak{s}\mathcal{E}}$ (respectively, $I_{\mathfrak{s}\mathcal{E}}$). $\square$

The existence of weak factorisation systems linking these classes is a direct consequence of the results of Section 3.

**Theorem 4.2.** Let $\mathcal{E}$ be a countably lextensive category. The category $\mathfrak{s}\mathcal{E}$ of simplicial objects in $\mathcal{E}$ admits two weak factorisation systems:

- cofibrations and trivial fibrations, cofibrantly generated by $I_{\mathfrak{s}\mathcal{E}}$;
- trivial cofibrations and fibrations, cofibrantly generated by $J_{\mathfrak{s}\mathcal{E}}$.

Proof. All morphisms of $I_{\mathfrak{s}\mathcal{E}}$ and $J_{\mathfrak{s}\mathcal{E}}$ are levelwise complemented inclusions since $S \mapsto \underline{S}$ preserves complemented inclusions. Moreover, their domains and codomains are finite colimits of representables and thus Lemma 3.11 implies that the assumptions of Theorem 3.14 are satisfied. $\square$

Recall that $\mathcal{E}$ admits a weak factorisation system consisting of complemented inclusions as left maps and split epimorphisms as right maps. We now wish to characterise our cofibrations and trivial fibrations in terms of the induced Reedy weak factorisation on $\mathfrak{s}\mathcal{E}$. Traditional treatments of Reedy theory such as [RV14] tacitly assume that the underlying category is bicomplete; this is not the case here. Separately, there is the treatment [RB06] of Reedy theory in the context of a (co)fibration category, but it only considers Reedy left or right maps between Reedy left or right objects; in our setting, not all objects are Reedy cofibrant or fibrant. Let us thus discuss some of the details of the Reedy weak factorisation system on $\mathfrak{s}\mathcal{E}$.

Let $m \geq 0$. We write $\Delta^{\mathrm{op}}[m]$ for $\Delta([m], -)$, i.e., the functor in $[\Delta, \mathsf{Set}]$ corepresented by $m$. The coboundary $\partial\Delta^{\mathrm{op}}[m]$ of $\Delta$ at level $m$ is the subobject of $\Delta^{\mathrm{op}}[m]$ consisting of those maps which are not face operators. Equivalently, $\partial\Delta^{\mathrm{op}}[m]_k \subseteq \Delta([m], [k])$ consists of those maps $[m] \to [k]$ whose degeneracy-face factorisation has non-identity degeneracy operator.

Let $A \in \mathfrak{s}\mathcal{E}$. The latching object $L_m A$, if it exists, is the colimit of $A$ weighted by $\partial\Delta^{\mathrm{op}}[m]$. We have a canonical map $L_m A \to A$.

Let $i: A \to B$ be a map in $\mathfrak{s}\mathcal{E}$ and $m \geq 0$. We wish to consider the relative latching map of $i$. Ordinarily, we would define it as the map $A_m \sqcup_{L_m A} L_m B \to B_m$. However, its domain depends on the existence of the latching objects $L_m A$ and $L_m B$ and a pushout. We wish to avoid these assumptions. Consider the functor $\mathfrak{s}\mathcal{E} \to \mathsf{Set}$ sending $X$ to the set of pairs consisting of a map $u: A_m \to X$ and a natural family $v_f: B_k \to X$ for $f: [m] \to [k]$ not a face operator such that $u \circ A f = v_f \circ i_k$. If this functor has a corepresenting object, we denote it by $A_m \sqcup_{L_m A} L_m B$ and obtain the relative latching map $A_m \sqcup_{L_m A} L_m B \to B_m$ of $i$ at level $m$. If $L_m A$ and $L_m B$ exist, this agrees with the description in terms of the pushout suggested by our notation.

We desire a more abstract view on the relative latching map. For this, we introduce the notion of pushout weighted colimit. Consider the two-variable functor

$$H: [\Delta, \mathsf{Set}]^{\mathrm{op}} \times \mathfrak{s}\mathcal{E}^{\mathrm{op}} \to [\mathcal{E}, \mathsf{Set}] \quad (4.1)$$

sending $W$ and $X$ to $I \mapsto [\Delta, \mathsf{Set}](W, \mathcal{E}(X(-), I))$ Recall that a $W$-weighted colimit of $X$, denoted $\operatorname{colim}^W X$, is by definition a representing object of $H(W, X)$. The pullback construction of $H$ is the two-variable functor

$$\widehat{H}: ([\Delta, \mathsf{Set}]^{\mathrm{op}})^{[1]} \times (\mathfrak{s}\mathcal{E}^{\mathrm{op}})^{[1]} \to [\mathcal{E}, \mathsf{Set}]^{[1]}$$

25

sending $w: U \rightarrow V$ in $[\Delta, \mathsf{Set}]$ and $i: A \rightarrow B$ in $\mathfrak{sE}$ to the map

$$H(V, B) \rightarrow H(V, A) \times_{H(U, A)} H(U, B) \quad (4.2)$$

in $[\mathcal{E}, \mathsf{Set}]$. Assume that domain and codomain of (4.2) have representing objects $Y$ and $X$, respectively (in particular, $Y$ is the $V$-weighted colimit of $B$). Then under the Yoneda embedding of $\mathcal{E}^{\mathrm{op}}$ into $[\mathcal{E}, \mathsf{Set}]$, (4.2) corresponds to a map $X \rightarrow Y$ in $\mathcal{E}$. We define this to be the *pushout weighted colimit* with $w: U \rightarrow V$ of $i: A \rightarrow B$ and denote it by $\widehat{\operatorname{colim}}^w i$. It forms a partial two-variable functor

$$\widehat{\operatorname{colim}}^{(-)}(=): [\Delta, \mathsf{Set}]^{[1]} \times \mathfrak{sE}^{[1]} \rightarrow [\mathcal{E}, \mathsf{Set}]^{[1]}.$$

Note that this is more general than a partially defined pushout construction of the two-variable weighted colimit functor because we do not require the individual colimits of $A$ with weight $V$ and $B$ with weights $U$ and $V$ to exist.

Unfolding the codomain of (4.2), we see that the relative latching map of $i: A \rightarrow B$ at level $m$ is precisely the pushout weighted colimit of $i$ with the coboundary inclusion $\partial \Delta^{\mathrm{op}}[m] \rightarrow \Delta^{\mathrm{op}}[m]$. Each side exist when the other does. This point of view is useful because it enables us to obtain pushout weighted colimits of $i$ with certain inclusions as cell complexes of relative latching maps.

We call a map $i$ a *Reedy complemented inclusion* if, for all $m$, the relative latching map of $i$ at level $m$ exists and is a complemented inclusion. This condition for $m < k$ suffices to guarantee the existence of the relative latching map at level $m = k$. Thus, in the inductive verification that a map is a Reedy complemented inclusion, the relevant latching maps always exist. Given a map $X \rightarrow Y$ in $\mathfrak{sE}$, the *relative matching map* at level $m$ is its weighted limit, i.e., pullback evaluation, at $\partial \Delta[m] \rightarrow \Delta[m]$, i.e., the map $X_m \rightarrow Y_m \times_{\operatorname{ev}_{\partial \Delta[m]} Y} \operatorname{ev}_{\partial \Delta[m]} X$. We call $X \rightarrow Y$ a *Reedy split epimorphism* if all its relative matching maps are split epimorphisms.

Following standard Reedy theory, Reedy complemented inclusions and Reedy split epimorphisms form a weak factorisation system. For this, we observe that instantiating the treatment of [RV14] and making use of Lemma 3.19, the use of (co)limits in $\mathfrak{sE}$ may be reduced to pushouts along complemented inclusions and pullbacks along split epimorphisms. We now relate this weak factorisation system to that of cofibrations and trivial fibrations, given in Theorem 4.2 (cf. also Proposition 4.1).

**Proposition 4.3.** *The weak factorisation system of cofibrations and trivial fibrations of Theorem 4.2 and Proposition 4.1 coincides with the weak factorisation system of Reedy complemented inclusions and Reedy split epimorphisms.*

*Proof.* Two weak factorisation systems coincide as soon as their right classes do. But, by inspecting the definition of a trivial fibration in Definition 1.3, a map in $\mathfrak{sE}$ is a Reedy split epimorphism if and only if it is a trivial Kan fibration. $\square$

The next lemma will be useful to simplify some saturation arguments in Section 6, as it allows us to avoid considering retracts, cf. the notion of a cell complex in Definition 3.16.

**Lemma 4.4.** *Every cofibration in $\mathfrak{sE}$ is an $I_{\mathfrak{sE}}$-cell complex.*

*Proof.* If $A \rightarrow B$ is a cofibration, then $B$ can be written as the colimit of its skeleta relative to $A$:

$$\operatorname{Sk}_A^{-1} B \longrightarrow \operatorname{Sk}_A^0 B \longrightarrow \operatorname{Sk}_A^1 B \longrightarrow \dots$$

26

where $\mathrm{Sk}_A^{-1}B = A$ and for $k \geq 0$ the square

$$\begin{array}{ccc} B_k \times \partial \Delta[k] \cup (A_m \sqcup_{L_m A} L_m B) \times \Delta[k] & \longrightarrow & \mathrm{Sk}_A^{k-1}B \\ \downarrow & & \downarrow \\ B_k \times \Delta[k] & \longrightarrow & \mathrm{Sk}_A^k B \end{array}$$

is a pushout. These statements are justified analogously to the proofs of [GSS19, Lemma 2.3.1, Corollary 2.3.3]. The colimits used in the construction exist by Corollary 2.12 since they are colimits of sequences of levelwise complemented inclusions and pushouts along levelwise complemented inclusions which is ensured by the assumption that $A \rightarrow B$ is a cofibration. $\square$

Our next goal is to provide a characterisation of cofibrations in terms of actions of degeneracy operators, stated in Theorem 4.6 below. This is a generalisation of [Hen18, Proposition 5.1.4] or [GSS19, Proposition 1.4.4] to a setting without arbitrary colimits. The proof is made significantly more complex by the fact that $\mathcal{E}$ is not assumed to be a Grothendieck topos. Instead, the required exactness properties are substituted by Lemma 2.14. We also need the following statement. For this, we observe that our discussion of Reedy theory and latching objects for the case of $\Delta$ applies just as well to arbitrary countable Reedy categories of countable height. Note that the assumption of a Reedy cofibrant diagram includes the hypothesis that all latching objects exist.

**Lemma 4.5.** *Let $D$ be a finite direct category. Let $F: D \rightarrow \mathfrak{s}\mathcal{E}$ be a Reedy cofibrant diagram. Then the colimit of $F$ exists and is van Kampen.*

*Proof.* We proceed by induction on the height of $D$. For height 0, note that $D$ is the empty and the claim holds because initial objects are van Kampen since $\mathfrak{s}\mathcal{E}$ is lextensive.

Now assume the claim for height $n$ and let $D$ have height $n+1$. Let $D'$ of height $n$ denote the restriction of $D$ to objects of degree below $n$. Let $I$ be the collection of objects of $D$ of degree $n$. As per usual Reedy theory, we may compute the colimit of $F$ as the following pushout:

$$\begin{array}{ccc} \coprod_{i \in I} L_i F & \longrightarrow & \operatorname{colim}_{D'} F|_{D'} \\ \downarrow & & \downarrow \\ \coprod_{i \in I} F(i) & \longrightarrow & \operatorname{colim}_D F. \end{array}$$

Here, the left map is a cofibration because it is a finite coproduct of cofibrations, and hence the pushout exists and is van Kampen by Lemma 2.9. By the inductive hypothesis, the colimit computing the latching object $L_i F$ for $i \in I$ is van Kampen, and so is the colimit of $F|_{D'}$. The finite coproducts are van Kampen since $\mathfrak{s}\mathcal{E}$ is lextensive. Using the characterisation of van Kampen colimits given by Lemma 2.2, one sees that $\operatorname{colim}_D F$ is van Kampen. $\square$

**Theorem 4.6** (Characterisation of cofibrations). *Let $i: A \rightarrow B$ be a map in $\mathfrak{s}\mathcal{E}$. Then the following are equivalent:*

- (i) *the map $i$ is a cofibration;*
- (ii) *the map $i$ is a levelwise complemented inclusion and the map $A_m \sqcup_{A_n} B_n \rightarrow B_m$ is a complemented inclusion for every degeneracy operator $[m] \rightarrow [n]$.*

27

*Proof.* We use from Proposition 4.3 that cofibrations are the same as Reedy complemented inclusions. As in [RV14], we work freely with pushout weighted colimits in $\mathcal{E}$, with index category both $\Delta$ and its wide subcategory $\Delta_-$ of degeneracy operators. As explained above (in the case of $\Delta$), these are partial two-variable functors in our situation. Mirroring our notation for $\Delta$, we write $\partial \Delta_\perp^{\mathrm{op}}[m]$ for the subobject of $\Delta_\perp^{\mathrm{op}}[m] = \Delta([m], -)$ in $[\Delta_-, \mathsf{Set}]$ consisting of the non-identity maps. Recall that the coboundary inclusion $\partial \Delta_\perp^{\mathrm{op}}[m] \rightarrow \Delta_\perp^{\mathrm{op}}[m]$ arises as left Kan extension along $\Delta_- \rightarrow \Delta$ of the coboundary inclusion $\partial \Delta_\perp^{\mathrm{op}}[m] \rightarrow \Delta_\perp^{\mathrm{op}}[m]$. For working with weighted colimits, we recall that left Kan extension on the side of the weight corresponds to restriction on the side of the diagram.

We start with the direction from (i) to (ii). Let $i$ be a Reedy complemented inclusion. Then the pushout weighted colimit of $i$ with any finite cell complex (finite composite of pushouts) of coboundary inclusions is a complemented inclusion. In particular, the pushout weighted colimit of the restriction $i|_{\Delta_-}$ of $i$ to $\Delta_-$ with any finite cell complex of coboundary inclusions $\partial \Delta_\perp^{\mathrm{op}}[k] \rightarrow \Delta_\perp^{\mathrm{op}}[k]$ of $\Delta_-$ is a complemented inclusion. For $m \geq 0$, the map $A_m \rightarrow B_m$ is the pushout weighted colimit of $i|_{\Delta_-}$ with such a finite cell complex $\varnothing \rightarrow \Delta_\perp^{\mathrm{op}}[m]$, hence a complemented inclusion. Every degeneracy operator $[m] \rightarrow [n]$ is a split epimorphism. It follows that $\Delta_\perp^{\mathrm{op}}[n] \rightarrow \Delta_\perp^{\mathrm{op}}[m]$ is an inclusion with levelwise finite complement, thus we can write it as a finite cell complex of coboundary inclusions of $\Delta_-$. Therefore, the pushout weighted colimit of $i$ with $\Delta_\perp^{\mathrm{op}}[n] \rightarrow \Delta_\perp^{\mathrm{op}}[m]$ is a complemented inclusion. But this is the map $A_m \sqcup_{A_n} B_n \rightarrow B_m$.

We finish with the direction from (ii) to (i). We show that the relative latching map $A_m \sqcup_{L_m A} L_m B \rightarrow B_m$ of $i$ is a complemented inclusion by induction on $m$. Recall that this is the pushout weighted limit of $i|_{\Delta_-}$ with $\partial \Delta_\perp^{\mathrm{op}}[m] \rightarrow \Delta_\perp^{\mathrm{op}}[m]$. Let $\partial(\Delta_\perp^{\mathrm{op}} \downarrow [m])$ denote the opposite of the poset of non-identity degeneracy operators with source $[m]$. Consider the diagram $F: \partial(\Delta_\perp^{\mathrm{op}} \downarrow [m]) \rightarrow \mathcal{E} \downarrow B_m$ sending a degeneracy operator $[m] \rightarrow [n]$ to the object $A_m \sqcup_{A_n} B_n$. It lives canonically under the object $A_m$ over $B_m$. By switching from the weighted colimit to the conical colimit point of view, the object $A_m \sqcup_{L_m A} L_m B$ is the colimit of $F$ in the category of factorisations of $A_m \rightarrow B_m$. Equivalently, in the slice over $B_m$, the object $A_m \sqcup_{L_m A} L_m B$ is the colimit of the diagram $F_*$ that is $F$ with shape adjoined with an initial object sent to $A_m$.

Note that, using our assumptions, we can regard $F$ as a diagram of complemented subobjects of $B_m$ that are bounded from below by the complemented subobject $A_m$. It remains to show that the colimit of $F_*$ in the slice over $B_m$ has a complemented inclusion as underlying map. It will suffice to show that this colimit is subterminal. For then, it is given by the non-empty finite union of the subobjects that constitute the values of $F_*$, and complemented subobjects are closed under finite unions by part (i) of Lemma 2.10.

The indexing category of $F_*$ is a finite direct category. The latching map of $F_*$ at the initial object is $0 \rightarrow A_m$, a complemented inclusion. The latching map of $F_*$ at an object $[m] \rightarrow [n]$ is a pushout of the relative latching map of $A \rightarrow B$ at $[m]$, a complemented inclusion by induction hypothesis. Thus, the diagram $F_*$ is Reedy cofibrant. By Lemma 4.5, the colimit of $F_*$ is van Kampen. All of this holds both in $\mathcal{E}$ as well as its slice over $B_m$.

Given a complemented subobject $U \rightarrow B_m$ and an arbitrary subobject $V \rightarrow B_m$, the pushout corner map in the pullback of $U \rightarrow B_m$ and $V \rightarrow B_m$ exists. If it is a monomorphism, it computes the union $U \cup V \rightarrow B_m$ of the given subobjects. Since degeneracy operators are split epimorphisms, the natural transformation $i|_{\Delta_-}$ is Cartesian. This makes the value of $F$ at an object $[m] \rightarrow [n]$ the union of the subobjects $A_m \rightarrow B_m$ and $B_n \rightarrow B_m$.

Since $\Delta$ is elegant [BR13], given non-identity degeneracy operators $[m] \rightarrow [n_i]$ for $i = 1, 2$, we

28

have an absolute pushout

![img-12.jpeg](img-12.jpeg)

in $\Delta$ with $[n_1] \to [k]$ and $[n_2] \to [k]$ degeneracy operators. Note that $[m] \to [k]$ is distinct from the identity. By absoluteness, we obtain a pullback

![img-13.jpeg](img-13.jpeg)

We now work in subobjects of $B_m$. From the above pullback, we have $B_k = B_{n_1} \cap B_{n_2}$. Using from Lemma 2.9 twice that pushouts along complemented inclusions are stable under pullback, we compute

$$
\begin{array}{l}
(A_m \cup B_{n_1}) \cap (A_m \cup B_{n_2}) = ((A_m \cup B_{n_1}) \cap A_m) \cup ((A_m \cup B_{n_1}) \cap B_{n_2}) \\
\quad = A_m \cup ((A_m \cup B_{n_1}) \cap B_{n_2}) \\
\quad = A_m \cup (B_{n_1} \cap B_{n_2}) \\
\quad = A_m \cup B_k.
\end{array}
$$

We obtain, in subobjects of $B_m$, that $F$ at $[m] \to [n]$ is the intersection (computed as pullback) of $F$ at $[m] \to [n_1]$ and $[m] \to [n_2]$. Thus, in subobjects of $B_m$, the diagram $F$ (and then also $F_\star$) preserves binary meets. Recollecting from above that the colimit of $F_\star$ in the slice over $B_m$ is van Kampen, Lemma 2.14 shows that it is subterminal.

## 5 Closure properties of cofibrations

This section is devoted to further study of weak factorisation systems constructed in Section 4, in preparation for the proof of the existence of the effective model structure. We begin with a simple verification.

**Lemma 5.1.** *If $A \to B$ is a (trivial) cofibration between levelwise countable simplicial sets, then $\underline{A} \to \underline{B}$ is a (trivial) cofibration in $\mathfrak{sE}$.*

*Proof.* Recall that the partial functor $X \mapsto \underline{X}$ is a partial left adjoint to the levelwise global sections functor. This is equivalently the functor $\operatorname{Hom}_{\mathfrak{sSet}}(1, -)$ with $1 \in \mathfrak{sE}$ from Section 1. By adjointness using the weak factorisation systems of Theorem 4.2 and Proposition 4.1, it suffices to show that $\operatorname{Hom}_{\mathfrak{sSet}}(1, -)$ preserves (trivial) fibrations. This holds by Proposition 1.4.

# Proposition 5.2.

(i) Trivial fibrations are fibrations.
(ii) Trivial cofibrations are cofibrations.

29

*Proof.* The first part is immediate since trivial Kan fibrations are Kan fibrations in simplicial sets. The second parts follows by adjointness using the weak factorisation systems of Theorem 4.2. $\square$

We now establish some formal properties of the two enriched weak factorisation systems, regarding the pushout-product, pushout-tensor and pullback-cotensor functors (cf. Remark 1.2).

# **Proposition 5.3** (Pushout-product properties).

(i) *In $\mathfrak{sE}$, cofibrations are closed under pushout product.*

(ii) *In $\mathfrak{sE}$, the pushout product of a cofibration and a trivial cofibration is a trivial cofibration.*

*Proof.* For part (i), recall that cofibrations in $\mathfrak{sSet}$ are closed under pushout product.$^{3}$ Since $S \mapsto \underline{S}$ preserves pushouts and products, it follows that the pushout product of generating cofibrations in $\mathfrak{sE}$ is a cofibration. The same follows for general cofibrations in $\mathfrak{sE}$ by Proposition 3.21. These pushout products exist by Lemma 2.13.

For part (ii), The result holds in $\mathfrak{sSet}$ by$^{4}$ [GZ67, Proposition IV.2.2] and thus it carries over to $\mathfrak{sE}$ by the argument of part (i). $\square$

**Lemma 5.4.** *Let $X \in \mathfrak{sE}$. For every finite simplicial set $K$, the tensor $K \cdot X$ exists and is given by $\underline{K} \times X$.*

*Proof.* Given $Y \in \mathfrak{sE}$, a morphism $X \rightarrow K \pitchfork Y$ consists of a family of morphisms $X_m \rightarrow Y_n^{(K \times \Delta[m])_n}$, natural in $m$ and dinatural in $n$. This corresponds to a family of morphisms $\underline{K \times \Delta[m]}_n \times X_m \rightarrow Y_n$, dinatural in $m$ and natural in $n$. Moreover:

$$\underline{K \times \Delta[m]}_n \times X_m = \underline{K}_n \times \underline{\text{Hom}([m], [n])} \times X_m.$$

Since $\int^{[m]} \underline{\text{Hom}([m], [n])} \times X_m = X_n$, such family of maps corresponds to a morphism $\underline{K}_n \times X_n \rightarrow Y_n$ natural in $n$, i.e., a morphism $\underline{K} \times X \rightarrow Y$ in $\mathfrak{sE}$. $\square$

**Proposition 5.5** (Pushout tensor properties). *Let $A \rightarrow B$ be a cofibration between finite simplicial sets. Then, the pushout tensor with $A \rightarrow B$ exists. Furthermore,*

(i) *it preserves trivial cofibrations,*

(ii) *it preserves cofibrations,*

(iii) *if $A \rightarrow B$ is a trivial cofibration, then it sends cofibrations to trivial cofibrations.*

*Proof.* The existence follows from Corollary 2.12 and Lemma 5.4. These other statements are dual to the ones of part (i) of Lemma 1.5 under the tensor-cotensor adjunction of Lemma 5.4. Note that for this conclusion it suffices to consider the underlying ordinary weak factorisation system of Lemma 3.6 so that we do not need to verify that the adjunction is enriched over $\text{Psh}\mathcal{E}$. $\square$

We now turn our attention to the cofibrations and the cofibrant objects in $\mathfrak{sE}$. From Section 3 and Proposition 4.1 these are exactly the maps with the left lifting property with respect to Kan fibrations. The next lemma provides us with a stock of cofibrant objects.

$^{3}$See [Hen18, Proposition 5.1.5] or [GSS19, Proposition 1.3.1] for the constructive version of this fact.

$^{4}$See [Hen18, Corollary 5.2.3] or [GSS19, Proposition 1.3.1] for the constructive version of this fact.

30

## Lemma 5.6.

- (i) *Let $E \in \mathcal{E}$. The constant simplicial object $E \in \mathfrak{s}\mathcal{E}$ is cofibrant.*
- (ii) *The domains and codomains of all morphisms of $I_{\mathfrak{s}\mathcal{E}}$ and $J_{\mathfrak{s}\mathcal{E}}$ are cofibrant.*
- (iii) *Let $X \in \mathfrak{s}\mathcal{E}$ and $K$ be a finite simplicial set. If $X$ is cofibrant, then so is $K \pitchfork X$.*

*Proof.* For part (i), by Lemma 3.9, the tensor of $\partial\Delta[0] \rightarrow \Delta[0]$ with $E$ is a cofibration. By Lemma 5.4, this map is the tensor of $E \in \mathfrak{s}\mathcal{E}$ with $\partial\Delta[0] \rightarrow \Delta[0]$, i.e., the map $\varnothing \rightarrow E$ in $\mathfrak{s}\mathcal{E}$. Part (ii) holds since $S \mapsto S$ preserves cofibrations by Lemma 5.1.$^{5}$ Finally, for part (iii), if $[m] \rightarrow [n]$ is a degeneracy operator, then the map $(K \pitchfork X)_n \rightarrow (K \pitchfork X)_m$ can be identified with the map $X(K \times \Delta[n]) \rightarrow X(K \times \Delta[m])$. It follows from [Hen19, Proposition 3.1.11] that when $K$ is a finite simplicial set, the map $K \times \Delta[n] \rightarrow K \times \Delta[m]$ is a finite composite of pushouts of degeneracy operators. This implies that the map $(K \pitchfork X)_n \rightarrow (K \pitchfork X)_m$ is a finite composite of pullbacks of degeneracy operator $X_a \rightarrow X_b$. As $X$ is cofibrant these maps are all complemented inclusions, hence as complemented inclusions are closed under pullback and composition, this implies that $(K \pitchfork X)_n \rightarrow (K \pitchfork X)_m$ is a complemented inclusion as well. $\square$

## Lemma 5.7. *Cofibrations are closed under pullback along a monomorphism.*

*Proof.* Consider a pullback square of simplicial objects:

![img-14.jpeg](img-14.jpeg)

We check that $S' \rightarrow S$ is a cofibration using characterisation (ii) of Theorem 4.6. In an lextensive category, a pullback of a complemented inclusion is a complemented inclusion, hence the map $S' \rightarrow S'$ is a levelwise complemented inclusion. Given any degeneracy operator $[m] \rightarrow [n]$, as it is a split epimorphism and $S \rightarrow B$ is a monomorphism, the naturality square:

![img-15.jpeg](img-15.jpeg)

is a pullback. The pushout $B_m \sqcup_{A_m} A_n$ is a van Kampen colimit because the map $A_m \rightarrow B_m$ is a complemented inclusion, it hence follows that we have a pullback square:

![img-16.jpeg](img-16.jpeg)

$^{5}$Constructively, for part (ii) one needs to check also that the relevant objects are cofibrant in $\mathfrak{s}\mathfrak{S}\mathfrak{e}$. The simplices and their boundaries are cofibrant in $\mathfrak{s}\mathfrak{S}\mathfrak{e}$ by [GSS19, Lemma 1.3.5] and the horns by [GSS19, Lemma 1.4.9].

31

and hence as the bottom map is a complemented inclusion by assumption, the top map is also a complemented inclusion. This shows that $S' \rightarrow S$ is a cofibration. $\square$

As discussed just before Lemma 1.8, the slice $\mathfrak{s}\mathcal{E} \downarrow X$ is enriched over simplicial sets and has cotensors by finite simplicial sets. Under the present hypotheses, it also has tensors by finite (and even countable) simplicial sets, which are simply tensors in the underlying category $\mathfrak{s}\mathcal{E}$.

Part (iii) of the next Proposition extends the pullback cotensor properties of part (i) of Lemma 1.5 to slice categories.

#### Proposition 5.8. Let $X \in \mathfrak{s}\mathcal{E}$.

- (i) *Pushout products of cofibrations in $\mathfrak{s}\mathcal{E} \downarrow X$ exist. Moreover, cofibrations in $\mathfrak{s}\mathcal{E} \downarrow X$ are closed under pushout product.*
- (ii) *The pushout tensor properties of Proposition 5.5 hold also in $\mathfrak{s}\mathcal{E} \downarrow X$.*
- (iii) *The pullback cotensor in $\mathfrak{s}\mathcal{E} \downarrow X$ of a cofibration between finite simplicial sets and a fibration is a fibration. If the given cofibration or fibration is trivial, then the result is a trivial fibration.*

*Proof.* For part (i), recall that pushout products in $\mathfrak{s}\mathcal{E} \downarrow X$ are computed from pushout products in $\mathfrak{s}\mathcal{E}$ by pulling back along the diagonal $X \rightarrow X \times X$. Since the latter is a monomorphism, the conclusion follows from Proposition 5.3 and Lemma 5.7. For part (ii), note that the forgetful functor $\mathfrak{s}\mathcal{E} \downarrow X \rightarrow \mathfrak{s}\mathcal{E}$ preserves tensors and pushouts and thus the pushout tensor properties follow directly from Proposition 5.5. Part (iii) was already established as Lemma 1.8, but now it also follows by the tensor-cotensor adjunction. $\square$

#### Proposition 5.9.

- (i) *Let $f: X \rightarrow Y$ be a morphism in $\mathfrak{s}\mathcal{E}$. If $X$ is cofibrant, then the pullback functor $f^*: \mathfrak{s}\mathcal{E} \downarrow Y \rightarrow \mathfrak{s}\mathcal{E} \downarrow X$ preserves cofibrations.*
- (ii) *Let $A \rightarrow X$ and $B \rightarrow X$ be morphisms in $\mathfrak{s}\mathcal{E}$. If $A$ and $B$ are cofibrant, then so is $A \times_X B$.*
- (iii) *Cofibrant objects in $\mathfrak{s}\mathcal{E}$ are closed under finite limits.*

*Proof.* For (i), if $A \rightarrow B$ is a cofibration over $Y$, then its pullback along $f: X \rightarrow Y$ coincides with the pushout product of $A \rightarrow B$ and $\varnothing \rightarrow X$ in $\mathfrak{s}\mathcal{E} \downarrow Y$, which is a cofibration by part (i) of Proposition 5.3. Part (ii) is a special case of part (i). Finally, for part (iii), it suffices to check that cofibrant objects are closed under pullback and that the terminal object is cofibrant. The former follows from part (ii). The latter follows by definition since $0 \rightarrow 1$ is a generating cofibration. $\square$

## 6 Pushforward along cofibrations

This section and Sections 7, 8 and 9 constitute the third part of the paper, in which we show how the two weak factorisation systems of Section 4 give rise to the effective model structure (Theorem 9.9). For this, we shall work with a fixed countably lextensive category $\mathcal{E}$. We do not assume that the category $\mathcal{E}$ is (locally) Cartesian closed, but we establish the existence of certain exponentials and pushforwards required by our argument. We also provide a criterion for the cofibrancy of some of these constructions. We begin with a few remarks on exponentiable maps.

#### Proposition 6.1. Let $f: X \rightarrow Y$ in $\mathcal{E}$. Then, the following are equivalent:

32

(i) the pullback functor $f^* : \mathcal{E} \downarrow Y \rightarrow \mathcal{E} \downarrow X$ has a right adjoint $f_* : \mathcal{E} \downarrow X \rightarrow \mathcal{E} \downarrow Y$,

(ii) $X$ is exponentiable as an object of $\mathcal{E} \downarrow Y$.

*Proof.* This follows from [Joh02, Lemma A1.5.2 (i)] and (the proof of) [Joh02, Corollary A1.5.3]. $\square$

When the equivalent conditions of Proposition 6.1 hold, we say that $f$ is *exponentiable* and refer to the right adjoint $f_*$ as the *pushforward along $f$*. (It is also known as the *dependent product along $f$*.)

**Example 6.2.** Let $S$ be a finite set. Then, $\underline{S} \in \mathcal{E}$ defined in (2.2) is exponentiable in $\mathcal{E}$ and the exponential of $X$ by $\underline{S}$ is the product $X^S$. Indeed, as finite coproducts in $\mathcal{E}$ are universal, $\underline{S} \times X \cong \prod_{s \in S} X$. Hence, a map $\underline{S} \times A \rightarrow X$ is the same as an $S$-indexed collection of maps $A \rightarrow X$, that is the same as a map $A \rightarrow X^S$.

**Proposition 6.3.** *Let*

![img-17.jpeg](img-17.jpeg)

be a pullback square in $\mathcal{E}$. If $f$ is exponentiable, then so is $g$ and the canonical natural transformation $u^* f_* \rightarrow g_* v^*$ is an isomorphism.

*Proof.* This follows from [Joh02, Lemma A1.5.2 (ii)] applied in the slice category over $Z$. If $K$ is an object over $W$, the pushforward $g_* K$ is constructed explicitly as the pullback:

![img-18.jpeg](img-18.jpeg)

where the bottom arrow is the unit of adjunction $Y \rightarrow f_* f^* Y = f_* W$. $\square$

**Proposition 6.4.** *Let $D$ be a small category and $f_*: X_* \rightarrow Y_*$ a natural transformation between two $D$-diagrams in $\mathcal{E}$ such that $f_*$ is Cartesian, $f_d$ is exponentiable for every $d \in D$, and $Y_*$ has a van Kampen colimit in $\mathcal{E}$. Then the colimit map*

$$f : \begin{array}{c} \operatorname{colim} \atop d \in D \end{array} X_d \rightarrow \begin{array}{c} \operatorname{colim} \atop d \in D \end{array} Y_d$$

*is exponentiable, and up to the equivalences*

$$\mathcal{E} \downarrow \operatorname{colim} \atop D X_d \simeq \lim \atop D (\mathcal{E} \downarrow X_d), \qquad \mathcal{E} \downarrow \operatorname{colim} \atop D Y_d \simeq \lim \atop D (\mathcal{E} \downarrow Y_d),$$

*the functor $f_*$ coincides with the collection of functors $(f_d)_*$.*

33

Proof. The claim follows from a general fact. If $F: \mathcal{A} \to \mathcal{B}$ is a pseudo-natural transformation between two diagrams $\mathcal{A}, \mathcal{B}: D \to \mathsf{Cat}$ of categories such that each $F_d$ has a right adjoint $R_d$ and for each naturality square of $F_d$ the Beck–Chevalley conditions are satisfied, then the isomorphisms given by the Beck–Chevalley condition exhibit $R_d: \mathcal{B}_d \to \mathcal{A}_d$ as a pseudo-natural transformation, and $\lim R_d$ is a right adjoint to $\lim F_d$, with the unit and counit of this adjunction being levelwise the unit and counit of the adjunction $F_d \dashv R_d$.

We now move on to discuss how exponentiability interacts with cofibrancy. In particular, the aim of the rest of the section is to prove the following result.

**Theorem 6.5.** Let $i: A \to B$ be a cofibration between cofibrant object in $\mathfrak{sE}$. Then:

(i) $i$ is exponentiable,
(ii) $i_*$ sends cofibrant objects to cofibrant objects.

We will prove this theorem by a saturation argument. For this purpose, we introduce now the class $\mathcal{G}$ of cofibrations between cofibrant objects that satisfy properties (i) and (ii) of the theorem.

Assume $i: A \to B$ an exponentiable monomorphism in $\mathcal{E}$. Then, for any $X \in \mathcal{E} \downarrow A$, the unit of the adjunction $i^* \dashv i_*$ induces a pullback square

$$\begin{array}{c} X \longrightarrow i_* X \\ \downarrow \quad \downarrow \\ A \xrightarrow[i]{} B. \end{array} \tag{6.1}$$

Indeed, since $i$ is a monomorphism, the counit $i^* i_! \to \mathrm{id}$ of the adjunction $i_! \dashv i^*$ is invertible, and therefore so is the unit $\mathrm{id} \to i^* i_*$.

**Lemma 6.6.** Let $i: A \to B$ be a map in $\mathcal{G}$. For cofibrant $X \in \mathcal{E} \downarrow A$, the map $X \to i_* X$ is a cofibration.

Proof. The claim follows from part (i) of Proposition 5.9, since the map $X \to i_* X$ is a pullback of a cofibration between cofibrant objects by (6.1) above.

**Proposition 6.7.** The class $\mathcal{G}$ is closed under pushouts along maps with cofibrant target.

Proof. If $i: A \to B$ is in $\mathcal{G}$ and $f: A \to X$ is an arbitrary arrow in $\mathfrak{sE}$ with $X$ cofibrant, we consider the diagram

![img-19.jpeg](img-19.jpeg)

Then the two squares are pullbacks (because $i$ is a monomorphism for the one on the right) the vertical maps are all exponentiable by assumption, so by Proposition 6.4, the map between the colimit of the first row to the colimit of the second row, that is the map

$$j: X \to X \sqcup_A B,$$

34

is indeed exponentiable. Moreover, still by Proposition 6.4, if $K$ is a cofibrant object over $X$, it corresponds with respect to the van Kampen pushout of the first row to the Cartesian natural transformation

![img-20.jpeg](img-20.jpeg)

Hence its image by $j_*$ corresponds to the Cartesian natural transformation

![img-21.jpeg](img-21.jpeg)

So, by gluing along the bottom van Kampen colimit, we have a pushout square

![img-22.jpeg](img-22.jpeg)

where the top arrow is a cofibration by Lemma 6.6 and the assumption that $i \in \mathcal{G}$ applied to the cofibrant object $f^*K$. It follows that $j_*K$ is cofibrant. $\square$

**Proposition 6.8.** *The class $\mathcal{G}$ is closed under sequential composition.*

*Proof.* The class $\mathcal{G}$ is clearly closed under finite composition. Given an $\omega$-chain $A_0 \xrightarrow{i_0} A_1 \xrightarrow{i_1} A_2 \xrightarrow{i_2} \dots$ of arrows in $\mathcal{G}$, we consider the diagram:

![img-23.jpeg](img-23.jpeg)

Each vertical map is in $\mathcal{G}$ as a composite of maps in $\mathcal{G}$; each square is a pullback as all these maps are monomorphisms, so by Proposition 6.4, the comparison map $j: A_0 \to \operatorname{colim} A_i$ between the two colimit is exponentiable. If $K$ is a cofibrant object over $A_0$, then again by Proposition 6.4 its image by $j_*$ corresponds to the Cartesian natural transformation:

![img-24.jpeg](img-24.jpeg)

35

where $K_0 = K$ and $K_{n+1} = (i_n)_*K_n$, hence all the maps in the top row are cofibrations, and so $j_*K = \text{colim } K_i$ is cofibrant. $\square$

**Proposition 6.9.** *The class $\mathcal{G}$ is closed under tensors by objects of $\mathcal{E}$.*

*Proof.* Let $i: A \mapsto B$ an arrow in $\mathcal{G}$, and let $X$ an object of $\mathcal{E}$. The square

![img-25.jpeg](img-25.jpeg)

is a pullback, so $j$ is exponentiable by Proposition 6.3. Moreover, the formula for $j_*$ given in the proof of Proposition 6.3 gives that $K$ over $A \times X$ we have a pullback square

![img-26.jpeg](img-26.jpeg)

Since $i \in \mathcal{G}$ and $B \times X$ is cofibrant, $i_*K$ is cofibrant, and so $j_*K$ is cofibrant, as required. $\square$

In order to conclude the proof of Theorem 6.5, it remains to show that the generating cofibrations $i: \partial\Delta[n] \mapsto \Delta[n]$ are in $\mathcal{G}$. This is based on an explicit description of $i_*$ using the characterisation of $\mathfrak{s}\mathcal{E} \downarrow \partial\Delta[n]$ and $\mathfrak{s}\mathcal{E} \downarrow \Delta[n]$ of Lemma 2.8.

**Proposition 6.10.** *The generating cofibrations $i: \partial\Delta[n] \mapsto \Delta[n]$ are in $\mathcal{G}$.*

*Proof.* Under the equivalence of Lemma 2.8, the pullback functor $i^*: \mathfrak{s}\mathcal{E} \downarrow \Delta[n] \to \mathfrak{s}\mathcal{E} \downarrow \partial\Delta[n]$ coincides with the functor

$$\mathfrak{s}\mathcal{E}^{\Delta^{\text{op}} \downarrow \Delta[n]} \to \mathfrak{s}\mathcal{E}^{\Delta^{\text{op}} \downarrow \partial\Delta[n]}$$

obtained by reindexing along the sieve inclusion: $\Delta^{\text{op}} \downarrow \partial\Delta[n] \to \Delta^{\text{op}} \downarrow \Delta[n]$, hence its right adjoint, if it exists, is the right Kan extension along this sieve inclusion. So if we prove that the pointwise right Kan extension along this sieve inclusion exists, it will coincide with $i_*$. If $\mathcal{F} \in \mathfrak{s}\mathcal{E} \downarrow \partial\Delta[n]$, then this pointwise right Kan extension evaluated at $\Delta[k] \to \Delta[n] \in \Delta \downarrow \Delta[n]$ is given by the limit

$$(i_*\mathcal{F})([k]) = \lim_{p \in P} \mathcal{F}(p), \quad \text{where } P = \left\{ \begin{array}{c} \Delta[a] \longrightarrow \Delta[k] \\ \searrow_p \searrow \downarrow \\ \Delta[n], \end{array} \right. \quad p \text{ not surjective} \right\}.$$

This is a limit over an infinite category so it is not guaranteed to exists, but the category $P$ has a finite reflective category given by the objects such that the map $\Delta[a] \to \Delta[k]$ is injective, with the reflection given by the image factorisation of this map, and hence this limit coincides with

$$(i_*\mathcal{F})([k]) = \lim_{p \in P^+} \mathcal{F}(p), \quad \text{where } P^+ = \left\{ \begin{array}{c} \Delta[a] \longmapsto \Delta[k] \\ \searrow_p \searrow \downarrow \\ \Delta[n], \end{array} \right. \quad p \text{ not surjective} \right\},$$

36

which is a finite limit, hence exists, which proves the existence of $i_*$.

Next, we assume that $\mathcal{F}$ is cofibrant, and we will show that $i_*\mathcal{F}$ is cofibrant. That is, given a degeneracy $[k] \rightarrow [k']$ the action $i_*\mathcal{F}([k']) \rightarrow i_*\mathcal{F}([k])$ is a complemented inclusion (by Theorem 4.6). The map $i_*\mathcal{F}([k]) \rightarrow \Delta[n] ([k])$ gives a decomposition of the map above into a coproduct indexed by all the map $\alpha: [k] \rightarrow [n]$, so it is enough to show that the fiber above each such map is a complemented inclusion. The fiber over such a map $\alpha$ of $i_*\mathcal{F}([k])$, is by definition of $i_*$ the object classifying maps $P \rightarrow \mathcal{F}$ over $\partial\Delta[n]$ where $P$ is the pullback square

![img-27.jpeg](img-27.jpeg)

The fiber of $i_*\mathcal{F}([k'])$ over $\alpha$ is described similarly with $P'$ the pullback of $\Delta[k'] \rightarrow \Delta[n]$, and the map we are interested in is induced by the map $P' \rightarrow P$ obtained as the pullback of $\Delta[k'] \rightarrow \Delta[k]$. But it follows from [Hen19, Proposition 3.1.11] that a pullback of a degeneracy operator is an iterated pushout of degeneracy operators, in this case a finite such iterated pushout as $P'$ is finite. As $\mathcal{F}$ is cofibrant, this decomposes $\mathcal{F}(P) \rightarrow \mathcal{F}(P')$ as a composite of complemented inclusions, and hence concludes the proof. $\square$

*Proof of Theorem 6.5.* We show that all cofibrations with cofibrant domain are in $\mathcal{G}$. By Lemma 4.4, it suffices to show that the generating cofibrations are in $\mathcal{G}$ and that $\mathcal{G}$ is closed under operations appearing in a cell complex. The case of generators is Proposition 6.10. Closure under tensoring by objects of $\mathcal{E}$ is Proposition 6.9, closure under pushout (along maps with cofibrant target) is Proposition 6.7, and closure under sequential composition is Proposition 6.8. $\square$

An analysis of the proof of Theorem 6.5 shows that the assumption that $A$ is cofibrant is not needed for the exponentiability of $i$, as it is only used for the part of the argument regarding preservation of cofibrant objects by $i_*$.

## 7 The Frobenius property

We adapt the notion of a strong homotopy equivalence and the associated concepts from [GS17, Section 3] to our setting. Recall that a map $f: A \rightarrow B$ is a 0-oriented (respectively, *1-oriented*) homotopy equivalence if there is a map $g: B \rightarrow A$ with homotopies $u: gf \sim \text{id}_A$ and $v: fg \sim \text{id}_B$ (respectively, $u: \text{id}_A \sim gf$ and $v: \text{id}_B \sim fg$). Such a homotopy equivalence is called *strong* if the homotopies satisfy the coherence condition $fu = vf$.

We recall the abstract characterisation of strong homotopy equivalences. The commuting square

![img-28.jpeg](img-28.jpeg)

induces maps $\theta_0: ! \rightarrow \lambda_1^0$ and $\theta_1: ! \rightarrow \lambda_1^1$ in the arrow category of sSet. (We will use $\lambda_k^i$ to denote the horn inclusion $\Lambda^i[k] \rightarrow \Delta[k]$.) Note that $!$ is the unit of the pushout tensor and pullback cotensor of

37

the enrichment of $\mathfrak{sE}$ in $\mathfrak{sSet}$. Recall that pushout tensors with levelwise complemented inclusions between finite simplicial sets such as $!$, $\lambda_1^0$, $\lambda_1^0$ exist by Proposition 5.5.

**Lemma 7.1.** *Let $f: X \to Y$ be a map in $\mathfrak{sE}$. For $k \in \{0, 1\}$, the following are equivalent:*

- (i) $f$ is a $k$-oriented strong homotopy equivalence,
- (ii) $\theta_k \widehat{\cap} f: f \to \lambda_1^k \widehat{\cap} f$ is a split monomorphism,
- (iii) $\theta_k \widehat{\cap} f: \lambda_1^k \widehat{\cap} f \to f$ is a split epimorphism.

*Proof.* Identical to [GS17, Lemma 4.3] and [GSS19, Lemma 3.1.1].

**Corollary 7.2.** *Let $i$ be a levelwise complemented inclusion between finite simplicial sets that is a strong homotopy equivalence. For any map $f$ in $\mathfrak{sE}$, the pushout tensor $i \widehat{\cap} f$ is a strong homotopy equivalence in $\mathfrak{sE}$.*

*Proof.* This is a formal consequence of the characterisation (ii) of strong homotopy equivalences given by Lemma 7.1. We have $\theta_k \widehat{\cap} (i \widehat{\cap} f) \cong (\theta_k \widehat{\times} i) \widehat{\cap} f$, a formal consequence of the isomorphism $A \cdot (B \cdot X) \cong (A \times B) \cdot X$ natural in $A, B \in \mathfrak{sSet}$ and $X \in \mathfrak{sE}$. By assumption, $\theta_k \widehat{\times} i$ has a retraction, hence also its image under $(-\widehat{\cap}) \widehat{\cap} f$.

Strong homotopy equivalences can be used to relate cofibrations and trivial cofibrations.

### Corollary 7.3.

- (i) *For a horn inclusion $j \in J_{\mathfrak{sSet}}$ and $E \in \mathcal{E}$, the map $j \cdot E$ is a strong homotopy equivalence and cofibration between cofibrant objects.*
- (ii) *Any cofibration that is a strong homotopy equivalence is a trivial cofibration.*

*Proof.* For part (i), recall from [GZ67, Chapter IV, Section 2, Paragraph 2.1.3] that the horn inclusion $j$ in $\mathfrak{sSet}$ is a strong homotopy equivalence. By Corollary 7.2, it follows that $j \cdot E$ is a strong homotopy equivalence. The object $E \in \mathfrak{sE}$ is cofibrant by part (i) of Proposition 5.9. By Proposition 5.5, it follows that $j \cdot E$ is a cofibration between cofibrant objects.

Part (ii) follows from the characterisation of strong homotopy equivalences in condition (ii) of Lemma 7.1, closure of trivial cofibrations under retracts (Lemma 3.9), and Proposition 5.5 (using that $\lambda_1^0$ and $\lambda_1^1$ are trivial cofibrations).

### Lemma 7.4. Let

$$\begin{array}{c} B \longrightarrow A \\ g \downarrow \quad \downarrow \quad \downarrow f \\ X \longrightarrow Y \end{array}$$

*be a pullback square with $X$ cofibrant. If, $f$ is a $k$-oriented strong homotopy equivalence, where $k \in \{0, 1\}$, then so is $g$.*

*Proof.* This is identical to [GSS19, Lemma 3.1.3], but played out in $\mathfrak{sE}_{\mathrm{cof}}$ instead of $\mathfrak{sSet}_{\mathrm{cof}}$. The pushout product with $\{1\} \to \Delta[1]$ (for $k = 0$) becomes a pushout tensor, which sends the cofibration $\varnothing \to X$ to a trivial cofibration by Proposition 5.5.

38

**Corollary 7.5.** Let $f \colon X \to Y$ be a Kan fibration with $X$ cofibrant. The pullback functor $f^* \colon \mathcal{E} \downarrow Y \to \mathcal{E} \downarrow X$ preserves maps that in $\mathfrak{s}\mathcal{E}$ are strong homotopy equivalences with cofibrant target.

*Proof.* This follows from Lemma 7.4 using part (ii) of Lemma 1.5 and stability of cofibrant objects under pullback along maps with cofibrant source using part (ii) of Proposition 5.9. $\square$

**Proposition 7.6** (Frobenius property). Let $f \colon X \to Y$ be a Kan fibration with $X$ cofibrant. The pullback functor $f^* \colon \mathcal{E} \downarrow Y \to \mathcal{E} \downarrow X$ preserves trivial cofibrations.

*Proof.* Let $j$ be a trivial cofibration over $Y$. By Proposition 3.17, its underlying map in $\mathfrak{s}\mathcal{E}$ can be written as a retract of a $J_{\mathfrak{s}\mathcal{E}}$-cell complex $j'$. The retraction (including $j'$) lifts uniquely to the slice over $Y$. Since functors preserve retracts, this makes $f^*j$ a retract of $f^*j'$. By Lemma 3.9, it will thus suffice to show that $f^*j'$ is a trivial cofibration.

Recall that $J_{\mathfrak{s}\mathcal{E}}$ consists of levelwise complemented inclusions. By countable lextensivity, Lemma 3.8, and Corollary 2.12, the pullback functor $f^*$ preserves the colimits (countable coproducts, pushouts, sequential colimit) forming the cell complex $j'$. By Lemma 3.9, it thus remains to show that $f^*$ sends to a trivial cofibration any map that in $\mathfrak{s}\mathcal{E}$ is of the form $E \times j''$ where $E \in \mathfrak{s}\mathcal{E}$ and $j'' \in J_{\mathfrak{s}\mathcal{E}}$. Using Lemma 5.4, this simplifies to $j'' \cdot E$. Here, we see $E$ as a constant simplicial object in $\mathcal{E}$.

By part (i) of Corollary 7.3, $j'' \cdot E$ is a strong homotopy equivalence and cofibration between cofibrant objects. By Corollary 7.5, $f^*(j'' \cdot E)$ is a strong homotopy equivalence (using that $f$ is a Kan fibration). By part (i), $f^*(j'' \cdot E)$ is a cofibration between cofibrant objects. By part (ii) of Corollary 7.3, we conclude that $f^*(j'' \cdot E)$ is a trivial cofibration. $\square$

## 8 Fibration extension properties

In this section, we establish two important ingredients in the construction of the effective model structure: the trivial fibration extension property (Proposition 8.5) and the fibration extension property (Proposition 8.13). These arguments are based on the equivalence extension property (Proposition 8.3). We work purely within the cofibrant fragment $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ of $\mathfrak{s}\mathcal{E}$. Our earlier preliminaries allow us to prove the equivalence extension property in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ following [Sat17, Proposition 5.1] and [GSS19, Proposition 3.2.1].

We begin with some observations on homotopy equivalences, which we introduced in Section 1, and an analysis of the restriction of the fibration category structure on $\mathfrak{s}\mathcal{E} \downarrow X$ established in Theorem 1.9 to cofibrant objects. Since the tensor of $X \in \mathfrak{s}\mathcal{E}$ with a finite simplicial set exists and is defined by the formula in (2.1), we may equivalently write a homotopy $H$ between $f_0, f_1 \colon X \to Y$ in $\mathfrak{s}\mathcal{E}$ or one of its slices, which was defined using cotensors in (1.3), via a map

$$H \colon \Delta[1] \cdot X \to Y. \tag{8.1}$$

In $\mathcal{E}$ and its slices, the homotopy relation between maps with cofibrant source and fibrant target is an equivalence relation. This is a formal consequence of part (i) of Lemma 1.5 and Lemma 1.8. It follows that homotopy equivalences between cofibrant and fibrant objects compose as usual.

### Proposition 8.1.

- (i) *For every $X \in \mathfrak{s}\mathcal{E}$, trivial cofibrations in $\mathfrak{s}\mathcal{E} \downarrow X$ are homotopy equivalences.*
- (ii) *Trivial fibrations $X \to Y$ in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ are homotopy equivalences over $Y$.*

39

Proof. For part (i), in $\mathcal{E} \downarrow X$, given a trivial cofibration $A \to B$, we take a lift

![img-29.jpeg](img-29.jpeg)

Here, the right map is a composition of the pullback cotensor with $\partial\Delta[1] \to \Delta[1]$ of $B \to 1$ and a pullback of $A \to 1$, hence a fibration by parts (i) and (ii) of Lemma 1.5. The lift exhibits $A \to B$ as a strong deformation retract, in particular a homotopy equivalence.

For part (ii), given a fibration $X \to Y$ in $\mathcal{E}_{\mathrm{cof}}$, we take a lift

![img-30.jpeg](img-30.jpeg)

Here, the left map is a composition of a pushout of $\varnothing \to Y$ and the pushout tensor with $\partial\Delta[1] \to \Delta[1]$ of $\varnothing \to X$, hence a cofibration by Lemma 3.9 and Proposition 5.5. The lift exhibits $X \to Y$ as the dual of a strong deformation retract, in particular a homotopy equivalence over $Y$.

**Proposition 8.2.** Let $X \in \mathfrak{s}\mathcal{E}_{\mathrm{cof}}$. The fibration category structure on $\mathfrak{s}\mathcal{E} \downarrow X$ of Theorem 1.9 restricts to $\mathfrak{s}\mathcal{E}_{\mathrm{cof}} \downarrow X$. Path objects are given by cotensor with $\Delta[1]$. The weak equivalences coincide with homotopy equivalences over $X$.

Proof. By part (iii) of Proposition 5.9, $\mathfrak{s}\mathcal{E}_{\mathrm{cof}} \downarrow X$ has finite limits and they are computed as in $\mathfrak{s}\mathcal{E} \downarrow X$. By part (iii) of Lemma 5.6, cotensor with $\Delta[1]$ over $X$ preserves cofibrant objects. Thus, all aspects of the fibration category $\mathfrak{s}\mathcal{E} \downarrow X$ of Theorem 1.9 restrict to cofibrant objects. This includes path objects, which are given by cotensor with $\Delta[1]$.

It remains to show that pointwise weak equivalences in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}} \downarrow X$ coincide with homotopy equivalences over $X$. Every homotopy equivalence is a pointwise weak equivalence by Proposition 1.10. For the reverse direction, we use the mapping path space factorisation in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}} \downarrow X$, which has a homotopy equivalence over $X$ as first factor and fibration as second factor. Since pointwise weak equivalences and homotopy equivalences over $X$ satisfy the 2-out-of-3 property, it suffices to show that every pointwise weak equivalence that is a fibration (hence a trivial fibration) is a homotopy equivalence over $X$. This is part (ii) of Proposition 8.1.

**Proposition 8.3** (Equivalence extension property). In $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$, consider the solid part of the diagram

![img-31.jpeg](img-31.jpeg)

40

where the lower square is a pullback and $X_0 \to X_1$ is a homotopy equivalence over $A$. Then there is $Y_0$ as indicated such that the back square is a pullback and $Y_0 \to Y_1$ is a homotopy equivalence over $B$.

Proof. The proof of [GSS19, Proposition 3.2.1] applies, but played out in $\mathfrak{sE}_{\mathrm{cof}}$ instead of $\mathfrak{sSet}_{\mathrm{cof}}$. We limit ourselves to listing the key claims used in the proof and why they hold in our setting.

- The slice categories $\mathfrak{sE}_{\mathrm{cof}} \downarrow A$ and $\mathfrak{sE}_{\mathrm{cof}} \downarrow B$ admit fibration category structures, established in Proposition 8.2, in which weak equivalences are given by fiberwise homotopy equivalences.
- The dependent product functor $i_*$ along $i$ exists and preserves cofibrant objects, as shown in Theorem 6.5.
- The functor $i_*$ preserves trivial fibrations, which follows by adjointness since $i^*$ preserves cofibrations, as stated in part (i) of Proposition 5.9.
- In the slice over $B$, pullback cotensor with a cofibration preserves trivial fibrations, which holds by Lemma 1.8.

In $\mathfrak{sE}_{\mathrm{cof}}$, we say that a (trivial) fibration $X \twoheadrightarrow A$ extends along a map $A \to B$ if there is a pullback square

$$\begin{array}{c} X \dashrightarrow Y \\ \downarrow \quad \downarrow \\ A \longrightarrow B \end{array} \tag{8.3}$$

with the extension $Y \to B$ of $X \to A$ again a (trivial) fibration. If $A \to B$ has this property for all (trivial) fibrations $X \twoheadrightarrow A$, we say that it has the (trivial) fibration extension property.

Lemma 8.4. Let $f$ and $g$ be composable maps in $\mathfrak{sE}_{\mathrm{cof}}$. If $g \circ f$ has the (trivial) fibration extension property, then so does $f$.

Proof. We extend along $f$ by extending along $g \circ f$ and pulling back along $g$ (using part (ii) of Lemma 1.5 and part (ii) of Proposition 5.9).

Proposition 8.5 (Trivial fibration extension property). Cofibrations in $\mathfrak{sE}$ have the trivial fibration extension property.

Proof. This is the special case of Proposition 8.3 where $X_1 \to A$ and $Y_1 \to B$ are the identities on $A$ and $B$, respectively. We use Theorem 1.9 and Proposition 4.1 to go between trivial fibrations and fibrations that are weak equivalences.

Lemma 8.6. Let $p \colon X \twoheadrightarrow \Delta[1] \cdot A$ be fibration in $\mathfrak{sE}$ with $A$ and $X$ cofibrant. Then there is a homotopy equivalence between $X|_{\{0\} \cdot A}$ and $X|_{\{1\} \cdot A}$ over $A$.

Proof. Take the pullback

![img-32.jpeg](img-32.jpeg)

41

Here, the bottom map is the unit of the tensor-cotensor adjunction. The right map is a fibration by part (i) of Lemma 1.5, hence the left map is a fibration by part (ii) of Lemma 1.5. The top right object is cofibrant is cofibrant by part (i) of Lemma 1.5 and part (ii), hence the top left object is cofibrant by part (ii).

We will argue that there are trivial fibrations from $P$ to $X|_{\{0\} \cdot A}$ and $X|_{\{1\} \cdot A}$ over $A$. These trivial fibrations are homotopy equivalences over $A$ by part (ii) of Proposition 8.1. Inverting and composing them as needed gives the desired weak equivalence.

We only construct the trivial fibration from $P$ to $X|_{\{0\} \cdot A}$ (the other case is dual). Consider the diagram

![img-33.jpeg](img-33.jpeg)

The two composite squares and the bottom right square are pullbacks by construction. Pullback pasting induces the top left map and makes the top left square a pullback. The top middle map is a trivial fibration by part (i) of Lemma 1.5, hence so is the top left map by part (ii) of Lemma 1.5. $\square$

Our aim now is to prove the fibration extension property for trivial cofibrations in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$. For this purpose, we introduce the class $\mathcal{H}$ of cofibrations in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ that have the fibration extension property.

**Lemma 8.7.** *The class $\mathcal{H}$ contains cofibrations in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ that are strong homotopy equivalences.*

*Proof.* Let $A \to B$ be a cofibration in $\mathfrak{s}\mathcal{E}_{\mathrm{cof}}$ and 0-oriented strong homotopy equivalence (the 1-oriented case is dual). We will solve the extension problem (8.3). By the characterisation of strong homotopy equivalences given by part (3) of Lemma 7.1, we have a retract diagram

![img-34.jpeg](img-34.jpeg)

Let $Z \to \Delta[1] \cdot A \sqcup_{\{0\} \cdot A} \{0\} \cdot B$ denote the pullback of $X \to A$ along the top right map. Pulling back $Z$ to $\Delta[1] \cdot A$, $\{0\} \cdot A$ and $\{0\} \cdot B$ (the components of its base pushout), we obtain the solid part of the diagram

![img-35.jpeg](img-35.jpeg)

42

with lower square a pullback. Here, the weak equivalences over $A$ is given by Lemma 8.6. We then complete the diagram using Proposition 8.3, making the back square a pullback. Note that $Z|_{\{1\} \cdot A}$ is isomorphic to $X$ over $A$ by the retract (8.4). The extension in (8.3) is then given by $Y \rightarrow B$. $\square$

**Corollary 8.8.** *For a horn inclusion $j \in J_{\mathfrak{sSet}}$ and $E \in \mathcal{E}$, we have $j \cdot E \in \mathcal{H}$.*

*Proof.* This is the application of Lemma 8.7 to part (i) of Corollary 7.3. $\square$

**Lemma 8.9.** *The class $\mathcal{H}$ is closed under countable coproducts.*

*Proof.* Let $A_i \rightarrow B_i$ be a family of maps in $\mathcal{H}$ for $i \in I$ countable. Note that $\coprod_{i \in I} A_i \rightarrow \coprod_{i \in I} B_i$ is a cofibration between cofibrant objects by Lemma 3.9. Suppose we are given a fibration $X \rightarrow \coprod_{i \in I} A_i$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. We aim to extend it along $\coprod_{i \in I} A_i \rightarrow \coprod_{i \in I} B_i$. Note that $\coprod_{i \in I} B_i$ is a van Kampen colimit since $\mathfrak{s}\mathcal{E}$ is countably lextensive.

For each $i \in I$, we pull it back to a fibration $X_i \rightarrow A_i$ (with $X_i$ cofibrant by part (ii)) and extend it to a fibration $Y_i \rightarrow B_i$. We take their coproduct $\coprod_{i \in I} Y_i \rightarrow \coprod_{i \in I} B_i$. This is a fibration by part (i) of Lemma 3.18. Its domain is cofibrant by Lemma 3.9. By effectivity, it pulls back along $A_i \rightarrow \coprod_{i \in I} B_i$ to the map $X_i \rightarrow A_i$ for $i \in I$. By universality, it thus pulls back along $\coprod_{i \in I} A_i \rightarrow \coprod_{i \in I} B_i$ to the original fibration $X \rightarrow \coprod_{i \in I} A_i$. $\square$

**Lemma 8.10.** *The class $\mathcal{H}$ is closed under pushouts in $\mathfrak{s}\mathcal{E}$ along maps with cofibrant target.*

*Proof.* Consider a pushout square

$$\begin{array}{c} A \longrightarrow A' \\ \downarrow \in \mathcal{H} \quad \downarrow \\ B \longrightarrow B'. \end{array}$$

with $A'$ cofibrant. Note that $A' \rightarrow B'$ is a cofibration between cofibrant objects by Lemma 3.9. The pushout is van Kampen by part (i) of Corollary 2.12. Suppose we are given a fibration $X' \rightarrow A'$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. We aim to extend it along $A' \rightarrow B'$.

We pull the given fibration back along $A \rightarrow A'$ to a fibration $X \rightarrow A$ (here, $X$ is cofibrant by part (ii)) and extend it to a fibration $Y \rightarrow B$. Let $Y' \rightarrow B'$ be the pushout in the arrow category of these three maps. By effectivity, it pulls back to them. It is a fibration by part (ii) of Lemma 3.18. By part (i), $X \rightarrow Y$ is a cofibration, hence so is $X' \rightarrow Y'$ by Lemma 3.9. This makes $Y'$ cofibrant.

We check that $Y' \rightarrow B'$ is a fibration using Proposition 3.4. For each horn inclusion $j \in J_{\mathfrak{sSet}}$, we construct a section of $\widehat{\mathrm{ev}}_j(Y' \rightarrow B')$ given sections of $\widehat{\mathrm{ev}}_j(X' \rightarrow A')$ and $\widehat{\mathrm{ev}}_j(Y \rightarrow B)$. We pull the section of $\widehat{\mathrm{ev}}_j(X' \rightarrow A')$ back to a section of $\widehat{\mathrm{ev}}_j(X \rightarrow A)$ and then extend it using Lemma 3.13 to a section of $\widehat{\mathrm{ev}}_j(Y \rightarrow B)$. The goal follows by Lemma 2.15 and functoriality of colimits. $\square$

**Lemma 8.11.** *The class $\mathcal{H}$ is closed under sequential colimits.*

*Proof.* Consider the colimit $B$ of a sequential diagram

$$A_0 \xrightarrow{\in \mathcal{H}} A_1 \xrightarrow{\in \mathcal{H}} \dots.$$

Note that it is van Kampen by part (ii) of Corollary 2.12. Suppose we are given a fibration $X_0 \rightarrow A_0$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. We aim to extend it along $A_0 \rightarrow B$.

43

By induction on $k$, we extend to a fibration $X_k \to A_k$. The maps $X_k \to X_{k+1}$ are cofibrations by part (i). In the end, we take the colimit and obtain a map $Y \to B$. By effectivity, it pulls back to the maps $X_k \to A_k$. It is a fibration by part (iii) of Lemma 3.18. Note that $Y$ is cofibrant by Lemma 3.9. $\square$

**Lemma 8.12.** *The class $\mathcal{H}$ is closed under codomain retracts.*

*Proof.* This is an instance of Lemma 8.4. $\square$

**Proposition 8.13** (Fibration extension property). *Trivial cofibrations in $\mathfrak{S}_{\mathrm{cof}}$ have the fibration extension property.*

*Proof.* We have to show that $\mathcal{H}$ includes all trivial cofibrations between cofibrant objects. By Proposition 3.17, any such trivial cofibration can be written as a codomain retract of a sequential colimit of pushouts of countable coproducts of tensors with objects of $E$ of maps in $J_{\mathfrak{S}_{\mathrm{cof}}}$. By induction, all the stages of the sequential colimit are cofibrant. This means that the above pushout squares all consist of cofibrant objects. The claim now follows starting from Corollary 8.8 using the closure properties of $\mathcal{H}$ given by Lemmas 8.9, 8.10, 8.11 and 8.12. $\square$

## 9 The effective model structure

The main goal of this section is to establish the existence of the effective model structure. Since the categories with which we work have finite limits but do not necessarily have finite colimits, it is appropriate to consider a slight generalisation of the usual notion of a model structure. For a category $\mathcal{E}$ with an initial object and a terminal object, a *model structure* on $\mathcal{E}$ consists of three classes of maps $\mathbf{W}$, $\mathbf{C}$, $\mathbf{F}$ such that

- $(\mathbf{C}, \mathbf{F} \cap \mathbf{W})$ and $(\mathbf{C} \cap \mathbf{W}, \mathbf{F})$ are weak factorisation systems;
- $\mathbf{W}$ satisfies the 2-out-of-3 property;
- $\mathcal{E}$ has pushouts along maps in $\mathbf{C}$;
- $\mathcal{E}$ has pullbacks along maps in $\mathbf{F}$.

It can then be shown that $\mathbf{W}$ is closed under retracts, as the known proof of this fact (see [JT07, Proposition 7.8] and [Rie14, Lemma 11.3.3]) applies also assuming only the restricted limits and colimits above. Thus, when $\mathcal{E}$ is finitely complete and cocomplete, this notion is equivalent to the usual one. Similarly, a model structure is determined by two of its three classes of maps also in this setting.

Let us now fix a countably lextensive category $\mathcal{E}$. The existence of the effective model structure on $\mathfrak{S}_{\mathrm{cof}}$ will be a formal consequence of the Frobenius property of Section 7, the (trivial) fibration extension property of Section 8, and elementary properties of the two weak factorisation systems of Theorem 4.2. To this end, we encapsulate what is used from Section 8 as a collection of extension operations that all follow the same pattern.

**Lemma 9.1.** *The following hold in $\mathfrak{S}_{\mathrm{cof}}$.*

44

(i) Let $A \rightarrow B$ be a cofibration and $X \rightarrow A$ be a trivial fibration. There is a pullback square

![img-36.jpeg](img-36.jpeg)

with $X \rightarrow Y$ a cofibration and $Y \rightarrow B$ a trivial fibration.

(ii) Let $A \rightarrow B$ be a trivial cofibration and $X \rightarrow A$ be a fibration. There is a pullback square

![img-37.jpeg](img-37.jpeg)

with $X \rightarrow Y$ a trivial cofibration and $Y \rightarrow B$ a fibration.

(iii) Let $A \rightarrow B$ be a trivial cofibration and $X \rightarrow A$ be a trivial fibration. There is a pullback square

![img-38.jpeg](img-38.jpeg)

with $X \rightarrow Y$ a trivial cofibration and $Y \rightarrow B$ a trivial fibration.

*Proof.* Part (i) is the combination of Proposition 8.5 with part (i) of Proposition 5.9. Part (ii) is the combination of Proposition 8.13 with Proposition 7.6. Part (iii) follows from part (i) using Proposition 7.6 (with Proposition 5.2). $\square$

Recall from Section 1 that a map $X \rightarrow Y$ in $\mathfrak{s}\mathcal{E}_{\text{fib}}$ is a weak equivalence in the fibration category of Theorem 1.7 if and only if it is a pointwise weak equivalence in the sense of Definition 1.6, i.e., $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \rightarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, Y)$ is a weak homotopy equivalence of simplicial sets for all $E \in \mathcal{E}$. Restricting to cofibrant objects, we obtain a notion of weak equivalence in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$ that satisfies 2-out-of-3 and interacts as expected with cofibrations and fibrations, as recollected below.

**Lemma 9.2.** In $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$, we have:

- (i) a cofibration is a trivial cofibration exactly if it is a weak equivalence,
- (ii) a fibration is a trivial fibration exactly if it is a weak equivalence.

*Proof.* Part (ii) is a corollary of Proposition 4.1. For part (i), the forward direction is the combination of part (i) of Proposition 8.1 and Proposition 1.10. With this, the reverse direction follows by the retract argument. $\square$

45

In the following, we fix the following terminology regarding the weak factorisation systems of Theorem 4.2. A *fibrant replacement* of $X \in \mathfrak{s}\mathcal{E}$ is a trivial cofibration $X \rightarrow X'$ with $X'$ fibrant. By a fibrant replacement of a diagram, we mean a levelwise fibrant replacement: given a diagram $X: \mathcal{S} \rightarrow \mathfrak{s}\mathcal{E}$, this is a diagram $X': \mathcal{S} \rightarrow \mathfrak{s}\mathcal{E}_{\text{fib}}$ with a natural transformation $X \rightarrow X'$ that is levelwise a trivial cofibration. If $\mathcal{S}$ is a finite Reedy category, we can always construct such a replacement using Theorem 3.14 and the Reedy process. In particular, for [1] seen as a direct category, we obtain a fibrant replacement of any arrow that we call *canonical*. Note that the canonical fibrant replacement preserves trivial cofibrations. We use dual terminology for *cofibrant replacement*.

Let us write $\mathbf{W}_{\text{cof}}$ for the class of maps in $\mathfrak{s}\mathcal{E}_{\text{cof}}$ whose canonical fibrant replacement is a weak equivalence in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$. This will be the class of weak equivalences in the model structure on $\mathfrak{s}\mathcal{E}_{\text{cof}}$ to be established in Proposition 9.6.

**Lemma 9.3.** *Let $A \rightarrow B$ in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. Then, the the following are equivalent:*

- (i) *the map $A \rightarrow B$ is in $\mathbf{W}_{\text{cof}}$*,
- (ii) *the map $A \rightarrow B$ has a fibrant replacement that is a weak equivalence in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$*,
- (iii) *all fibrant replacements of the map $A \rightarrow B$ are weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$*.

*Proof.* This is a standard argument and goes exactly as in [GSS19, Lemma 3.3.1]. What is used is part (i) of Corollary 2.12 with the fact that trivial cofibrations are levelwise complemented inclusions (Proposition 3.17), and closure properties of trivial cofibrations (Lemma 3.9), the forward direction of part (i) of Lemma 9.2, and 2-out-of-3 for weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$. $\square$

**Corollary 9.4.** *The class $\mathbf{W}_{\text{cof}}$ satisfies the 2-out-of-3 property.*

*Proof.* Using Lemma 9.3 with levelwise fibrant replacement of the given 2-out-of-3 diagram, this reduces to closure of weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$ under 2-out-of-3. This is part of Theorem 1.7. $\square$

**Lemma 9.5.** *In $\mathfrak{s}\mathcal{E}_{\text{cof}}$, a fibration is a trivial fibration if and only if it is in $\mathbf{W}_{\text{cof}}$.*

*Proof.* Let $X \rightarrow Y$ be a fibration in $\mathfrak{s}\mathcal{E}_{\text{cof}}$. Take a fibrant replacement $Y \rightarrow \overline{Y}$.

If $X \rightarrow Y$ is a trivial fibration, we extend it to a trivial fibration $\overline{X} \rightarrow \overline{Y}$ using part (iii) of Lemma 9.1. Then $\overline{X} \rightarrow \overline{Y}$ is a weak equivalence by part (ii) of Lemma 9.2, hence $X \rightarrow Y$ is in $\mathbf{W}_{\text{cof}}$ by Lemma 9.3.

In the reverse direction, we extend $X \rightarrow Y$ to a fibration $\overline{X} \rightarrow \overline{Y}$ using part (ii) of Lemma 9.1. If $X \rightarrow Y$ is in $\mathbf{W}_{\text{cof}}$, then $\overline{X} \rightarrow \overline{Y}$ is a weak equivalence by Lemma 9.3, hence a trivial fibration by part (ii) of Lemma 9.2. Then its pullback $X \rightarrow Y$ is a trivial fibration by part (ii) of Lemma 1.5. $\square$

**Proposition 9.6.** *The category $\mathfrak{s}\mathcal{E}_{\text{cof}}$ admits a model structure with weak equivalences $\mathbf{W}_{\text{cof}}$ and the two weak factorisation systems of Theorem 4.2.*

*Proof.* First note that $\mathfrak{s}\mathcal{E}_{\text{cof}}$ has finite limits by part (iii) of Proposition 5.9, an initial object by lextensivity, and pushouts of cofibrations by part (i) of Corollary 2.12 (since cofibrations are levelwise complemented inclusions by Proposition 3.17). The class $\mathbf{W}_{\text{cof}}$ satisfies 2-out-of-3 by Corollary 9.4.

It remains to show that a (co)fibration is trivial exactly if it is a weak equivalence. For fibrations, this is Lemma 9.5. For cofibrations, the forward direction is immediate using Lemma 9.3: a given trivial cofibration has as fibrant replacement the identity on a fibrant replacement of its codomain; but identities are weak equivalences in $\mathfrak{s}\mathcal{E}_{\text{cof, fib}}$ by Theorem 1.7. The backward direction follows from this by the retract argument. $\square$

46

We write $\mathbf{W}$ for the class of maps in $\mathfrak{SE}$ whose canonical cofibrant replacement is in $\mathbf{W}_{\mathrm{cof}}$. This is the class of weak equivalences of the effective model structure, to be established in Theorem 9.9.

**Lemma 9.7.** *Let $A \to B$ in $\mathfrak{SE}$. Then, the following are equivalent:*

(i) the map $A \to B$ is in $\mathbf{W}$,
(ii) the map $A \to B$ has a cofibrant replacement in $\mathbf{W}_{\mathrm{cof}}$,
(iii) all cofibrant replacements of the map $A \to B$ are in $\mathbf{W}_{\mathrm{cof}}$.

*Proof.* This is a standard argument, dual to the one of Lemma 9.3. What is used is closure properties of trivial fibrations (part (ii) of Lemma 1.5) and the model structure on $\mathcal{E}_{\mathrm{cof}}$ of Proposition 9.6. $\square$

**Corollary 9.8.** *The class $\mathbf{W}$ satisfies the 2-out-of-3 property.*

*Proof.* This is analogous to the proof of Corollary 9.4. $\square$

We can finally establish the existence of the effective model structure on $\mathfrak{SE}$.

**Theorem 9.9** (The effective model structure). *Let $\mathcal{E}$ be a countably lextensive category.*

(i) The category $\mathfrak{SE}$ of simplicial objects in $\mathcal{E}$ admits a model structure determined by the two weak factorisation systems of Theorem 4.2.
(ii) A map between fibrant objects is a weak equivalence in this model structure if and only if it is a pointwise weak equivalence in the sense of Definition 1.6.
(iii) More generally, for $X \in \mathfrak{SE}$, a map in $\mathfrak{SE} \nmid X$ is a weak equivalence exactly if and only if it is a pointwise weak equivalence in $\mathfrak{SE}$ in the sense of Definition 1.6.

*Proof.* First note that $\mathfrak{SE}$ has finite limits by lextensivity and the required colimits of a model structure by the same reasoning used for Proposition 9.6. We define the class of weak equivalences to be $\mathbf{W}$. It satisfies 2-out-of-3 by Corollary 9.4. It remains to show that a (co)fibration is trivial exactly if it is a weak equivalence.

Due to our definition of $\mathbf{W}$, we get for free that every trivial fibration is a weak equivalence, dually to the reasoning for trivial cofibrations in Proposition 9.6.

For the reverse direction, let $X \to Y$ be a fibration and weak equivalence. Let $\widehat{X} \to \widehat{Y}$ denote its canonical cofibrant replacement. This is the Reedy cofibrant replacement over the inverse category [1], hence again a fibration. Since $\widehat{X} \to \widehat{Y}$ is a fibration and weak equivalence in $\mathcal{E}_{\mathrm{cof}}$, it is a trivial fibration by Proposition 9.6. The composite $\widehat{X} \to Y$ is a trivial fibration by part (ii) of Lemma 1.5. By part (iii) of Lemma 1.5, we deduce that $X \to Y$ is a trivial fibration.

Let $A \to B$ be a trivial cofibration. Take a cofibrant replacement $\widehat{B} \to B$. Let $\widehat{A} \to A$ be its pullback along $A \to B$. Then $\widehat{A}$ is cofibrant by Lemma 5.7 since trivial cofibrations are monomorphisms by Proposition 5.2, $\widehat{A} \to A$ is a trivial fibration by part (ii) of Lemma 1.5, and $\widehat{A} \to \widehat{B}$ is a trivial cofibration by Proposition 7.6. In particular, $\widehat{A} \to \widehat{B}$ is a cofibrant replacement of $A \to B$. Since it is a trivial cofibration, it is a weak equivalence in $\mathcal{E}_{\mathrm{cof}}$ by Proposition 9.6. By Lemma 9.7, this makes $A \to B$ is a weak equivalence.

It remains to show that every cofibration that is a weak equivalence is a trivial cofibration. As in Proposition 9.6, this follows from what we have already established by the retract argument.

47

This finishes the verification of part (i). Parts (ii) and (iii) follow since every model structure induces a fibration category structure on its fibrant objects (and those of its slices) and the weak equivalences in a fibration category are determined by its fibrations and trivial fibrations. In our case, we obtain the fibration categories of Theorems 1.7 and 1.9. $\square$

By part (ii) of Theorem 9.9, a map is a weak equivalence in the effective model structure if and only if its fibrant replacement is a pointwise weak equivalence. This gives us a description of weak equivalences independent from the class $\mathbf{W}$ used in the construction of the model structure.

The next remark compares the effective model structure Theorem 9.9 to other model structures on categories of simplicial objects.

**Remark 9.10.** When $\mathcal{E}$, and hence $\mathfrak{s}\mathcal{E}$, is a locally presentable, then one can use the enriched small object argument of [Rie14, Chapter 13] to produce the two weak factorisation systems on $\mathfrak{s}\mathcal{E}$ whose fibrations and trivial fibrations are as in Definition 1.3. Theorem 1.7 then implies that $\mathfrak{s}\mathcal{E}$ is a weak model category, for example using the dual of [Hen18, Proposition 2.3.3]. It then follows from [Hen20, Theorem 3.7] that its left saturation (in the sense of [Hen20, Theorem 4.1]) is a left semi-model category, and from [Hen20, Theorem 3.8] that it is also a right semi-model category. In general, this is not quite enough to conclude that it is a Quillen model category (it is what is called a two-sided model category in [Hen20, Section 5]), but this is already sufficient for many applications.

When $\mathcal{E}$ is an additive locally presentable category, then there is Quillen model structure on $\mathfrak{s}\mathcal{E}$ whose fibrations and trivial fibrations are exactly as in Definition 1.3. The additional ingredient in this case is that for $A \in \mathcal{E}$ and $X \in \mathfrak{s}\mathcal{E}$, the object $\operatorname{Hom}_{\mathfrak{s}\mathfrak{s}\mathfrak{e}}(A, X)$ is a simplicial abelian group, hence is always a Kan complex. This shows that when $\mathcal{E}$ is additive, all objects of $\mathfrak{s}\mathcal{E}$ are Kan complexes, hence in the discussion above it is immediate that $\mathfrak{s}\mathcal{E}$ is left saturated (in the sense of [Hen20]) and as it is a saturated right semi-model category where every object is fibrant it is a Quillen model category. By the Dold–Kan correspondence, the category $\mathfrak{s}\mathcal{E}$ is equivalent to the category of chain complexes concentrated in non-negative degrees in $\mathcal{E}$ and under this equivalence the model structure is the so-called absolute (or Hurewicz) model structure on chain complexes (see, e.g., [CH02, Corollary 6.4]).

A different model structure on $\mathfrak{s}\mathcal{E}$ is established by Quillen in [Qui67, Section II.4] assuming that $\mathcal{E}$ has finite limits, enough projectives and is either cocomplete with a small set of generators (thus permitting the small object argument) or such that every object in $\mathfrak{s}\mathcal{E}$ is fibrant. Quillen's weak equivalences and fibrations include the *pointwise* weak equivalences and fibrations defined here (as the former are defined using evaluation with respect to projective objects only) and the identity functor is a left Quillen functor from Quillen's model structure to the effective one. If effective epimorphisms split, then the two model structures coincide.

A class of model structures on $\mathfrak{s}\mathcal{E}$ is also defined in [GJ99, Chapter II]. The construction is parametrised by a functor $G: \mathfrak{s}\mathcal{E} \rightarrow \mathfrak{s}\mathfrak{s}\mathfrak{e}$ with a left adjoint from which weak equivalences and fibrations are created. If $\mathcal{E}$ is complete and cocomplete and maps with the left lifting property with respect to fibrations are weak equivalences, one obtains a model structure. This is quite different from the effective model structure and more in the spirit of generalizing [Qui67, Section II.4].

Finally, a model structure on $\mathfrak{s}\mathcal{E}$ has been obtained also in [Hör21], which appeared shortly after the first version of the present paper and was developed independently. Theorem 6.1 therein is a special case of our Theorem 9.9, obtained under the additional assumption that every object of $\mathcal{E}$ is a coproduct of $\mathbb{N}$-small objects (see [Hör21] for details).

48

## 10 Descent and right properness

Having established the existence of the effective model structure on $\mathfrak{s}\mathcal{E}$, we now study some of its properties and those of its associated $\infty$-category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$. There are many (essentially equivalent) ways of associating an $\infty$-category to a model category, and our result will make little use of a concrete details of how it is done beyond some very general results. For the sake of completeness, when we say $\infty$-category we mean quasicategory, and for a general category $\mathcal{C}$ equipped with a class of weak equivalences, we define $\mathrm{Ho}_{\infty}(\mathcal{C})$ as the $\infty$-category obtained by universally inverting the weak equivalences in $\mathcal{C}$. We refer to [Cis20], especially its Chapter 7, for the general theory of such localisations.

We begin by studying the behaviour of colimits, using the notion of descent, which was introduced in model categories by Rezk [Rez10] as a part of development of higher topos theory. We show that $\mathfrak{s}\mathcal{E}$ and hence $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ satisfies *descent* whenever $\mathfrak{s}\mathcal{E}$ is countably extensive. This means that colimits in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ satisfy the higher categorical version of the van Kampen property. In the case of pushouts, this is spelled out in Proposition 10.1 below. As in the ordinary categorical case, a colimit in an $\infty$-category $\mathcal{C}$ satisfies descent if and only if it is preserved by the functor from $\mathcal{C}^{\mathrm{op}}$ to the $\infty$-category of $\infty$-category classified by the slice cartesian fibration. This is essentially proved in section 6.1.3 of [Lur09], see for example 6.1.3.9.

**Proposition 10.1** (Model structure descent for pushouts). *Let $\mathcal{E}$ be a countably extensive category and let*

![img-39.jpeg](img-39.jpeg)

*be a cube in $\mathfrak{s}\mathcal{E}$. Assume that the bottom face is a homotopy pushout and that the left and back faces are homotopy pullbacks. Then the following are equivalent:*

- (i) *The top face is a homotopy pushout,*
- (ii) *the right and front faces are homotopy pullbacks.*

*Proof.* Let us view $[1]$ as a Reedy category consisting only of face operators. We consider the Reedy model structure $[D^{\mathrm{op}}, \mathfrak{s}\mathcal{E}]$ of $\mathfrak{s}\mathcal{E}$ over the Reedy category $D = [1] \times ([1] \times [1])^{\mathrm{op}}$. The significance of taking opposites on the latter two factors is that the Reedy category structure is inverted; the face operators become degeneracy operators. Recall from the beginning of Section 9 that we regard only certain (co)limits to be part of a model structure; the theory of Reedy model structures makes sense in this setting as seen in Section 4 for the case of the Reedy weak factorisation system over $\Delta$.

The given cube (10.1) forms an object of this category by sending $(0, a, b)$ to $Y_{ab}$ and $(1, a, b)$ to $X_{ab}$. Recall that weak equivalences in the Reedy model structure are levelwise and homotopy

49

pushouts and pullbacks are invariant under levelwise weak equivalences. We replace the given cube by a cofibrant and fibrant object. This reduces the claim to the case of (10.1) where all object are cofibrant and fibrant, all horizontal maps are cofibrations, and all vertical maps are fibrations.

Let us check the direction from (i) to (ii), i.e., universality. Take the pullback of the bottom face along $X_{11} \rightarrow Y_{11}$. Since all vertical faces in (10.1) are homotopy pullbacks, we obtain a square weakly equivalent to the top face. This reduces the claim to the situation where in addition all vertical faces in (10.1) are pullbacks. Note that the cofibrancy assumptions are preserved by part (i) of Proposition 5.9.

Denote $Q$ the pushout in the bottom face. Since $Y_{00} \rightarrow Y_{01}$ is a levelwise complemented inclusion (Proposition 3.17), $P$ is a van Kampen pushout by Lemma 2.9, in particular stable under pullback. From universality, we obtain a pullback square

![img-40.jpeg](img-40.jpeg)

where $P$ is the pushout in the top face. Since $X_{00} \rightarrow X_{01}$ and $Y_{00} \rightarrow Y_{01}$ are cofibrations, the bottom and top faces are homotopy pushouts exactly if the maps $P \rightarrow X_{11}$ and $Q \rightarrow Y_{11}$ are weak equivalences, respectively. The goal thus follows from right properness applied to (10.2).

Let us check the direction from (ii) to (i), i.e., effectivity. Take the pushout in the horizontal faces. Since all horizontal maps are cofibrations and the horizontal faces are homotopy pushouts, we obtain a cube weakly equivalent to the given cube. This reduces the goal to the situation where all horizontal faces in (10.1) are pushouts, but note that we lose fibrancy properties involving $X_{11}$ and $Y_{11}$. The cube is now determined (up to isomorphism) by just the left and back faces. Weakly equivalent left and back faces give rise to weakly equivalent cubes.

Since the back face is a homotopy pullback and the vertical maps are fibrations, the map $X_{00} \rightarrow Y_{00} \times Y_{01} X_{01}$ is a weak equivalence. We apply the equivalence extension property of Proposition 8.3 to this situation:

![img-41.jpeg](img-41.jpeg)

We perform the same construction in the left face, obtaining $X'_{10}$. Now, the squares

![img-42.jpeg](img-42.jpeg)

are weakly equivalent to the left and back faces, but are pullbacks. We have thus reduced to the situation where additionally the left and back faces of (10.1) are pullbacks.

50

Having strictified the given homotopy pushouts and homotopy pullbacks, we proceed as follows. The maps $X_{00} \to X_{01}$ and $X_{00} \to X_{10}$ are levelwise complemented inclusions by Proposition 3.17. The bottom pushout is van Kampen by part (i) of Corollary 2.12. In particular, the right and front faces are pullbacks. For them to be homotopy pullbacks, it suffices for $X_{11} \to Y_{11}$ to be a fibration. This holds by part (ii) of Lemma 3.18. $\square$

**Proposition 10.2** (Model structure descent for coproducts). *Let $\mathcal{E}$ be an $\alpha$-extensive category, $X \to Y$ a morphism in $\mathfrak{s}\mathcal{E}$ and $S$ an $\alpha$-small set. Given a square*

![img-43.jpeg](img-43.jpeg)

*for each $s \in S$ such that the induced morphism $\coprod_s Y_s \to Y$ is a weak equivalence, the following are equivalent:*

- (i) *the square above is a homotopy pullback for each $s \in S$,*
- (ii) *the induced morphism $\coprod_s X_s \to X$ is a weak equivalence.*

*Proof.* This follows from a simpler variant of the previous argument, for $\alpha$-small coproducts instead of pushouts. This uses part (i) instead of part (ii) of Lemma 3.18. $\square$

Propositions 10.1 and 10.2 have an immediate counterpart at the $\infty$-categorical level.

**Theorem 10.3.** *Let $\mathcal{E}$ be an $\alpha$-extensive category. The $\infty$-category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ has all $\alpha$-small colimits. These colimits satisfy descent.*

*Proof.* It follows from [Cis20, Proposition 7.5.18] that $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ has finite limits and that finite homotopy limits in $\mathfrak{s}\mathcal{E}$ are sent to limits in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$, the dual also holds for finite (homotopy) colimits. Moreover, one can deduce the same for $\alpha$-coproducts using [Cis20, Proposition 7.7.1 and Theorem 7.5.30]. This, together with Propositions 10.1 and 10.2 immediately implies that pushouts and $\alpha$-coproducts satisfy descent in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$. From there, [Lur09, Proposition 4.4.2.6] shows that the existence of finite colimits and $\alpha$-coproducts implies the existence of all $\alpha$-small colimits in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$. And given that a certain colimit satisfies descent if and only if it is preserved by the contravariant functor from $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ to the $\infty$-category of $\infty$-categories classified by the slice fibration, [Lur09, Proposition 4.4.2.7] shows that this implies that all $\alpha$-small colimits satisfy descent. $\square$

We now move on to consider right properness of the effective model structure, which will be the key to transfer local Cartesian closure from $\mathcal{E}$ to $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$.

**Proposition 10.4.** *Let $\mathcal{E}$ be a countably lextensive category. The effective model structure on $\mathfrak{s}\mathcal{E}$ is right proper.*

*Proof.* This follows from Proposition 7.6 using the argument in [GSS19, Proposition 4.1, Second proof]. $\square$

51

**Theorem 10.5.** *Let $\mathcal{E}$ be a countably lextensive category. If $\mathcal{E}$ is locally Cartesian closed, then the $\infty$-category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ is locally Cartesian closed.*

*Proof.* We first observe that if $\mathcal{E}$ is countably lextensive and locally Cartesian closed, then $\mathfrak{s}\mathcal{E}$ is also locally Cartesian closed. Indeed, if $\mathcal{E}$ is countably lextensive then $\mathfrak{s}\mathcal{E}$ can be realised as the category of internal presheaves for the category object $\Delta \in \mathcal{E}$. Such categories of internal presheaves over an internal category in a locally Cartesian closed categories are always locally Cartesian closed. Indeed, this follows from [Joh02, Theorem A4.2.1 and Proposition B2.3.16], using exactly the same argument as in the proof of [Joh02, Corollary B2.3.17] (which deals with the similar statement for toposes instead of locally Cartesian closed categories). Note that we are applying these results taking the category $\mathbb{D}$ therein to be the canonical self-indexing of the base category $\mathcal{E}$, which satisfies the assumption of having $\mathcal{E}$-indexed products because of [Joh02, Lemma B1.4.7, part (iii)] since $\mathcal{E}$ is locally Cartesian closed.

An arbitrary map in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ can always be represented by a fibration $p \colon X \to Y$ between fibrant objects in $\mathfrak{s}\mathcal{E}$ with $X$ cofibrant. The functor $p^*$ is a left adjoint functor since $\mathfrak{s}\mathcal{E}$ is locally Cartesian closed, it preserves cofibrations by part (i) of Proposition 5.9 and it preserves trivial cofibrations by the Frobenius property of Proposition 7.6. It hence follows from [Cis20, Proposition 7.6.16] that the pullback functor $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})/Y \to \mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})/X$ admits a right adjoint (given by the action of the right adjoint of $p^*$ on fibrant objects).

We conclude this section by combining our results in the case $\mathcal{E}$ is a Grothendieck topos.

**Theorem 10.6.** *Let $\mathcal{E}$ be a Grothendieck topos. Then $\infty$-category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ is locally Cartesian closed and has all small colimits, which satisfy descent.*

For a Grothendieck topos $\mathcal{E}$, the effective model structure on $\mathfrak{s}\mathcal{E}$ is typically not a model topos in the sense of Rezk [Rez10] and $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ is not a higher topos in the sense of Lurie [Lur09]. Indeed, as we will see in Example 11.8, if $\mathcal{E} = \mathsf{Set}^{[1]}$, then the category of 0-truncated objects in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ is neither a Grothendieck topos nor an elementary topos, as it does not have a subobject classifier. The situation is reminiscent of that of Grothendieck toposes whose exact completion is neither a Grothendieck topos nor an elementary topos [Men03].

## 11 A generalised Elmendorf theorem

Elmendorf's theorem [Elm83, Ste16] states that the genuine equivariant model structure on $G$-spaces is equivalent to the projective model structure on presheaves of spaces on the category of orbits of $G$. In this section, we show as Theorem 11.7 that, under the assumption that the category $\mathcal{E}$ is completely lextensive and locally connected (in the sense of Definition 11.1 below), then the effective model category structure on $\mathfrak{s}\mathcal{E}$ models the $\infty$-category of small presheaves of spaces on the full subcategory $\mathcal{E}^{\mathrm{con}}$ of connected objects in $\mathcal{E}$. Note that extension of Elmendorf's theorem beyond the case of group action already appears in the literature (cf. [Cho15, DK84, F87]). The work in [Cho15] is especially close to what we prove in the present section.

**Definition 11.1.** Let $\mathcal{E}$ be a lextensive category.

- An object $X \in \mathcal{E}$ is said to be *connected* if it is not the initial object and whenever $X = A \sqcup B$ then $A = \varnothing$ or $B = \varnothing$.

52

- A lextensive category is said to be *locally connected* if every object is a van Kampen coproduct of connected objects.

The terminology of Definition 11.1 is compatible with the notion of a locally connected Grothendieck topos. For example, the category of sheaves of set over a locally connected topological space is locally connected. The category of presheaves over a category $\mathcal{I}$ is locally connected, its connected objects are called the “orbit” of $I$, i.e., the presheaves whose category of elements is connected, or equivalently whose colimits is a singleton. The coproduct completion of a category with finite limits is also a locally connected category.

Let us now fix a lextensive category $\mathcal{E}$. We denote by $\mathcal{E}^{\text{con}}$ the full subcategory of of $\mathcal{E}$ of connected objects. It is important to note that even if $\mathcal{E}$ is a Grothendieck topos, this category is in general not a small category, as the next example illustrates.

**Example 11.2.** If $\mathcal{E} = \text{Set}^{[1]} = \text{Fam Set}$, then the connected objects of $\mathcal{E}$ are the objects of the form $X \to \ast$ for an arbitrary set $X$. In particular $\mathcal{E}^{\text{con}}$ is equivalent to the category of all sets. More generally, if $\mathcal{C}$ is a category with finite limits, and $\text{Fam } \mathcal{C}$ is its coproduct completion, then $(\text{Fam } \mathcal{C})^{\text{con}} = \mathcal{C}$.

**Lemma 11.3.** *Let $X$ be a connected object in a lextensive category. Then $\text{Hom}_{\text{Set}}(X, -)$ commutes with van Kampen coproducts.*

*Proof.* Given a map $f: X \to \coprod A_i$, then $X = \coprod X_i$ where $X_i = X \times_A A_i$, but as $X$ is connected all the $X_i$ except one are the initial object. As $X$ is itself non-initial, then exactly one of the $X_i$ is non initial and hence $X = X_i$ and the map $X \to \coprod A_i$ factors into $X \to A_i$ for a unique $i$. $\square$

For a possibly large category $\mathcal{D}$, we write $\text{Psh } \mathcal{D}$ for the category of small presheaves on $\mathcal{D}$, that is the category of presheaves on $\mathcal{D}$ that can be written as small colimits of representables. We denote by $\text{sPsh } \mathcal{D}$ the category of small simplicial presheaves, or equivalently simplicial objects in $\text{Psh } \mathcal{D}$. In general, limits of small presheaves can fail to be small, but if we assume that $\mathcal{D}$ has $\alpha$-small limits, then $\text{Psh } \mathcal{D}$ also has $\alpha$-small limits. This is proved in [DL07] as Theorem 4.3 applied to Example 4.1.1.

**Proposition 11.4.** *Let $\mathcal{D}$ be a category with finite limits. Then $\text{sPsh } \mathcal{D}$ carries the projective model structure, in which an arrow $f: X \to Y$ if a fibration, trivial fibration or weak equivalence if and only if for all $d \in \mathcal{D}$, the arrow $f_d: X(d) \to Y(d)$ is one.*

*Proof.* This is proved in [CD09] under the assumption that $\mathcal{D}$ has all limits. However, the proof applies unchanged if we only assume that $\text{sPsh } \mathcal{D}$ has finite limits, as long as we do not require that a model category has all limits, but only finite limits. Indeed the only use of limits in $\mathcal{D}$ in the proof is to show that $\text{Psh } \mathcal{D}$ has all limits. Moreover, [DL07, Theorem 4.3 applied to Example 4.1.1] shows that if the category $\mathcal{D}$ has finite limits then the category $\text{Psh } \mathcal{D}$ of small presheaves on $\mathcal{D}$ also has finite limits. Note that the existence of the corresponding weak factorisation system in $\text{sPsh } \mathcal{D}$ follows from the generalised small object argument with respect to locally small class of arrows exactly as explained in [CD09] $\square$

The claim of Proposition 11.4 follows also from the assumption that $\text{sPsh } \mathcal{D}$ has finite limits, which is a weaker condition than the existence of finite limits in $\mathcal{D}$.

53

**Remark 11.5.** The $\infty$-category associated to the projective model structure on $\mathfrak{sPsh}\mathcal{D}$ is really the $\infty$-category of small presheaves of spaces on $\mathcal{D}$, essentially by the same argument as for small categories.

**Lemma 11.6.** *Given a locally connected countably lextensive category $\mathcal{E}$.*

- (i) *The restricted Yoneda embedding $y: \mathcal{E} \to \mathrm{Psh}(\mathcal{E}^{\mathrm{con}})$ is well-defined, fully faithful and preserves limits and all van Kampen coproducts.*
- (ii) *The restricted Yoneda embedding $y: \mathfrak{s}\mathcal{E} \to \mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ is well-defined, fully faithful and preserves limits, pushouts along a cofibration, tensoring by objects of $\mathcal{E}$ and $\mathfrak{sSet}$ and colimits of sequences of cofibrations.*

*Proof.* For any connected object $X \in \mathcal{E}^{\mathrm{con}}$, $\mathrm{Hom}_{\mathrm{Set}}(X, -)$ preserves coproducts by Lemma 11.3, hence as every object $Y \in E$ is a small van Kampen coproduct of connected objects, its image under the restricted Yoneda embedding is a small coproduct of representables, and hence is a small presheaf. This proves the existence and the preservation of coproducts by the Yoneda embedding. Preservation of limits is immediate. It is fully faithful on connected objects by the Yoneda lemma, and this implies that it is fully faithful in general as morphisms between van Kampen coproducts of connected objects can be explicitly described as maps between their components.

The simplicial version is just the ordinary version applied levelwise in the simplicial direction so all results of part (ii) follow immediately. For the preservation of colimits we use the fact that a functor that preserves countable coproducts preserves pushouts of complemented inclusions and colimits of sequences of complemented inclusions, and all the colimits considered in the lemma are levelwise of this form. $\square$

**Theorem 11.7** (Generalised Elmendorf's theorem). *Let $\mathcal{E}$ a locally connected countably lextensive category.*

- (i) *A map in $\mathfrak{s}\mathcal{E}$ is a cofibration, fibration or weak equivalence if and only if its image by the restricted Yoneda embedding is one for the projective model structure.*
- (ii) *If $\mathcal{E}$ is in addition completely lextensive, then the restricted Yoneda embedding induces an equivalence between the full subcategories of cofibrant objects of $\mathfrak{s}\mathcal{E}$ and $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$. In particular it induces an equivalence of the corresponding $\infty$-categories.*

*Proof.* The (cofibration, trivial fibration) and (trivial cofibration, fibration) weak factorisation systems on $\mathfrak{s}\mathcal{E}$ are cofibrantly generated in the (non-enriched) sense of [CD09] by the classes of arrows $\{i \cdot E \mid i \in I_{\mathfrak{sSet}}, E \in \mathcal{E}\}$ and $\{j \cdot E \mid j \in I_{\mathfrak{sSet}}, E \in \mathcal{E}\}$. As every object in $\mathcal{E}$ is assumed to be a (van Kampen) coproduct of connected objects, one can restrict to $E \in \mathcal{E}^{\mathrm{con}}$. Because of Lemma 11.6, these generators are sent exactly to the generators of the projective model structure of $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$.

It immediately follows that an arrow in $\mathfrak{s}\mathcal{E}$ is a (trivial) fibration if and only if it is one in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ as these classes are characterised by the same lifting property.

Moreover, also because of Lemma 11.6 the restricted Yoneda embedding preserves coproducts and pushouts of the generating cofibrations, transfinite composition of cofibrations and retracts. Thus because of how (trivial) cofibrations are constructed in $\mathfrak{s}\mathcal{E}$ from the small object argument, it follows that their images in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ are projective (trivial) cofibrations. Conversely, an arrow in $\mathfrak{s}\mathcal{E}$ which is a (trivial) cofibration in the projective model structure on $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ has the lifting property against all (trivial) fibrations in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$, but as the restricted Yoneda embedding is

54

fully faithful and preserves (trivial) fibrations, it follows that it also has the lifting property against all (trivial) fibrations in $\mathfrak{s}\mathcal{E}$ and hence is a (trivial) cofibration in $\mathfrak{s}\mathcal{E}$. This proves part (i) for (trivial) cofibrations and (trivial) fibrations, the case of equivalences also follows as an arrow is an equivalence if and only if it can be factored as trivial cofibration followed by a trivial fibration.

For part (ii), we just make one additional observation. If $\mathcal{E}$ is completely lextensive, then any cofibrant object in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ is in the image of the Yoneda embedding. Indeed, the image of $y$ contains the initial object and the generating cofibrations, and is closed under pushout of cofibrations, transfinite composition of cofibrations and retract (because it is closed under finite limits). Therefore, it contains all cofibrant objects. So as $y$ is fully faithful it is an equivalence of categories between the categories of cofibrant objects. $\square$

In short, Theorem 11.7 says that if $\mathcal{E}$ is completely lextensive and locally connected, the effective model category structure on $\mathfrak{s}\mathcal{E}$ of Theorem 9.9 models the category of small presheaves of spaces on the large category $\mathcal{E}^{\mathrm{con}}$. Note that we cannot quite say that the restricted Yoneda embedding is a Quillen equivalence because it does not admit an adjoint in general. However it follows from the theorem that if $\mathcal{E}$ has all colimits, then it is a right Quillen equivalence. Note that a very general Elmendorf's theorem was also proved in [Cho15, Theorem 3.1], which is similar to our version in many aspects. In fact, if we assume that $\mathcal{E}$ is both complete and cocomplete then we can deduce our result from Chorny's theorem.

**Example 11.8.** We take $\mathcal{E}$ to be the category $\mathsf{Set}^{[1]}$ of arrows in $\mathsf{Set}$. It is completely lextensive and locally connected, and its connected objects are the ones of the form $X \rightarrow Y$ where $Y$ is the singleton. Thus the category of connected objects can be identified with the category of sets, it hence follows by Theorem 11.7 that the category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E})$ can be identified with the category of small presheaves of spaces on the category of all sets. This $\infty$-category satisfies descent (all its colimits are van Kampen) and is locally cartesian closed, for example by Theorem 10.5 and Theorem 10.3. But, it is not a (locally) presentable $\infty$-category, so is not an $\infty$-topos in the sense of [Lur09, Chapter 6]. It is also not an elementary $\infty$-topos in the sense of [Shu17] or [Ras18], for example its full subcategory of set-truncated objects is the category of small presheaves of sets on the category of all sets and is not an elementary topos as it does not have a subobject classifier. This category of set-truncated objects is however a pretopos (in the infinitary sense of the term) and is locally cartesian closed.

## 12 Semisimplicial objects and left properness

In this section, we consider the category of semisimplicial objects $\mathfrak{s}_x\mathcal{E}$. While its homotopy theory is overall less well-behaved than its simplicial counterpart we developed so far, it is in some respects simpler. This allows us to derive certain properties of $\mathfrak{s}\mathcal{E}$ that we do not seem to be able to prove otherwise. In particular, we use these results to show that the model structure on $\mathfrak{s}\mathcal{E}$ is left proper (Corollary 12.18) and to establish certain universal property of the $\infty$-category associated with $\mathfrak{s}\mathcal{E}$ in Section 13.

Our development will be mostly parallel to the simplicial one. We will start under the assumption that $\mathcal{E}$ has finite limits and show that the category of Kan complexes in $\mathfrak{s}_x\mathcal{E}$ carries a structure of a fibration category. If $\mathcal{E}$ is countably lextensive, the category $\mathfrak{s}_x\mathcal{E}$ also carries natural notions of cofibrations and trivial cofibrations, but these do not fit into a model structure. (They can be organised into certain weaker structures as discussed below in Remark 12.9.) Nonetheless, we show

55

that they are sufficiently well-behaved for our purposes. Indeed, a particularly simple characterisation of cofibrations (they coincide with levelwise complemented inclusions, see Lemma 12.3) enables certain arguments unavailable in $\mathfrak{s}\mathcal{E}$.

The critical result that is that the homotopy theories of simplicial and semisimplicial objects in $\mathfrak{s}\mathcal{E}$ are equivalent (Theorem 12.6). We will show that under the assumption that $\mathcal{E}$ is either countably complete (Theorem 12.8) or countably lextensive (Theorem 12.17).

We begin by introducing some basic concepts. Since these are largely analogous to the simplicial case, we only treat them briefly, mainly to fix the notation. We write $\Delta_+$ for the subcategory of $\Delta$ consisting of the face operators (i.e., the injective maps) and $\mathfrak{s}_*\mathcal{E} = [\Delta_+^{\mathrm{op}}, \mathcal{E}]$ for the category of semisimplicial objects in $\mathcal{E}$. In particular, $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ is the category of semisimplicial sets. The representable semisimplicial sets are denoted by $\Delta_+[n]$. For any finite semisimplicial set $K$, we define the *evaluation functor* $\mathrm{ev}_K: \mathfrak{s}\mathcal{E} \to \mathcal{E}$ as

$$\mathrm{ev}_K(X) = \int_{[n] \in \Delta_+} X_n^{K_n}.$$

The category $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ carries a non-Cartesian closed symmetric monoidal structure whose tensor is called the *geometric product* and denoted by $\boxtimes$. It is uniquely determined by the property that $\Delta_+[m] \boxtimes \Delta_+[n]$ is the semisimplicial set of non-degenerate simplices in the nerve of the poset $[m] \times [n]$.

The forgetful functor $U: \mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t} \to \mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ has both the left adjoint $L$ and the right adjoint $R$ given by $\mathfrak{K}\mathfrak{n}$ extensions along the inclusion $\Delta_+ \to \Delta$. The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ also has the left or the right adjoint if $\mathcal{E}$ is countably lextensive (or even just finitely cocomplete) or countably complete, respectively. These will be used in the proofs of the two variants of this section's main theorem announced above.

The homotopy theory of semisimplicial sets is well established. Weak homotopy equivalences are defined as semisimplicial maps that become simplicial weak homotopy equivalences upon applying the functor $L$. The category $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ also carries classes of (trivial) fibrations and cofibrations, defined below. These do not form a model structure, but they satisfy certain weaker axioms. E.g., $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ is a weak model category (and even a right semi-model category), see [Hen19, Section 5.5]. For our purposes, Theorem 12.2 below is sufficient.

For a finite semisimplicial set $K$ and $X \in \mathfrak{s}_*\mathcal{E}$ we define the cotensor $K \pitchfork X \in \mathfrak{s}_*\mathcal{E}$ by letting

$$(K \pitchfork X)_n = X(\Delta_+[n] \boxtimes K)$$

and the semisimplicial hom-object

$$\mathrm{Hom}_{\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}}(X, Y)_n = \mathrm{Hom}_{\mathfrak{S}\mathfrak{e}\mathfrak{t}}(X, \Delta_+[n] \pitchfork Y).$$

Exactly as in the simplicial case, this makes $\mathfrak{s}_*\mathcal{E}$ into a $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$-enriched category with respect to the geometric product and $\pitchfork$ becomes the cotensor for this enrichment.

The boundaries $\partial\Delta_+[n]$ and horns $\Lambda_+^k[n]$ are defined analogously to their simplicial counterparts ($\partial\Delta_+[n]$ consists of non-degenerate simplices of $\partial\Delta[n]$ and similarly for $\Lambda_+^k[n]$). This gives rise to the generating sets

$$\begin{aligned} I_{\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}} &= \{\partial\Delta_+[n] \to \Delta_+[n]\} \text{ and } J_{\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}} = \{\Lambda_+^k[n] \to \Delta_+[n]\} \text{ in } \mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t} \\ \text{ and } I_{\mathfrak{s}_*\mathcal{E}} &= \{\underline{\partial\Delta_+[n]} \to \underline{\Delta_+[n]}\} \text{ and } J_{\mathfrak{s}_*\mathcal{E}} = \{\Lambda_+^k[n] \to \underline{\Delta_+[n]}\} \text{ in } \mathfrak{s}_*\mathcal{E}. \end{aligned}$$

Then a morphism $X \to Y$ in $\mathfrak{s}\mathcal{E}$ is a *fibration* if the pullback evaluation

$$X(\Delta_+[n]) \to X(\Lambda_+^k[n]) \times_{Y(\Lambda_+^k[n])} Y(\Delta_+[n])$$

56

has a section for all horn inclusions $\Lambda^L_+[n] \to \Delta_+[n]$ in $J_{\mathfrak{s},\text{Set}}$ and a *trivial fibration* if

$$X(\Delta_+[n]) \to X(\partial\Delta_+[n]) \times_{Y(\partial\Delta_+[n])} Y(\Delta_+[n])$$

has a section for all boundary inclusions $\partial\Delta_+[n] \to \Delta_+[n]$ in $I_{\mathfrak{s},\text{Set}}$. Similarly, *cofibrations* and *trivial cofibrations* are defined as $I_{\mathfrak{s},\mathcal{E}}$-cofibrations and $J_{\mathfrak{s},\mathcal{E}}$-cofibrations in the sense of Definition 3.2. Note that fibrations and trivial fibrations defined above coincide with $J_{\mathfrak{s},\mathcal{E}}$-fibrations and $I_{\mathfrak{s},\mathcal{E}}$-fibrations by the same argument as in Proposition 4.1.

**Lemma 12.1.** *If $\mathcal{E}$ is countably lextensive, then $\mathfrak{s},\mathcal{E}$ carries two enriched weak factorisation systems consisting of:*

- *cofibrations and trivial fibrations,*
- *trivial cofibrations and fibrations.*

*Proof.* This follows from Theorem 3.14 with the assumptions verified exactly as in the proof of Theorem 4.2. $\square$

**Theorem 12.2.** *The category of fibrant semisimplicial sets with weak homotopy equivalences as defined above (i.e., created by the free functor $L: \mathfrak{s},\text{Set} \to \mathfrak{s}\text{Set}$) is a fibration category.*

*Proof sketch.* The claim can be deduced from the existence of the fibration category of fibrant simplicial sets in [GSS19, Theorem 2.2.2]. The proof is analogous to the proof of [GSS19, Theorem 2.2.2] itself and depends on the following fact. If $f: X \to Z$ is a map between simplicial sets and $Uf$ factors (in semisimplicial sets) as a composite of a cofibration $i: UX \to B$ and a fibration $p: B \to UZ$, then $f$ factors as a composite of $i': X \to Y$ and $p': Y \to Z$ such that $i = Ui'$ and $p = Up'$. (Note that, in particular, $B = UY$, $i$ is a cofibration and $p$ is a fibration.) This holds by [Ste17, Theorem 2.1 and Addendum 2.2]. It will also rely the fact that $U$ preserves and reflects weak equivalences by [Hen19, Lemma 2.2.1].

Compared to the proof of [GSS19, Theorem 2.2.2], the present argument requires only two modifications. First, to construct a path object on a fibrant semisimplicial set $K$, we first apply the fact above (with $X = \emptyset$, $Y = K$ and $Z = 1$) to obtain a simplicial Kan complex $A$ such that $UA = K$. Then we obtain a path object on $K$ by applying $U$ to a path object on $A$. Second, we observe that the facts above imply that a fibration in $\mathfrak{s},\text{Set}$ is acyclic if and only if it is trivial (by reducing it to the same statement in $\mathfrak{s}\text{Set}$). Thus acyclic fibrations are stable under pullback. $\square$

**Lemma 12.3.** *A map $f: X \to Y$ in $\mathfrak{s},\mathcal{E}$ is a cofibration if and only if for all $n$ the map $X_n \to Y_n$ is a complemented inclusion. In particular, every object of $\mathfrak{s},\mathcal{E}$ is cofibrant.*

*Proof.* The claim follows already from the semisimplicial version of Proposition 4.3 since latching objects are empty, which is simpler to prove than Proposition 4.3 due to absence of degeneracy operators. $\square$

**Corollary 12.4.** *If $\mathcal{E}$ has finite limits, then every trivial fibration in $\mathfrak{s},\mathcal{E}$ admits a section.*

$^6$This is non-constructive, because of the use of [Ste17]. An alternative argument which works constructively can be found in [Hen19, Theorem 5.5.6]. It shows that semisimplicial set have a weak model structure analogous to the Kan–Quillen model structure. Given that even constructively all semisimplicial sets are cofibrant this is enough to obtain that the full subcategory of fibrant objects is a fibration category.

57

*Proof.* First, note that if $\mathcal{E}$ is countably lextensive, this follows from Lemmas 12.1 and 12.3. If $\mathcal{E}$ is merely finitely complete, then $\mathsf{Fam}_{\omega_1}\mathcal{E}$ is countably lextensive and the conclusion holds since the functor $\mathsf{s}_\varepsilon\mathcal{E} \to \mathsf{s}_\varepsilon\mathsf{Fam}_{\omega_1}\mathcal{E}$ is fully faithful, cf. the explicit construction of $\mathsf{Fam}_\alpha$ in Example 2.5. $\square$

A morphism $X \to Y$ between Kan complexes in $\mathsf{s}_\varepsilon\mathcal{E}$ is a *pointwise weak equivalence* if

$$\operatorname{Hom}_{\mathsf{s}_\varepsilon\operatorname{Set}}(E, X) \to \operatorname{Hom}_{\mathsf{s}_\varepsilon\operatorname{Set}}(E, Y)$$

is a weak equivalence in $\mathsf{s}_\varepsilon\operatorname{Set}$ for all $E \in \mathcal{E}$.

**Theorem 12.5.** *Pointwise weak equivalences, fibrations and trivial fibrations equip the category of Kan complexes in $\mathsf{s}_\varepsilon\mathcal{E}$ with the structure of a fibration category.*

*Proof.* The proof is entirely analogous to the proof of Theorem 1.7 except for the construction of path objects. A path object on $X \in \mathsf{s}_\varepsilon\mathcal{E}$ can be constructed as $X \to \Delta_+[1] \cap X \to X \times X$ as before. However, there is no semisimplicial map $\Delta_+[1] \to \Delta_+[0]$ (i.e., $\Delta_+[0]$ does not admit a cylinder object) and so the morphism $X \to \Delta_+[1] \cap X$ cannot be induced by functoriality of cotensors. The problem can be fixed by constructing a “weak cylinder object” on $\Delta_+[0]$ in the sense of [Hen18].

There is a unique map $\Lambda_+^2[2] \to \Delta_+[1]$. It sends both 1-simplices to the unique 1-simplex of $\Delta_+[1]$. We define $D$ to be the pushout of this map along the trivial cofibration $\Lambda_+^2[2] \to \Delta_+[2]$:

![img-44.jpeg](img-44.jpeg)

Thus $D$ has two 0-simplices $b$ and $x$, two 1-simplices $f: b \to x$ and $e: b \to b$ and a unique 2-simplex that witnesses that $f \circ e \sim e$. Informally speaking, this forces $e$ to behave as an “identity cell” of $b$. More precisely, we obtain a diagram

![img-45.jpeg](img-45.jpeg)

which upon cotensoring into $X \in \mathsf{s}_\varepsilon\mathcal{E}$ yields

![img-46.jpeg](img-46.jpeg)

When $X$ is a Kan complex, the right vertical morphism is a trivial fibration and hence it has a section by Corollary 12.4. We obtain the required factorisation by composing $D \cap X \xrightarrow{\sim} \Delta_+[1] \cap X$ with such section. This last map is a pointwise weak equivalence, because applying $\operatorname{Hom}_{\mathsf{s}_\varepsilon\operatorname{Set}}(E, -)$ to it gives, up to isomorphism, the map

$$D \cap \operatorname{Hom}_{\mathsf{s}_\varepsilon\operatorname{Set}}(E, X) \to \Delta_+[1] \cap \operatorname{Hom}_{\mathsf{s}_\varepsilon\operatorname{Set}}(E, X)$$

58

which is a semisimplicial weak equivalence for each fibrant semisimplicial set $\operatorname{Hom}_{\mathfrak{s},\operatorname{Set}}(E, X)$, for example because both evaluation maps to $\operatorname{Hom}_{\mathfrak{s},\operatorname{Set}}(E, X)$ are trivial fibrations as the weak factorisation systems on $\mathfrak{s},\operatorname{Set}$ are compatible to the monoidal structure on $\mathfrak{s},\operatorname{Set}$ (see for eg. Theorem 5.5.6.(iii) of [Hen19]).

The following theorem is the main result of this section. It is valid under two separate sets of assumptions which require two independent proofs. Thus we will consider them separately as Theorem 12.8 and Theorem 12.17.

**Theorem 12.6.** *If $\mathcal{E}$ is either countably extensive or countably complete, then the forgetful functor $\mathfrak{s}\mathcal{E} \rightarrow \mathfrak{s},\mathcal{E}$ induces an equivalence of fibration categories between the fibration categories of Theorems 1.7 and 12.5.*

We start with the case of a category $\mathcal{E}$ with countable limits, this is the proof that relies on the adjunction $U \dashv R$.

**Proposition 12.7.** *If $\mathcal{E}$ is countably complete, then the forgetful functor $U: \mathfrak{s}\mathcal{E} \rightarrow \mathfrak{s},\mathcal{E}$ has a right adjoint $R$. Moreover, for every object $E \in \mathcal{E}$, evaluation at $E$ commutes with this right adjoint, i.e., the square*

![img-47.jpeg](img-47.jpeg)

*commutes (up to canonical isomorphism).*

*Proof.* We claim that for any $X \in \mathfrak{s},\mathcal{E}$, seen as a functor $\Delta_{+}^{\mathrm{op}} \rightarrow E$, its right Kan extension along $\Delta_{+}^{\mathrm{op}} \rightarrow \Delta^{\mathrm{op}}$ exists and is a pointwise right Kan extension. Indeed, the pointwise right Kan extension computed at $[n] \in \Delta$ should be

$$RV = \lim_{[m] \rightarrow [n] \in E} V([m])$$

where $E$ is the comma category of $[m] \in \Delta_{+}^{\mathrm{op}}$ endowed with a map $[m] \rightarrow [n]$ in $\Delta$. This category is countable, so as $\mathcal{E}$ is countably complete, the limit exists, and hence the pointwise right Kan extension exists. By definition taking this right Kan extension is right adjoint to the forgetful functor $\mathfrak{s}\mathcal{E} \rightarrow \mathfrak{s},\mathcal{E}$, so this proves the existence of the right adjoint. The commutation of the square in the proposition is because the evaluation functor preserves limits, and hence preserves this pointwise right Kan extension as well. $\square$

**Theorem 12.8.** *If $\mathcal{E}$ is countably complete, then both the forgetful functor and its right adjoint*

$$U: \mathfrak{s}\mathcal{E} \leftrightarrows \mathfrak{s},\mathcal{E}: R$$

*restrict to equivalences of fibration categories between $\mathfrak{s}\mathcal{E}_{\mathrm{fib}}$ and $\mathfrak{s},\mathcal{E}_{\mathrm{fib}}$.*

*Proof.* The theorem is valid for simplicial and semisimplicial sets, i.e., in the case of $\mathcal{E} = \operatorname{Set}$. As both $U$ and $R$ commute with evaluation at $E \in \mathcal{E}$ and weak equivalences and fibrations are detected by these evaluations, it follows that:

- $U$ and $R$ preserve fibrant objects and are morphisms of fibrations categories;

59

- the unit and counit of the adjunctions are weak equivalences on fibrant objects.

We now move to the case of a countably lextensive category $\mathcal{E}$. Despite the fact that the theorem concerns only the fibrant objects of $\mathfrak{s}_e\mathcal{E}$, the proof will depend on the homotopy theory of all, not necessarily fibrant, semisimplicial objects in $\mathcal{E}$. We define a general morphism of $\mathfrak{s}_e\mathcal{E}$ to be a weak equivalence if it has a fibrant replacement (as constructed from factorisations of Lemma 12.1) that is a pointwise weak equivalence in $\mathfrak{s}_e\mathcal{E}_{\mathrm{fib}}$. This is analogous to the characterisation of weak equivalences between simplicial objects in the model structure of Theorem 9.9. The weak equivalences, fibrations and cofibrations defined in this section do not form a model structure on $\mathfrak{s}_e\mathcal{E}$, but we can still prove that they are sufficiently well-behaved for our purposes. For example, the definition of weak equivalences immediately implies that trivial cofibrations are weak equivalences. On the other hand, not all trivial fibrations are weak equivalences.

**Remark 12.9.** If $\mathcal{E}$ is countably lextensive then $\mathfrak{s}_e\mathcal{E}$ is a weak model category in the sense of [Hen18] with weak equivalences, fibrations and cofibrations as defined above. This can be derived from (the dual of) [Hen18, Proposition 2.3.3] and properties of the classes established in this section. In fact, as every object of $\mathfrak{s}_e\mathcal{E}$ is cofibrant, this is even a right semi-model category, as long as we use the definition of a semi-model category in [Fre09] and not that in [Spi01] (see [Hen20, Section 3] for the explanation of differences between the two definitions). Our discussion of homotopy theory of semisimplicial objects can be phrased both in terms of this weak model structure or right semi-model structure. However, we prefer to provide more elementary arguments to make this section more self-contained.

**Proposition 12.10.** *If $\mathcal{E}$ has finite coproducts, then the forgetful functor $\mathfrak{s}\mathcal{E} \to \mathfrak{s}_e\mathcal{E}$ has a left adjoint. It is given by*

$$(LX)_n = \coprod_{[n] \to [m]} X_m$$

*where the coproduct is over all degeneracy operators $[n] \to [m]$ in $\Delta$.*

*Proof.* The functor $L$ is the left Kan extension along $\Delta_+ \to \Delta$. If it can be computed pointwise, it is given by the formula

$$(LX)_n = \underset{[n] \to [m]}{\operatorname{colim}} X_m$$

where the colimit is taken over the comma category $[n] \downarrow \Delta_+^{\mathrm{op}}$. (Its objects are arbitrary simplicial operators $[n] \to [m]$, but its morphisms are just the face operators.) It follows from the existence of the degeneracy/face unique factorisation system in $\Delta$ that the discrete category of degeneracy operators $[n] \to [m]$ is cofinal in this category. Hence the colimit above can be rewritten as the coproduct in the statement of the proposition. Thus if $\mathcal{E}$ has finite coproducts, this colimit exists which concludes the proof.

**Lemma 12.11.** *The free functor $L: \mathfrak{s}_e\mathcal{E} \to \mathfrak{s}\mathcal{E}$ preserves cofibrations and trivial cofibrations.*

*Proof.* It can be checked easily that the natural transformation from the initial functor to $L$ satisfies the assumptions of Lemma 3.20, so it is enough to verify that $L$ sends the generating cofibrations and trivial cofibrations to cofibrations and trivial cofibrations, respectively. These generators are of the form $\underline{\Lambda}_+[n] \mapsto \underline{\Delta}_+[n]$ or $\underline{\partial\Delta}_+[n] \mapsto \underline{\Delta}_+[n]$ the image by $L$ is computed as in Set, thus giving $\underline{\Lambda}^k[n] \mapsto \underline{\Delta[n]}$ or $\underline{\partial\Delta[n]} \mapsto \underline{\Delta[n]}$, i.e., the generating cofibrations and trivial cofibrations in $\mathfrak{s}\mathcal{E}$.

60

**Lemma 12.12.** *The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ preserves cofibrations and trivial cofibrations.*

*Proof.* The forgetful functor preserves all colimits that exist so it is enough to show that the generating (trivial) cofibrations of $\mathfrak{s}\mathcal{E}$ are sent to (trivial) cofibrations. The case of cofibrations follows from Theorem 4.6 and Lemma 12.3. For trivial cofibrations, note that if $X \in \mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}$, then $\underline{U}\underline{X} = U\underline{X}$ (the first $U$ is the forgetful functor $\mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t} \to \mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$, the second one is $\mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$). Thus it is enough to show that $U\Lambda^n[k] \to U\Delta[n]$ is a trivial cofibration in $\mathfrak{s}_*\mathcal{E}$ for all $0 \leq k \leq n$. For this it is sufficient to show that $\Lambda^n[k] \to U\Delta[n]$ is a trivial cofibration in $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ which was proven in [Hen18, Corollary 5.5.15 (ii)]. $\square$

Note that the forgetful functor $U$ preserves trivial fibrations, but trivial fibrations in $\mathfrak{s}_*\mathcal{E}$ are not necessarily weak equivalences. Nonetheless, the following statement is valid.

**Lemma 12.13.** *The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ sends trivial fibrations to weak equivalences.*

*Proof.* This follows by the same argument as the second part of [Hen19, Lemma 2.2.1]. $\square$

**Lemma 12.14.** *For each $X \in \mathfrak{s}_*\mathcal{E}$, the unit $X \to ULX$ is a trivial cofibration.*

*Proof.* The composite $UL$ preserves all the relevant colimits, so it is enough to check that for each generating cofibration $\underline{\partial\Delta_*[n]} \to \underline{\Delta_*[n]}$, the map

$$UL(\underline{\partial\Delta_*[n]}) \sqcup_{\underline{\partial\Delta_*[n]}} \underline{\Delta_*[n]} \to UL\underline{\Delta_*[n]}$$

is a trivial cofibration. It then follows from Lemma 3.20 that the same holds for all cofibrations and the case of $\varnothing \to X$ concludes the proof. Thus it suffices to prove the statement in the case of semisimplicial sets which is [Hen18, Proposition 5.5.14]. $\square$

**Proposition 12.15.** *The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ preserves and reflects weak equivalences.*

*Proof.* The conclusion is valid for $\mathfrak{s}\mathcal{E} = \mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}$ by [Hen19, Lemma 2.2.1] and thus it holds for morphisms between fibrant objects. Indeed, $\operatorname{Hom}_{\mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}}(E, UX) = U\operatorname{Hom}_{\mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}}(E, X)$ and weak equivalences between fibrant objects in both $\mathfrak{s}\mathcal{E}$ and $\mathfrak{s}_*\mathcal{E}$ are detected by pointwise evaluation.

For a general morphism $X \to Y$, we consider its fibrant replacement as constructed in the small object argument. Since $U$ preserves trivial cofibrations (by Lemma 12.12) and fibrations, it follows that it preserves such fibrant replacements. Thus the conclusion follows from the special case of morphisms between fibrant objects. $\square$

**Corollary 12.16.** *For each $X \in \mathfrak{s}\mathcal{E}$, the counit $LUX \to X$ is a weak equivalence.*

*Proof.* This follows from the triangle identities using Lemma 12.14 and Proposition 12.15. $\square$

**Theorem 12.17.** *When $\mathcal{E}$ is countably lextensive, the functor $U: \mathfrak{s}\mathcal{E}_{\text{fib}} \to \mathfrak{s}_*\mathcal{E}_{\text{fib}}$ is an equivalence of fibration categories.*

*Proof.* Consider the functor $L': \mathfrak{s}_*\mathcal{E}_{\text{fib}} \to \mathfrak{s}\mathcal{E}_{\text{fib}}$ obtained by composing $L$ with a chosen fibrant replacement functor in $\mathfrak{s}\mathcal{E}$. Such fibrant replacement along with the unit of the adjunction $L \dashv U$ induce a natural transformation $\operatorname{id}_{\mathfrak{s}_*\mathcal{E}_{\text{fib}}} \to UL'$ which is a weak equivalence by Lemma 12.14 and Proposition 12.15. Similarly, using the counit we obtain two natural transformations $L'UX \leftarrow LUX \to X$ for $X \in \mathfrak{s}\mathcal{E}$. They are weak equivalences by definition and by Corollary 12.16, but $LU$ is not an endofunctor of $\mathfrak{s}\mathcal{E}_{\text{fib}}$, just of $\mathfrak{s}\mathcal{E}$. However, we can apply a functorial factorisation to

61

the morphism $LUX \to L'UX \times X$ to obtain a weak equivalence $LUX \xrightarrow{\sim} TX$ and a fibration $TX \to L'UX \times X$. Then $T$ is an endofunctor of $\mathfrak{s}\mathcal{E}_{\mathrm{fib}}$ and we have two natural weak equivalences $L'U \leftarrow T \to \mathrm{id}_{\mathfrak{s}\mathcal{E}_{\mathrm{fib}}}$ as required.

**Corollary 12.18.** *Let $\mathcal{E}$ be a countably lextensive category. Then the effective model structure on $\mathfrak{s}\mathcal{E}$ is left proper.*

*Proof.* This follows by the combination of the following facts. First, the functor $LU: \mathfrak{s}\mathcal{E} \to \mathfrak{s}\mathcal{E}$ preserves colimits; secondly, $LU$ preserves cofibrations by Lemmas 12.11 and 12.13; thirdly, $LU$ takes values in cofibrant objects by Lemmas 12.3 and 12.11; and, finally, the counit $LUX \to X$ is a weak equivalence by Corollary 12.16.

## 13 The $\infty$-category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$.

Section 11 provides a description of the $\infty$-category $\mathrm{Ho}_{\infty}\mathfrak{s}\mathcal{E}$ presented by the effective model structure on $\mathfrak{s}\mathcal{E}$ when $\mathcal{E}$ is completely lextensive and locally connected. The goal of this section is to give an alternative characterisation of this $\infty$-category under fewer assumptions on $\mathcal{E}$. As shown in Section 1, if $\mathcal{E}$ is only a category with finite limits, we already have a fibration category structure on $\mathfrak{s}\mathcal{E}_{\mathrm{fib}}$, which, in the case where $\mathcal{E}$ is countably lextensive corresponds to the category of fibrant objects of the effective model structure hence models the same $\infty$-category. We will consider the more general problem of describing the $\infty$-category $\mathrm{Ho}_{\infty}\mathfrak{s}\mathcal{E}_{\mathrm{fib}}$ in this case.

We do not know such description for a general category $\mathcal{E}$ with finite limits, but we will present an answer that applies when $\mathcal{E}$ is either countably complete or countably lextensive. More precisely, we will give a description of the $\infty$-category $\mathrm{Ho}_{\infty}\mathfrak{s}_{\varepsilon}\mathcal{E}_{\mathrm{fib}}$, which we showed in Section 12 is equivalent to $\mathrm{Ho}_{\infty}\mathfrak{s}\mathcal{E}_{\mathrm{fib}}$ when $\mathcal{E}$ is either countably lextensive or countably complete.

**Theorem 13.1.** *Let $\mathcal{E}$ be a category that is either countably complete or countably lextensive. Then, evaluations at all $E \in \mathcal{E}$ induce a fully faithful embedding of $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ into the category of presheaves of spaces over $\mathcal{E}$. More precisely, $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ is equivalent to the full subcategory of presheaves of spaces over $\mathcal{E}$ that are homotopy colimits (geometric realisations) of Kan complexes in $\mathcal{E}$.*

This is closely related to the exact completion (or ex/lex completion) of $\mathcal{E}$. In general, the exact completion (see, e.g., [CV98]) of a category $\mathcal{E}$ with finite limits can be described as the full subcategory of $\mathrm{Psh}\mathcal{E}$ of objects that can be written as colimits of "setoids objects" in $\mathcal{E}$, i.e., as coequalisers of "proof-relevant equivalence relations", that is diagrams $R \Rightarrow X$ in $\mathcal{E}$, such that the image of the map

$$\mathrm{Hom}_{\mathrm{Set}}(E, R) \to \mathrm{Hom}_{\mathrm{Set}}(E, X) \times \mathrm{Hom}_{\mathrm{Set}}(E, X)$$

is an equivalence relation on $\mathrm{Hom}_{\mathrm{Set}}(E, X)$ for each $E \in \mathcal{E}$. The term "proof-relevant" refers to the fact that we do not assume that $R \to X \times X$ is a monomorphism, or equivalently that $\mathrm{Hom}_{\mathrm{Set}}(E, R)$ is a subset of $\mathrm{Hom}_{\mathrm{Set}}(E, X) \times \mathrm{Hom}_{\mathrm{Set}}(E, X)$. The fact that $R \to X \times X$ is a proof-relevant equivalence relation can be encoded as a structure consisting of morphisms in $\mathcal{E}$ witnessing transitivity $(R \times_X R \to R)$, symmetry $(R \to R)$ and reflexivity $(X \to R)$. Proposition 1.4 can be seen as a higher categorical version of this observation, i.e., Kan simplicial objects are a higher categorical generalisation of proof-relevant equivalence relations. In fact, it is easy to deduce from the theorem above that the full subcategory of set-truncated objects in $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ is equivalent to the ex/lex completion of $\mathcal{E}$.

62

However, it does not seem accurate to think of $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ as the $\infty$-categorical version of the ex/lex completion. Let us say that an $\infty$-category is exact if it has finite limits and quotients of groupoid objects exist and are van Kampen colimits. Lurie has shown that this condition together with complete lextensivity and local presentability characterises $\infty$-toposes [Lur09]. We can then define the ex/lex completion of an $\infty$-category $\mathcal{C}$ with finite limits in the usual way: it is an exact $\infty$-category $\mathcal{C}^{\mathrm{ex/lex}}$ with a functor $\mathcal{C} \rightarrow \mathcal{C}^{\mathrm{ex/lex}}$ such that any finite limit preserving functor to an exact $\infty$-category $\mathcal{C} \rightarrow \mathcal{D}$ extends essentially uniquely to an exact functor $\mathcal{C}^{\mathrm{ex/lex}} \rightarrow \mathcal{D}$. We conjecture that the effective model structure is related to this ex/lex completion operation in the following way:

**Conjecture 13.2.** *Let $\mathcal{E}$ be a countably lextensive category or countably complete category. The ex/lex completion of the $\infty$-category associated to $\mathcal{E}$ is equivalent to the full subcategory of $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ on objects that are $n$-truncated for some $n$.*

More generally, we believe that this holds for any finitely complete category $\mathcal{E}$ when $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ is replaced with $\mathrm{Ho}_{\infty}(\mathfrak{s}_s\mathcal{E}_{\mathrm{fib}})$.

The general idea of the proof of Theorem 13.1 is that the category $\mathsf{Fam}\,\mathcal{E}$ of families of objects of $\mathcal{E}$ is always a completely lextensive locally connected category, such that $\mathcal{E}$ can be identified with its category of connected objects. Hence, we can apply Theorem 11.7 to it and show that

$$\mathrm{Ho}_{\infty}(\mathfrak{s}\mathsf{Fam}\,\mathcal{E}) \simeq \mathrm{Ho}_{\infty}\,\mathfrak{s}\mathsf{Psh}\,\mathcal{E}$$

The right hand side is a model for the $\infty$-category of small presheaves of spaces on $\mathcal{E}$ (in the $\infty$-categorical sense). We always have a fully faithful embedding $\mathfrak{s}\mathcal{E} \rightarrow \mathfrak{s}\mathsf{Fam}\,\mathcal{E}$ which identifies $\mathfrak{s}\mathcal{E}$ with the full subcategory of levelwise connected simplicial objects. Moreover, a map is a fibration or a weak equivalence (between fibrant objects) in $\mathfrak{s}\mathcal{E}$ if and only if its image in $\mathfrak{s}\mathsf{Fam}\,\mathcal{E}$ is one, so this embedding also restricts to a morphism of fibration categories.

Our goal is to show that (under the assumptions of Theorem 13.1) this also induces a fully faithful embedding on the level of the $\infty$-categories. Unfortunately, we are able to give a proof of this only when we consider instead the semisimplicial version of this embedding $\mathfrak{s}_s\mathcal{E} \rightarrow \mathfrak{s}_s\mathsf{Fam}\,\mathcal{E}$. But as $\mathsf{Fam}\,\mathcal{E}$ is always countably lextensive we have an equivalence of fibration categories $\mathfrak{s}\mathsf{Fam}\,\mathcal{E} \simeq \mathfrak{s}_s\mathsf{Fam}\,\mathcal{E}$ by Theorem 12.17, and as soon as $\mathcal{E}$ is countably complete or countably lextensive we have an equivalence $\mathrm{Ho}_{\infty}(\mathfrak{s}_s\mathcal{E}_{\mathrm{fib}}) \simeq \mathrm{Ho}_{\infty}(\mathfrak{s}\mathcal{E}_{\mathrm{fib}})$ by Theorem 12.6. So we need to show that $\mathfrak{s}_s\mathcal{E} \rightarrow \mathfrak{s}_s\mathsf{Fam}\,\mathcal{E}$ induces a fully faithful functor between the corresponding $\infty$-categories. Because of the following lemma, it is enough to prove that it is fully faithful at the level of the homotopy categories.

**Lemma 13.3.** *A finite limit preserving functor between two $\infty$-categories which is an equivalence (resp. fully faithful) on the homotopy categories is an equivalence (resp. fully faithful).*

*Proof.* This is shown for the case of equivalences in [Cis20, Theorem 7.6.10]. The case of fully faithful functors can be deduced from the case of equivalences. Let $f: \mathcal{X} \rightarrow \mathcal{Y}$ be a finite limit preserving functor which is fully faithful on the homotopy category and let $\mathcal{Y}'$ denote its essential image. Then $\mathcal{Y}'$ contains the terminal object since $f$ preserves finite limits. Similarly, $\mathcal{Y}'$ is closed under pullbacks. Indeed, since $f$ is fully faithful on the homotopy categories, any cospan in $\mathcal{Y}'$ can be lifted to a cospan in $\mathcal{X}$. Its pullback exists in $\mathcal{X}$ and is preserved by $f$. It follows that $f$ induces a finite limit preserving functor $\mathcal{X} \rightarrow \mathcal{Y}'$ which is fully faithful and essentially surjective on the homotopy categories, so it is an equivalence, and hence by the result above, $f$ induces an equivalence between $\mathcal{X}$ and $\mathcal{Y}'$, i.e., it is fully faithful. $\square$

63

**Theorem 13.4.** *For any category $\mathcal{E}$ with finite limits, the functor $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}_{\mathrm{fib}} \to (\mathfrak{s}_{\mathfrak{c}}\mathsf{Fam}\mathcal{E})_{\mathrm{fib}}$ is fully faithful on the homotopy categories.*

*Proof.* The homotopy category of $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}_{\mathrm{fib}}$ is the quotient by the homotopy relation defined via maps $X \to \Delta_{+}[1] \pitchfork Y$. This follows since all semisimplicial objects are cofibrant and $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}_{\mathrm{fib}}$ is a path category in the sense of [BM18a]. The functor $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}_{\mathrm{fib}} \to (\mathfrak{s}_{\mathfrak{c}}\mathsf{Fam}\mathcal{E})_{\mathrm{fib}}$ preserves finite limits and hence it preserves cotensors by $\Delta_{+}[1]$. Thus morphisms in $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}_{\mathrm{fib}}$ are homotopic in $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}_{\mathrm{fib}}$ if and only if they are homotopic in $\mathfrak{s}_{\mathfrak{c}}\mathsf{Fam}\mathcal{E}_{\mathrm{fib}}$. $\square$

**Remark 13.5.** The crucial difference between semisimplicial and simplicial settings is that every semisimplicial object in $\mathfrak{s}_{\mathfrak{c}}\mathcal{E}$ is cofibrant in $\mathfrak{s}_{\mathfrak{c}}\mathsf{Fam}\mathcal{E}$. However, a non-constant simplicial object in $\mathfrak{s}\mathcal{E}$ is levelwise connected in $\mathfrak{s}\mathsf{Fam}\mathcal{E}$ and thus not cofibrant by Theorem 4.6.

We are now ready to prove Theorem 13.1.

*Proof of Theorem 13.1.* We always have a diagram of functors:

![img-48.jpeg](img-48.jpeg)

Theorem 12.17 shows that the bottom horizontal functor is always an equivalence of the homotopy categories as $\mathsf{Fam}\mathcal{C}$ is always a completely lextensive category. The top horizontal map is also an equivalence on the homotopy categories by Theorem 12.6 since $\mathcal{E}$ is countably lextensive or countably complete. Finally, we have shown in Theorem 13.4 that the right vertical functor is fully faithful on the homotopy categories. It follows that the left vertical functor is also fully faithful on the homotopy categories, and hence by Lemma 13.3 induces a fully faithful embedding of $\infty$-categories $\mathfrak{s}\mathcal{E}_{\mathrm{fib}} \to (\mathfrak{s}\mathsf{Fam}\mathcal{E})_{\mathrm{fib}}$.

Now, $\mathsf{Fam}\mathcal{E}$ is a locally connected completely lextensive category, and $\mathcal{E}$ is its category of connected objects. Hence, by Theorem 11.7, the $\infty$-category $\mathrm{Ho}_{\infty}(\mathfrak{s}\mathsf{Fam}\mathcal{E})_{\mathrm{fib}}$ is equivalent to the category of presheaves of spaces over $\mathcal{E}$, which proves the first half of the theorem.

For the description of the essential image we simply investigate the precise nature of the embedding constructed above. If $X \in \mathfrak{s}\mathcal{E}_{\mathrm{fib}}$ then its image in $(\mathfrak{s}\mathsf{Fam}\mathcal{E})_{\mathrm{fib}}$ is also fibrant, and the objects corresponding to $E \in \mathcal{E}$ are cofibrant, so, as this is a simplicial model category, the Hom space in the corresponding $\infty$-category between them is simply $\mathrm{Hom}_{\mathfrak{s}\mathrm{Set}}(E, X)$. Hence $X$ is sent to the presheaf of spaces $E \mapsto \mathrm{Hom}_{\mathfrak{s}\mathrm{Set}}(E, X)$. Note that as colimits in presheaf categories are computed levelwise and the colimit of a simplicial set in the $\infty$-category of spaces is the spaces represented by this simplicial sets, this can equivalently be expressed as the fact that $X$ is sent to its geometric realisation in the presheaf category. $\square$

## Appendix A Remarks on constructivity

While the present paper has been written within ZFC for simplicity, many of our results and proofs are constructive, i.e., do not rely on the law of excluded middle or the axiom of choice, subject to some clarifications, which we will discuss briefly here.

64

First of all, in the constructive reading of the paper, a finite set means a finite cardinal, or a finite decidable set, i.e., a set equipped with a bijection with $\{1, \ldots, n\}$, for some $n \in \mathbb{N}$. A countable set is a set which is equipped with a bijection with either $\{1, \ldots, n\}$ or $\mathbb{N}$. With this definition, a countable coproduct of countable sets is countable.

Secondly, we restrict ourselves to consider finitely lextensive, countably lextensive and completely lextensive categories. Here, by a finitely lextensive category we mean a category with a strict initial object and van Kampen binary coproducts and by a countably lextensive category we mean a finitely lextensive category that in addition has $\mathbb{N}$-indexed van Kampen coproducts. With this definition, the category of countable sets is countably lextensive. Without these changes, we would run into problems as $\omega_1$ is not a regular cardinal in ZF and the axiom of countable choice is needed to show that a countable union of countable set is countable, and therefore Definition 2.4 would be problematic, as we could not show that the category of countable sets is countably lextensive.

Finally, one should assume the convention that every time we discuss existence of an object, this involves explicit structure, rather than a mere property. For example, when we say that a map $f$ has the left lifting property against $g$, we mean that $f$ comes equipped with a function that associates a solution to each lifting problem.

We make no claim on whether it is possible to make the results in Section 11 and Section 13 constructive. Indeed, both of these sections involve $\infty$-categories, for which a constructive theory has not been developed yet. Also, Lemma 11.3 is non-constructive: in a constructive setting, its conclusion should be taken as the definition of a connected object. Finally, Section 11 relies on the existence of the projective model structure on the category of small presheaves on a large category, which is not known to exist constructively.

## References

[AW09] S. Awodey and M. Warren, Homotopy-theoretic models of identity types, Math. Proc. Camb. Phil. Soc. 146 (2009), no. 1, 45-55.

[Bar10] C. Barwick, On left and right model categories and left and right Bousfield localizations, Homology, Homotopy and Applications 12 (2010), no. 2, 245-320.

[BM18a] B. van den Berg and I. Moerdijk, Exact completion of path categories and algebraic set theory: Part I: Exact completion of path categories, Journal of Pure and Applied Algebra 222 (2018), no. 10, 3137-3181.

[BM18b] B. van den Berg and I. Moerdijk, Univalent completion, Mathematische Annalen 371 (2018), 1337-1350.

[Bro73] K. S. Brown, Abstract homotopy theory and generalized sheaf cohomology, Trans. Amer. Math. Soc. 186 (1973), 419-458.

[BR13] J. Bergner and C. Rezk, Reedy categories and the $\Theta$-construction, Mathematische Zeitschrift 274 (2013), no. 1-2, 499-514.

[CLW93] A. Carboni, S. Lack, and R. F. C. Walters, Introduction to extensive and distributive categories, J. Pure Appl. Algebra 84 (1993), no. 2, 145-158.

[CV98] A. Carboni and E. M. Vitale, Regular and exact completions, J. Pure Appl. Algebra 125 (1998), no. 1-3, 79-116.

[Car95] A. Carboni, Some free constructions in proof theory and realizability, J. Pure Appl. Algebra 103 (1995), no. 2, 117-148.

[CD09] B. Chorny and W. G. Dwyer, Homotopy theory of small diagrams over large categories, Forum Mathematicum, 2009, pp. 167-179.

[Cho15] B. Chorny, Homotopy theory of relative simplicial presheaves, Israel Journal of Mathematics 205 (2015), no. 1, 471-484.

65

[Cis20] D.-C. Cisinski, *Higher categories and homotopical algebra*, Cambridge Studies in Advanced Mathematics, Cambridge University Press, 2020.
[CH02] J. D. Christensen and M. Hovey, *Quillen model structures for relative homological algebra*, Math. Proc. Cambridge Philos. Soc. **133** (2002), no. 2, 261-293. See also https://arxiv.org/abs/math/0011216.
[DL07] B. J. Day and S. Lack, *Limits of small functors*, Journal of Pure and Applied Algebra **210** (2007), no. 3, 651-663.
[DHI04] D. Dugger, S. Hollander, and D. C. Isaksen, *Hypercovers and simplicial presheaves*, Math. Proc. Camb. Phil. Soc. **136** (2004), no. 1, 9-51.
[DK84] W. G. Dwyer and D. M. Kan, *Singular functors and realization functors*, Indagationes Mathematicae (Proceedings), 1984, pp. 147-153.
[Elm83] A. D. Elmendorf, *Systems of fixed point sets*, Transactions of the American Mathematical Society **277** (1983), no. 1, 275-284.
[EP17] J. Emmenegger and E. Palmgren, *Exact completion and constructive theories of sets* (2017), available at https://arxiv.org/abs/1710.10685. To appear in Journal of Symbolic Logic.
[F87] E. Dror Farjoun, *Homotopy theories for diagrams of spaces*, Proceedings of the American Mathematical Society **101** (1987), no. 1, 181-189.
[Fre09] B. Fresse, *Modules over operads and functors*, Lecture Notes in Mathematics. Springer-Verlag, Berlin **1967** (2009).
[GZ67] P. Gabriel and M. Zisman, *Calculus of fractions and homotopy theory*, Ergebnisse der Mathematik und ihrer Grenzgebiete, Band 35, Springer-Verlag New York, Inc., New York, 1967.
[GS17] N. Gambino and C. Sattler, *The Frobenius property, right properness and uniform fibrations*, J. Pure Appl. Algebra **221** (2017), No. 12, 3027-3068.
[GK17] D. Gepner and J. Kock, *Univalence in locally Cartesian closed ∞-categories*, Forum Math. **29** (2017), 617-652.
[GSS19] N. Gambino, C. Sattler, and K. Szumilo, *The constructive Kan-Quillen model structure: two new proofs* (2019), available at https://arxiv.org/abs/1907.05394.
[Gar09] R. Garner, *Understanding the small object argument*, Appl. Cat. Struct. **17** (2009), no. 3, 247-285.
[GJ99] P. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Birkauer, 1999.
[Hen18] S. Henry, *Weak model categories in classical and constructive mathematics* (2018), available at https://arxiv.org/abs/1807.02650.
[Hen19] S. Henry, *A constructive account of the Kan-Quillen model structure and of Kan's Ex∞ functor* (2019), available at https://arxiv.org/abs/1905.06160.
[Hen20] S. Henry, *Combinatorial and accessible weak model categories* (2020), available at https://arxiv.org/abs/2005.02360.
[Hof97] M. Hofmann, *Extensional concepts in intensional type theory*, Springer, 1997.
[Hör21] F. Hörmann, *Model category structures on simplicial objects* (2021), available at https://arxiv.org/abs/2103.01156.
[Hyl82] M. Hyland, *The effective topos*, The L. E. J. Brouwer Centenary Symposium, 1982, pp. 165-216.
[HT96] H. Hu and W. Tholen, *A note on free regular and exact completions and their infinitary generalizations*, Theor. App. Cat. **2** (1996), no. 10, 113-132.
[John02] P. T. Johnstone, *Sketches of an elephant: a topos theory compendium. Vol. 1*, Oxford Logic Guides, vol. 43, The Clarendon Press, Oxford University Press, New York, 2002. MR1953060
[Jar96] R. Jardine, *Boolean localisation in practice*, Documenta Mathematica **1** (1996), 245-275.
[Joy84] A. Joyal, *Letter to A. Grothendieck* (1984), available at https://webusers.inj-prg.fr/~georges.maltiniotis/ps/lettreJoyal.pdf
[JT07] A. Joyal and M. Tierney, *Quasi categories vs Segal spaces*, Categories in algebra, geometry and mathematical physics, 2007, pp. 277-326.
[KL12] C. Kapulkin and P. LeFanu Lumsdaine, *The Simplicial Model of Univalent Foundations (after Voevodsky)* (2012), available at https://arxiv.org/abs/1211.2851.

66

[Lur09] J. Lurie, *Higher topos theory*, Princeton University Press, 2009.
[MLM92] S. Mac Lane and I. Moerdijk, *Sheaves in geometry and logic - A first introduction to topos theory*, Springer, 1992.
[Men03] M. Menni, *A characterization of the left exact categories whose exact completions are toposes*, Journal of Pure and Applied Algebra **177** (2003), no. 3, 287–301.
[MV99] F. Morel and V. Voevodsky, *A$^{1}$-homotopy theory of schemes*, Publ. Math. I.H.E.S **90** (1999), 45–143.
[Qui67] D. G. Quillen, *Homotopical algebra*, Lecture Notes in Mathematics, vol. 43, Springer, 1967.
[RB06] A. Rădulescu-Banu, *Cofibrations in Homotopy Theory* (2006), available at https://arxiv.org/abs/math/0610009v4.
[Ras18] N. Rasekh, *A Theory of Elementary Higher Toposes* (2018), available at https://arxiv.org/abs/1805.03805.
[Rez01] C. Rezk, *A model for the homotopy theory of homotopy theories*, Transactions of the American Mathematical Society **353** (2001), no. 3, 973–1007.
[Rez10] C. Rezk, *Toposes and Homotopy Toposes* (2010), available at https://faculty.math.illinois.edu/~rezk/homotopy-topos-sketch.
[Rie14] E. Riehl, *Categorical Homotopy Theory*, Cambridge University Press, 2014.
[RV14] E. Riehl and D. Verity, *The theory and practice of Reedy categories*, Theory Appl. Categ. **29** (2014), 256–301.
[Sat17] C. Sattler, *The Equivalence Extension Property and Model Structures* (2017), available at https://arxiv.org/abs/1704.06911.
[Shu17] M. Shulman, *Elementary $(\infty, 1)$-topoi* (2017), available at https://golem.ph.utexas.edu/category/2017/04/elementary_1topoi.html.
[Shu19] M. Shulman, *All $(\infty, 1)$-toposes have strict univalent universes* (2019), available at https://arxiv.org/abs/1904.07004.
[Spi01] M. Spitzweck, *Operads, Algebras and Modules in General Model Categories* (2001), available at https://arxiv.org/abs/math/0101102.
[Ste17] W. Steimle, *Degeneracies in quasi-categories* (2017), available at https://arxiv.org/abs/1702.08696.
[Ste16] M. Stephan, *On equivariant homotopy theory for model categories*, Homology, Homotopy and Applications **18** (2016), no. 2, 183–208.
[Szu17] K. Szumilo, *Homotopy theory of cocomplete quasicategories*, Algebraic & Geometric Topology **17** (2017), 765–791.
[TV05] B. Toën and G. Vezzosi, *Homotopical algebraic geometry I: higher topos theory*, Advances in Mathematics **193** (2005), 257–372.
N. Gambino, UNIVERSITY OF LEEDS, N.Gambino@leeds.ac.uk
S. Henry, UNIVERSITY OF OTTAWA, shenry2@uottawa.ca
C. Sattler, CHALMERS UNIVERSITY OF TECHNOLOGY, sattler.christian@gmail.com
K. Szumilo, UNIVERSITY OF LEEDS, K.Szumilo@leeds.ac.uk

67