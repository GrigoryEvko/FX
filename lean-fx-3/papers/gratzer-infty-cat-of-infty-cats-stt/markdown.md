# The ∞-category of ∞-categories in simplicial type theory

Daniel Gratzer

gratzer@cs.au.dk

Aarhus University

Jonathan Weinberger

jweinberger@chapman.edu

Chapman University

Ulrik Buchholtz

ulrik.buchholtz@nottingham.ac.uk

University of Nottingham

## Abstract

Simplicial type theory (STT) was introduced by Riehl and Shulman to leverage homotopy type theory to prove results about (∞, 1)-categories. Initial work on simplicial type theory focused on "formal" arguments in higher category theory and, in particular, no non-trivial examples of ∞-category theory were constructible within STT. More recent work has changed this state of affairs by applying techniques developed initially for cubical type theory to construct the ∞-category of spaces. We complete this process by constructing the ∞-category of ∞-categories, recovering one of the main foundational results of ∞-category theory (straightening–unstraightening) purely type-theoretically. We also show how this construction enables new examples of the directed version of the structure identity principle: the structure homomorphism principle.

## Acknowledgments

Jonathan Weinberger is grateful to the Fowler of School of Engineering at Chapman University for generous support of this work. He is particularly thankful to the Fletcher Jones Foundation and their award of a Fletcher Jones Foundation Faculty Fellowship in Engineering '25–'28 and the ensuing generous funding of this work. He also thanks the Schmid School of Science and Technology as well as the Center of Excellence in Computation, Algebra, and Topology (CECAT), both at Chapman University, for providing an excellent research environment.

## 1 Introduction

A defining characteristic of dependent type theories is their focus on universes of (small) types. More than in other foundations of mathematics, such universes are critical for even proving such basic properties as 0 ≠ 1 [38]. This focus on universes is only intensified with homotopy type theory (HoTT) [39] where the universe is supplemented with the univalence axiom. Such univalent universes allow type theorists to view types as a synthetic incarnation of spaces (i.e., ∞-groupoids) with the intensional identity type a =_A b modeling paths in the type A. The utility of this viewpoint is demonstrated by development of synthetic homotopy theory inside of HoTT: a reconstruction of classical results in homotopy theory with simpler and more conceptual proofs.

A long-standing challenge in HoTT has been to broaden the reach of synthetic homotopy theory to include homotopy-coherent algebraic structures and, especially, the homotopical enhancement of category theory: (∞, 1)-category theory.¹ While numerous approaches to this problem have been proposed [1, 14, 17, 25–29, 33, 40–42] we will focus on the approach introduced by Riehl and Shulman [33]. There the authors leveraged a non-standard model of HoTT where types are realized by simplicial spaces. In particular,

they showed that the complete Segal spaces—a known model of ∞-categories [31]—then arise as certain types satisfying a pair of easily-defined properties. Thus, in this setting not every type is an ∞-category, but every ∞-category gives rise to a valid type.

Concretely, simplicial type theory extends HoTT with a directed interval, a postulated totally ordered lattice (I, 0, 1, ≤). This new type is meant to represent the ∞-category with two objects 0, 1 and a single non-identity morphism 0 → 1—an interpretation justified by the model of STT in simplicial spaces—and we then use I to define morphisms in an arbitrary type A as ordinary functions I → A. By constraining the endpoints of a synthetic morphism, we arrive at the definition of the space of synthetic morphisms in a type: hom_A(a, b) = Σ_{f:I→A} f 0 = a × f 1 = b.

Riehl and Shulman [33] then demonstrate that the definition of an ∞-category can be formulated concisely as a predicate isCat on types, essentially requiring every pair of composable morphisms have a unique composite. Furthermore, they show that ordinary functions between such types constitute functors and that other classical definitions in ∞-category theory become expressible. Subsequent work has further expanded this approach, developing fibered category theory [5, 43], limits and colimits [3], etc.

While not every type constitutes an ∞-category in STT, many type-theoretic operations preserve the property of being an ∞-category. For instance, 0 and 1 are the initial and terminal categories, A × B (A + B) is the (co)product category, and A → B is the category of functors. As an extension of HoTT, STT comes equipped with a (hierarchy of) universes and it is therefore natural to ask:

Is U a recognizable category, e.g., the category of categories?

Unfortunately, the answer is negative; U is the canonical example of a type that is not an ∞-category in STT. In fact, even if one considers simple subtypes of the universe (e.g., Σ_{A:U} isCat(A)) one does not obtain a category, as synthetic morphisms I → Σ_{A:U} isCat(A) neither compose nor faithfully represent functors. However, it has long been conjectured that the category of categories should be constructible in STT as a certain subtype of the universe.

We address this final gap in the foundations of STT by settling this conjecture affirmatively and constructing the category of categories as a subtype Cat ↩ U and verifying its essential properties.

### 1.1 Directed univalence and Cat

What criteria should be used to determine if a subtype Cat ↩ U is a valid definition of the category of categories? If one is not considering ∞-categories, the answer to this question is straightforward: Cat is a valid definition if the objects denote precisely small types satisfying isCat, synthetic morphisms are exactly functions (i.e., functors) between these types, and the composition and identity operations behave as expected. In the ∞-categorical case, the story does not end here; we must also convince ourselves that all the higher synthetic morphisms also behave "as expected". However, it is far from clear what the expected behavior ought to be! Instead,

¹In both the title and hereafter, we shall simply write "∞-category" or even "category" to refer to (∞, 1)-categories. If we wish to specifically discuss ordinary categories, we shall specifically denote them by 1-categories.

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

we take a different approach by isolating a particular universal property for the embedding Cat $\hookrightarrow$ $\mathcal{U}$ and arguing that all the other properties of Cat stem from this single property.

The universal property in question is an $\infty$-categorical version of the Grothendieck correspondence, often referred to as straightening-unstraightening in the $\infty$-categorical context. Classically, the Grothendieck correspondence states there is an equivalence between pseudofunctors $C \to \text{Cat}$ for some 1-category $C$ and pairs of a category $\mathcal{E}$ and a cocartesian family $\mathcal{E} \to C$.$^2$ Naively, this suggests a simple universal property for the type Cat: We should require for every $\infty$-category $C$ an equivalence between the type of functions $C \to \text{Cat}$ and the type $\sum_{E:\mathcal{U}} \sum_{\pi:E \to C} \text{isCocart}(\pi)$. Unfortunately, this definition is too straightforward: if such a Cat existed we would be able to show that isCocart held for every map $\pi$ which is certainly not true.

The problem is familiar to cubical type theorists: we are essentially asking for Cat to be a universal fibration, where isCocart is our notion of fibrancy. It is well-known that one cannot give universal property for the univalent universe in the extensional type theory of cubical sets [30]: the naive equivalence is only valid with respect to closed elements and cannot be internalized this way into type theory where it would also apply to elements in an arbitrary context. A solution to this problem in cubical type theory was presented by Licata et al. [18]. There the authors give a description of a universal fibration in an extensional type theory for cubical sets using modal type theory. They supplement type theory with an idempotent comonad $b$, such that the modal type $\langle b \mid A \rangle$ contains only the global elements of $A$. After further extending type theory with a right adjoint to $\mathbb{I} \to -$, they are then not only able to express the desired universal property (appropriately annotated with $b$), but also use the aforementioned right adjoint to derive it.

This idea has been adapted to variants of simplicial type theory first by Weaver and Licata [42] and later by Gratzer et al. [10] to construct a category of discrete $\infty$-categories (spaces). We follow on this line of work—specifically Gratzer et al. [10]—and use the $b$ modality to state the correct universal property for the category of categories and produce a type satisfying it. In particular:

**Theorem 4.3.** Cat is the base of the universal cocartesian family, i.e., for any $C \ni_b \mathcal{U}$, we have $\langle b \mid C \to \text{Cat} \rangle \simeq \langle b \mid \sum_{E:C \to \mathcal{U}} \text{isCocart}(E) \rangle$.

On its own, this statement is not worth much. We do not know whether Cat is a category itself, let alone to what its objects and morphisms correspond. To resolve this, we give a detailed analysis of the structure of cocartesian fibrations over certain categories, relying on the established results in simplicial type theory. As a particular case of these results, we conclude that cocartesian fibrations over $\mathbb{I}$ are determined by (1) a pair of categories $C, D$ along with (2) a function $C \to D$. Consequently, we are able to prove the directed univalence theorem for Cat:

**Corollary 5.5** (Directed univalence). If $A, B$ are $b$-elements of Cat, then there is a equivalence $\text{dua}: \hom_{\text{Cat}}(A, B) \simeq \langle b \mid A \to B \rangle$.

Here we see the first major divergence between the case of categories and the previously considered case of discrete categories. Directed univalence for Cat only guarantees that $\hom_{\text{Cat}}(A, B)$ is

equivalent to $\langle b \mid A \to B \rangle$ whereas in the discrete case one obtains an equivalence with $A \to B$. This is inevitable: no category can have hom-spaces equivalent to $A \to B$ for arbitrary categories $A, B$. However, the appearance of modalities in directed univalence is a significant complication.

Further consequences of our analysis prove that Cat is a category and that composition of synthetic morphisms corresponds (under directed univalence) to composition of ordinary functions. In total then, we show that the universal property of Cat is sufficient to derive all the expected behavior of a category of categories as well as uniquely characterize Cat itself.

Directed univalence opens up a wide array of applications. For instance, we use it to show that Cat contains a number of recognizable reflective subcategories (truncated categories, partial orders, spaces, etc.). It also allows us to build new and important categories by combining Cat with existing type-theoretic connectives. As a simple example, we show that $\sum_{c:\text{Cat}} c$ can be analyzed using directed univalence and use its attendant structure homomorphism principle (SHP) to see that $\sum_{c:\text{Cat}} c$ is the lax slice category 1 $\nmid$ Cat.

Finally, while Theorem 4.3 is a form of the Grothendieck correspondence, it is not the strongest form possible. This would state that there is an equivalence of $\infty$-categories between cocartesian families over $C$ and the functor category $C \to \text{Cat}$. We adapt an argument sketched by Cisinski et al. [6] to STT to show that Theorem 4.3 upgrades to an equivalence of categories and thereby give a synthetic proof of the straightening-unstraightening theorem [19].

## 1.2 Contributions and outline

Our main contribution is the first construction of a directed univalent category of categories within STT together with a verification of all its essential properties. This is the last major primitive missing from the theory of $\infty$-categories in simplicial type theory and, additionally, also constitutes a new and novel approach to a foundational theorem in $\infty$-category theory itself. With this in place, we also note that a putative full directed type theory can be interpreted into $\infty$-categories by giving a mere syntactic translation to the appropriate fragment of STT.

- We extend the methodology of Licata et al. [18] to construct a universal cocartesian family $\text{Cat}_\bullet \to \text{Cat}$.
- We derive purely from this universal property that Cat is a category, satisfies directed univalence, etc.
- We prove various properties of Cat and showcase the novel applications of SHP it enables.
- Finally, we give a fully synthetic proof of the foundational straightening-unstraightening theorem.

Over all, we demonstrate how type theory (through STT) is highly effective for proving major results in higher category theory.

The remainder of the paper is organized as follows. In Section 2 we recall the main ideas of simplicial type theory, its triangulated type theory variant, and the modal extensions thereof. This, along with Section 3 on cocartesian fibrations, is intended to make the paper as self-contained as possible. In Section 4 we define Cat and prove Theorem 4.3, the main construction of this paper. In Section 5, we combine our new results on cocartesian fibrations along with the results of the prior section to prove Corollary 5.5 along with the fact that Cat is a category. Finally, in Sections 6 and 7, we

$^2$In the 1- and 2-categorical literature these are often referred to as Grothendieck opfibrations. We use "cocartesian" as it is the standard term in $\infty$-category theory.

The $\infty$-category of $\infty$-categories in simplicial type theory

give a number of consequences of our results, including a proof of straightening–unstraightening (Corollary 6.6). For reasons of space we have omitted various technical details and proofs from the main body of the paper; most of these are recorded in the appendix.

## 2 Simplicial and triangulated type theory

We now turn to giving a more precise account of the flavor of simplicial type theory we shall use. There are two major modifications to the theory compared with the original system studied by Riehl and Shulman [33]. First is that we supplement our theory with a collection of modalities, including the $b$ modality discussed in the introduction. We do this using MTT, a general purpose modal dependent type theory [9]. Secondly, the intended model of STT is simplicial spaces, the $\infty$-categorical version of $\mathrm{PSh}(\Delta)$. However, in order to leverage the techniques of Licata et al. [18] to define Cat, we require a postulated amazing right adjoint to $\mathbb{I} \to -$. Unfortunately, in the intended model of simplicial spaces, such a right adjoint simply does not exist; the category of simplices does not have products.

To circumvent this, Gratzer et al. [10] introduced a further relaxation of the modal variant of STT: triangulated type theory $\mathrm{TT}_{\square}$. The intended model of $\mathrm{TT}_{\square}$ is Dedekind cubical spaces, rather than simplicial ones. Simplicial spaces embed into this intended model as a subtopos and the original structure therefore remains. Concretely, this change involves relaxing the requirement that $\mathbb{I}$ be totally ordered to merely asking it to be a bounded distributive lattice. In this section, we recall the details of $\mathrm{TT}_{\square}$ relevant for this work and, in particular, describe the modal extensions necessary to construct the category of categories.

### 2.1 First steps in triangulated type theory

As mentioned in Section 1, STT and its relaxation $\mathrm{TT}_{\square}$, extend homotopy type theory. Accordingly, we begin by recalling the basic definitions and notations from homotopy type theory. For a more complete account, see the Univalent Foundations Program [39].

Homotopy type theory begins with intensional Martin-Löf type theory, complete with a hierarchy of universes, $\mathcal{U}_0, \mathcal{U}_1, \ldots$, and intensional identity types $a =_A b$. We use $\prod$ and $\sum$ for the standard dependent product and sum types of this type theory and use $p$ for the transport map $B(x) \to B(y)$ induced by $p : x = y$. The key extension of HoTT, the univalence axiom, governs the behavior of the intensional identity type of the universe. In particular, this axiom relates equality in the universe to equivalences. See op. cit. for a detailed discussion of the type of equivalences $A \simeq B$; we only note that it is a subtype of $A \to B$ which, when $A = B$, includes the identity function.

Axiom 1. The canonical map $A =_{\mathcal{U}_i} B \to A \simeq B$ sending refl to id is an equivalence.

We shall also have use for a few other HoTT concepts. First, since univalence causes the unicity of identity proofs to fail rather spectacularly, so we isolate those types for which this property still holds as (homotopy) sets. We will also use for the stronger properties of being a (homotopy) proposition, or contractible:

$$\operatorname{isSet}(A) = \prod_{a,b:A} \operatorname{isProp}(a = b)$$

$$\operatorname{isProp}(A) = \prod_{a,b:A} \operatorname{isContr}(a = b)$$

$$\operatorname{isContr}(A) = \sum_{a:A} \prod_{b:A} a = b$$

If $\phi : \mathcal{U} \to \mathcal{U}$ is valued in propositions, we write $\mathcal{U}_\phi$ for $\sum_{A:\mathcal{U}} \phi(A)$. Moreover, we use HProp as condensed notation for $\mathcal{U}_{\mathrm{isProp}}$.

Next, we require a few higher inductive types (HITs). These are inductive types that postulate constructors not only of elements of the type, but also of elements of its identity type. For instance, we shall use pushouts $A +_B C$ and localizations as defined by Rijke et al. [34]. Since the models of HITs satisfying strict equations is somewhat fraught, we only assume that our HITs satisfy propositional computation rules, i.e., that they are homotopy-initial algebras.

We now turn to the first and most basic axiom of triangulated type theory, which introduces the directed interval.

Axiom 2. There is a set $\mathbb{I}$ equipped with the structure of a bounded distributive lattice $(0, 1, \wedge, \vee)$ such that $0 \neq 1$.

Crucially, compared with STT we do not assume that $\prod_{i,j:\mathbb{I}} i \leq j \vee j \leq i$ holds. However, just as with the failure of UIP, we may isolate those types that "believe $i \leq j \vee j \leq i$" as simplicial types. These are types $A$ such that the following holds:

$$\operatorname{isSimp}(A) = \prod_{i,j:\mathbb{I}} \operatorname{isEquiv}(\operatorname{const} : A \to (i \leq j \vee j \leq i \to A))$$

The next result follows from Rijke et al. [34]:

Proposition 2.1. There is a lex idempotent monad $\square : \mathcal{U} \to \mathcal{U}$ with $\square A$ universal among simplicial types receiving a map from $A$.

In other words, ordinary simplicial type theory is the "subset of $\mathrm{TT}_{\square}$" given by types for which $\eta_A : A \to \square A$ is an equivalence. We write $\mathcal{U}_{\square} = \sum_{A:\mathcal{U}} \operatorname{isEquiv}(\eta_A)$ for the subtype of $\mathcal{U}$ spanned by simplicial types and note that $\mathcal{U}_{\square}$ is itself simplicial. Consequently, there is a unique $\bar{\square} : \square \mathcal{U} \to \mathcal{U}_{\square}$ such that $\bar{\square} \circ \eta = \square$.

With $\mathbb{I}$, we can make a number of important definitions that isolate those types that actually behave like categories. First, as mentioned earlier, we can define a synthetic morphism in a type $A$ to be a map $\mathbb{I} \to A$. Constraining the endpoints of this map, we arrive at the definition of the synthetic hom-type:

$$\hom_A(a, b) = \sum_{f:\mathbb{I}\to A} f \, 0 = a \times f \, 1 = b$$

Every type comes equipped with a collection of identity morphisms: $\operatorname{id}_a = \lambda_-.a : \hom(a, a)$. However, the other operation we expect from a category–composition–is not available by default. What is available instead is a proof-relevant composition relation, stating that a pair of synthetic morphisms compose to a third. To define these, we derive the 2-simplex $\Delta^2$ from $\mathbb{I}$. For the sake of future use, we define the $n$-simplex for any $n \geq 0$:

$$\Delta^n = \sum_{\bar{i}:\mathbb{I}^n} (i_0 \geq i_1 \geq \dots \geq i_{n-1})$$

Crucially, the 2-simplex can be visualized as a triangle (the shaded region below), if $\mathbb{I}$ is seen as a line segment whence $\mathbb{I}^2$ as a square:

![img-0.jpeg](img-0.jpeg)

We also have need for the inner horn $\Lambda_1^2 = \sum_{i,j:\mathbb{I}} i = 1 \vee j = 0$, a subtype of $\Delta^2$ which captures the two highlighted segments above.

Say that $\tau : \Delta^2 \to A$ is a witness for the fact that $\tau(-, 0), \tau(1, -) : \mathbb{I} \to A$ compose to $\lambda i. \tau(i, i)$. A Segal type (sometimes called a pre-category) is one where every pair of composable arrows admits a

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

unique composition witness. To define this formally, we note that maps $\Lambda_1^2 \to A$ precisely capture the data of composable arrows:

Definition 2.2. A type $A$ is Segal if isEquiv($A^{\Lambda^2} \to A^{\Lambda_1^2}$) holds.

Notation 2.3. If $f, g: A^\ell$ and $p: f(1) = g(0)$, we write $[f, g, p]$ for the induced map $A^{\Lambda_1^2}$ and, if $A$ is Segal, $g \circ_p f$ for the composite. Furthermore, we shall subsequently have use for the outer horns $\Lambda_0^2 = \sum_{i,j:\mathbb{I}} i = j \lor j = 0$ and $\Lambda_2^2 = \sum_{i,j:\mathbb{I}} i = 1 \lor i = j$. Finally, we write $i$ for the element of $\Delta^{n+i}$ given by $(1, \dots, 1, 0, \dots)$ of $i$ copies of 1 followed by $n$ copies of 0.

Segal types enjoy a unique composition operation given by the inverse of the map $A^{\Lambda^2} \to A^{\Lambda_1^2}$, and calculation shows that the aforementioned definition of the identity morphism is a left and right unit for composition. However, objects in a pre-category have two distinct notions of sameness: via either the identity type or synthetic isomorphism. By the latter, we mean a morphism $f: \hom(a, b)$ equipped with $g, h: \hom(b, a)$ along with composition witnesses showing that $g(h)$ is left (right) inverse to $f$. One can define $\mathbb{E} = \Delta^2 \sqcup_{\Lambda_1^2} \mathbb{I} \sqcup_{\Lambda_2^2} \Delta^2$ such that $\mathbb{E} \to X$ precisely corresponds to an equivalence in $X$ [5, §4.2]). A distinctive feature of $\infty$-category theory is that these two notions (object equality and isomorphism) can be made to coincide; a property similar to the univalence axiom. We therefore also single out those types which satisfy this local univalence condition:

Definition 2.4. A type $A$ is Rezk if isEquiv(const: $A \to A^\mathbb{E}$).

Definition 2.5. A simplicial, Segal, and Rezk type is called a category. A category whose morphisms are all invertible is a groupoid.

Remark 2.6. The general results of Rijke et al. [34] show that categories and groupoids are modal types for idempotent monads. We write $\bigcirc_{\text{grpd}}$ for the idempotent modality associated with groupoids in particular, i.e., nullification at $\mathbb{I}$.

We shall also have occasion to use the relative versions of the Segal and Rezk conditions. Given a family of types $A: X \to \mathcal{U}$, we say that $A$ is (right) orthogonal to a map $I \to J$ if the following canonical map is an equivalence:

$$\left(\sum_{x:X} A(x)\right)^J \to X^J \times_{X^J} \left(\sum_{x:X} A(x)\right)^I$$

The relative Segal condition asks that a family of types $A: X \to \mathcal{U}$ be right orthogonal to $\Lambda_1^2 \to \Delta^2$ and the relative Rezk condition asks the same for $\mathbb{E} \to \mathbf{1}$. A Segal family is called inner and a family that is both Segal and Rezk is iso-inner.

For use in Section 4, we note that we can phrase the requirement that a family be inner using the following predicate:

$$\text{isInner}: (\Delta^2 \to \mathcal{U}) \to \text{HProp}$$

$$\text{isInner } A = \text{isEquiv}\left(\left(\prod_{t:\Delta^2} A t\right) \to \left(\prod_{t:\Lambda_1^2} A t\right)\right)$$

A family $A: X \to \mathcal{U}$ is inner if and only if $\prod_{h:\Delta^2 \to X} \text{isInner}(A \circ h)$ holds.

Notation 2.7. We shall often identify a family $A: X \to \mathcal{U}$ with its associated total space projection $\pi$ from $\overline{A} := \sum_{x:X} A x$ to $X$. We shall say that an arbitrary map of types $f: X \to Y$ is, for instance, inner if the associated map $Y \to \mathcal{U}$ sending $y$ to $f^{-1}(y)$ is inner.

Given a family $A: X \to \mathcal{U}$ and an arrow $f: \mathbb{I} \to X$ we define dependent arrows over $f$ from $a: A(f0)$ to $a': A(f1)$ as follows:

$$\hom_f^A(a, a') := \sum_{\alpha: (t:\mathbb{I}) \to A(f t)} (\alpha 0 = a) \times (\alpha 1 = a')$$

In an inner family there exists an induced composition operation for dependent arrows [5].

## 2.2 Multimodal type theory

The next step in $\text{TT}_{\mathbb{Q}}$ is to include modalities: special type constructors that violate key properties we ordinarily require in type theory, such as stability under substitution. We use these modalities to internalize crucial operations from our intended model of cubical spaces such as the discrete and codiscrete endofunctors, the opposite functor, etc. To this end, we recall some of the details of the modal extension to type theory, MTT, following [9]. See Gratzer [8] for a more detailed account. Since our primary goal is to write programs in MTT, we focus on the "informal" version of the syntax and defer the formal rules (replete with de Bruijn indices and a substitution calculus) to Appendix A.

First, MTT is parameterized by a mode theory $\mathcal{M}$. This is a strict 2-category describing the modalities (as 1-cells) and transformations between them (as 2-cells). While MTT also permits distinct type theories to be related by modalities by considering mode theories with multiple modes (0-cells), we do not need this generality and therefore assume that mode theories have only one object. We shall also only be concerned with mode theories with at most one 2-cell between every pair of 1-cells i.e., 2-categories that are merely poset-enriched. As such, our mode theories are simply given by ordered monoids. The mode theory required for $\text{TT}_{\mathbb{Q}}$ is described in Section 2.3, but we continue with an arbitrary mode theory satisfying these constraints for the moment.

The main extension of MTT is to add a new modal type $\langle \mu \mid - \rangle$ for each modality $\mu \in \text{Arr}(\mathcal{M})$. However, as already mentioned modal types are somewhat peculiar, and to accommodate them MTT also modifies context extension. Specifically, each variable in an MTT context is annotated with a "formal division" of modalities $x:_{\mu/\nu} A$. We write $\Gamma/\nu$ for the operation which modifies each annotation in $\Gamma$ to send $x:_{\mu/\nu_0} A$ to $x:_{\mu/\nu_0 \circ \nu} A$. The variable rule is then modified to account for these formal divisions as follows:

$$\frac{\mu \le \nu \quad x:_{\mu/\nu} A \in \Gamma}{\Gamma \vdash x: A}$$

Note that one can recover the ordinary rules for variables by considering the annotation id/id. As a matter of notation therefore, we generally suppress division by id and omit the annotation entirely for id/id so that we instead write $x:_{\mu} A$ or $x: A$.

These annotations are then manipulated by the modal operators $\langle \mu \mid - \rangle$. In particular, they are added by the formation and introduction rules. The (somewhat lengthy) elimination rule, on the other hand, papers over the difference between annotations on a variable and modal types by allowing us to convert a binding $x:_{\nu/\text{id}} \langle \mu \mid A \rangle$

The \(\infty\)-category of \(\infty\)-categories in simplicial type theory

into a binding \(y:_{\nu \circ \mu /\mathrm{id}}A\)

\[
\frac {\Gamma / \mu \vdash A \text {type}}{\Gamma \vdash \langle \mu | A \rangle \text {type}}
\]

\[
\frac {\Gamma / \mu \vdash a : A}{\Gamma \vdash \operatorname{mod} _ {\mu} (a) : \langle \mu | A \rangle}
\]

\[
\begin{array}{c} \Gamma / \nu \circ \mu \vdash A \text {type} \qquad \Gamma , y: _ {\nu / \mathrm{id}} \langle \mu | A \rangle \vdash B (y) \text {type} \\ \Gamma , x: _ {\nu \circ \mu / \mathrm{id}} A \vdash b (x): B [ \operatorname{mod} _ {\mu} (x) / y ] \qquad \Gamma / \nu \vdash a: \langle \mu | A \rangle \\ \hline \Gamma \vdash \operatorname{let} _ {\nu} \operatorname{mod} _ {\mu} (x) \leftarrow a \text {in} b (x): B [ a / y ] \end{array}
\]

\[
\operatorname{let} _ {\nu} \operatorname{mod} _ {\mu} (x) \leftarrow \operatorname{mod} _ {\mu} (a _ {0}) \text {   in   } b (x) = b [ a _ {0} / x ]
\]

Aside from these modal types, MTT extends type theory with an extended version of the dependent product type,  \( (a :_{\mu} A) \to B(a) \) . Up to equivalence, these modal dependent products are the same as  \( (a : \langle \mu | A \rangle) \to \text{let mod}_{\mu}(a_0) \leftarrow a \text{ in } B(a_0) \) , but offer lighter-weight notation and support a stronger  \( \eta \) -rule.

\[
\frac {\Gamma / \mu \vdash A \text {type} \quad \Gamma , a : _ {\mu} A \vdash b (a) : B (a)}{\Gamma \vdash \lambda a . b (a) : (a : _ {\mu} A) \to B (a)}
\]

\[
\frac {\Gamma \vdash f : (a : _ {\mu} A) \to B (a) \qquad \Gamma / \mu \vdash a : A}{\Gamma \vdash f (a) : B (a)}
\]

When we write “for all  \( a :_{\mu} A \) , the type  \( B(a) \)  is inhabited” this should be understood to denote a function  \( (a :_{\mu} A) \to B(a) \) .

Finally, we require the following technical axiom on MTT which governs the interaction between modalities and identity types:

Axiom 3. If \(A:_{\mu} \mathcal{U}\) and \(a, b:_{\mu} A\), then the following canonical map sending refl to mod\(_{\mu}\) (refl) is an equivalence:

\[
\operatorname{mod} _ {\mu} (a) = \operatorname{mod} _ {\mu} (b) \rightarrow \langle \mu | a = b \rangle
\]

We summarize several basic properties of modalities:

#### Proposition 2.8.

• Each  \( \langle\mu\mid-\rangle \)  commutes with 1 and pullbacks.
•  \( \langle\mu\mid\langle\nu\mid-\rangle\rangle\simeq\langle\mu\circ\nu\mid-\rangle \)  and  \( \langle id\mid-\rangle\simeq- \) .
- If \(\mu \leq \nu\), then there is a canonical map \(\langle \mu | - \rangle \to \langle \nu | - \rangle\).
- There is an equivalence \(\langle b \mid A \to \langle \sharp \mid B \rangle \rangle \simeq \langle b \mid \langle b \mid A \rangle \to B \rangle\) for \(A, B:_{\mathfrak{b}} \mathcal{U}\). Similarly with \(\sharp\) and \(b\) replaced with op.

From the first point, we obtain \(\circledast : \langle \mu | A \to B \rangle \times \langle \mu | A \rangle \to \langle \mu | B \rangle\). We often write \(f^{\dagger}\) for \(\mathrm{mod}_{\mu}(f) \circledast -\), when the latter is well-formed.

### 2.3 Modalities in triangulated type theory

We now turn from MTT generally to the specific instantiation of MTT we require for  \( TT_{\square} \) . Namely, we will work with the mode theory generated by one 0-cell m, three generating non-identity 1-cells  \( \{b,\sharp,op\} \) , and the following (in)equalities:

\[
b = b \circ b = b \circ \sharp = b \circ o p \quad \sharp = \sharp \circ b = \sharp \circ \sharp = \sharp \circ o p
\]

\[
b \leq \mathrm{id} = \mathrm{op} \circ \mathrm{op} \leq \sharp
\]

For intuition, in the cubical spaces model of  \( TT_{\square} \)  the modal operations for the generating modalities are interpreted as follows:

- \(\llbracket \langle b \mid -\rangle \rrbracket\) is the discrete functor—sending a cubical space \(X\) to the constant cubical space \(\Delta(X([0]))\).
- \(\llbracket \langle \sharp \mid -\rangle \rrbracket\) is the codiscrete functor—right adjoint to the discrete functor—and sends a cubical space \(X\) to the cubical space whose value at \([n]\) is given by \(X([0])^{2^n}\).

- \(\llbracket \langle \mathrm{op} \mid -\rangle \rrbracket\) sends a cubical space \(X\) to \(X \circ \mathrm{op}\) where op is the functor on the cube category reversing 0 and 1.

If we consider a category \(C:_{\mathfrak{b}} \mathcal{U}\), then these interpretations of \(\mathfrak{b}\) and op have very concrete meanings: \(\langle \mathfrak{b} \mid C \rangle\) is the underlying discrete groupoid of objects of \(C\) and \(\langle \mathrm{op} \mid C \rangle\) is the opposite category. In general \(\langle \sharp \mid C \rangle\) will fail to be a category even when \(C\) is—its utility is mostly in forcing \(\mathfrak{b}\) to be a left adjoint. We note that the first two modalities are an instance of cohesion [16, 23, 36].

Note, however, that these are presently just intuitions from a particular model. To actually make these have force within  \( TT_{\square} \)  itself, we require additional axioms governing the behavior of I and its interactions with modalities. A complete list of axioms is given in Appendix B so we discuss only axioms playing a direct role in the proofs given in the paper.

First, we have axioms governing the behavior of b and I:

Axiom 4. 0,1: I induce an equivalence \(\langle b \mid \text{Bool} \rangle \simeq \langle b \mid \mathbb{I} \rangle\)

Axiom 5. If \(A:_{\mathfrak{b}} \mathcal{U}\), then is Equiv(\(\langle b \mid A \rangle \to A\)) if is Equiv(\(A \to A^{\mathbb{I}}\))

Intuitively, the first of this pair states that \(\mathbb{I}\) has just two global elements: the specified endpoints 0 and 1. The second axiom ensures that \(\mathbb{I}\) "detects" whether a type is of the form \(\langle b \mid A \rangle\). Phrased pithily: a type \(A\) is equivalent to a groupoid of objects if and only if it has no non-invertible synthetic morphisms. These axioms—particularly the last one—are what force \(\langle b \mid -\rangle\) to match our earlier idea of taking the groupoid core.

The next axiom forces cubes \(\mathbb{I}^n\) to form a separating family among all types. That is, to detect whether a particular (b-)map is invertible, it suffices to check whether post-composing with this map induces equivalences between groupoids of maps \(\langle b \mid \mathbb{I} \to -\rangle\):

Axiom 6. If \(A, B:_{\mathfrak{b}} \mathcal{U}\) and \(f:_{\mathfrak{b}} A \to B\), then \(f\) is an equivalence if

\[
\prod_ {n: \text { Nat }} \text { isEquiv } ((f _ {\star}) ^ {\dagger}: \langle b | \mathbb {I} ^ {n} \to A \rangle \to \langle b | \mathbb {I} ^ {n} \to B \rangle)
\]

Since \(\square\) has a universal "mapping-out" property, we have a succinct description of \(\square A \to B\) in terms of \(A \to B\). In general, there is no such simple relationship between \(A \to \square B\) and \(A \to B\), with the notable exception of the case when \(A = \Delta^n\). Intuitively, \(\square B\) ensures that all hyper-cubes in \(B\) are determined uniquely by the composite of simplices and so while the hyper-cubes of \(\square B\) may be quite different than in \(B\), the collection of simplices in \(B\) remains unchanged. The following records this relationship:

Axiom 7. For every \(A:_{\mathfrak{b}} \mathcal{U}\), the following holds:

\[
\prod_ {n: \text { Nat }} \text { isEquiv } ((\eta_ {\star}) ^ {\dagger}: \langle b | \Delta^ {n} \to A \rangle \to \langle b | \Delta^ {n} \to \square A \rangle)
\]

Our final axiom in this section records the right adjoint to \(\mathbb{I} \to -\) mentioned in Section 1. We must be somewhat more careful in stating this than Licata et al. [18], as we wish to ensure that the postulated adjoint is fully coherent, so we use the following formulation which records that the adjoint exists uniquely:

Axiom 8. For every \(A:_{\mathfrak{b}} \mathcal{U}\), the following holds:

\[
\sum_ {A _ {\mathbb {I}} \backslash \mathfrak {b}} \mathcal {U}, \epsilon : _ {\mathfrak {b}} (A _ {\mathbb {I}}) ^ {\mathbb {I}} \rightarrow A \prod_ {B: \mathfrak {b}} \mathcal {U} \text {   is   Equiv } (\langle b | B \rightarrow A _ {\mathbb {I}} \rangle \rightarrow \langle b | B ^ {\mathbb {I}} \rightarrow A \rangle)
\]

Intuitively,  \( A_{I} \)  is the application of this “amazing” right adjoint to a b-annotated type A and  \( \epsilon \)  is the counit of this adjunction at A. From

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

this data we may reconstruct a functor  \( (-)_{\mathbb{I}}:\langle b\mid\mathcal{U}\rangle\to\langle b\mid\mathcal{U}\rangle \) . Crucially, this axiom only applies when A is b-annotated; Licata et al. [18] show that requiring it for arbitrary types forces  \( I=1 \) , contradicting  \( 0\neq1:I \) . Moreover, as noted earlier, this axiom is not validated by the model of STT in simplicial spaces; it is only after shifting to cubical spaces that Axiom 8 is valid. Concretely, it is often the case that even if A is known to be simplicial, the same will not be true of  \( A_{I} \) . Our main use of this axiom is to “transpose” various b-annotated predicates  \( X^{I}\to HProp \)  into predicates  \( X\to HProp \) . For convenience, we bundle up this process into the following lemma:

Lemma 2.9. If \(\phi :_{\mathfrak{b}} \mathcal{U}^{\mathbb{I}^{n}} \to \mathrm{HProp}\), there is a \(\bar{\phi} :_{\mathfrak{b}} \mathcal{U} \to \mathrm{HProp}\) equipped with a canonical equivalence:

\[
\prod_ {A \ni X \to \mathcal {U}} \langle b | (x: X) \to \bar {\phi} (A x) \rangle \simeq \langle b | (x: X ^ {\mathbb {I} ^ {n}}) \to \phi (A \circ x) \rangle
\]

Finally, Gratzer et al. [10] have shown that  \( TT_{\mathbb{S}} \)  (MTT with this mode theory extended with all of the above axioms) has a model in cubical spaces. They further show, based on a result of Riehl and Shulman [33], that categories in  \( TT_{\mathbb{S}} \)  are realized by a standard model of  \( \infty \) -categories: complete Segal spaces [31].

Theorem 2.10. There is a model of \(TT_{\mathbb{S}}\) in cubical spaces \(\mathrm{PSh}_{\mathrm{eSet}}(\square)\). In this model, categories are realized by complete Segal spaces.

### 2.4 Category theory in triangulated type theory

We require some of the category theory developed previously in  \( TT_{\Sigma} \)  and STT [5, 10, 11, 33]. To keep this paper more self-contained, we recall the relevant results and definitions here.

As noted by Riehl and Shulman [33], a natural transformation between functors \(f, g: C \to D\)—i.e., an element of \(\hom(f, g)\)—corresponds precisely to a family \(\prod_{c: C} \hom(f, c, g, c)\). Consequently, a pointwise invertible natural transformation is invertible. We note a refinement of this statement by Gratzer et al. [11] which further reduces this to \(b\) elements (i.e., objects) of \(C\):\( ^{3} \)

Lemma 2.11. If \(C, D \ni_{\mathfrak{b}} \mathcal{U}\) are categories and \(f, g \ni_{\mathfrak{b}} C \to D\), then a natural transformation \(\alpha \ni_{\mathfrak{b}} \hom(f, g)\) is invertible if and only if for all \(c \ni_{\mathfrak{b}} C\) the map \(\alpha(c): \hom(f, c, g, c)\) is invertible.

We similarly have a synthetic version of the classical result that full, faithful and essentially surjective functors are equivalences.

Lemma 2.12. If \(C, D \ni_{\mathfrak{b}} \mathcal{U}_{\mathrm{isCat}}\), then \(f \ni_{\mathfrak{b}} C \to D\) is invertible iff \(f\) is essentially surjective and fully faithful on \(b\)-elements of \(C\).

Our calculations with cocartesian fibrations in Sections 3 and 4 will rely on the theory of adjunctions in \(\mathrm{TT}_{\mathbb{S}}\). To begin with, an adjunction between two functors \(f: C \to D\) and \(g: D \to C\) is given by a collection of equivalences:

\[
\alpha : \prod_ {c: C} \prod_ {d: D} \hom (f c, d) \simeq \hom (c, g d)
\]

Note that we do not require any additional naturality constraints on \(\alpha\), these are automatically enforced by virtue of working synthetically. We say \(f\) is a left adjoint if there exists a (necessarily unique) \((g, \alpha)\), and dually that \(g\) is a right adjoint if there exists \((f, \alpha)\). It is often difficult to construct such a family of equivalences directly, so we often use the following result of Gratzer et al. [11]:

\( ^{3} \) Gratzer et al. [11] prove Lemmas 2.11 and 2.13 using the twisted arrow modality, which we have chosen not to include in TT \( _{S} \) for simplicity. More elementary proofs merely relying on Axiom 6 are possible and so there is no issue with their use in TT \( _{S} \).

Lemma 2.13. If \(C, D \ni_{\mathfrak{b}} \mathcal{U}\) are categories, then \(f \ni_{\mathfrak{b}} C \to D\) is a left adjoint iff for all \(d \ni_{\mathfrak{b}} D\) there exists \(c \ni_{\mathfrak{b}} C\) and \(\epsilon \ni_{\mathfrak{b}} \hom(f(c), d)\) such that the following is an equivalence for all \(c' \ni_{\mathfrak{b}} C\):

\[
\epsilon_ {*} \circ f: \hom (c ^ {\prime}, c) \to \hom (f (c ^ {\prime}), d)
\]

We shall also have use for the various concrete examples of categories constructed by Gratzer et al. [10]. Foremost among these is the category of groupoids S—the  \( \infty \) -categorical analog of the category of sets. Like our eventual definition of the category of categories, this is characterized through a universal property.

Definition 2.14. A family of types \(A: X \to \mathcal{U}\) is covariant if it is right orthogonal to the inclusion \(\{\emptyset\} \to \mathbb{I}\).

More intuitively, covariant families are families of groupoids such that synthetic homomorphisms of the base lift coherently to functors of the fibers. We shall give more exposition of this idea indirectly in Section 3 when we study their generalization: cocartesian families. Covariant families are closed under numerous properties, including precomposition, \(\Sigma\)-types, etc. We now define \(S\) as the base of the universal covariant family:

Definition 2.15. S is the unique subtype of the universe such that  \( S \to U \)  is covariant, and for all  \( X \ni_{b} U \) , the canonical map  \( \langle b | X \to S \rangle \to \langle b | \sum_{A:X \to U} \text{isCov}(A) \rangle \)  is an equivalence.

Consequently, the type of objects of S, i.e.,  \( \langle b \mid S \rangle \) , is immediately seen to be equivalent to b-covariant families over 1. These, in turn, are equivalent to b-groupoids. The main result of Gratzer et al. [10] extends this characterization to synthetic morphisms:

Theorem 2.16. S is a category, and there is a canonical equivalence  \( \hom_{S}(A,B) \simeq (A \to B) \) . Moreover, under this equivalence, identities and composition of synthetic morphisms are realized by identity functions and ordinary function composition.

Finally, we record a minor but useful result stating that \(\mathbb{I}\), and some types derived from it, form categories [10].

Lemma 2.17. \(\mathbb{I},\mathbb{I}^n\) , and \(\Delta^n\) all form categories.

## 3 Recollections on cocartesian fibrations

Our eventual goal of characterizing \(\langle b | X \to \mathrm{Cat} \rangle\) crucially depends on the theory of cocartesian families [13, 19]. These are a subset of type families \(A: X \to \mathcal{U}\) for which (1) each \(Ax\) is a category, and (2) each morphism \(f: \hom(x, y)\) in \(X\) induces a transport function \(Ax \to Ay\). We shall require that these transport functions are functorial, and that the coherences enforcing functoriality are themselves coherent, etc. In order to structure all of this data, we ask for \(A\) to satisfy a number of propositions that, when combined, give rise to (1) and (2) above. While somewhat indirect, this accounts for the infinite hierarchy of coherences that would otherwise be impossible to write down. This material has been developed within STT [5]. We recall it for the reader's benefit.

### 3.1 The definition of cocartesian families

Consider a family \(A: X \to \mathcal{U}\) and write \(\rho^A\) for the canonical map given by restriction and projection \(\widetilde{A}^{\Delta^2} \to \widetilde{A}^{\Delta_0^2} \times_{X^{\Delta_0^2}} X^{\Delta^2}\). Note that the restriction \(\widetilde{A}^{\Delta^2}\) to \(\widetilde{A}^{\{\emptyset \to 1\}}\) along with the corresponding

The \(\infty\)-category of \(\infty\)-categories in simplicial type theory

map \(\widetilde{A}^{\Lambda_0^2}\times_{\Lambda_0^2\to X}X^{\Delta^2}\to \widetilde{A}^{\{\tilde{0}\to \tilde{1}\}}\) commute with \(\rho^A\), so we may view \(\rho^A\) as a map between two families of types over \(\mathbb{I}\rightarrow \widetilde{A}\). Given \(x:\mathbb{I}\rightarrow \widetilde{A}\), we denote by \(\rho_x^A\) the restriction of \(\rho^A\) to the fibers of these families over \(x\).

Definition 3.1. A morphism \( f: \mathbb{I} \to \widetilde{A} \) is cocartesian in \( A \) (written is \( \operatorname{CocartArr}_A(f) \)) if \( \rho_f^A \) is an equivalence.

Informally, \( f: \mathbb{I} \to \widetilde{A} \) is cocartesian if diagrams of the following shape have a unique lift whenever \( \Delta^{\{\tilde{0}\to\tilde{1}\}} \to \Delta^2 \to \widetilde{A} \) is \( f \):

![img-1.jpeg](img-1.jpeg)

Definition 3.2. A family \(A: X \to \mathcal{U}\) is cocartesian if it is iso-inner, each \(A(x)\) is simplicial, and the following holds:

\[
\prod_ {u: \mathbb {I} \rightarrow X} \prod_ {a: A (u 0)} \sum_ {f: \hom_ {a} ^ {A} (a, \bullet)} \text { is   CocartArr } _ {A} (f)
\]

This requirement is a proposition [5] and each fiber of such a family is a category, satisfying the first of our requirements.

Example 3.3. For every category A the codomain map  \( A^{I} \rightarrow A \)  is cocartesian. The domain projection is cocartesian iff A has pushouts.

Remark 3.4. An arrow is vertical if it maps to an isomorphism. In a cocartesian fibration, every arrow factors as “vertical \(\circ\) cocartesian”.

In case that X is a category and A is simplicial and iso-inner, a slick characterization of cocartesian families becomes available.

Proposition 3.5 (Buchholtz and Weinberger [5]). An iso-inner family \(A: X \to \mathcal{U}_{\square}\) over a category \(X\) is cocartesian iff the map \((\widetilde{A})^{\mathbb{I}} \to (\widetilde{A})^{\{\theta\}} \times_{X^{\{\theta\}}} X^{\mathbb{I}}\) has a left adjoint right inverse.\(^4\)

This characterization implies many closure properties such as under composition, pullback, and Leibniz cotensors [5].

For the second desideratum of cocartesian families, we define the cocartesian transport operation, providing the desired functors between fibers. If \( A: X \to \mathcal{U} \) is cocartesian and \( u: \hom(x, y) \), transport \( u: Ax \to Ay \) is defined by mapping \( a: Ax \) to the codomain of the (unique) cocartesian lift of \( u \) starting at \( a \).

Proposition 3.6. If \(A: X \to \mathcal{U}\) is cocartesian, then cocartesian transport is functorial, i.e., \((vu)_{!} = v_{!} \circ u_{!} \text{ and } (\mathrm{id})_{!} = \mathrm{id}\).

Definition 3.7. For \(A, B: X \to \mathcal{U}\) cocartesian, we say that \(f: \prod_{x: X} Ax \to Bx\) is a cocartesian functor if \(f\) preserves cocartesian arrows. We write \(A \to^{\mathrm{cc}} B\) for the type of cocartesian functors.

For our construction of Cat, it will be helpful to develop the theory of locally cocartesian fibrations. These are families \(A: X \to \mathcal{U}\) that are cocartesian after restriction \(A \circ f\) for every \(f: \mathbb{I} \to X\). As setup, for a family \(A: \mathbb{I} \to \mathcal{U}\), we call an edge \(a: (i: \mathbb{I}) \to Ai\) locally cocartesian if the following proposition holds:

\[
\text { isLocallyCoCart }: (A: \mathbb {I} \to \mathcal {U}) \to ((i: \mathbb {I}) \to A i) \to \mathrm{HProp}
\]

\[
\text { isLocallyCoCart } A a = \prod_ {b: (i: \mathbb {I}) \to A i} \prod_ {p: a 0 = b 0}
\]

\[
\operatorname{isContr} \left(\sum_ {t: (i, j: \Delta^ {2}) \rightarrow A i} t | _ {\Lambda_ {0} ^ {2}} = [ a, b, p ]\right)
\]

\( ^{4} \) That is, a left adjoint where the unit map is an isomorphism.

We then define the structure of having locally cocartesian lifts:

\[
\text { hasLCCLifts }: (\mathbb {I} \to \mathcal {U}) \to \mathcal {U}
\]

\[
\text { hasLCCLifts } A = \prod_ {a _ {0}: A 0} \sum_ {a: \hom_ {A} (a _ {0}, \bullet)} \text { isLocallyCoCart } a
\]

Unlike for cocartesian edges, locally cocartesian edges need not compose. Let us quickly isolate what it means for them to do so:

\[
\text { LCCLiftsCompose }: (\Delta^ {2} \rightarrow \mathcal {U}) \rightarrow \text { HProp }
\]

\[
\text { LCCLiftsCompose } A = (a: \prod_ {s: \Delta^ {2}} A s)
\]

\[
\rightarrow \text { isLocallyCoCart } (a (-, 0)) \times \text { isLocallyCoCart } (a (1, -))
\]

\[
\rightarrow \text { isLocallyCoCart } (\lambda i. a (i, i))
\]

We extend the preceding two definitions to general families \(A: X \to \mathcal{U}\) by stating that they hold for \(A\) if they hold for \(A \circ f: \mathbb{I} \to \mathcal{U}\) for all arrows \(f: \mathbb{I} \to X\) (or squares \(h: \mathbb{I} \times \mathbb{I} \to X\), respectively). We overload the predicates, writing, e.g., hasLCCLifts(A) also for a general family \(A\). A locally cocartesian family is one with hasLCCLifts structure.

Theorem 3.8. If \(A: X \to \mathcal{U}_{\square}\) is iso-inner and locally cocartesian where locally cocartesian edges compose, then locally cocartesian edges are cocartesian and \(A\) is cocartesian.

In this case, locally cocartesian lifts are unique, since cocartesian lifts are. This will be important shortly.

### 3.2 The directed gluing of cocartesian families

We close this section by generalizing the directed gluing type inspired by Weaver and Licata [42] and used in this context by Gratzer et al. [10]. Roughly, this type takes two cocartesian families over \(X\) and a cocartesian functor between them and bundles them into a single cocartesian family over \(X \times \mathbb{I}\). This is a key ingredient of our proof of directed univalence, which will eventually amount to a proof that Gl lifts to an equivalence.

Fix cocartesians fibrations \(F_{0}, F_{1}: X \to \mathcal{U}_{\square}\) and a cocartesian functor \(\alpha: \prod_{x: X} F_{0} x \to F_{1} x\). The directed gluing of this data is

\[
\operatorname{Gl} \left(F _ {0}, F _ {1}, \alpha\right): X \times \mathbb {I} \rightarrow \mathcal {U} _ {\square}
\]

\[
\operatorname{Gl} \left(F _ {0}, F _ {1}, \alpha\right) (x, i) = \sum_ {f: F _ {1} (x)} i = 0 \rightarrow \alpha (x) ^ {- 1} (f)
\]

We note that the fibers over  \( (x,0) \)  and  \( (x,1) \)  are given by  \( F_{0}(x) \)  and  \( F_{1}(x) \) , respectively. Moreover, for each  \( w:F_{0}(x) \)  there is a map over  \( \lambda i.(x,i) \)  connecting w to  \( \alpha(x,w) \) . We show that  \( \mathrm{Gl}(F_{0},F_{1},\alpha) \)  is iso-inner over  \( I\times X \)  and that the aforementioned collection of edges make this family cocartesian with transport functor  \( \alpha \) .

In what follows, we assume that \(X, F_0, F_1\) and \(\alpha\) are all \(b\)-annotated. These proofs are all routine applications of orthogonality properties, combined with Lemma 2.13; we give details only in Appendix C.

Lemma 3.9. If X is simplicial, then  \( \mathrm{Gl}(F_{0}, F_{1}, \alpha) \)  is iso-inner.

Lemma 3.10. If X is a category, then  \( \mathrm{Gl}(F_{0}, F_{1}, \alpha) \)  is cocartesian.

Corollary 3.11. Cocartesian transport from \(\mathrm{Gl}(F_0,F_1,\alpha)(-,0)\) to \(\mathrm{Gl}(F_0,F_1,\alpha)(-,1)\) is given by \(\alpha\).

Corollary 3.12. The projection map \(\pi_0: \mathrm{Gl}(F_0, F_1, \alpha) \to F_1 \circ \pi_0\) is a cocartesian functor over \(X \times \mathbb{I}\).

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

## 4 The universe of amazingly cocartesian types

We now turn to the construction of Cat. As mentioned in the introduction, Cat will be a subtype of $\mathcal{U}$ and therefore must be classified by a proposition $\mathcal{U} \to \text{HProp}$. The most obvious choice of proposition is something akin to being cocartesian, but a moment's thought reveals this is unworkable: if we are to define a map isCocartFib : $\mathcal{U} \to \text{HProp}$, what should the input be cocartesian over? Cocartesianness is a property of families!

To fix this, we follow Licata et al. [18] as refined in the context of directed type theories [10, 42]. First, consider a general notion of fibration isFib$_X$: $\mathcal{U}^X \to \text{HProp}$. The goal is to define a predicate that witnesses fibrancy of a type $A$ viewed as a family over the entire ambient context. From isFib$_\mathbb{I}$ : $\mathcal{U}^\mathbb{I} \to \text{HProp}$, Lemma 2.9 yields precisely such a notion of fibrancy. Moreover, this stronger notion of fibration can be shown to agree with the classical notion when we restrict attention to b-annotated families.

We will now apply this construction, leveraging Theorem 3.8.

Lemma 4.1. If $A: X \to \mathcal{U}_\square$ is iso-inner, then hasLCCLifts($A$) and LCCLiftsCompose($A$) are propositions.

Let us write $i: \Delta^2 \to \mathbb{I}^2$ for the canonical inclusion. Using Lemma 2.9, we now transpose isInner($-\circ i$), hasLCCLifts, and LCCLiftsCompose($-\circ i$) to obtain elements of $\mathcal{U} \to \mathcal{U}$, namely aisInner, aHasLCCLifts, and aLCCLiftsCompose. Here we have used $i$ as, e.g., isInner takes $\Delta^2 \to \mathcal{U}$ not $\mathbb{I}^2 \to \mathcal{U}$.

We then define Cat:

$$\text{Cat} := \sum_{A: \mathcal{U}_\square} \begin{array}{l} \text{isRezk } A \times \text{aisInner } A \\ \times \text{aHasLCCLifts } A \times \text{aLCCLiftsCompose } A \end{array}$$

Lemma 4.2. Cat is a subtype of $\mathcal{U}_\square$.

Theorem 4.3. Cat is the base of the universal cocartesian family, i.e., for any $C$ : $\mathcal{U}$, we have $\langle b \mid C \to \text{Cat} \rangle \simeq \langle b \mid \sum_{E:C \to \mathcal{U}} \text{isCocart}(E) \rangle$.

PROOF. Fix $A$ : $X \to \mathcal{U}_\square$. Our goal is to show that $A$ factors through Cat if and only if $A$ is cocartesian. To prove this, let us consider the data involved in a factorization through Cat. By definition, this is equivalent to factoring through four distinct subobjects of $\mathcal{U}_\square$: those carved out by isRezk, aisInner, aHasLCCLifts, and aLCCLiftsCompose. In the latter three cases, we may analyze these subobjects using the transpositions used to define them.

For instance, if $A$ factors through $\sum_{B: \mathcal{U}_\square}$ aisInner($B$), then there is an element of the following type by Lemma 2.9:

$$\langle b \mid \prod_{x:X \bowtie} \text{isInner}(A \circ x \circ i) \rangle$$

Such an element exists if and only if $A$ is an inner fibration.

This reasoning applies to aHasLCCLifts and aLCCLiftsCompose so we may conclude that $A$ factors through Cat if and only if it is iso-inner, locally cocartesian, and locally cocartesian edges compose. The desired bi-implication is then Theorem 3.8. $\square$

## 5 The category of categories

In this section, we leverage Theorem 4.3 to prove the crucial properties of Cat. Namely, we prove Cat is Segal and Rezk, satisfies directed univalence as described in Section 1, and is simplicial. Combining these results together we show that Cat is a category and, in particular, the category of categories.

## 5.1 Classifying cocartesian fibrations

The main input to the proofs that Cat is Segal and Rezk is a characterization of cocartesian fibrations over $\Delta^n \times C$ where $C$ is a category. To see why, note that by Theorem 4.3, we know that $f$ : $X \times \Delta^n \to \text{Cat}$ is determined by a cocartesian family over $X \times \Delta^n$. By giving a precise description of such families, we obtain a more tractable version of, e.g., the restriction map $\langle b \mid \mathbb{I}^n \times \Delta^2 \to \text{Cat} \rangle \to \langle b \mid \mathbb{I}^n \times \Delta^2_1 \to \text{Cat} \rangle$. This version will be manifestly invertible, and so we can conclude that Cat is Segal. A key lemma in this process is the following:

Lemma 5.1. For $X$ : $\mathcal{U}$ a category and $A, B$ : $X \to \mathcal{U}$ cocartesian, a cocartesian functor $\alpha: \prod_{X:X} A(x) \to B(x)$ induces an equivalence of total categories $\widetilde{\alpha}: \widetilde{A} \simeq \widetilde{B}$ iff $\prod_{x:\widetilde{A}} \text{isEquiv}(\alpha(x))$ holds.

PROOF. Since cocartesian families are isofibrations, we know that $\widetilde{A}$ and $\widetilde{B}$ are both categories themselves. By Lemma 2.12, we check that $\widetilde{\alpha}$ is fully faithful, and essentially surjective.

Essential surjectivity is straightforward: given $(x, b)$ : $\widetilde{B}$, we take $(x, \alpha(x)^{-1}(b))$ as $\alpha$ is invertible on $b$ elements of $X$. To show that $\widetilde{\alpha}$ is fully faithful, note that transport induces an equivalence between $\mathbb{I} \to \widetilde{A}$ and $\sum_{x:\mathbb{I}\to X} \sum_{a_0:A(x0),a_1:A(x1)} \text{hom}_{A(x1)}(x_1 a_0, a_1)$. Since $\alpha$ preserves cocartesian edges, it therefore suffices to show that $\text{hom}_{A(x_1)}(x_1 a_0, a_1) = \text{hom}_{B(x_1)}(\alpha(x1, x_1 a_0), \alpha(x1, a_1))$ for $x$ : $\mathbb{I} \to X$ and $a_\epsilon$ : $A(x\epsilon)$. This holds as $\alpha(x1)$ is invertible. $\square$

Next we show that every cocartesian family $A$ : $X \times \mathbb{I} \to \mathcal{U}$, where $X$ is a category, is of the form $\text{Gl}(A(-, 0), A(-, 1), \lambda x. (x, -)_!)$. To this end, we note the following:

Lemma 5.2. Given $A$ as above, the transport map $\alpha = \lambda x. (x, -)_!$ is a cocartesian functor $A(-, 0) \to A(-, 1)$.

PROOF. Unfolding, this follows from the 3-for-2 condition which holds for cocartesian arrows [5, Proposition 5.1.8]. $\square$

Consequently, $B = \text{Gl}(A(-, 0), A(-, 1), \alpha)$ is a cocartesian family. Moreover, we can produce a map of families $A \to B$:

$$\text{glue}(x, i, a) = (x, i, ((x, i \vee -)_! a, \lambda p: i = 0. p_! a))$$

In words, we use cocartesian transport to move $a: A(x, i)$ to $A(x, 1)$ and, if $i = 0$ to begin with, record the original $a$ as well.

Lemma 5.3. glue: $\prod_{p:X \times \mathbb{I}} A(p) \to B(p)$ is a cocartesian functor.

PROOF. Following Buchholtz and Weinberger [5, Theorem 5.3.19], to check that glue is cocartesian, it suffices to check that the Beck-Chevalley natural transformation is invertible. By Lemma 2.11, it suffices to check this on $b$ elements where it is immediate. $\square$

Corollary 5.4. glue is an equivalence of cocartesian families.

PROOF. Applying Lemma 5.1, it suffices to check this equivalence fiberwise on $b$-annotated elements $(x, i)$ : $X \times \mathbb{I}$. In particular, it suffices to check that induces an equivalence on $b$-annotated elements of $\mathbb{I}$ which, by Axiom 4, consists only of 0 and 1. However, over 0 and 1 we see that glue is an equivalence: over 0, this is immediate and over 1 it follows from the observation that cocartesian transport over the identity arrow is the identity. $\square$

The ∞-category of ∞-categories in simplicial type theory

Thus, a cocartesian family $A \ni_{\flat} X \times \mathbb{I} \to \mathcal{U}$ is fully described by its restrictions to 0 and 1 along with the associated transport map. Combining this classification result in the case where $X = 1$ with Theorem 4.3, we obtain the directed univalence principle:

Corollary 5.5 (Directed univalence). If $A, B$ are $b$-elements of Cat, then there is a equivalence $\text{dua}: \hom_{\text{Cat}}(A, B) \simeq \langle b \mid A \to B \rangle$.

We note that, in general, we actually obtain an equivalence between $\langle b \mid X \times \mathbb{I} \to \text{Cat} \rangle$ and $\langle b \mid \sum_{A_0, A_1: \text{Cat}^X} A_0 \to^{\text{cc}} A_1 \rangle$. For what follows, we also require a similar accounting of cocartesian families $A \ni_{\flat} X \times \Delta^2 \to \mathcal{U}$. The story plays out in much the same way; we define $B_1$ as the following iterated glue type:

$$B_0 = \text{Gl}(A(-, \bar{0}), A(-, \bar{1}), \lambda x. (x, -)_!)$$

$$B_1 = \text{Gl}(B_0, A(-, \bar{2}) \circ \pi_0, \lambda x. (x, \bar{1} \vee - \wedge \bar{2})_! \circ \pi_0)$$

Combining Corollary 3.12 and Lemma 5.2 with Lemma 3.10, we conclude that $B_1$ is a cocartesian family $X \times \mathbb{I}^2 \to \mathcal{U}$. We then take $B$ to be the restriction of $B_1$ to $X \times \Delta^2$. The map of families glue considered previously easily generalizes to this $\Delta^2$ case and we may prove the following:

Lemma 5.6. The map $\text{glue}_2: \prod_{p: X \times \Delta^2} A p \to B p$ is cocartesian.

Again, an application of Lemma 5.1 allows us to conclude that $\text{glue}_2$ is an equivalence. Combining these steps once more with Theorem 4.3 once more, we conclude the following:

Corollary 5.7. Cocartesian transport induces an equivalence $\langle b \mid \text{Cat}^{X \times \Delta^2} \rangle \simeq \langle b \mid \sum_{A_0, A_1, A_2: \text{Cat}^X} A_0 \to^{\text{cc}} A_1 \times A_1 \to^{\text{cc}} A_2 \rangle$.

### 5.2 Cat is Segal and Rezk

Having characterized both cocartesian fibrations over $X \times \Delta^2$ and $X \times \mathbb{I}$ for all categories $X$, it is only slightly more work to prove that Cat is both Segal and Rezk.

Lemma 5.8. Cat is Segal.

PROOF. We wish to show that $\text{Cat}^{\Delta^2} \to \text{Cat}^{\Lambda_1^2}$ is an equivalence. Using Axiom 6, it suffices to show that the following map is an equivalence for all $n: \langle b \mid \mathbb{I}^n \times \Delta^2 \to \text{Cat} \rangle \to \langle b \mid \mathbb{I}^n \times \Lambda_1^2 \to \text{Cat} \rangle$.

Note that $\langle b \mid \mathbb{I}^n \times \Lambda_1^2 \to \text{Cat} \rangle$ is equivalent to the following:

$$\langle b \mid \mathbb{I}^n \times \mathbb{I} \to \text{Cat} \rangle \times_{\langle b \mid \mathbb{I}^n \to \text{Cat} \rangle} \langle b \mid \mathbb{I}^n \times \mathbb{I} \to \text{Cat} \rangle$$

This follows from the fact that $\langle b \mid - \rangle$ has an internal right adjoint ($\langle b \mid - \rangle$) together with the fact that $\Lambda_1^2 = \mathbb{I} \sqcup_1 \mathbb{I}$. Next, since $\mathbb{I}^n$ is a category, the results of the previous section allow us to rephrase the above map into the following:

$$\langle b \mid \sum_{A, B, C: \text{Cat}^{\mathbb{I}^n}} A \to^{\text{cc}} B \times B \to^{\text{cc}} C \rangle \to$$

$$\langle b \mid \sum_{A, B: \text{Cat}^{\mathbb{I}^n}} A \to^{\text{cc}} B \rangle \times_{\langle b \mid \text{Cat}^{\mathbb{I}^n} \rangle} \langle b \mid \sum_{B, C: \text{Cat}^{\mathbb{I}^n}} B \to^{\text{cc}} C \rangle$$

This being an equivalence follows immediately from the fact that $\langle b \mid - \rangle$ preserves pullbacks by virtue of Axiom 3.

Inspecting this proof, we see that if $P: \Lambda_1^2 \to \text{Cat}$, the resulting composed edge $f: \mathbb{I} \to \text{Cat}$ is a cocartesian fibration where $f(0) = P(\bar{0})$, $f(1) = P(\bar{2})$ and cocartesian transport from 0 to 1 is the composite of transporting in $P$ from $\bar{0}$ to $\bar{1}$ and then from $\bar{1}$ to $\bar{2}$.

Lemma 5.9. Cat is Rezk.

PROOF. We wish to show that all synthetic isomorphisms in Cat are equivalent to the identity. Once more, we apply Axiom 6 showing that the restriction map $\langle b \mid \mathbb{I}^n \to \text{Cat} \rangle \to \langle b \mid \mathbb{I}^n \times \mathbb{E} \to \text{Cat} \rangle$ is an equivalence. Commuting $\langle b \mid - \rangle$ with the pushout defining $\mathbb{E}$ once more, we may instead consider the map:

$$\langle b \mid \mathbb{I}^n \to \text{Cat} \rangle$$

$$\to \langle b \mid \text{Cat}^{\mathbb{I}^n \times \Delta^2} \rangle \times_{\dots} \langle b \mid \text{Cat}^{\mathbb{I}^n \times \mathbb{I}} \rangle \times_{\dots} \langle b \mid \text{Cat}^{\mathbb{I}^n \times \Delta^2} \rangle$$

Applying the results of the previous section and commuting $\langle b \mid - \rangle$ past pullbacks, we may recast the above:

$$\langle b \mid \mathbb{I}^n \to \text{Cat} \rangle$$

$$\to \langle b \mid \sum_{A, B: \text{Cat}^{\mathbb{I}^n}} \sum_{f: A \to^{\text{cc}} B} \sum_{g, h: B \to^{\text{cc}} A} f \circ g = \text{id} \times h \circ f = \text{id} \rangle$$

However, since Cat is a subtype of $\mathcal{U}$ it satisfies the univalence axiom. The result then follows from the observation that the data imposed on $f$ ensures that it is a family of equivalences.

### 5.3 Cat is simplicial

Our remaining task is to show that Cat is simplicial. Unfortunately, this is far from immediately obvious. After all, Cat is defined using the amazing right adjoint to $\mathbb{I} \to -$, which is the primary source of non-simplicial types. Fortunately, in this case we may use Theorem 4.3 to produce a left section to $\eta: \text{Cat} \to \boxtimes\text{Cat}$ and this implies that $\eta$ is an equivalence [34, Lemma 1.20].

To begin with, we record the following lemma:

Lemma 5.10. The commuting square between $\text{Cat}_{\bullet} = (\sum_{A: \text{Cat}} A) \to \text{Cat}$ and $\boxtimes\text{Cat}_{\bullet} \to \boxtimes\text{Cat}$ induced by $\eta$ is cartesian.

PROOF. Unfolding definitions and comparing fibers, this follows from the fact that each $A: \text{Cat}$ is simplicial and $\boxtimes$ is lex.

Next, we note that if $\boxtimes\text{Cat}_{\bullet} \to \boxtimes\text{Cat}$ represents a cocartesian family itself, then there must be a unique classifying map $\boxtimes\text{Cat} \to \text{Cat}$ and, pasting together the relevant pullback squares, we obtain the following composite pullback diagram:

![img-2.jpeg](img-2.jpeg)

By the univalence property of Cat, this bottom composite must be the identity. Consequently, the classifying map $\boxtimes\text{Cat} \to \text{Cat}$ is the required left inverse to the unit. All that remains, therefore, is to prove that $\boxtimes\text{Cat}_{\bullet} \to \boxtimes\text{Cat}$ is a cocartesian fibration.

To prove this we will use Axiom 7 along with Lemma 2.13 and Proposition 3.5. First, we must note that $\boxtimes\text{Cat}$ and $\boxtimes\text{Cat}_{\bullet}$ are both categories. We therefore record the following result:

Lemma 5.11. If $X \ni_{\flat} \mathcal{U}$ is Segal and Rezk, then $\boxtimes X$ is a category.

Lemma 5.12. The family $\boxtimes\text{Cat}_{\bullet} \to \boxtimes\text{Cat}$ is cocartesian.

PROOF. As a map between categories, it is automatically isonner and simplicial. It therefore suffices to prove that the comparison map $(\boxtimes\text{Cat}_{\bullet})^{\mathbb{I}} \to (\boxtimes\text{Cat})^{\mathbb{I}} \times_{\boxtimes\text{Cat}} \boxtimes\text{Cat}_{\bullet}$ has a left adjoint right inverse. For concision, we write $C = \boxtimes\text{Cat}$ and, commute $\boxtimes$ with $\Sigma$ to replace $\boxtimes\text{Cat}_{\bullet}$ with $E = \Sigma_{A: \boxtimes\text{Cat}} \hat{\boxtimes} A$ in what follows.

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

We may use Lemma 2.13 so that it suffices to check that this property holds when restricted to b-annotated elements of $C^{\mathbb{I}} \times_C E$. Accordingly, we may fix $A :_{\flat} \mathbb{I} \to C$ along with an element $a_0 :_{\flat} A 0$. By Axiom 7, we may assume that $A = \eta \circ A'$ and $a_0 = \eta(a'_0)$ for some unique $A' :_{\flat} \mathbb{I} \to \text{Cat}$ and $a'_0 :_{\flat} A$.

Since $\text{Cat}_{\bullet} \to \text{Cat}$ is cocartesian, we lift $A', a'_0$ to a cocartesian morphism $a' :_{\flat} (i : \mathbb{I}) \to A' i$ with $p' : a' 0 = a'_0$. We now argue that $a = \eta \circ a' : (i : \mathbb{I}) \to \widehat{\mathbb{Q}} A i$ and the induced equality $p : a 0 = a_0$ is the desired universal lift over $A, a$.

After appropriately massaging the input data, it suffices to show that if we are given $H :_{\flat} \Delta^2 \to \square \text{Cat}$ and a lift of this map $h :_{\flat} (t : \Delta_0^2) \to \widehat{\square} H(t)$. There are a handful of paths relating these two $a$ and $A$, but after induction we may definitionally identify (1) $H(0, -)$ with $A$ (2) $h(0, -)$ with $a$. We must show that $h$ extends uniquely to some $\hat{h} : (t : \Delta^2) \to \widehat{\square} H(t)$. By Axiom 7, we may once more factor $H$ and $h$ through Cat whereby the result is an immediate consequence of our construction of $a'$ as a cocartesian lift. □

Corollary 5.13. Cat is a category.

## 6 Full straightening-unstraightening

In this section, we prove the Lurie's straightening-unstraightening theorem which states that for a category $C :_{\flat} \mathcal{U}$, the type $C \to \text{Cat}$ is equivalent to the subcategory of $\text{Cat}_{/C}$ (that is, $\sum_{f: \text{Cat}^{\mathbb{I}}} f(1) = C$) restricted such that its 0- and 1-cells are given cocartesian families and cocartesian functors. Accordingly, for the remainder of this section let us fix $C :_{\flat} \mathcal{U}$ a category.

To do this, we will construct a map $U : (C \to \text{Cat}) \to \text{Cat}_{/C}$ and prove that it is (1) an embedding such that (2) its image on b-annotated elements $C \to \text{Cat}$, and $\mathbb{I} \to (C \to \text{Cat})$ satisfies precisely the above criteria. From this, we show that $(C \to \text{Cat}) \to \text{Cat}_{/C}$ satisfies the expected universal property for the subcategory $\text{Cocart}(C)$ of cocartesian families over $C$ (Corollary 6.6).

Remark 6.1. The material in this section closely follows Cisinski et al. [6] with only minor alterations to make it more convenient in $\text{TT}_{\square}$. In particular, it is from there that we learned of this method of constructing the unstraightening functor and characterizing its image. That such an adaptation is possible is expected but encouraging: the axiomatic approach given by op. cit. is intended to give high-level arguments which can be translated into formal systems satisfying their axioms and our construction of Cat ensures that $\text{TT}_{\square}$ satisfies all the relevant axioms for this argument.

Remark 6.2. We avoid explicitly constructing $\text{Cocart}(C)$ merely to avoid the detour of describing the construction of non-full subcategories. Such constructions are possible using e.g., $(-)_{\mathbb{I}}$.

### 6.1 The unstraightening map

We begin by constructing a map $U$ from $C \to \text{Cat}$ to $\text{Cat}_{/C}$. We break this process into several steps. We begin by considering two particular cocartesian families over $C \to \text{Cat}$:

$$E(f) = \sum_{c:C} f(c) \quad B(f) = C$$

These are both cocartesian families over $C$ and the canonical projection is a cocartesian map $\pi_0 : E \to {}^{cc} B$ as well—and therefore a cocartesian functor. We may therefore glue these together to form a cocartesian family: $\text{Gl}(E, B, \pi_0) : (\text{Cat}^C) \times \mathbb{I} \to \text{Cat}$. First,

let us compute $\text{Gl}(E, B, \pi_0)(-, 1)$ and observe that it is canonically identified to $\lambda_- C$, via the following family of paths:

$$\Phi = \lambda f. \text{ua}(\pi_1) : \prod_{f:C \to \text{Cat}} \text{Gl}(E, B, \pi_0)(f, 1) = C$$

By transposing and using this identification, we obtain:

$$U : (C \to \text{Cat}) \to \text{Cat}_{/C}$$

$$U = \lambda f. (\text{Gl}(E, B, \pi_0)(f, -), \Phi(f))$$

### 6.2 The image of the unstraightening map

Our next task to identify the image of $U$ and, in particular, to show that it is precisely the category of cocartesian families over $C$ and cocartesian functors between them. We therefore compute fibers of $\langle \flat \mid \text{Cat}^C \rangle \to \langle \flat \mid \text{Cat}_{/C} \rangle$ and $\langle \flat \mid \mathbb{I} \to \text{Cat}^C \rangle \to \langle \flat \mid \mathbb{I} \to \text{Cat}_{/C} \rangle$.

In particular, we will show that the fiber over $p :_{\flat} \text{Cat}_{/C}$ is precisely the proposition stating whether $p$ is cocartesian and over $f :_{\flat} \mathbb{I} \to \text{Cat}_{/C}$ it corresponds to the triple of propositions requiring $f(0)$ and $f(1)$ to be cocartesian and $f$ itself to induce a map of cocartesian families. In light of the Segal condition, this characterizes the fibers over arbitrary simplices and, via Axiom 6 and the simpliciality of Cat, proves that $U$ is an embedding. Moreover, our description of the fibers shows that the resultant subcategory of $\text{Cat}_{/C}$ is precisely as described at the beginning of this section.

Lemma 6.3. The fiber of $U$ over $p :_{\flat} \text{Cat}_{/C}$ is a proposition inhabited iff $p$ is cocartesian.

PROOF. Post-composing with directed univalence, we may identify a fiber of $U$ with a fiber of the map:

$$U' : \langle \flat \mid C \to \text{Cat} \rangle \to \langle \flat \mid \sum_{E: \text{Cat}} E \to C \rangle$$

Consider a category $E :_{\flat} \text{Cat}$ and a function $\pi_E :_{\flat} E \to C$. Our goal is to compute the fiber $\sum_{f: \langle \flat | C \to \text{Cat} \rangle} U'(f) = \text{mod}_{\flat}(E, \pi_E)$.

Unfolding $U'$, an element $f :_{\flat} C \to \text{Cat}$ is sent to $(E, \pi_E)$ if and only if we have an equivalence $e :_{\flat} E \simeq \sum_{c:C} f(c)$ and an equation $p :_{\flat} \pi_E = \pi_1 \circ e$. By another application of univalence, this is equivalent to requiring that $\langle \flat \mid \pi_E^{-1}(-) = f \rangle$, so the fiber amounts to $\sum_{f:_{\flat} C \to \text{Cat}} \langle \flat \mid \pi_E^{-1} = f \rangle$. This is a proposition by Proposition 2.8 and by Theorem 4.3 inhabited iff $\pi_E$ is a cocartesian family. □

Lemma 6.4. The fiber of $U$ over $f :_{\flat} \mathbb{I} \to \text{Cat}_{/C}$ is a proposition inhabited iff $f$ is a cocartesian functor between cocartesian families.

PROOF. Rearranging equations, we may identify $\langle \flat \mid \mathbb{I} \to \text{Cat}_{/C} \rangle$ with $\langle \flat \mid \sum_{h: \Delta^2 \to \text{Cat}} h(\bar{2}) = C \rangle$ which we may then identify via directed univalence with $\langle \flat \mid \sum_{E, F: \text{Cat}} E \to F \times F \to C \rangle$. Post-composing $U$ with these maps, we instead consider the following:

$$U' : \langle \flat \mid \mathbb{I} \to \text{Cat}^C \rangle \to \langle \flat \mid \sum_{E, F: \text{Cat}} E \to F \times F \to C \rangle$$

Consider categories $E, F :_{\flat} \text{Cat}$ and functions $\pi_F :_{\flat} F \to C$ and $\alpha :_{\flat} E \to F$. Our goal is to compute the fiber of $U'$ over this data.

Unfolding, an element $h :_{\flat} \mathbb{I} \to \text{Cat}^C$ is sent to $E, F, \pi_F$ if and only if we have the following:

- an equivalence $e_0 :_{\flat} E \simeq \sum_{c:C} h(0, c)$,
- an equivalence $e_1 :_{\flat} F \simeq \sum_{c:C} h(1, c)$,
- a path $\phi :_{\flat} e_1 \circ \alpha = \beta \circ e_0$ where $\beta = \lambda c$. $(-, c)_!$ is given by the cocartesian transport of $h$
- a path $\phi :_{\flat} \pi_F = \pi_0 \circ e_1$.

The ∞-category of ∞-categories in simplicial type theory

Once more using univalence, we are reduced to b-annotated equation between maps of families over C (i.e. C → Σ_{A,B:U} B^A):

$$\lambda c. \pi_0 : \prod_{c:C} (\sum_{f:\pi_F^{-1}(c)} \alpha^{-1}(f)) \to \pi_F^{-1}(c)$$

$$\lambda c. (-, c) : \prod_{c:C} h(0, c) \to h(1, c)$$

Since ⟨b | I → Cat^C⟩ embeds into ⟨b | C → Σ_{A,B:U} B^A⟩ by directed univalence, Proposition 2.8 ensures this fiber over (E, F, π_F) is a proposition. The same analysis shows that it is inhabited iff π_F ∘ α and π_E are cocartesian and α is a map of cocartesian families. □

Corollary 6.5. The map U : (C → Cat) → Cat/C is an embedding.

In fact, in light of our identification of the fibers of U we may also characterize when a functor lifts along it. This is, in essence, the universal property of Cocart(C) mentioned earlier:

Corollary 6.6 (Straightening–unstraightening). If D :_b U is a category, a map f :_b D → Cat/C lifts along U to Cat^C if and only if

- (1) for each d :_b D, the functor f(d) is a cocartesian family.
- (2) for each d :_b I → D, the functor induced by f ∘ d : I → Cat/C is a cocartesian functor between the cocartesian families.

## 7 Examples

We have thus far focused on the construction of Cat and verifying its essential properties and so we close by discussing some of the new examples and category theory unlocked by Cat. For reasons of space, we content ourselves with only sketching several examples.

### 7.1 Subcategories of Cat

We begin by noting that since every covariant family is cocartesian, there is a unique map from the base of the universal covariant family S to the base of the universal cocartesian family Cat. This is the inclusion of groupoids into categories.

Lemma 7.1. The map i : S → Cat is fully faithful and possesses both left and right adjoints: |−| + i + (−)^∞.

PROOF SKETCH. The second half of this statements follows from Lemma 2.13. In particular, we use this lemma to extend the point-wise assignments of X :_b Cat ↦ ⟨b | X⟩ : S and X :_b Cat ↦ ○_grpd X : S to functors Cat → S. The fact that i is fully faithful is then immediate from Axiom 5: if X is a groupoid then the unit X → ⟨b | i(X)⟩ is an equivalence. It is a standard argument that a unit being invertible implies the left adjoint is fully faithful. □

Many other interesting categories exist as full subcategories of Cat. For instance, we may isolate univalent 1-categories as the full subcategory of Cat [10, §7] given by the following predicate:

$$\text{is1Cat} : (\flat \mid \text{Cat}) \to \text{HProp}$$

$$\text{is1Cat}(C) = \prod_{a,b:\flat,C} \text{isSet}(\hom_C(a, b))$$

Similar definitions immediately yield (n, 1)-categories for all n. Notably, by restricting to n = −1 we obtain the category of partial orders and, restricting further to linear partial orders, the simplex category Δ ⇔ Cat. In fact, the same argument as was used to S ⇔ Cat allows us to prove the following:

Lemma 7.2. The inclusion of Cat_n ⇔ Cat is a right adjoint.

PROOF SKETCH. One adapts Lemma 7.1 to use the modality nullifying the maps Λ_1^2 → Λ^2, B → 1, and ∂Δ^(n+2) → Δ^(n+2). □

Towards algebraic K-theory. For a small example of how these ingredients might be combined to build a useful and important construction in higher category theory, we turn our attention to monoidal categories. Let us write [n] for the element of Δ realizing the linear order {0 ≤ ··· ≤ n}. Using Corollary 5.5, we define ρ_n^1 : hom([1], [n]) which sends 0 ≤ 1 to {i ≤ i + 1} ⊆ [n].

Definition 7.3. A monoidal category C^⊗ : Cat^⟨op|Δ⟩ is a functor where (ρ_n^1, …, ρ_n^n) : C^⊗([n]) → C^⊗([1]) × ··· × C^⊗([1]) is an equivalence for all n.

Replacing Cat by S in the above gives the definition of an E_1-monoid: a homotopy-coherent monoid [10, §7].

Definition 7.4. The category of monoidal categories MCat is the full subcategory of ⟨op | Δ⟩ → Cat spanned by monoidal categories.

We readily adapt this definition to (1) the category of E_1-monoids Mon as a subcategory of S^⟨op|Δ⟩ and to (2) the category of monoidal 1-categories MCat_1 as a subcategory of Cat_1^⟨op|Δ⟩.

As both (−)^∞ : Cat → S and the inclusion Cat_1 → Cat are right adjoints, they preserve finite products and therefore post-composing by these maps induces functors MCat → Mon and MCat_1 → MCat. We note next that—viewing Mon as a subcategory of S^⟨op|Δ⟩—we may take the colimit of M : Mon to obtain a space lim M. In fact, this space is canonically pointed: the initial object in Mon is the functor const 1 and lim const 1 = 1. Finally, regarding the loop-space functor as a map Ω : S_* → S_* we define k to be the following chain of functors:

$$k : \text{MCat}_1 \to \text{MCat} \to \text{Mon} \to S_* \to S_*$$

We may now define the simplest form of algebraic K-theory:

Definition 7.5 (Quillen). The ith K-group of a monoidal 1-category C^⊗ is the ith homotopy group K_i(C^⊗) = π_i(k(C^⊗)).

Notably, with Cat to hand all of these definitions are quite conceptual and automatically functorial. We emphasize that this is only a first step towards realizing K-theory. We leave it to future work to show e.g., that modules over a ring are a monoidal category.

### 7.2 The structure homomorphism principle

To give a different class of examples involving Cat, we turn to the structure homomorphism principle. This is the directed enhancement of HoTT's structure identity principle. This principle states that by taking ordinary type-theoretic definitions of objects in a certain category but using Cat or S instead of U, we obtain the correct synthetic category with the expected homomorphisms.

For a simplest example of this phenomena:

Lemma 7.6. The type Σ_{A:Cat} A is the lax slice 1 ∮ Cat i.e. its objects are pointed categories (C, c) and when (C, c), (D, d) :_b Σ_{A:Cat} A morphisms hom((C, c), (D, d)) consist of functions f : C → D together with a morphism hom(f(c), d).

PROOF. As Σ_{A:Cat} A is the total space of the cocartesian family Cat → U, it is a category. The characterization of objects is immediate from Proposition 2.8. For morphisms, we use Corollary 5.5

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

with the factorization of a morphism in a total space of a cocartesian family into a cocartesian map followed by a vertical map. □

More generally, one may show that $\sum_{A:\text{Cat}} A^C$ is the lax slice category $C \nmid \text{Cat}$ for any $C \ni_0 \text{Cat}$.

For a more sophisticated example, consider the following type built using the right adjoint to $i: S \to \text{Cat}$.

$$\text{Cat}_{\text{smarked}} = \sum_{C:\text{Cat}} ((\mathbb{I} \to C)^\simeq \text{Bool})$$

By directed univalence applied to $S$, this type is equivalent to $\sum_{C:\text{Cat}} \text{hom}((\mathbb{I} \to C)^\simeq, \text{Bool})$ which is easily seen to be a category. Objects of $\text{Cat}_{\text{smarked}}$ are pairs of (1) a category $C \ni_0 \text{Cat}$ and (2) a (decidable) predicate $\phi_C$ on the groupoid $\langle b \mid \mathbb{I} \to C \rangle$ (recall that $(-)^\simeq$ extends $\langle b \mid - \rangle$). The morphisms in $\text{Cat}_{\text{smarked}}$ are then functors between the underlying category $f: C \to D$ such that $\phi_C = \phi_D \circ f$. This is almost the category of marked categories (the category of categories with a distinguished class of morphisms along with functors preserving these morphisms) but the morphisms are off: we should expect only that $\phi_C$ implies $\phi_D \circ f$.

To rectify this, we should replace Bool with the non-discrete category $\mathbb{I}$. Just as with $\sum_{A:\text{Cat}} A$, this introduces the required laxity in the morphism. Unfortunately, however, we can no longer rely on directed univalence for $S$ in this case; we must use Corollary 5.5 which only applies to $b$-annotated elements. This makes it much more difficult to prove that $\sum_{C:\text{Cat}} ((\mathbb{I} \to C)^\simeq \to \mathbb{I})$ is a category. Systematically handling these "mixed-variance" applications of SHP requires more exploration of exponentiable functors [2]; we must show that (co)cartesian functors are exponentiable. We defer this to future work and instead work relative to the following conjecture:

Conjecture 7.7. If $C \ni_0 \text{Cat}$ then $- \to C: S \to \text{Cat}$ is cartesian where the cartesian lift of $f \ni_0 \text{hom}_S(A, B)$ to $(B, \phi)$ is $(A, \phi \circ f)$.

The difficult piece of this conjecture is establishing that $- \to C$ is an iso-inner family, with the cartesian lifts following directly from the dual of Proposition 3.5. To see this enables further applications of SHP, note that choosing $C = \mathbb{I}$ yields:

Lemma 7.8. The category $\text{Cat}_{\text{marked}} = \sum_{C:\text{Cat}} ((\mathbb{I} \to C)^\simeq \to \mathbb{I})$ is the category of marked categories.

PROOF. We discuss only the characterization of synthetic morphisms. First, $\pi_0: (\sum_{C:\text{Cat}} ((\mathbb{I} \to C)^\simeq \to \mathbb{I})) \to \text{Cat}$ is a pullback of the family described in Conjecture 7.7 and therefore cartesian. We may then factor any morphism $f \ni_0 \text{hom}_{\text{Cat}_{\text{marked}}}((C, \phi_C), (D, \phi_D))$ uniquely into a cartesian lift of a map $f_0: C \to D$ along with a morphism $f_1: \text{hom}_\mathbb{I}(\phi_C, \phi_D \circ ((f_0)_*)^\simeq)$. This is precisely the data of a morphism of marked categories. □

## 8 Conclusions and related work

In this work, we have constructed a subtype of the universe $\text{Cat} \hookrightarrow \mathcal{U}$ and shown that it gives rise to the category of categories within STT. In particular, we have shown that it is simplicial, Segal, and Rezk and characterized its objects and mapping spaces to be categories and functors. To give an even more precise characterization of Cat, we then prove Lurie's straightening-unstraightening theorem. Finally, we show how results from $\infty$-category theory can now be proved (e.g., various adjunctions between $S$ and Cat) in short order and use the particular nature of type theory (in the form of the SHP) to construct new $\infty$-categories quickly and intuitively.

### 8.1 Related work

There has been a large amount of work on both directed approaches to type theory and straightening-unstraightening generally. Our work fits into the broader tradition of directed type theory, specifically the line of work initiated by Riehl and Shulman [33] on simplicial type theory [2, 3, 5, 11, 32, 37, 43-45].

In this specific context, Cat fills a major missing piece in the foundations of STT and allows for new applications to, for instance, higher algebra and monoidal category theory. For directed type theory generally, we believe this construction should make it possible to more directly provide semantics to "fully directed" type theories [1, 14, 17, 24-29, 40]. In particular, a model of those type theories which adequately models $\infty$-categories can now be constructed by a syntactic translation to $\text{TT}_{\mathbb{S}_2}$. The presence of Cat, in particular, means that the features supported by $\text{TT}_{\mathbb{S}_2}$ should be adequate to encode all of those presently considered.

Other approaches to amazing right adjoints. The use of the right adjoint to $\mathbb{I} \to -$ to construct a universal family with suitable structure dates back to Licata et al. [18], where it was used in the context of cubical type theory. While, for instance, Riley [35] proposed a more refined version of this technique which gave a more judgmental account of the amazing right adjoint, our approach closely follows Licata et al. [18] and, especially, its adaptation to directed type theory by Weaver and Licata [42]. In particular, op. cit. use this methodology to construct a directed univalent universe of groupoids in bicubical type theory. Gratzer et al. [10] then introduced $\text{TT}_{\mathbb{S}_2}$ in order to adapt this methodology to apply to standard $\infty$-categories and further prove that the universe of groupoids is a category. Our work carries this program further forward by constructing not just a category of groupoids via a universal covariant family, but a category of categories via a universal cocartesian family. This is a substantial step-cocartesian families enjoy fewer nice properties than covariant families and this complicates various aspects of the proof e.g., the argument that Cat is simplicial.

Existing proofs of straightening-unstraightening. Since Lurie's original proof [19], two additional proofs have been published in the literature. The first is given by Hebestreit et al. [12] and is a much more directed and succinct version of Lurie's proof, but still employs the same fundamental approach. In particular, the main result is a Quillen equivalence of two model categories rather than an intrinsically $\infty$-categorical or synthetic approach.

More closely related is the work of Cisinski and Nguyen [7] which develops a universal cocartesian family as we do and uses this to prove straightening-unstraightening, directed univalence, and similar. The proof strategy of our approach is quite similar to op. cit.: a straightforward proof of the universal fibration and a more lengthy argument that its base is a category. In fact, op. cit. is influenced by various standard techniques in the semantics of type theory. A crucial difference between our approaches, however, is the ambient framework used to manage $\infty$-categories. Unlike our approach, Cisinski and Nguyen [7] use quasicategories along with various model categorical tools from the Joyal and marked model structures. This is in contrast with our more synthetic approach, which uses model categories only indirectly via Theorem 2.10.

The ∞-category of ∞-categories in simplicial type theory

Particularly in light of the last proof, we feel that our approach is an interesting example in how higher category theory can influence the development of type theory (through HoTT) which can in turn contribute new techniques and proofs to higher category theory. We also hope that the model-independent nature of our proof will result in a result which can be applied to exotic situations such as internal ∞-categories in an ∞-topos [21, 22].

## 8.2 Future work

While this work has constructed the category of categories, much work still remains to be done around (1) the use of Cat in synthetic ∞-category theory and (2) deriving a computational account of this type theory, following on the work of Weaver and Licata [42]. For the first point, we believe that higher algebra and the theory of operads is particularly interesting to study in this regard, as the existing foundations of the theory [20] are notoriously technical and rely on intricate simplex-by-simplex arguments. For the second, we believe that the machinery of our argument could be adapted to bicubical type theory which would, at the very least, provide a constructive model of our argument.

## References

[1] Benedikt Ahrens, Paige Randall North, and Niels van der Weide. 2023. Bicategorical type theory: semantics and syntax. Mathematical Structures in Computer Science 33, 10 (10 2023), 868–912. https://doi.org/10.1017/s0960129523000312
[2] César Bardomiano Martínez. 2025. Exponentially functions between synthetic ∞-categories. Mathematical Structures in Computer Science 35 (2025). https://doi.org/10.1017/S0960129525100339
[3] César Bardomiano Martínez. 2025. Limits and colimits in synthetic ∞-categories. Mathematical Structures in Computer Science 35 (2025). https://doi.org/10.1017/S0960129525100248
[4] Inge Blechschmidt. 2023. A general Nullstellensatz for generalized spaces. https://rawgit.com/blech/internal-methods/mastri/paper-qcob.pdf Draft.
[5] Ulrik Buchholtz and Jonathan Weinberger. 2023. Synthetic fibered (∞, 1)-category theory. Higher Structures 7 (2023), 74–165. Issue 1. https://doi.org/10.21136/HS.2023.04
[6] Denis-Charles Cisinski, Bastiaan Cnossen, Kim Nguyen, and Tashi Walde. 2025. Synthetic Category Theory. https://drive.google.com/file/d/1Kaq7watGGSxvjqw9qHjm6SDPFJ2-0o/view Book in progress.
[7] Denis-Charles Cisinski and Hoang Kim Nguyen. 2022. The universal coCartesian fibration. arXiv:2210.08945 [math.CT]
[8] Daniel Gratzer. 2023. Syntax and semantics of modal type theory. Ph. D. Dissertation. Aarhus University.
[9] Daniel Gratzer, G.A. Kavvos, Andreas Nuyts, and Lars Birkedal. 2020. Multimodal Dependent Type Theory. In Proceedings of the 35th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS '20). ACM. https://doi.org/10.1145/3373718.3394736
[10] Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz. 2024. Directed univalence in simplicial homotopy type theory. https://arxiv.org/abs/2407.09146
[11] Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz. 2025. The Yoneda embedding in simplicial type theory. In 40th Annual ACM/IEEE Symposium on Logic in Computer Science, LICS 2025, Singapore, June 23-26, 2025. IEEE, 127–142. https://doi.org/10.1109/LICS65433.2025.00017
[12] Fabian Hebestreit, Gijs Heuts, and Jaco Ruit. 2025. A short proof of the straightening theorem. Transactions of the American Mathematical Society, Series B 12, 19 (05 2025), 697–747. https://doi.org/10.1090/htras/225
[13] André Joyal. 2008. The Theory of Quasi-Categories. Online. https://math.uchicago.edu/~may/PEOPLE/JOYAL/0newcategories.pdf
[14] G.A. Kavvos. 2019. A quantum of direction. Online. https://seis.bristol.ac.uk/~tz0061/papers/meio.pdf
[15] Anders Kock. 2014. Duality for generic algebras. https://arxiv.org/abs/1412.6660
[16] F. William Lawvere. 2007. Axiomatic cohesion. Theory and Applications of Categories 19, 3 (2007), 41–49. http://www.tac.mta.ca/tac/volumes/19/3/19-03.pdf
[17] Daniel R. Licata and Robert Harper. 2011. 2-Dimensional Directed Type Theory. Electronic Notes in Theoretical Computer Science 276 (09 2011), 263–289. https://doi.org/10.1016/j.entcs.2011.09.026
[18] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. 2018. Internal Universes in Models of Homotopy Type Theory. In 3rd International Conference on Formal Structures for Computation and Deduction (FSCD 2018) (Leibniz International Proceedings in Informatics (LIPics), Vol. 108). Hélène Kirchner (Ed.). Schloss Dagstuhl – Leibniz-Zentrum für Informatik, Dagstuhl, Germany, 22:1–22:17. https://doi.org/10.4230/LIPics.FSCD.2018.22
[19] Jacob Lurie. 2009. Higher Topos Theory. Princeton University Press.
[20] Jacob Lurie. 2017. Higher Algebra. https://www.math.ias.edu/~lurie/papers/HA.pdf Book draft.
[21] Louis Martini. 2022. Cocartesian fibrations and straightening internal to an ∞-topos. arXiv:2204.00295 [math.CT]
[22] Louis Martini and Sebastian Wolf. 2025. Presentability and topoi in internal higher category theory. arXiv:2209.05103 [math.CT]
[23] David Jaz Myers and Mitchell Riley. 2023. Commuting Cohesions. arXiv:2301.13780 [math.CT]
[24] Jacob Neumann. 2025. A Generalized Algebraic Theory of Directed Equality. Ph. D. Dissertation. University of Nottingham.
[25] Jacob Neumann. 2025. A Judgmental Construction of Directed Type Theory. arXiv:2510.17494 [cs.LO] https://arxiv.org/abs/2510.17494
[26] Jacob Neumann and Thorsten Altenkirch. 2024. The Category Interpretation of Directed Type Theory. Online. https://jacobnen.github.io/research/preprints/catModel-2024.pdf
[27] Paige Randall North. 2018. Towards a directed homotopy type theory. arXiv:1807.10566 [cs.LO] https://arxiv.org/abs/1807.10566
[28] Andreas Nuyts. 2015. Towards a Directed Homotopy Type Theory based on 4 Kinds of Variance. Master's thesis. KU Leuven.
[29] Andreas Nuyts. 2020. A Vision for Natural Type Theory. https://anuyts.github.io/files/natrt-vision.pdf
[30] Ian Orton and Andrew M. Pitts. 2018. Axioms for Modelling Cubical Type Theory in a Topos. Logical Methods in Computer Science 14, 4 (2018). https://doi.org/10.23638/LMCS-14(4.23)2018 arXiv:1712.04864
[31] Charles Reik. 2001. A model for the homotopy theory of homotopy theory. Trans. Amer. Math. Soc. 353, 3 (2001), 973–1007. https://doi.org/10.1090/S0002-9947-00-02653-2
[32] Emily Riehl. 2025. Synthetic perspectives on spaces and categories. arXiv:2510.15795 [math.CT]
[33] Emily Riehl and Michael Shulman. 2017. A type theory for synthetic ∞-categories. Higher Structures 1 (2017), 147–224. Issue 1. https://doi.org/10.21136/HS.2017.06
[34] Egbert Rijke, Michael Shulman, and Bas Spitters. 2020. Modalities in homotopy type theory. Logical Methods in Computer Science 16, 1 (2020). https://doi.org/10.23638/LMCS-16(1.2)2020
[35] Mitchell Riley. 2024. A Type Theory with a Tiny Object. arXiv:2403.01939 [math.CT]
[36] Michael Shulman. 2018. Brouwer's fixed-point theorem in real-cohesive homotopy type theory. Mathematical Structures in Computer Science 28, 6 (2018), 856–941. https://doi.org/10.1017/S0960129517000147
[37] Michael Shulman. 2019. All (∞, 1)-toposes have strict univalent universes. arXiv:1904.07004 [math.AT]
[38] Jan M. Smith. 1989. Propositional functions and families of types. Notre Dame Journal of Formal Logic 30, 3 (06 1989). https://doi.org/10.1305/ndjfl-1093635159
[39] The Univalent Foundations Program. 2013. Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study. https://homotopytypotheory.org/book
[40] Michael Warren. 2013. Directed type theory. Online. https://www.ias.edu/video/univalent/1213/0410-MichaelWarren Seminar talk.
[41] Matthew Zachary Weaver. 2024. Bicubical Directed Type Theory. Ph. D. Dissertation. Princeton University. http://arbs.princeton.edu/ark:/8835/dsp03r5f5dg778
[42] Matthew Z. Weaver and Daniel R. Licata. 2020. A Constructive Model of Directed Univalence in Bicubical Sets. In Proceedings of the 35th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS '20). ACM. https://doi.org/10.1145/3373718.3394794
[43] Jonathan Weinberger. 2022. A Synthetic Perspective on (∞, 1)-Category Theory: Fibrational and Semantic Aspects. Ph. D. Dissertation. Technische Universität Darmstadt. https://doi.org/10.26883/tuprints-00020716
[44] Jonathan Weinberger. 2024. Internal sums for synthetic fibered (∞, 1)-categories. Journal of Pure and Applied Algebra 228, 9 (09 2024), 107659. https://doi.org/10.1016/j.jpja.2024.107659
[45] Jonathan Weinberger. 2024. Two-sided cartesian fibrations of synthetic (∞, 1)-categories. Journal of Homotopy and Related Structures 19, 2 (06 2024). https://doi.org/10.1007/s40062-024-00348-3

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

## A Formal syntax of MTT

We provide a succinct description of the formal syntax of MTT in this section. Since most connectives of type theory ($\Sigma$, $\Pi$, etc.) are not impacted by modalities, we focus only on those rules which must be changed. These are (1) some aspects of the substitution calculus and (2) the rules for modal types are modal $\Pi$ types. We assume a mode theory $\mathcal{M}$ which has 1 object and which is enriched in posets, as is in this paper.

First, we extend contexts with the following new forms:

$$\frac{\vdash \Gamma \text{ cx} \quad \mu : m \to m \in \mathcal{M}}{\vdash \Gamma.\{\mu\} \text{ cx}} \quad \frac{\vdash \Gamma \text{ cx} \quad \Gamma.\{\mu\} \vdash A \text{ type}}{\vdash \Gamma.(\mu \mid A) \text{ cx}}$$

Our previous notation with formal divisions was really syntactic sugar for these operations. In particular, $x :_{\mu/\nu} A, y :_{\text{id}/\nu} B, z : C$ becomes $1.(\mu \mid A).(\text{id} \mid B).\{\nu\}.C$. Notably, while $-/\mu$ was mere notation for the paper, it is actually the primitive operation in MTT. Any context built using either notation using the rules of the system is translatable.

We then add several new to the substitution calculus to account for this. This includes a new form of the variable rule (built using de Bruijn indices) to account for $\Gamma.\{\mu\}$.

$$\frac{\Delta \vdash \gamma : \Gamma}{\Delta.\{\mu\} \vdash \gamma.\{\mu\} : \Gamma.\{\mu\}} \quad \frac{\vdash \Gamma \text{ cx} \quad \mu \le \nu}{\Gamma.\{\nu\} \vdash \Gamma.\{\mu \le \nu\} : \Gamma.\{\mu\}}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type}}{\Gamma.(\mu \mid A) \vdash \uparrow : \Gamma}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Delta \vdash \gamma : \Gamma \quad \Delta \vdash M : A[\gamma.\{\mu\}]}{\Delta \vdash \gamma.M : \Gamma.(\mu \mid A)}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type}}{\Gamma.(\mu \mid A).\{\mu\} \vdash \text{var} : A[\uparrow.\{\mu\}]}$$

We have normal substitution rules around substitution extensions and weakenings. These are essentially standard, and so we omit them. We further require a handful of equations which ensure that $\Gamma \mapsto \Gamma.\{\mu\}$, $\gamma \mapsto \gamma.\{\mu\}$, and $-\{- \le -\}$ organize into a 2-functor from $\mathcal{M}^{\text{coop}}$ to Cat sending $m$ to the category of contexts. We refer the reader to Gratzer et al. [9] for a full account.

The additional types and terms are then given as follows:

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type}}{\Gamma \vdash \langle \mu \mid A \rangle \text{ type}} \quad \frac{\Gamma.\{\mu\} \vdash M : A}{\Gamma \vdash \text{mod}_\mu(M) : \langle \mu \mid A \rangle}$$

$$\frac{\Gamma.\{\nu \circ \mu\} \vdash A \text{ type} \quad \Gamma.(\nu \mid \langle \mu \mid A \rangle) \vdash B \text{ type}}{\Gamma.(\nu \circ \mu \mid A) \vdash b : B[\uparrow.\text{mod}_\mu(\text{var})] \quad \Gamma.\{\nu\} \vdash a : \langle \mu \mid A \rangle} \quad \frac{\Gamma.\{\nu\} \vdash a : \langle \mu \mid A \rangle}{\Gamma \vdash \text{let}_\nu \text{ mod}_\mu(-) \leftarrow a \text{ in } b : B[\text{id.}a]}$$

$$\frac{\Gamma.\{\nu \circ \mu\} \vdash A \text{ type} \quad \Gamma.(\nu \mid \langle \mu \mid A \rangle) \vdash B \text{ type}}{\Gamma.(\nu \circ \mu \mid A) \vdash b : B[\uparrow.\text{mod}_\mu(\text{var})] \quad \Gamma.\{\nu \circ \mu\} \vdash a : A} \quad \frac{\Gamma.\{\nu \circ \mu\} \vdash a : A}{\Gamma \vdash \text{let}_\nu \text{ mod}_\mu(-) \leftarrow \text{mod}_\mu(a) \text{ in } b = b[\text{id.}a] : B[\text{id.} \text{mod}_\mu(a)]}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Gamma.(\mu \mid A) \vdash B \text{ type}}{\Gamma \vdash (\mu \mid A) \to B \text{ type}}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Gamma.(\mu \mid A) \vdash b : B}{\Gamma \vdash \lambda M : (\mu \mid A) \to B}$$

$$\frac{\Gamma \vdash f : (\mu \mid A) \to B \quad \Gamma.\{\mu\} \vdash a : A}{\Gamma \vdash f(a) : B[\text{id.}a]}$$

$$\frac{\Gamma.\{\mu\} \vdash A \text{ type} \quad \Gamma.(\mu \mid A) \vdash b : B \quad \Gamma.\{\mu\} \vdash a : A}{\Gamma \vdash (\lambda b)(a) = b[\text{id.}a] : B[\text{id.}a]}$$

$$\frac{\Gamma \vdash f : (\mu \mid A) \to B}{\Gamma \vdash f = \lambda f[\uparrow](\text{var}) : (\mu \mid A) \to B}$$

## B Full list of axioms

**Axiom 1.** *The canonical map $A = \mathcal{U}_i, B \to A \simeq B$ sending refl to id is an equivalence.*

**Axiom 2.** *There is a set $\mathbb{I}$ equipped with the structure of a bounded distributive lattice $(0, 1, \wedge, \vee)$ such that $0 \ne 1$.*

**Axiom 3.** *If $A :_\mu \mathcal{U}$ and $a, b :_\mu A$, then the following canonical map sending refl to $\text{mod}_\mu(\text{refl})$ is an equivalence:*

$$\text{mod}_\mu(a) = \text{mod}_\mu(b) \to \langle \mu \mid a = b \rangle$$

**Axiom 4.** $0, 1 : \mathbb{I}$ induce an equivalence $\langle b \mid \text{Bool} \rangle \simeq \langle b \mid \mathbb{I} \rangle$

**Axiom 5.** *If $A :_b \mathcal{U}$, then is $\text{Equiv}(\langle b \mid A \rangle \to A)$ if is $\text{Equiv}(A \to A^\mathbb{I})$*

**Axiom 6.** *If $A, B :_b \mathcal{U}$ and $f :_b A \to B$, then $f$ is an equivalence if $\prod_{n:\text{Nat}} \text{isEquiv}((f_*)^\dagger : \langle b \mid \mathbb{I}^n \to A \rangle \to \langle b \mid \mathbb{I}^n \to B \rangle)$*

**Axiom 7.** *For every $A :_b \mathcal{U}$, the following holds:*

$$\prod_{n:\text{Nat}} \text{isEquiv}((\eta_*)^\dagger : \langle b \mid \Delta^n \to A \rangle \to \langle b \mid \Delta^n \to \square A \rangle)$$

**Axiom 8.** *For every $A :_b \mathcal{U}$, the following holds:*

$$\sum_{A :_b \mathcal{U}, \varepsilon :_b (A :_b \mathbb{I}) \to A} \prod_{B :_b \mathcal{U}} \text{isEquiv}(\langle b \mid B \to A :_b \rangle \to \langle b \mid B^\mathbb{I} \to A \rangle)$$

**Axiom 9.** *There is an equivalence $\langle \text{op} \mid \mathbb{I} \rangle \to \mathbb{I}$ which exchanges 0 for 1 and $\wedge$ for $\vee$.*

Define a *finitely-presented $\mathbb{I}$-algebra* to be a map of bounded distributive lattice $\mathbb{I} \to X$ where $X$ is equivalent to a bounded distributive lattice of the form $\mathbb{I}[x_1 \dots x_n]/(f_1 = g_1 \dots f_m = g_m)$ and $\mathbb{I} \to X$ is the canonical map. That is, $X$ is freely generated over $\mathbb{I}$ by the operations of a bounded distributive lattice, the indeterminates $x_1 \dots x_n$, and subject to the equations $f_i = g_i$. With this notation to hand, we state a duality axiom due originally to Kock [15] and proposed in this form by Blechschmidt [4].

**Axiom 10.** *If $\mathbb{I} \to X$ is a finitely presented $\mathbb{I}$-algebra, the following evaluation map is an equivalence of underlying sets:*

$$\lambda x, f, f(x) : X \simeq \mathbb{I}^{\text{hom}_U(X, \mathbb{I})}$$

## C Selected details from omitted proofs

If a proof of a proposition given in the main body is presented here in the appendix, we have ensured that the numbering in the appendix matches that of the main body. Propositions numbered "C.X" are therefore only intermediate results used in the process of proving those main results.

The ∞-category of ∞-categories in simplicial type theory

### C.1 Amazing propositions

Lemma 2.9. If \(\phi :_{\mathfrak{b}} \mathcal{U}^{\mathbb{I}^{n}} \to \mathrm{HProp}\), there is a \(\bar{\phi} :_{\mathfrak{b}} \mathcal{U} \to \mathrm{HProp}\) equipped with a canonical equivalence:

\[
\prod_ {A _ {\mathfrak {b}} X \to \mathcal {U}} \langle b | (x: X) \to \bar {\phi} (A x) \rangle \simeq \langle b | (x: X ^ {\mathbb {I} ^ {n}}) \to \phi (A \circ x) \rangle
\]

PROOF. Fix a predicate \(\phi :_{\mathfrak{b}} \mathcal{U}^{\mathbb{I}} \to \mathrm{HProp}\) (for simplicity, we handle only the case of \(n = 1\) as the case general case is identical modulo notational clutter). We begin by using Axiom 8 to obtain a map \(\phi_{\mathbb{I}} :_{\mathfrak{b}} \mathcal{U} \to \mathrm{HProp}_{\mathbb{I}}\) where \(\mathrm{HProp}_{\mathbb{I}}\) is the unique type arising from applying the amazing right adjoint to HProp. Next, following Gratzer et al. [10, §3.3], we observe that the tautological family \(1_{\mathbb{I}} \to \mathrm{HProp}_{\mathbb{I}}\) is classified by a map \(\mathrm{HProp}_{\mathbb{I}} \to \mathrm{HProp}\) (in particular, it is a small family) and, composing this with \(\phi_{\mathbb{I}}\), we obtain our desired \(\bar{\phi} : \mathcal{U} \to \mathrm{HProp}\). In total, we have the following diagram:

![img-3.jpeg](img-3.jpeg)

To show that the desired equivalence holds, fix \(A:_{\mathfrak{b}}X \to \mathcal{U}\). We wish to show that \(\prod_{x:X} \bar{\phi}(Ax)\) holds if and only if \(\prod_{x:X^{\mathbb{I}}} \bar{\phi}(A \circ x)\). The former holds if and only if there is a (necessarily unique) extension of the above diagram:

![img-4.jpeg](img-4.jpeg)

After transposing  \( (-)_{\mathbb{I}} \)  (and discarding the right-hand vertical map as it is redundant for our purposes), we see that the left-hand triangle of this diagram is precisely equivalent to the following:

![img-5.jpeg](img-5.jpeg)

Examining this diagram yields the desired conclusion.

### C.2 Technical results on iso-inner fibrations

We write Spine \( ^{n} \) for the iterated pushout \( I \sqcup_{1} \ldots \sqcup_{1} I \) which glues together n copies of I attaching 0 to 1 and 1 to 0.

Lemma C.1. If \( f:_{\mathfrak{b}} X \to Y \) is inner it is orthogonal to Spine\( ^{n} \) → \( \Delta^{n} \) for all \( n \geq 2 \).

PROOF. The \(n = 2\) case is by definition, so we proceed by induction. By induction hypothesis, \(\mathrm{Spine}^{n + 1}\to \Delta^n\sqcup_1\mathbb{I}\) is orthogonal

to all inner maps(left maps are closed under pushouts). It suffices to show that \(\Delta^n \sqcup_1 \mathbb{I} \to \Delta^{n+1}\) is orthogonal to all inner maps. Unfolding these conditionals, we must show the following:

\[
\{(v, i) \mid v (n) = 1 \vee i = 0 \} \rightarrow \{(v, i) \mid v (n) \geq i \}
\]

This, in turn, is a retract of \(\mathbb{I}^{n - 1}\times \Lambda_1^2\to \mathbb{I}^{n - 1}\times \Delta^2\)

Lemma C.2. If \(X:_{\mathfrak{b}} \mathcal{U}\) is Segal so too is \(\square X\).

PROOF. For this, we must show that the following map is an equivalence:

\[
\langle b \mid \Delta^ {n} \times \Delta^ {2} \rightarrow \square X \rangle \rightarrow \langle b \mid \Delta^ {n} \times \Lambda_ {1} ^ {2} \rightarrow \square X \rangle
\]

To prove this, we argue that (1) \(\square X\) is \(b\)-orthogonal\(^{5}\) to \(\mathrm{Spine}^{n} \to \Delta^{n}\) and that (2) if a type \(Y:_{\mathfrak{b}} \mathcal{U}_{\square}\) is \(b\)-orthogonal to \(\mathrm{Spine}^{n} \to \Delta^{n}\) so too is \(Y^{\mathbb{I}}\). For the first claim, we note that this follows immediately from simplicial stability (Axiom 7) along with the fact that \(\langle b | - \rangle\) commutes with limits:

\[
\begin{array}{l} \langle b \mid \text { Spine } ^ {n} \to \square X \rangle \\ \simeq \langle b | \mathbb {I} \rightarrow \square X \rangle \times_ {\langle b | \square X \rangle} \langle b | \mathbb {I} \rightarrow \square X \rangle \times_ {\langle b | \square X \rangle} \dots \\ \simeq \langle b | \mathbb {I} \rightarrow X \rangle \times_ {\langle b | X \rangle} \langle b | \mathbb {I} \rightarrow X \rangle \times_ {\langle b | X \rangle} \dots \\ \simeq \langle b \mid \text { Spine } ^ {n} \to X \rangle \\ \end{array}
\]

Consequently, we are reduced to the same question for \( X \to 1 \) which follows from Lemma C.1.

For the second claim, we must show that \(\mathrm{Spine}^n\times \mathbb{I}\to \Delta^n\times \mathbb{I}\) is b-orthogonal to a simplicial \(f\) provided that \(f\) is b-orthogonal to all spine inclusions. To this end, we note the following identifications:

\[
\Delta^ {n} \times \mathbb {I} = \{(v, i): \Delta^ {n} \times \mathbb {I} | \exists k \in \{0, \dots , n + 1 \}. v (k) \geq i \geq v (k + 1) \}
\]

Here, by convention, we treat \( v(0) = 1 \) and \( v(n + 1) = v(n + 2) = 0 \). In what follows, we write \( \Phi_k \) for the condition \( v(k) \geq i \geq v(k + 1) \).

Consequently, to show the desired lifting it suffices to show that there is a unique such lift for  \( \{(v,i):\Delta^{n}\times\mathbb{I}\mid\Phi_{k_{0}}\times\cdots\times\Phi_{k_{l}}\} \) . A moment's thought reveals that each such intersection is a subsimplex of  \( \Delta^{n}\times\mathbb{I} \) . In particular, each  \( \{(v,i)\mid\Phi_{k}\} \)  is  \( \Delta^{n+1} \)  and each higher intersection is a smaller simplex. Moreover, its intersection with  \( Spine^{n}\times\mathbb{I} \)  is either exactly the spine of this smaller simplex (in the cases of  \( \Phi_{0} \)  and  \( \Phi_{n} \)  or higher intersections) or  \( I\sqcup_{1}\ldots\sqcup_{1}\Delta^{2}\sqcup_{1}\ldots \) . In either case, the unique lifting exists by assumption on Y (in the latter case, by 2-for-3 and the closure of left classes under pushouts, as one may see by observing the following decomposition:  \( Spine^{n+1}\to(\mathbb{I}\sqcup_{1}\ldots\sqcup_{1}\Delta^{2}\sqcup_{1}\ldots\sqcup_{1}\mathbb{I})\to\Delta^{n+1} \) ).

Corollary C.3. If \(X:_{\mathfrak{b}} \mathcal{U}\) is simplicial, it suffices to show that it is b-orthogonal to \(\mathrm{Spine}^n \to \Delta^n\) to prove that it is Segal.

Lemma C.4. If \(X:_{\mathfrak{b}} \mathcal{U}\) is Segal and Rezk then \(\square X\) is Rezk.

PROOF. We must show that \(\square X\) is b-orthogonal to \(\mathbb{E} \times \Delta^n \to \Delta^n\) and, since \(\square X\) is Segal, we may reduce immediately to the case where \(n = 0\) or \(n = 1\). The first case is an immediate consequence of simplicial stability, as \(\mathbb{E}\) is built by pushing out various simplices and therefore maps \(\langle b | \mathbb{E} \to \square X \rangle\) correspond to those maps which factor through \(X\).

For the \(n = 1\) case, we must show that diagrams of the following shape in \(X\) are determined by the bottom-most edge

\( ^{5} \) Meaning, orthogonal when we restrict our attention to b-annotated maps

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

![img-6.jpeg](img-6.jpeg)

By simplicial stability along with the previous case, we may safely assume that each of these components (including the relevant 2-cells and section-retraction pairs) all come from \( X \). Moreover, since \( X \) is Segal, the top simplex is redundant. In particular, it is equivalent to the type \( \sum_{\iota_1: \mathbb{B} \to X} \sum_{f: \mathbb{B} \to X} \sum_{p: \iota_1(1) = f(0)} \iota \circ_p f = g \circ \iota_1 \). By the \( n = 0 \) case we have already discussed, we may assume \( \iota_1 = \mathrm{id} \) and replace \( \iota_1: \mathbb{B} \to X \) by simply \( x: \mathbb{B} \to X \). After this replacement, the whole type collapses to a singleton type.

It finally suffices to show that the bottom triangle is equivalent to the bottom edge. However, we may replace this triangle by the corresponding inner horn, whereafter another application of the Rezk condition for n = 0 finishes things off. □

Lemma 5.11. If \(X:_{\mathbb{D}}\mathcal{U}\) is Segal and Rezk, then \(\square X\) is a category.

### C.3 Locally cocartesian families

Lemma C.5. If \(A: X \to \mathcal{U}_{\square}\) is an iso-inner fibration, then a dependent edge \(a: (i: \mathbb{I}) \to A(xi)\) over \(x: \mathbb{I} \to X\) is locally cocartesian if and only if the following map is an equivalence:

\[
a ^ {*}: \left(\sum_ {f: \mathbb {I} \rightarrow A (x 1)} f (0) = a (1)\right)\rightarrow \left(\sum_ {f: (i: \mathbb {I}) \rightarrow A (x i)} f (0) = a (0)\right)
\]

PROOF. This question is once more restricted to a particular \(x: \mathbb{I} \to X\), we may pull back \(A\) along this map to suppose that \(A: \mathbb{I} \to \mathcal{U}_{\square}\) and that \(a: (i: \mathbb{I}) \to Ai\). In this case, \(a\) is locally cocartesian if and only if the following holds (by definition):

\[
\prod_ {b: (i: \mathbb {I}) \to A i} \prod_ {p: a 0 = b 0} \text { isContr } \left(\sum_ {t: (i, j: \Delta^ {2}) \to A i} t | _ {\Delta_ {0} ^ {2}} = [ a, b, p ]\right)
\]

Fix \( b: (i: \mathbb{I}) \to Ai \) and \( p: a0 = b0 \). Then \( \sum_{t: (i,j:\Delta^2) \to Ai} t|_{\Delta_0^2} = [a, b, p] \) is equivalent (by innerness) to \( c: \mathbb{I} \to A1 \) along with \( q: c(0) = a(1) \), \( \theta: c \circ_q a = b \), and \( \theta_0: \mathrm{ap}_{-(0)}(\theta) = p \). However, this is precisely the fiber of \( a^* \), so an edge is locally cocartesian if and only if each fiber of \( a^* \) is contractible.

Theorem 3.8. If \(A: X \to \mathcal{U}_{\square}\) is iso-inner and locally cocartesian where locally cocartesian edges compose, then locally cocartesian edges are cocartesian and \(A\) is cocartesian.

PROOF. We wish to show that \(\Lambda_0^2\to \Delta^2\) is orthogonal to \(\tilde{A}\rightarrow X\) if the \(0\to 1\) edge of \(\Lambda_0^2\) is sent to a locally cocartesian edge. Since this property can be tested after pulling back \(\sum_{x:X}Ax\to X\), we may assume that \(X = \Delta^2\) and concern ourselves only with the tautological 2-simplex. Moreover, in this situation \(\sum_{x:X}Ax\) is a (simplicial) category.

Let us now fix \([f, g, p] : \Lambda_0^2 \to \sum_{x: X} Ax\) which lifts id such that \(f\) is locally cocartesian. Let us write \(x = f(0)\), \(y = f(1)\), and \(z = g(1)\). With this notation, \(p : x = g(0)\).

We wish to show that \([f, g, p]\) extends uniquely to a 2-simplex (such a 2-simplex will necessarily lie correctly over the unique non-degenerate 2-simplex in \(X\) and—since \(X\) is a set—there is no interesting data in how it lies over this simplex). To this end, it suffices

to show that the following map is an equivalence [5, Proposition 5.1.10]:

\[
f ^ {*}: \hom (y, z) \to \hom (x, z)
\]

If so, we may choose the (unique) preimage of  \( (g,p,\text{refl}) \)  to conclude the proof. Now, let us choose a locally cocartesian lift of  \( (1,-):\mathbb{I}\to\Delta^{2} \)  with starting point y. This is a morphism  \( h' \) . Let us write w for the target of  \( h' \) . Since  \( h'\circ f \)  is locally cocartesian by assumption, we conclude that the following maps are equivalences by Lemma C.5:

\[
(h ^ {\prime} \circ f) ^ {*}: \hom (w, z) \to \hom (x, z) \quad h ^ {\prime *} \colon \hom (w, z) \to \hom (y, z)
\]

By 3-for-2, the same is then true of \( f^{*} : \hom(y, z) \to \hom(x, z) \) as required.

Lemma 4.1. If \(A: X \to \mathcal{U}_{\square}\) is iso-inner, then hasLCCLifts(A) and LCCLiftsCompose(A) are propositions.

PROOF. Note that it suffices to prove that for all \(x: \mathbb{I} \to X\) (respectively, \(x: \mathbb{I}^2 \to X\)) that hasLCCLifts(A \(\circ x\)) (respectively, LCCLiftsCompose(A \(\circ x\))) is a proposition.

Only the first of these obligations is non-trivial, since isLocallyCoCart is manifestly valued propositions. Note that if \(a\) and \(a'\) are both locally cocartesian lifts, then by construction there is a unique vertical isomorphism \(\iota : a(1) \cong a'(1)\) such that \(\iota \circ a = a'\). We may then consider these as isomorphic arrows in the fiber \(\mathbb{I} \times_X \sum_{x: X} Ax\), which is a category by iso-innerness. Consequently, \(a = a'\) in the fiber \(\mathbb{I} \times_X \sum_{x: X} Ax\) whereby they are equal in \(\sum_{x: X} Ax\). The type of locally cocartesian lifts is therefore a proposition as required.

### C.4 The directed gluing of cocartesian fibrations

Lemma 3.9. If X is simplicial, then  \( \mathrm{Gl}(F_{0}, F_{1}, \alpha) \)  is iso-inner.

PROOF. First, we note by elementary manipulation of closure properties, it suffices to consider the case where \( F_{1} = \lambda_{-}.1 \) (use the 3-for-2 fact available for iso-inner families with the factorization \( \mathrm{Gl}(F_0,F_1,\alpha)\to (\sum_{x:X}F_1(x))\times \mathbb{I}\to X\times \mathbb{I}) \).

We must show that \(\mathrm{Spine}^n\to \Delta^n\) is b-orthogonal to \(\mathrm{Gl}(F_0,F_1,\alpha)\) by Corollary C.3. To this end, fix a map \(b:\mathbb{I}_{\mathbb{D}}\Delta^{n}\to X\times \mathbb{I}\) along with a partial section:

\[
s _ {0}: _ {\mathbb {D}} (v: \operatorname{Spine} ^ {n}) \to \operatorname{Gl} (F _ {0}, F _ {1}, \alpha) (b (v))
\]

We must show that \( s_0 \) extends uniquely. Let us begin by investigating \( i = \pi_1 \circ b \), a \( b \)-annotated map \( \Delta^n \to \mathbb{I} \). By duality, such a map corresponds to a \( b \) element of \( \mathbb{I}[x_0 \leq \cdots \leq x_n] \) so it is either 0, 1, or \( x_k \) for some particular \( 0 \leq k \leq n \). If we are in the case of \( i = \lambda_{-}.0 \) or \( i = \lambda_{-}.1 \), then the conclusion is immediate from the innerness of \( F_0 \). If we are instead in the case where \( i = \text{dual}(x_k) \), we must proceed differently. We note that in such a case, \( i(v) = 0 \) if and only if \( v_k = 0 \). This means that \( s_0 \) has the type \( (v: \text{Spine}^k) \to F_0(b(v, 0, \ldots)) \) and we must construct a unique extension \( s \) of type \( (v: \Delta^k) \to F_0(b(v, 0, \ldots)) \). This is immediate by the innerness of \( F_0(b(-, 0, \ldots)) \) which in turn is a consequence of the innerness of \( F \).

To show the “iso” part of iso-innerness, we note that this can be checked fiberwise. However, over each fiber, this is immediate by the fact that Rezk types are an exponential ideal and  \( F_{0} \)  is iso-inner.

The ∞-category of ∞-categories in simplicial type theory

**Lemma 3.10.** If $X$ is a category, then $\mathrm{Gl}(F_0, F_1, \alpha)$ is cocartesian.

PROOF. In light of Lemma 3.9, everything involved is a (simplicial) category. Accordingly, we may use the LARI condition of [5] to prove this result. Applying the results of [11], we are then further reduced to constructing this adjoint on objects.

Fix $i \cdot \mathbb{I} \to \mathbb{I}$ along with $x \cdot \mathbb{I} \to X$, $f_0^1 \cdot \mathbb{I} \to F_1(x)$ and $f_0^0 \cdot \mathbb{I} \to i(0) = 0 \to \alpha_x^{-1}(f_0^1)$. We begin by constructing a lift of $(f_0^1, f_0^0)$ and then we argue that it is suitably initial.

First, let us note that since $\alpha$ preserves cocartesian edges, if we have $g: F_0(x)$ which lies over $f: F_1(x)$, then $x \cdot g_0$ lies over $x \cdot f_0$ by a contractible choice of path since $\alpha(x \cdot g_0)$ is a cocartesian lift of the same data as $x \cdot f_0$. Consequently, we may construct the desired lifts:

$$f^1 = \lambda j : \mathbb{I}. x(-\wedge j) \cdot (f_0^1) \quad f^0 = \lambda j : \mathbb{I}, z : i(j) = 0. x(-\wedge j) \cdot (f_0^0(\_))$$

Assume now we are given $\alpha: \mathbb{I} \times \mathbb{I} \to \mathbb{I}$ and $\chi: \mathbb{I} \times \mathbb{I} \to X$ such that $i = \alpha(0, -)$ and $\chi(0, -) = x$ (we silently replace $x$ and $i$ by transport along these paths to treat them as reflexivity in what follows). We also assume we are given partial lifts: $g^1: (j: \mathbb{I}) \to F_1(\chi(1, j))$ $g^0: (j: \mathbb{I}) \to \alpha(1, j) = 0 \to \alpha_{\chi(1, j)}^{-1}(g^1(j))$ and $h_0^1: (k: \mathbb{I}) \to F_1(\chi(k, 0))$. $h_0^0: (k: \mathbb{I}) \to \alpha(k, 0) = 0 \to \alpha_{\chi(k, 0)}^{-1}(h_0^1(k))$. We may further assume that all of these are $\mathbb{I}$-annotated and that there are paths $q: (g^1(0), g^0(0)) = (h_0^1(1), h_0^0(1))$ and $p: (f^1(0), f^0(0)) = (h_0^1(0), h_0^0(0))$

We wish to show that there is a unique extension $(h_0^1, h_0^0)$ to all of $\mathbb{I} \times \mathbb{I}$ which matches with $h_0$, $e$, and $f$ over $p$ and $q$. First, we note that we may uniquely extend $h_0^1$ to $h^1$ since $F_1$ is cocartesian. Let us therefore replace $h_0^1, f^1$, and $g^1$ with $h^1$ so that our new goal is to construct an extension of $h_0^0$ given the following:

$$h_0^0: (k: \mathbb{I}) \to \alpha(k, 0) = 0 \to \alpha_{\chi(k, 0)}^{-1}(h^1(k, 0))$$

$$f^0: (j: \mathbb{I}) \to \alpha(0, j) = 0 \to \alpha_{\chi(0, j)}^{-1}(h^1(k, 0))$$

$$g^0: (j: \mathbb{I}) \to \alpha(1, j) = 0 \to \alpha_{\chi(1, j)}^{-1}(h^1(k, 1))$$

To prove this, we must perform a somewhat lengthy case analysis on $\alpha$. Since it is $\mathbb{I}$-annotated, we know that it is a $\mathbb{I}$-element of $\mathbb{I}[x_0, x_1]$ and we can analyze it somewhat extensively.

Case. $\alpha(0, -) = \lambda_{\_.1}$.

In this case, $\alpha = \lambda_{\_.1}$ by monotonicity, and so any extension is necessarily trivial.

Case. $\alpha(0, -) = \lambda_{\_.0}$.

Here, we have several sub-cases to consider:

Case. $\alpha(1, -) = \lambda_{\_.0}$.

In this case, the condition $\alpha(-, -) = 0$ holds in all cases, so this reduces precisely to the fact that $F_0$ is cocartesian. In particular, we note that we may extend $h^0$ in $F_0$ (not in the fiber) using the fact that $f^0$ is cocartesian. This extension is unique by construction and, since the input to the extension lies over $h^1$, it lives in the correct fiber (uniquely).

Case. $\alpha(1, -) = \lambda j. j$.

In this case, we must construct a lift of the following type:

$$(k, j: \mathbb{I}) \to k \wedge j = 0 \to \alpha_{\chi(k, j)}^{-1}(h^1(k, j))$$

Given $k, j: \mathbb{I}$, since everything is simplicial we may assume that $k \le j$ or $j \le k$. In other words, our condition is equivalent to $k = 0$ or $j = 0$; any extension is fully determined by the boundary conditions.

Case. $\alpha(1, -) = \lambda_{\_.1}$.

In this case, $\alpha = \lambda(k, j). k$ and so we may just take $h_0 = h_0^0$.

Case. $\alpha(0, -) = \lambda j. j$.

Here, we have several sub-cases to consider:

Case. $\alpha(1, -) = \lambda j. j$.

In this case, $\alpha(k, j) = j$ and so we may simply take $h^0 = f^0$.

Case. $\alpha(1, -) = \lambda_{\_.1}$.

In this case, $\alpha(k, j) = k \vee j$, so our condition $\alpha(k, j) = 0$ amounts to $k = 0 \wedge j = 0$. Consequently, we may take $h = f_0^0$.

**Corollary 3.11.** Cocartesian transport from $\mathrm{Gl}(F_0, F_1, \alpha)(-, 0)$ to $\mathrm{Gl}(F_0, F_1, \alpha)(-, 1)$ is given by $\alpha$.

PROOF. First, we note that given $f: \mathrm{Gl}(F_0, F_1, \alpha)(c, 0) \cong F_0(c)$, there is a functorial choice of edges:

$$\lambda i. (\alpha(f), \lambda_{\_.}(f, \text{refl})) : (i: \mathbb{I}) \to \mathrm{Gl}(F_0, F_1, \alpha)(c, i)$$

To show the desired identification, it suffices to show that this edge is cocartesian and, using the standard result that a natural transformation is an equivalence if and only if it is pointwise such, we restrict our attention to the case where $c \cdot \mathbb{I}_0 \to C$. This, however, is immediate in light of the above proof—in particular, cocartesian transport along a constant edge in $C$ is trivial.

### C.5 Classification of cocartesian fibrations

**Corollary 5.7.** Cocartesian transport induces an equivalence

$$\langle \mathbb{I} \mid \mathrm{Cat}^{X \times \Delta^1} \rangle \simeq \langle \mathbb{I} \mid \sum_{A_0, A_1, A_2: \mathrm{Cat}^X} A_0 \to {}^{\mathrm{cc}} A_1 \times A_1 \to {}^{\mathrm{cc}} A_2 \rangle.$$

PROOF. As before, one direction of this equivalence is given by taking fibers and cocartesian transports. We must construct a quasi-inverse.

Fix $F_0, F_1, F_2 \cdot \mathbb{I}_0 \to \mathcal{U}_{\mathbb{I}}$ cocartesian and $\alpha \cdot \mathbb{I}_0 \to {}^{\mathrm{cc}} F_1$ and $\beta \cdot \mathbb{I}_0 \to {}^{\mathrm{cc}} F_2$. We wish to apply Gl once more, but some additional care is required. As was described above in the text, we take $F_{01} = \mathrm{Gl}(F_0, F_1, \alpha) : C \times \mathbb{I} \to \mathcal{U}_{\mathbb{I}}$ and then consider $\gamma$ to be the composite $F_{01} \to {}^{\mathrm{cc}} F_1 \times \mathbb{I} \to {}^{\mathrm{cc}} F_2 \times \mathbb{I}$ where these operations are induced by cocartesian transport and $\mathbb{I} \times \beta$. Let us note that cocartesian transport preserves cocartesian edges—using 3-for-2 of cocartesian edges—and the transformation $F_1 \to F_2$ preserves cocartesian edges by assumption.

Consequently, we may glue along this once more to obtain a cocartesian family $F_{01,2} : C \times \mathbb{I} \times \mathbb{I} \to \mathcal{U}_{\mathbb{I}}$. Pre-composing with $\Delta^2 \to \mathbb{I} \times \mathbb{I}$, we obtain the desired family over $F_{012} : C \times \Delta^2 \to \mathcal{U}_{\mathbb{I}}$.

Unfolding, this family sends $(c, i, j)$ to the following type:

$$\sum_{x_2: F_2(c)} j = 0 \to \sum_{x_{01}: F_{01}(c, i)} \gamma(x_{01}) = (i, x_2)$$

$$\simeq \sum_{x_2: F_2(c)} j = 0 \to \sum_{x_1: \beta^{-1}(x_2)} i = 0 \to \alpha^{-1}(x_1)$$

There is then a canonical assignment $t_2 : F(c, i, j) \to F_{012}(c, i, j)$ given as follows:

$$x \mapsto ((c, - \vee i, - \vee j) \cdot (x), \lambda_{\_.} : j = 0 \, ((c, - \vee i, 0) \cdot (x), \lambda_{\_.} : i = 0. x))$$

Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

We may then check directly that this assignment preserves cocartesian arrows by unfolding their construction in the Gl and checking this holds on global data once more. In the end, it amounts to the proof that $\iota$ preserves cocartesian edges; when restricted to the global edges $0 \le 1, 1 \le 2$ and $2 \le 3$ we find that the above characterization of $F_{012}$ collapses to a single application of Gl along various cocartesian functors. $\square$

### C.6 Straightening–unstraightening

**Corollary 6.5.** *The map $U : (C \to \text{Cat}) \to \text{Cat}_{/C}$ is an embedding.*

PROOF. To show that $U$ is an embedding, we will show that $\Delta_U : (C \to \text{Cat}) \to (C \to \text{Cat}) \times_{\text{Cat}_{/C}} (C \to \text{Cat})$ is an equivalence. Applying Axiom 6 along with the fact that all of the objects involved here are simplicial, it suffices to show that the following map is an equivalence:

$$\langle b \mid \Delta^n \to \text{Cat} \rangle \to \langle b \mid \Delta^n \to (C \to \text{Cat}) \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \rangle$$

Since both sides of this are categories, we may restrict to the case where $n = 0, 1$. In this case, it suffices to show that if $f, g :_b \Delta^n \to (C \to \text{Cat})$ and $p :_b U \circ f = U \circ g$ then there is a path $(f, \text{refl}) = (g, p)$. However, this is precisely equivalent to asking that the fiber of $(U \circ -)^\top$ over $\text{mod}_b (U \circ f)$ is contractible. By previous results, we know the fiber is a proposition and it is inhabited by $(f, \text{refl})$. Consequently, it is contractible as required. $\square$

**Corollary 6.6** (Straightening–unstraightening). *If $D :_b \mathcal{U}$ is a category, a map $f :_b D \to \text{Cat}_{/C}$ lifts along $U$ to $\text{Cat}^C$ if and only if*

- (1) for each $d :_b D$, the functor $f(d)$ is a cocartesian family.
- (2) for each $d :_b \mathbb{I} \to D$, the functor induced by $f \circ d : \mathbb{I} \to \text{Cat}_{/C}$ is a cocartesian functor between the cocartesian families.

PROOF. Our goal is to characterize for which $f$ the following map is an equivalence:

$$D \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \to D$$

Notably, we know already this map is an embedding (it is the pullback of $U$) and so we merely wish to characterize when it is surjective. Using Axiom 6 along with the fact that both sides are categories, it suffices to consider when the following maps are surjective:

$$\begin{array}{l} \langle b \mid D \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \rangle \to \langle b \mid D \rangle \\ \langle b \mid \mathbb{I} \to D \times_{\text{Cat}_{/C}} (C \to \text{Cat}) \rangle \to \langle b \mid \mathbb{I} \to D \rangle \end{array}$$

We now unfold these maps and use Proposition 2.8. These guarantee that the first map will hit $d :_b D$ if and only if $f(d)$ is a cocartesian family. Similarly, the second map will hit $d :_b \mathbb{I} \to D$ if and only if $f \circ d$ is a cocartesian functor between cocartesian families. $\square$