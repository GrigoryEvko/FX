Canad. J. Math. Vol. 00 (0), 2020 pp. 1–69
http://dx.doi.org/10.4153/xxxx
© Canadian Mathematical Society 2020

# Relative elegance and cartesian cubes with one connection*

Evan Cavallo and Christian Sattler

Abstract. We establish a Quillen equivalence between the Kan–Quillen model structure and a model structure, derived from a cubical model of homotopy type theory, on the category of cartesian cubical sets with one connection. We thereby identify a second model structure which both constructively models homotopy type theory and presents ∞-groupoids, the first example being the equivariant cartesian model of Awodey–Cavallo–Coquand–Riehl–Sattler.

## Contents

|  1 | Introduction | 1  |
| --- | --- | --- |
|  2 | Background | 7  |
|  3 | Model structures from cubical models of type theory | 14  |
|  4 | Semilattice cubical sets | 24  |
|  5 | Relatively elegant Reedy categories | 39  |
|  6 | Reedy structures on categories of finite algebras | 52  |
|  7 | Equivalences and equalities | 55  |
|  A | Negative results | 60  |

## 1 Introduction

Homotopy type theory (HoTT) [Uni13] is said to be a language for reasoning in homotopical settings. The conjecture (“Awodey’s proposal”) goes that HoTT should have an interpretation in any (∞, 1)-category belonging to some class of “elementary (∞, 1)-topoi”, indeed, that models of HoTT should be in correspondence with such (∞, 1)-categories. When one says that HoTT interprets in a given (∞, 1)-category, one typically means more precisely that it admits a 1-categorical presentation interpreting HoTT in a 1-categorical sense. These presentations have historically come in the form of Quillen model categories. As an example, Voevodsky’s interpretation of HoTT [KL21] lands in the Kan–Quillen model structure on simplicial sets, which presents the (∞, 1)-category ∞-Gpd of (∞, 1)-groupoids. Shulman [Shu19] has now shown that every Grothendieck (∞, 1)-topos can be presented by a model category that interprets HoTT.

AMS subject classification: 55U35, 03B38.

Keywords: cubical sets, homotopy type theory, Quillen model structure, elegant Reedy category.

*The first author was supported by the Knut and Alice Wallenberg Foundation (KAW) under grants no. 2020.0266 and 2019.0116. The second author was supported by Swedish Research Council grant 2019-03765.

arXiv:2211.14801v6 [math.AT] 15 Oct 2025

2025/10/16 00:43

2

E. Cavallo and C. Sattler

The interests of type theorists have thus led to new questions in homotopy theory; one avenue is through the search for constructive interpretations of HoTT. The first constructive model to be discovered, due to Bezem, Coquand, and Huber [BCH13; BCH19], interprets HoTT in a category of affine cubical sets, presheaves over a certain affine cube category $\square_{\mathrm{aff}}$ whose objects are symmetric monoidal products of an interval object $I$. Subsequent constructions [CCHM15; OP18; LOPS18; AFH18; CMS20; ABCHFL21] use different cube categories to obtain better properties. With the exception of the BCH model, all employ presheaves over a cube category with cartesian products, i.e., including degeneracy, diagonal, and permutation maps among its generators. While natural from a type-theoretic perspective, the presence of diagonals—and to a lesser degree, permutations—is not typical in the homotopy-theoretic literature on cubical structure.

Initially, none of these cubical models was shown to be compatible with a Quillen model structure; they were models of HoTT (or of cubical type theories) in the direct sense that they gave an interpretation of the type-theoretic judgments, though they certainly made use of model-categorical intuitions. The connection with model category theory is first made precise in [GS17; Sat17], where it is shown that structure patterned on Cohen et al.'s cubical set model [CCHM15]—in particular, a functorial cylinder with connections—gives rise to a Quillen model structure. These methods were adapted by Cavallo, Mörtberg, and Swan [CMS20] and Awodey [Awo23] to presheaves over cartesian cube categories not necessarily supporting connections, producing model structures compatible with the type theories and interpretations of Angiuli et al. [AFH18; ABCHFL21]. Model structures in this lineage have been called cubical-type model structures.

It is now natural to ask which $(\infty, 1)$-categories these model structures present. In particular, we would like to know if any present $\infty$-Gpd: such a presentation would be a constructive setting for standard homotopy theory equipped with a constructive interpretation of HoTT, and could serve as a base case for constructing further constructive models following Shulman [Shu19]. However, Buchholtz and Sattler determined in 2018 [Coq+18; Sat18] that almost all concrete cubical-type model structures considered up to that point present $(\infty, 1)$-categories inequivalent to $\infty$-Gpd. The exception is the Sattler model structure $\square_{\wedge V}^{\mathrm{IV}}$ on presheaves on the Dedekind cube category $\square_{\wedge V}$, the cube category with cartesian structure and both connections, whose status remains an open problem.

### Cubes with one connection

The difficulty in analyzing the Dedekind cube category $\square_{\wedge V}$ is that it is not a (generalized) Reedy category [BM11], one in which each object is associated an ordinal degree and any morphism factors as a degeneracy-like degree-lowering map followed by a face-like degree-raising map. Any presheaf over a Reedy category can be built up inductively by attaching cells drawn from a set of generators, namely quotients of representables by automorphism subgroups. In the subclasses of elegant or Eilenberg-Zilber (EZ) categories, this cellular decomposition is moreover homotopically well-behaved with respect to any model structure in which the cofibrations are the monomorphisms: it exhibits any presheaf as the homotopy colimit of basic cells. The problem in $\square_{\wedge V}$ is the combination of connections and diagonals, exemplified the morphism $(x, y, z) \mapsto (x \vee y, y \vee z, x \wedge y)$

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

3

from the 3-cube to itself. This map has no (split epi, mono) factorization, a state of affairs forbidden in an elegant Reedy category.¹

Thus, while Sattler [Sat19] and Streicher and Weinberger [SW21] have identified an adjoint triple of Quillen adjunctions relating $\widehat{\Omega}_{\Lambda V}^{ty}$ and $\widehat{\Lambda}^{kq}$, it is not known whether there is a Quillen equivalence. In particular, it is unclear how to prove that a round-trip composite $\widehat{\Omega}_{\Lambda V}^{ty} \to \widehat{\Lambda}^{kq} \to \widehat{\Omega}_{\Lambda V}^{ty}$ is weakly equivalent to the identity in the absence of an elegant Reedy structure on $\Omega_{\Lambda V}$.

In this article we consider an overlooked cube category: the category $\Omega_V$ of cubes with cartesian structure and a single connection. (We arbitrarily choose the “max” or “negative” connection, but this choice plays no role.) Presheaves on this category satisfy conditions sufficient to obtain a cubical-type model structure $\widehat{\Omega}_V^{ty}$ using existing techniques [CMS20; Awo23]. Moreover, the arguments used in [Sat19; SW21] adapt readily from $\Omega_{\Lambda V}$ to $\Omega_V$, providing a Quillen adjoint triple relating $\widehat{\Omega}_V^{ty}$ with $\widehat{\Lambda}^{kq}$.

Like the Dedekind cube category, $\Omega_V$ is not Reedy. In this case, the archetypical problematic map is $(x, y, z) \mapsto (x \vee y, y \vee z, z \vee x)$.² However, $\Omega_V$ does embed nicely in a Reedy category, namely the category of finite inhabited join-semilattices: we have a functor $i: \Omega_V \to \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ sending the $n$-cube to the $n$-fold product of the poset $\{0 < 1\}$. While $\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ is not itself elegant, it satisfies a relativized form of elegance with respect to the subcategory $\Omega_V$. Whereas elegance would require the Yoneda embedding $\mathcal{L}: \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}} \to \mathrm{PSh}(\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}})$ to preserve pushouts of spans of degeneracy maps, here it is the nerve $N_i := i^* \mathcal{L}: \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}} \to \mathrm{PSh}(\Omega_V)$ that preserves such pushouts. We say that $\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ is elegant relative to $i$, or that $i$ is an elegant embedding.

We find that the useful properties of elegant Reedy categories can be extended, in an appropriately relativized form, to categories $\mathbf{C}$ with an elegant embedding $i: \mathbf{C} \to \mathbf{R}$ in a Reedy category. In particular, we show that any presheaf over $\mathbf{C}$ admits a homotopically well-behaved cellular decomposition whose cells are automorphism quotients of objects in the image of $N_i$. With these tools in hand, we are able to establish that the Quillen adjunctions relating $\widehat{\Omega}_V^{ty}$ and $\widehat{\Lambda}^{kq}$ are Quillen equivalences. We thus identify a cubical-type model structure presenting $\infty$-Gpd, compatible with a constructive interpretation of either HoTT or of cubical type theory with one connection.

## Outline

We begin in Section 2 with a brief review of model structures, Quillen equivalences, Reedy categories, and the Kan–Quillen model structure on simplicial sets. In Section 3, we present an improvement on the first part of [Sat17]: a series of increasingly specialized criteria under which candidate (cofibration, trivial fibration) and (trivial cofibration, fibration) factorization systems induce a model structure, culminating in a theorem tailored to models of type theory with universes.

¹A simpler map without a (split epi, mono) factorization in $\Omega_{\Lambda V}$ is $(x, y) \mapsto (x, x \vee y)$, but this is an idempotent and so admits such a factorization in the idempotent completion $\overline{\Omega}_{\Lambda V}$ (characterized in [Sat19, Theorem 2.1]). The aforementioned 3-cube endomap does not: it does have an (epi, mono) factorization in $\overline{\Omega}_{\Lambda V}$, but the left map does not split. It is the idempotent completion that counts when we consider whether elegant Reedy techniques apply.

²See Appendix A.1 for a proof that neither $\Omega_V$ nor its idempotent completion is Reedy.

2025/10/16 00:43

4

E. Cavallo and C. Sattler

In Section 4, we introduce the cube category $\square_{\vee}$ and its basic properties, construct the cubical-type model structure on $\mathrm{PSh}(\square_{\vee})$ using the results of the previous section, and define a triangulation adjunction $\mathrm{T}: \mathrm{PSh}(\square_{\vee}) \xrightarrow{\leftarrow} \mathrm{PSh}(\Delta): N_{\square}$. We moreover characterize the cube category's idempotent completion $\overline{\square}_{\vee}$. The categories of presheaves on $\square_{\vee}$ and $\overline{\square}_{\vee}$ are equivalent, but by working with the latter we can more easily compare with the simplex category, following [Sat19; SW21]. In particular we have an embedding $\blacktriangle: \Delta \to \overline{\square}_{\vee}$, thus an adjoint triple $\blacktriangle_{!} \dashv \blacktriangle^{*} \dashv \blacktriangle_{*}$ relating $\mathrm{PSh}(\Delta)$ and $\mathrm{PSh}(\overline{\square}_{\vee})$; the triangulation adjunction corresponds to $\blacktriangle^{*} \dashv \blacktriangle_{*}$ along the equivalence $\mathrm{PSh}(\square_{\vee}) \simeq \mathrm{PSh}(\overline{\square}_{\vee})$. In Section 4.4 we show that both $\blacktriangle_{!} \dashv \blacktriangle^{*}$ and $\blacktriangle^{*} \dashv \blacktriangle_{*}$ are Quillen adjunctions.

We focus on the adjunction $\blacktriangle_{!} \dashv \blacktriangle^{*}$. It is easy to see that its derived unit is valued in weak equivalences, as $\blacktriangle$ is fully faithful. To show its derived counit is valued in weak equivalences, we spend Section 5 developing a theory of relative elegance. In Section 6, we show that the functor $i: \square_{\vee} \to \mathbf{SLat}_{\mathrm{im}}^{\mathrm{inh}}$ is relatively elegant by way of a general analysis of Reedy categories of finite algebras. In Section 7 we use this result to complete the Quillen equivalence between $\widehat{\square}_{\vee}^{\mathrm{ty}}$ and $\widehat{\Delta}^{\mathrm{kq}}$. We show first that $\blacktriangle_{!} \dashv \blacktriangle^{*}$ is a Quillen equivalence, then deduce that $\blacktriangle^{*} \dashv \blacktriangle_{*}$ is one as well, concluding with our main theorem as an immediate corollary:

Theorem 7.8 The triangulation-nerve adjunction $\mathrm{T}: \widehat{\square}_{\vee}^{\mathrm{ty}} \xrightarrow{\leftarrow} \widehat{\Delta}^{\mathrm{kq}}: N_{\square}$ is a Quillen equivalence.

As a final corollary, we show in Section 7.2 that $\widehat{\square}_{\vee}^{\mathrm{ty}}$ coincides with Cisinski's test model structure on $\mathrm{PSh}(\square_{\vee})$.

In Appendix A, we give proofs of some negative results concerning Reedy structures on cartesian cube categories with connections. First, we check that neither $\square_{\vee}$ nor its idempotent completion supports a Reedy structure, justifying our recourse to relative elegance. Second, we prove that $\square_{\wedge \vee}$ does not embed elegantly in any Reedy category, showing that our techniques cannot be applied in the two-connection case.

# 1.1 Related work

# 1.1.1 Cartesian cubes

This work's closest relative is the equivariant model structure $\widehat{\square}_{\times}^{\mathrm{eq}}$ on presheaves over the cartesian cube category $\square_{\times}$ constructed by Awodey, Cavallo, Coquand, Riehl, and Sattler (ACCRS) [ACCRS24], which also classically presents $\infty$-Gpd. The ACCRS construction is a modification of earlier models in presheaves on $\square_{\times}$ [ABCHFL21; CMS20; Awo23]. Briefly, where the definition of fibration involves lifting against maps $1 \to \mathbb{I}$ from the point to the interval, the definition of equivariant fibration involves lifting against maps $1 \to \mathbb{I}^n$ for all $n$ and requires lifts stable under permutations of $\mathbb{I}^n$. Like our own model structure, $\widehat{\square}_{\times}^{\mathrm{eq}}$ is compatible with a constructive interpretation of HoTT.

In $\widehat{\square}_{\vee}^{\mathrm{ty}}$, equivariance does not appear explicitly but is still implicitly present: when the interval supports a connection operator, ordinary and equivariant lifting become interderivable (see Remark 4.25). Our model structure may thus be seen as an instance of the equivariant model structure construction applied in $\mathrm{PSh}(\square_{\vee})$, one which happens to admit a simpler description.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

5

### 1.1.2 Test category theory

Buchholtz and Morehouse [BM17] catalogue a number of categories of cubical sets, specifically investigating cube categories used in models of HoTT such as $\Box_{\times}$, $\Box_{\wedge\vee}$, and the De Morgan cube category. They observe that these categories are all test categories, thus that each supports a test model structure equivalent to $\widehat{\Delta}^{\mathrm{kq}}$ [Cis06]. To our knowledge, however, none of these model structures is known to be compatible with a model of HoTT with the exception of the test model structure on $\Box_{\times}$, which coincides with $\widehat{\Box}_{\times}^{\mathrm{kq}}$ [ACCRS24, Theorem 6.3.6]. As a corollary of our Quillen equivalence, we check in Section 7.2 that $\widehat{\Box}_{\vee}^{\mathrm{ry}}$ coincides with the test model structure on $\Box_{\vee}$. Cisinski [Cis14] does show that the test model structure on any elegant strict (that is, non-generalized) Reedy category is compatible with a model of HoTT, but the strictness condition precludes application to any cube category with permutations.

### 1.1.3 Cubes with one connection

To our knowledge, the category of cubes with cartesian structure and $\vee$-connections (or $\wedge$-connections) has not been studied before, except in passing by Buchholtz and Morehouse [BM17], though cartesian cube categories with both $\vee$- and $\wedge$-connections have been used in interpretations of HoTT beginning with Cohen et al. [CCHM15].

On the other hand, subcategories without diagonals have seen use in classical homotopy theory. Indeed, Brown and Higgins use the cube category generated by faces, degeneracies, and $\vee$-connections in their seminal article introducing connections for cubical sets [BH81]. Isaacson [Isa11] studies the cube category with faces, degeneracies, symmetries, and $\wedge$-connections. Unlike $\Box_{\vee}$, these are elegant Reedy categories [Mal09, Remarque 5.6; Isa11, Proposition 3.4]: connections are only problematic in combination with diagonals. They furthermore have useful properties compared to the minimal cube category (generated by faces and degeneracies). For one, they are strict test categories [Mal09; BM17, Theorem 3], meaning that the localization functor from the test model structures on these cubical sets to their homotopy categories preserves products.

It should be noted, however, that this particular distinction disappears in the cartesian cases: any cube category with cartesian structure is a strict test category, regardless of the presence of connections [BM17, Corollary 2]. For us, the convenient properties of $\Box_{\vee}$ relative to $\Box_{\times}$ are (1) the existence of an embedding from the simplex category into the idempotent completion of $\Box_{\vee}$, which facilitates the comparison between their presheaf categories, and (2) the existence of a contracting homotopy of each $n$-cube invariant under permutations, namely $(x_1, \dots, x_n, t) \mapsto (x_1 \vee t, \dots, x_n \vee t) : [1]^n \times [1] \to [1]^n$.

### 1.1.4 Constructive simplicial models

Another line of work aims to reformulate the Kan–Quillen model structure and Voevodsky's simplicial model of HoTT so that these can be obtained constructively. Bezem, Coquand, and Parmann [BC15; BCP15; Par18] show that fibrations as usually defined$^3$ in $\widehat{\Delta}^{\mathrm{kq}}$ do not provide a model of HoTT constructively; in particular, they are not closed under pushforward along fibrations, which is necessary to interpret $\Pi$-types. These

$^3$[BC15; Par18] prove obstructions for a definition of fibration where lifting is treated as an operation, while [BCP15] considers fibrations requiring mere existence of a lift.

2025/10/16 00:43

6

E. Cavallo and C. Sattler

obstructions are avoided in the cubical models by working with uniform fibrations, which classically coincide with ordinary fibrations but provide necessary extra structure in the constructive case. However, there are obstructions to constructing a universe classifying uniform fibrations in simplicial sets [BF22, Appendix D; Swa22, §8.4.1].

Henry [Hen25] discovered that the Kan–Quillen model structure can be constructivized by instead modifying the class of cofibrations, in particular taking a simplicial set to be cofibrant only when degeneracy of its cells is decidable. Alternative constructions of the same model structure were later presented by Gambino, Sattler, and Szumiło [GSS22]. Gambino and Henry [GH22] exhibit a constructive form of Voevodsky's simplicial model of HoTT using these ideas. The problem is not entirely settled, however: the left adjoint splitting coherence construction [LW15], applied to the classical simplicial model to obtain a strict model of type theory, does not apply constructively in this case [GH22, Remark 8.5]. There has since been progress on coherence theorems that do apply here [Boc22; GL21], but the question is not to our knowledge fully resolved. Separately, van den Berg and Faber [BF22] have identified and developed a theory of effective fibrations of simplicial sets, which are both closed under pushforward and support a classifying universe, but have not yet addressed the interpretation of univalence.

### 1.1.5 Constructivity

Though our interest in cubical-type model structures is motivated by constructive concerns, we work entirely and incautiously within a classical metatheory in this article, our goal being an equivalence with a classically defined model structure. Given that $\widehat{\square}_{\nu}^{iy}$ is constructively definable, however, it is natural to wonder whether it is constructively equivalent with the ACCRS or constructive simplicial model structures. We leave this question for the future, referring to Shulman [Shu23] for further discussion of the constructive homotopy theory of spaces.

We note that the triangulation functor T: PSh($\square_{\nu}$) $\to$ PSh($\Delta$) (Definition 4.35) is definitely not a left Quillen adjoint from $\widehat{\square}_{\nu}^{iy}$ to Henry's simplicial model structure constructively, as it does not preserve cofibrations unless the excluded middle holds. The (triangulation, nerve) adjunction exhibits PSh($\Delta$) as a reflective subcategory of PSh($\square_{\nu}$), so every simplicial set is the triangulation of some cubical set. But while every cubical set is cofibrant in $\widehat{\square}_{\nu}^{iy}$, not every simplicial set is cofibrant in Henry's model structure. For example, given a subsingleton set P, the pushout of the span $\Delta^1 \leftarrow \Delta^1 \times P \rightarrow P$ is cofibrant if and only if P is decidable.

### 1.1.6 Reedy, non-Reedy, and Reedy-like categories

Campion [Cam23] studies the existence and non-existence of elegant Reedy structures on various cube categories, among them $\square_{\nu}$ (under the name $\square_{d,c^{\vee},s}$). A few observations are made independently in that article and our own; in particular, [Cam23, Proposition 8.3] is our Theorem 4.46, while [Cam23, Theorem 8.12(2)] follows from our Proposition A.1.

Shulman's almost c-Reedy categories [Shu15, Definition 8.8] generalize beyond generalized Reedy categories. These allow for non-isomorphisms that do not factor through a lower-degree object, so one may wonder if the aforementioned pathological map $u: [1]^3 \to [1]^3$ in $\square_{\nu}$ (and $\overline{\square}_{\nu}$) defined by $(x, y, z) \mapsto (x \vee y, y \vee z, z \vee x)$ can be

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

7

accommodated in this way. However, the class of degree-preserving maps not admitting a lower-degree factorization must be closed under composition [Shu15, Theorem 8.13(ii)]. While u factors through no lower-dimensional object, uu factors through the 1-cube. As such, this generalization is unlikely to be helpful here.

## 1.2 Acknowledgments

We thank Steve Awodey, Thierry Coquand, and Emily Riehl, our collaboration with whom inspired this spin-off project, for their suggestions and feedback. We also thank Emily Riehl for alerting us to errors in the first preprint version of this article. The idea of embedding non-Reedy cube categories in larger Reedy categories came to us via Matthew Weaver and Daniel Licata, who experimented with (but did not ultimately use) this strategy in work on cubical models of directed type theory [WL20]. The first author thanks Brandon Doherty, Anders Mörtberg, Axel Ljungström, and Matthew Weaver for helpful conversations. We credit an observation of Imrich, Kalinowski, Lehner, and Piłśniak [IKLP14, Lemma 2] for inspiring the argument in Appendix A.2.2.

## 2 Background

### 2.1 Preliminaries

We begin by fixing a few notational conventions.

Notation 2.1 We write [E, F] for the category of functors from E and F. We write PSh(C) := [C^op, Set] for the category of presheaves on a category C and ∗: C → PSh(C) for the Yoneda embedding.

Notation 2.2 When regarding a functor as a diagram, we use superscripts for covariant indexing and subscripts for contravariant indexing. Thus if F: D → E then we have F^d ∈ E for d ∈ D, while if F: C^op → E then we have F_c ∈ E for c ∈ C. We sometimes partially apply a multi-argument functor: given F: C^op × D → E and c ∈ C, d ∈ D, we have F_c ∈ D → E, F^d ∈ C^op → E, and F_c^d ∈ E.

By a bifunctor we mean a functor in two arguments. We make repeated use of the Leibniz construction [RV14, Definition 4.4], which transforms a bifunctor into an bifunctor on arrow categories.

Definition 2.3 Given a bifunctor ⊙: C × D → E into a category E with pushouts, the Leibniz construction defines a bifunctor ⊖: C^→ × D^→ → E^→, with f ⊖ g defined for

2025/10/16 00:43

8

E. Cavallo and C. Sattler

$f: A \rightarrow B$ and $g: X \rightarrow Y$ as the following induced map:

![img-0.jpeg](img-0.jpeg)

**Example 2.4** If $\mathbf{E}$ is a category with binary products and pushouts, applying the Leibniz construction to the binary product functor $\times: \mathbf{E} \times \mathbf{E} \rightarrow \mathbf{E}$ produces the *pushout product* bifunctor $\bar{\times}: \mathbf{E}^{\rightarrow} \times \mathbf{E}^{\rightarrow} \rightarrow \mathbf{E}^{\rightarrow}$.

## 2.2 Model structures and Quillen equivalences

In the abstract, the force of our result is that a certain model category presents the $(\infty, 1)$-category of $\infty$-groupoids. Concretely, we work entirely in model-categorical terms, exhibiting a Quillen equivalence between this model category and another model category—simplicial sets—already known to present $\infty$-**Gpd**. We briefly fix the relevant basic definitions here but assume prior familiarity, especially with factorization systems; standard references include [Hov99; DHKS04].

**Definition 2.5** A *model structure* on a category $\mathbf{M}$ is a triple $(\mathcal{C}, \mathcal{W}, \mathcal{F})$ of classes of morphisms in $\mathbf{M}$, called the *cofibrations*, *weak equivalences*, and *fibrations* respectively, such that $(\mathcal{C}, \mathcal{F} \cap \mathcal{W})$ and $(\mathcal{C} \cap \mathcal{W}, \mathcal{F})$ are weak factorization systems and $\mathcal{W}$ satisfies the 2-out-of-3 property. A *model category* is a finitely complete and cocomplete category equipped with a model structure. We use the arrow $\mapsto$ for cofibrations, $\Rightarrow$ for weak equivalences, and $\rightarrow$ for fibrations. Maps in $\mathcal{C} \cap \mathcal{W}$ and $\mathcal{F} \cap \mathcal{W}$ are called *trivial* cofibrations and fibrations respectively.

We say that a model structure on $\mathbf{M}$ *has monos as cofibrations* when its class of cofibrations is exactly the class of monomorphisms in $\mathbf{M}$.$^4$

**Definition 2.6** We say an object is *cofibrant* when $0 \rightarrow A$ is a cofibration, dually *fibrant* if $A \rightarrow 1$ is a fibration. The weak factorization system $(\mathcal{C}, \mathcal{F} \cap \mathcal{W})$ implies that for every object $A$, we have a diagram $0 \mapsto A^{\text{cof}} \Rightarrow A$ obtained by factorizing $0 \rightarrow A$; we say such an $A^{\text{cof}}$ is a *cofibrant replacement* of $A$. Likewise, an object $A^{\text{fib}}$ sitting in a diagram $A \mapsto A^{\text{fib}} \rightarrow 1$ is a *fibrant replacement* of $A$.

**Definition 2.7** We say an object $X$ in a model category is *weakly contractible* when the map $X \rightarrow 1$ is a weak equivalence.

$^4$Such a model structure which is also cofibrantly generated (see below) is called a *Cisinski model structure*, these being the subject of [Cis06].

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

9

Note that given any two of the classes $(\mathcal{C}, \mathcal{W}, \mathcal{F})$, we can reconstruct the third: $\mathcal{C}$ is the class of maps with left lifting against $\mathcal{F} \cap \mathcal{W}$, $\mathcal{F}$ is the class of maps with right lifting against $\mathcal{C} \cap \mathcal{W}$, and $\mathcal{W}$ is the class of maps that can be factored as a map with left lifting against $\mathcal{F}$ followed by a map with right lifting against $\mathcal{C}$. We will thus frequently introduce a model category by giving a description of two of its classes.

The two factorization systems are commonly generated by sets of left maps:

Definition 2.8 We say a weak factorization system $(\mathcal{L}, \mathcal{R})$ on a category $\mathbf{E}$ is cofibrantly generated by some set $S \subseteq \mathcal{L}$ when $\mathcal{R}$ is the class of maps with the right lifting property against all maps in $S$. A model structure is cofibrantly generated when its component weak factorization systems are.

Now we come to relationships between model categories.

Definition 2.9 A Quillen adjunction between model categories $\mathbf{M}$ and $\mathbf{N}$ is a pair of adjoint functors $F: \mathbf{M} \xrightarrow{\text{def}} \mathbf{N}: G$ such that $F$ preserves cofibrations and $G$ preserves fibrations.

Note that $F$ preserves cofibrations if and only if $G$ preserves trivial fibrations, while $G$ preserves fibrations if and only if $F$ preserves trivial cofibrations.

Definition 2.10 A Quillen adjunction $F: \mathbf{M} \xrightarrow{\text{def}} \mathbf{N}: G$ is a Quillen equivalence when

- for every cofibrant $X \in \mathbf{M}$, the derived unit $X \xrightarrow{n_X} GFX \xrightarrow{Gm} G((FX)^{\mathrm{fib}})$ is a weak equivalence for some fibrant replacement $m: FX \mapsto (FX)^{\mathrm{fib}}$;
- for every fibrant $Y \in \mathbf{N}$, the derived counit $F((GY)^{\mathrm{cof}}) \xrightarrow{Fp} FGY \xrightarrow{FY} Y$ is a weak equivalence for some cofibrant replacement $p: (GY)^{\mathrm{cof}} \xrightarrow{\circ} GY$.

Two model structures are Quillen equivalent when there is a zigzag of Quillen equivalences connecting them.

## 2.3 Reedy categories and elegance

The linchpin of our approach is Reedy category theory, the theory of diagrams over categories whose morphisms factor into degeneracy-like and face-like components. As our base category of interest contains non-trivial isomorphisms, we work more specifically with the generalized Reedy categories introduced by Berger and Moerdijk [BM11].

Definition 2.11 A (generalized) Reedy structure on a category $\mathbf{R}$ consists of an orthogonal factorization system $(\mathbf{R}^{-}, \mathbf{R}^{+})$ on $\mathbf{R}$ together with a degree map $|-|: \operatorname{Ob} \mathbf{R} \to \mathbb{N}$, compatible in the following sense: given $f: a \to b$ in $\mathbf{R}^{-}$ (resp. $\mathbf{R}^{+}$), we have $|a| \geq |b|$ (resp. $|a| \leq |b|$), with $|a| = |b|$ only if $f$ is invertible.

We refer to maps in $\mathbf{R}^{-}$ as lowering maps and maps in $\mathbf{R}^{+}$ as raising maps, and we use the annotated arrows $\xrightarrow{\circ}$ and $\xrightarrow{\circ}$ to denote lowering and raising maps respectively. The degree of a map is the degree of the intermediate object in its Reedy factorization. Note

2025/10/16 00:43

10

E. Cavallo and C. Sattler

that this definition is self-dual: if R is a Reedy category, then R^op is a Reedy category with the same degree function but with lowering and raising maps swapped.

Terminology 2.12 We henceforth drop the qualifier generalized, as we are almost always working with generalized Reedy categories. Instead, we say a Reedy category is strict if any parallel isomorphisms are equal and it is skeletal, i.e., it is a Reedy category in the original sense.

The prototypical strict Reedy category is the simplex category Δ: the degree of an n-simplex is n, while the lowering and raising maps are the degeneracy and face maps respectively [GZ67, §II.3.2].

A Reedy structure on a category R is essentially a tool for working with R-shaped diagrams. For example, a weak factorization system on any category E induces injective and projective Reedy weak factorization systems on the category [R, E] of R-shaped diagrams in E; likewise for model structures. Importantly for us, any diagram of shape R can be regarded as built iteratively from "partial" diagrams specifying the elements at indices up to a given degree. We are specifically interested in presheaves, i.e., R^op-shaped diagrams in Set. We refer to [DHKS04, §22; BM11; RV14; Shu15] for overviews of Reedy categories and their applications.

Berger and Moerdijk's definition of generalized Reedy category [BM11, Definition 1.1] includes one additional axiom. Following Riehl [Rie17], we treat this as a property to be assumed only where necessary:

Definition 2.13 In a Reedy category R, we say isos act freely on lowering maps when for any e : r → s and isomorphism θ : s ≅ s, if θe = e then θ = id.

Note that any Reedy category in which all lowering maps are epic satisfies this property. The main results of this paper are restricted to pre-elegant Reedy categories (Definition 5.28) for which this is always the case (Lemma 5.29); nevertheless, we try to record where only the weaker assumption is needed.

The following cancellation property will come in handy.

Lemma 2.14 Let f : r → s, g : s → t be maps in a Reedy category. If gf is a lowering map, then so is g. Dually, if gf is a raising map, then so is f.

Proof We prove the first statement; the second follows by duality. Suppose gf is a lowering map. We take Reedy factorizations f = me, g = m'e', and then e'm = m''e'':

![img-1.jpeg](img-1.jpeg)

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

11

This gives us a Reedy factorization $g f = (m'm'')(e''e)$. By uniqueness of factorizations, $m'm''$ must be an isomorphism; this implies $|t''| = |t'| = |r|$, so $m'$ and $m''$ are also isomorphisms. Thus $g \cong e'$ is a lowering map.

Corollary 2.15 Any split epimorphism in a Reedy category is a lowering map; dually, any split monomorphism is a raising map.

When studying Set-valued presheaves over a Reedy category, it is useful to consider the narrower class of elegant Reedy categories [BM11; BR13].

Definition 2.16 A Reedy structure on a category $\mathbf{R}$ is elegant when

- (a) any span $s \stackrel{e}{\leftarrow} r \stackrel{e'}{\rightarrow} s'$ consisting of lowering maps $e, e'$ has a pushout;
- (b) the Yoneda embedding $\mathfrak{K}: \mathbf{R} \to \mathrm{PSh}(\mathbf{R})$ preserves these pushouts.

We refer to spans consisting of lowering maps as lowering spans, likewise pushouts of such spans as lowering pushouts. Note that all the maps in a lowering pushout square are lowering maps, as the left class of any factorization system is closed under cobase change.

Intuitively, an elegant Reedy category is one where any pair of "degeneracies" $s \stackrel{\leftarrow}{\leftarrow} r \stackrel{\rightarrow}{\rightarrow} s'$ has a universal "combination" $r \stackrel{\rightarrow}{\rightarrow} s \sqcup_r s'$, namely the diagonal of their pushout. The condition on the Yoneda embedding asks that any $r$-cell in a presheaf is degenerate along (that is, factors through) both $r \stackrel{\rightarrow}{\rightarrow} s$ and $r \stackrel{\rightarrow}{\rightarrow} s'$ if and only if it is degenerate along their combination. Again, the simplex category is the prototypical elegant Reedy category [GZ67, §II.3.2].

Remark 2.17 This definition is one of a few equivalent formulations introduced by Bergner and Rezk [BR13, Definition 3.5, Proposition 3.8] for strict Reedy categories. For generalized Reedy categories, Berger and Moerdijk [BM11, Definition 6.7] define Eilenberg-Zilber (or EZ) categories, which additionally require that $\mathbf{R}^+$ and $\mathbf{R}^-$ are exactly the monomorphisms and split epimorphisms respectively. We make do without this restriction. It is always the case that the lowering maps in an elegant Reedy category are the split epis (see Remark 5.39 below), but the raising maps need not be monic. For example [Cam23, Example 4.3], any direct category (that is, any Reedy category with $\mathbf{R}^+ = \mathbf{R}^-$) is elegant, but a direct category can contain non-monic arrows.

A presheaf $X \in \mathrm{PSh}(\mathbf{R})$ over any Reedy category can be written as the sequential colimit of a sequence of $n$-skeleta containing non-degenerate cells of $X$ only up to degree $n$, with the maps between successive skeleta obtained as cobase changes of certain basic cell maps. When $\mathbf{R}$ is elegant, these cell maps are moreover monic. This property gives rise to a kind of induction principle: any property closed under certain colimits can be verified for all presheaves on an elegant Reedy category by checking that it holds on basic cells. This principle is conveniently encapsulated by the following definition.

Definition 2.18 (Cis19, Definition 1.3.9) Let a category $\mathbf{E}$ be given. We say a replete class of objects $\mathcal{P} \subseteq \mathbf{E}$ is saturated by monomorphisms when

2025/10/16 00:43

12

E. Cavallo and C. Sattler

(a) $\mathcal{P}$ is closed under small coproducts;
(b) For every pushout square

![img-2.jpeg](img-2.jpeg)

such that $X, X', Y \in \mathcal{P}$, we have $Y' \in \mathcal{P}$;

(c) For every diagram $X: \omega \to \mathbf{E}$ such that each object $X^i$ is in $\mathcal{P}$ and each morphism $X^i \to X^{i+1}$ is monic, we have $\operatorname{colim}_{i < \omega} X^i \in \mathcal{P}$.

We note that when $\mathbf{E}$ is a model category with monos as cofibrations, these are all diagrams whose colimits agree with their homotopy colimits: we can compute their colimits in the $(\infty, 1)$-category presented by $\mathbf{E}$ by simply computing their 1-categorical colimits in $\mathbf{E}$, which is hardly the case in general. This fact is another application of Reedy category theory; see for example Dugger [Dug08, §14]. As a result, these colimits have homotopical properties analogous to 1-categorical properties of colimits. For example, recall that given a natural transformation $\alpha: F \to G$ between left adjoint functors $F, G: \mathbf{E} \to \mathbf{F}$, the class of $X \in \mathbf{E}$ such that $\alpha_X$ is an isomorphism is closed under colimits. If $F, G$ are left Quillen adjoints and $\mathbf{E}, \mathbf{F}$ have monomorphisms as cofibrations, then the class of $X$ such that $\alpha_X$ is a weak equivalence is saturated by monomorphisms. This particular fact will be key in Section 7.1.

For presheaves over an elegant Reedy category, the basic cells are the quotients of representables by automorphism subgroups.

Definition 2.19 Given an object $X$ of a category $\mathbf{E}$ and a subgroup $H \leq \operatorname{Aut}_{\mathbf{E}}(X)$, their quotient is the colimit $X/H := \operatorname{colim}(H \to \operatorname{Aut}_{\mathbf{E}}(X) \to \mathbf{E})$.

Proposition 2.20 Let $\mathbf{R}$ be an elegant Reedy category. Let $\mathcal{P} \subseteq \operatorname{PSh}(\mathbf{R})$ be a class of objects such that

- for any $r \in \mathbf{R}$ and $H \leq \operatorname{Aut}_{\mathbf{R}}(r)$, we have $\not\leq r/H \in \mathcal{P}$;
- $\mathcal{P}$ is saturated by monomorphisms.

Then $\mathcal{P}$ contains all objects of $\operatorname{PSh}(\mathbf{R})$.

Proof [Cis19, Corollary 1.3.10] gives a proof for strict elegant Reedy categories; the proof for the generalized case is similar (and a special case of our Theorem 5.47).

As described above, we will be studying a category $\square_{\vee}$ that is not a Reedy category. Thus, we will not use the previous proposition directly. Instead, our Section 5 establishes a generalization to categories that only embed in a Reedy category in a nice way.

### 2.4 Simplicial sets

To show that a given model category presents $\infty$-Gpd, it suffices to exhibit a Quillen equivalence to a model category already known to present $\infty$-Gpd. Here, our standard of

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

13

comparison will be the classical Kan–Quillen model structure on simplicial sets [Qui67, §II.3].

Definition 2.21 The simplex category $\Delta$ is the full subcategory of the category **Pos** of posets and monotone maps consisting of the finite inhabited linear orders $[n] := \{0 < \cdots < n\}$ for $n \in \mathbb{N}$.

This is a strict Reedy category, in fact an Eilenberg-Zilber category (see Remark 2.17). The raising and lowering maps are given by the *face* and *degeneracy maps*, defined as the injective and surjective maps of posets, respectively.

Definition 2.22 We define the usual generating maps of the simplex category:

- given $n \ge 0$ and $i \in [n]$, the *generating degeneracy map* $s_i: [n+1] \to [n]$ identifies the elements $i$ and $i+1$ of $[n+1]$,
- given $n \ge 1$ and $i \in [n]$, the *generating face map* $d_i: [n-1] \to [n]$ skips over the element $i$ of $[n]$.

Definition 2.23 Write $\Delta^n \in \mathrm{PSh}(\Delta)$ for the representable $n$-simplex $\not\perp [n]$. We define the following sets of maps in simplicial sets:

- For $n \ge 0$, the *boundary inclusion* $\partial \Delta^n \mapsto \Delta^n$ is the union of the subobjects $\Delta^i \mapsto \Delta^n$ given by a non-invertible face map $[i] \to [n]$.
- For $n \ge 1$ and $0 \le k \le n$, the $k$-*horn* $\Lambda_k^n \mapsto \Delta^n$ is the union of the subobjects $\Delta^i \mapsto \Delta^n$ given by a face map $d: [i] \to [n]$ whose pullback along $[n] - k \mapsto [n]$ is non-invertible.

Proposition 2.24 (Kan–Quillen model structure) There is a model structure on $\mathrm{PSh}(\Delta)$ with the following weak factorization systems:

- the weak factorization system (cofibration, trivial fibration) is *cofibrantly generated by the boundary inclusions*;
- the weak factorization system (trivial cofibration, fibration) is *cofibrantly generated by the horn inclusions*.

We write $\widehat{\Delta}^{\mathrm{kq}}$ for this model category.

Proof This is Theorem 3 and the following Proposition 2 in [Qui67, §II.3].

Proposition 2.25 (GZ67, §IV.2) The weak factorization systems of $\widehat{\Delta}^{\mathrm{kq}}$ admit the following alternative descriptions:

- the cofibrations are the monomorphisms; the trivial fibrations are the maps right lifting against monomorphisms.
- the weak factorization system (trivial cofibration, fibration) is generated by pushout products $d_k \asymp m$ of an endpoint inclusion $d_k: 1 \to \Delta^1$ with a monomorphism $m: A \mapsto B$.

2025/10/16 00:43

14

E. Cavallo and C. Sattler

### 3 Model structures from cubical models of type theory

As the cube category $\square_{\nu}$ is cartesian, we may obtain our cubical-type model structure on PSh($\square_{\nu}$) immediately by applying existing arguments [CMS20; Awo23], which build on a criterion for recognizing model structures introduced in the first part of [Sat17]. We will instead take the opportunity to present an improvement on the latter criterion, hoping to give an idea of the character of these model structures along the way.

We begin in Section 3.1 with a set of conditions necessary and sufficient to determine when a premodel structure—essentially, all the ingredients of a model structure except 2-out-of-3 for weak equivalences—is in fact a model structure. In Section 3.2, we give a simplified set of conditions for the case where the premodel structure is equipped with a compatible adjoint functorial cylinder. Finally, in Section 3.3 we show that such a cylindrical premodel structure satisfies these conditions when all its objects are cofibrant and it satisfies the fibration extension property. We shall apply this result in Section 4.2 to obtain our model structure on PSh($\square_{\nu}$); a reader who would prefer to take the existence of the model structure for granted may skip this section and read only Theorem 4.34 in Section 4.2.

### 3.1 Model structures from premodel structures

Definition 3.1 (Bar19, Definition 2.1.23) A premodel structure on a finitely complete and cocomplete category $\mathbf{M}$ consists of weak factorization systems $(C, \mathcal{F}_t)$ (the cofibrations and trivial fibrations) and $(C_t, \mathcal{F})$ (the trivial cofibrations and fibrations) on $\mathbf{M}$ such that $C_t \subseteq C$ (or equivalently $\mathcal{F}_t \subseteq \mathcal{F}$).

Remark 3.2 (Stability under (co)slicing) Given an object $X \in \mathbf{M}$, any weak factorization system on $\mathbf{M}$ descends to weak factorization systems on the slice over $X$ and the coslice under $X$, with left and right classes created by the respective forgetful functor to $\mathbf{M}$. In the same fashion, any premodel structure on $\mathbf{M}$ descends to slices and coslices of $\mathbf{M}$.

As any two of the classes $(C, \mathcal{W}, \mathcal{F})$ defining a model structure determines the third, any premodel structure induces a candidate class of weak equivalences.

Definition 3.3 We say that a morphism in a premodel structure is a weak equivalence if it factors as a trivial cofibration followed by a trivial fibration; we write $\mathcal{W}(C, \mathcal{F})$ for the class of such morphisms.

Remark 3.4 The above definition is only necessarily appropriate when examining when a premodel structure forms a model structure: there are premodel structures with a useful definition of weak equivalence not agreeing with $\mathcal{W}(C, \mathcal{F})$. For example, there are various weak model structures on semisimplicial sets in which not all trivial fibrations are weak equivalences [Hen20, Remark 5.5.7].

For the remainder of this section, we fix a premodel category $\mathbf{M}$ with factorization systems $(C, \mathcal{F}_t)$ and $(C_t, \mathcal{F})$. The following two propositions are standard.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

15

Proposition 3.5 $C_t = C \cap \mathcal{W}(C, \mathcal{F})$ and $\mathcal{F}_t = \mathcal{F} \cap \mathcal{W}(C, \mathcal{F})$.

Proof An immediate consequence of the retract argument [Hov99, Lemma 1.1.9].

In light of the above, we use the arrows $\leftrightarrow$ and $\Rightarrow$ to denote trivial cofibrations and fibrations also in a premodel structure.

Corollary 3.6 $(C, \mathcal{W}(C, \mathcal{F}), \mathcal{F})$ forms a model structure if and only if $\mathcal{W}(C, \mathcal{F})$ satisfies 2-out-of-3.

We now reduce the problem of checking 2-out-of-3 for $\mathcal{W}(C, \mathcal{F})$ to a reduced collection of special cases of 2-out-of-3 where some or all maps belong to $C$ or $\mathcal{F}$.

Definition 3.7 Given a wide subcategory $\mathcal{A} \subseteq \mathbf{E}$ of a category $\mathbf{E}$, we say $\mathcal{A}$ has left cancellation in $\mathbf{E}$ (or among maps in $\mathbf{E}$) when for every composable pair $g, f$ in $\mathbf{E}$, if $gf$ and $g$ are in $\mathcal{A}$ then $f$ is in $\mathcal{A}$. Dually, $\mathcal{A}$ has right cancellation in $\mathbf{E}$ when for all $g, f$ with $gf, f \in \mathcal{A}$, we have $g \in \mathcal{A}$.

Theorem 3.8 $\mathcal{W}(C, \mathcal{F})$ satisfies 2-out-of-3 exactly if the following hold:

- (A) trivial cofibrations have left cancellation among cofibrations and trivial fibrations have right cancellation among fibrations.
- (B) any (cofibration, trivial fibration) factorization or (trivial cofibration, fibration) factorization of a weak equivalence is a (trivial cofibration, trivial fibration) factorization;
- (C) any composite of a trivial fibration followed by a trivial cofibration is a weak equivalence.

Note that each of these conditions is self-dual.

Proof Conditions A–C all follow by straightforward applications of 2-out-of-3 for $\mathcal{W}(C, \mathcal{F})$. Suppose conversely that we have A–C and let maps $g: Y \to Z$ and $f: X \to Y$ be given. Then using the two factorization systems and condition C, we have the following diagram:

![img-3.jpeg](img-3.jpeg)

Suppose first that $g$ and $f$ are weak equivalences. Then we may choose the factorizations of $f$ and $g$ such that the map $X \leftrightarrow U$ is a trivial cofibration and the map $V \to Z$ is a trivial fibration. Thus $gf$ factors as a trivial cofibration followed by a trivial fibration, i.e., is a weak equivalence.

Now suppose that $f$ and $gf$ are weak equivalences. We may choose the factorization of $f$ such that the map $X \leftrightarrow U$ is a trivial cofibration. The composite $X \leftrightarrow W$ is then a trivial cofibration, so the composite $W \to Z$ is a trivial fibration by condition B. Then

2025/10/16 00:43

16

E. Cavallo and C. Sattler

the map $V \to Z$ is a trivial fibration by condition A. Hence $g$ is a weak equivalence. By the dual argument, if $g$ and $gf$ are weak equivalences then so is $f$.

### 3.2 Cylindrical premodel structures

Now we derive a simpler set of criteria for premodel structures equipped with a compatible adjoint functorial cylinder.

Definition 3.9 A functorial cylinder on a category $\mathbf{E}$ is a functor $\mathbb{I} \otimes (-): \mathbf{E} \to \mathbf{E}$ equipped with endpoint and contraction transformations fitting in a diagram as shown:

![img-4.jpeg](img-4.jpeg)

An adjoint functorial cylinder is a cylinder such that $\mathbb{I} \otimes (-)$ is a left adjoint.

Notation 3.10 Given a functorial cylinder in a finitely cocomplete category, we have induced boundary maps $\partial \otimes X := [\delta_0 \otimes X, \delta_1 \otimes X]: X \sqcup X \to \mathbb{I} \otimes X$.

There is a dual notion of functorial path object consisting of a functor $\mathbb{I} \oslash (-)$ and natural transformations $\delta_k \oslash (-): \mathbb{I} \otimes (-) \to \mathrm{Id}$ and $\varepsilon \oslash (-): \mathrm{Id} \to \mathbb{I} \otimes (-)$. By transposition, each adjoint functorial cylinder corresponds to an adjoint functorial path object.

Remark 3.11 (Stability under (co)slicing) Fix a functorial cylinder denoted as above and an object $X \in \mathbf{E}$. Then $\mathbb{I} \otimes (-)$ lifts through the forgetful functor $\mathbf{E}/X \to \mathbf{E}$ to a functorial cylinder $\mathbb{I} \otimes_{\mathbf{E}/X} (-)$ on the slice over $X$. This crucially uses the contraction. For example, the action of $\mathbb{I} \otimes_{\mathbf{E}/X} (-)$ on $f: Y \to X$ is given by $(\varepsilon \otimes X)(\mathbb{I} \otimes f): \mathbb{I} \otimes Y \to X$. Furthermore, $\mathbb{I} \otimes (-)$ lifts through the pushout functor $\mathbf{E} \to X/\mathbf{E}$ to a functorial cylinder $\mathbb{I} \otimes_{X/\mathbf{E}} (-)$ on the coslice under $X$. For example, the action of $\mathbb{I} \otimes_{X/\mathbf{E}} (-)$ on $f: X \to Y$ is given by the pushout of $\mathbb{I} \otimes f: \mathbb{I} \otimes X \to \mathbb{I} \otimes Y$ along $\varepsilon \otimes X$. In both cases, adjointness is preserved, and the corresponding functorial path object is given by performing the dual construction.

Definition 3.12 Write @: $[\mathbf{E}, \mathbf{F}] \times \mathbf{E} \to \mathbf{F}$ for the application bifunctor defined by $F @ X := F(X)$. Given a category $\mathbf{E}$ with a functorial cylinder and $f \in \mathbf{E}^\to$, we abbreviate $(\delta_k \otimes (-)) \widehat{\otimes} f \in \mathbf{E}^\to$ as $\delta_k \widehat{\otimes} f$. We likewise write $\varepsilon \widehat{\otimes} f$ for Leibniz application of the contraction. We write $\delta_k \widehat{\oslash} (-)$ and $\varepsilon \widehat{\oslash} (-)$ for the dual operations associated to a functorial path object.

Definition 3.13 Given a finitely cocomplete category $\mathbf{E}$ with a functorial cylinder, a weak factorization system $(\mathcal{L}, \mathcal{R})$ is cylindrical when $\partial \widehat{\otimes} (-)$ preserves left maps.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

17

Definition 3.14 Given $f: A \to B$ in a finitely cocomplete category with a functorial cylinder and $k \in \{0, 1\}$, we write $\mathrm{M}_k(f)$ for its $k$-sided mapping cylinder, defined as the pushout

$$\begin{array}{c} A \xrightarrow {f} B \\ \delta_ {k} \otimes A \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb {I} \otimes A \xrightarrow [ t _ {0} ]{} \mathrm {M} _ {k} (f) \end{array}$$

The $k$-sided mapping cylinder factorization of $f$ is the factorization

$$A \xrightarrow {\iota_ {0} (\delta_ {1 - k} \otimes A)} \mathrm{M} _ {k} (f) \xrightarrow {[ f (\varepsilon \otimes A) , \mathrm{id} ]} B.$$

Definition 3.15 A cylindrical premodel structure on a finitely complete and cocomplete category $\mathbf{E}$ consists of a premodel structure and adjoint functorial cylinder on $\mathbf{E}$ such that

- the (cofibration, trivial fibration) and (trivial cofibration, fibration) weak factorization systems are cylindrical;
- $\delta_{k} \otimes (-)$ sends cofibrations to trivial cofibrations for $k \in \{0, 1\}$.

Remark 3.16 The above conditions are transpose to equivalent dual conditions on the corresponding adjoint functorial path object. Like its constituent components, the notion of cylindrical premodel structure is thus self-dual: a cylindrical premodel structure on $\mathbf{E}$ is the same as a cylindrical premodel structure on $\mathbf{E}^{\mathrm{op}}$.

Remark 3.17 (Stability under (co)slicing) Continuing Remarks 3.2 and 3.11, a cylindrical premodel structure on $\mathbf{E}$ descends to cylindrical premodel structures on slices and coslices of $\mathbf{E}$. We may exploit this to simplify arguments by for example working in a slice.

Fix once more a premodel category $\mathbf{M}$ with factorization systems $(\mathcal{C},\mathcal{F}_t)$ and $(\mathcal{C}_t,\mathcal{F})$. We show that condition $\mathbf{C}$ is reducible to condition $\mathbf{A}$ when $\mathbf{M}$ is cylindrical by relating trivial fibrations with dual strong deformation retracts.

Definition 3.18 In a category with a functorial cylinder, we say $f: Y \to X$ is a dual strong $k$-oriented deformation retract for some $k \in \{0, 1\}$ when we have a map $s: X \to Y$ such that $f s = \mathrm{id}$ and a homotopy $h: \mathbb{I} \otimes Y \to Y$ such that $h(\delta_k \otimes Y) = sf, h(\delta_{1-k} \otimes Y) = \mathrm{id}$, and $f h$ is a constant homotopy. Equivalently (if the category is finitely cocomplete), $f$ is a dual strong $k$-oriented deformation retract when we have a diagonal filler

$$\begin{array}{c} Y \xrightarrow {=} Y \\ \iota_ {0} (\delta_ {1 - k} \otimes Y) \Biggl \downarrow \\ \mathrm{M} _ {k} (f) \xrightarrow [ [ f (\varepsilon \otimes Y) , \mathrm{id} ] ]{} X. \end{array}$$

The following is a standard construction (see, e.g., [Qui67, Lemma I.5.1]).

2025/10/16 00:43

18

E. Cavallo and C. Sattler

Lemma 3.19 Let $$(\mathcal{L}, \mathcal{R})$$ be a cylindrical weak factorization system on a finitely cocomplete category with a functorial cylinder. Then any $$\mathcal{R}$$-map between $$\mathcal{L}$$-objects is a dual strong $$k$$-oriented deformation retract for any $$k \in \{0, 1\}$$.

Proof Let $$f: Y \to X$$ be an $$\mathcal{R}$$-map between $$\mathcal{L}$$-objects. We solve two lifting problems in turn:

![img-5.jpeg](img-5.jpeg)

![img-6.jpeg](img-6.jpeg)

The maps $$s$$ and $$h$$ exhibit $$f$$ as a dual strong 0-oriented deformation retract; we may similarly construct a 1-oriented equivalent.

Corollary 3.20 Let $$(\mathcal{L}, \mathcal{R})$$ be a cylindrical weak factorization system on a category with a functorial cylinder. Then in any diagram of the form

![img-7.jpeg](img-7.jpeg)

the horizontal map is a dual strong $$k$$-oriented deformation retract for any $$k \in \{0, 1\}$$.

Proof By Lemma 3.19, applied in the coslice under $$A$$ via Remark 3.17.

Lemma 3.21 If $$\mathbf{M}$$ is cylindrical, then any fibration $$f: Y \to X$$ that is a dual strong $$k$$-oriented deformation retract for some $$k \in \{0, 1\}$$ is a trivial fibration.

Proof Let $$s: X \to Y$$ and $$h: \mathbb{I} \otimes Y \to Y$$ be as in the definition of dual strong $$k$$-oriented deformation retract. Then the diagram

![img-8.jpeg](img-8.jpeg)

exhibits $$f$$ as a retract of a trivial fibration.

Lemma 3.22 Suppose $$\mathbf{M}$$ is cylindrical. If trivial fibrations have right cancellation among fibrations, then any (trivial cofibration, fibration) factorization of a weak equivalence is a (trivial cofibration, trivial fibration) factorization.

Dually, if trivial cofibrations have left cancellation among cofibrations, then any (cofibration, trivial fibration) factorization of a weak equivalence is a (trivial cofibration, trivial fibration) factorization.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

19

Proof Suppose we have a weak equivalence $X \to Y$ factoring as a trivial cofibration followed by a fibration, thus a diagram of the following form:

![img-9.jpeg](img-9.jpeg)

We first take a pullback and factorize the induced gap map as a trivial cofibration followed by a fibration.

![img-10.jpeg](img-10.jpeg)

By Corollary 3.20, the composites $Z \to U$ and $Z \to V$ are dual strong deformation retracts, thus trivial fibrations by Lemma 3.21. Then the composite $Z \to Y$ is a trivial fibration by composition, so $V \to Y$ is a trivial fibration by right cancellation.

Theorem 3.23 Suppose $\mathbf{M}$ is a cylindrical premodel structure. Then $\mathcal{W}(\mathcal{C}, \mathcal{F})$ satisfies 2-out-of-3 exactly if the following hold:

- (A) trivial cofibrations have left cancellation among cofibrations and trivial fibrations have right cancellation among fibrations;
- (C) any composite of a trivial fibration followed by a trivial cofibration is a weak equivalence.

Proof Theorem 3.8 combined with Lemma 3.22.

Finally, we prove for reference below that the cancellation properties opposite of condition A always hold in a cylindrical premodel structure, though we will not need this fact.

Lemma 3.24 Let $(\mathcal{L}, \mathcal{R})$ be a cylindrical weak factorization system on a category with a functorial cylinder. If $f$ is a map between $\mathcal{L}$-objects, then the first factor of its $k$-sided mapping cylinder factorization is an $\mathcal{L}$-map.

Proof The first factor $A \to M_k(f)$ in the factorization of $f: A \to B$ decomposes as the composite

$$A \xrightarrow{\iota_0} A \sqcup B \xrightarrow{\cong} (A \sqcup A) \sqcup_A B \xrightarrow{(\partial \otimes A) \sqcup_A B} \mathbb{I} \otimes A \sqcup_A B.$$

The first map is a cobase change of $0 \to B$, thus an $\mathcal{L}$-map. The last map is a cobase change of $\partial \otimes A \cong \partial \widehat{\otimes} (0 \to A)$, thus also an $\mathcal{L}$-map.

2025/10/16 00:43

20

E. Cavallo and C. Sattler

Lemma 3.25 If M is cylindrical, then any cofibration between trivially cofibrant objects is a trivial cofibration. Dually, any fibration between trivially fibrant objects is a trivial fibration.

Proof Let m: A ↦ B be a cofibration between trivially cofibrant objects. Consider the commutative square

$$\begin{array}{c} A \xmapsto{\iota_0(\delta_1 \otimes A)} M_0(m) \\ m \downarrow \\ B \xrightarrow{\delta_1 \otimes B} \mathbb{I} \otimes B. \end{array}$$

The top horizontal map is a trivial cofibration by Lemma 3.24, while the right vertical map is a trivial cofibration by cylindricality. The bottom map is split monic, so m is a retract of a trivial cofibration and thus a trivial cofibration itself.

Corollary 3.26 (Sat17, Lemma 4.5(iii)) If M is cylindrical, then trivial cofibrations have right cancellation among cofibrations. Dually, trivial fibrations have left cancellation among fibrations.

Proof Given a diagram

![img-11.jpeg](img-11.jpeg)

we apply Lemma 3.25 to f in the coslice under A via Remark 3.17.

### 3.3 Model structures from the fibration extension property

We now narrow our attention to premodel structures satisfying properties common to cubical-type model structures: first, that all objects are cofibrant, and second, that fibrations extend along trivial cofibrations, the latter of which follows in particular from the existence of enough fibrant universes classifying fibrations. Note that our conditions cease to be self-dual at this point; moreover, the result is a criterion sufficient but not necessary to obtain a model structure.

Lemma 3.27 Let M be a premodel category. Trivial fibrations have right cancellation in M if and only if the (cofibration, trivial fibration) factorization system is generated by cofibrations between cofibrant objects. Dually, trivial cofibrations have left cancellation in M if and only if the (trivial cofibration, fibration) factorization system is cogenerated by fibrations between fibrant objects.

Proof Suppose trivial fibrations have right cancellation in M and let p: Y → X be a map lifting against cofibrations between cofibrant objects. We take a cofibrant replacement of Y, obtaining maps 0 ↦ Y' → Y. By cancellation, it suffices to show the composite p': Y' → X is a trivial fibration. We appeal to the retract argument: p' has the lifting property against the left part of its (cofibration, trivial fibration)

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

21

factorization—this being a cofibration between cofibrant objects—so is a retract of the right part of its factorization. It is thus itself a trivial fibration.

The converse is an elementary exercise in lifting. Suppose the (cofibration, trivial fibration) factorization system is generated by cofibrations between cofibrant objects, let $f: Z \to Y$ and $g: Y \to X$ be such that $gf$ is a trivial fibration. Given a cofibration $m: A \mapsto B$ between cofibrant objects and a lifting problem

![img-12.jpeg](img-12.jpeg)

we solve lifting problems first against $f$ and then against $gf$:

![img-13.jpeg](img-13.jpeg)

![img-14.jpeg](img-14.jpeg)

The composite $fv$ is a lift for the original square.

In particular, Lemma 3.27 tells us that trivial fibrations have right cancellation in any premodel structure where all objects are cofibrant. If the premodel structure is additionally cylindrical, then condition C is also always satisfied:

Lemma 3.28 Let $\mathbf{M}$ be cylindrical and suppose that all objects are cofibrant. Then any composite of a trivial fibration followed by a trivial cofibration is a weak equivalence.

Proof Suppose we have $p: B \to A$ and $m: A \mapsto X$. We take their composite's (trivial cofibration, fibration) factorization:

![img-15.jpeg](img-15.jpeg)

We intend to show $q$ is a trivial fibration. By Corollary 3.20 and the assumption that all objects are cofibrant, $p$ has the structure of a dual strong 0-oriented deformation retract. Thus we have a diagonal lift

![img-16.jpeg](img-16.jpeg)

2025/10/16 00:43

22

E. Cavallo and C. Sattler

Using that $q$ is a fibration, we show that $q$ is a dual strong deformation retract by solving a lifting problem of the form

![img-17.jpeg](img-17.jpeg)

The map $A \sqcup_B \mathrm{M}_1(n) \mapsto \mathrm{M}_0(q)$ is the following composite:

$$\begin{array}{c} A \sqcup_B \mathrm{M}_1(n) \xrightarrow{\quad} X \sqcup_B \mathrm{M}_1(n) \xrightarrow{\quad} X \sqcup_Y (\mathbb{I} \otimes B \sqcup_B (Y \sqcup Y)) \xrightarrow{\quad} \mathrm{M}_0(q) \\ m \sqcup_B \mathrm{M}_1(n) \hspace{4em} X \sqcup_Y (\partial \otimes n) \end{array}$$

The first map is a cobase change of the trivial cofibration $m$, while the final map is a cobase change of the trivial cofibration $\partial \otimes n$; thus the composite is indeed a trivial cofibration. The diagonal lift exhibits $q$ as a dual strong deformation retract, thus a trivial fibration by Lemma 3.21.

Thus, in a cylindrical premodel structure where all objects are cofibrant, the only non-trivial property necessary to apply Theorem 3.23 is left cancellation for trivial cofibrations among cofibrations. This we can further reduce to the following condition.

Definition 3.29 (FEP) We say a premodel category $\mathbf{M}$ has the fibration extension property when for any fibration $f: Y \to X$ and trivial cofibration $m: X \mapsto X'$, there exists a fibration $f': Y' \to X'$ whose base change along $m$ is $f$:

$$\begin{array}{c} Y \longrightarrow Y' \\ f \downarrow \quad \downarrow \quad \downarrow f' \\ X \xrightarrow[m]{} X'. \end{array}$$

Lemma 3.30 Suppose $\mathbf{M}$ is a premodel category with the fibration extension property. Then trivial cofibrations have left cancellation in $\mathbf{M}$.

Proof By Lemma 3.27, it suffices to show the (trivial cofibration, fibration) factorization system is cogenerated by fibrations between fibrant objects. Suppose $g: A \to B$ is a map with the left lifting property against all fibrations between fibrant objects. Let $f: Y \to X$ be an arbitrary fibration. Its codomain $X$ has a fibrant replacement $m: X \mapsto X^{\mathrm{fib}}$; by the fibration extension property there is some $f': Y' \to X^{\mathrm{fib}}$ whose pullback along $m$ is $f$. By assumption $g$ lifts against $f'$, and this lift induces a lift for

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

23

$g$ against $f$ via the usual argument that right maps of a weak factorization system are closed under base change.

**Theorem 3.31** Let $\mathbf{M}$ be a cylindrical premodel category in which

- (D) all objects are cofibrant;
- (E) the fibration extension property is satisfied.

Then the premodel structure on $\mathbf{M}$ defines a model structure.

**Proof** By Theorem 3.23. Condition C is satisfied by Lemma 3.28. Trivial cofibrations have left cancellation by Lemma 3.30, while trivial fibrations have right cancellation by Lemma 3.27.

The fibration extension property can in particular be obtained from the existence of fibrant classifiers for fibrations, i.e., fibrant universes of fibrations. We do not generally expect to have a single classifier for all fibrations, only those below a certain size. Thus we now consider a setup where a premodel category sits inside a larger category containing classifiers for its fibrations.

**Lemma 3.32** Let $\mathbf{E}$ be a category, and let $\mathbf{M}$ be a subcategory of $\mathbf{E}$ equipped with a premodel structure. Say that a map in $\mathbf{E}$ is a fibration if it has the right lifting property against all trivial cofibrations in $\mathbf{M}$. Suppose we have a class $\mathcal{U} \subseteq \mathbf{E}^{\rightarrow}$ of fibrations between fibrant objects that classifies fibrations in $\mathbf{M}$, in following sense:

- (a) every fibration in $\mathbf{M}$ is a pullback of some fibration in $\mathcal{U}$;
- (b) if $p: E \to U$ is a map in $\mathcal{U}$ and $y: X \to U$ is a map with $X \in \mathbf{M}$, then there exists a map in $\mathbf{M}$ which is the pullback of $p$ along $y$:

$$\begin{array}{c} \bullet \longrightarrow E \\ \mathbf{M} \ni \downarrow \quad \downarrow p \\ X \xrightarrow{y} U. \end{array}$$

Then $\mathbf{M}$ has the fibration extension property.

**Proof** Let a fibration $f: Y \to X$ in $\mathbf{M}$ and trivial cofibration $m: X \mapsto X'$ in $\mathbf{M}$ be given. Then $f$ is the pullback of some fibration between fibrant objects $p: E \to U$ in $\mathbf{E}$ along some map $y: X \to U$. As $U$ is fibrant, $y$ extends along $m$ to some $y': X' \to U$. By assumption, we can choose a pullback $f': Y' \to X'$ of $p$ along $y'$ belonging to $\mathbf{M}$. By the pasting law for pullbacks, $f$ is the pullback of $f'$ along $m$.

**Corollary 3.33** Let $\mathbf{E}$ be a category, and let $\mathbf{M}$ be a subcategory of $\mathbf{E}$ equipped with a premodel structure. Suppose that $\mathbf{M}$ is cylindrical and the following conditions are satisfied:

- (D) all objects of $\mathbf{M}$ are cofibrant;
- (F) there is a class of fibrations between fibrant objects in $\mathbf{E}$ that classifies fibrations in $\mathbf{M}$ in the sense of Lemma 3.32.

2025/10/16 00:43

24

E. Cavallo and C. Sattler

Then the premodel structure on M defines a model structure.

Proof By Theorem 3.31 and Lemma 3.32.

Remark 3.34 In applications, one usually starts with a set (or category, when working with algebraic weak factorization systems) of generating trivial cofibrations that defines the class of fibrations via lifting. We can then consider an “extension” E of M large enough to build a classifier for fibrations in M (for example, by passing from presheaves to “large” presheaves as in Section 4.2). Fibrancy of the classifier is shown by extending fibrations along generating trivial cofibrations.

In such settings, there is also an alternative approach that directly moves from fibration extension along generating trivial cofibrations to general fibration extension. For a set of generating trivial cofibrations with representable codomain, this is described in [Sat17, §7]. It involves exhibiting trivial cofibrations as codomain retracts of cell complexes of the generators using the small object argument; fibration extension along such a cell complex is then obtained inductively. In the model structure we construct in Section 4.2, we instead have a category of generating trivial cofibrations with representable codomain (Definition 4.16). However, the same technique still applies, using an analysis of the algebraic small object argument [Sat23].

## 4 Semilattice cubical sets

### 4.1 The semilattice cube category

We now introduce this article’s main character: the (join-)semilattice cube category $\square_{\vee}$ generated by an interval object, finite cartesian products, and a binary connection operator. Like other cartesian cube categories, it is a (single-sorted) Lawvere theory [Law63]: a finite product category in which every object is a finite power of some distinguished object.

Definition 4.1 The theory of (join-)semilattices consists of an associative and commutative binary operator $\vee$ for which all elements are idempotent, which we call the join. This means the following laws:

$$(x \vee y) \vee z = x \vee (y \vee z), \quad x \vee y = y \vee x, \quad x \vee x = x.$$

The theory of 01-bounded (join-)semilattices consists, in addition to the above, of two constants 0, 1 and the following laws:

$$0 \vee x = x, \quad 1 \vee x = 1.$$

The (join-)semilattice cube category $\square_{\vee}$ is the Lawvere theory of 01-bounded semilattices. Concretely, the objects of $\square_{\vee}$ are of the form $T^n$ for $n \in \mathbb{N}$, and the morphisms $T^m \to T^n$ are $n$-ary tuples of expressions over 0, 1, $\vee$ in $m$ variables modulo the equations above. We write $\mathbf{T}_{\vee}$ for the Lawvere theory of semilattices.

Remark 4.2 As a bicategory, $\mathbf{T}_{\vee}$ can be identified with the subcategory of the bicategory of onto (decidable) relations between finite sets. Equivalently, these are jointly injective

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

25

spans in finite sets whose second leg is surjective. This can be strictified to a 1-category by replacing relations with Boolean-valued matrices.

Recall that the category of algebras $\operatorname{Alg}(\mathbf{T}) := [\mathbf{T}, \mathbf{Set}]_{\mathrm{fp}}$ of a Lawvere theory $\mathbf{T}$ is the category of finite-product-preserving functors from $\mathbf{T}$ to $\mathbf{Set}$, which supports an "underlying set" functor $U: [\mathbf{T}, \mathbf{Set}]_{\mathrm{fp}} \to \mathbf{Set}$ given by evaluation at the distinguished object $T^1$. This functor has a left adjoint $F: \mathbf{Set} \to \operatorname{Alg}(\mathbf{T})$ which produces the free $\mathbf{T}$-algebra on a set, and the covariant Yoneda embedding restricts to an embedding $\mathbf{T}^{\mathrm{op}} \to \operatorname{Alg}(\mathbf{T})$ sending $T^n$ to the free algebra on $n$ elements. We write $\mathbf{SLat}$ and $\mathbf{01SLat}$ for the categories of algebras of $\mathbf{T}_{\vee}$ and $\square_{\vee}$ respectively. Concretely, these are the categories of sets equipped with the operations described in Definition 4.1 and operation-preserving morphisms between them.

It can also be useful to take an order-theoretic perspective on $\mathbf{SLat}$ and $\mathbf{01SLat}$, identifying them as subcategories of the category $\mathbf{Pos}$ of posets and monotone maps. Recall that the operator $\vee$ induces a poset structure on any semilattice, with $x \leq y$ when $x \vee y = y$.

Proposition 4.3 $\mathbf{SLat}$ is equivalent to the subcategory of $\mathbf{Pos}$ consisting of posets with finite non-empty joins (that is, least upper bounds) and monotone maps that preserve said joins. $\mathbf{01SLat}$ is equivalent to the further (non-full) subcategory of posets that also have a minimum and maximum element and monotone maps that also preserve them.

Remark 4.4 Any finite linear order is a semilattice, and it is 01-bounded if it is inhabited. Moreover, any monotone map between linear orders preserves joins. Thus the inclusion $\Delta \to \mathbf{Pos}$ factors through a fully faithful inclusion $\Delta \to \mathbf{SLat}$.

In particular, the interval $[1] \in \mathbf{Pos}$ is a 01-bounded semilattice.

Proposition 4.5 The interval is a dualizing object for a duality between the categories of finite semilattices and finite 01-bounded semilattices, which is to say that we have the following categorical equivalence:

$$\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{op}} \xleftarrow[\mathrm{01SLat}(-, [1])]{\mathrm{SLat}(-, [1])} \mathbf{01SLat}_{\mathrm{fin}}.$$

Proof By a slight variation on the argument that $\mathbf{0SLat}_{\mathrm{fin}}^{\mathrm{op}} \simeq \mathbf{0SLat}_{\mathrm{fin}}$ indicated in [Joh82, §VI3.6, §VI.4.6(b)].

Given a semilattice $A$, the 01-bounded semilattice structure on $\mathbf{SLat}(A, [1])$ is defined pointwise from that on $[1]$; likewise $\mathbf{01SLat}(B, [1])$ has a pointwise semilattice structure for any $B \in \mathbf{01SLat}$. This extends the duality between the augmented simplex category and the category of finite intervals (i.e., finite bounded linear orders and bound-preserving monotone maps) observed by Joyal [Joy97, §1.1; Wra93].

2025/10/16 00:43

26

E. Cavallo and C. Sattler

By way of this duality, we have in particular an embedding of $\square_{\vee}$ in the category of finite semilattices, induced by the embedding of its opposite in its category of models:

$$\square_{\vee} \xrightarrow{k} \mathbf{01SLat}_{\text{fin}}^{\text{op}} \xrightarrow{\simeq} \mathbf{SLat}_{\text{fin}}.$$

Here we use that the free semilattice on a finite set of generators is a finite semilattice. Unpacking, this embedding sends $T^n$ to $\mathbf{01SLat}(F(n), [1]) \cong \mathbf{Set}(n, U[1]) \cong [1]^n$.

Notation 4.6 Henceforth we regard $\square_{\vee}$ as a subcategory of SLat, in particular writing $[1]^n$ rather than $T^n$ for its objects.

We can also describe the cubes in SLat as free semilattices on posets. Given a poset $A$, write $1 \star A$ for the poset obtained by adjoining a minimum element $\bot$ to $A$. For any set $S$, we have a monotone map $\eta_n: 1 \star S \to [1]^S$ sending $\bot$ to $\bot$ and $i \in S$ to the element of $[1]^S$ with 1 at its $i$th component and 0 elsewhere.

Proposition 4.7 For any $S \in \mathbf{Set}_{\text{fin}}$, the map $\eta_S$ exhibits $[1]^S$ as the free semilattice on the poset $1 \star S$. That is, for any $A \in \mathbf{SLat}$ and monotone map $f: 1 \star S \to A$, there is a unique semilattice morphism $f^1: [1]^S \to A$ such that $f = f^1 \eta_S$.

### 4.2 Cubical-type model structure on semilattice cubical sets

We now define our model structure on $\mathrm{PSh}(\square_{\vee})$ using Corollary 3.33. That our case satisfies the corollary's hypotheses is essentially an application of existing work, namely [CMS19] or [Awo23], so we do not give many proofs, only enough of an outline to guide an unfamiliar reader through the appropriate references. We point to [GS17; Sat17; AGH24, §8] for further details on constructing model structures of this kind and to [LOPS18] for the definition of the universe in particular.

Assumption 4.8 For simplicity, we work with a single universe: we assume a strongly inaccessible cardinal $\kappa$ and define a model structure on the category $\mathrm{PSh}_{\kappa}(\square_{\vee})$ of $\kappa$-small presheaves. Outside of this section, we suppress the subscript $\kappa$. As described in Remark 3.34, it is possible to eliminate the use of universes at the cost of some complication; alternatively, one can assume that every fibration belongs to some universe to obtain a model structure on all of $\mathrm{PSh}(\square_{\vee})$.

Notation 4.9 We write $\mathbb{I} := k[1] \in \mathrm{PSh}(\square_{\vee})$ for the representable 1-cube. We write $\delta_k: 1 \to [1]$ for the endpoint inclusion picking out $k \in \{0, 1\}$ and write $\varepsilon$ for the unique degeneracy map $[1] \to 1$.

#### 4.2.1 Factorization systems

As analyzed by Gambino and Sattler [GS17], a key feature of cubical-type model structures is that their fibrations are characterized by a uniform lifting property. This characterization is used to obtain the model structure's factorization systems constructively and to define fibrant universes of fibrations. We avoid formally introducing algebraic

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

27

weak factorization systems [GT06; Gar09] for the sake of concision, but these form the conceptual backbone of Gambino and Sattler's results.

Definition 4.10 (Uniform lifting) Let $u: \mathbf{I} \to \mathbf{E}^{\rightarrow}$ be a functor. A right $u$-map is a map $f: Y \to X$ in $\mathbf{E}$ equipped with

- for each $i \in \mathbf{I}$ and filling problem

$$\begin{array}{c} A_{i} \xrightarrow{h} Y \\ u_{i} \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B_{i} \xrightarrow{k} X, \end{array}$$

a diagonal filler $\varphi(i, h, k): B_{i} \to Y$;

- such that for each $\alpha: j \to i$ and diagram

$$\begin{array}{c} A_{j} \xrightarrow{a} A_{i} \xrightarrow{h} Y \\ u_{j} \Big\downarrow \qquad u_{\alpha} \qquad \Big\downarrow u_{i} \qquad \Big\downarrow f \\ B_{j} \xrightarrow{b} B_{i} \xrightarrow{k} X, \end{array}$$

we have $\varphi(i, h, k)b = \varphi(j, ha, kb)$.

When $u$ is a subcategory inclusion, we may instead say that $f$ is a right $\mathbf{I}$-map.

Notation 4.11 Given a category $\mathbf{E}$, write $\mathbf{E}_{\text{cart}}^{\rightarrow} \subseteq \mathbf{E}^{\rightarrow}$ for the category of arrows in $\mathbf{E}$ and cartesian squares between them.

Write $\mathcal{M}$ for the full subcategory of $\mathrm{PSh}_{\kappa}(\square_{\vee})_{\text{cart}}^{\rightarrow}$ consisting of monomorphisms.

Definition 4.12 We say a map in $\mathrm{PSh}_{\kappa}(\square_{\vee})_{\text{cart}}^{\rightarrow}$ is a uniform trivial fibration when it is a right $\mathcal{M}$-map.

Remark 4.13 If working constructively, one must replace $\mathcal{M}$ with the full subcategory $\mathcal{M}_{\text{dec}}$ of levelwise decidable monomorphisms, i.e., those $m: A \mapsto B$ such that $m_I$ is isomorphic to a coproduct inclusion for all $I \in \square_{\vee}$. This restriction is used (see e.g., Orton and Pitts [OP18, Theorem 8.4]) in the proof of the realignment property, which is important to the construction of fibrant universes.

The following proposition lets us characterize the trivial fibrations (and later, the fibrations) as the maps with uniform right lifting against a small category.

Proposition 4.14 (GS17, Proposition 5.16) Let $\mathbf{C}$ be a small category and $\mathbf{I}$ be a full subcategory of $\mathrm{PSh}(\mathbf{C})_{\text{cart}}^{\rightarrow}$ closed under base change to representables, i.e., such that $x^* f \in \mathbf{I}$ for any $f: Y \to X$ in $\mathbf{I}$ and $x: \not\perp a \to X$. Write $\mathbf{I}^{\not\perp}$ for the full subcategory of $\mathbf{I}$ consisting of maps with representable codomain. Then a map in $\mathrm{PSh}(\mathbf{C})$ is a right $\mathbf{I}$-map if and only if it is a right $\mathbf{I}^{\not\perp}$-map.

2025/10/16 00:43

28

E. Cavallo and C. Sattler

Proposition 4.15 (Uniform trivial fibrations) We have a weak factorization system $(\mathcal{M}, \mathcal{F}_t)$ where $\mathcal{F}_t$ is the class of uniform trivial fibrations.

Proof By [GS17, Theorem 9.1], which goes through Garner's algebraic small object argument [Gar09], we have a factorization system $(\mathcal{C}, \mathcal{F}_t)$ where $\mathcal{F}_t$ is the class of uniform trivial fibrations. Here we need that the right $\mathcal{M}$-maps coincide with the right $\mathcal{M}^{\mathcal{K}}$-maps and that $\mathcal{M}^{\mathcal{K}}$ is a small category. That the algebraic small object argument is constructive in this case is explained in [GS17, Remark 9.4]; see also [Hen20, Appendix C].

An alternative construction of the factorization using partial map classifiers is described in [GS17, Remark 9.5] and used by Awodey et al. [AGH24; Awo23], while Swan [Swa18, §6] describes a construction using W-types with reductions. The partial map classifier factorization factors any map as a mono followed by a trivial fibration. By the retract argument, any map in $\mathcal{C}$ is then a retract of a mono and hence itself monic, so $\mathcal{C} = \mathcal{M}$.

Definition 4.16 Define $u_{\delta}: \{0, 1\} \times \mathcal{M}^{\mathcal{K}} \to \mathrm{PSh}_{\kappa}(\square_{\gamma})^{\to}$ by $u_{\delta}(k, -) := \delta_k \widehat{\times} (-)$. A uniform fibration is a right $u_{\delta}$-map.

Proposition 4.17 (Uniform fibrations) There exists a weak factorization system $(\mathcal{C}_t, \mathcal{F})$ such that $\mathcal{F}$ is the class of uniform fibrations.

Proof By [GS17, Theorem 7.5], using the algebraic small object argument. Again, see [GS17, Remark 9.4] for discussion of constructivity.

Though the algebraic/uniform description is important to constructively establish the existence of these weak factorization systems, we can also—still constructively—recognize that $\mathcal{F}_t$ and $\mathcal{F}$ are classes of maps with lifting properties in the non-algebraic sense.

Proposition 4.18 Let $f: Y \to X$ in $\mathrm{PSh}_{\kappa}(\square_{\gamma})$. Then

- $f$ is a right $\mathcal{M}$-map if and only if it has the right lifting property against all monomorphisms;
- $f$ is a right $u_{\delta}$-map if and only if it has the right lifting property with respect to $\delta_k \widehat{\times} m$ for all $k \in \{0, 1\}$ and monomorphisms $m$.

Proof By [GS17, Theorem 9.9].

With the two factorization systems in hand, it is straightforward to verify the following.

Proposition 4.19 $(\mathcal{C}_t, \mathcal{F})$ and $(\mathcal{M}, \mathcal{F}_t)$, together with the adjoint functorial cylinder $\mathbb{I} \times (-) \dashv (-)^{\mathbb{I}}$, constitute a cylindrical premodel structure.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

29

### 4.2.2 Unbiased fibrations

In order to apply Corollary 3.33, we must check that we have a fibration between fibrant objects in $\mathrm{PSh}(\square_{\nu})$ classifying fibrations in $\mathrm{PSh}_{\varepsilon}(\square_{\nu})$. This follows from work on cubical models of type theory, specifically the interpretation of universes. Our cube category falls within the ambit of [ABCHFL21], which describes a universe $p_{\mathrm{fib}}: \widehat{U}_{\mathrm{fib}} \to U_{\mathrm{fib}}$ with fibration structures on $p_{\mathrm{fib}}$ and $U_{\mathrm{fib}}$ in type-theoretic terms; Awodey gives a construction of the same in categorical language [Awo23, §§6–8].

However, the fibrations used in these models are not a priori the fibrations we defined in the previous section: they are what Awodey [Awo23] calls unbiased fibrations, which lift not only against (pushout products with) endpoint inclusions $\delta_k: 1 \to \mathbb{I}$ but against generalized points on the interval. To see that $\overline{\square}_{\nu}^{\mathrm{N}}$ is compatible with this model of type theory, we check here that biased (i.e., ordinary) and unbiased fibrations coincide in the presence of a connection.

Definition 4.20 Given $r: B \to \mathbb{I}$ and $f: A \to B$, their unbiased mapping cylinder is the following pushout:

$$\begin{array}{c} A \xrightarrow{f} B \\ \langle r f, \mathrm{id}_A \rangle \Biggl\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{I} \times A \xrightarrow[d_r]{} \mathrm{M}_r(f). \end{array}$$

Note that $\mathrm{M}_{\delta_k!_B}(f)$ is the ordinary $k$-sided mapping cylinder (Definition 3.14). We write $r \widehat{\times}_B m: \mathrm{M}_r(m) \to \mathbb{I} \times B$ for the unique map fitting in the diagram

$$\begin{array}{c} A \xrightarrow{f} B \\ \langle r f, \mathrm{id}_A \rangle \Biggl\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{I} \times A \xrightarrow[d_r]{} \mathrm{M}_r(f) \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{I} \times m \end{array}$$

This is the pushout product in the slice over $B$ of $\langle r, \mathrm{id}_B \rangle: \mathrm{id}_B \to \varepsilon \times B$ and $m: m \to \mathrm{id}_B$, hence the notation. Note that $(\delta_k!_B) \widehat{\times}_B f$ is the ordinary pushout product $\delta_k \widehat{\times} f$.

Definition 4.21 We say $f: Y \to X$ is an unbiased fibration when it has the right lifting property against $r \widehat{\times}_B m$ for all $r: B \to \mathbb{I}$ and $m: A \mapsto B$.

Lemma 4.22 $r \widehat{\times}_B m$ is a trivial cofibration for any $r: B \to \mathbb{I}$ and $m: A \mapsto B$.

2025/10/16 00:43

30

E. Cavallo and C. Sattler

Proof Define $u(i, a) := (i \lor r(m(a)), a) : \mathbb{I} \times A \to \mathbb{I} \times A$. Take a pushout of $\delta_0 \widehat{\times} m$:

$$\begin{array}{c} \mathrm{M}_{0}(m) \xrightarrow{u \sqcup \mathrm{id}} \mathrm{M}_{r}(m) \\ \delta_{0} \widehat{\times} m \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \times B \xrightarrow{b} C. \end{array}$$

Define a map $v : \mathrm{M}_{1}(r \widehat{\times}_{B} m) \to C$ like so:

$$\begin{array}{c} \mathrm{M}_{r}(m) \xrightarrow{r \widehat{\times}_{B} m} \mathbb{I} \times B \xrightarrow{\varepsilon \times B} B \\ \delta_{1} \times \mathrm{M}_{r}(m) \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \times B \\ \mathbb{I} \times \mathrm{M}_{r}(m) \xrightarrow{d_{1}} \mathrm{M}_{1}(r \widehat{\times}_{B} m) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \times B \\ u \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \\ \mathrm{M}_{r(\varepsilon \times B)}(\mathbb{I} \times m) \xrightarrow{[nd_{r}(\vee \times A), b]} C. \end{array}$$

Take the pushout of $\delta_{1} \widehat{\times} (r \widehat{\times}_{B} m)$ by this map:

$$\begin{array}{c} \mathrm{M}_{1}(r \widehat{\times}_{B} m) \xrightarrow{\nu} C \\ \delta_{1} \widehat{\times} (r \widehat{\times}_{B} m) \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \\ \mathbb{I} \times \mathbb{I} \times B \xrightarrow{b'} D. \end{array}$$

Then we can exhibit $r \widehat{\times}_{B} m$ as a retract of $n' n$:

$$\begin{array}{c} \mathrm{M}_{r}(m) \xrightarrow{\mathrm{id}} \mathrm{M}_{r}(m) \xrightarrow{\mathrm{id}} \mathrm{M}_{r}(m) \\ r \widehat{\times}_{B} m \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{I} \\ \mathbb{I} \times B \xrightarrow{\delta_{0} \times \mathbb{I} \times B} \mathbb{I} \times \mathbb{I} \times B \xrightarrow{b'} D \xrightarrow{[\varepsilon \times \mathbb{I} \times B, [\mathrm{id}, r \widehat{\times}_{B} m]]} \mathbb{I} \times B. \end{array}$$

As a retract of a trivial cofibration, $r \widehat{\times}_{B} m$ is thus a trivial cofibration.

Corollary 4.23 A map is a fibration in $\overline{\Omega}_{\vee}^{\mathrm{ty}}$ if and only if it is an unbiased fibration.

Proof If $f : Y \to X$ is an unbiased fibration, then lifting against any $\delta_{k} \widehat{\times} m$ is obtained as lifting against $(\delta_{k}!_{B}) \widehat{\times}_{B} m$. The converse is Lemma 4.22.

Remark 4.24 For the reader more comfortable with cubical type theories, we give the type-theoretic analogue to the proof of Corollary 4.23. The ABCHFL type theory equips

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

31

types with a composition operator of the following form.

$$\frac {i : \mathbb { I } \vdash A \text { type } \quad \varphi \text { cof } \quad r , s : \mathbb { I } } { i : \mathbb { I } , \varphi \vdash M : A \quad M _ { 0 } : A [ r / i ] \quad \varphi \vdash M [ r / i ] = M _ { 0 } : A [ r / i ] }$$ $$\operatorname { c o m } _ { i , A } ^ { r \rightarrow s } [ \varphi \mapsto i . M ] \ M _ { 0 } : A [ s / i ]$$

$$\operatorname { c o m } _ { i , A } ^ { r \rightarrow r } [ \varphi \mapsto i . M ] \ M _ { 0 } = M _ { 0 } : A [ r / i ]$$

$$\varphi \vdash \operatorname { c o m } _ { i , A } ^ { r \rightarrow s } [ \varphi \mapsto i . M ] \ M _ { 0 } = M [ s / i ] : A [ s / i ]$$

In the presence of a connection, we can derive a term satisfying the equations required of $\operatorname { c o m } _ { i , A } ^ { r \rightarrow s } [ \varphi \mapsto i . M ] \ M _ { 0 }$ using only composition $\varepsilon \rightarrow s$ where $\varepsilon \in \{ 0 , 1 \}$, namely the term $Q$ below.

$$\begin{array} { l } { P ( k ) : = \operatorname { c o m } _ { j . A [ r \vee j / i ] } ^ { 0 \rightarrow k } \left[ \varphi \mapsto j . M [ r \vee j / i ] \right] M _ { 0 } } \\ { Q : = \operatorname { c o m } _ { j . A [ s \vee j / i ] } ^ { 1 \rightarrow 0 } \left[ \begin{array} { c } { \varphi \mapsto j . M [ s \vee j / i ] } \\ { r \equiv s \mapsto j . P ( j ) } \end{array} \right] P ( 1 ) } \end{array}$$

Remark 4.25 We can also use $\vee$ to show that any fibration is an equivariant fibration in the sense of the ACCRS model structure [ACCRS24]. For simplicity, let us restrict attention to lifting along $\delta _ { 1 } ^ { n } \colon 1 \rightarrow \mathbb { I } ^ { n }$, which is the simplest case; we leave it as an exercise to formulate and derive unbiased equivariant lifting by combining the proof of Lemma 4.22 with the following sketch. A more complete proof (for simplicial sets rather than semilattice cubical sets, but with the same argument) is in [ACCRS24, Proposition 6.1.7].

Write $\Sigma : = \operatorname { C o r e } ( \square _ { \vee } )$ for the wide subcategory of isomorphisms of $\square _ { \vee }$. We have a functor $\delta \colon \Sigma \rightarrow \operatorname { P S h } ( \square _ { \vee } ) ^ { \rightarrow }$ sending $[ 1 ] ^ { n }$ to $\delta _ { 1 } ^ { n } \colon 1 \rightarrow \mathbb { I } ^ { n }$ and $\sigma \colon [ 1 ] ^ { n } \cong [ 1 ] ^ { n }$ to $(\mathrm { i d } , \sigma ) \colon \delta _ { 1 } ^ { n } \rightarrow \delta _ { 1 } ^ { n }$. Take $u _ { \delta \Sigma }$ to be the composite

$$\Sigma \times \mathcal { M } ^ { \varkappa } \xrightarrow { \delta \times \mathcal { M } ^ { \varkappa } } \operatorname { P S h } ( \square _ { \vee } ) ^ { \rightarrow } \times \mathcal { M } ^ { \varkappa } \xrightarrow { \overline { { { \varkappa } } } } \operatorname { P S h } ( \square _ { \vee } ) ^ { \rightarrow } .$$

A uniform equivariant 1-fibration is a right $u _ { \delta \Sigma }$-map.

Suppose $f \colon Y \rightarrow X$ is a uniform fibration and let $m \colon A \mapsto B$ and a lifting problem $( y , x ) \colon \delta _ { 1 } ^ { n } \widehat { \times } \ m \rightarrow f$ be given. We have a map $\uparrow _ { n } \colon [ 1 ] \times [ 1 ] ^ { n } \rightarrow [ 1 ] ^ { n }$ sending $( t , i _ { 1 } , \ldots , i _ { n } ) \mapsto ( t \vee i _ { 1 } , \ldots , t \vee i _ { n } )$ which we use to form a lifting problem against $\delta _ { 1 } \widehat { \times } ( \mathbb { I } ^ { n } \times m )$:[{"box_2d": [244, 670, 751, 752], "label": "equation", "caption": "$$\\begin{array} { c } { { ( \\mathbb { I } \\times \\mathbb { I } ^ { n } \\times A ) \\sqcup _ { \\mathbb { I } \\times A } ( \\mathbb { I } \\times B ) \\xrightarrow { ( \\uparrow ^ { n } \\times A ) \\sqcup ( \\varepsilon \\times B ) } ( \\mathbb { I } ^ { n } \\times A ) \\sqcup _ { A } B \\xrightarrow { y } Y } } \\\\ { { \\delta _ { 1 } \\widehat { \\times } ( \\mathbb { I } ^ { n } \\times m ) \\Biggl \\downarrow \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\q i } } \\\\ { { \\mathbb { I } \\times \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\q i } } \\\\ { { \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\q i } } \\\\ { { \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\q i } } \\\\ { { \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\qquad \\q i } } \\\\ { { \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times B \\xrightarrow { \\qquad \\qquad \\q i } \\mathbb { I } ^ { n } \\times

32

E. Cavallo and C. Sattler

### 4.2.3 Universe

To define a universe classifying fibrations, we use a theorem of Licata, Orton, Pitts, and Spitters [LOPS18]. The cardinal $\kappa$ provides a Grothendieck universe in Set, from which Hofmann and Streicher's construction produces a universe $p_U \colon \widetilde{U} \to U$ in $\mathrm{PSh}(\square_\nu)$ classifying $\kappa$-small maps [HS97; Str05; Awo24]. Our classifier for $\kappa$-small fibrations shall be a subuniverse of $p_U$. The key property of $\mathrm{PSh}(\square_\nu)$ is that the cocylinder $(-)^\mathbb{I}$ has a right adjoint, i.e., that $\mathbb{I}$ is internally tiny: we have $(-)^\mathbb{I} \cong ((-) \times [1])^*$ and therefore $(-)^\mathbb{I} \dashv \sqrt{-} := ((-) \times [1])_+$. This property is common to cube categories but fails for example in simplicial sets. We refer to Swan [Swa22] for a deeper analysis.

Given a $\kappa$-small map $f \colon Y \to X$ with characteristic map $A \colon X \to U$, we define a family $X^\mathbb{I} \to U$ whose sections correspond to fibration structures on $A$. To do so, it is convenient to work in the internal extensional type theory of the universe $p_U$ in the style of Orton and Pitts [OP18].$^5$ Writing $\top \colon 1 \to \Omega$ for the subobject classifier in $\mathrm{PSh}(\square_\nu)$, the maps $!_\Omega \colon \Omega \to 1$ and $\top$ are both classified by $p_U$,$^6$ so appear as a closed type $\cdot \vdash \Omega : U$ and type family $\varphi \colon \Omega \vdash [\varphi] : U$ respectively. The interval likewise appears as a closed type $\cdot \vdash \mathbb{I} : U$ with inhabitants $\cdot \vdash 0, 1 : \mathbb{I}$.

Definition 4.26 Given a type $A \colon U$, define its type of trivial fibration structures $\mathrm{TFib}\, A \colon U$ as follows:

$$\mathrm{TFib}\, A := \Pi \varphi \colon \Omega. \, \Pi \nu \colon [\varphi] \to A. \, \Sigma a \colon A. \, \Pi a \colon [\varphi]. \, \nu(a) = a.$$

Definition 4.27 Given $k \in \{0, 1\}$ and $A \colon X \to U$, define the pullback exponential $(\delta_k \xrightarrow{\sim} A) : (\Sigma p \colon X^\mathbb{I}. A(p(k))) \to U$ internally as follows:

$$(\delta_k \xrightarrow{\sim} A)(p, a) := \Sigma q \colon (\Pi i \colon \mathbb{I}. A(p(i))). \, q(k) = a.$$

Definition 4.28 Given $A \colon X \to U$, define $\mathrm{Fib}_k\, A \colon X^\mathbb{I} \to U$ for $k \in \{0, 1\}$ and then $\mathrm{Fib}\, A \colon X^\mathbb{I} \to U$ as follows:

$$(\mathrm{Fib}_k\, A)(p) := \Pi a \colon A(p(k)). \, \mathrm{TFib}((\delta_k \xrightarrow{\sim} A)(p, a))$$

$$(\mathrm{Fib}\, A)(p) := (\mathrm{Fib}_0\, A)(p) \times (\mathrm{Fib}_1\, A)(p).$$

Proposition 4.29 Let $f \colon Y \to X$ be given with classifying map $A \colon X \to U$. Then $f$ is a uniform fibration if and only if the type $\Pi p \colon X^\mathbb{I}$. $(\mathrm{Fib}\, A)(p)$ is inhabited.

Proof See [AGH24, Corollary 8.7].

Using the right adjoint to $(-)^\mathbb{I}$, we carve out the subuniverse of $p_U$ corresponding to families $A \colon X \to U$ for which $\Pi p \colon X^\mathbb{I}$. $(\mathrm{Fib}\, A)(p)$ is inhabited. For this step we return to working externally, as $\sqrt{-}$ does not straightforwardly internalize; Licata et al. [LOPS18] use a global sections modality to axiomatize $\sqrt{-}$ internally, while Riley [Ril24]

$^5$We refer to [AGH24] for a detailed translation between external and internal constructions in presheaf categories and to [Awo23, §6] for a fully externalized argument.

$^6$If working predicatively, one should replace $\Omega$ with the classifier for levelwise decidable subobjects.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

33

has recently proposed a type theory which directly represents $\sqrt{-}$ as a modality. The following definition and proposition constitute Theorem 5.2 of [LOPS18].

Definition 4.30 Define $p_{\mathrm{fib}}: \widetilde{U}_{\mathrm{fib}} \to U_{\mathrm{fib}}$ by pullback as follows:

$$\begin{array}{c} \widetilde{U}_{\mathrm{fib}} \xrightarrow{\pi_1} \widetilde{U} \\ p_{\mathrm{fib}} \downarrow \quad \downarrow p_U \\ U_{\mathrm{fib}} \xrightarrow{\pi_1} U \\ \pi_0 \downarrow \quad \downarrow (\mathrm{Fib\,id}_U)^\dagger \\ \sqrt[3]{\widetilde{U}} \xrightarrow[\sqrt[3]{p_U}]{\mathcal{J} \cdot \mathcal{U}}. \end{array}$$

Proposition 4.31 (LOPS18, Theorem 5.2) If $f: Y \to X$ is the pullback of $p_U$ along some $A: X \to U$, then $f$ is a uniform fibration if and only if $A$ factors through $\pi_1: U_{\mathrm{fib}} \to U$.

Corollary 4.32 The map $p_{\mathrm{fib}}$ is a uniform fibration.

Proof $p_{\mathrm{fib}}$ is the pullback of $p_U$ along $\pi_1$, which of course factors through itself.

Finally, we need a fibrancy structure on the universe $U$ itself. This is the most technically involved argument; we defer to prior work.

Proposition 4.33 The object $U_{\mathrm{fib}}$ is uniform fibrant.

Proof A fibrancy structure on $U_{\mathrm{fib}}$ is described in type-theoretic language in [ABCHFL21, §2.12], while Awodey [Awo23, §8] gives an external categorical construction.

Theorem 4.34 (Cubical-type model structure on semilattice cubical sets) There is a model structure on $\mathrm{PSh}_\kappa(\square_\nu)$ in which

- the cofibrations are the monomorphisms;
- the fibrations are those maps with the right lifting property against all pushout products $\delta_k \times m$ of an endpoint inclusion with a monomorphism.

We write $\widehat{\square}_\nu^{\mathrm{ty}}$ for this model category.

Proof By Corollary 3.33 applied with $\mathrm{PSh}_\kappa(\square_\nu)$ inside $\mathrm{PSh}(\square_\nu)$ and the factorization systems $(\mathcal{M}, \mathcal{F}_t)$ and $(C_t, \mathcal{F})$ defined in this section. Clearly all objects are cofibrant, and every fibration in $\mathrm{PSh}_\kappa(\square_\nu)$ is classified by $p_{\mathrm{fib}}: \widetilde{U}_{\mathrm{fib}} \to U_{\mathrm{fib}}$, which is a fibration (Corollary 4.32) between fibrant objects (Proposition 4.33).

Our question now is whether $\widehat{\square}_\nu^{\mathrm{ty}}$ presents $\infty$-Gpd. More narrowly, we can ask whether the following comparison adjunction evinces a Quillen equivalence between $\widehat{\square}_\nu^{\mathrm{ty}}$ and $\widehat{\Delta}^{\mathrm{kq}}$.

2025/10/16 00:43

34

E. Cavallo and C. Sattler

Definition 4.35 (Triangulation) Define $\varnothing: \square_{\vee} \to \mathrm{PSh}(\Delta)$ to be the functor sending the $n$-cube $[1]^n$ to the $n$-fold product $(\Delta^1)^n$ of the 1-simplex, with the evident functorial action. The triangulation functor $\mathrm{T}: \mathrm{PSh}(\square_{\vee}) \to \mathrm{PSh}(\Delta)$ is the left Kan extension of $\varnothing$:

![img-18.jpeg](img-18.jpeg)

Triangulation has a right adjoint, the nerve functor $N_{\varnothing}: \mathrm{PSh}(\Delta) \to \mathrm{PSh}(\square_{\vee})$ defined by $N_{\varnothing}X := \mathrm{PSh}(\Delta)(\varnothing -, X)$.

### 4.3 Idempotent completion

Although the triangulation adjunction $\mathrm{T} \dashv N_{\varnothing}$ is the most immediate means of comparing $\overline{\square}_{\vee}^{\mathrm{N}}$ and $\widehat{\Delta}^{\mathrm{kq}}$, it is not the most convenient. Ideally, we would like to have a comparison on the level of the base categories, some functor $i: \Delta \to \square_{\vee}$ or vice versa, in which case we would obtain an adjoint triple $i_1 \dashv i^* \dashv i_*$ on their presheaf categories. This is too much to hope for, but we can define an embedding from $\Delta$ into the idempotent completion of $\square_{\vee}$, following the strategy used by Sattler [Sat19] and Streicher and Weinberger [SW21] to relate $\Delta$ and $\square_{\wedge \vee}$. The category of presheaves on any category $\mathbf{C}$ is equivalent to the category of presheaves on its idempotent completion $\overline{\mathbf{C}}$, the closure of $\mathbf{C}$ under splitting of idempotents [BD86]. We shall exhibit an embedding $\blacktriangle: \Delta \to \overline{\square}_{\vee}$; by composing the triple $\blacktriangle_1 \dashv \blacktriangle^* \dashv \blacktriangle_*$ with the adjoint equivalence $\blacksquare^*: \mathrm{PSh}(\overline{\square}_{\vee}) \xleftarrow{\mathrm{T}} \mathrm{PSh}(\square_{\vee}): \blacksquare_1$, we obtain a triple relating $\mathrm{PSh}(\Delta)$ and $\mathrm{PSh}(\square_{\vee})$.

We then observe that $\mathrm{T} \cong \blacktriangle^*\blacksquare_1$ (Lemma 4.48); thus the upshot of this detour is that $\mathrm{T}$ is also a right adjoint. It will, however, be easier to study the adjunction $\blacktriangle_1 \dashv \blacktriangle^*$ than $\mathrm{T} \dashv N_{\varnothing}$, in particular because both $\blacktriangle_1$ and $\blacktriangle^*$ are left Quillen adjoints (Corollary 4.53 and Lemma 4.54). We will first show in Section 7.1 that $\blacktriangle_1 \dashv \blacktriangle^*$ is a Quillen equivalence, then deduce formally that $\blacktriangle^* \dashv \blacktriangle_*$ and $\mathrm{T} \dashv N_{\varnothing}$ are also Quillen equivalences.

Definition 4.36 An idempotent in a category $\mathbf{C}$ is a morphism $f: A \to A$ such that $ff = f$. A splitting for an idempotent is a section-retraction pair $(s, r)$ such that $f = sr$.

The splitting of an idempotent is unique up to isomorphism if it exists: $s$ is the equalizer of the pair $f$, id: $A \to A$, while $r$ is the coequalizer of the same. We say that $\mathbf{C}$ is idempotent complete if every idempotent splits.

Definition 4.37 An idempotent completion of a category $\mathbf{C}$ is a fully faithful functor $i: \mathbf{C} \to \overline{\mathbf{C}}$ such that $\overline{\mathbf{C}}$ is idempotent complete and every object in $\overline{\mathbf{C}}$ is a retract of $iA$ for some $A \in \mathbf{C}$.

Equivalently, an idempotent completion is a universal (in a bicategorical sense) fully faithful functor $\mathbf{C} \to \overline{\mathbf{C}}$ into an idempotent complete category. We shall only need the following consequence of this characterization:

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

35

Proposition 4.38 (essentially BD86, Theorem 1) Given an idempotent completion $i: \mathbf{C} \to \overline{\mathbf{C}}$, the induced substitution functor $i^*: \mathrm{PSh}(\overline{\mathbf{C}}) \to \mathrm{PSh}(\mathbf{C})$ is an equivalence of categories.

We can describe the idempotent completion of $\square_{\vee}$ concretely as a full subcategory of SLat.

Definition 4.39 Write $\overline{\square}_{\vee}$ for the full subcategory of SLat consisting of finite inhabited distributive lattices. This subcategory contains all of $\square_{\vee}$; we write $\blacksquare: \square_{\vee} \to \overline{\square}_{\vee}$ for the inclusion.

Remark 4.40 Any finite inhabited lattice is bounded, with $\top$ and $\bot$ obtained as the join and meet of all elements respectively. Moreover, a finite lattice is distributive if and only if it is a Heyting algebra, i.e., supports an implication operator $\Rightarrow$. Note however that we do not require the morphisms of $\overline{\square}_{\vee}$ to preserve $\wedge, \bot, \top$, or $\Rightarrow$, only binary (i.e., non-empty finite) joins.

We show that $\blacksquare: \square_{\vee} \to \overline{\square}_{\vee}$ is an idempotent completion using the following observations of Horn and Kimura.

Proposition 4.41 (HK71, Theorem 1.1) A morphism in SLat is epic if and only it is surjective.

Proposition 4.42 (HK71, Corollaries 2.9 and 5.4) Recall that an object in a category is injective if maps into it extend along monomorphisms, and dually projective if maps out of it lift along epimorphisms. A finite semilattice $A \in \mathrm{SLat}_{\mathrm{fin}}$ is

- injective if and only if $A$ is a distributive lattice;
- projective if and only if $1 \star A$ is a distributive lattice.

Corollary 4.43 $\overline{\square}_{\vee}$ is closed under retracts in SLat.

Proof A retract of an inhabited finite semilattice is clearly inhabited and finite, and the class of injective objects is closed under retracts in any category.

Corollary 4.44 $\overline{\square}_{\vee}$ is idempotent complete.

Proof Note that SLat is idempotent complete because it has limits. The claim follows from this using Corollary 4.43.

Lemma 4.45 Any $A \in \overline{\square}_{\vee}$ is a retract of $[1]^n$ for some $n \in \mathbb{N}$.

Proof For any $A \in \overline{\square}_{\vee}$, we have a poset map $p: 1 \star UA \to A$ sending $\bot$ to $\bot$ and $a \in UA$ to $a$. Per Proposition 4.7, this induces a surjective semilattice map $p^\dagger: [1]^{UA} \to A$. This is epic by Proposition 4.41. As $A$ is distributive, so too is $1 \star A$, so $A$ is projective. Thus, the identity on $A$ factors through $p^\dagger$, exhibiting $A$ as a retract of $[1]^{UA}$.

2025/10/16 00:43

36

E. Cavallo and C. Sattler

Theorem 4.46 ■: □_V → □̅_V is an idempotent completion.

Proof By Corollary 4.44 and Lemma 4.45.

Recall from Remark 4.4 that we have an embedding Δ → SLat. The induced lattice structure on a simplex is distributive, so this embedding factors through □̅_V.

Notation 4.47 We write ▲: Δ → □̅_V for the inclusion of the simplices among the finite inhabited distributive semilattices.

We can now decompose the triangulation functor.

Lemma 4.48 We have ▲*■_! ≅ T: PSh(□_V) → PSh(Δ).

Proof As both functors are left adjoints and thus cocontinuous, it suffices to exhibit a natural isomorphism between their restrictions to representables, i.e., show that ▲*■_! ≅ ∅. Both ▲*■_! and ∅ preserve products, and ▲*■_! [1] ≅ Δ¹ ≅ ∅ [1] by inspection.

### 4.4 Two Quillen adjunctions

In light of the equivalence PSh(□̅_V) ≃ PSh(□_V), it now suffices to compare Δ̂^kq with the induced model structure □̅_V^v on PSh(□̅_V), which again has monomorphisms for cofibrations and fibrations generated by pushout products δ_k ∇̅ m. We begin by observing that both ▲_! and ▲_* are left Quillen adjoints.

Lemma 4.49 ▲_! preserves monomorphisms.

Proof Write Δ_a for the augmented simplex category, the full subcategory of Pos consisting of the objects [n] for n ∈ ℕ as well as [-1] := ∅. Write □̅_Va for the category of finite distributive semilattices, which similarly freely extends □̅_V with an initial object (the empty semilattice). The inclusion ▲ extends to an inclusion between the augmented categories:

$$\begin{array}{c} \Delta \xrightarrow{\blacktriangle} \overline{\square}_V \\ \iota \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta_a \xrightarrow{\blacktriangle}_a \overline{\square}_{Va}. \end{array}$$

The square is a pullback and the vertical maps are (discrete) Grothendieck opfibrations, so the square is exact in the sense that the canonical map v*(▲_a)_! → ▲_!t* is invertible [nLa24, Proposition 5.2 and Corollary 3.1]. This is also straightforward to check directly: the functors are cocontinuous, so it suffices to check on representables, and t* and v* preserve all representables except for the initial representable, which they send to an initial object. Since t is fully faithful, this gives ▲_! ≅ ▲_!t* t_* ≅ v*(▲_a)_!t*. Therefore, it suffices to prove that (▲_a)_! preserves monomorphisms.

Just like in simplicial sets, the monomorphisms in augmented simplicial sets form the left class of a weak factorization system generated by boundary inclusions (of augmented

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

37

simplices). As $(\blacktriangle_{a})_{1}$ is a left adjoint, it therefore suffices to show that it sends boundary inclusions to monomorphisms. The boundary inclusion $\partial\Delta^{n}\mapsto\Delta^{n}$ is the joint image of the non-identity face maps $\Delta^{k}\xrightarrow{s}\Delta^{n}$. The joint image of a set of maps $(f_{i}:A_{i}\to B)_{i\in I}$ in any pretopos is computed as the coequalizer of

$$\coprod_{i,j\in I}A_{i}\times_{B}A_{j}\longrightarrow\coprod_{i\in I}A_{i}.$$

It therefore suffices to check that $(\blacktriangle_{a})_{1}$ sends face maps to monomorphisms and preserves pullbacks of cospans whose legs are face maps. As face maps are monic, the latter condition implies the former. For the latter condition, as face maps go between representables and $\Delta_{a}$ has these pullbacks, it suffices to check that $\blacktriangle_{a}$ preserves pullbacks of cospans whose legs are face maps. In fact $\blacktriangle_{a}$ creates such pullbacks, as any subposet of a linear poset is again linear.

The following statements can be phrased more generally at the level of cylinder objects in a model category. They also have evident dual version in terms of path objects with fibrancy assumptions instead.

Lemma 4.50 In a cylindrical model category, let maps $f,g:A\to X$ be related by a homotopy $h:\mathbb{I}\otimes A\to X$. If $A$ is cofibrant, then $f$ is a weak equivalence exactly if $g$ is.

Proof The top maps in the following diagram are trivial cofibrations because $A$ is cofibrant:

![img-19.jpeg](img-19.jpeg)

The claim follows using 2-out-of-3.

In a cylindrical model category, a homotopy retract is a pair of maps $s:X\to Y,r:Y\to X$ equipped with a homotopy $h:\mathbb{I}\otimes X\to X$ from $rs$ to $\mathrm{id}_{X}$.

Corollary 4.51 In a cylindrical model category, any cofibrant homotopy retract of a weakly contractible object is weakly contractible.

Proof Let a homotopy retract $s:X\to Y,r:Y\to X,h:\mathbb{I}\otimes X\to X$ from $rs$ to $\mathrm{id}_{X}$ be given with $X$ cofibrant and $Y$ weakly contractible. By Lemma 4.50, $rs$ is a weak equivalence. Since $Y$ is weakly contractible, any endomorphism on $Y$ is a weak equivalence by 2-out-of-3. As the two binary sub-composites of the ternary composite $X\xrightarrow{s}Y\xrightarrow{r}X\xrightarrow{s}Y$ are weak equivalences, both $r$ and $s$ are weak equivalences by 2-out-of-6 [Rie14, Remark 2.1.3].

Lemma 4.52 Consider a model category $\mathbf{M}$ and a left adjoint $L:\widehat{\Delta}^{\mathrm{leq}}\to \mathbf{M}$ that preserves cofibrations. Then $L$ is a left Quillen adjoint exactly if it sends representables to weakly contractible objects.

2025/10/16 00:43

38

E. Cavallo and C. Sattler

Proof For the non-trivial direction, assume that $L$ sends representables to weakly contractible objects. Given $n \geq 1$ and $I \subseteq [n]$, write $\Lambda_I^n$ for the union of the subobjects $d_i: \Delta^{n-1} \mapsto \Delta^n$ over $i \in I$. We check by induction that $L$ sends $\Lambda_I^n \mapsto \Delta^n$ to a trivial cofibration for $n \in \mathbb{N}$ and $\emptyset \subseteq I \subseteq [n]$. When $|I| = 1$, $\Lambda_I^n$ is the representable $\Delta^{n-1}$, so the claim holds by assumption and 2-out-of-3. Otherwise, choose some $i \in I$. We have the following pushout square, which is preserved by $L$:

$$\begin{array}{c} \Lambda_{d_i^{-1}(I)}^{n-1} \longrightarrow \Lambda_{I \setminus \{i\}}^n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Delta^{n-1} \xrightarrow[d_i]{} \Lambda_I^n. \end{array}$$

By induction hypothesis, $L$ sends the left vertical map to a trivial cofibration. As trivial cofibrations are closed under cobase change, $L$ then also sends the right vertical map to a trivial cofibration. By induction hypothesis, $L$ sends $\Lambda_{I \setminus \{i\}}^n \mapsto \Delta^n$ to a trivial cofibration. By 2-out-of-3, we conclude that $L$ sends $\Lambda_{I \setminus \{i\}}^n \mapsto \Delta^n$ to a trivial cofibration. For $I = [n] \setminus k$, we obtain that $L$ sends the horn inclusion $\Lambda_k^n \to \Delta^n$ to a trivial cofibration. This makes $L$ a left Quillen adjoint.

The combinatorics of the above proof have a conceptual explanation in terms of the pushout join in augmented simplicial sets, which produces boundary inclusions and horn inclusions starting from the maps $\emptyset \to 1$ and $\Delta^{-1} \to 1$.

Corollary 4.53 (cf. Sat 19, Proposition 3.6) $\blacktriangle_!$ is a left Quillen adjoint $\widehat{\Delta}^{\mathrm{kq}} \to \overline{\square}_{\vee}^{\mathrm{ty}}$.

Proof By Lemma 4.49, $\blacktriangle_!$ preserves monomorphisms. Using Lemma 4.52, it suffices to show that $\blacktriangle_! \Delta^n \cong \not\cong [n]$ is weakly contractible for $n \in \mathbb{N}$. For this, we observe that $\not\cong [n]$ is a homotopy retract of 1 for each $n \in \mathbb{N}$ via the homotopy $(t, i) \mapsto (t \vee i): [1] \times [n] \to [n]$ and apply Corollary 4.51.

Lemma 4.54 (cf. Sat 19, §3.3) $\blacktriangle^*$ is a left Quillen adjoint $\overline{\square}_{\vee}^{\mathrm{ty}} \to \widehat{\Delta}^{\mathrm{kq}}$.

Proof $\blacktriangle^*$ preserves monomorphisms because it is a right adjoint. As it is also a left adjoint, it also preserves pushout products, so $\blacktriangle^*(\delta_k \overline{\times} m) \cong \blacktriangle^* \delta_k \overline{\times} \blacktriangle^* m \cong d_{1-k} \overline{\times} \blacktriangle^* m$ is a trivial cofibration for any $k \in \{0, 1\}$ and $m: A \mapsto B$.

We quickly see that $\blacktriangle_! \dashv \blacktriangle^*$ is a Quillen coreflection in the following sense:

Lemma 4.55 The derived unit $X \xrightarrow{\eta_X} \blacktriangle^* \blacktriangle_! X \to \blacktriangle^* ((\blacktriangle_! X)^{\mathrm{fib}})$ is valued in weak equivalences.

Proof It is equivalent to prove the unit $\eta$ is valued in weak equivalences: any fibrant replacement map $\blacktriangle_! X \mapsto (\blacktriangle_! X)^{\mathrm{fib}}$ is a trivial cofibration, so is mapped to a trivial cofibration by the left Quillen adjoint $\blacktriangle^*$. But $\blacktriangle$ is fully faithful, so the unit is valued in isomorphisms.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

39

## 5 Relatively elegant Reedy categories

To show that the adjunction $\blacktriangle_{\cdot} \dashv \blacktriangle^{*}$ defined in Section 4.4 is a Quillen equivalence, it remains to check that its counit is valued in weak equivalences, that is, that $\varepsilon_X: \blacktriangle_{\cdot}\blacktriangle^{*}X \to X$ is a weak equivalence for every fibrant $X \in \mathrm{PSh}(\overline{\square}_{\vee})$. We noted earlier (Proposition 2.20) that for an elegant Reedy category $\mathbf{R}$, we have a convenient set of objects—the automorphism quotients of representables—that generate the whole of $\mathrm{PSh}(\mathbf{R})$ upon saturation by monomorphisms. We will see later on (Corollary 7.3) that the class of $X \in \mathrm{PSh}(\overline{\square}_{\vee})$ for which $\varepsilon_X$ is a weak equivalence is saturated by monomorphisms, so if $\overline{\square}_{\vee}$ were an elegant Reedy category we would have a line of attack. Unfortunately, this is not the case. Indeed, $\overline{\square}_{\vee}$ is not a Reedy category at all (Proposition A.1).

We therefore require a generalization of elegant Reedy theory. We consider categories $\mathbf{C}$ equipped with a fully faithful functor $i: \mathbf{C} \to \mathbf{R}$ into a Reedy category $\mathbf{R}$ that has pushouts of lowering spans and is elegant relative to $i$: such that $N_i := i^* \nmid: \mathbf{R} \to \mathrm{PSh}(\mathbf{C})$ preserves lowering pushouts. In this case, the objects of $\mathrm{PSh}(\mathbf{C})$ are generated upon saturation by monos from the set of automorphism quotients of objects in the image of $N_i$. When $i = \mathrm{id}$, we recover the original theorem for elegant Reedy categories. In Section 6, we shall see that $\overline{\square}_{\vee}$ embeds elegantly in the category of inhabited finite semilattices.

In Section 5.1, we review Reedy monomorphisms and the construction of cellular presentations for maps between presheaves over a Reedy category. In Section 5.2, we narrow our focus to what we call pre-elegant Reedy categories, those having pushouts of lowering spans. The Reedy monic presheaves are in this case characterized as those sending lowering pushouts to pullbacks. This sets the stage for Section 5.3, where we define and study elegance relative to an embedding $i: \mathbf{C} \to \mathbf{R}$.

### 5.1 Cellular presentations and Reedy monomorphisms

For the theory of cellular presentations of diagrams over Reedy categories, we follow Riehl and Verity [RV14; Rie17]. Almost none of the content in this section is novel. For simplicity, we restrict our attention throughout to presheaves, though much of the theory generalizes to functors from a Reedy category into any category.

#### 5.1.1 Weighted colimits

Riehl and Verity observe that many arguments in Reedy category theory are naturally phrased in terms of weighted (col)imits. While more fundamental to enriched category theory, these can have a clarifying role even in ordinary (i.e., Set-enriched) category theory.

Definition 5.1 Let $\mathbf{E}$ be a category. Let a functor $W: \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$ (the weight) and a diagram $F: \mathbf{C} \to \mathbf{E}$ be given. A weighted colimit for this data is an object $W \circledast_{\mathbf{C}} F \in \mathbf{E}$, equipped with a natural transformation $W \to \mathbf{E}(F-, W \circledast_{\mathbf{C}} F)$, such that for any $X \in \mathbf{E}$ the induced map

$$\mathbf{E}(W \circledast_{\mathbf{C}} F, X) \to [\mathbf{C}^{\mathrm{op}}, \mathbf{Set}](W, \mathbf{E}(F-, X))$$

2025/10/16 00:43

40

E. Cavallo and C. Sattler

of sets is an isomorphism.

Informally, the weight $W$ specifies how many "copies" of each object in the diagram $F$ to include in the weighted colimit $W \circledast_{\mathbf{C}} F$.

Example 5.2 The ordinary colimit of a diagram $F: \mathbf{C} \to \mathbf{E}$ can be described as $1 \circledast_{\mathbf{C}} F$, a colimit weighted by the terminal presheaf $1 \in \mathrm{PSh}(\mathbf{C})$. Conversely, any weighted colimit $W \circledast_{\mathbf{C}} F$ admits a characterization as an ordinary colimit over the category of elements of $W$:

$$W \circledast_{\mathbf{C}} F \cong \operatorname{colim}\left(\operatorname{el} W \xrightarrow{\pi} \mathbf{C} \xrightarrow{F} \mathbf{E}\right).$$

In particular, any cocomplete category has weighted colimits.

Example 5.3 Recall that a tensor of a set $S \in \mathbf{Set}$ and object $X \in \mathbf{E}$ is an object $S * X$ such that morphisms $S * X \to Y$ correspond to objects $\mathbf{Set}(S, \mathbf{E}(X, Y))$, i.e., families of morphisms $f_s: X \to Y$ for $s \in S$. In ordinary category theory, this is simply the $S$-ary coproduct $\coprod_{s \in S} X$, so can be expressed as the weighted colimit $1 \circledast_S \Delta X$ of the constant diagram $\Delta X: S \to \mathbf{E}$. Alternatively, we can encode the tensor as the $S$-weighted colimit $S \circledast_1 X$ of the diagram $X: \mathbf{1} \to \mathbf{E}$ over the terminal category. We can characterize any weighted colimit $W \circledast_{\mathbf{C}} F$ as a coend of tensors:

$$W \circledast_{\mathbf{C}} F \cong \int^{c \in \mathbf{C}} W_c * F^c.$$

We will always be working in cocomplete categories. For a given $\mathbf{C}$, weighted colimits over $\mathbf{C}$ are then functorial in both the weight and the diagram, giving a bifunctor $\circledast_{\mathbf{C}}: [\mathbf{C}^{\mathrm{op}}, \mathbf{Set}] \times [\mathbf{C}, \mathbf{E}] \to \mathbf{E}$. This functoriality will be an essential tool. In particular, we will often take a family of weighted colimits over a family of weights:

Notation 5.4 Given a family of weights $W: \mathbf{D} \times \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$ and $F: \mathbf{C} \to \mathbf{E}$, we write $W \circledast_{\mathbf{C}} F: \mathbf{D} \to \mathbf{E}$ for the result of calculating the weighted colimit pointwise, that is $(W \circledast_{\mathbf{C}} F)^d := W^d \circledast_{\mathbf{C}} F$.

Remark 5.5 From the characterization in terms of ordinary colimits, it follows that weighted colimits in presheaf categories are computed pointwise. Thus for $W: \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$ and $F: \mathbf{C} \times \mathbf{D}^{\mathrm{op}} \to \mathbf{Set}$, we have $(W \circledast_{\mathbf{C}} F)_d \cong W \circledast_{\mathbf{C}} F_d$, where on the left we regard $F$ as a functor $\mathbf{C} \to \mathrm{PSh}(\mathbf{D})$.

It follows quickly from the universal property defining weighted colimits that the bifunctor $\circledast_{\mathbf{C}}$ preserves colimits in both arguments. It is therefore determined by its behavior on representable weights, which is simply characterized:

Proposition 5.6 Naturally in $c \in \mathbf{C}$ and $X: \mathbf{C} \to \mathbf{E}$, we have $\not\cong c \circledast_{\mathbf{C}} X \cong X^c$. ■

Corollary 5.7 Naturally in $W: \mathbf{D}^{\mathrm{op}} \to \mathbf{Set}$, $V: \mathbf{D} \times \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$, and $F: \mathbf{C} \to \mathbf{E}$, we have $(W \circledast_{\mathbf{D}} V) \circledast_{\mathbf{C}} F \cong W \circledast_{\mathbf{D}} (V \circledast_{\mathbf{C}} F)$.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

41

Proof By cocontinuity, it suffices to check the case where W is representable.

Notation 5.8 In this section, we use the notation $\nexists C: C^{\mathrm{op}} \times C \to \mathbf{Set}$ for the hombifunctor $C(-, -)$. Thus the representable functor for $c \in C$, written $\nexists c$ in our usual notation, may now be written as $\nexists C^c$, while we also have the co-representable $\nexists C_c: C \to \mathbf{Set}$. With our notation for parameterized weighted colimits, Proposition 5.6 then tells us that $\nexists C \circledast_C X \cong X$ for any $X \in \mathrm{PSh}(C)$. We have an analogous equation in the second argument: $X \circledast_C \nexists C \cong X$.

### 5.1.2 Cellular presentations of presheaves

A central theorem of Reedy theory is the existence of cellular presentations: when $\mathbf{R}$ is a Reedy category, any $\mathbf{R}$-indexed diagram is a sequential colimit of maps that successively attach cells of increasing degree. Likewise, any natural transformation between $\mathbf{R}$-indexed diagrams decomposes as a transfinite composite of such maps. In the Riehl–Verity style, the intermediate objects and maps are obtained by taking (Leibniz) weighted colimits of the input diagram. As $X \cong \nexists \mathbf{R} \circledast_{\mathbf{R}^{\mathrm{op}}} X$ for any diagram $X$, one can exhibit a cellular presentation for $X$ by constructing a cellular presentation for $\nexists \mathbf{R}$ and then applying the cocontinuous functor $(-) \circledast_{\mathbf{R}^{\mathrm{op}}} X$.

For the remainder of this section, we fix a Reedy category $\mathbf{R}$.

Definition 5.9 For each $n \in \mathbb{N}$, define $\partial \mathbf{R}: \mathrm{sk}_{<n}\mathbf{R} \mapsto \nexists \mathbf{R}$ to be the subfunctor of arrows of degree less than $n$.

Definition 5.10 For any $n \in \mathbb{N}$, write $\mathbf{R}[n]$ for the subcategory of $\mathbf{R}$ consisting of objects of degree $n$ and isomorphisms between them. We introduce the following notation for restrictions of $\nexists \mathbf{R}$ where one argument or the other is required to have a given degree:

![img-20.jpeg](img-20.jpeg)

We similarly introduce notation for the corresponding restrictions of the skeleton bifunctor $\mathrm{sk}_{<n}\mathbf{R}: \mathbf{R}^{\mathrm{op}} \times \mathbf{R} \to \mathbf{Set}$:

![img-21.jpeg](img-21.jpeg)

Finally, we write $\partial_n \mathbf{R}: \partial_n \mathbf{R} \mapsto \nexists_n \mathbf{R}$ and $\partial^n \mathbf{R}: \partial^n \mathbf{R} \mapsto \nexists^n \mathbf{R}$ for the restrictions of the inclusion $\partial \mathbf{R}: \mathrm{sk}_{<n}\mathbf{R} \mapsto \nexists \mathbf{R}$.

Notation 5.11 For $r \in \mathbf{R}$ of degree $n$, we abbreviate $\partial_r \mathbf{R} := (\mathrm{sk}_{<n}\mathbf{R})_r: \mathbf{R} \to \mathbf{Set}$ and $\partial^r \mathbf{R} := (\mathrm{sk}_{<n}\mathbf{R})^r: \mathbf{R}^{\mathrm{op}} \to \mathbf{Set}$. Likewise, we write $\partial_r \mathbf{R} := (\partial \mathbf{R})_r: \partial_r \mathbf{R} \mapsto \nexists \mathbf{R}_r$ and $\partial^r \mathbf{R} := (\partial \mathbf{R})^r: \partial^r \mathbf{R} \mapsto \nexists \mathbf{R}^r$.

2025/10/16 00:43

42

E. Cavallo and C. Sattler

Definition 5.12 For any $f: X \to Y$ in $\mathrm{PSh}(\mathbf{R})$ and $n \in \mathbb{N}$, the $<n$-skeleton map for $f$ is the Leibniz weighted colimit

$$(\mathrm{sk}_{<n}\mathbf{R} \mapsto \mathscr{L}\mathbf{R}) \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f.$$

We write $\mathrm{sk}_{<n}f \in \mathrm{PSh}(\mathbf{R})$ for the domain of this map, which we call the $<n$-skeleton of $f$; its codomain is $Y$. For $Y \in \mathrm{PSh}(\mathbf{R})$, we write $\mathrm{sk}_{<n}Y$ for the $n$-skeleton of the map $0 \mapsto Y$.

Note that the $<0$-skeleton map is $(0 \mapsto \mathscr{L}\mathbf{R}) \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f \cong \mathscr{L}\mathbf{R} \circledast_{\mathbf{R}^{\mathrm{op}}} f \cong f$. For each $m \leq n \in \mathbb{N}$, the inclusion $\mathrm{sk}_{<m}\mathbf{R} \mapsto \mathrm{sk}_{<n}\mathbf{R}$ induces a morphism $\mathrm{sk}_{<m}f \to \mathrm{sk}_{<n}f$ by functoriality of weighted colimits, and the fact that $\mathscr{L}\mathbf{R}$ is the union of the subfunctors $\mathrm{sk}_{<n}\mathbf{R}$ implies that $Y \cong \mathrm{colim}_{n \in \mathbb{N}} \mathrm{sk}_{<n}f$. Thus we have a natural decomposition of $f$ as the transfinite composite $\mathrm{sk}_{<0}f \to \mathrm{sk}_{<1}f \to \mathrm{sk}_{<2}f \to \cdots$ where we may compute $\mathrm{sk}_{<n}f \cong X \sqcup_{\mathrm{sk}_{<n}X} \mathrm{sk}_{<n}Y$. The chain of skeleta may be further decomposed in terms of latching maps:

Definition 5.13 Given $f: X \to Y$ in $\mathrm{PSh}(\mathbf{R})$ and $r \in \mathbf{R}$, define the latching map $\widehat{\ell}_r f \in \mathbf{Set}^\to$ for $f$ at $r$ by the Leibniz weighted colimit

$$\widehat{\ell}_r f := \partial_r \mathbf{R} \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f.$$

The codomain of this map is $Y_r$; we write $L_r f$ for its domain and call this the latching object for $f$ at $r$.

We write $\widehat{\ell}_r Y$ and $L_r Y$ for the latching map and object of $0 \mapsto Y$ at $r$. For general $f: X \to Y$, we can calculate that $L_r f \cong X_r \sqcup_{L_r X} L_r Y$ and $\widehat{\ell}_r f \cong [f_r, L_r f]$. It is convenient to have notation for the collected $\mathbf{R}[n]$-sets of latching maps at a given degree:

Definition 5.14 Given $f: X \to Y$ and $n \in \mathbb{N}$, we define the $n$th latching map of $f$ by $\widehat{\ell}_n f := \partial_n \mathbf{R} \widehat{\circledast}_{\mathbf{R}^{\mathrm{op}}} f$. We write $L_n f \in \mathrm{PSh}(\mathbf{R}[n])$ for its domain and $f_n \in \mathrm{PSh}(\mathbf{R}[n])$ for its codomain.

These maps are assembled from the latching maps at the individual objects of degree $n$: we have $(\widehat{\ell}_n f)_r \cong \widehat{\ell}_r f$ for each $r \in \mathbf{R}[n]$.

We can now exhibit the maps between successive $<n$-skeleta as pushouts of Leibniz weighted colimits of boundary inclusions and latching maps. The induced decomposition of a map $f$ into a sequential colimit of pushouts of basic maps is what we mean by a cellular presentation of $f$:

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

43

Proposition 5.15 (Rie17, Corollary 4.21) For any $f: X \to Y$ and $n \in \mathbb{N}$, we have a pushout square of the following form:

![img-22.jpeg](img-22.jpeg)

We refer to the maps $\partial^n\mathbf{R}\widehat{\otimes}_{\mathbf{R}[n]\mathrm{op}}\widehat{\ell}_n f$ as cell maps.

Proof By applying $(-)\widehat{\otimes}_{\mathbf{R}^{\mathrm{op}}}f$ to a pushout square in $\mathbf{R}^{\mathrm{op}}\times \mathbf{R}\to \mathbf{Set}$; see [Rie17, Theorem 4.15].

Corollary 5.16 Every $f: X \to Y$ in $\mathrm{PSh}(\mathbf{R})$ has a cellular presentation by maps of the form $\partial^n\mathbf{R}\widehat{\otimes}_{\mathbf{R}[n]\mathrm{op}}\widehat{\ell}_nf$.

For our purposes, namely working with properties saturated by monomorphisms, it is important to know when the cell maps are monic.

Definition 5.17 A map $f: X \to Y$ in $\mathrm{PSh}(\mathbf{R})$ is a Reedy monomorphism when $\widehat{\ell}_r f$ is monic in Set for all $r \in \mathbf{R}$.

Here and in the following, we are specializing the theory of Reedy cofibrations to the (mono, epi) weak factorization system on Set. To see when Reedy monomorphisms have monic cell maps, we use the following lemma. Recall that a map is epi-projective if it has the left lifting property against all epimorphisms.

Proposition 5.18 Let $\mathbf{C}$ be a small category, $f \in [\mathbf{C}^{\mathrm{op}}, \mathbf{Set}]^{\rightarrow}$, and $g \in [\mathbf{C}, \mathbf{Set}]^{\rightarrow}$. If $f$ is epi-projective and $g$ is monic, then $f \widehat{\otimes}_{\mathbf{C}} g$ is monic.

Proof By [Rie17, Lemma 3.13 and Corollary 3.17] applied to the (mono, epi) weak factorization system on Set.

Lemma 5.19 If isos act freely on lowering maps in $\mathbf{R}$, then $\partial^n\mathbf{R}_r$ is epi-projective in $\mathbf{R}[n] \to \mathbf{Set}$.

Proof A given morphism from $r$ to an object of degree $n$ is either a lowering map or has degree less than $n$. This induces the following coproduct decomposition in $\mathbf{R}[n] \to \mathbf{Set}$:

![img-23.jpeg](img-23.jpeg)

Since epi-projective is the left class in a weak factorization system, it is stable under cobase change. It thus suffices to show that $\mathbf{R}^{-}(r, -)$ is epi-projective. Since isos act

2025/10/16 00:43

44

E. Cavallo and C. Sattler

freely on $\mathbf{R}^{-}(r, -)$, it is the left Kan extension along some functor $A \to \mathbf{R}[n]$ of some $F: A \to \mathbf{Set}$ with $A$ a set. Recall that epimorphisms are characterized levelwise in Set-valued functors. By adjoint transposition, it thus suffices to show that $F$ is epi-projective. Since $A$ is a set, this just means that $F$ is levelwise epi-projective. And in Set, every object is epi-projective.

Corollary 5.20 Suppose that isos act freely on lowering maps in $\mathbf{R}$. Given a Reedy monic $f \in \mathrm{PSh}(\mathbf{R})^{\rightarrow}$, the map $\mathfrak{o}^n\mathbf{R} \widehat{\otimes}_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n f$ is monic for all $n \in \mathbb{N}$.

Proof We have $(\mathfrak{o}^n\mathbf{R} \widehat{\otimes}_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n f)_r = \mathfrak{o}^n\mathbf{R}_r \widehat{\otimes}_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n f$ for every $r \in \mathbf{R}$. We know $\mathfrak{o}^n\mathbf{R}_r$ is epi-projective by Lemma 5.19, and $\widehat{\ell}_n f$ is monic by assumption, so their Leibniz weighted colimit is monic by Proposition 5.18.

### 5.1.3 Eilenberg-Zilber decompositions

The Reedy monomorphisms with initial domain can be characterized more simply: an object $X$ is Reedy monic exactly if every element of $X$ writes uniquely up to isomorphism as a degeneracy of a non-degenerate element of $X$. We are not aware of a proof of this precise statement (Lemma 5.24) in the literature, though we would be surprised if it were unknown. We use Cisinski's term "Eilenberg-Zilber decomposition" [Cis06, Proposition 8.1.13] for what Berger and Moerdijk call standard decompositions.

Definition 5.21 Let $X \in \mathrm{PSh}(\mathbf{R})$. We say that $x \in X_r$ is non-degenerate when every lowering map $e: r \xrightarrow{\sim} s$ admitting an $x' \in X_s$ with $x'e = x$ is an isomorphism. An Eilenberg-Zilber (EZ) decomposition of $x \in X_r$ is a pair $(e, x')$ where $x' \in X_s$ is non-degenerate, $e: r \to s$ is a lowering map, and $x = x'e$. We regard two EZ decompositions $(e_0, x_0')$ and $(e_1, x_1')$ of $x$ as isomorphic when there exists an isomorphism $\theta: s_0 \cong s_1$ in $\mathbf{R}$ such that $x_0'\theta = x_1'$ and $e_0 = e_1\theta$. We say $X$ has unique EZ decompositions when any two EZ decompositions of any element of $X$ are isomorphic.

Remark 5.22 Every element of a presheaf admits at least one EZ decomposition: for any $x \in X_r$ there exists a minimal $n \in \mathbb{N}$ such that $x$ factors though a lowering map to an object of degree $n$, and any such factorization is an EZ decomposition.

Proposition 5.23 (RV14, Observation 3.23) Given $X \in \mathrm{PSh}(\mathbf{R})$ and $r \in \mathbf{R}$, we have an isomorphism

$$\begin{array}{c} L_r X_- \quad \widehat{\ell}_r X_- \\ \downarrow \\ \downarrow^W \\ L_r X \quad \xrightarrow{\widehat{\ell}_r X} X_r, \end{array}$$

where $X_- \in \mathrm{PSh}(\mathbf{R}^-)$ is the restriction of $X$ along the Reedy category inclusion $\mathbf{R}^- \to \mathbf{R}$.

Lemma 5.24 A presheaf $X \in \mathrm{PSh}(\mathbf{R})$ is Reedy monic if and only if it has unique EZ decompositions.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

45

Proof Suppose that $X$ is Reedy monic. We show that any two EZ decompositions of any $x \in X_r$ are isomorphic by induction on $|r|$. Let two such factorizations $(e_0, x_0)$, $(e_1, x_1)$ be given. If either of $e_0$ or $e_1$ is an isomorphism, then the other must be as well, in which case the factorizations are trivially isomorphic; thus we can assume that each $e_k$ strictly decreases degree. Then $(e_0, x_0)$ and $(e_1, x_1)$ belong to $L_r X_-$; because $X$ is Reedy monic, they are moreover equal therein. By the concrete characterization of colimits in Set, we have a finite sequence of lowering spans $s_i \xleftarrow{f_i} t_i \xrightarrow{f'_i} s_{i+1}$ for $0 \le i < n$, always with $|s_i|, |t_i| < |r|$, together with elements $y_i: \not\cong s_i \to X$ for each $i \le n$, such that $y_0 = x_0, y_n = x_1$, and $y_i f_i = y_{i+1} f'_i$:

![img-24.jpeg](img-24.jpeg)

By taking an EZ decomposition of each $y_i$ and absorbing the lowering map into $f'_i, f_{i+1}$, we can assume without loss of generality that each $y_i$ is non-degenerate. Then for each $i$, the equation $y_i f_i = y_{i+1} f'_i$ makes $(y_i, f_i)$ and $(y_{i+1}, f'_i)$ EZ decompositions of the same element of $X_{t_i}$. As $|t_i| < |r|$, it follows by induction hypothesis that they are isomorphic. Chaining these isomorphisms, we conclude that $(e_0, x_0)$ and $(e_1, x_1)$ are isomorphic.

Now suppose conversely that $X$ has unique EZ decompositions. By Proposition 5.23, it suffices to show the map $L_r X_- \to X_r$ is monic. The elements of $L_r X_-$ are pairs $(e: r \to s, x \in X_s)$ where $e$ is a strictly lowering map, quotiented by the relation $(fe, x) = (e, xf)$ for any $f \in \mathbf{R}^-$; the latching map sends $(e, x)$ to $xe \in X_r$. Let $(e_0, x_0), (e_1, x_1) \in L_r X_-$ be given such that $x_0 e_0 = x_1 e_1$. Without loss of generality, we may assume that these are EZ decompositions, in which case they are isomorphic and thus equal as elements of $L_r X_-$.

### 5.1.4 Saturation by monomorphisms

Now we check that the class of Reedy monic presheaves is contained in the saturation by monos of the set of automorphism quotients of representables, assuming isos act freely on lowering maps in $\mathbf{R}$.

Lemma 5.25 For any $X \in \mathrm{PSh}(\mathbf{R}[n])$, the presheaf $\not\cong^n \mathbf{R} \circledast_{\mathbf{R}[n]^op} X$ is a coproduct of automorphism quotients of representables.

Proof Write $\mathbf{R}[n]$ as a coproduct of groups $\mathbf{R}[n] \cong \coprod_i G_i$. Using the characterization of orbits as quotients by stabilizer groups, we may decompose $X$ as a coproduct of orbits $X \cong \coprod_{i,j} \not\cong r_i / H_{ij}$, where $r_i \in \mathbf{R}$ is the point of $G_i$. By cocontinuity of $\not\cong^n \mathbf{R} \circledast_{\mathbf{R}[n]^op} (-)$, we then have

$$\not\cong^n \mathbf{R} \circledast_{\mathbf{R}[n]^op} X \cong \coprod_{i,j} (\not\cong^n \mathbf{R} \circledast_{\mathbf{R}[n]^op} \not\cong r_i) / H_{ij} \cong \coprod_{i,j} \not\cong r_i / H_{ij}$$

2025/10/16 00:43

46

E. Cavallo and C. Sattler

as desired.

Lemma 5.26 Any colimit of a groupoid of representables in PSh(R) is Reedy monic.

Proof Let a groupoid G and d: G → R be given. Set C := colim_{i∈G} ∉ d^i. We show that C has unique EZ decompositions. Let two EZ decompositions (e_0, x_0) and (e_1, x_1) of the same element of C be given. As colimits are computed pointwise, each x_k factors as x_k = i_k m_k through some leg i_k: ∉ d^{i_k} → C of the coproduct and we have an arrow g: i_0 ≅ i_1 in G making the following diagram commute:

![img-25.jpeg](img-25.jpeg)

Each m_k must be a raising map because x_k is non-degenerate. By uniqueness of Reedy factorizations, we have an isomorphism θ: s_0 ≅ s_1 fitting in the diagram above.

Theorem 5.27 Let R be a Reedy category in which isos act freely on lowering maps. Let P ⊆ PSh(R) be a class of objects such that

- for any r ∈ R and H ≤ Aut_R(r), we have ∉ r/H ∈ P;
- P is saturated by monomorphisms.

Then P contains every Reedy monic presheaf.

Proof First we show by induction on n that sk_{<n}X ∈ P for any Reedy monic presheaf X. It then follows that X ≅ colim_{n∈N} sk_{<n}X ∈ P by saturation.

In the base case, sk_{<0}X is the empty coproduct and thus belongs to P by saturation. For any n ∈ N, we have the following pushout square by Proposition 5.15:

![img-26.jpeg](img-26.jpeg)

The upper horizontal map is monic by Corollary 5.20, the lower by closure of monos in PSh(R) under cobase change. We have sk_{<n}X ∈ P by induction hypothesis. The upper-right corner is ∉^n R ⊗_{R[n]op} X_n, which belongs to P by Lemma 5.25. Finally, the upper-left corner is by definition the following pushout object:

![img-27.jpeg](img-27.jpeg)

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

47

The upper horizontal map is monic by Proposition 5.18 and Lemma 5.19, as we can write it as the pushout product $\partial^n\mathbf{R}\circledast_{\mathbf{R}[n]^{\mathrm{op}}}(\emptyset \mapsto L_nX)$. The object $\not\perp^n\mathbf{R}\circledast_{\mathbf{R}[n]^{\mathrm{op}}}L_nX$ is in $\mathcal{P}$ by Lemma 5.25. Using Corollary 5.7, we have

$$\partial^n\mathbf{R}\circledast_{\mathbf{R}[n]^{\mathrm{op}}}F\cong(\mathrm{sk}_{<n}\mathbf{R}\circledast_{\mathbf{R}^{\mathrm{op}}}\not\perp^n\mathbf{R})\circledast_{\mathbf{R}[n]^{\mathrm{op}}}F\cong\mathrm{sk}_{<n}\mathbf{R}\circledast_{\mathbf{R}^{\mathrm{op}}}(\not\perp^n\mathbf{R}\circledast_{\mathbf{R}[n]^{\mathrm{op}}}F)$$

for any $F$. The objects $\partial^n\mathbf{R}\circledast_{\mathbf{R}[n]^{\mathrm{op}}}L_nX$ and $\partial^n\mathbf{R}\circledast_{\mathbf{R}[n]^{\mathrm{op}}}X_n$ thus belong to $\mathcal{P}$ by Lemmas 5.25 and 5.26 and the induction hypothesis. By saturation, the upper-left corner of our original pushout diagram now belongs to $\mathcal{P}$. For the same reason, we conclude that $\mathrm{sk}_{<n+1}X$ belongs to $\mathcal{P}$.

## 5.2 Pre-elegant Reedy categories

We next consider the subclass of Reedy categories in which any span of lowering maps has a pushout. This restriction has some simplifying consequences (e.g., that all lowering maps are epic), and we can characterize the Reedy monic presheaves over such categories as those preserving lowering pushouts.

Definition 5.28 A Reedy category is pre-elegant when it has pushouts of lowering spans.

Intuitively, this means that any pair of lowering maps from the same object has a universal combination, the diagonal of their pushout. Of course, any elegant Reedy category is pre-elegant, so $\Delta$ is one example. Our motivating example is the (surjective, mono) Reedy structure on the category of finite inhabited semilattices, which is pre-elegant but not elegant. In Section 6, we see this is an instance of a general class of examples: the (surjective, mono) Reedy structure on the category $\mathrm{Alg}(\mathbf{T})_{\mathrm{fin}}$ of finite algebras for a Lawvere theory $\mathbf{T}$ is always pre-elegant, but not necessarily elegant.

The following lemma generalizes the fact that any lowering map in an elegant Reedy category is split epic, with essentially the same proof as Bergner and Rezk's Proposition 3.8(3) [BR13].

Lemma 5.29 Let $\mathbf{R}$ be a pre-elegant Reedy category. Then any lowering map is epic.

Proof Consider a lowering map $e: r \xrightarrow{\quad} s$. We take the pushout of $e$ with itself, then use its universal property to see that the legs of the pushout are split monic:

![img-28.jpeg](img-28.jpeg)

Any split mono is a raising map (Corollary 2.15), so $f_0, f_1$ are isomorphisms. Thus $e$ is epic.

2025/10/16 00:43

48

E. Cavallo and C. Sattler

Corollary 5.30 If R is a pre-elegant Reedy category, then isos act freely on lowering maps in R.

Lemma 5.31 Let R be a Reedy category in which isos act freely on lowering maps. If X ∈ PSh(R) is Reedy monic, then X sends pushouts of lowering spans (should they exist) to pullbacks.

Proof Let a pushout square of lowering maps be given like so:

$$\begin{array}{c} r \xrightarrow{e_1} s_1 \\ e_0 \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text { f } _ {1} \\ s _ {0} \xrightarrow{f _ {0}} t. \end{array}$$

Suppose we have x₀ ∈ Xₛ₀ and x₁ ∈ Xₛ₁ such that x₀e₀ = x₁e₁; we show this data determines a unique element of Xₜ restricting to x₀ and x₁. For each k ∈ {0, 1}, take an EZ decomposition (gₖ, yₖ) of xₖ. Then (g₀e₀, y₀) and (g₁e₁, y₁) are EZ decompositions of the same map, so by Lemma 5.24 they are isomorphic via some θ: u₀ ≅ u₁. The universal property of the pushout in R then provides a map h₁: t → u₁ like so:

![img-29.jpeg](img-29.jpeg)

This gives our desired element y₁h₁ ∈ Xₜ restricting to xₖ along each fₖ. Note that h₁ is a lowering map by Lemma 2.14.

To see that this element is unique, suppose we have x ∈ Xₜ such that xfₖ = xₖ for k ∈ {0, 1}. Take an EZ decomposition (h, y) of X, say through u ∈ R. By uniqueness of EZ decompositions, we have isomorphisms ψₖ as shown:

![img-30.jpeg](img-30.jpeg)

Because isos act freely on lowering maps, we have ψ₁⁻¹ψ₀ = θ. It follows from the universal property of the pushout in R that ψ₁h = h₁, thus that yh = y₁h₁ as desired.

Theorem 5.32 If R is a pre-elegant Reedy category, then X ∈ PSh(R) is Reedy monic if and only if it sends pushouts of lowering spans to pullbacks.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

49

Proof One direction is Lemma 5.31. For the other, suppose X sends pushouts of lowering spans to pullbacks. By Lemma 5.24, it suffices to show X has unique EZ decompositions. Let (e₀, x₀) and (e₁, x₁) be EZ decompositions of the same element. We have an induced element as shown:

![img-31.jpeg](img-31.jpeg)

By non-degeneracy of x₀ and x₁, the maps ι₀ and ι₁ must be isomorphisms, so (e₀, x₀) and (e₁, x₁) are isomorphic.

Remark 5.33 A corollary of the previous theorem is that a pre-elegant Reedy category R is elegant if and only if all presheaves on R are Reedy monic. Bergner and Rezk [BR13, Proposition 3.8] show that this bi-implication actually holds for any Reedy category. That is, if all presheaves on R are Reedy monic, then R is necessarily pre-elegant (and thus elegant).

### 5.3 Relative elegance

Now we come to our central definition, elegance of a category relative to a full subcategory.

Definition 5.34 We say that a pre-elegant Reedy category R is elegant relative to a fully faithful functor i: C → R if the nerve Nᵢ := i*&: R → PSh(C) preserves pushouts of lowering spans. We also say that i is relatively elegant with the same meaning.

Remark 5.35 As pushouts in PSh(C) are computed pointwise, i is relatively elegant if and only if R(ia, −): R → Set preserves lowering pushouts for all a ∈ C.

Remark 5.36 A Reedy category is elegant if and only if it is elegant relative to the identity functor, in which case the nerve is simply the Yoneda embedding. At the other extreme, any pre-elegant Reedy category is elegant relative to the unique functor 0 → R.

Lemma 5.37 If R is elegant relative to i: C → R, then Nᵢ: R → PSh(C) sends lowering maps to epimorphisms.

Proof By Lemma 5.29, any e ∈ R⁻ fits in the pushout square

![img-32.jpeg](img-32.jpeg)

2025/10/16 00:43

50

E. Cavallo and C. Sattler

which is then preserved by $N_i$.

Corollary 5.38 If $\mathbf{R}$ is elegant relative to $i: \mathbf{C} \to \mathbf{R}$, then objects in the image of $i$ are $\mathbf{R}^-$-projective: given a lowering map $e: r \to s$ and $f: ia \to s$, there exists a lift as below.

![img-33.jpeg](img-33.jpeg)

Proof By Lemma 5.37, $N_i e: N_i r \to N_i s$ is epic; this means exactly post-composition with $e$ is a surjective map $\mathbf{R}(ia, r) \to \mathbf{R}(ia, s)$.

Remark 5.39 As a special case of the corollary above, we recover the fact that lowering maps in elegant Reedy categories are split epimorphisms [BR13, Proposition 3.8]. Split epis are lowering maps in any Reedy category (Corollary 2.15), so in the elegant case they coincide. It is not generally the case that the lowering maps in a Reedy category $\mathbf{R}$ elegant relative to some $i$ are exactly those sent to epimorphisms by $N_i$: consider that $\mathbf{R}$ is always elegant relative to $\mathbf{0} \to \mathbf{R}$.

On the basis of Remark 5.35, we can identify the maximal subcategory relative to which a pre-elegant Reedy category $\mathbf{R}$ is elegant.

Definition 5.40 Let $\mathbf{R}$ be a pre-elegant Reedy category. We define its elegant core $\mathbf{R}^{\mathrm{ec}}$ to be the full subcategory of $\mathbf{R}$ consisting of objects $r$ such that $\mathbf{R}(r, -)$ preserves lowering pushouts.

Proposition 5.41 An fully faithful functor $i: \mathbf{C} \to \mathbf{R}$ into a pre-elegant Reedy category is relatively elegant exactly if it factors through the inclusion $\mathbf{R}^{\mathrm{ec}} \to \mathbf{R}$.

We can give another characterization of relative elegance in terms of the right Kan extension $i_*: \mathrm{PSh}(\mathbf{C}) \to \mathrm{PSh}(\mathbf{R})$:

Lemma 5.42 Let $\mathbf{R}$ be a pre-elegant Reedy category. Then $i: \mathbf{C} \to \mathbf{R}$ is relatively elegant if and only if $i_* X \in \mathrm{PSh}(\mathbf{R})$ is Reedy monic for every $X \in \mathrm{PSh}(\mathbf{C})$.

Proof By definition, $i: \mathbf{C} \to \mathbf{R}$ is relatively elegant exactly if $N_i = i^* \not\cong$ preserves lowering pushouts. Testing pushouts by mapping out of them, this holds exactly if $\mathrm{PSh}(\mathbf{C})(i^* \not\cong -, X)$ sends lowering pushouts to pullbacks for every $X \in \mathrm{PSh}(\mathbf{C})$. Using the natural isomorphism

$$\mathrm{PSh}(\mathbf{C})(i^* \not\cong -, X) \cong \mathrm{PSh}(\mathbf{R})(i \not\cong -, i_* X) \cong i_* X,$$

this rewrites to $i_* X$ sending lowering pushouts to pullbacks.

This property of presheaves extends to morphisms as follows.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

51

Definition 5.43 A map $m: X \to Y$ in PSh(R) reflects degeneracy if has the right lifting property against lowering maps $e: \not\perp r \xrightarrow{\sim} \not\perp s$.

This means that for any $x \in X_r$, if $m_r(x)$ factors through some $e: \not\perp r \xrightarrow{\sim} \not\perp s$, then $x$ also factors through $e$.

Lemma 5.44 Let $\mathbf{R}$ be a Reedy category, let $Y \in \mathrm{PSh}(\mathbf{R})$ be Reedy monic, and let $m: X \mapsto Y$ be a degeneracy-reflecting monomorphism. Then $m$ is Reedy monic.

Proof By Proposition 5.23, it suffices to show, for any $r \in \mathbf{R}$, that the pushout gap map in the naturality square

$$\begin{array}{c} L_r X_- \to X_r \\ \downarrow \qquad \qquad \downarrow \\ L_r Y_- \to Y_r \end{array}$$

is monic. The bottom and right maps are monic by assumption. Because $m$ reflects degeneracy, the square is a weak pullback, i.e., the pullback gap map is surjective. This means that the pushout gap map, seen as an object over $Y_r$, is the union of the subobjects given by the bottom and right maps.

Corollary 5.45 If $i: \mathbf{C} \to \mathbf{R}$ is relatively elegant, then $i_*m$ is Reedy monic for every $m: X \mapsto Y$ in PSh(C).

Proof By Lemma 5.44, it suffices to show that $i_*m$ reflects degeneracy. For any $e: r \xrightarrow{\sim} s$, $N_{\ell}e$ is epic by Lemma 5.37, so has left lifting against monos. By transposition, $e$ has left lifting against $i_*m$.

In any presheaf category, all monomorphisms can be presented as cell complexes (transfinite composites of cobase changes of coproducts) of monomorphisms whose codomains are quotients of representables [Cis06, Proposition 1.2.27]. With Corollary 5.45, we can give an alternative—not necessarily comparable—set of generators in terms of the boundary inclusions in $\mathbf{R}$.

Theorem 5.46 If $i: \mathbf{C} \to \mathbf{R}$ is relatively elegant, then every monomorphism in PSh(C) is a cell complex of maps of the form $i^*(\mathfrak{o}^n\mathbf{R} \circledast_{\mathbf{R}[n]^{\oplus}}(\not\perp r/H))$ where $r \in \mathbf{R}$ and $H \leq \mathrm{Aut}_{\mathbf{R}}(r)$.

Proof Let $m: X \mapsto Y$ in PSh(C). By Corollary 5.16, $i_*m$ has a cellular presentation by maps of the form $\mathfrak{o}^n\mathbf{R} \circledast_{\mathbf{R}[n]^{\oplus}} \widehat{\ell}_n(i_*m)$; by Corollary 5.45, each $\widehat{\ell}_n(i_*m)$ is monic in PSh(R[n]). In PSh(R[n]), any monomorphism is a cell complex of maps of the form $0 \mapsto \not\perp r/H$ for some $r \in \mathbf{R}[n]$ and $H \leq \mathrm{Aut}_{\mathbf{R}}(r)$, because PSh(R[n]) is Boolean and any R[n]-set decomposes as a coproduct of orbits. By [RV14, Lemma 5.7], it follows that $i_*m$ is a cell complex of maps $\mathfrak{o}^n\mathbf{R} \circledast_{\mathbf{R}[n]^{\oplus}}(0 \mapsto \not\perp r/H)$. Finally, $i^*$ preserves colimits and thus cell complexes.

2025/10/16 00:43

52

E. Cavallo and C. Sattler

Finally, we exploit the fact that $i^*$ preserves the operations of saturation by monomorphisms to transfer the induction principle on the Reedy monic presheaves of PSh(R) given by Theorem 5.27 to PSh(C).

Theorem 5.47 Let $\mathbf{R}$ be elegant relative to $i: \mathbf{C} \to \mathbf{R}$. Let $\mathcal{P} \subseteq \mathrm{PSh}(\mathbf{C})$ be a class of objects such that

- for any $r \in \mathbf{R}$ and $H \leq \operatorname{Aut}_{\mathbf{R}}(r)$, we have $N_i r / N_i H \in \mathcal{P}$;
- $\mathcal{P}$ is saturated by monomorphisms.

Then $\mathcal{P}$ contains every presheaf in PSh(C).

Proof As a left and right adjoint, $i^*$ preserves colimits and monomorphisms. The class $(i^*)^{-1}\mathcal{P}$ of $X \in \mathrm{PSh}(\mathbf{R})$ such that $i^*X \in \mathcal{P}$ is thus saturated by monomorphisms. By our first assumption and the fact that $i^*$ preserves colimits, we have $\mathscr{L}r / H \in (i^*)^{-1}\mathcal{P}$ for every $r \in \mathbf{R}$ and $H \leq \operatorname{Aut}_{\mathbf{R}}(r)$. By Theorem 5.27 and Lemma 5.42, we thus have $i_*X \in (i^*)^{-1}\mathcal{P}$ for all $X \in \mathrm{PSh}(\mathbf{C})$. Hence $X \cong i^*i_*X \in \mathcal{P}$ for all $X \in \mathrm{PSh}(\mathbf{C})$. ■

## 6 Reedy structures on categories of finite algebras

### 6.1 Finite algebras

Per Section 4, $\square_\nu$ and its idempotent completion can be regarded as full subcategories of the category $\mathbf{SLat}_{\mathrm{fin}}$ of finite semilattices. Any category of finite algebras of a Lawvere theory carries a natural Reedy structure: the degree of an object is its cardinality, and the lowering and raising maps are given by the (surjective, mono) factorization system. Here we observe that this Reedy structure is pre-elegant and characterize its elegant core in the case where free finitely-generated algebras are finite. As a corollary, the embedding $\square_\nu \to \mathbf{SLat}_{\mathrm{fin}}$ and its restriction $\square_\nu \to \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ to inhabited algebras are relatively elegant.

For this section, we fix a Lawvere theory $\mathbf{T}$. We recall a few basic properties of its category of algebras.

Proposition 6.1 (ARV10, Corollary 3.5) A morphism $f$ in $\operatorname{Alg}(\mathbf{T})$ is regular epic if and only $Uf$ is surjective. ■

Proposition 6.2 (ARV10, Corollary 3.7) Any morphism in $\operatorname{Alg}(\mathbf{T})$ factors as a regular epi followed by a mono. ■

Write $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}} \to$ and $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{\mathrm{inh}}$ for the full subcategories of $\operatorname{Alg}(\mathbf{T})$ consisting of algebras with finite and finite inhabited underlying sets respectively. When we write $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{(\mathrm{inh})}$ below, the relevant statement or proof applies to both of these.

Corollary 6.3 The (surjective, mono) factorization system restricts to a Reedy structure on $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{(\mathrm{inh})}$ with degree map given by cardinality. ■

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

53

As any category of algebras has limits and colimits [ARV10, Proposition 1.21, Theorem 4.5], $\operatorname{Alg}(\mathbf{T})$ has in particular pushouts of spans of surjections.

Corollary 6.4 The Reedy structure on $\operatorname{Alg}(\mathbf{T})_{\mathrm{fin}}^{(\mathrm{inh})}$ is pre-elegant.

Proof The pushout of a span of surjections has cardinality bounded by those of the objects in the span, as surjections are left maps and thus closed under cobase change. ■

Recall that the forgetful functor $U$ preserves limits. While $U$ does not generally preserve colimits, we can show that it preserves pushouts of surjective spans using the technology of sifted colimits.

Definition 6.5 A small category $\mathbf{D}$ is

- filtered if $\operatorname{colim}_{\mathbf{D}}: [\mathbf{D}, \mathbf{Set}] \to \mathbf{Set}$ commutes with finite limits;
- sifted if $\operatorname{colim}_{\mathbf{D}}: [\mathbf{D}, \mathbf{Set}] \to \mathbf{Set}$ commutes with finite products.

A filtered (sifted) colimit is a colimit over a filtered (sifted) category.

Recall that a reflexive coequalizer is a coequalizer of maps $f_0, f_1: A \to B$ with a mutual section, that is, some $d: B \to A$ such that $f_0 d = f_1 d = \operatorname{id}$. Reflexive coequalizers are sifted (but not filtered) colimits [ARV10, Remark 3.2].

Lemma 6.6 Let $F: \mathbf{C} \to \mathbf{D}$ be a functor between regular categories preserving finite limits and sifted colimits. Then $F$ preserves pushouts of regular epi spans.

Proof Let a span $B_0 \stackrel{e_0}{\leftarrow} A \stackrel{e_1}{\twoheadrightarrow} B_1$ in $\mathbf{C}$ be given. We compute the following reflexive coequalizer:

$$A \times_{B_0} A \times_{B_1} A \xrightarrow[\pi_2]{\pi_0} A \xrightarrow{e} B$$

It is straightforward to check, using the characterizations of $e_0, e_1$ as the coequalizers of their kernel pairs, that we have induced maps $B_0 \twoheadrightarrow B \leftrightarrow B_1$ exhibiting $B$ as the pushout of our span. As $F$ preserves the diagram above, it preserves this pushout. ■

Corollary 6.7 $U: \operatorname{Alg}(\mathbf{T}) \to \mathbf{Set}$ preserves pushouts of surjective spans.

Proof $U$ preserves limits and sifted colimits [ARV10, Proposition 2.5]. ■

We now assume that any $\mathbf{T}$-algebra free on a finite set has a finite underlying set. In this case, the elegant core coincides with the class of perfectly presentable (also called strongly finitely presentable) algebras.

Definition 6.8 (ARV10, Definition 5.3) An object $A$ of a category $\mathbf{C}$ is

- finitely presentable if $\mathbf{C}(A, -): \mathbf{C} \to \mathbf{Set}$ preserves filtered colimits;

2025/10/16 00:43

54

E. Cavallo and C. Sattler

- • perfectly presentable if $\mathbf{C}(A, -): \mathbf{C} \rightarrow \mathbf{Set}$ preserves sifted colimits.

**Proposition 6.9** (*ARV10, Corollary 5.16 and Proposition 11.28*) Let $A \in \text{Alg}(\mathbf{T})$. The following are equivalent:

- • $A$ is perfectly presentable;
- • $A$ is finitely presentable and regular projective;
- • $A$ is a retract of a finitely-generated free algebra.

**Theorem 6.10** Suppose that every finitely-generated free algebra in $\text{Alg}(\mathbf{T})$ has a finite underlying set. Then the elegant core of $\text{Alg}(\mathbf{T})_{\text{fin}}^{(\text{inh})}$ is the subcategory of objects perfectly presentable in $\text{Alg}(\mathbf{T})$.

**Proof** Suppose $A \in \text{Alg}(\mathbf{T})_{\text{fin}}^{(\text{inh})}$ is in the elegant core of the Reedy structure. By assumption, the free algebra $FUA$ belongs to $\text{Alg}(\mathbf{T})_{\text{fin}}^{(\text{inh})}$, and the counit $\varepsilon_A: FUA \rightarrow A$ is clearly surjective. Then by Corollary 5.38, we have a lift

![img-34.jpeg](img-34.jpeg)

exhibiting $A$ a retract of a free algebra. Thus $A$ is perfectly presentable. Conversely, if $A$ is perfectly presentable, then $\text{Alg}(\mathbf{T})(A, -): \text{Alg}(\mathbf{T}) \rightarrow \mathbf{Set}$ preserves finite limits and sifted colimits, so preserves pushouts of lowering spans by Lemma 6.6.

## 6.2 Semilattice cubes

Applying the preceding results, we have a (surjective, mono) Reedy structure on $\mathbf{SLat}_{\text{fin}}^{(\text{inh})}$. We can give a concrete description of its elegant core.

**Lemma 6.11** A semilattice $A \in \mathbf{SLat}_{\text{fin}}^{(\text{inh})}$ is in the elegant core of the (surjective, mono) Reedy structure if and only if $1 \star A$ is a distributive lattice.

**Proof** By Theorem 6.10, the elegant core consists of the perfectly presentable objects in $\mathbf{SLat}$. By Proposition 6.9, these are the finite regular projectives in $\mathbf{SLat}$. These are characterized as above by Propositions 4.41 and 4.42.

**Theorem 6.12** The inclusion $i: \overline{\square}_v \rightarrow \mathbf{SLat}_{\text{fin}}^{(\text{inh})}$ is relatively elegant.

**Proof** If $A \in \mathbf{SLat}_{\text{fin}}^{(\text{inh})}$ is a distributive lattice, then $1 \star A$ is a distributive lattice as well, so $A$ is in the elegant core of $\mathbf{SLat}_{\text{fin}}^{(\text{inh})}$.

**Remark 6.13** The subcategory $\mathbf{SLat}_{\text{fin}}^{\perp}$ of $\mathbf{SLat}_{\text{fin}}^{(\text{inh})}$ consisting of finite semilattices with a minimum element is closed under Reedy factorizations and lowering pushouts, so

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

55

$\overline{\square}_{\vee} \to \mathbf{SLat}_{\mathrm{fin}}^{\perp}$ is also relatively elegant. This embedding gives a more parsimonious set of generators, but $\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ suffices for our purposes.

## 7 Equivalences and equalities

### 7.1 Equivalence with the Kan–Quillen model structure

Returning to the candidate Quillen equivalence $\blacktriangle_{!} \dashv \blacktriangle^{*}$, it remains to show that its counit is valued in weak equivalences. We first note that the collection of those $X \in \mathrm{PSh}(\overline{\square}_{\vee})$ for which $\varepsilon_{X}: \blacktriangle_{!} \blacktriangle^{*} X \to X$ is a weak equivalence is saturated by monomorphisms.

Proposition 7.1 (Cis06, Remarque 1.1.13) Let $F: \mathbf{E} \to \mathbf{F}$ be a mono- and colimit-preserving functor between cocomplete categories. If $\mathcal{P} \subseteq \mathbf{F}$ is saturated by monos, then the class $F^{-1}(\mathcal{P})$ of objects whose image by $F$ is in $\mathcal{P}$ is saturated by monos.

Proposition 7.2 If $\mathbf{M}$ has monos as cofibrations, then its class of weak equivalences is saturated by monos as a class of objects of $\mathbf{M}^{\rightarrow}$.

Proof This is proven by Cisinski [Cis06, Remarque 1.4.16] for localizers [Cis06, Définition 1.4.1]; the class of weak equivalences in a model category with monos as cofibrations is always a localizer.

Corollary 7.3 Let $\mathbf{E}$ be a cocomplete category, $\mathbf{N}$ be a model category with monos as cofibrations, and $F, G: \mathbf{E} \to \mathbf{N}$ be mono- and colimit-preserving functors. For any natural transformation $h: F \to G$, the class of objects $X \in \mathbf{E}$ such that $h_{X}: FX \to GX$ is a weak equivalence is saturated by monos.

Proof By Propositions 7.1 and 7.2, regarding $h$ as a functor $\mathbf{E} \to \mathbf{N}^{\rightarrow}$.

In particular, any natural transformation $h: F \to G$ of left Quillen adjoints $F, G: \mathbf{M} \to \mathbf{N}$ between model categories with monos as cofibrations satisfies the hypotheses of Corollary 7.3. In light of this, we only need to check that $\varepsilon$ is a weak equivalence at generating presheaves.

Lemma 7.4 Let $A \in \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ and $H \leq \operatorname{Aut}_{\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}}(A)$ be given. Then $N_{i}A / N_{i}H$ is weakly contractible.

Proof Per Corollary 4.51, it suffices to show that this object is a homotopy retract of 1. We have a semilattice morphism $\uparrow: [1] \times A \to A$ sending $(0, a) \mapsto a$ and $(1, a) \mapsto \top$.

2025/10/16 00:43

56

E. Cavallo and C. Sattler

Any automorphism $g \in H$ preserves maximum elements, so we have a diagram like so:

$$\begin{array}{c} [1] \times A \xrightarrow{\uparrow} A \\ [1] \times g \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \times A \xrightarrow{\uparrow} A \end{array}$$

We thus obtain a contracting homotopy $\mathbb{I} \times (N_i A / N_i H) \to (N_i A / N_i H)$, using that $N_i([1] \times A) \cong \mathbb{I} \times N_i A$ and that $\mathbb{I} \times (-)$ commutes with colimits.

Lemma 7.5 The counit map $\varepsilon_X: \blacktriangle_! \blacktriangle^* X \to X$ is a weak equivalence for every $X \in \mathrm{PSh}(\overline{\square}_V)$.

Proof Recall that both $\blacktriangle_!$ and $\blacktriangle^*$ are left Quillen (Corollary 4.53 and Lemma 4.54). By Theorem 5.47 and Corollary 7.3, it suffices to show that $\varepsilon_X: \blacktriangle_! \blacktriangle^* X \to X$ is a weak equivalence whenever $X$ is an automorphism quotient of an object in the image of $N_i$. In this case $X$ is weakly contractible by Lemma 7.4. As $\blacktriangle_! \blacktriangle^*$ preserves the terminal object, it preserves weak contractibility by Ken Brown's lemma; thus $\blacktriangle_! \blacktriangle^* X$ is weakly contractible and so $\varepsilon_X$ is a weak equivalence by 2-out-of-3.

Theorem 7.6 $\blacktriangle_!: \widehat{\Delta}^{\mathrm{kq}} \xleftarrow{\longleftrightarrow} \widehat{\square}_V^{\mathrm{ty}}: \blacktriangle^*$ is a Quillen equivalence.

Proof By Corollary 4.53 and Lemmas 4.55 and 7.5.

Corollary 7.7 $\blacktriangle^*: \widehat{\square}_V^{\mathrm{ty}} \xleftarrow{\longleftrightarrow} \widehat{\Delta}^{\mathrm{kq}}: \blacktriangle_*$ is a Quillen equivalence.

Proof Write $\eta'$ and $\varepsilon'$ for the unit and counit of this adjunction. The counit is an isomorphism, so trivially valued in weak equivalences. To check the derived unit, let $X \in \mathrm{PSh}(\square_V)$ and let $m: \blacktriangle^* X \hookrightarrow (\blacktriangle^* X)^{\mathrm{fib}}$ be a fibrant replacement. We have the following naturality square:

$$\begin{array}{c} \blacktriangle_! \blacktriangle^* X \xrightarrow[\cong]{\blacktriangle_! \blacktriangle^* \eta_X'} \blacktriangle_! \blacktriangle^* \blacktriangle_* \blacktriangle^* X \xrightarrow{\blacktriangle_! \blacktriangle^* \blacktriangle_* m} \blacktriangle_! \blacktriangle^* \blacktriangle_* (\blacktriangle^* X)^{\mathrm{fib}} \\ \varepsilon_X \downarrow_! \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \xrightarrow{\eta_X'} \blacktriangle_* \blacktriangle^* X \xrightarrow{\blacktriangle_* m} \blacktriangle_* (\blacktriangle^* X)^{\mathrm{fib}}. \end{array}$$

It follows by 2-out-of-3 that the bottom composite is a weak equivalence.

Theorem 7.8 T: $\widehat{\square}_V^{\mathrm{ty}} \xleftarrow{\longleftrightarrow} \widehat{\Delta}^{\mathrm{kq}}: N_{\square}$ is a Quillen equivalence.

Proof By the decomposition $T \cong \blacktriangle^* \blacksquare$: (Lemma 4.48).

In particular, both $\widehat{\square}_V^{\mathrm{ty}}$ and $\widehat{\square}_V^{\mathrm{ty}}$ present $\infty$-Gpd.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

57

## 7.2 Equality with the test model structure

It is worth remarking that there is a model structure on PSh(□_v) already known to present ∞-Gpd, namely its test model structure. Constructed by Cisinski [Cis06] based on Grothendieck's theory of test categories [Gro83], a test model structure exists on the category of presheaves PSh(C) over any local test category C. If C is moreover a test category, then this model structure is Quillen equivalent to Δ̂^kq.

Buchholtz and Morehouse observe that □_v, among various other cube categories, is a test category [BM17, Corollary 3]. Thus it supports a model structure presenting ∞-Gpd. However, it has not been established whether this model structure is constructive or compatible with a model of homotopy type theory. Cisinski [Cis14] has shown that the test model structure on an elegant strict Reedy local test category is type-theoretic in the sense of Shulman [Shu19, Definition 6.1], but the strictness requirement prevents application of this result to any cube category with permutations (or any non-Reedy category).

By virtue of the Quillen equivalences to Δ̂^kq already established, we know that □̄^ty and □̄̄^ty are Quillen equivalent to the test model structures on their respective base categories. Here we check that they are in fact identical, adapting an argument of Streicher and Weinberger [SW21, §5].

We must begin by recalling the main definitions of test category theory. For more detail, we refer the reader to Maltsiniotis [Mal05], Cisinski [Cis06], or Jardine [Jar06]. The foundation of test category theory that we can relate presheaves on an arbitrary base category C with simplicial sets by way of the category of small categories, Cat. We write N_Δ: Cat → PSh(Δ) for the nerve of the inclusion Δ → Cat.

Definition 7.9 Given a small category C, write i_C: C → Cat for the slice category functor a ↦ C/a. We have an induced nerve functor i_C*: Cat → PSh(C). As Cat is cocomplete, this functor has a left adjoint PSh(C) → Cat, for which we also write i_C.

The composite N_Δi_C: PSh(C) → PSh(Δ) is the means by which we can inherit a model structure on PSh(C) from Δ̂^kq under appropriate conditions.

Remark 7.10 The definitions and results of Cisinski that we cite below are typically parameterized by an arbitrary basic localizer [Cis06, Définition 3.3.2], a class of functors to be regarded as the weak equivalences in Cat. We always instantiate with the minimal basic localizer W_∞: the class of functors f: C → D such that N_Δf: N_ΔC → N_ΔD is a weak equivalence of Δ̂^kq [Cis06, Corollaire 4.2.19].

Definition 7.11 (Cis06, §3.3.3 and Définition 4.1.3) We say X ∈ PSh(C) is aspheric if N_Δi_C X ∈ PSh(Δ) is weakly contractible in Δ̂^kq.

Definition 7.12 (Cis06, Définitions 4.1.8 and 4.1.12) A small category C is

Maltsiniotis [Mal09] also observed that a cube category with one connection is a strict test category, but a different one: the subcategory of □_v generated by faces, degeneracies, and connections, i.e., not including diagonals and permutations.

2025/10/16 00:43

58

E. Cavallo and C. Sattler

- a weak test category if $i_{\mathbf{C}}^{*}\mathbf{D}$ is aspheric for every $\mathbf{D}$ with a terminal object;
- a local test category if $\mathbf{C}/a$ is a weak test category for all $a \in \mathbf{C}$;
- a test category if it is both a weak and local test category.

Proposition 7.13 (Cis06, Corollaire 4.2.18) Let $\mathbf{C}$ be a local test category. There is a model structure on $\mathrm{PSh}(\mathbf{C})$ in which

- the cofibrations are the monomorphisms;
- the weak equivalences are the maps sent by $N_{\Delta}i_{\mathbf{C}}$ to a weak equivalence of $\widehat{\Delta}^{\mathrm{kq}}$.

We write $\widehat{\mathbf{C}}^{\mathrm{test}}$ for this model category.

Remark 7.14 The test model structure $\widehat{\Delta}^{\mathrm{test}}$ coincides with $\widehat{\Delta}^{\mathrm{kq}}$. A proof is contained in the proof of [Cis06, Corollaire 4.2.19]: the class of weak equivalences of $\widehat{\Delta}^{\mathrm{test}}$ is by definition the preimage $N_{\Delta}^{-1}\mathcal{W}_{\infty}$, which is the minimal test $\Delta$-localizer by Théorème 4.2.15, and said localizer is the class of weak equivalences of $\widehat{\Delta}^{\mathrm{kq}}$ by Corollaire 2.1.21 and Proposition 3.4.25.

Note that whereas cubical-type model structures come with explicit characterizations of their cofibrations and fibrations (or rather generating trivial cofibrations), the test model structure comes with explicit descriptions of its cofibrations and weak equivalences. In general, $\widehat{\mathbf{C}}^{\mathrm{test}}$ is Quillen equivalent to a slice of $\widehat{\Delta}^{\mathrm{kq}}$, namely $\widehat{\Delta}^{\mathrm{kq}}/N_{\Delta}\mathbf{C}$ [Cis06, Corollaire 4.4.20]. When $\mathbf{C}$ is a test category, $N_{\Delta}\mathbf{C}$ is weakly contractible, and so we have an equivalence to $\widehat{\Delta}^{\mathrm{kq}}$ itself.

We recall the argument used by Buchholtz and Morehouse [BM17, Theorem 1] to show that $\square_{\vee}$ is a test category—actually a strict test category.

Definition 7.15 (Cis06, §4.3.1, Proposition 4.3.2, §4.3.3) We say a category $\mathbf{C}$ is totally aspheric if it is non-empty and $\nless a \times \nless b$ is aspheric for every $a, b \in \mathbf{C}$. A test category that is totally aspheric is called a strict test category.

Any representable is aspheric: the category $i_{\mathbf{C}}(\nless a)$ has a terminal object, thus a natural transformation from its identity functor to a constant functor, and this induces a contracting homotopy on $N_{\Delta}i_{\mathbf{C}}(\nless a)$. Thus, any category with binary products is totally aspheric.

The following result originates in [Gro83, Section 44(c)] and is invoked in [BM17] for a broad class of cube categories.

Proposition 7.16 (Cis06, Proposition 4.3.4) Let $\mathbf{C}$ be a totally aspheric category. If $\mathrm{PSh}(\mathbf{C})$ contains an aspheric presheaf $I$ with disjoint maps $e_0, e_1: 1 \to I$, then $\mathbf{C}$ is a strict test category.

In particular, both $\square_{\vee}$ and $\overline{\square}_{\vee}$ are strict test categories. To relate their test model structures to $\widehat{\Delta}^{\mathrm{kq}}$, we recall the notion of aspheric functor.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

59

Definition 7.17 (Cis06, §3.3.3, Proposition 4.2.23(a⇔b'') A functor u: C → D is aspheric if for every d ∈ D, the presheaf u*(&d) is aspheric.

An aspheric functor u: C → D between test categories induces a Quillen equivalence u* + u* between their test model structures [Cis06, Proposition 4.2.24]. For our purposes, the more relevant property is the following immediate consequence.

Proposition 7.18 (Cis06, Proposition 4.2.23(d)) Let u: C → D be an aspheric functor between two test categories. Then a map f in PSh(D) is a weak equivalence in D̅test if and only if u*f is a weak equivalence in C̅test.

Lemma 7.19 Any idempotent completion i: C → C̅ is aspheric.

Proof Any A ∈ C̅ is a retract of ia for some a ∈ C. Then i*& A is likewise a retract of i*& (ia) ≅ & a, thus aspheric by Corollary 4.51.

Lemma 7.20 ▲: Δ → D̅⊙ is aspheric.

Proof For any [1]ⁿ ∈ D̅⊙, we have ▲*& [1]ⁿ ≅ (Δ¹)ⁿ. As Δ is a strict test category [Mal05, Proposition 1.6.14], any finite product of representables in PSh(Δ) is aspheric [Cis06, Proposition 4.3.2(b)].

Lemma 7.21 A map f in PSh(D̅⊙) is a weak equivalence in D̅⊙⊙ if and only if ▲*f is a weak equivalence in Δ̅ᵏ.

Proof Any left Quillen equivalence both preserves (Ken Brown's lemma) and reflects [Hov99, Corollary 1.3.16] weak equivalences between cofibrant objects, so this follows from Corollary 7.7.

Theorem 7.22 The model structures D̅⊙test and D̅⊙⊙ are identical.

Proof As they have the same cofibrations, it suffices to show they have the same weak equivalences. This follows from Proposition 7.18 and Lemma 7.20 (together with Remark 7.14) and Lemma 7.21.

Corollary 7.23 The model structures D̅⊙test and D̅⊙⊙ are identical.

Proof Again, it suffices to show they have the same weak equivalences. By Proposition 7.18 and Lemma 7.19, a map f is a weak equivalence in D̅⊙test if and only if ■f is a weak equivalence in D̅⊙test. Likewise, f is a weak equivalence in D̅⊙⊙ if and only if ■f is a weak equivalence in D̅⊙⊙.

These results can also be read as characterizations of the fibrations in the test model structures:

2025/10/16 00:43

60

E. Cavallo and C. Sattler

Corollary 7.24 The fibrations in $\overline{\overline{\square}}_{\vee}^{\mathrm{test}}$ and $\overline{\square}_{\vee}^{\mathrm{test}}$ are those maps lifting against $\delta_k \widehat{\times} m$ for all $k \in \{0, 1\}$ and $m: A \mapsto B$.

## A Negative results

Here we collect a pair of negative results concerning the existence of (relative) Reedy structures on (idempotent completions of) cube categories. In Appendix A.1, we check that $\square_{\vee}$ and $\overline{\square}_{\vee}$ are not Reedy categories, motivating this paper's approach. Appendix A.2 concerns the limits of relative elegance: we show that the Dedekind cube category does not embed elegantly in any Reedy category.

### A.1 Semilattice cubes

The non-existence of a Reedy structure on $\square_{\vee}$ is easily verified: every Reedy category is idempotent complete [Bor94, Proposition 6.5.9], but we have seen in Section 4.3 that $\square_{\vee}$ is not. The map $(x, y) \mapsto (x, x \vee y): [1]^2 \to [1]^2$ is a simple example of an idempotent with no splitting in $\square_{\vee}$.

It is therefore more appropriate to ask if the cube category's idempotent completion $\overline{\square}_{\vee}$, which we have characterized as the full subcategory of SLat consisting of finite inhabited distributive lattices (Definition 4.39), is Reedy. If this were so, we could simply study PSh($\square_{\vee}$) by way of the equivalent PSh($\overline{\square}_{\vee}$). However, this is not the case:

Proposition A.1 There is no Reedy structure on $\overline{\square}_{\vee}$.

Proof We consider the following morphism $u: [1]^3 \to [1]^3$:

$$u(x, y, z) := (x \vee y, y \vee z, z \vee x).$$

For intuition, note that the image of $u$ computed in SLat is the non-distributive diamond lattice $\mathfrak{M}_3$.

Suppose that we do have a Reedy structure on $\overline{\square}_{\vee}$. The unique map $[1]^2 \to 1$ is split epic and thus a lowering map (Corollary 2.15). Every raising map must have the right lifting property against this map, so every raising map is monic.⁸ Take a Reedy factorization of $u$:

![img-35.jpeg](img-35.jpeg)

$L$ is a sub-semilattice of $[1]^3$ that forms a distributive lattice and contains the image of $u$. Note that $\vee, \bot$, and $\top$ are computed in $L$ as in $[1]^3$, but $\wedge$ may not be; we write $\wedge_L$ for the meet in $L$. We show that in fact $L = [1]^3$.

⁸If we only want to show $\overline{\square}_{\vee}$ is not elegant Reedy, we are already done, as observed in [Cam23, Theorem 8.12(2)]: if $\overline{\square}_{\vee}$ were elegant we would have a (split epi, mono) factorization of $u$, which would necessarily be preserved by the inclusion $\overline{\square}_{\vee} \to \mathbf{SLat}$, but $u$'s (split epi, mono) factorization in SLat is $\mathfrak{M}_3$.

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

61

Consider the set $S := \{011, 101, 110\} \subseteq L \subseteq [1]^3$. Let $v, v', v''$ be any pairwise distinct elements of $S$ and note that we have

$$(v \wedge_L v') \vee (v \wedge_L v'') = v \wedge_L (v' \vee v'') = v \wedge_L \top = v.$$

This implies the following.

- (a) $v \wedge_L v' \neq v \wedge_L v''$: otherwise we have $(v \wedge_L v') \vee (v \wedge_L v'') = v \wedge_L v''$ and thus $v = v \wedge_L v''$, but $v$ and $v''$ are incomparable.
- (b) $v \wedge_L v' \neq \bot$: otherwise we again have $(v \wedge_L v') \vee (v \wedge_L v'') = v \wedge_L v''$.

Thus the meets $011 \wedge_L 101, 011 \wedge_L 110$, and $011 \wedge_L 110$ are pairwise distinct and lie outside the image of $u$, which by a cardinality argument implies that $L$ is the whole of $[1]^3$.

The lowering map $f$ of our supposed factorization must then be $u$ itself; it remains to show that $u$ cannot be a lowering map. Consider the semilattice morphism $t: [1]^3 \to [2]$ defined by $t(x, y, z) := x \vee 2y \vee 2z$. We have the following commutative diagram in $\overline{\Omega}_v$, where $d_1$ and $s_1$ are the simplex face and degeneracy maps from Definition 2.22:

$$\begin{array}{c} [1]^3 \xrightarrow{t} [2] \xrightarrow{s_1} [1] \\ u \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1]^3 \xrightarrow{t} [2]. \end{array}$$

The face map $d_1$ is split monic and therefore a raising map. If $u$ were a lowering map, this square would have a diagonal lift. But as $t$ is surjective, there can be no diagonal $[1]^3 \to [1]$ making the lower triangle commute.

### A.2 Dedekind cubes

As mentioned in the introduction, it is an open question whether the cubical-type model structure for presheaves on the Dedekind cube category $\overline{\Omega}_{\wedge V}$ is equivalent to the Kan-Quillen model structure $\overline{\Delta}^{\mathrm{aq}}$; see Streicher and Weinberger [SW21] for further discussion. In this appendix, we show that $\overline{\Omega}_{\wedge V}$ supports no relatively elegant embedding in a Reedy category, thus that our argument for $\overline{\Omega}_V$ admits no naive adaptation to the two-connection case.

Definition A.2 The Dedekind cube category $\overline{\Omega}_{\wedge V}$ is the Lawvere theory of bounded distributive lattices.

$\overline{\Omega}_{\wedge V}$ admits an alternative description arising from the duality between finite bounded distributive lattices and finite posets [Wra93], analogous to the description of $\overline{\Omega}_V$ as a full subcategory of SLat:

Proposition A.3 $\overline{\Omega}_{\wedge V}$ is equivalent to the full subcategory of Pos consisting of posets of the form $[1]^n$ for $n \in \mathbb{N}$.

We will only need this latter description.

2025/10/16 00:43

62

E. Cavallo and C. Sattler

The Dedekind cube category attracted attention [Spi16; Sat19; KV20; SW21; HR22] in the HoTT community following Cohen et al.'s interpretation of HoTT in De Morgan cubical sets [CCHM15]. As Orton and Pitts note [OP18, Remark 3.2], this interpretation does not require all the structure of De Morgan cubes; in particular, it can be repeated with $\Box_{\delta\nu}$. The name "Dedekind" was coined by Awodey in reference to the fact that the cardinality of $\Box_{\delta\nu}([1]^n, [1])$ is the $n$th Dedekind number.

### A.2.1 A no-go theorem

We begin by identifying a property shared by all categories $\mathbf{C}$ with a relatively elegant functor $i: \mathbf{C} \to \mathbf{R}$; the contrapositive will show that no such functor exists out of $\Box_{\delta\nu}$.

Definition A.4 A sieve on an object $a$ of a small category $\mathbf{C}$ is a set of morphisms $S \subseteq \mathbf{C}/a$ such that $g \in S$ implies $gf \in S$ for any composable $f \in \mathbf{C}^\to$. We regard the collection $\mathrm{Sv}_{\mathbf{C}}(a)$ of sieves on $a \in \mathbf{C}$ as a poset ordered by inclusion. A sieve is principal if it is of the form $\langle f \rangle := \{gf \mid g \in \mathbf{C}/b\}$ for some $f: b \to a$; we write $\mathrm{PrSv}_{\mathbf{C}}(a) \subseteq \mathrm{Sv}_{\mathbf{C}}(a)$ for the subposet of principal sieves on $a$.

Recall that $\mathrm{Sv}_{\mathbf{C}}(a)$ is isomorphic to the poset of subobjects of $\mathcal{Z}a \in \mathrm{PSh}(\mathbf{C})$. The principal sieve $\langle f \rangle$ on a map $f: b \to a$ corresponds to the subobject $\mathrm{Im}f \mapsto \mathcal{Z}a$. Given a relatively elegant $i: \mathbf{C} \to \mathbf{R}$, the following lemma deduces a well-foundedness property of these subobjects in $\mathrm{PSh}(\mathbf{C})$ from the well-foundedness of the Reedy category $\mathbf{R}$.

Lemma A.5 Let $\mathbf{C}$ be a category, and let $\mathbf{R}$ be a Reedy category elegant relative to some $i: \mathbf{C} \to \mathbf{R}$. Then for any $a \in \mathbf{C}$, there exists a strictly monotone map $d: \mathrm{PrSv}_{\mathbf{C}}(a) \to \mathbb{N}$. In particular, $\mathrm{PrSv}_{\mathbf{C}}(a)$ is well-founded.

Proof Given a principal sieve $\langle f \rangle \in \mathrm{PrSv}_{\mathbf{C}}(a)$ generated by $f: b \to a$, we define $d(\langle f \rangle)$ to be the degree of $i(f)$, i.e., the degree of the intermediate object in its Reedy factorization. To see that this definition is independent of the choice of representative $f$ and that $d$ is order-preserving, it suffices to check that for any $f: b \to a$ and $f': b' \to a$, if $\langle f' \rangle \subseteq \langle f \rangle$ then $d(\langle f' \rangle) \leq d(\langle f \rangle)$. If $\langle f' \rangle \subseteq \langle f \rangle$, then there exists some $g: b' \to b$ such that $f' = fg$. Upon Reedy factorizing $i(f') = m'e'$ and $i(f) = me$, orthogonality gives us a map as shown:

$$\begin{array}{c} i(b') \xrightarrow{i(g)} i(b) \xrightarrow{e} c \\ e' \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ c' \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \xrightarrow{\quad} \end{array}$$

By Lemma 2.14, the lift is a raising map, so $d(\langle f \rangle) = |c'| \leq |c| = d(\langle f' \rangle)$.

To see that $d$ is strictly monotone, suppose that additionally $|c'| = |c|$. Then the diagonal above is an isomorphism. By $\mathbf{R}^-$-projectivity of $i(b)$ (Corollary 5.38) and fullness

2025/10/16 00:43

Relative Elegance and Cartesian Cubes with One Connection

63

of $i$, we obtain a lift as below:

![img-36.jpeg](img-36.jpeg)

Then $f = f'h$, so $\langle f \rangle \subseteq \langle f' \rangle$.

### A.2.2 Principal sieves in Dedekind cubes

Now we show that the poset of principal sieves on $[1]^3 \in \square_{\mathbb{N}}$ is not well-founded. We embed a poset model of the circle $\mathfrak{C}_n \mapsto [1]^n$ in each cube, then exhibit a chain of subobjects of $[1]^n$ (for any $n \ge 3$) induced by maps $\cdots \to \mathfrak{C}_{n_2} \to \mathfrak{C}_{n_1} \to \mathfrak{C}_n$ that cannot stabilize.

Definition A.6 The fence $\mathfrak{F} \in \mathbf{Pos}$ is the poset whose elements are integers and whose order is generated by the inequalities $i \le i - 1$ and $i \le i + 1$ for all even $i \in \mathbb{Z}$.

Definition A.7 The $n$th crown poset $\mathfrak{C}_n \in \mathbf{Pos}$ is the quotient of $\mathfrak{F}$ identifying $i, j \in \mathfrak{F}$ whenever $i = j \pmod{2n}$. We write $p_n: \mathfrak{F} \to \mathfrak{C}_n$ for the quotient map.

For example, $\mathfrak{C}_4$ is the following poset:

![img-37.jpeg](img-37.jpeg)

Remark A.8 Each crown poset is freely generated by a graph (though not the graphs usually known as crown graphs, which have more edges).

The simplicial nerve $N_\Delta$ sends each crown poset to a simplicial set weakly equivalent to the circle. As such, any map between crown posets can be associated a winding number. Concretely, we can define the winding number on the level of posets as follows:

Definition A.9 Any poset map $f: \mathfrak{C}_m \to \mathfrak{C}_n$ lifts to an endomap

![img-38.jpeg](img-38.jpeg)

which is unique modulo $2n$. The winding number of $f$ is

$$\deg(f) := \frac{\mathring{f}(2m) - \mathring{f}(0)}{2n}.$$

2025/10/16 00:43

64

E. Cavallo and C. Sattler

It is straightforward to check that $\deg(gf) = \deg(g)\deg(f)$ for $\mathfrak{C}_m \xrightarrow{f} \mathfrak{C}_n \xrightarrow{g} \mathfrak{C}_p$, as we expect from a winding number. Because $\mathfrak{C}_m$ is "too short" to wrap around $\mathfrak{C}_n$ when $m < n$, we have the following:

Lemma A.10 If $m < n$, then $\deg(f) = 0$ for any $f: \mathfrak{C}_m \to \mathfrak{C}_n$.

Proof By induction, $|\dot{f}(i) - \dot{f}(0)| \leq i$ for every $i \in \mathbb{N}$, so $|\dot{f}(2m) - \dot{f}(0)| < 2n$.

Definition A.11 For $n \geq 3$, define an poset embedding $c_n: \mathfrak{C}_n \mapsto [1]^n$ by

$$c_n(i)_j = \begin{cases} 1 & \text{if } \lfloor \frac{i}{2} \rfloor \leq j \leq \lceil \frac{i}{2} \rceil \\ 0 & \text{otherwise} \end{cases}$$

Definition A.12 Given $m, n \geq 3$ and a monotone map $f: \mathfrak{C}_m \to \mathfrak{C}_n$, define an extension

$$\begin{array}{c} \mathfrak{C}_m \xrightarrow{f} \mathfrak{C}_n \\ c_m \searrow \quad \searrow c_n \\ [1]^m - \overline{f} \to [1]^n \end{array}$$

by setting

$$\overline{f}(v) := \begin{cases} c_n(f(i)) & \text{if } v = c_m(i), \\ \bot & \text{if } v = \bot, \\ \top & \text{otherwise.} \end{cases}$$

The mapping $f \mapsto \overline{f}$ is the functorial action of a semifunctor from the category of crown posets to $\square_{\mathcal{N}}$: compositions are preserved, but not identities.

Lemma A.13 The diagram in Definition A.12 is a pullback.

Proof The three cases in the definition of $\overline{f}$ have disjoint values.

Theorem A.14 There exists no Reedy category $\mathbf{R}$ with a fully faithful functor $i: \square_{\mathcal{N}} \to \mathbf{R}$ such that $\mathbf{R}$ is elegant relative to $i$.

Proof Suppose for sake of contradiction that we have some $i: \square_{\mathcal{N}} \to \mathbf{R}$ such that $\mathbf{R}$ is elegant relative to $i$. Choose any $n \geq 3$. For every $m \geq 2$ and $a \geq 1$, the identity function on $\mathfrak{F}$ induces a map $f_a: \mathfrak{C}_{am} \to \mathfrak{C}_m$ with winding number $a$. We then have the following diagram in Pos:

$$\begin{array}{c} \dots \xrightarrow{f_2} \mathfrak{C}_{8n} \xrightarrow{f_2} \mathfrak{C}_{4n} \xrightarrow{f_2} \mathfrak{C}_{2n} \\ \downarrow f_8 \quad \downarrow f_4 \quad \downarrow f_2 \\ \dots \xrightarrow{\text{id}} \mathfrak{C}_n \xrightarrow{\text{id}} \mathfrak{C}_n \xrightarrow{\text{id}} \mathfrak{C}_n. \end{array}$$

2025/10/16 00:43

REFERENCES

65

Applying  \( (-) \) , we have a chain of principal sieves  \( \langle\overline{f_{2}}\rangle\supseteq\langle\overline{f_{4}}\rangle\supseteq\langle\overline{f_{8}}\rangle\supseteq\cdots \)  on  \( [1]^{n} \) . By Lemma A.5, this chain must stabilize; in particular, there must be some pair a<b (both powers of 2) such that  \( \langle\overline{f_{a}}\rangle=\langle\overline{f_{b}}\rangle \) . Then there exists a map

![img-39.jpeg](img-39.jpeg)

By Lemma A.13, we have an induced map of crown posets:

![img-40.jpeg](img-40.jpeg)

But because an < bn, we must have  \( \deg(g') = 0 \)  by Lemma A.10, which contradicts that  \( \deg(f_b)\deg(g') = \deg(f_a) = a \) .

## References

[ABCHFL21] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Robert Harper, Kuen-Bang Hou (Favonia), and Daniel R. Licata, "Syntax and models of Cartesian cubical type theory". In: Math. Structures in Comput. Sci. 31.4 (2021), pp. 424–468. DOI: 10.1017/S0960129521000347.

[ACCRS24] Steve Awodey, Evan Cavallo, Thierry Coquand, Emily Riehl, and Christian Sattler. The equivariant model structure on cartesian cubical sets. 2024. arXiv: 2406.18497 [math.AT].

[AFH18] Carlo Angiuli, Kuen-Bang Hou (Favonia), and Robert Harper. "Cartesian Cubical Computational Type Theory: Constructive Reasoning with Paths and Equalities". In: 27th EACSL Annual Conference on Computer Science Logic, CSL 2018, September 4-7, 2018, Birmingham, UK. Ed. by Dan R. Ghica and Achim Jung, Schloss Dagstuhl – Leibniz-Zentrum für Informatik, 2018, 6:1–6:17. DOI: 10.4230/LIPIcs.CSL.2018.6.

[AGH24] Steve Awodey, Nicola Gambino, and Sina Hazratpour. "Kripke-Joyal forcing for type theory and uniform fibrations". In: Sel. Math. New Ser. 30.74 (2024). DOI: 10.1007/s00029-024-00962-2.

[ARV10] Jiří Adámek, Jiří Rosický, and Enrico M. Vitale. Algebraic Theories: A Categorical Introduction to General Algebra. Cambridge Tracts in Mathematics. Cambridge: Cambridge University Press, 2010. DOI: 10.1017/CBO9780511760754.

[Awo23] Steve Awodey. Cartesian cubical model categories. 2023. arXiv: 2305.00893 [math.CT].

[Awo24] Steve Awodey. "On Hofmann–Streicher universes". In: Math. Structures in Comput. Sci. 34.9 (2024), pp. 894–910. DOI: 10.1017/S0960129524000203.

[Bar19] Reid William Barton. "A model 2-category of enriched combinatorial premodel categories". PhD thesis. Harvard University, 2019. URL: http://nrs.harvard.edu/urn-3:HUL.InstRepos:42013127.

[BC15] Marc Bezem and Thierry Coquand. "A Kripke model for simplicial sets". In: Theoret. Comput. Sci. 574 (2015), pp. 86–91. DOI: 10.1016/j.tcs.2015.01.035.

[BCH13] Marc Bezem, Thierry Coquand, and Simon Huber. "A Model of Type Theory in Cubical Sets". In: 19th International Conference on Types for Proofs and Programs, TYPES 2013, April 22-26,

2025/10/16 00:43

66

REFERENCES

2013. Toulouse, France. Schloss Dagstuhl – Leibniz-Zentrum für Informatik, 2013, pp. 107–128. DOI: 10.4230/LIPics.TYPES.2013.107.
[BCH19] Marc Bezem, Thierry Coquand, and Simon Huber. “The Univalence Axiom in Cubical Sets”. In: J. Automat. Reason. 63 (2019), pp. 159–171. DOI: 10.1007/s10817-018-9472-6.
[BCP15] Marc Bezem, Thierry Coquand, and Erik Parmann. “Non-Constructivity in Kan Simplicial Sets”. In: 13th International Conference on Typed Lambda Calculi and Applications, TLCA 2015, July 3-3, 2015, Warsaw, Poland. Ed. by Thorsten Altenkirch. Vol. 38. 2015, pp. 92–106. DOI: 10.4230/LIPics.TLCA.2015.92.
[BD86] Francis Borceux and Dominique Dejean. “Cauchy completion in category theory”. en. In: Cah. Topol. Géom. Différ. Catég. 27.2 (1986), pp. 133–146. URL: http://www.numdam.org/item/CTGDC_1986_27_2_133_0/.
[BF22] Benno van den Berg and Eric Faber. Effective Kan Fibrations in Simplicial Sets. Lecture Notes in Mathematics. Cham: Springer, 2022. DOI: 10.1007/978-3-031-18900-5.
[BH81] Ronald Brown and Philip J. Higgins. “On the algebra of cubes”. In: J. Pure Appl. Algebra 21.3 (1981), pp. 233–260. DOI: 10.1016/0022-4049(81)90018-9.
[BM11] Clemens Berger and Ieke Moerdijk. “On an extension of the notion of Reedy category”. In: Math. Z. 269.3 (2011), pp. 977–1004. DOI: 10.1007/s00209-010-0770-x.
[BM17] Ulrik Buchholtz and Edward Morehouse. “Varieties of Cubical Sets”. In: Relational and Algebraic Methods in Computer Science - 16th International Conference, RAMICS 2017, Lyon, France, May 15-18, 2017, Proceedings. Ed. by Peter Höfner, Damien Pous, and Georg Struth. 2017, pp. 77–92. DOI: 10.1007/978-3-319-57418-9_5.
[Boc22] Rafaël Bocquet. “Strictification of Weakly Stable Type-Theoretic Structures Using Generic Contexts”. In: 27th International Conference on Types for Proofs and Programs (TYPES 2021). Ed. by Henning Basold, Jesper Cockx, and Silvia Ghilezan. Vol. 239. Dagstuhl, Germany, 2022, 3:1–3:23. DOI: 10.4230/LIPics.TYPES.2021.3.
[Bor94] Francis Borceux. Handbook of Categorical Algebra. Vol. 1. Encyclopedia of Mathematics and its Applications. Cambridge: Cambridge University Press, 1994. DOI: 10.1017/CBO9780511525858.
[BR13] Julia E. Bergner and Charles Rezk. “Reedy categories and the Θ-construction”. In: Math. Z. 274.1 (2013), pp. 499–514. DOI: 10.1007/s00209-012-1082-0.
[Cam23] Timothy Campion. Cubical sites as Eilenberg-Zilber categories. 2023. arXiv: 2303.06206 [math.CT].
[CCHM15] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. “Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom”. In: 21st International Conference on Types for Proofs and Programs, TYPES 2015, May 18-21, 2015, Tallinn, Estonia. Ed. by Tarmo Uustalu. Schloss Dagstuhl – Leibniz-Zentrum für Informatik, 2015, 5:1–5:34. DOI: 10.4230/LIPics.TYPES.2015.5.
[Cis06] Denis-Charles Cisinski. Les préfaiseaux comme modèles des types d’homotopie. Astérisque 308. Paris: Société mathématique de France, 2006.
[Cis14] Denis-Charles Cisinski. Univalent universes for elegant models of homotopy types. 2014. arXiv: 1406.0058 [math.AT].
[Cis19] Denis-Charles Cisinski. Higher Categories and Homotopical Algebra. Cambridge Studies in Advanced Mathematics 308. Cambridge University Press, 2019. DOI: 10.1017/9781108588737.
[CMS19] Evan Cavallo, Anders Mörtberg, and Andrew Swan. “Model structures on cubical sets”. Unpublished note. June 2019. URL: https://github.com/mortberg/gen-cart/blob/master/modelstructure.pdf.
[CMS20] Evan Cavallo, Anders Mörtberg, and Andrew W. Swan. “Unifying Cubical Models of Univalent Type Theory”. In: 28th EACSL Annual Conference on Computer Science Logic, CSL 2020, January 13-16, 2020, Barcelona, Spain. Vol. 152. 2020, 14:1–14:17. DOI: 10.4230/LIPics.CSL.2020.14.
[Coq+18] Thierry Coquand et al. “Quillen model structure”. Mailing list discussion. June 2018. URL: https://groups.google.com/g/homotopytypetheory/c/RQkLWZ_83kQ.
[DHKS04] William G. Dwyer, Philip S. Hirschhorn, Daniel M. Kan, and Jeffrey H. Smith. Homotopy Limit Functions on Model Categories and Homotopical Categories. Vol. 113. Mathematical Surveys and

2025/10/16 00:43

REFERENCES

67

Monographs. Providence, Rhode Island: American Mathematical Society, 2004. ISBN: 978-0-8218-3703-0.
[Dug08] Daniel Dugger. "A primer on homotopy colimits". Unpublished. 2008. URL: http://math.uoregon.edu/~ddugger/hocolim.pdf.
[Gar09] Richard Garner. "Understanding the Small Object Argument". In: Appl. Categ. Structures 17.3 (2009), pp. 247–285. DOI: 10.1007/s10485-008-9137-4.
[GH22] Nicola Gambino and Simon Henry. "Towards a constructive simplicial model of Univalent Foundations". In: J. Lond. Math. Soc. 105.2 (2022), pp. 1073–1109. DOI: 10.1112/jlms.12532.
[GL21] Nicola Gambino and Marco Federico Larrea. "Models of Martin-Löf type theory from algebraic weak factorisation systems". In: J. Symb. Log. 88.1 (2021), pp. 1–45. DOI: 10.1017/jsl.2021.39.
[Gro83] Alexander Grothendieck. "Pursuing Stacks". 1983.
[GS17] Nicola Gambino and Christian Sattler. "The Frobenius condition, right properness, and uniform fibrations". In: J. Pure Appl. Algebra 221.12 (2017), pp. 3027–3068. DOI: 10.1016/j.jpaa.2017.02.013.
[GSS22] Nicola Gambino, Christian Sattler, and Karol Szumiło. "The constructive Kan-Quillen model structure: two new proofs". In: Q. J. Math. 73.4 (2022), pp. 1307–1373. DOI: 10.1093/qmath/haab057.
[GT06] Marco Grandis and Walter Tholen. "Natural Weak Factorization Systems". In: Arch. Math. (Brno) 42 (2006), pp. 397–408. URL: http://hdl.handle.net/10338.dmlcz/108015.
[GZ67] Pierre Gabriel and Michel Zisman. Calculus of fractions and homotopy theory. Ergebnisse der Mathematik und ihrer Grenzgebiete 35. Springer, 1967. DOI: 10.1007/978-3-642-85844-4.
[Hen20] Simon Henry. "Weak model categories in classical and constructive mathematics". In: Theory Appl. Categ. 35.24 (2020), pp. 875–958. DOI: 10.70930/tac/0tkrfy1d.
[Hen25] Simon Henry. "A constructive account of the Kan-Quillen model structure and of Kan's Exon functor". In: Cah. Topol. Géom. Différ. Catég. LXVI.1 (2025), pp. 65–124. URL: https://cahierstgd.com/wp-content/uploads/2025/01/HENRY-SIMON-_-LXVI-1-1.pdf.
[HK71] Alfred Horn and Naoki Kimura. "The category of semilattices". In: Algebra Universalis 1.1 (1971), pp. 26–38. DOI: 10.1007/BF02944952.
[Hov99] Mark Hovey. Model Categories. Vol. 63. Mathematical surveys and monographs. Providence, Rhode Island: American Mathematical Society, 1999. ISBN: 978-0-8218-4361-1. DOI: 10.1090/surv/063.
[HR22] Philip Hackney and Martina Rovelli. "Induced model structures for higher categories". In: Proc. Amer. Math. Soc. 150 (2022), pp. 4629–4644. DOI: 10.1090/proc/15982.
[HS97] Martin Hofmann and Thomas Streicher. "Lifting Grothendieck Universes". Unpublished note. 1997. URL: https://www2.mathematik.tu-darmstadt.de/~streicher/NOTES/lift.pdf.
[IKLP14] Wilfried Imrich, Rafał Kalinowski, Florian Lehner, and Monika Piśniak. "Endomorphism Breaking in Graphs". In: Electron. J. Combin. 21.1 (2014). DOI: 10.37236/3073.
[Isa11] Samuel B. Isaacson. "Symmetric cubical sets". In: J. Pure Appl. Algebra 215.6 (2011), pp. 1146–1173. ISSN: 0022-4049. DOI: 10.1016/j.jpaa.2010.08.001.
[Jar06] J. F. Jardine. "Categorical Homotopy Theory". In: Homology Homotopy Appl. 8.1 (2006), pp. 71–144.
[John82] Peter T. Johnstone. Stone Spaces. Cambridge Studies in Advanced Mathematics 3. Cambridge University Press, 1982. ISBN: 9780521337793.
[Joy97] André Joyal. "Disks, duality and $\Theta$-categories". Preprint. 1997.
[KL21] Krzysztof Kapulkin and Peter LeFanu Lumsdaine. "The Simplicial Model of Univalent Foundations (after Voevodsky)". In: J. Eur. Math. Soc. (JEMS) 23.6 (2021), pp. 2071–2126. DOI: 10.4171/JEMS/1050.
[KV20] Krzysztof Kapulkin and Vladimir Voevodsky. "A cubical approach to straightening". In: J. Topol. 13.4 (2020), pp. 1682–1700. DOI: 10.1112/topo.12173.
[Law63] F. William Lawvere. "Functorial Semantics of Algebraic Theories". PhD thesis. Columbia University, 1963.

2025/10/16 00:43

68

REFERENCES

[LOPS18] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. "Internal Universes in Models of Homotopy Type Theory". In: 3rd International Conference on Formal Structures for Computation and Deduction, FSCD 2018, July 9-12, 2018, Oxford, UK. Ed. by Hélène Kirchner. Vol. 108. 2018, 22:1–22:17. DOI: 10.4230/LIPICS.FSCD.2018.22.
[LW15] Peter LeFanu Lumsdaine and Michael A. Warren. "The Local Universes Model: An Overlooked Coherence Construction for Dependent Type Theories". In: ACM Trans. Comput. Log. 16.3 (2015), 23:1–23:31. DOI: 10.1145/2754931.
[Mal05] Georges Maltsiniotis. La théorie de l'homotopie de Grothendieck. Astérisque 301. Paris: Société mathématique de France, 2005. URL: https://webusers.imj-prg.fr/~georges.maltsiniotis/ps/prstnew.pdf.
[Mal09] Georges Maltsiniotis. "La catégorie cubique avec connexions est une catégorie test stricte". In: Homology Homotopy Appl. 11.2 (2009), pp. 309–326. DOI: hha/1296138523.
[nLa24] nLab authors. Beck-Chevalley condition. https://ncatlab.org/nlab/show/Beck-Chevalley+condition.Revision 60, accessed 10 June 2024, June 2024.
[OP18] Ian Orton and Andrew M. Pitts. "Axioms for Modelling Cubical Type Theory in a Topos". In: Log. Methods Comput. Sci. 14.4 (2018). DOI: 10.23638/LMCS-14(4:23)2018.
[Par18] Erik Parmann. "Functional Kan Simplicial Sets: Non-Constructivity of Exponentiation". In: 21st International Conference on Types for Proofs and Programs (TYPES 2015). Ed. by Tarmo Uustalu. Vol. 69. Dagstuhl, Germany, 2018, 8:1–8:25. DOI: 10.4230/LIPICS.TYPES.2015.8.
[Qui67] Daniel G. Quillen. Homotopical Algebra. Lecture Notes in Mathematics. Heidelberg: Springer, 1967. DOI: 10.1007/BFb0097438.
[Rie14] Emily Riehl. Categorical Homotopy Theory. New Mathematical Monographs. Cambridge University Press, 2014. DOI: 10.1017/CBO9781107261457.
[Rie17] Emily Riehl. Inductive presentations of generalized Reedy categories. Unpublished note. 2017. URL: https://math.jhu.edu/~eriehl/generalized-reedy.pdf.
[Ril24] Mitchell Riley. A Type Theory with a Tiny Object. 2024. arXiv: 2403.01939 [math.CT].
[RV14] Emily Riehl and Dominic Verity. "The theory and practice of Reedy categories". In: Theory Appl. Categ. 29.9 (2014), pp. 256–301. DOI: 10.70930/tac/2q3vx1tg.
[Sat17] Christian Sattler. The Equivalence Extension Property and Model Structures. 2017. arXiv: 1704.06911 [math.CT].
[Sat18] Christian Sattler. Do cubical models of type theory also model homotopy types. Lecture at the Hausdorff Trimester Program: Types, Sets and Constructions. 2018. URL: https://www.youtube.com/watch?v=wkPDyIGmEoA.
[Sat19] Christian Sattler. Idempotent completion of cubes in posets. 2019. arXiv: 1805.04126 [math.CT].
[Sat23] Christian Sattler. Free monad sequences and extension operations. Unpublished note. 2023. URL: https://www.cse.chalmers.se/~sattler/docs/extension.pdf.
[Shu15] Michael Shulman. Reedy categories and their generalizations. 2015. arXiv: 1507.01065 [math.AT].
[Shu19] Michael Shulman. All (∞, 1)-toposes have strict univalent universes. 2019. arXiv: 1904.07004 [math.AT].
[Shu23] Michael Shulman. "The derivator of setoids". In: Cab. Topol. Géom. Différ. Catég. LXIV.1 (2023), pp. 29–96. URL: https://cahierstgdc.com/wp-content/uploads/2023/01/SHULMAN-LXIV-1.pdf.
[Spi16] Bas Spitters. Cubical sets and the topological topos. 2016. arXiv: 1610.05270 [cs.LO].
[Sir05] Thomas Streicher. "Universes in Toposes". In: From Sets and Types to Topology and Analysis: Towards practicable foundations for constructive mathematics. Ed. by Laura Crosilla and Peter Schuster. Vol. 48. Oxford Logical Guides. Oxford University Press, 2005, pp. 78–90. ISBN: 978-0-19-856651-9. DOI: 10.1093/acprof:oso/9780198566519.003.0005.
[SW21] Thomas Streicher and Jonathan Weinberger. "Simplicial sets inside cubical sets". In: Theory Appl. Categ. 37.10 (2021), pp. 276–286. DOI: 10.70930/tac/ob3pmmyi.
[Swa18] Andrew W Swan. W-Types with Reductions and the Small Object Argument. 2018. arXiv: 1802.07588 [math.CT].
[Swa22] Andrew W Swan. Definable and Non-definable Notions of Structure. 2022. arXiv: 2206.13643 [math.LO].

2025/10/16 00:43

REFERENCES

69

[Uni13] The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study, 2013.
[WL20] Matthew Z. Weaver and Daniel R. Licata. "A Constructive Model of Directed Univalence in Bicubical Sets". In: *LICS '20: 35th Annual ACM/IEEE Symposium on Logic in Computer Science, Saarbrücken, Germany, July 8-11, 2020*. Ed. by Holger Hermanns, Lijun Zhang, Naoki Kobayashi, and Dale Miller. New York, New York: Association for Computing Machinery, 2020, pp. 915–928. DOI: 10.1145/3373718.3394794.
[Wra93] Gavin C. Wraith. "Using the generic interval". In: *Cah. Topol. Géom. Différ. Catég.* 34.4 (1993), pp. 259–266. URL: https://www.numdam.org/item/CTGDC_1993__34_4_259_0.pdf.

Department of Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg, Gothenburg, Sweden
e-mail: evan.cavallo@gu.se.

Department of Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg, Gothenburg, Sweden
e-mail: sattler@chalmers.se.

2025/10/16 00:43