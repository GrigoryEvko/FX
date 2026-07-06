arXiv:2406.18497v3 [math.AT] 20 Apr 2026

# THE EQUIVARIANT MODEL STRUCTURE ON CARTESIAN CUBICAL SETS

STEVE AWODEY, EVAN CAVALLO, THIERRY COQUAND, EMILY RIEHL, AND CHRISTIAN SATTLER

ABSTRACT. We develop a constructive model of homotopy type theory in a Quillen model category that classically presents the usual homotopy theory of spaces. Our model is based on presheaves over the cartesian cube category, a well-behaved Eilenberg–Zilber category. The key innovation is an additional equivariance condition in the specification of the cubical Kan fibrations, which can be described as the pullback of an interval-based class of uniform fibrations in the category of symmetric sequences of cubical sets. The main technical results in the development of our model have been formalized in a computer proof assistant.

# CONTENTS

|  1. Introduction | 2  |
| --- | --- |
|  1.1. Interpreting homotopy type theory | 2  |
|  1.2. Cubical interpretations | 3  |
|  1.3. Cubical model structures | 3  |
|  1.4. Standard homotopy theory | 4  |
|  1.5. The equivariant cubical model | 4  |
|  1.6. Results | 7  |
|  1.7. Related and future work | 9  |
|  1.8. Acknowledgments | 11  |
|  2. Notions of fibred structure and universes | 12  |
|  2.1. Locally representable and relatively acyclic notions of fibred structure | 12  |
|  2.2. Monomorphisms and uniform trivial fibrations | 18  |
|  2.3. Universes | 22  |
|  3. Cylindrical model structures | 24  |
|  3.1. Cylindrical premodel structures | 25  |
|  3.2. Brown factorizations | 28  |
|  3.3. Equivalence extension property | 30  |
|  3.4. The Frobenius condition | 32  |
|  3.5. Univalence | 34  |
|  3.6. Fibrant universes | 37  |
|  3.7. Fibration extension property and 2-of-3 | 40  |
|  4. The interval model structure on cubical species | 41  |
|  4.1. Groupoid-indexed diagram categories | 42  |
|  4.2. Cubical species and the symmetric interval | 43  |
|  4.3. The cylindrical premodel structure on cubical species | 44  |
|  4.4. The cubical species model of homotopy type theory | 51  |
|  5. The equivariant model structure on cubical sets | 52  |
|  5.1. From cubical species to equivariant cubical sets | 53  |
|  5.2. The cylindrical premodel structure on cubical sets | 54  |
|  5.3. The equivariant cubical sets model of homotopy type theory | 58  |

Date: April 21, 2026.

1

|  6. The equivalence with classical homotopy theory | 61  |
| --- | --- |
|  6.1. Triangulation | 62  |
|  6.2. Eilenberg–Zilber categories | 69  |
|  6.3. The equivariant model structure is the test model structure | 74  |
|  Appendix A. Type-theoretic development and formalization | 75  |
|  A.1. Introduction | 75  |
|  A.2. Judgments of the homotopical interpretation | 77  |
|  A.3. Cubes and cofibrations | 77  |
|  A.4. Partial elements and contractible types | 78  |
|  A.5. Filling and equivariant filling | 78  |
|  A.6. The Frobenius condition | 79  |
|  A.7. Other type formers | 80  |
|  A.8. Tiny interval and universes | 81  |
|  References | 83  |

## 1. INTRODUCTION

1.1. **Interpreting homotopy type theory.** Martin-Löf's dependent type theory [ML75; NPS01] provides a foundation for constructive mathematics. It functions both as a formal language for mathematical arguments and as a programming language: proofs of mathematical statements in Martin-Löf type theory can be regarded as functions or algorithms with computational content. At the turn of the 21st century, higher-dimensional and ultimately homotopical interpretations of Martin-Löf type theory were discovered [HS97; AW09; BG12; KL21]. The novelty of these interpretations is concentrated in their treatment of *identities*, i.e. equalities: an identity between two elements of a type is interpreted as a *path* or higher cell connecting them. *Homotopy type theory* (HoTT) or *univalent foundations* (UF) [UF13] refers to the formal system of Martin-Löf type theory augmented by Voevodsky's *univalence axiom*, which asserts that a certain canonical map is an equivalence

$$(A =_U B) \simeq (A \simeq B) \quad (1.1.1)$$

between the type $A =_U B$ of identities between types $A, B$ in a universe $U$ and the type $A \simeq B$ of homotopy equivalences between them.

To establish the consistency of the univalence axiom with the rules of Martin-Löf type theory (relative to the consistency of the rest of mathematics), Voevodsky [KL21] built a model of homotopy type theory using the standard model of homotopy theory in simplicial sets. The construction makes use of the *Quillen model structure* on simplicial sets [Qui67], which exhibits this category as a setting for abstract homotopy theory. In particular, dependent type families are interpreted as the fibrations of this model structure (the *Kan fibrations*), and the interpretations of type formers rely on established properties of the model structure; for example, the interpretation of $\Pi$-types rests on the fact that the model structure is *right proper* [KL21, 2.3.1].

Voevodsky's definition of the model relies on classical principles of reasoning such as the law of excluded middle and the axiom of choice, a surprising dependency given the constructive character of type theory itself. Bezem, Coquand, and Parmann [BC15; BCP15; Par18] showed that components of the model are in fact inherently non-constructive (though see §1.7.3 below). Thus one is also interested in finding models that can be defined using only constructively valid reasoning. Such a model would, in particular, construct an explicit equivalence inverse to the map (1.1.1), supplying computational content to proofs that invoke the univalence axiom.

2

1.2. **Cubical interpretations.** The first step towards a constructive model was taken by Bezem, Coquand, and Huber (BCH) [BCH14], who gave a partial constructive interpretation of homotopy type theory that was later completed in [BCH19]. Their interpretation replaces simplicial sets by a form of *cubical* sets, i.e. presheaves on a *cube category*,$^{1}$ thereby avoiding non-constructive elements of Voevodsky's model. Cohen, Coquand, Huber, and Mörtberg (CCHM) [CCHM15] gave a complete constructive interpretation in a second, highly structured form of cubical sets; in this setting they were also able to interpret *higher inductive types* [CHM18]. Angiuli, Favonia, and Harper [AFH18] described a computational interpretation based on a third cube category proposed by Awodey [Awo18a], the *cartesian cubes*, using a definition of fibration for these cubical sets proposed by Coquand [Coq14]. This work cuts down the cube category from the CCHM model, retaining only the diagonal face maps that are apparently essential for interpreting higher inductive types. The computational interpretation was then translated to a cubical set interpretation by Angiuli et al. [ABCHFL21]. The CCHM and cartesian interpretations can now be understood as instances of a single construction that works for any cube category with at least cartesian structure [CMS20].

The inspiration for these models traces back to Kan's early work on abstract homotopy theory in cubical sets [Kan55]. His *E-complexes* (now called *cubical Kan complexes*) are the fibrant objects of a Quillen model structure whose fibrations are the maps satisfying a *box-filling* property [Jar02, §3; Cis06, 8.4.38]. Relative to simplicial sets, one essential feature of cubical sets for constructive interpretation of type theory seems to be the closure of cubes under a symmetric monoidal product—the product of the $m$-cube and $n$-cube is the $(m+n)$-cube—which plays a key role in the construction of universes. The monoidal product of cubes in Kan's cubical sets is *not* symmetric, so the techniques do not seem to yield a constructive interpretation in these cubical sets. There is, however, a great variety of symmetric cube categories that one can consider (see, e.g., Grandis and Mauri [GM03] and Buchholtz and Morehouse [BM17]), hence the proliferation of cubical interpretations.

1.3. **Cubical model structures.** Although the cubical interpretations of HoTT/UF were not introduced using Quillen model categories, a posteriori each can be seen [Sat17; CMS20; Awo26] to determine a Quillen model structure in the following sense.$^{2}$ Given a model of Martin-Löf type theory in the form of a suitably-structured category with families [Dyb96] or natural model [Awo18b] (such as the aforementioned cubical interpretations), we consider its category of contexts. On this category, we have a candidate class of *fibrations*: the retracts of context projections $p_A: \Gamma, A \rightarrow \Gamma$ associated to semantic types $\Gamma \vdash A$. We also have a candidate class of *trivial fibrations*: those fibrations derived from *contractible* semantic types in the sense of HoTT [UF13, 3.11].$^{3}$ A Quillen model structure is completely characterized by its classes of fibrations and trivial fibrations, but not every choice of classes forms a Quillen model structure. First, each class should form the right

$^{1}$There is a wide variety of cube categories in common use. In all instances, the objects are indexed by the natural numbers, defining an “$n$-cube” for each $n \in \mathbb{N}$, and there are *face* and *degeneracy* maps that include exterior faces or project away from one of the $n$ dimensions of an $n$-cube. Other optional structure is given by maps that encode automorphisms of an $n$-cube in the form of either *symmetries* or *reversals*, *diagonal* face maps, or extra degeneracies in the form of *connections*.

$^{2}$The existence of a model structure associated to the BCH interpretation has not appeared explicitly in the literature, to our knowledge, but it can be deduced from known results. Swan constructs the two factorization systems [Swa16; Swa18b, §7.5.3], and these form a cylindrical premodel structure in the sense of §3 with all objects cofibrant. The 2-out-of-3 property then follows from the existence of fibrant universes [Hub16, §1.4] via Lemma 3.7.2 and Proposition 3.7.3.

$^{3}$We do not claim that this is the only sensible way to associate a candidate model structure to a model of type theory. Note that all objects are cofibrant in any model structure of this form, as every contractible type has a section. By contrast, in work on constructive simplicial models of homotopy theory and type theory (discussed in §1.7.3 below), one works with a model structure in which not all objects are cofibrant and uses the full subcategory of cofibrant objects as the category of contexts for the model of type theory.

3

class of a weak factorization system. If this is the case, we have a *premodel structure* in the sense of Barton [Bar19]. A premodel structure determines a candidate class of weak equivalences, and a premodel structure is a Quillen model structure exactly if this class satisfies the 2-of-3 property. When said property is satisfied, we may speak of the *Quillen model structure associated to* the model of type theory.

As the semantic types of the cubical interpretations are defined by right lifting properties, it is not so surprising that the induced classes of fibrations and trivial fibrations indeed define a premodel structure. The main technical challenge lies in checking the 2-of-3 property. In a reversal of the history of Voevodsky's simplicial model, the property is verified using components of the model of type theory. In particular, the *fibration extension property* and *equivalence extension property*, used to interpret universes and univalence respectively, play a direct role [Sat17], as does the *Frobenius condition* [BG12, 3.3.3; GS17] used to interpret $\Pi$-types.

1.4. **Standard homotopy theory.** Having associated a Quillen model structure to each cubical interpretation, we are in a position to ask what *homotopy theory* each presents, i.e., to characterize the $(\infty, 1)$-categories they present. In particular, we would like to know if any constructive interpretation of HoTT presents the $(\infty, 1)$-category of *spaces* (or *homotopy types* or $\infty$-*groupoids*), as does Voevodsky's classical model in simplicial sets. While we might ultimately hope to interpret HoTT in all $\infty$-toposes, as accomplished by Shulman in the classical setting [Shu19], interpretation in spaces is a fundamental motivation for synthetic homotopy theory in HoTT.

In model-categorical language, we seek a *Quillen equivalence* (or zigzag of Quillen equivalences) between a model structure associated to a cubical interpretation and some model category known to present spaces, such as the classical Kan–Quillen model structure on simplicial sets. In fact, we can compare more directly with existing classical model structures on cubical sets. Buchholtz and Morehouse [BM17] observe that each of the cube categories used to model type theory is a so-called *test category*. The theory of test categories, initiated by Grothendieck [Gro84] and continued by Maltsiniotis [Mal05] and Cisinski [Cis06], guarantees (using classical logic) that the category of presheaves on any test category admits a Quillen model structure presenting the homotopy theory of spaces. Thus, we may also ask whether the Quillen model structure associated to a cubical interpretation coincides with the test model structure. This is a stronger condition, as multiple equivalent but non-identical Quillen model structures can exist on the same underlying category.

These questions were first discussed in 2018, at the Hausdorff Institute Trimester, and a number of negative results became folklore, discussed on the Homotopy Type Theory mailing list [Coq+18] and sketched in [Sat18]. The upshot is that many cubical interpretations do not present spaces, and a fortiori do not coincide with the corresponding test model structures. In particular, the BCH model in the minimal symmetric monoidal cube category does not. The later model constructions yield interpretations in any cube category with cartesian products, so there are many candidates to consider here. However, neither the *De Morgan cube category* with connections and reversals, which is the focus of [CCHM15], nor the minimal *cartesian cube category* considered in [ABCHFL21; Awo26], gives a model of spaces. It is an open question whether the interpretation in the *Dedekind cube category* (with cartesian structure and connections) presents spaces.

This brings us to the main result of this article, the construction of a cubical interpretation that *does* classically present the homotopy theory of spaces.

1.5. **The equivariant cubical model.** We define a new model of HoTT with an associated Quillen model structure, the *equivariant cartesian model*, by modifying the original cartesian cubical set model of Angiuli et al., replacing its fibrations with a more restrictive class of *equivariant fibrations*.

1.5.1. *The problem.* Our definition of equivariant fibration is motivated by a specific pathology in the original Quillen model structure associated to the model of type theory on cartesian cubical sets

4

[CMS20; Awo26], namely the non-contractibility of automorphism quotients of cubes. In cartesian cubical sets, the group of automorphisms of the representable n-cube  \( I^{n} \)  is the symmetric group  \( \Sigma_{n} \) : the only automorphisms are the permutations of the axes of the cube. For any subgroup  \( H \subset \Sigma_{n} \) , we then have a quotient  \( I_{/H}^{n} \in cSet \) , the colimit of the H-indexed diagram sending a permutation to the corresponding automorphism of  \( I^{n} \) . When H is non-trivial,  \( I_{/H}^{n} \)  is not contractible in this model structure.

First, to see why this is problematic, let us consider a natural comparison to a model category presenting the homotopy theory of spaces: the adjunction

![img-0.jpeg](img-0.jpeg)

between cartesian cubical and simplicial sets whose left adjoint, triangulation, sends the \(n\)-cube to the \(n\)-ary cartesian product of the 1-simplex. This adjunction is in fact a Quillen adjunction, but the triangulations \(TI_{/H}^{n} \in \mathsf{sSet}\) are all contractible; for example, the quotient \(I_{/\Sigma_2}^2\) is isomorphic to \(\Delta^2\). As the left adjoint of a Quillen equivalence reflects contractibility of cofibrant objects [Hov99, 1.3.16], this adjunction cannot be a Quillen equivalence if \(I_{/H}^{n}\) is not contractible. Of course, the model structure on cSet could present spaces without this particular adjunction being a Quillen equivalence. However, it is worth noting that triangulation does define a Quillen equivalence from the test model structure on cSet to the Kan-Quillen model structure on sSet (see §6.3).

Second, let us give some intuition as to why  \( I_{/H}^{n} \)  is not contractible in the model structure of [CMS20; Awo26]. We recall the “uniform unbiased box-filling” characterization of its fibrations alluded to above. Briefly, a map  \( f: Y \to X \)  is a fibration when it admits a choice of lifts

![img-1.jpeg](img-1.jpeg)

for each lifting problem against an open box inclusion (determined by a subobject \( c \colon C \hookrightarrow I^n \) and generalized point \( \xi \colon I^n \to I^1 \)) in such a way that for every morphism of cubes \( \alpha \colon I^m \to I^n \), the resulting triangle

![img-2.jpeg](img-2.jpeg)

formed by the two chosen lifts commutes.

In the language of algebraic weak factorization systems (awfs), the class of fibrations is generated by the category of open box inclusions and pullback squares between them. In fact, this open box category generates categories of trivial cofibration coalgebras and fibration algebras, which by Garner's algebraic small object argument [Gar09] constitute an awfs. There is then an underlying weak factorization system whose left and right maps are the retracts of maps admitting trivial cofibration coalgebra and fibration algebra structures respectively. \( ^{4} \)  The forgetful functor sending a trivial cofibration coalgebra to its underlying map creates colimits, and the open box category

\( ^{4} \) Since the awfs under consideration is cofibrantly generated by a category, the monad algebras are already retract closed. Equivalently, the left and right maps are those admitting coalgebra structures for the copointed endofunctor underlying the comonad and algebra structures for the pointed endofunctor underlying the monad, respectively.

5

embeds in the category of coalgebras; thus, in particular, the colimit in $\mathsf{cSet}^2$ of any diagram of open box inclusions and pullback squares is a trivial cofibration.

With this definition, it is immediate that the 1-cube is contractible: the endpoint $0: 1 \mapsto I$ is the open box formed by the subobject $\emptyset \mapsto I^0$ and point $0: I^0 \to I^1$, thus a trivial cofibration. That the 2-cube is contractible is slightly less immediate: we can write $\vec{0}: 1 \to I^2$ as a composite of generating trivial cofibrations

$$1 \xrightarrow[0]{\sim} I^1 \xrightarrow[I^1 \times 0]{\sim} I^2$$

where the second map is the open box formed by $\emptyset \mapsto I^1$ and the constant map $0: I^1 \to I^1$. We can continue inductively to see that $\vec{0}: 1 \to I^n$ is a trivial cofibration for all $n$, the composite of $n$ generating trivial cofibrations. Observe, however, that this construction is inherently *asymmetric*: we collapse a 2-cube by collapsing first along one axis and then along the other. This prevents us, for example, from deriving a trivial cofibration coalgebra structure on $\vec{0}: 1 \to I^2_{/\Sigma_2}$ by taking a colimit: writing $\Sigma_2$ for the one-object groupoid corresponding to $\Sigma_2$, the diagram $\Sigma_2 \to \mathsf{cSet}^2$ sending the object to $\vec{0}: 1 \xrightarrow{\sim} I^2$ and $\sigma \in \Sigma_2$ to

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \\ \vec{0} \downarrow & & \vec{0} \downarrow \\ I^2 & \xrightarrow{\sigma} & I^2 \end{array}$$

does *not* lift to a diagram of trivial cofibration coalgebras. In fact, one can show that if $A \xrightarrow{\sim} B$ is a trivial cofibration and $B$ contains a non-trivial (in an appropriate sense) copy of $I^2_{/\Sigma_2}$, then so does $A$ [Coq18, §4]: trivial cofibrations cannot collapse copies of $I^2_{/\Sigma_2}$. It follows that $I^2_{/\Sigma_2}$ is not contractible [Coq18, §5]; the same argument applies to quotients of higher cubes.

1.5.2. *The solution.* Our solution to this problem is to require a more general *equivariant* uniform box-filling structure on our fibrations. First, we generalize the open box inclusions, replacing generalized points $\xi: I^n \to I^1$ on the 1-cube with points $\xi: I^n \to I^k$ in arbitrary $k$-cubes, so that we ask for lifts

$$\begin{array}{ccc} I^n \cup_C C \times I^k & \longrightarrow & Y \\ \langle [\xi], c \times I^k \rangle \downarrow & & \downarrow f \\ I^n \times I^k & \longrightarrow & X. \end{array}$$

This generalization alone does not change the class of fibrations. The key is in our generalization of the uniformity condition: for every morphism of cubes $\alpha: I^m \to I^n$ and *automorphism* $\sigma: I^k \cong I^k$, the resulting triangle of lifts

$$\begin{array}{ccc} I^m \cup_D D \times I^k & \longrightarrow & I^n \cup_C C \times I^k \xrightarrow{\sim} Y \\ \downarrow & \downarrow & \downarrow \\ I^m \times I^k & \xrightarrow[\alpha \times \sigma]{} & I^n \times I^k \xrightarrow{\sim} X \end{array}$$

must commute.

With this definition, the vertex inclusion $\vec{0}: 1 \to I^n$ is immediately a trivial cofibration: it is the open box formed by $\emptyset \mapsto 1$ and the point $\vec{0}: 1 \to I^n$. Moreover, for any $H \subset \Sigma_n$, the diagram

6

$\mathsf{H} \to \mathsf{cSet}^2$ sending the object to $\vec{0}: 1 \xrightarrow{\sim} I^n$ and $\sigma \in H$ to

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \\ \vec{0} \updownarrow & & \vec{0} \updownarrow \\ I^n & \xrightarrow{\sigma} & I^n \end{array}$$

now *does* lift to a diagram of trivial cofibration coalgebras; its colimit exhibits the point $\vec{0}: 1 \to I^n_H$ as a trivial cofibration, making $I^n_H$ contractible.

These observations led us to a construction of the generating categories of cofibrations and trivial cofibrations for the equivariant model structure in Summer 2019. While we felt confident that these categories were canonical—since we had arrived at their definition simultaneously through two different constructions, one category theoretic and one type theoretic—the corresponding model structure felt somewhat ad hoc, not fitting into known paradigms for constructions of model categorical models of homotopy type theory. A few years later, we realized that the equivariant premodel structure could be transferred from a premodel structure on the category $\mathsf{cSet}^2$ of *cubical species* (i.e., symmetric sequences of cubical sets), where there exists a canonical equivariant interval object $\mathbb{I} = (I^n)_{n \geq 1}$. There the generating cofibrations and trivial cofibrations fit into a known paradigm where the latter are defined from the former using the generic point of the interval $\mathbb{I}$ (as in [ABCHFL21; CMS20; Awo26]).$^{5}$

1.6. **Results.** Our results are summarized by the following theorem.

**Theorem 1.6.1.** *There is a constructively definable model of HoTT in cartesian cubical sets with an associated constructively definable Quillen model structure that is classically Quillen equivalent to the Kan–Quillen model structure on simplicial sets.*

By *associated Quillen model structure*, we mean as in §1.3 a model structure whose fibrations are the retracts of context extensions of the model of HoTT and whose trivial fibrations are the retracts of context extensions by contractible types.

By a *model of HoTT* we mean a model of Martin-Löf type theory validating the univalence axiom, and by *model of Martin-Löf type theory* we mean a natural model [Awo18b] equipped with $\Pi$-types, $\Sigma$-types, identity types, and universes closed under these. More precisely, what we construct is a *natural pseudo-model* in the sense of Shulman [Shu19, §A] with weakly stable equivalents of this structure (a weakly stable class of $\Pi$-types, etc.); one can then apply Lumsdaine and Warren's *left adjoint splitting* coherence construction [LW15; Awo18b; Shu19, §A] to obtain a natural model with strictly stable structure. Concretely, our category of contexts is the category $\mathsf{cSet}$ of cartesian cubical sets, and the natural pseudo-model specifying the types and terms is the *notion of fibred structure* encoding the equivariant fibrations (Lemma 5.3.3). The interpretation of type formers is as follows.

- Weakly stable $\Sigma$-types and identity types arise immediately from the model structure (see, e.g., [LW15, §4.2]). $\Sigma$-types are interpreted by composition of fibration algebras, while the identity type on $A \to \Gamma$ is interpreted by the (trivial cofibration, fibration) factorization of its diagonal $A \to A \times_\Gamma A$ (as in [AW09]).
- Weakly stable $\Pi$-types come from the *Frobenius condition* [BG12, 3.3.3; GS17], that is the closure of fibrations under pushforward along fibrations, which is verified in Proposition 5.3.2.
- Universes are interpreted by classifiers for the notions of fibred structure encoding $\kappa$-small equivariant fibrations for sufficiently large inaccessible cardinals $\kappa$ (Proposition 5.3.7). Importantly,

$^{5}$Interestingly, while the equivariant premodel structure is lifted along a right adjoint, the constant functor $\Delta: \mathsf{cSet} \to \mathsf{cSet}^2$, the model structure itself is not: the fibrations and trivial fibrations are created by $\Delta$, but the weak equivalences between non-fibrant objects are not.

7

these classifiers have fibrant base objects (Proposition 5.3.9) and are univalent (Proposition 5.3.8).

The former property is closely connected to the model-categorical *fibration extension property* (Proposition 5.3.10), the latter to the *equivalence extension property* (Proposition 5.3.1).

The main technical work lies in the construction of univalent universes.

In the course of proving the main theorem, we actually construct *two* models of homotopy type theory and associated Quillen model structures: a model on the category $\mathsf{cSet}^{\Sigma}$ of cubical species, which does not model classical homotopy theory, and a model on $\mathsf{cSet}$, which does. To avoid repetition and with an eye towards future applications, we prove the core theorems that will establish the necessary properties of these model categories in more general axiomatic settings, proving results that are of independent interest.

1.6.1. *Outline.* Our development proceeds as follows.

- In §2, we recall Shulman's *notions of fibred structure*, which in particular include categories of right maps obtained from an algebraic weak factorization system. Again following Shulman, we define a *universe* for a notion of fibred structure to be a representable "resolution" via an acyclic fibration. We define our first example of a notion of fibred structure, the *uniform trivial fibrations*, following [Awo26].
- In §3, we work in the abstract setting of a *cylindrical premodel structure* as defined in [Sat20; CS25, §3]. We establish, individually, sufficient conditions under which a cylindrical premodel structure
  - satisfies the equivalence extension property;
  - satisfies the Frobenius condition,
  - supports fibrant and univalent universes of fibrations;
  - defines a Quillen model structure.

These constructions form the backbone of existing model-categorical cubical interpretations and could be applied with appropriate inputs from [ABCHFL21] or [Awo26] to recover the known model structures on, e.g., cartesian or De Morgan cubical sets. In the following sections, we apply them to two cylindrical premodel structures: first to $\mathsf{cSet}^{\Sigma}$ and then to $\mathsf{cSet}$ itself. As a rule of thumb, properties whose proofs rely only on *closure* properties of fibrations (such as the equivalence extension property) are derived directly in $\mathsf{cSet}$, while properties whose proofs rely on the *generation* of fibrations by box filling (such as the Frobenius condition) are first proven in $\mathsf{cSet}^{\Sigma}$ and then transferred to $\mathsf{cSet}$.

- In §4, we introduce the category $\mathsf{cSet}^{\Sigma}$ of cubical species. We define the *symmetric interval* $\mathbb{I} \in \mathsf{cSet}^{\Sigma}$ and use it to define, by essentially the same construction used for the ordinary cartesian cubical set model [ABCHFL21; CMS20; Awo26], a model of HoTT and Quillen model structure on $\mathsf{cSet}^{\Sigma}$.
- In §5, we transfer the cylindrical premodel structure on $\mathsf{cSet}^{\Sigma}$ to $\mathsf{cSet}$ by means of the constant functor $\Delta: \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$, defining the equivariant (trivial) fibrations to be those sent to (trivial) fibrations in $\mathsf{cSet}^{\Sigma}$ by $\Delta$. We show that this premodel structure satisfies 2-of-3, proving the first part of Theorem 1.6.1: the existence of a constructively definable model of HoTT and associated Quillen model structure on $\mathsf{cSet}$ whose fibrations are the equivariant fibrations.
- In §6, we prove the second part of Theorem 1.6.1, building a Quillen equivalence between the equivariant model structure on $\mathsf{cSet}$ and the Kan–Quillen model structure on $\mathsf{sSet}$. The left adjoint of this equivalence is the triangulation functor $T: \mathsf{cSet} \to \mathsf{sSet}$ mentioned above; we rely on a characterization, due to Reid Barton, of $T$ as restriction along a functor $i: \Delta \to \square$. Key to the proof is that $\Delta$ and $\square$ are *Eilenberg–Zilber categories*, which implies that the monomorphisms in their respective presheaf categories are cell complexes of quotients by automorphism groups of boundary inclusions into representables. In this way, the fact that $T$ reflects weak equivalences comes to rest on the contractibility of the quotients $I/H \in \mathsf{cSet}$, which we have seen in §1.5.2 is

8

ensured by the definition of equivariant fibration. Using the Quillen equivalence, we also prove that our model structure on cSet coincides with the test model structure.

Finally, we devote an appendix (§A) to a second perspective on the construction of the equivariant model of HoTT in cSet. There we outline a translation of HoTT into the internal extensional type theory of cubical sets augmented by an axiomatisation of the interval and cofibration classifier, which is backed by a complete formalisation in the proof assistant Agda [ACCRS24] following Orton and Pitts [OP18]. This also demonstrates that, as usual for cubical models of HoTT, a coherence construction is not actually needed to obtain a model of Martin-Löf type theory: our types are sufficiently structured to directly interpret strictly stable structure (without the need to, e.g., choose lifts).

1.6.2. *Constructivity*. Part of the aim of this paper is to describe a *constructive* model of HoTT. Thus §§2–5, which culminate in the construction of the equivariant model of HoTT and Quillen model structure on cSet, can be made completely constructive. Note, however, that one must replace the use of monomorphisms in presheaf categories everywhere with *levelwise decidable monomorphisms*, that is, $m \in (\mathsf{Set}^{\mathsf{Cop}})^2$ such that $m_c$ is isomorphic to a coproduct coprojection for all $c \in \mathsf{C}$. Constructively, the Hofmann–Streicher classifiers form universes in the sense of §2.3 only with this modification, as used in the CCHM model [CCHM15, 15] and observed explicitly by Orton and Pitts [OP18, 8.4]. Note that this replaces the subobject classifier with a classifier for subobjects whose corresponding sieve is decidable. This also has the effect of making the development *predicative*.

We justify constructivity of our use of Garner’s algebraic small object argument in Constructions 2.2.13, 4.3.6, 5.2.1, and 5.2.4. Note that the set of morphisms of the cartesian cube category $\square$ has decidable equality. The Eilenberg–Zilber category structure on $\square$ is constructively definable and has finite slices of face maps. By induction, we show that any object $S$ with a levelwise decidable inclusion into $\upharpoonright a$ with $a \in \square$ is compact: if this map contains the generic element of $\upharpoonright a$, then $\supseteq S \simeq \upharpoonright a$ is representable; otherwise, it is a finite cell complex of boundary inclusions of degree lower than $a$. Note that any double left adjoint preserves compact objects. The generating (trivial) cofibrations in cubical species are levelwise decidable subobjects of representables. By Lemma 4.3.1, these arise via left Kan extension from levelwise decidable subobjects of representables in cubical sets. Then the generating (trivial) cofibrations in cubical sets are created from these via the double left adjoint $L$ in §5.1. Therefore, all the generating categories for each of our uses of the algebraic small object argument consist of maps with compact domain. This makes the pointed endofunctor for the one-step factorization preserve filtered colimits. Hence, its free monad sequence converges at stage $\omega$. For more details on the algebraic small object argument in a constructive context, we refer to Henry [Hen25, §C.2].

The Kan–Quillen model structure on simplicial sets is definable constructively [Hen25; GSS22a]. However, our proof of the Quillen equivalence between the equivariant model structure and the Kan–Quillen model structure in §6 is not constructive. In its heart, it relies on the non-constructive presentation of (levelwise decidable) monomorphisms in cSet as Reedy cell complexes. Constructively, only the *Reedy decidable* monomorphisms—that is, those whose latching maps are decidable—can be presented in this way (compare [GSS22a, §1.4]). While it may be possible to define an analogue of the equivariant fibration model structure with Reedy decidable monomorphisms as cofibrations (as in [Hen25; GSS22a] for simplicial sets), this choice interferes with coherence constructions used to interpret HoTT, as Gambino and Henry find [GH22, 8.5].

It is more generally unclear how to judge whether a homotopy theory is “the homotopy theory of spaces” constructively. Indeed, it is likely that there are multiple constructively distinct homotopy theories that are all classically equivalent to the Kan–Quillen model structure. Shulman does some preliminary analysis of this question through the lens of *derivators* [Shu23].

## 1.7. Related and future work.

9

1.7.1. *Models of HoTT in higher toposes.* Shulman has shown that every Grothendieck $\infty$-topos admits a presentation by a *type-theoretic model topos*, a Quillen model category with structure sufficient to interpret HoTT [Shu19]. His setup uses classical logic and is inherently simplicial: a type-theoretic model topos is by definition a simplicial model category. As far as we know, our model structure falls outside of this framework: we are not aware of any appropriate simplicial enrichment on cSet. The natural candidate definition, taking the mapping space between $X, Y \in \text{cSet}$ to be the triangulated internal hom $T[X, Y] \in \text{sSet}$, does not yield a simplicial model structure, essentially because the left adjoint to $T$ (constructed in §6) does not preserve products.

Shulman uses the description of Grothendieck $\infty$-toposes as left exact localizations of presheaf $\infty$-toposes, showing that the class of type-theoretic model toposes is closed under model-categorical constructions presenting left exact localizations and categories of presheaves. The base case is then the $\infty$-topos of spaces: the category of simplicial sets with the Kan–Quillen model structure is a type-theoretic model topos. Our work suggests a future path towards constructivizing (at least some of) Shulman's results, namely by developing a *cubical* notion of type-theoretic model topos and using the equivariant model structure on cSet as the base model of spaces.

1.7.2. *Other cubical models.* In 2022, the second and fifth author discovered a second cubical interpretation of type theory whose associated Quillen model structure presents spaces, this one in presheaves on the category of *cartesian cubes with one connection* [CS25]. In this setting, it is not necessary to introduce the notion of equivariant fibration: applying the original cartesian cubical model construction as in [ABCHFL21; CMS20; Awo26] yields a Quillen model structure presenting spaces. This can be explained by the fact that any fibration in presheaves over this cube category is *automatically* equivariant, as sketched in [CS25, 4.25] (compare our Proposition 6.1.7). A downside of this model is that the cube category with one connection is less well-behaved: while the cartesian cube category is an Eilenberg–Zilber category [Cam23, 8.12(1)], the cube category with one connection is not a Reedy category [CS25, §A.1]. The main task of [CS25] is to develop a generalization of Eilenberg–Zilber category which can be used in this case.

Equivariance is not a catch-all solution: it is not the case that we can take any of the existing cubical interpretations and impose an equivariance condition on fibrations to obtain a model for spaces. For example, as in the one connection case, fibrations in Dedekind cubical sets (i.e., over the cartesian cube category with two connections) are automatically equivariant, but we still do not know if this model presents spaces, essentially because this cube category is even farther from being an Eilenberg–Zilber category than the one-connection category [CS25, §A.2]. Over the BCH cube category, which *is* an Eilenberg–Zilber category [Cam23, 7.10], adding equivariance would have the effect of making the cube quotients $I_H^n$ contractible, as it does in cartesian cubical sets. This is desirable from the point of view of triangulation. Note however that in the test model structure on BCH cubical sets, the quotient $I_{\Sigma_2}^2$ is *not* contractible but rather presents the suspension of $\mathbb{R}P^\infty$.

1.7.3. *Constructive simplicial models.* The Kan–Quillen model structure on simplicial sets has been developed constructively by Henry [Hen25] and Gambino, Sattler, and Szumilo [GSS22a]. However, Bezem, Coquand, and Parmann show that Voevodsky's model in simplicial sets relies in an essential way on classical principles [BC15; BCP15; Par18]. Essentially, this is because the Kan–Quillen model structure cannot generally be shown to have cofibrant objects; indeed, the cofibrant objects are the *Reedy decidable objects*, those for which we can decide if a cell is degenerate. In particular, the interpretation of $\Pi$-types is problematic: constructively, the exponential $Y^X$ need not be a Kan complex even if $X$ and $Y$ are—cofibrancy of $X$ is required.

As mentioned in §1.6.2, Gambino and Henry [GH22] give a constructive reformulation of Voevodsky's simplicial model of HoTT in *cofibrant simplicial sets*. However, the restriction to cofibrant objects interferes with the coherence constructions needed to obtain a strict model, meaning that the end result falls short of its classical equivalent.

10

Van den Berg and Faber [BF22] present a second approach to constructivizing Voevodsky's model replacing Kan fibrations with a restricted notion of *effective Kan fibration*. As in our own work, the idea is to impose additional uniformity conditions on lifts. Although this approach does not require restricting cofibrations to Reedy decidable monomorphisms and thus may avoid the coherence issues of [GH22], it is still work in progress: to our knowledge, neither an interpretation of universes nor a Quillen model structure have been established thus far.

1.7.4. *Cubical type theories.* Cohen, Coquand, Huber, and Mörtberg [CCHM15] present not only a model of homotopy type theory but also a *cubical type theory*, an extension of Martin-Löf type theory with new judgments and type formers that reflect the structure of the De Morgan cubical sets model. Angiuli et al. [AFH18; ABCHFL21] likewise devise a cubical type theory interpreting in cartesian cubical sets. Unlike HoTT as formulated in [UF13], these theories enjoy canonicity: any closed natural number computes definitionally to a numeral [AFH18; Hub19].

The cartesian cubical type theory of [ABCHFL21] can also be interpreted in the equivariant cartesian model: every equivariant fibration is in particular a fibration in the sense of the original cartesian cubical set model, so interprets the filling operator (sometimes also called the *composition* operator) of cartesian cubical type theory [ABCHFL21, §1.2]. Thus, cartesian cubical type theory has a model presenting the homotopy theory of spaces.

One could imagine extending cartesian cubical type theory with an equivariant filling operator. Such an operator could be introduced by the rule

$$\begin{array}{c} k \in \mathbb{N} \quad \Gamma, \vec{r}: I^k \vdash A \text{ type} \quad \Gamma \vdash \phi \text{ cof} \quad \Gamma \vdash \vec{r}, \vec{s}: I^k \\ \Gamma, \phi, \vec{r}: I^k \vdash u: A \quad \Gamma \vdash u_0: A[\vec{r}/\vec{r}] \quad \Gamma, \phi \vdash u[\vec{r}/\vec{r}] = u_0: A \\ \hline \Gamma \vdash \text{comp}_{\vec{r},A}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0: A[\vec{r}/\vec{r}] \end{array}$$

which straightforwardly generalizes the ordinary filling operator by replacing the interval $I$ with an arbitrary $k$-cube $I^k$, together with the usual equations

$$\begin{array}{ll} \text{comp}_{\vec{r},A}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0 = u[\vec{s}/\vec{r}] & \text{when } \phi \text{ holds} \\ \text{comp}_{\vec{r},A}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0 = u_0 & \text{when } \vec{r} = \vec{s} \end{array}$$

which specify that the output of comp is a filler for the input box. *Equivariance* states that, for each $\sigma \in \Sigma_k$, we have the equation

$$\text{comp}_{\vec{r},A}^{\sigma^* \vec{r} \rightarrow \sigma^* \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0 = \text{comp}_{\vec{j},A[\sigma^* \vec{j}/\vec{r}]}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{j}.u[\sigma^* \vec{j}/\vec{r}]] \ u_0,$$

where $\sigma^*$ is the action of $\sigma$ on $k$-tuples of terms in $I$.

We are, however, not aware of any practical use for the equivariant filling operator in cubical type theory. Synthetic homotopy theorists working in cubical type theories have yet to encounter any fundamental difference in expressivity between, e.g., cartesian and De Morgan cubical type theories, or even between cubical type theories and HoTT à la [UF13], and the situation seems to be the same here. It would also be expensive and complicated to type-check equivariant filling operators: to compare two $k$-dimensional comp terms for equality requires testing whether they agree modulo any of the $k!$ permutations.

1.8. **Acknowledgments.** The discovery of the equivariant model occurred at the Centre for Advanced Study (CAS) at the Norwegian Academy of Science and Letters in Oslo, Norway, in the academic year 2018–19 research project on Homotopy Type Theory and Univalent Foundations organized by Marc Bezem and Bjørn Dundas. We gratefully acknowledge their support. The first and third authors are also grateful to the Institut des Hautes Études Scientifiques for hosting two weeks of very nice discussions in June 2022.

The perspective of the generating categories of cofibrations and trivial cofibrations as internally indexed by cubical species (see §4.3) was informed by discussions with Andrew Swan. Reid Barton's

11

recent insights into the triangulation functor enabled us to considerably simplify the proofs of the results in §6.

The first and fourth author were supported by the US Air Force Office of Scientific Research under award number FA9550-21-1-0009 as well as, for the first author, award number FA9550-20-1-0305. The second author was supported by the US Air Force Office of Scientific Research under award number FA9550-19-1-0216 and by the Knut and Alice Wallenberg Foundation (KAW) under grant numbers 2020.0266 and 2019.0116. The third author was supported by the ForCUTT project, ERC advanced grant number 101053291. The fourth author is also supported by US National Science Foundation via the grants DMS-2204304 and DMS-2507077 and by the President's Frontier Award at Johns Hopkins, which supported visits to the other authors. The fifth author was supported by the Swedish Research Council under grant number 2019-03765 and the US Air Force Office of Scientific Research under award number FA9550-24-1-0302.

## 2. NOTIONS OF FIBRED STRUCTURE AND UNIVERSES

A (model-categorical) model of HoTT comes with two classes of “right” maps: the *fibrations*, which model type families, and the *trivial fibrations*, which model contractible type families. A key feature of both classes of maps is their stability under pullbacks along arbitrary maps, which models substitution of terms for variables in type theory.

In this section, we consider such “notions of fibred structure” abstractly, proving general results that will apply to both the fibrations and the trivial fibrations in the model categories we construct. In §2.1, we recall the precise, technical meaning of the phrase “notion of fibred structure” and explore what it means when such fibred structure is *locally representable*. In §2.2, we specialize to elementary toposes and show that suitably structured maps that lift against the monomorphisms define a locally representable notion of fibred structure. In §2.3, introduce our notion of universe and, in the case of presheaf toposes, construct universes for locally representable notions of fibred structure from the Hofmann–Streicher classifiers.

2.1. **Locally representable and relatively acyclic notions of fibred structure.** The maps in a 1-category $\mathsf{E}$ with pullbacks assemble into a contravariant groupoid-valued pseudofunctor on $\mathsf{E}$ sending an object $X$ to the large groupoid of maps with codomain $X$. This pseudofunctor $\mathfrak{E}$ is referred to as the **core of self-indexing**—the “self-indexing” referring to the slice categories $\mathsf{E}_{/X}$ and the “core” referring to their groupoid cores. In [Shu19, 3.1], Shulman defines a **notion of fibred structure** on a category $\mathsf{E}$ with pullbacks as a strict discrete fibration with small fibers $\psi: \mathfrak{F} \rightarrow \mathfrak{E}$ in the 2-category of contravariant groupoid-valued pseudofunctors on $\mathsf{E}$ and pseudonatural transformations between them. Here, a *strict discrete fibration* is a strictly natural transformation whose components are fibrations of groupoids.

Unpacking this, a notion of fibred structure is given by:

- (i) for each map $f: Y \rightarrow X$ of $\mathsf{E}$, a set of “fibration structures”,

$$\begin{array}{c} W \xrightarrow{f^* g} Y \\ g^* f \downarrow \quad \downarrow f \\ Z \xrightarrow{g} X, \end{array} \tag{2.1.1}$$

a function from the set of fibration structures on $f$ to the set of fibration structures on $g^* f$ that is pseudofunctorial in pullback squares.

See [Shu19, §3] for considerably more discussion. Following Shulman, we refer to the “structured fibrations” associated to a notion of fibred structure $\mathfrak{F}$ as **$\mathfrak{F}$-algebras** and then refer to a pullback

12

square (2.1.1) in which the $\mathfrak{F}$-algebra structure on $g^*f$ is induced from the $\mathfrak{F}$-algebra structure on $f$ as an $\mathfrak{F}$-morphism.

**Definition 2.1.2** ([Shu19, 3.2]). A notion of fibred structure $\psi \colon \mathfrak{F} \to \mathfrak{E}$ is **full** if $\mathfrak{F}(X) \to \mathfrak{E}(X)$ is fully faithful for each object $X$ of $\mathsf{E}$.^6

That is, $\mathfrak{F}$ is full if every pullback square between $\mathfrak{F}$-algebras uniquely extends to an $\mathfrak{F}$-morphism.

Shulman then axiomatizes various conditions associated to such a notion of fibred structure that can be used to build a classifying universe. The first of these conditions is the following:

**Definition 2.1.3** ([Shu19, 3.10]). A notion of fibred structure $\mathfrak{F}$ is **locally representable** if each pullback in the category of contravariant groupoid-valued pseudofunctors

$$\begin{array}{c} \bullet \xrightarrow{\quad} \mathfrak{F} \\ \downarrow \quad \downarrow \quad \downarrow \psi \\ \mathsf{E}(-, X) \xrightarrow[f]{} \mathfrak{E} \end{array}$$

is representable. Explicitly, every map $f \colon Y \to X$ has a *classifier* $\psi_f \colon \mathfrak{F}(f) \to X$ for $\mathfrak{F}$-algebra structures on $f$, meaning that that for all $g \colon Z \to X$, $\mathfrak{F}$-algebra structures on $g^*f$ correspond bijectively to lifts of $g$ through $\psi_f$, naturally in $g$:

$$\begin{array}{c} \mathfrak{F}(f) \\ \downarrow \quad \downarrow \psi_f \\ Z \xrightarrow[g]{} X. \end{array}$$

In particular, sections of the canonical map $\psi_f \colon \mathfrak{F}(f) \to X$ correspond uniquely to $\mathfrak{F}$-algebra structures on $f \colon Y \to X$.

**Lemma 2.1.4.** *Let $\mathfrak{F}$ be a locally representable notion of fibred structure.*

- (i) The pullback of any map $f \colon Y \to X$ along $\psi_f \colon \mathfrak{F}(f) \to X$ has a canonical $\mathfrak{F}$-algebra structure.
- (ii) If $g^*f$ is a pullback of $f$ along $g$, then $\mathfrak{F}(g^*f)$ is a pullback of $\mathfrak{F}(f)$ along $g$, i.e. $\mathfrak{F}(g^*f) \cong g^*\mathfrak{F}(f)$.

*Proof.* The top horizontal map in the pullback square

$$\begin{array}{c} \mathsf{E}(-, \mathfrak{F}(f)) \xrightarrow{\gamma_f} \mathfrak{F} \\ \downarrow \quad \downarrow \quad \downarrow \psi \\ \mathsf{E}(-, X) \xrightarrow[f]{} \mathfrak{E} \end{array}$$

specifies an $\mathfrak{F}$-algebra structure $\gamma_f$ on the map $\psi_f^*f$.

By pullback cancelation and fully faithfulness of the Yoneda embedding, local representability implies that the left-hand square is a pullback in contravariant groupoid-valued pseudofunctors and thus also in $\mathsf{E}$:

$$\begin{array}{c} \mathsf{E}(-, \mathfrak{F}(g^*f)) \xrightarrow{i_g} \mathsf{E}(-, \mathfrak{F}(f)) \xrightarrow{\gamma_f} \mathfrak{F} \\ \downarrow \quad \downarrow \quad \downarrow \psi_f \\ \mathsf{E}(-, Z) \xrightarrow[g]{} \mathsf{E}(-, X) \xrightarrow[f]{} \mathfrak{E}. \end{array}$$

^6 Shulman's definition asks that $\psi \colon \mathfrak{F} \to \mathfrak{E}$ is a subfunctor inclusion; this is equivalent because $\psi$ is a discrete fibration.

13

Remark 2.1.5. Recall that a pullback of $\mathfrak{F}$-algebras as in (ii) is an $\mathfrak{F}$-morphism just when the $\mathfrak{F}$-algebra structure on $g^*f$ is created from the $\mathfrak{F}$-algebra structure on $f$. The naturality condition in Definition 2.1.3 tells us that this is the case just when the square defined by the corresponding sections of the representing morphisms commute:

$$\begin{array}{c} \mathfrak{F}(g^*f) \xrightarrow{i_g} \mathfrak{F}(f) \\ \psi_{g^*f} \Big\downarrow \Big\downarrow^{r_s g^*f} \qquad s_f \Big\uparrow \Big\downarrow \psi_f \\ Z \xrightarrow{g} X. \end{array}$$

A large family of examples of locally representable notions of fibred structure are considered in [Shu19, §3]. We mention just one, which will be applied in the following section.

Example 2.1.6 ([Shu19, 3.7,3.14]). From a functorial factorization on $\mathsf{E}$ one obtains a notion of fibred structure $\mathfrak{F}$ whose $\mathfrak{F}$-algebras are maps with chosen solutions to the canonical lifting problem against their left factor:

$$\begin{array}{c} Y \xlongequal{\quad} Y \\ Lf \Big\downarrow \quad \Big\downarrow^{j_f} \quad \Big\downarrow^{r_s} \\ Ef \xrightarrow{Rf} X. \end{array}$$

If $\mathsf{E}$ is locally cartesian closed and the functorial factorization is cartesian, in the sense that the functors $L, R \colon \mathsf{E}^2 \to \mathsf{E}^2$ carry pullback squares to pullback squares, then this notion of fibred structure is locally representable. Explicitly, $j^f$ may be encoded as an element in the internal hom $[Rf, f]_X := (Rf)_*(Rf)^*f$ from $Rf$ to $f$ in $\mathsf{E}_{/X}$

$$\begin{array}{c} X \xrightarrow{j^f} \Pi_{Ef}(Ef \times_X Y) \\ \searrow \quad \swarrow \\ X \xleftarrow{[Rf,f]_X} \end{array}$$

which restricts along $Lf$ to the identity at $Y$. Thus, we define $\phi_f \colon \mathfrak{F}(f) \to X$ to be the pullback

$$\begin{array}{c} \mathfrak{F}(f) \xrightarrow{\quad} \Pi_{Ef}(Ef \times_X Y) \\ \phi_f \Big\downarrow \quad \Big\downarrow^{-\circ L_f} \\ X \xrightarrow{\text{id}_Y} \Pi_Y(Y \times_X Y) \end{array}$$

of this restriction map.$^7$

Definition 2.1.7 ([Shu19, 5.11]). A notion of fibred structure $\mathfrak{F}$ is relatively acyclic if for any pullback square

$$\begin{array}{c} Y' \xrightarrow{i'} Y \\ f' \Big\downarrow \quad \Big\downarrow^{J} \quad \Big\downarrow^{f} \\ X' \xrightarrow{i} X \end{array}$$

with $\mathfrak{F}$-algebra structures $x$ on $f$ and $x'$ on $f'$, there is an $\mathfrak{F}$-algebra structure $\overline{x}$ on $f$ making the square an $\mathfrak{F}$-morphism from $x'$ to $\overline{x}$.

$^7$The map $-\cdot L_f$ is the restriction between internal homs in the cartesian closed category $\mathsf{E}_{/X}$. A construction of this map in $\mathsf{E}$ may be found in [HR24, 3.9].

14

Recall from [Shu19, 2.8] the bicategorical notion of lifting property in a 2-category K: morphisms $i: A \to B$ and $f: Y \to X$ have the lifting property when the map $\mathsf{K}(B, Y) \to \mathsf{K}(A, Y) \times_{\mathsf{K}(A, X)}^h \mathsf{K}(B, X)$ is essentially surjective, where $\times^h$ is a weak bicategorical pullback.

**Definition 2.1.8** ([Shu19, 5.1]). A morphism in contravariant groupoid-valued pseudofunctors on $\mathsf{E}$ is an **acyclic fibration** if it right lifts bicategorically against images of monomorphisms under the Yoneda embedding.

*Remark 2.1.9.* For strict discrete fibrations in contravariant groupoid-valued pseudofunctors on $\mathsf{E}$, the bicategorical right lifting property is equivalent to the categorical right lifting property [Shu19, 2.10]. In particular, this applies to notions of fibred structure and their pullbacks.

**Lemma 2.1.10.** *Given a notion of fibred structure $\psi: \mathfrak{F} \to \mathfrak{E}$, the following conditions are equivalent:*

(i) $\psi: \mathfrak{F} \to \mathfrak{E}$ is relatively acyclic,

(ii) each kernel pair projection of $\psi$ is an acyclic fibration.

*Proof.* For a diagram

$$\begin{array}{c} Y' \xrightarrow{i'} Y \\ f' \downarrow \quad \downarrow \quad \downarrow f \\ X' \xrightarrow{i} X, \end{array} \tag{2.1.11}$$

a pair of $\mathfrak{F}$-algebra structures on $f$ and $f'$ consists of a pair of maps $x: \mathsf{E}(-, X) \to \mathfrak{F}$ and $x': \mathsf{E}(-, X') \to \mathfrak{F}$ such that the outer square

$$\begin{array}{c} \mathsf{E}(-, X') \xrightarrow{\quad} \mathfrak{F} \times_{\mathfrak{E}} \mathfrak{F} \xrightarrow{\quad} \mathfrak{F} \\ i \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \mathsf{E}(-, X) \xrightarrow{\quad} \mathfrak{F} \xrightarrow{\quad} \mathfrak{F}, \end{array}$$

commutes, i.e., corresponds to a lifting problem against the kernel pair of $\psi$. A solution to such a lifting problem is determined by a map $\overline{x}: \mathsf{E}(-, X) \to \mathfrak{F}$ such that $\overline{x}i = x'$ and $\psi\overline{x} = \psi x$, which is to say an $\mathfrak{F}$-algebra structure on $f$ such that (2.1.11) is an $\mathfrak{F}$-morphism from $x'$ to $\overline{x}$. $\square$

**Lemma 2.1.12.** *When $\mathfrak{F}$ is a locally representable and relatively acyclic notion of fibred structure on $\mathsf{E}$ then for any map $f: Y \to X$ the maps in the kernel pair of $\psi_f: \mathfrak{F}(f) \to X$ lift against monomorphisms in $\mathsf{E}$.*

*Proof.* Recall the definition of the maps in question:

$$\begin{array}{c} \mathsf{E}(-, \mathfrak{F}(f)) \longrightarrow \mathfrak{F} \\ \psi_f \downarrow \quad \downarrow \quad \downarrow \psi \\ \mathsf{E}(-, X) \xrightarrow{f} \mathfrak{E}. \end{array}$$

As the kernel pair of a pullback is the pullback of the kernel pair, the kernel pair of the representable map $\psi_f: \mathsf{E}(-, \mathfrak{F}(f)) \to \mathsf{E}(-, X)$ lifts against representable monomorphisms. But since the Yoneda embedding is fully faithful and preserves limits, this means that the kernel pair of the map $\psi_f: \mathfrak{F}(f) \to X$ lifts against monomorphisms in $\mathsf{E}$. $\square$

By Lemma 2.1.10, a full notion of fibred structure, such as the following example, is automatically relatively acyclic.

15

Example 2.1.13 ([Lur09, 6.1.6.4–7][Shu19, 4.18]). For any locally presentable and locally cartesian closed category E, for sufficiently large regular cardinals  \( \kappa \) , the relatively  \( \kappa \) -presentable morphisms form a locally representable and relatively acyclic full notion of fibred structure  \( E^{\kappa} \) .⁸

Locally representable notions of fibred structure may also be transferred from one category to another via various devices. Here we make use of a transfer result involving the Leibniz construction of [RV14, §4–5], deployed in the following setting.

Definition 2.1.14. Consider the application bifunctor

\[
\mathsf {E} ^ {\mathsf {D}} \times \mathsf {D} \xrightarrow {\circ} \mathsf {E}
\]

\[
(F, X) \longmapsto F X
\]

associated to a pair of categories D and E. Assuming E has pushouts and pullbacks, this induces Leibniz pushout application and Leibniz pullback application bifunctors

\[
\mathsf {E} ^ {\mathsf {D} \times 2} \times \mathsf {D} ^ {2} \xrightarrow {\delta} \mathsf {E} ^ {2} \quad \mathsf {E} ^ {\mathsf {D} \times 2} \times \mathsf {D} ^ {2} \xrightarrow {\delta} \mathsf {E} ^ {2}
\]

which, respectively, send a natural transformation \(\alpha \colon F \Rightarrow G\) and an arrow \(f \colon Y \to X\) to the induced maps in the naturality squares:

![img-3.jpeg](img-3.jpeg)

![img-4.jpeg](img-4.jpeg)

Lemma 2.1.15. Suppose D and E have weak factorization systems  \( (\mathcal{L},\mathcal{R}) \)  and  \( (\mathcal{M},\mathcal{E}) \)  respectively. Then the Leibniz pushout application of a natural transformation  \( \alpha\colon F\Rightarrow L \)  between left adjoints preserves the left classes if and only if the Leibniz pullback application of the conjugate natural transformation  \( \alpha\colon R\Rightarrow U \)  between the right adjoints preserves right classes.

Proof. Write  \( \operatorname{Ladj}(\mathsf{D},\mathsf{E})\subset\mathsf{E}^{\mathsf{D}} \)  and  \( \operatorname{Radj}(\mathsf{E},\mathsf{D})\subset\mathsf{D}^{\mathsf{E}} \)  for the full subcategories spanned by the left and right adjoint functors, respectively. Note we have an equivalence of categories  \( \operatorname{Ladj}(\mathsf{D},\mathsf{E})^{\mathrm{op}}\simeq\operatorname{Radj}(\mathsf{E},\mathsf{D}) \)  which exchanges left and right adjoints and conjugate transformations. Moreover, via this equivalence, the restricted application bifunctors

\[
\operatorname{Ladj} (D, E) \times D \xrightarrow {\circ} E \quad \operatorname{Radj} (E, D) \times E \xrightarrow {\circ} D
\]

are parametrized adjoints. Thus, by [RV14, 4.10, 4.11], the Leibniz pushout application of left adjoints bifunctor and Leibniz pullback application of right adjoints bifunctor are parametrized adjoints, inducing a bijective correspondence between lifting problems:

![img-5.jpeg](img-5.jpeg)

for \(\ell\colon A\to B\) in \(\mathcal{L}\) and \(e\colon Y\to X\) in \(\mathcal{E}\). The claim follows.

\( ^{8} \) In a presheaf topos  \( E = Set^{Cop} \)  where C is  \( \kappa \) -small, the relatively  \( \kappa \) -presentable morphisms coincide with the  \( \kappa \) -small morphisms, those maps whose fibers have cardinality less than  \( \kappa \)  [Shu19, 4.10].

16

**Lemma 2.1.16.** Suppose $\mathsf{E}$ and $\mathsf{E}'$ have pullbacks, $\alpha : L \Rightarrow K : \mathsf{E}' \to \mathsf{E}$ is a natural transformation between pullback-preserving functors, and $L$ has an indexed right adjoint:

![img-6.jpeg](img-6.jpeg)

![img-7.jpeg](img-7.jpeg)

Then if $\mathsf{E}$ has a notion of fibred structure $\mathfrak{F}$, then $\mathsf{E}'$ has a notion of fibred structure $\mathfrak{F}'$ in which $\mathfrak{F}'$-algebras are created from $\mathfrak{F}$-algebras under the Leibniz pullback application of $\alpha$. Moreover,

- (i) if $\mathfrak{F}$ is relatively acyclic, so is $\mathfrak{F}'$, and
- (ii) if $\mathsf{E}$ is locally cartesian closed and $\mathfrak{F}$ is locally representable, so is $\mathfrak{F}'$.

Proof. Since the functor $\alpha \circ - : (\mathsf{E}')^2 \to \mathsf{E}^2$ preserves pullbacks, $\mathfrak{F}'$ defines a notion of fibred structure on $\mathsf{E}'$. Since $L$ and $K$ preserve pullbacks, they preserve monomorphisms, so the functor $\alpha \circ -$ preserves the monomorphisms in Definition 2.1.7, and thus if $\mathfrak{F}$ is relatively acyclic, so is $\mathfrak{F}'$.

It remains to verify local representability. To that end, consider a pullback in $\mathsf{E}'$

$$\begin{array}{c} W \xrightarrow{f^*g} Y \\ g^*f \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } f \\ Z \xrightarrow{g} X \end{array}$$

inducing a pullback in $\mathsf{E}$ as below-left:

$$\begin{array}{c} LW \xrightarrow{Lf^*g} LY \\ \alpha \circ g^*f \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ KW \times_{KZ} LZ_{Kf^*g \times_{Kg}Lg} KY \times_{KX} LX \end{array}$$

$$\begin{array}{c} \mathfrak{F}(\alpha \circ g^*f) \longrightarrow \mathfrak{F}(\alpha \circ f) \\ \phi_{\alpha \circ g^*f} \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ KW \times_{KZ} LZ_{Kf^*g \times_{Kg}Lg} KY \times_{KX} LX. \end{array}$$

By definition $\mathfrak{F}'$-algebra structures on $g^*f$ correspond to $\mathfrak{F}$-algebra structures on $\alpha \circ g^*f$. Since $\mathfrak{F}$ is locally representable, these correspond to sections and thus lifts in the pullback square above-right constructed in Lemma 2.1.4. Transposing across the pullback $\dashv$ pushforward adjunction associated to the projection $\alpha_X^*Kf : KY \times_{KX} LX \to LX$, such dashed lifts correspond bijectively to lifts as below-left

$$\begin{array}{c} \Pi\mathfrak{F}(\alpha \circ f) \\ LZ \xrightarrow{\quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad LX \end{array}$$

$$\begin{array}{c} \mathfrak{F}'(g^*f) \longrightarrow R_X \Pi\mathfrak{F}(\alpha \circ f) \\ \psi_{g^*f} \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } R_X(\alpha_X^*Kf)_*\phi_{\alpha \circ f} \\ Z \xrightarrow{g} X, \end{array}$$

and since $L$ has an indexed right adjoint $R_X$ [PTJ02, B1.2.3], such dashed lifts correspond bijectively to dashed lifts as above right. By the universal property of the pullback, we can thus define $\psi_{g^*f} : \mathfrak{F}'(g^*f) \to Z$ as the pullback displayed above-right. $\square$

**Example 2.1.17.** For instance, $L : \mathsf{E}' \to \mathsf{E}$ might have an ordinary right adjoint and, supposing $\mathsf{E}$ has a terminal object, $K : \mathsf{E}' \to \mathsf{E}$ may be taken to be the terminal functor. In this setting, Leibniz pullback application reduces to application of $L$ and Lemma 2.1.16 specializes to Shulman's observation that locally representable notions of fibred structure may be lifted along pullback-preserving left adjoints [Shu19, 3.5, 3.12], though for that result $\mathsf{E}$ needs only to have pullbacks and need not be locally cartesian closed.

17

For instance, for any object $X \in \mathsf{E}$, such an adjunction is given by the pullback functor along $X \to 1$:

$$\mathsf{E}_{/X} \xrightarrow[\perp]{X^*} \mathsf{E}.$$

Thus a locally representable notion of fibred structure on $\mathsf{E}$ may be lifted to its slice categories.

2.2. Monomorphisms and uniform trivial fibrations. Let $\mathsf{E}$ be an elementary topos and write $\top: 1 \to \Omega$ for its subobject classifier. We consider a class of “trivial fibrations” characterized by the right lifting property against the monomorphisms and show that it underlies a notion of fibred structure which we call uniform trivial fibration structure. We then show that this notion of fibred structure is locally representable.

First, since elementary toposes are in particular locally cartesian closed, every map $f: X \to Y$ in $\mathsf{E}$ induces an adjoint triple of functors

$$\mathsf{E}_{/X} \xleftarrow[\perp]{f^*} \mathsf{E}_{/Y}$$

where $f_!$ is post-composition, $f^*$ is pullback, and $f_*$ is (by definition) pushforward. Furthermore, the following applies to $\mathsf{E}$:

Lemma 2.2.1. In a locally cartesian closed category, the pullback-pushforward adjunction $i^* \dashv i_*$ along a monomorphism $i$ forms a reflective embedding.

Proof. The counit of $i^* \dashv i_*$ is an isomorphism just when its conjugate, the unit of $i_! \dashv i^*$, is an isomorphism, but the latter is clear, since the pullback of $i$ along itself is an isomorphism. □

We note the following closure property of monomorphisms in a topos, for later use:

Remark 2.2.2. Since elementary toposes are adhesive, the class of monomorphisms is closed under pushout products, and the same is true in slice categories: given a pair of monomorphisms $i: A \mapsto B$ and $j: C \mapsto D$, the pushout product is the join of the subobjects $i \times D: A \times D \mapsto B \times D$ and $B \times j: B \times C \mapsto B \times D$ [LS04, 17].

We now use the subobject classifier to define partial map classifiers (called partial-map representers in [PTJ02, §A.2.4]). In turn, these will be used to define our trivial fibrations. The following two propositions are proven in [Awo26, §3] (see also [PTJ02, A2.4.7] and [GS17, 9.8–9]):

Proposition 2.2.3. For any $Y \in \mathsf{E}$, there is a pullback square as below-left with the property that any partial map as below-right

$$\begin{array}{ccc} Y & \xrightarrow{!} & 1 \\ \eta_Y \downarrow & \downarrow^\top & \downarrow^\top \\ Y^+ & \xrightarrow{\top_* Y} & \Omega \end{array} \qquad \begin{array}{c} C & \xrightarrow{y} & Y \\ \downarrow^c & \\ Z & \end{array}$$

18

is classified by a unique map $\zeta_c^y: Z \to Y^+$ defining a pullback square

$$\begin{array}{c} C \xrightarrow{y} Y \xrightarrow{!} 1 \\ \downarrow_c \quad \downarrow_{\text{丨}} \quad \eta_Y \downarrow_{\text{丨}} \\ Z \xrightarrow{\zeta_c^y} Y^+ \xrightarrow{\top_* Y} \Omega. \\ \downarrow_{\chi_c} \end{array}$$

Moreover, for any $X \in \mathsf{E}$, the same results are true in $\mathsf{E}_{/X}$, and these classifying squares are stable under pullback. $\square$

We refer to the monomorphism $\eta_Y: Y \mapsto Y^+$ as the partial map classifier for $Y$, since partial maps from $Z$ to $Y$ are classified by (total) maps $Z \to Y^+$. We write $f^+: Y^{+X} \to X$ for the codomain of the partial map classifier for $(Y, f) \in \mathsf{E}_{/X}$, so that we have $\eta_f: Y \to Y^{+X}$.

**Definition 2.2.4.** A **relative +-algebra** structure on $f: Y \to X$ is a retraction over $X$ to the map $\eta_f: Y \mapsto Y^{+X}$ over $X$:

$$\begin{array}{c} Y \xlongequal{\quad} Y \\ \eta_f \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_f \\ Y^{+X} \xrightarrow{f^+} X. \end{array} \tag{2.2.5}$$

The **category of relative +-algebras** has relative +-algebras as objects and, as morphisms $f' \to f$, squares as below-left such that the induced diagram below-right commutes:

$$\begin{array}{ccc} Y' \longrightarrow Y & & Y' \longrightarrow Y \\ f' \downarrow \quad \downarrow_f & & \uparrow_{\text{丨}} \\ X' \longrightarrow X & & Y'^{+X'} \longrightarrow Y^{+X}. \end{array}$$

*Remark 2.2.6.* The relative version of the construction of Proposition 2.2.3 defines a pullback-preserving functorial factorization:

$$\begin{array}{ccc} W \xrightarrow{f^* g} Y & & W \xrightarrow{f^* g} Y \\ g^* f \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_f & & \eta_{g^* f} \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_{\text{丨}} \\ Z \xrightarrow{g} X & & W^{+Z} \longrightarrow Y^{+X} \\ & & g^* f^+ \downarrow \quad \downarrow_{\text{丨}} \quad \downarrow_{f^+} \\ & & Z \xrightarrow{g} X \end{array}$$

satisfying the hypotheses of Example 2.1.6. This defines a weak factorization system whose left maps are the monomorphisms and whose right maps are those admitting a relative +-algebra structure.

*Remark 2.2.7.* The partial map classifier $\eta_Y: Y \mapsto Y^+$ is the component at $Y$ of a unit natural transformation which is part of a monad structure on the (fibred) endofunctor $(-)^+: \mathsf{E} \to \mathsf{E}$. Thus the object $Y^+ = \Omega_! \top_* Y$ is itself a (free) +-algebra. This can be used to show that the functorial factorization of Remark 2.2.6 underlies an algebraic weak factorization system. See [GS17, 9.5] or [Awo26, §3] for details.

By the following proposition, we can see a relative +-algebra structure as consisting of a uniform choice of lifts against all monomorphisms.

**Proposition 2.2.8.** *The category of relative +-algebras is isomorphic to the category whose*

19

(i) objects are maps $f: Y \to X$ paired with a choice of lifts against all monomorphisms uniformly in all pullback squares:

![img-8.jpeg](img-8.jpeg)

and

(ii) morphisms $f' \to f$ are commutative squares compatible with the choices of lifts.

Proof. By Proposition 2.2.3 any lifting problem between a monomorphism and a map $f$ factors uniquely as

$$\begin{array}{c c c} C & \xrightarrow {x} Y & C \xrightarrow {x} Y = Y \\ c \Big \downarrow & \Big \downarrow f & c \Big \downarrow \quad \eta_ {f} \Big \downarrow \quad \rho \quad \neg \\ Z & \xrightarrow [ y ]{} X & Z \xrightarrow [ y ]{\zeta^ {x, y}} Y ^ {+ x} \xrightarrow [ f ^ {+} ]{} X \\ & & y \end{array}$$

Thus a relative $+$-algebra structure uniquely equips $f$ with a uniform choice of lifts against all monomorphisms and conversely such lifts specialize to equip $f$ with a relative $+$-algebra structure. Likewise, compatibility of a square $f' \to f$ with chosen lifts against all monomorphisms reduces to compatibility with the retractions $\rho_{f'}$ and $\rho_f$. See [Awo26, 3.7] and [GS17, 9.9(i)].

Definition 2.2.9. Write $\mathcal{TF}$ for the notion of fibred structure on $\mathsf{E}$ obtained by applying Example 2.1.6 with the partial map factorization of Remark 2.2.6. We call $\mathcal{TF}$ the notion of uniform trivial fibration structure.

The $\mathcal{TF}$-algebras are then exactly the relative $+$-algebras, while the $\mathcal{TF}$-morphisms are those pullback squares which are also relative $+$-algebra morphisms. By Proposition 2.2.8, the $\mathcal{TF}$-algebras are equivalently maps equipped with a choice of lifts against all monomorphisms uniformly in pullback squares, and a pullback square $f' \to f$ is a $\mathcal{TF}$-morphism when the chosen lifts against $f'$ are determined by restriction of those against $f$.

Lemma 2.2.10. The notion of fibred structure $\mathcal{TF}$ in an elementary topos is relatively acyclic and locally representable.

Proof. Since, by Remark 2.2.6, the functorial factorization preserves pullbacks and our ambient category is locally cartesian closed, Example 2.1.6 tells us that relative $+$-algebras define a locally representable notion of fibred structure.

The proof of relative acyclicity follows by an adaptation of Shulman's [Shu19, 5.18]. In this setting, relative acyclicity asserts that for any solid-arrow pullback square whose horizontal maps are monomorphisms and vertical maps are relative $+$-algebras as below-left, the relative $+$-algebra structures encoded by the dashed maps below-right can be made to commute by changing the relative $+$-algebra structure for $f$:

$$\begin{array}{c c} Y ^ {\prime} \xrightarrow {i ^ {\prime}} Y & Y ^ {\prime} \xrightarrow [ j ]{\neg i ^ {\prime}} Y \\ f ^ {\prime} \Big \downarrow \quad \neg \quad \Big \downarrow f & \eta_ {f ^ {\prime}} \Big \downarrow \quad \rho_ {f ^ {\prime}} \Big \downarrow \eta_ {f} \\ X ^ {\prime} \xrightarrow [ i ]{} X & Y ^ {\prime + x ^ {\prime}} \xrightarrow [ j ]{} Y ^ {+ x} \\ & f ^ {\prime +} \Big \downarrow \quad \neg \quad \Big \downarrow f ^ {+} \\ & X ^ {\prime} \xrightarrow [ i ]{} X. \end{array}$$

20

Since the functorial factorization of Remark 2.2.6 is cartesian, the pushout below-left constructs the union of subobjects over $Y^{+x}$ and thus defines a monomorphism:

![img-9.jpeg](img-9.jpeg)

![img-10.jpeg](img-10.jpeg)

Since $f$ is a relative $+$-algebra, the resulting lifting problem admits a solution, defining a new relative $+$-algebra structure for $f$ that defines a $\mathcal{TF}$-morphism with the relative $+$-algebra structure for $f'$. $\square$

When we forget structure and consider class of maps underlying $\mathcal{TF}$, we find another equivalent characterization.

**Proposition 2.2.11.** *The following are equivalent for a map $f: Y \to X$ in an elementary topos $\mathsf{E}$:*

- (i) $f$ is a relative $+$-algebra.
- (ii) $f$ lifts against all monomorphisms, uniformly in all pullback squares between monomorphisms.
- (iii) $f$ lifts against all monomorphisms.

*Proof.* The equivalence between (i) and (ii) follows from Proposition 2.2.8. Clearly (ii) implies (iii), and (iii) implies (i) because the diagram (2.2.5) is a lifting problem against a monomorphism. $\square$

**Definition 2.2.12.** We refer to maps $f$ satisfying the equivalent conditions of Proposition 2.2.11 as trivial fibrations.

Internally to $\mathsf{E}$, the relative $+$-algebras can be seen as generated by right lifting against the family $\top: 1 \to \Omega$ indexed by the subobject classifier $\Omega$. In the case where $\mathsf{E}$ is a presheaf topos, this can be externalized as generation by a small *category* of maps. Both of these viewpoints are instances of the framework of Swan [Swa18b] of lifting in a Grothendieck fibration: the codomain fibration for the internal viewpoint and the category-indexed families fibration for the external viewpoint.

**Construction 2.2.13.** Let $\mathsf{E} = \mathsf{Set}^{\mathsf{Cop}}$ be a presheaf topos. In the slice category over $\Omega$, the morphism $\top: 1 \to \Omega$ may be regarded as a subterminal object, determining a family of maps internally indexed by the base object $\Omega$. This family can be externalized to determine a functor $I: \int \Omega \to \mathsf{E}^2$ on the category of elements of $\Omega$, defined by pulling back this internal family to the representables.

The cartesian functor $I$ thus lifts the Yoneda embedding $\nmid$ from the discrete fibration associated to the category of elements of $\Omega$ to the codomain fibration of $\mathsf{E}$:

![img-11.jpeg](img-11.jpeg)

It sends an element $\chi_c: \nmid a \to \Omega$ to the subobject $C \mapsto \nmid a$ that it classifies, while morphisms in $\int \Omega$

![img-12.jpeg](img-12.jpeg)

are carried to pullback squares between subobjects as below:

$$\begin{array}{c} D \xrightarrow{\alpha} C \\ \downarrow_{d} \downarrow_{\perp} \quad \downarrow_{c} \\ \updownarrow_{b} \xrightarrow{\alpha} \updownarrow_{a}. \end{array}$$

Recall that for any index category I and functor $I: \mathsf{I} \to \mathsf{E}^2$ into an arrow category, there is a corresponding category $\mathsf{I}^{\square}$ whose objects are arrows of E equipped with chosen lifts against the images of the objects of I, in a way that is natural in the morphisms of I [BG16, 15].

In particular, when $\mathsf{E} = \mathsf{Set}^{\mathsf{Cop}}$ is a presheaf topos, an object of the category $(\int \Omega)^{\square}$ is a morphism $f: Y \to X$ in E equipped with chosen lifts against subobjects of representables that are uniform in pullback squares:

![img-13.jpeg](img-13.jpeg)

**Proposition 2.2.14.** For $\mathsf{E} = \mathsf{Set}^{\mathsf{Cop}}$ a presheaf topos, the category of relative $+$-algebras is isomorphic over $\mathsf{E}^2$ to $(\int \Omega)^{\square}$.

*Proof.* The statement asserts that in a presheaf topos, the lifting properties of Proposition 2.2.8 reduce to the case where we only ask for lifts against subobjects of representables. See [GS17, 5.16].

*Remark 2.2.15.* In summary, in the setting of a presheaf topos, we have multiple isomorphic characterizations of the category of relative $+$-algebras and the notion of fibred structure $\mathcal{TF}$. Note, however, that these perspectives suggest two non-isomorphic algebraic weak factorization systems providing a functorial factorization of a map into a monomorphism followed by a trivial fibration.

On the one hand, the relative $+$-algebra factorization underlies an awfs as described in Remark 2.2.7. On the other hand, Garner's algebraic small object argument applied to the generating category $I: \int \Omega \to \mathsf{E}^2$ yields an awfs whose category of monad algebras is isomorphic to $(\int \Omega)^{\square}$ [Gar09, 4.4]. By Proposition 2.2.14, the category of monad algebras for the second awfs is thus isomorphic to the category of pointed endofunctor algebras for the first, which is the category of relative $+$-algebras of Definition 2.2.4. In fact, the relative $+$-algebra factorization is the one-step factorization of the algebraic small object argument. See also the discussion in [GS17, 9.5].

### 2.3. Universes.

**Definition 2.3.1.** Fix a notion of fibred structure $\mathfrak{F}$. A **universe** for $\mathfrak{F}$ is an $\mathfrak{F}$-algebra $\pi: \dot{U} \to U$ such that $\pi: \mathsf{E}(-, U) \to \mathfrak{F}$ is an acyclic fibration, meaning that we have bicategorical lifts against Yoneda embeddings of monomorphisms $i: A \mapsto B$ as below:

$$\begin{array}{c} \mathsf{E}(-, A) \xrightarrow{h} \mathsf{E}(-, U) \\ \downarrow_{i} \quad \downarrow_{k} \\ \mathsf{E}(-, B) \xrightarrow{p} \mathfrak{F}. \end{array}$$

Unpacked, this requires that given any pair of $\mathfrak{F}$-algebras $p, q$ and $\mathfrak{F}$-morphisms as displayed by the solid-arrow squares below, with $i: A \mapsto B$ a monomorphism,

![img-14.jpeg](img-14.jpeg)

there exists an extension $k$ of $h$ along $i$ factoring the back pullback square as a composite of pullbacks and defining an $\mathfrak{F}$-morphism from $p$ to $\pi$.

**Proposition 2.3.2.** Assume that $\mathsf{E}$ has initial objects which are preserved by pullback along arbitrary maps. Given a relatively acyclic notion of fibred structure $\mathfrak{F}$ with universe $\pi: \dot{U} \to U$, each $\mathfrak{F}$-algebra is a pullback of $\pi$.

*Proof.* Suppose $p: E \to B$ is an $\mathfrak{F}$-algebra. The back pullback square in the diagram below gives the identity on the initial object an $\mathfrak{F}$-algebra structure, and by relative acyclicity, the $\mathfrak{F}$-algebra $p$ can be given an $\mathfrak{F}$-algebra structure making the left-hand pullback into an $\mathfrak{F}$-morphism. Because $\pi: \dot{U} \to U$ is a universe, $p$ is then a pullback of $\pi$:

![img-15.jpeg](img-15.jpeg)

We now specialize to the setting of a presheaf topos $\mathsf{E} = \mathsf{Set}^{\mathsf{Cop}}$ for some small indexing category $\mathsf{C}$ to give an example of a universe. For any regular cardinal $\kappa$ for which $\mathsf{C}$ is $\kappa$-small, the Hofmann–Streicher construction [HS97; Awo24] provides a classifier $\varpi: \dot{V}_{\kappa} \to V_{\kappa}$ for $\kappa$-small families, i.e., those maps whose components have $\kappa$-small fibres. As noted in Example 2.1.13, for sufficiently large $\kappa$ this defines a locally representable and relatively acyclic full notion of fibred structure $\mathfrak{E}^{\kappa}$. By [Cis14, 3.9], [OP18, 8.4], or [Awo24, 6], the classifier $\varpi: \dot{V}_{\kappa} \to V_{\kappa}$ is a universe for $\mathfrak{E}^{\kappa}$.

Now consider a notion of fibred structure $\mathfrak{F}$ on the presheaf topos $\mathsf{E}$.

**Construction 2.3.3.** If $\mathfrak{F}$ is locally representable, then for sufficiently large $\kappa$ we may define a $\kappa$-small $\mathfrak{F}$-algebra classifier $\pi: \dot{U}_{\kappa} \to U_{\kappa}$ as follows. Firstly, we define a new notion of fibred structure $\mathfrak{F}^{\kappa}$ for which an $\mathfrak{F}^{\kappa}$-algebra is an $\mathfrak{F}$-algebra that is $\kappa$-small. If $\mathfrak{F}$ is locally representable or relatively acyclic, then for $\kappa$ sufficiently large so that Example 2.1.13 holds, $\mathfrak{F}^{\kappa}$ inherits these properties [Shu19, 3.3, 3.11, 4.18, 5.14].

23

Now set $U_\kappa := \mathfrak{F}^\kappa(\varpi)$ and form the pullback

$$\begin{array}{ccc} \dot{U}_\kappa & \longrightarrow & \dot{V}_\kappa \\ \pi \downarrow & \downarrow^\perp & \downarrow^\varpi \\ U_\kappa & \xrightarrow[\psi_\varpi]{} & V_\kappa. \end{array}$$

As a special case of Lemma 2.1.4(i):

**Lemma 2.3.4.** *The map $\pi: \dot{U}_\kappa \to U_\kappa$ is canonically an $\mathfrak{F}^\kappa$-algebra.*

**Proposition 2.3.5.** *Let $\mathfrak{F}$ be a locally representable notion of fibred structure on a presheaf topos. For sufficiently large regular cardinals $\kappa$, the $\mathfrak{F}^\kappa$-algebra $\pi: \dot{U}_\kappa \to U_\kappa$ is a universe for $\mathfrak{F}^\kappa$.*

*Proof.* Construction 2.3.3 defines the $\mathfrak{F}^\kappa$-algebra classifier as the pullback

$$\begin{array}{ccc} \mathsf{E}(-, U_\kappa) & \xrightarrow{\psi_\varpi} & \mathsf{E}(-, V_\kappa) \\ \pi \downarrow & \downarrow^\perp & \downarrow^\varpi \\ \mathfrak{F}^\kappa & \longrightarrow & \mathfrak{C}^\kappa. \end{array}$$

Note that this strict pullback is also a bicategorical pullback, as $\mathfrak{F}^\kappa \to \mathfrak{C}^\kappa$ is a strict discrete fibration. Since the Hofmann–Streicher classifier $\varpi: \dot{V}_\kappa \to V_\kappa$ is a universe, the right-hand vertical map is an acyclic fibration, whence its bicategorical pullback is as well. $\square$

For size reasons, multiple universes will be required to classify all maps belonging to a given notion of fibred structure. So that the maps classified by a given universe are closed under various categorical operations, we now assume that the cardinals $\kappa$ are inaccessible so that the corresponding Hofmann–Streicher universes $\varpi: \dot{V}_\kappa \to V_\kappa$ can be thought of as internalized Grothendieck universes.

**Definition 2.3.6.** A pullback-stable class of maps $\mathcal{P}$ in a presheaf topos **has universes** if for any cardinal $\lambda$, there exists an inaccessible cardinal $\kappa \geq \lambda$ and a universe $\pi: \dot{U}_\kappa \to U_\kappa$ for a relatively acyclic notion of fibred structure whose underlying maps are the $\kappa$-small maps in $\mathcal{P}$.

In particular, each $\kappa$-small map in $\mathcal{P}$ is a pullback of $\pi: \dot{U}_\kappa \to U_\kappa$, by Proposition 2.3.2.

We now make a standing assumption that there exist arbitrarily large inaccessible cardinals. Proposition 2.3.5 then provides universes for the class of maps underlying any locally representable and relatively acyclic notion of fibred structure on a presheaf topos. See [Shu19] or [GSS22b] for a treatment of universe levels in more general categorical settings.

**Notation 2.3.7.** In the setting of Definition 2.3.6, it is often not necessary to disambiguate between the inaccessible cardinals indexing universe levels. Thus, we typically write $\pi: \dot{U} \to U$ for a generic member of the classifying family of universes, without explicitly designating the cardinal bound.

### 3. CYLINDRICAL MODEL STRUCTURES

In this section, we lay the theoretical groundwork for the construction of our two models of homotopy type theory, proving our results at a level of generality that ensures that they will apply to both cubical sets and cubical species while also enabling their use elsewhere. In §3.1, we introduce the notion of cylindrical premodel structure [Sat20], also used in [CS25], which provides the familiar structures of abstract homotopy theory in a setting where the weak equivalences are not yet known to satisfy the 2-of-3 property. In particular, these axioms provide fibred mapping path space factorizations that are stable under slicing, the basic properties of which we establish in §3.2.

In §3.3, we state and prove the equivalence extension property in a locally cartesian closed cylindrical premodel category in which the cofibrations are the monomorphisms and these are stable

24

under pushout products in all slices. In §3.4, we introduce the Frobenius condition and mention a few consequences. In §3.5, we connect the equivalence extension property to the univalence axiom in the presence of the Frobenius condition on the cylindrical premodel structure. In §3.6, we use this to establish the fibrancy of the universe, assuming that the fibrations are defined from the trivial fibrations via one of the standard constructions. In §3.7, we translate the fibrancy of the universe into the fibration extension property, which implies that the cylindrical premodel structure is in fact a model structure, retroactively justifying the title of this section as well as the nonstandard encodings of the weak equivalences and the univalence axioms we use along the way.

3.1. Cylindrical premodel structures. Following Barton [Bar19], a premodel structure on a category E is a pair of weak factorization systems, called the (trivial cofibration, fibration) and (cofibration, trivial fibration) weak factorization systems, such that every trivial cofibration is a cofibration (equivalently, any trivial fibration is a fibration). We also require finite limits and colimits (in practice, often only pullbacks along fibrations and pushouts along cofibrations are needed). We denote trivial cofibrations with the arrow $\rightsquigarrow$, fibrations with $\rightarrow$, cofibrations with $\mapsto$, and trivial fibrations with $\rightsquigarrow$.

In a premodel structure, define a map to be a weak equivalence $\rightsquigarrow$ if it factors as a composite of a trivial cofibration followed by a trivial fibration. In particular, the trivial cofibrations and trivial fibrations admit such factorizations, so both of these classes are included in the class of weak equivalences. Conversely, by a standard argument:

Lemma 3.1.1. Any cofibration and weak equivalence is a trivial cofibration, and any fibration and weak equivalence is a trivial fibration.

Proof. The proofs are dual, and standard. If a cofibration factors as a trivial cofibration followed by a trivial fibration, this presents a lifting problem

![img-16.jpeg](img-16.jpeg)

a solution to which presents the cofibration as a retract of the trivial cofibration.

Thus, from the Joyal–Tierney characterization [JT07, 7.7–7.8] of a (closed) Quillen model structure:

Proposition 3.1.2. A premodel structure defines a model structure if and only if the weak equivalences satisfy the 2-of-3 property.

Remark 3.1.3. Premodel structures lift to slice and coslice categories, with all of the classes of maps created by the forgetful functor to the base category.

For a general premodel structure, the 2-of-3 property for the weak equivalences may be hard to prove (and is often false). A convenient technical device that can be used when present to analyze the weak equivalences in a premodel structure is an adjoint functorial cylinder, introduced below, that satisfies three compatibility conditions making the premodel structure into a cylindrical premodel structure.

Definition 3.1.4. A functorial notion of homotopy on a category E is a reflexive binary relation on the hom-bifunctor in the category of profunctors from E to E:

![img-17.jpeg](img-17.jpeg)

25

For any pair of objects $A, B \in \mathsf{E}$, we refer to elements of the set $\mathsf{I}(A, B)$ as **homotopies** between maps from $A$ to $B$. More precisely, the fiber over a parallel pair of morphisms $f, g \colon A \rightrightarrows B$

$$\begin{array}{c} \mathsf{I}(A, B)_{(f, g)} \xrightarrow{\quad} \mathsf{I}(A, B) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ * \xrightarrow{(f, g)} \mathsf{E}(A, B) \times \mathsf{E}(A, B) \end{array}$$

defines the set of **homotopies** from $f$ to $g$. We write $\alpha \colon f \sim g$ to mean that $\alpha \in \mathsf{I}(A, B)_{f, g}$. The map $\epsilon \colon \mathsf{E}(A, B) \to \mathsf{I}(A, B)$ sends each $f \colon A \to B$ to a **constant homotopy** $\epsilon_f \colon f \sim f$.

**Definition 3.1.5.** A functorial notion of homotopy $\mathsf{I}$ on $\mathsf{E}$ is

- **representable** if the profunctor $\mathsf{I}$ is covariantly represented by a functor $P \colon \mathsf{E} \to \mathsf{E}$, which then defines a **functorial cocylinder** $\mathsf{I}(A, B) \cong \mathsf{E}(A, PB)$, and
- **corepresentable** if the profunctor $\mathsf{I}$ is contravariantly represented by a functor $C \colon \mathsf{E} \to \mathsf{E}$, which then defines a **functorial cylinder** $\mathsf{I}(A, B) \cong \mathsf{E}(CA, B)$.

In the co/represented setting, by the profunctorial Yoneda lemma, the natural transformations $(\epsilon, \partial_0, \partial_1)$ determine natural transformations

![img-18.jpeg](img-18.jpeg)

![img-19.jpeg](img-19.jpeg)

When $\mathsf{I}$ is **birepresentable**, that is both representable and corepresentable, these functors are adjoints $C \dashv P$ and the natural transformations are conjugates. As in Lemma 2.1.15, we use the same notation for a conjugate pair of transformations, e.g., $\epsilon \colon C \Rightarrow \mathrm{id}$ and $\epsilon \colon \mathrm{id} \Rightarrow P$. We follow [CS25, 3.9] and refer to a birepresentable functorial notion of homotopy as an **adjoint functorial cylinder**.

We now show that all of these notions are stable under slicing—that is, passage to $\mathsf{E}_{/X}$—and coslicing—that is, passage to $^{X}/\mathsf{E}$—over and under arbitrary objects $X \in \mathsf{E}$. In fact it suffices to consider slice categories, since functorial notions of homotopy are self-dual.

**Lemma 3.1.6.** *If $\mathsf{E}$ has a functorial notion of homotopy $\mathsf{I}$ then for any $X \in \mathsf{E}$ the slice category $\mathsf{E}_{/X}$ has a functorial notion of homotopy $\mathsf{I}_X$. Moreover:*

(i) if $\mathsf{I}$ is corepresentable, then so is $\mathsf{I}_X$, and
(ii) if $\mathsf{I}$ is representable and $\mathsf{E}$ has pullbacks then so is $\mathsf{I}_X$.

*Proof.* We leave the general case to the reader and construct the functorial cylinder and cocylinder in the birepresentable case.

Given an object $g \colon Y \to X$ in the slice $\mathsf{E}_{/X}$ its **fibred cylinder factorization** is created by the forgetful functor to $\mathsf{E}$, with the projections to $X$ defined by composing in the diagram

$$\begin{array}{c} Y + Y \xrightarrow{(\partial_0, \partial_1)} CY \xrightarrow{\epsilon} Y \\ f + f \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X + X \xrightarrow{(\partial_0, \partial_1)} CX \xrightarrow{\epsilon} X. \end{array}$$

26

Meanwhile, the fibred cocylinder factorization is constructed as follows:

![img-20.jpeg](img-20.jpeg)

Remark 3.1.7. Definitions 3.1.4 and 3.1.5 are self-dual, so in particular the dual of Lemma 3.1.6 applies to coslice categories $X/E$.

Let I be a birepresented notion of homotopy on a category E with finite limits and colimits. Write $\partial: \mathrm{id} + \mathrm{id} \Rightarrow C$ and $\partial: P \Rightarrow \mathrm{id} \times \mathrm{id}$ for the conjugate pair of natural transformations with components defined by $\partial_0$ and $\partial_1$. The notion of a cylindrical premodel structure makes use of the Leibniz applications introduced in Definition 2.1.14.

Definition 3.1.8. A premodel structure on E is cylindrical if E admits an adjoint functorial cylinder so that:

- (i) Leibniz pullback application of $\partial: P \Rightarrow \mathrm{id} \times \mathrm{id}$ preserves fibrations and trivial fibrations.
- (ii) Leibniz pullback application of $\partial_0: P \Rightarrow \mathrm{id}$ and $\partial_1: P \Rightarrow \mathrm{id}$ sends fibrations to trivial fibrations.

By Lemma 2.1.15 these conditions could be phrased dually in terms of Leibniz pushout application of the conjugate natural transformations. As observed in [CS25, 3.2, 3.11, 3.17]:

Lemma 3.1.9. A cylindrical premodel structure on E induces a cylindrical premodel structure on each of its coslice and slice categories.

Proof. We prove the case of slice categories, the coslices being dual. By Lemma 2.1.15, it suffices to show that Leibniz pushout application of $\partial: \mathrm{id} + \mathrm{id} \Rightarrow C$ preserves cofibrations and trivial cofibrations and Leibniz pushout application of $\partial_0, \partial_1: \mathrm{id} \Rightarrow C$ send cofibrations to trivial cofibrations. But both these classes and these constructions are created by the forgetful functor to E and E is cylindrical, so this is immediate. □

The cylindrical premodel structure axioms allow us to deduce various “2-of-3-like” properties of “acyclic” morphisms without relying on the 2-of-3 property for the weak equivalences. Two such results are the following.

Lemma 3.1.10 ([CS25, 3.19–20, 3.27]). In a cylindrical premodel structure, in any diagram of the form below-left, the fibration is a trivial fibration,

![img-21.jpeg](img-21.jpeg)

![img-22.jpeg](img-22.jpeg)

and if the trivial fibrations are detected by lifting against cofibrations between cofibrant objects, the same is true in any diagram of the form above-right.

The first statement is proven by exhibiting $f$ as a retract of a trivial fibration constructed using axiom 3.1.8(ii) in a retract diagram whose data is defined by lifting. The second statement holds more generally even when $f$ is not known to be a fibration, by an elementary lifting argument.

27

3.2. **Brown factorizations.** The structure of a cylindrical premodel structure is designed to provide fibred mapping cylinder and mapping path space factorizations that are stable under coslicing and slicing, respectively. In this section, we focus on the mapping path space construction, which we call the “Brown factorization” after [Bro73], which will be used in the next section to establish the equivalence extension property.

**Construction 3.2.1.** Given a map $f: Z \rightarrow Y$ in a cylindrical premodel category, its **Brown factorization** $f = p_f \cdot s_f$ is constructed by factoring the graph of $f$ as follows:

$$\begin{array}{c} Z \xrightarrow{f} Y \\ (1,f) \left( \begin{array}{c} \downarrow s_f \\ \downarrow \\ Bf \xrightarrow{f \times Y} PY \\ \downarrow (q_f, p_f) \end{array} \right) \\ Z \times Y \xrightarrow{f \times Y} Y \times Y. \end{array}$$

By construction $f = p_f \cdot s_f$ and $1 = q_f \cdot s_f$.

**Lemma 3.2.2.** *For the Brown factorization of a map $f: Z \rightarrow Y$ in a cylindrical premodel category,*

$$\begin{array}{c} q_f \xrightarrow{f} Bf \\ \downarrow \xrightarrow{s_f} y \\ Z \xrightarrow{f} Y, \end{array}$$

- (i) If $Y$ is fibrant, then $(q_f, p_f): Bf \rightarrow Z \times Y$ is a fibration.
- (ii) If $Y$ is fibrant, then $q_f: Bf \rightarrow Z$ is a trivial fibration.
- (iii) If $Y$ and $Z$ are both fibrant, then $p_f: B_f \rightarrow Y$ is a fibration.

*Proof.* These maps arise as

$$\begin{array}{c} Bf \longrightarrow PY \\ q_f \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \\ Z \xrightarrow{f} Y, \end{array}$$

If $Y$ is fibrant, then by Definition 3.1.8, $\partial: PY \rightarrow Y \times Y$ is a fibration and $\partial_0: PY \xrightarrow{\sim} Y$ is a trivial fibration, proving the first two statements. If $Z$ is fibrant, then the projection $\pi: Z \times Y \rightarrow Y$ is a fibration as well, proving the third statement. $\square$

*Remark 3.2.3.* By Lemma 3.1.9, Construction 3.2.1 can be implemented in slice categories. Given a map $f: Z \rightarrow Y$ lying over $X$ via $g: Y \rightarrow X$, the **fibred Brown factorization** is defined by implementing the Brown factorization construction in the slice over $X$. This factors the graph of $f$, regarded as a morphism with codomain $Z \times_X Y$, through a pullback of the fibred path object as

28

displayed below-left:

(3.2.4)

![img-23.jpeg](img-23.jpeg)

By interchange of the pullback constructing the Brown factorization with pullback to the slice over $X$, the fibred Brown factorization is a pullback of the non-fibred Brown factorization as indicated in the right diagram above. Here the right-hand rectangle is formed by applying the non-fibred Brown factorization to the commutative square from $f$ to the identity on $X$.

In this setting, Lemma 3.2.2 specializes to tell us that

- (i) when $g$ is a fibration, $(q_f, p_f) \colon B_X f \to Z \times_X Y$ is a fibration,
- (ii) when $g$ is a fibration, $q_f \colon B_X f \to Z$ is a trivial fibration,
- (iii) when $g$ and $gf$ are both fibrations, $p_f \colon B_X f \to Y$ is a fibration.

**Lemma 3.2.5.** *The fibred Brown factorization is stable under all pullbacks.*

*Proof.* This is the combination of the description of the fibred Brown factorization in the right-hand diagram of (3.2.4) with pullback pasting. $\square$

**Definition 3.2.6.** A map $f \colon Z \to Y$ between fibrant objects in a cylindrical premodel category is called **contractible** when the right factor $p_f \colon B_f \to Y$ in its Brown factorization is a trivial fibration:

![img-24.jpeg](img-24.jpeg)

In the presence of the 2-of-3 property, the contractible maps agree with the weak equivalences between fibrant objects:

**Lemma 3.2.7.** *In a cylindrical model category, where the weak equivalences satisfy the 2-of-3 property, a map between fibrant objects is contractible if and only if it is a weak equivalence.*

*Proof.* If the weak equivalences satisfy the 2-of-3 property, then the section $s_f$ of the trivial fibration $q_f$ is also a weak equivalence. Thus, again by 2-of-3, $f$ is a weak equivalence if and only if the fibration $p_f$ is a trivial fibration. $\square$

For emphasis, we shall refer to a contractible map in a slice $\mathsf{E}_{/X}$ as a **contractible map over $X$**. Explicitly, a fibred map $f \colon Z \to Y$ over $X$ is contractible just when its domain $Z \to X$ and codomain $Y \to X$ are fibrations, and the fibration $p_f \colon B_X f \to Y$ of Remark 3.2.3 is a trivial fibration.

29

3.3. **Equivalence extension property.** In this section, we show that under suitable hypotheses, a cylindrical premodel category satisfies the following condition, the significance of which is explained in the sequel.

**Definition 3.3.1.** A cylindrical premodel structure has the **equivalence extension property** when any contractible map $e$ over an object $A$ can be extended along any cofibration $i: A \mapsto B$ to a contractible map $f$ over $B$ with a specified codomain extending that of the original map:

![img-25.jpeg](img-25.jpeg)

In a setting such as a presheaf topos where we have universe levels, there is an additional requirement: for sufficiently large inaccessible cardinals $\kappa$, if $p_0$, $p_1$, and $q_1$ are $\kappa$-small, so is the extended fibration in (3.3.2).

**Theorem 3.3.3.** *Let $\mathsf{E}$ be a locally cartesian closed category with a cylindrical premodel structure in which the cofibrations are the monomorphisms, and these are stable under pushout-products in all slices. Then the equivalence extension property holds in $\mathsf{E}$.*

**Example 3.3.4.** For instance, by Remark 2.2.2, the hypotheses are satisfied in a cylindrical premodel structure on an elementary topos if the cofibrations are the monomorphisms. Moreover, in a presheaf topos, all of the constructions in the proof of Theorem 3.3.3 will respect universe levels.

Our approach to the equivalence extension property phrased using contractible maps follows [Sat17]. In a cylindrical model category, where the weak equivalences satisfy the 2-of-3 condition, this is equivalent by Lemma 3.2.7 to the equivalence extension property phrased instead using weak equivalences as in [KL21; Shu15].

The proof of Theorem 3.3.3 occupies the remainder of this section. To begin, in the diagram (3.3.2), we have $i^*Y_1 \cong X_1$ by hypothesis, and we define an object $Y_0$ with a map $f: Y_0 \to Y_1$ as a pullback of the pushforward along $i$ of the given fibred map $e: X_0 \to X_1$:

$$\begin{array}{c} Y_0 \xrightarrow{\eta_{Y_0}} i_* X_0 \\ f \downarrow \quad \downarrow i_* e \\ Y_1 \xrightarrow{\eta_{Y_1}} i_* i^* Y_1. \end{array} \tag{3.3.5}$$

By Lemma 2.2.1, $i^*\eta_{Y_1}$ is invertible. Considering the image of (3.3.5) under the pullback-preserving functor $i^*$, we conclude that $i^*f$ is isomorphic to $i^*i_*e \cong e$. In other words, $f: Y_0 \to Y_1$ pulls back along $i$ to the original map $e: X_0 \to X_1$, giving a diagram of the required form (3.3.2).

It remains to show that $q_1 f: Y_0 \to B$ is a fibration and that $f: Y_0 \to Y_1$ is a contractible map over $B$. We shall prove both in the slice over $B$.

30

For contractibility, consider the fibred Brown factorizations for both $e$ and $f$:

![img-26.jpeg](img-26.jpeg)

By Lemma 3.2.5, the fibred Brown factorization for $f$ pulls back along $i$ to the factorization for $e$, and similarly the fibred path objects pullback $i^*P_BY_1 \cong P_AX_1$ (not shown in the diagram). The relationship between the pushforward of the fibred Brown factorization for $e$ and that for $f$ is more complicated, however. To understand it, first consider the naturality cube resulting from the pullback square defining the map $(q_f, p_f)$ and the unit natural transformation $\eta: \mathrm{id} \Rightarrow i_*i^*$, which by Lemma 3.2.5 determines the following commutative cube:

![img-27.jpeg](img-27.jpeg)

The back face is the pullback in Construction 3.2.1, and the front face is its image under the right adjoint $i_*$, and is therefore also a pullback. Since (3.3.5) is a pullback, the bottom square is one as well. By pullback composition and cancelation, the top square is therefore also a pullback.

Now consider the naturality cube associated to the commutative square relating $p_f$ and $\partial_1$:

![img-28.jpeg](img-28.jpeg)

The top square was just shown to be a pullback, and the bottom square is evidently one. So when we form the pullbacks indicated in the left and right faces, we obtain a factorization of $p_f$ as a pullback of the map $i_*p_e$, after a pullback of the comparison map $z$ indicated as a dashed arrow in the right-hand face. This factorization will display $p_f$ as a trivial fibration, as we now argue.

First, since $e$ is a contractible map over $A$, its second Brown factor $p_e$ is a trivial fibration. Since the cofibrations are the monomorphisms, and therefore stable under pullback, the trivial fibrations are stable under pushforward, and so $i_*p_e$ is a trivial fibration, as is any pullback of it.

Next, the map $z$ may be described as a Leibniz pullback application of the unit $\eta$ applied to the trivial fibration $\partial_1: P_BY_1 \xrightarrow{\sim} Y_1$. But this is also a trivial fibration, as it is the Leibniz exponential, in the slice over $B$, of the cofibrant object $i: A \mapsto B$ and the trivial fibration $\partial_1: P_BY_1 \xrightarrow{\sim} Y_1$, and monomorphisms are closed under pushout-products in slices.

31

Thus $p_f$ factors as a composite of pullbacks of trivial fibrations and so is itself a trivial fibration. The map $f$ is therefore contractible over $B$, provided that its domain $q_1 f \colon Y_0 \to B$ is a fibration. But $q_1 f$ is a retract of $q_1 p_f$:

$$\begin{array}{c c c c} Y_0 & \xrightarrow{s_f} & B_B f & \xrightarrow{q_f} & Y_0 \\ f \downarrow & & \downarrow p_f & & \downarrow f \\ Y_1 & = & Y_1 & & Y_1 \\ q_1 \downarrow & & \downarrow q_1 & & \downarrow q_1 \\ B & = & B & = & B. \end{array}$$

Here the right rectangle commutes because in the fibred Brown factorization of $f \colon Y_0 \to Y_1$ over $B$, $p_f$ and $q_f$ live over $B$ and $p_f$ and $f$ both have target $q_1 \colon Y_1 \to B$. We have just shown that $p_f$ is a (trivial) fibration, while $q_1$ was assumed to be a fibration; thus the retract diagram implies $q_1 f \colon Y_0 \to B$ is also a fibration, as required. This completes the proof of Theorem 3.3.3.

3.4. The Frobenius condition. In the setting of a locally cartesian closed category, it is natural to ask that a premodel structure satisfies the Frobenius condition.

Definition 3.4.1. A weak factorization system satisfies the Frobenius condition if the left maps are stable under pullback along the right maps. A premodel structure satisfies the Frobenius condition if this holds for both of its weak factorization systems.

When the cofibrations are the monomorphisms, since these are stable under all pullbacks, the Frobenius condition only requires proof for the trivial cofibration–fibration weak factorization system. This condition has been studied in the homotopy type theory literature owing to the fact that, in a locally cartesian closed category, it is equivalent to the fibrations being closed under the pushforward operation, corresponding to type theory's $\Pi$-type construction. Various proofs of the Frobenius condition are given [CCHM15; GS17; Awo26; HR24; Bar24a], depending on how exactly the fibrations are defined from the trivial fibrations. For the premodel structure introduced in §4, the result we will need is the following:

Proposition 3.4.2 ([ABCHFL21, 3.1.8], [Awo26, §6], [HR24, §4], [Bar24a, 8]). Let $\mathsf{E}$ be a locally cartesian closed category with a premodel structure in which the cofibrations are the monomorphisms. Suppose there is an object $I$ such that a map is a fibration just when the Leibniz exponential of its pullback to the slice over $I$ by the diagonal $\delta \colon I \to I \times I$ is a trivial fibration in the slice premodel structure. Then the premodel structure satisfies the Frobenius condition. $\square$

Now assume we are working with a premodel structure in which there is a locally representable and relatively acyclic notion of fibred structure $\mathcal{TF}$ such that the $\mathcal{TF}$-algebras are the trivial fibrations. By Lemma 2.2.10, these hypotheses are satisfied by a premodel structure on an elementary topos whose cofibrations are the monomorphisms. If this premodel structure satisfies the Frobenius condition, then the trivial fibration structure classifier has an important property:

Lemma 3.4.3. Consider a locally cartesian closed category with a cylindrical premodel structure satisfying the Frobenius condition in which the trivial fibrations are generated by right lifting against cofibrations between cofibrant objects. Suppose $\mathcal{TF}$ is a locally representable and relatively acyclic notion of fibred structure such that the $\mathcal{TF}$-algebras are the trivial fibrations. Then if $f \colon Y \to X$ is a fibration, then so is $\phi_f \colon \mathcal{TF}(f) \to X$.

32

Proof. To solve a lifting problem of the form

![img-29.jpeg](img-29.jpeg)

we can equivalently solve the induced lifting problem against the pullback of $\phi_f$ along $B \to X$. By pullback stability of the fibrations and Lemma 2.1.4(ii), it thus suffices to solve lifting problems of the form

![img-30.jpeg](img-30.jpeg)

where $t: A \xrightarrow{\sim} B$ is a trivial cofibration and $g: D \to B$ is a fibration. This amounts to showing that if the fibration $g$ becomes a $\mathcal{TF}$-algebra upon pulling back along $t$, then it has a $\mathcal{TF}$-algebra structure making the pullback square

![img-31.jpeg](img-31.jpeg)

into a $\mathcal{TF}$-morphism. Note that by the Frobenius condition, the map $s$ in this pullback square is also a trivial cofibration, as a pullback of the trivial cofibration $t$ along the fibration $g$.

Since $t^*g$ is a trivial fibration by assumption, the pushforward $t_*t^*g: t_*C \to B$ is also a trivial fibration. Since $t$ is monic, Lemma 2.2.1 implies that $t_*t^*g$ pulls back along $t$ to $t^*g$:

![img-32.jpeg](img-32.jpeg)

Again since $t_*t^*g$ is a (trivial) fibration, the pullback $s'$ is also a trivial cofibration, by the Frobenius condition. We therefore have a (trivial cofibration, fibration) and a (trivial cofibration, trivial fibration) factorization of a common map $g \cdot s = t_*t^*g \cdot s'$. In a cylindrical premodel structure, it follows that the fibration $g$ is a trivial fibration, by an argument we now reprise.

In the commutative square defined by the pair of factorizations, form the pullback $P$ and factor the gap map in the square as a trivial cofibration followed by a fibration:

![img-33.jpeg](img-33.jpeg)

33

By the first part of Lemma 3.1.10, the dashed composite fibrations are both trivial fibrations, and now the fibration $g$ is the base of a commutative triangle of trivial fibrations with summit $E$, so $g$ is a trivial fibration by the second part of that lemma.

This proves that $g$ admits some $\mathcal{TF}$-algebra structure. By relative acyclicity, this structure may be aligned with that of $t^*g$ to make the square (3.4.5) into a $\mathcal{TF}$-morphism. This specification of a new $\mathcal{TF}$-algebra structure on $g$ finally solves the original lifting problem (3.4.4).

In the setting of Lemma 3.4.3, Voevodsky constructs an alternate contractible map classifier, which we briefly digress to describe.

Digression 3.4.6. In a locally cartesian closed category with a cylindrical premodel structure satisfying the Frobenius condition, for any fibration $f: Y \to X$, there is a fibration $\phi_f: \text{isContr}_X f \to X$ defined by pushing forward and then summing over its fibred path space fibration:

$$\begin{array}{c c c c c} P_X Y & \Pi_Y P_X Y & \Sigma_Y \Pi_Y P_X Y & =: & \text{isContr}_X(f) \\ \partial \Big\downarrow & \Big\downarrow (\pi_2)_* \partial & \Big\downarrow f \cdot (\pi_2)_* \partial & & \Big\downarrow \phi_f \\ Y \times_X Y & \xrightarrow{\pi_2} Y & \xrightarrow{f} X & =: & X. \end{array}$$

By construction, sections to $\phi_f: \text{isContr}_X(f) \to X$ correspond to sections $s: X \to Y$ to $f$ together with a fibred homotopy $s \cdot f \sim_X \text{id}_Y$.

As our notation suggests, there is a close relationship between the map $\phi_f: \text{isContr}_X(f) \to X$ and the map $\phi_f: \mathcal{TF}(f) \to X$ constructed in Lemma 2.2.10 in the setting of a premodel structure on an elementary topos in which the cofibrations are the monomorphisms. For a fibration $f: Y \to X$, these define “logically equivalent notions” of fibred structure witnessing that $f$ is a trivial fibration.

Indeed, if $\phi_f: \mathcal{TF}(f) \to X$ has a section, then $f$ is a trivial fibration, so admits a section $s: X \to Y$, since all objects are cofibrant. This data defines a lifting problem

$$\begin{array}{c} \emptyset \longrightarrow P_X Y \\ \Big\downarrow \quad \stackrel{h}{\longrightarrow} \quad \Big\downarrow \partial \\ Y \xrightarrow{(sf,id_Y)} Y \times_X Y, \end{array}$$

which admits a solution by the axiom 3.1.8(i) in the setting of Lemma 3.1.9, constructing a section $(s, h)$ of $\phi_f: \text{isContr}_X(f) \to X$.

Conversely, if $\phi_f: \text{isContr}_X(f) \to X$ has a section, then this data defines a retract diagram

$$\begin{array}{c} Y \xrightarrow{h} P_X Y \xrightarrow{\partial_1} Y \\ f \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

exhibiting $f$ as a retract of $\partial_0$, which is a trivial fibration in the setting of Lemma 3.1.9 by the axiom 3.1.8(ii). Thus, $\phi_f: \mathcal{TF}(f) \to X$ has a section.

3.5. Univalence. In a premodel structure that satisfies the Frobenius condition and for which the fibrations have universes in the sense of Definition 2.3.6, the equivalence extension property of Definition 3.3.1 is related to Voevodsky’s univalence axiom. To state this, we require the following construction. Following Notation 2.3.7, we write $\pi: \dot{U} \to U$ for a generic classifying universe and refer to this as the “universe of fibrations,” without explicitly designating a cardinal bound.

34

Lemma 3.5.1. In a locally cartesian closed category with a cylindrical premodel structure satisfying the Frobenius condition, any fibration \(\pi: \dot{U} \twoheadrightarrow U\) has a factorization

![img-34.jpeg](img-34.jpeg)

of the diagonal \(U\to U\times U\) such that

(i) \((s,t)\colon \operatorname {Eq}(\dot{U})\twoheadrightarrow U\times U\) is a fibration and
(ii) the pullback of \(\operatorname{Eq}(\dot{U}) \twoheadrightarrow U \times U\) along any \(e: \Gamma \to U \times U\) classifies (structured) contractible maps over \(\Gamma\) between pullbacks of \(p: \dot{U} \twoheadrightarrow U\).

Under the stated hypotheses, the construction is the one due to Voevodsky, described, for instance, in [Shu15, §4] and involves his classifier for contractible maps. As discussed in Digression 3.4.6, we can prove Lemma 3.5.1 using any locally representable and relatively acyclic notion of fibred structure for trivial fibrations.

Proof of Lemma 3.5.1. We construct \(\operatorname{Eq}(\dot{U}) \twoheadrightarrow U \times U\) by first forming the pullbacks on the left below, and then the internal hom between them in the slice over \(U \times U\), as shown on the right:

\[
\begin{array}{c} \dot {U} \times U \longrightarrow \dot {U} \longleftarrow U \times \dot {U} \\ \pi_ {1} ^ {*} \pi \Biggl \downarrow \quad \text {   } \quad \Biggl \downarrow \pi \quad \text {   } \quad \Biggl \downarrow \pi_ {2} ^ {*} \pi \\ U \times U \xrightarrow [ \pi_ {1} ]{} U \xleftarrow [ \pi_ {2} ]{} U \times U \end{array}
\]

\[
\begin{array}{c} \operatorname{Map} _ {U \times U} (\pi_ {1} ^ {*} \dot {U}, \pi_ {2} ^ {*} \dot {U}) \\ \Big \downarrow [ \pi_ {1} ^ {*} \pi , \pi_ {2} ^ {*} \pi ] _ {U \times U} \\ U \times U. \end{array}
\]

By the Frobenius condition, this map is a fibration. The counit \(\epsilon\colon\mathrm{Map}_{U\times U}(\pi_{1}^{*}\dot{U},\pi_{2}^{*}\dot{U})\times_{U\times U}\pi_{1}^{*}\dot{U}\to\pi_{2}^{*}\dot{U}\) equivalently defines a map

\[
\epsilon \colon \operatorname{Map} _ {U \times U} (\pi_ {1} ^ {*} \dot {U}, \pi_ {2} ^ {*} \dot {U}) \times_ {U \times U} \dot {U} \times U \to \operatorname{Map} _ {U \times U} (\pi_ {1} ^ {*} \dot {U}, \pi_ {2} ^ {*} \dot {U}) \times_ {U \times U} U \times \dot {U}
\]

over \(\mathrm{Map}_{U\times U}(\pi_1^*\dot{U},\pi_2^*\dot{U})\), which is the universal map between two pullbacks of \(\pi\), i.e. small fibrations.

We define \(\mathrm{Eq}(\dot{U})\) by equipping this \(\epsilon\) with the data of a contractible map over \(\mathrm{Map}_{U\times U}(\pi_1^*\dot{U},\pi_2^*\dot{U})\), by taking the classifier \(\phi_{p_\epsilon}\colon \mathcal{T}\mathcal{F}(p_\epsilon)\to \mathrm{Map}_{U\times U}(\pi_1^*\dot{U},\pi_2^*\dot{U})\times_{U\times U}\pi_2^*\dot{U}\) for trivial fibration structures on the right Brown factor \(p_\epsilon \colon B_{\mathrm{Map}_U(\pi_1^*\dot{U},\pi_2^*\dot{U})}\epsilon \twoheadrightarrow \mathrm{Map}_{p_\epsilon}(\pi_1^*\dot{U},\pi_2^*\dot{U})\times_{U\times U}\pi_2^*\dot{U}\), pushing it forward to obtain an object over \(\mathrm{Map}_{U\times U}(\pi_1^*\dot{U},\pi_2^*\dot{U})\), and then summing to obtain one over \(U\times U\).

The resulting map \(\operatorname{Eq}(\dot{U}) \to U \times U\) would thus be written in type theory as:

\[
\operatorname{Eq} (\dot {U}) = \Sigma_ {A, B: U} \Sigma_ {f: A \to B} \Pi_ {b: B} \mathcal {T F} (\operatorname{fib} _ {f} (b)) \to U \times U.
\]

It is easily seen to have the stated classifying property (ii). It is a fibration as required by (i) provided that the map \(\phi_{p_{\epsilon}}\colon \mathcal{T}\mathcal{F}(p_{\epsilon})\to \mathrm{Map}_{U\times U}(\pi_1^*\dot{U},\pi_2^*\dot{U})\times_{U\times U}\pi_2^*\dot{U}\) is one. But this follows from Lemma 3.4.3, since \(\mathrm{fib}_f(b)\) is just the right Brown factor \(p_{\epsilon}\colon B_{\mathrm{Map}_U(\pi_1^*\dot{U},\pi_2^*\dot{U})}\epsilon \twoheadrightarrow \mathrm{Map}_{p_{\epsilon}}(\pi_1^*\dot{U},\pi_2^*\dot{U})\times_{U\times U}\pi_2^*\dot{U}\), which is a fibration by Remark 3.2.3.

By the construction just given, the fibration \((s,t)\colon \operatorname {Eq}(\dot{U})\twoheadrightarrow U\times U\) factors as follows:

\[
\operatorname{Eq} (\dot {U}) \xrightarrow [ (s , t) ]{v} \operatorname{Map} _ {U \times U} (\pi_ {1} ^ {*} \dot {U}, \pi_ {2} ^ {*} \dot {U}) ^ {\left[ \pi_ {1} ^ {*} \pi , \pi_ {2} ^ {*} \pi \right] _ {U \times U}} U \times U.
\]

The contractible map classifier just constructed satisfies a relative version of the relative acyclicity property of the following form inherited from relative acyclicity for \(\mathcal{T}\mathcal{F}\).

35

**Lemma 3.5.2.** In a locally cartesian closed category with a cylindrical premodel structure satisfying the Frobenius condition, contractible map structures defined using a locally representable and relatively acyclic notion of fibred structure $\mathcal{TF}$ for trivial fibrations can be aligned along monomorphisms, in the sense that the kernel pair projections lift against monomorphisms:

![img-35.jpeg](img-35.jpeg)

Proof. By construction, the map $\upsilon$ is the pushforward of the classifier

$$\phi_{p_\epsilon} \colon \mathcal{TF}(p_\epsilon) \to \mathrm{Map}_{U \times U}(\pi_1^* \dot{U}, \pi_2^* \dot{U}) \times_{U \times U} \pi_2^* \dot{U}$$

for trivial fibration structures. Since the notion of fibred structure $\mathcal{TF}$ is locally representable and relatively acyclic, by Lemma 2.1.12 the maps in the kernel pair of $\phi_{p_\epsilon}$ lift against monomorphisms. Since monomorphisms are stable under pullback, this condition is stable under pushforward. $\square$

The construction of Lemma 3.5.1 allows us to codify univalence as follows.

**Definition 3.5.3.** A fibration $\pi \colon \dot{U} \twoheadrightarrow U$ is **univalent** if the map $t \colon \mathrm{Eq}(\dot{U}) \twoheadrightarrow U$ is a trivial fibration.

Remark 3.5.4. Definition 3.5.3 connects to the standard homotopy type theoretic encoding of the univalence axiom as follows. By Lemma 3.5.1, the diagonal on $U$ lifts through a map $\mathrm{id} \colon U \to \mathrm{Eq}(\dot{U})$, classifying the identity map. This factorization of the diagonal can be related to the canonical one of the cocylinder by a map $u$, as indicated below:

$$\begin{array}{c} U \xrightarrow{\mathrm{id}} \mathrm{Eq}(\dot{U}) \\ \downarrow_{\epsilon} \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(s,t)} \\ PU \xrightarrow{\partial} U \times U. \end{array}$$

If the base of the universe is fibrant, as will be proven under mild hypotheses in §3.6 below, the map $\partial_1 \colon PU \xrightarrow{\sim} U$ will be a trivial fibration, so in the presence of the 2-of-3 axiom, $t$ is a trivial fibration if and only if $u$ is a weak equivalence.

**Proposition 3.5.5.** Consider a cylindrical premodel structure on a presheaf topos satisfying the Frobenius condition in which the cofibrations are the monomorphisms. If the premodel structure has universes in the sense of Definition 2.3.6, the equivalence extension property holds if and only if each universe $\pi \colon \dot{U} \twoheadrightarrow U$ is univalent.

Proof. To prove the equivalence extension property assuming univalence, choose a univalent universe sufficiently large to classify the data in (3.3.2) by means of a lifting problem

![img-36.jpeg](img-36.jpeg)

For this, we first choose classifying maps $\overline{p}_0 \colon A \to U$ for $p_0$ and $\overline{q}_1 \colon B \to U$ and then use Lemma 3.5.1 to extend the map $(\overline{p}_0, \overline{q}_1 i) \colon A \to U \times U$ to a map $\overline{e} \colon A \to \mathrm{Eq}(\dot{U})$ classifying the contractible map $e$. By univalence, $t$ is a trivial fibration, so this lifting problem has a solution $\overline{f}$, which classifies a contractible map $f$ that pulls back along $i$ to $e$.

36

For the converse, consider a lifting problem as above, and suppose the equivalence extension property holds. By Lemma 3.5.1, the map $\overline{e}$ classifies a contractible map $e$ between fibrations into $A$ as in (3.3.2), while $\overline{q}_1$ classifies a fibration $q_1$ into $B$ that pulls back along $i$ to the codomain of $e$. By the equivalence extension property, the equivalence extends to an equivalence $f$ over $B$ with codomain $q_1$ at the same universe level. Using the given universe and relative acyclicity of its associated notion of fibred structure, we obtain a classifying map $\overline{q}_1$ for $q_1$ so that the exterior rectangle of classifying maps commutes:

![img-37.jpeg](img-37.jpeg)

In fact, by the universal property of the fibration $[\pi_1^*\pi, \pi_2^*\pi]_{U\times U} \colon \mathrm{Map}_{U\times U}(\pi_1^*\dot{U}, \pi_2^*\dot{U}) \twoheadrightarrow U\times U$ and commutativity the diagram (3.3.2), the interior of the diagram commutes as well. Thus, our original lifting problem factors as displayed below:

![img-38.jpeg](img-38.jpeg)

and can be solved by Lemma 3.5.2, which aligns the equivalence structure on $f$ with that of $e$. $\square$

3.6. **Fibrant universes.** We next introduce an axiomatic setup that allows us to use Proposition 3.5.5 to infer that the universes $\pi \colon \dot{U} \to U$ of fibrations have fibrant base objects $U$. Our argument follows that in [ABCHFL21, 2.12].

Suppose that $\mathsf{E}$ has a (cofibration, trivial fibration) weak factorization system in which every object is cofibrant, and let $P \colon \mathsf{E} \to \mathsf{E}$ be a finite-product preserving endofunctor equipped with a natural retraction, i.e. $\epsilon \colon \mathrm{id} \Rightarrow P$ and $\delta \colon P \Rightarrow \mathrm{id}$ such that $\delta \cdot \epsilon = \mathrm{id}$. For instance, $P$ could be the cocylinder part of an adjoint functorial cylinder with $\delta$ taken to be either $\partial_0$ or $\partial_1$. Alternately:

**Example 3.6.1.** For any object $I$ in a cartesian closed category $\mathsf{E}$, we have a diagram in the slice $\mathsf{E}_{/I}$

![img-39.jpeg](img-39.jpeg)

expressing the terminal object as a retract of $I$ pulled back to the slice. Here $\delta$ is the diagonal map and $\epsilon$ is the product projection obtained by pulling back $I \to 1$ to the slice. Exponentiating by these objects defines an endofunctor $P \colon \mathsf{E}_{/I} \to \mathsf{E}_{/I}$ together with natural transformations $\epsilon \colon \mathrm{id} \Rightarrow P$ and $\delta \colon P \Rightarrow \mathrm{id}$ such that $\delta \cdot \epsilon = \mathrm{id}$.

37

By a reflexive relation $R \rightrightarrows X$ on an object $X$ we mean a factorization of the diagonal:

![img-40.jpeg](img-40.jpeg)

Note that we do not require the canonical pairing $(s, t) \colon R \to X \times X$ to be monic.

Definition 3.6.2. A $\delta$-contractor for a reflexive relation $R \rightrightarrows X$ is a map $c \colon PX \to PR$ making the following diagrams commute:

![img-41.jpeg](img-41.jpeg)

![img-42.jpeg](img-42.jpeg)

Remark 3.6.3. To gain some intuition for this definition, suppose we are in a topological setting and $PX = X^I$ is the path space functor, $\epsilon$ the constant path operation, and $\delta$ evaluates a path at some fixed point $i \in I$. A $\delta$-contractor $c$ takes a path $p \colon x_0 \rightsquigarrow x_1$ in $X$ and produces a square as shown below, where the horizontal arrows are paths, the vertical arrows are witnesses to the relation $R$, and $x_i$ is the value of $p$ at $i$:

![img-43.jpeg](img-43.jpeg)

The first diagram in Definition 3.6.2 determines the horizontal arrows: it asks that $c$ is a path of witnesses relating $p$ to the constant path $\epsilon(x_i)$. The second diagram asks that the value of $c$ at $i$, which relates $x_i$ to itself, is the reflexivity for $R$.

Lemma 3.6.4. Let $R \rightrightarrows X$ be a reflexive relation. If the Leibniz pullback application of $\delta$ to $(s, t) \colon R \to X \times X$ is a trivial fibration, then $R$ has a $\delta$-contractor.

Proof. The required diagrams from 3.6.2 can be repackaged into a single lifting problem as follows:

![img-44.jpeg](img-44.jpeg)

But the vertical map is the said Leibniz pullback application $\delta \circ (s, t)$, which is assumed to be a trivial fibration, and so there is the indicated lift $c$, since all objects are cofibrant. $\square$

Lemma 3.6.5. Let $R \rightrightarrows X$ be a reflexive relation with a $\delta$-contractor. Consider the square

![img-45.jpeg](img-45.jpeg)

as a morphism $t \to !_X$ in $\mathsf{E}^2$. The image of this morphism under the Leibniz pullback application functor $\delta \circ - \colon \mathsf{E}^2 \to \mathsf{E}^2$ is a split epimorphism.

38

Proof. The claim is that the canonical square on the right below admits a section

$$\begin{array}{c} P X \xrightarrow {c} P R \xrightarrow {P s} P X \\ \delta_ {X} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \xrightarrow [ (\epsilon_ {X} , r) ]{} P X \times_ {X} R \xrightarrow [ s \pi ]{} X. \end{array}$$

The notion of a $\delta$-contractor is such that the indicated maps constitute just such a section. $\square$

Lemma 3.6.6. Let $R \rightrightarrows X$ be a reflexive relation such that the Leibniz pullback applications of $\delta$ to $(s, t) \colon R \to X \times X$ and $t \colon R \to X$ are both trivial fibrations. Then $\delta_X \colon PX \to X$ is also a trivial fibration.

Proof. Note that $\delta_X \colon PX \to X$ is the Leibniz pullback application of $\delta$ to $!_X \colon X \to 1$. By Lemmas 3.6.4 and 3.6.5, $\delta \hat{\circ}!_X$ is a retract of $(Pt, \delta_R) = \delta \hat{\circ} t$ and thus a trivial fibration. $\square$

When the fibrations are created from the trivial fibrations in a particular way, Lemma 3.6.6 can be used to establish the fibrancy of an object $X$ admitting a suitable reflexive relation. For later use, we introduce the following general definitions.

Definition 3.6.7. Let $\mathsf{E}$ be a (locally) cartesian closed category with a class of trivial fibrations.

- (i) Relative to an interval object $\delta_0, \delta_1 \colon 1 \to I$ in $\mathsf{E}$, the biased fibrations are those maps whose Leibniz exponentials by $\delta_0$ and $\delta_1$ are trivial fibrations.
- (ii) Relative to an object $I \in \mathsf{E}$, the unbiased fibrations are those maps for which the Leibniz exponential of their pullback to the slice over $I$ by the diagonal $\delta \colon I \to I \times I$ is a trivial fibration in the slice.

Proposition 3.6.8. Let $\mathsf{E}$ be a cartesian closed category with a premodel structure in which its fibrations are the biased fibrations defined relative to an interval object. Then an object $X$ is fibrant if it has a reflexive relation $s, t \colon R \rightrightarrows X$ such that both $(s, t) \colon R \to X \times X$ and $t \colon R \to X$ are fibrations.

Proof. As in Example 3.6.1, exponentiation by the interval defines an endofunctor $(-)^I$ equipped with a natural retraction $\epsilon \colon \mathrm{id} \Rightarrow (-)^I$ and $\delta_0, \delta_1 \colon (-)^I \Rightarrow \mathrm{id}$. Applying Lemma 3.6.6 separately with $\delta_0$ and $\delta_1$, we see that both $(\delta_0)_X = \delta_0 \hat{\circ}!_X$ and $(\delta_1)_X = \delta_1 \hat{\circ}!_X$ are trivial fibrations, proving that $X$ is fibrant. $\square$

Proposition 3.6.9. Let $\mathsf{E}$ be a cartesian closed category with a premodel structure in which the fibrations are the unbiased fibrations defined relative to an object $I$. Then an object $X$ is fibrant if it has a reflexive relation $s, t \colon R \rightrightarrows X$ such that $(s, t) \colon R \to X \times X$ and $t \colon R \to X$ are both fibrations.

Proof. By Example 3.6.1 the standing hypotheses of this section are satisfied in the slice over $I$. The fibrations $(s, t) \colon R \twoheadrightarrow X \times X$ and $t \colon R \twoheadrightarrow X$ pullback to fibrations in the sliced premodel structure over $I$. Lemma 3.6.6 applies, and $\delta \hat{\circ}!_{X \times I}$ is therefore a trivial fibration, proving that $X$ is fibrant. $\square$

We now combine these observations with the construction of the previous section to prove that the universe is a fibrant object under the combined hypotheses of these sections.

Proposition 3.6.10. Suppose $\mathsf{E}$ is a presheaf topos with a cylindrical premodel structure satisfying the Frobenius condition in which the cofibrations are the monomorphisms. If the fibrations are characterized as in Proposition 3.6.8 or 3.6.9 and have universes, then the bases of the universal fibrations $\pi \colon \hat{U} \twoheadrightarrow U$ are fibrant objects.

39

*Proof.* By Lemma 3.5.1, the fibration $\pi: \dot{U} \to U$ gives rise to a reflexive relation $\operatorname{Eq}(\dot{U}) \rightrightarrows U$ for which the pairing $\operatorname{Eq}(\dot{U}) \to U \times U$ is a fibration. By Theorem 3.3.3, the equivalence extension property holds, so by Proposition 3.5.5 the map $t: \operatorname{Eq}(\dot{U}) \xrightarrow{\sim} U$ is a trivial fibration, and in particular a fibration. Now either Proposition 3.6.8 or 3.6.9 applies to conclude that $U$ is fibrant. $\square$

**3.7. Fibration extension property and 2-of-3.** Recall Definition 2.3.6, which introduces what it means for a premodel structure on a presheaf topos to have universes. We say that a premodel structure **has fibrant universes** if in addition the base of each of these universes for each sufficiently large inaccessible cardinal is fibrant.

The aim of this section will be to connect the fibrancy of the universes to a useful property of the premodel structure.

**Definition 3.7.1.** A premodel structure on a presheaf topos satisfies the **fibration extension property** just when, for each sufficiently large inaccessible cardinal $\kappa$, any $\kappa$-small fibration $p: X \to A$, and trivial cofibration $t: A \xrightarrow{\sim} B$, there exists a $\kappa$-small fibration over $B$ which pulls back to $p$ along $t$:

$$\begin{array}{ccc} X & \dashrightarrow & Y \\ p \downarrow & \downarrow^\perp & \downarrow^q \\ A & \xleftarrow[\text{t}]{} & B. \end{array}$$

There is a well-known connection between the fibration extension property and fibrancy of the universe [Shu15] that we spell out carefully because we are working with a somewhat different axiomatization here.

**Lemma 3.7.2.** *Any premodel structure on a presheaf topos with fibrant universes has the fibration extension property. Conversely, if a premodel structure with the fibration extension property has universes, then those universes have fibrant base objects.*

*Proof.* We first show that fibrant universes imply the fibration extension property. For any fibration $p: X \to A$, we have a classifying universe $\pi: \dot{U} \to U$ with fibrant base $U$. In particular, this choice defines a classifying map and thus a lifting problem

$$\begin{array}{ccc} A & \xrightarrow{\bar{p}} & U, \\ j \downarrow^\perp & \searrow^\pi & \\ B & & \end{array}$$

which admits a solution since $U$ is fibrant. The pullback of $\pi$ along this map, displayed below-right, defines a small fibration over $B$. The pullback square for $p$ factors through the one for $q$ defining the desired extension square:

$$\begin{array}{ccc} X & \xrightarrow{\quad} & Y \xrightarrow{\quad} & \tilde{U} \\ p \downarrow^\perp & \downarrow^\perp & q \downarrow^\perp & \downarrow^\pi \\ A & \xrightarrow{\quad} & B \xrightarrow{\bar{q}} & U. \\ & \xrightarrow{\bar{p}} & & \\ & & 40 \end{array}$$

Conversely, suppose the fibration extension property holds and consider a lifting problem into the base of one of the universal fibrations:

![img-46.jpeg](img-46.jpeg)

Define a fibration $p: X \rightarrow A$ by pulling back $\pi$ along $\bar{p}$. Then use the fibration extension property to extend this to a fibration $q: Y \rightarrow B$ that pulls back along $j$ to $p$. As required by Definition 3.7.1, this extended fibration is classified by the same universe. Using the given universe and relative acyclicity of its associated notion of fibred structure, the classifying map $\bar{p}$ extends along $j$ to a classifying map $\bar{q}$ for $q$ so that $\bar{q} \cdot j = \bar{p}$, solving the lifting problem. This proves that the fibration extension property implies fibrancy of the universe. $\square$

We can now make use of the following result from [CS25], the proof of which is entirely axiomatic.

**Proposition 3.7.3** ([CS25, 3.31]). *Let $\mathsf{E}$ be a cylindrical premodel category in which all objects are cofibrant. If the fibration extension property holds, then the weak equivalences satisfy the 2-of-3 condition.*

Thus, the constructions of a model of homotopy type theory and of a Quillen model structure from a cylindrical premodel category with all objects cofibrant are intertwined. First one checks the equivalence extension property, which is the heart of the interpretation of univalence. Then one proves the Frobenius condition, which provides the interpretation of $\Pi$-types and is connected to right properness of the model structure. The equivalence extension property and Frobenius condition may then also play a role in the construction of fibrant universes. Besides interpreting the universes of the type theory, the fibrant universes can be used to derive the fibration extension property, which then yields the model structure. In the sequel, we see two versions of this story, both showing that a cylindrical premodel structure is a model structure, first in cubical species and then in cubical sets.

#### 4. THE INTERVAL MODEL STRUCTURE ON CUBICAL SPECIES

On a presheaf topos with a suitable interval object there is a now well-known strategy for defining a model structure that models homotopy type theory. The cofibrations are the monomorphisms, making the trivial fibrations those of Definition 2.2.12. The fibrations are then defined from the trivial fibrations as either the *biased* or *unbiased* fibrations of Definition 3.6.7.$^9$ The results in the previous section then apply to establish the equivalence extension property, the Frobenius condition, the fibration extension property, the univalence and fibrancy of the universes, and verify the 2-of-3 condition for the weak equivalences.

Here we apply this outline not in the category of cubical sets but in the category of *cubical species* introduced in §4.2, which has a suitable “symmetric” interval object. The category of cubical species is a category of groupoid-indexed functors valued in cubical sets, so in §4.1 we first discuss some general results about subobject classifiers, pushforwards, and tiny objects that apply in that general setting. In §4.3, we establish the cylindrical premodel structure on cubical species. Then in §4.4, we apply the results from §3 to prove that this premodel structure is a model structure modeling homotopy type theory.

$^9$As noted in [CS25, 4.22–23] and Proposition 6.1.7, sometimes these classes coincide.

41

4.1. **Groupoid-indexed diagram categories.** We collect some statements about diagram categories indexed by a groupoid. In fact, the first few results apply more generally to category-indexed diagrams.

**Lemma 4.1.1.** *In a diagram category $\mathsf{E}^\mathsf{C}$ whose base category $\mathsf{E}$ has pullbacks, consider a cartesian natural transformation $f: Y \rightarrow X$. The family of evaluation functors $c^*: \mathsf{E}^\mathsf{C} \rightarrow \mathsf{E}$ at objects $c: 1 \rightarrow C$ creates pushforward along $f$.*

*Proof.* The slice of $\mathsf{E}^\mathsf{C}$ over $X$ is the lax bilimit of the categories $\mathsf{E}_{/X(c)}$ indexed over $c \in \mathsf{C}$, with functorial action given by pullback, and similarly for $Y$. For each $u: c \rightarrow d$ in $\mathsf{C}$, there are canonical isomorphisms $f_c^* X_u^* \cong Y_u^* f_d^*$ satisfying coherence under pasting. Thus, the pullback functor $f^*: \mathsf{E}_{/X} \rightarrow \mathsf{E}_{/Y}$ is given by functoriality of lax bilimits from pullback along the components of $f$.

Since the naturality square of $f$ at $u$ is a pullback, the mate $(Y_u)_! f_c^* \rightarrow f_d^*(X_u)_!$ is invertible. By adjointness, so is the mate $X_u^*(f_d)_* \rightarrow (f_c)_* Y_u^*$, assuming we have pushforward along the components of $f$. Therefore, the pullback-pushforward adjunctions at each level assemble into an indexed adjunction. By bifunctoriality of lax bilimits, this gives a right adjoint to pullback along $f$. $\square$

**Lemma 4.1.2.** *In category of diagrams $\mathsf{E}^\mathsf{C}$ whose base category $\mathsf{E}$ has binary products, consider a diagram $A$ with invertible functorial actions. The family of evaluation functors $c^*: \mathsf{E}^\mathsf{C} \rightarrow \mathsf{E}$ at objects $c: 1 \rightarrow C$ creates exponential with $A$ and its right adjoint.*

*Proof.* We argue similarly to the previous proof. The product with $A$ is given bifunctorially from product with $A(c)$ at level $c \in \mathsf{C}$ and invertibility of the map $(-) \times A(c) \rightarrow (-) \times A(d)$ for $u: c \rightarrow d$, using that $A_u$ is invertible. Assuming levelwise exponentials, the induced map on right adjoints $(-)^{A(d)} \rightarrow (-)^{A(c)}$ is invertible. Assuming further right adjoints $(-)^{A(c)} \dashv (-)_{A(c)}$ for $c \in \mathsf{C}$, so is the induced map $(-)_{A(c)} \rightarrow (-)_{A(d)}$. Bifunctoriality of lax bilimits gives the desired right adjoints $(-)^A$ and $(-)_A$. $\square$

**Lemma 4.1.3.** *Consider a category $\mathsf{E}$ with pullbacks and a subobject classifier $1 \rightarrow \Omega$, and the constant diagram functor $\Delta: \mathsf{E} \rightarrow \mathsf{E}^\mathsf{C}$. Then $\Delta 1 \rightarrow \Delta \Omega$ classifies monomorphisms that define cartesian natural transformations in $\mathsf{E}^\mathsf{C}$.*

*Proof.* Note that cartesian natural transformations are closed under pullback and that the claimed classifier is one. Given a cartesian natural transformation that is a componentwise monomorphism, its levelwise classifying squares assemble into a (unique) classifying square by pullback pasting and uniqueness of classification. Since $\mathsf{E}$ has pullbacks, monomorphisms in $\mathsf{E}^\mathsf{C}$ are componentwise monomorphisms. $\square$

For a groupoid $\mathsf{G}$, every functor from $\mathsf{G}$ to $\mathsf{E}$ has invertible functorial action and every natural transformation between such functors is cartesian. Therefore:

**Corollary 4.1.4.** *Consider a locally cartesian closed category $\mathsf{E}$. For each groupoid $\mathsf{G}$, the functor category $\mathsf{E}^\mathsf{G}$ is locally cartesian closed. For each functor $F: \mathsf{G} \rightarrow \mathsf{H}$ between groupoids, restriction $F^*: \mathsf{E}^\mathsf{H} \rightarrow \mathsf{E}^\mathsf{G}$ preserves pushforward.* $\square$

**Corollary 4.1.5.** *Consider a cartesian closed category $\mathsf{E}$. For each groupoid $\mathsf{G}$, an object $A \in \mathsf{E}^\mathsf{C}$ is tiny if it is componentwise tiny. For each functor $F: \mathsf{G} \rightarrow \mathsf{H}$ between groupoids, restriction $F^*: \mathsf{E}^\mathsf{H} \rightarrow \mathsf{E}^\mathsf{G}$ preserves exponentiation with componentwise tiny objects.* $\square$

**Corollary 4.1.6.** *Consider a finitely complete category $\mathsf{E}$ with a subobject classifier. For each groupoid $\mathsf{G}$, the functor category $\mathsf{E}^\mathsf{G}$ has a subobject classifier. For each functor $F: \mathsf{G} \rightarrow \mathsf{H}$ between groupoids, restriction $F^*: \mathsf{E}^\mathsf{H} \rightarrow \mathsf{E}^\mathsf{G}$ preserves subobject classifiers.* $\square$

42

4.2. Cubical species and the symmetric interval. The “cubical” in the phrase cubical species refers to the cartesian cube category, defined below. In Buchholtz and Morehouse’s taxonomy of cube categories [BM17], this is $\mathbb{C}_{(\mathrm{wec},\cdot)}$.

Definition 4.2.1. The cartesian cube category $\square := \mathsf{Fin}_{\perp \neq \top}^{\mathrm{op}}$ is the opposite of the category of finite strictly bipointed sets and bipointed maps. Its objects are bipointed sets of the form $\{\bot, 1, \dots, n, \top\}$ for $n \geq 0$. We write $\mathsf{cSet} := \widehat{\square}$ for the topos of presheaves and call its objects (cartesian) cubical sets. Under the Yoneda embedding $\bot: \square \to \mathsf{cSet}$, the object $\{\bot, 1, \dots, n, \top\}$ is identified with the $n$-cube $I^n$. By the Yoneda lemma, morphisms $\alpha: I^m \to I^n$ correspond to functions $\alpha: \{\bot, 1, \dots, n, \top\} \to \{\bot, 1, \dots, m, \top\}$ preserving the basepoints $\bot$ and $\top$.

Let $\Sigma \cong \coprod_{k \geq 1} \Sigma_k$ be the maximal subgroupoid of the cube category $\square$ excluding, for reasons explained in Remark 4.3.17, the identity automorphism of the 0-cube. Here $\Sigma_k$ is the one-object groupoid associated to the symmetric group $\Sigma_k$, which acts on $\{\bot, 1, \dots, k, \top\}$ by permuting the indices and thus acts on the representable cubical set $I^k$ by permuting the dimensions.

Definition 4.2.2. A cubical species is a set-valued functor on $\square^{\mathrm{op}} \times \Sigma$.

It is convenient to represent a cubical species as a symmetric sequence of cubical sets, i.e., as a family $\mathbb{X} = (X^k)_{k \geq 1}$ of cubical sets, in which each $X^k$ has a specified $\Sigma_k$-action. Indeed, as a category we have

$$\mathsf{Set}^{\square^{\mathrm{op}} \times \Sigma} \cong \mathsf{cSet}^{\Sigma} \cong \prod_{k \geq 1} \mathsf{cSet}^{\Sigma_k}.$$

A cubical species that is non-empty in only a single factor $\mathsf{cSet}^{\Sigma_k}$ is said to be concentrated in degree $k$.

Write $\mathbb{F}_k: \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$ for left Kan extension along $*_k: \mathbb{1} \to \Sigma$, the left adjoint to the functor $U_k: \mathsf{cSet}^{\Sigma} \to \mathsf{cSet}$ which projects to the $k$th component of the cubical species and forgets the action:

![img-47.jpeg](img-47.jpeg)

Definition 4.2.3. For $k \geq 1$, a $k$-free cubical species is a cubical species of the form $\mathbb{F}_k X$ for $X \in \mathsf{cSet}$. Explicitly, the $k$-free cubical species $\mathbb{F}_k X$ is concentrated in degree $k$ with free $\Sigma_k$-action on the cubical set $X \times \Sigma_k$.

We highlight two particularly important examples of cubical species.

Example 4.2.4. The representable cubical species

$$\hom_{\square \times \Sigma^{\mathrm{op}}} \bigl(-, ([n], *_k)\bigr),$$

represented by the pair of objects $[n] = \{\bot, 1, \dots, n, \top\} \in \square$ and $*_k \in \Sigma$, is the free cubical species $\mathbb{F}_k I^n$ concentrated in degree $k$ and given there by the cubical set $I^n \times \Sigma_k$ with the free $\Sigma_k$-action.

Example 4.2.5. The restriction of the hom bifunctor $\hom \in \mathsf{Set}^{\square^{\mathrm{op}} \times \square}$ along the inclusion $\Sigma \hookrightarrow \square$ in the codomain variable defines a cubical species $\mathbb{I}$ whose $k$th component is the geometric $k$-cube $I^k$ with its regular action, permuting the $k$ dimensions.

Remark 4.2.6. The symmetric interval $\mathbb{I}$ has $2^\omega$ points $\mathbb{1} \to \mathbb{I}$: for any countable sequence $\vec{v}$ of 0s and 1s there is a corresponding point $\vec{v}: \mathbb{1} \to \mathbb{I}$ that chooses either the initial or final vertex in each component. Since the terminal cubical species $\mathbb{1}$ has a trivial action in each component, all points of the interval are fixed points for the coordinatewise actions of the symmetric groups.

43

**Lemma 4.2.7.** *The cubical species $\mathbb{I}$ is tiny.*

*Proof.* Recall that $\mathbb{I}(c) = \square(-, c) \in \mathsf{cSet}$ is representable. Since $\square$ has binary products, representables in $\mathsf{cSet}$ are tiny. Now $\mathbb{I}$ is tiny by Corollary 4.1.5. $\square$

**4.3. The cylindrical premodel structure on cubical species.** We determine a pair of (algebraic) weak factorization systems that constitute a premodel structure on the cubical species and prove that it is cylindrical, with adjoint functorial cylinder represented by the interval object

$$\mathbb{1} \xrightarrow[\delta_1]{\delta_0} \mathbb{I} \xrightarrow{!} \mathbb{1}$$

where the points $\delta_0, \delta_1$ correspond to the constant sequences $\vec{0}, \vec{1}$ of Remark 4.2.6.

As a presheaf topos, the category $\mathsf{cSet}^{\mathbb{I}}$ has a subobject classifier $\top: \mathbb{1} \mapsto \Omega$, which we can describe explicitly as follows.

**Lemma 4.3.1.** *For $n, k \in \mathbb{N}$, $k \ge 1$, elements $\chi_c: \mathbb{F}_k I^n \to \Omega$ of the subobject classifier correspond bijectively to subobjects $c: C \mapsto I^n$ of the $n$-cube.*

*Proof.* By definition, an element $\chi_c: \mathbb{F}_k I^n \to \Omega$ corresponds to a subobject of the representable cubical species $\mathbb{F}_k I^n$. Since $\mathbb{F}_k I^n$ is concentrated in degree $k$ and has a free $\Sigma_k$-action, its subobject must have these properties as well. Thus, we see that the subobject has the form $\mathbb{F}_k c: \mathbb{F}_k C \mapsto \mathbb{F}_k I^n$ for a necessarily unique subobject $c: C \mapsto I^n$ of the $n$-cube. $\square$

**Definition 4.3.2.** As the **cofibrations** we take the monomorphisms, which are classified (up to equivalence) by the subobject classifier $\top: \mathbb{1} \mapsto \Omega$. The **trivial fibrations** are then the maps with the right lifting property against all monomorphisms.

As we saw in §2.2, the cofibrations and trivial fibrations form a weak factorization system. By Lemma 2.2.10, we can recognize the trivial fibrations as the class underlying a locally representable and relatively acyclic notion of fibred structure $\mathbb{TF}$.

We now turn to the (trivial cofibration, fibration) weak factorization system. The fibrations will be the unbiased fibrations of Definition 3.6.7(ii)—see Theorem 4.3.14—which we now describe explicitly. The fibrations will be determined by the trivial fibrations, by Leibniz pullback application of the evaluation natural transformation $\mathrm{ev}: (-)^{\mathbb{I}} \times \mathbb{I} \Rightarrow (-)$ involving the interval $\mathbb{I}$. Equivalently, we may describe them as given by right lifting against a category of generating trivial cofibrations constructed using the universal subobject $\top: \mathbb{1} \to \Omega$ and the “generic point” $\delta: \mathbb{I} \to \mathbb{I} \times \mathbb{I}$—see Definition 4.3.11. With the latter description, we can obtain a functorial factorization (indeed, an awfs) constructively using Garner’s algebraic small object argument.

**Definition 4.3.3.** As a map in the slice category $\mathsf{cSet}_{/\mathbb{I}}^{\mathbb{I}}$, the diagonal $\delta: \mathbb{I} \to \mathbb{I} \times \mathbb{I}$ defines an additional point of $\mathbb{I}$, called the **generic point**.

The morphisms $\top: \mathbb{1} \to \Omega$ in $\mathsf{cSet}_{/\Omega}^{\mathbb{I}}$ and $\delta: \mathbb{I} \to \mathbb{I} \times \mathbb{I}$ in $\mathsf{cSet}_{/\mathbb{I}}^{\mathbb{I}}$ can be reindexed to lie in the common slice $\mathsf{cSet}_{/\Omega \times \mathbb{I}}^{\mathbb{I}}$. Their pushout product there defines a family of maps $\top \hat{\times}_{\Omega \times \mathbb{I}} \delta$ internally

44

indexed by the object $\Omega \times \mathbb{I}$:

![img-48.jpeg](img-48.jpeg)

Our category of generating trivial cofibrations will be given by externalizing the family $\top \hat{\times}_{\Omega \times \mathbb{I}} \delta$ and will therefore be indexed by the category of elements of $\Omega \times \mathbb{I}$.

*Remark 4.3.4.* Since in general $\int_{\mathbb{X}} 1 \cong \mathbb{X}$, and the category of elements functor $\int$ preserves pullbacks, the category of elements of a product is the pullback of the categories of elements:

$$\begin{array}{ccc} \int \Omega \times \mathbb{I} & \longrightarrow & \int \Omega \\ \downarrow & \downarrow \downarrow & \downarrow \\ \int \mathbb{I} & \longrightarrow & \square \times \Sigma^{\text{op}}. \end{array}$$

Now $\mathbb{I}$ is a restriction of the hom bifunctor, so its category of elements is a restriction of the twisted arrow category. Thus, the objects of $\int \Omega \times \mathbb{I}$ are pairs $(c, \zeta)$ as displayed vertically below while $(\alpha, \sigma): (d, \xi) \rightarrow (c, \zeta)$ defines a morphism just when the displayed diagram of cubical sets commutes, and the top square is a pullback:

$$\begin{array}{ccc} D & \xrightarrow{\alpha} & C \\ d \downarrow & \downarrow \downarrow & \downarrow c \\ I^m & \xrightarrow{\alpha} & I^n \\ \xi \downarrow & & \downarrow \zeta \\ I^k & \xleftarrow{\sigma} & I^k. \end{array} \quad (4.3.5)$$

As observed in *Remark 4.3.4*, the elements of $\Omega \times \mathbb{I}$ stand in bijection with maps $(\chi_c, \zeta): \mathbb{F}_k I^n \rightarrow \Omega \times \mathbb{I}$ where $\chi_c: \mathbb{F}_k I^n \rightarrow \Omega$ classifies a subobject $c: C \mapsto I^n$ of the cubical set $I^n$ and $\zeta: \mathbb{F}_k I^n \rightarrow \mathbb{I}$, by adjunction, corresponds to a map $\zeta: I^n \rightarrow U_k \mathbb{I} \cong I^k$ in $\square$. Thus, we regard the objects in $\int \Omega \times \mathbb{I}$ as composable pairs of cubical set morphisms

$$\begin{array}{ccc} C & \xleftarrow{c} & I^n \\ & \swarrow & \swarrow \\ & I^k, & \end{array}$$

which we call **triangles**.

**Construction 4.3.6.** The family of maps $\top \hat{\times}_{\Omega \times \mathbb{I}} \delta$ internally indexed by the object $\Omega \times \mathbb{I}$ can be externalized to define a functor $J: \int \Omega \times \mathbb{I} \rightarrow (\mathsf{cSet}^{\Sigma})^2$ externally indexed by the category of

45

elements of \(\Omega \times \mathbb{I}\) and defined by pulling back the given internal family of maps to representables. The cartesian functor \(J\) lifts the Yoneda embedding \(\nmid\) from the discrete fibration associated to the category of elements of the functor \(\Omega \times \mathbb{I}\) to the codomain fibration:

\[
\begin{array}{c} \int \Omega \times \mathbb {I} \xrightarrow {J} (\mathrm{cSet} ^ {\Sigma}) ^ {2} \\ \pi \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \square \times \Sigma^ {\mathrm{op}} \xrightarrow {\perp} \mathrm{cSet} ^ {\Sigma}. \end{array}
\]

Explicitly, the functor \( J \) sends an element \( (c, \zeta) \) to the pullback along it of the universal element \( \top \hat{\times} \delta \), as indicated below:

![img-49.jpeg](img-49.jpeg)

The resulting map \( J(c, \zeta) = (\chi_c, \zeta)^*(\top \hat{\times} \delta) \) can also be computed as the pushout product of the subobject \( \mathbb{F}_k c \colon \mathbb{F}_k C \mapsto \mathbb{F}_k I^n \) and the generic point \( \delta \colon \mathbb{I} \to \mathbb{I} \times \mathbb{I} \) regarded as maps in the slice over \( \mathbb{I} \) via \( \zeta \colon \mathbb{F}_k I^n \to \mathbb{I} \) and \( \pi \colon \mathbb{I} \times \mathbb{I} \to \mathbb{I} \).

Note the map \(\delta\) pulls back along \((\chi_c, \zeta)\) to define the graph \((\mathbb{F}_k C, \zeta \cdot \mathbb{F}_k c) \colon \mathbb{F}_k C \to \mathbb{F}_k C \times \mathbb{I}\) of \(\zeta \cdot \mathbb{F}_k c \colon \mathbb{F}_k C \to \mathbb{I}\) and similarly \(\Omega \times \delta\) pulls back to define the graph of \(\zeta \colon \mathbb{F}_k I^n \to \mathbb{I}\). Henceforth, for any map \(\gamma \colon \mathbb{A} \to \mathbb{B}\), we shall write \([\gamma] \colon \mathbb{A} \to \mathbb{A} \times \mathbb{B}\) for its graph \((\mathbb{A}, \gamma)\).

Morphisms in \(\int \Omega \times \mathbb{I}\)

\[
\begin{array}{c} \mathbb {F} _ {k} I ^ {m} \xrightarrow [ (\chi_ {d} , \xi) ]{\alpha \times \sigma} \mathbb {F} _ {k} I ^ {n} \\ \Omega \times \mathbb {I} \end{array}
\]

correspond to pairs \(\alpha\colon I^{m}\to I^{n}\) and \(\sigma\in\Sigma_{k}\) as in (4.3.5). The functor \(J\) carries such a morphism to the following pullback square of cubical species:

\[
\begin{array}{c} \mathbb {F} _ {k} I ^ {m} \cup_ {\mathbb {F} _ {k} D} \mathbb {F} _ {k} D \times \mathbb {I} \xrightarrow {\alpha \times \sigma \times 1} \mathbb {F} _ {k} I ^ {n} \cup_ {\mathbb {F} _ {k} C} \mathbb {F} _ {k} C \times \mathbb {I} \\ \langle [ \xi ], \mathbb {F} _ {k} d \times 1 \rangle \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \end{array} \tag {4.3.7}
\]

We refer to the subobjects in the image of the functor J as open boxes, though the nature of the gluing of the “lid”  \( F_{k}I^{n} \)  onto the “box”  \( F_{k}C \times I \)  is somewhat subtle because it involves the map  \( \zeta: F_{k}I^{n} \to I \) . The open boxes are themselves pushout products on account of the following general lemma.

46

**Lemma 4.3.8.** If $i$ is a morphism in the slice over $\mathbb{X}$ and $j$ is a morphism in the slice over $\mathbb{Y}$ and $(x, y): \mathbb{Z} \to \mathbb{X} \times \mathbb{Y}$, then the pushout product of $i$ and $j$ in the slice over $\mathbb{X} \times \mathbb{Y}$ pulls back along $(x, y)$ to the map over $\mathbb{Z}$ obtained as the pushout product over $\mathbb{Z}$ of the evident pullbacks of $i$ and $j$.

*Proof.* Pushout products in slices are stable under pullback.

**Corollary 4.3.9.** *The open box*

$$\mathbb{F}_k I^n \cup_{\mathbb{F}_k C} \mathbb{F}_k C \times \mathbb{I} \xrightarrow{\langle [\zeta], \mathbb{F}_k c \times 1 \rangle} \mathbb{F}_k I^n \times \mathbb{I}$$

is the pushout product over $\mathbb{F}_k I^n$ of the maps obtained by pullback

![img-50.jpeg](img-50.jpeg)

![img-51.jpeg](img-51.jpeg)

*Remark 4.3.10.* Since the representables are concentrated in a single degree, each open box is as well. The “triangle” of cubical sets as below-left—where the first map is a morphism and the second map is between representables—gives rise to the “open-box” of cubical species as below-center, concentrated in degree $k$:

$$\begin{array}{ccc} C \xrightarrow{c} I^n & \mathbb{F}_k I^n \cup_{\mathbb{F}_k C} \mathbb{F}_k C \times \mathbb{I} & \Sigma_k \times I^n \cup_{\Sigma_k \times C} \Sigma_k \times C \times I^k \\ I^k & \downarrow \langle [\zeta], \mathbb{F}_k c \times 1 \rangle & \downarrow \langle [\zeta^{\Sigma_k}], 1 \times c \times 1 \rangle \\ & \mathbb{F}_k I^n \times \mathbb{I} & \Sigma_k \times I^n \times I^k. \end{array}$$

The non-empty component of this map is the map of $\Sigma_k$-cubical sets above-right, defined by the pushout below:

![img-52.jpeg](img-52.jpeg)

Here the action of $\Sigma_k$ is trivial on $C$ and $I^n$; by left multiplication on $\Sigma_k$; and by permuting the dimensions on $I^k$—the “regular” action. The map $[\zeta^{\Sigma_k}]: I^n \times \Sigma_k \to I^n \times \Sigma_k \times I^k$ is the graph of a twisted version of $\zeta$: the map $\zeta^{\Sigma_k}: I^n \times \Sigma_k \to I^k$ acts on the component of the domain coproduct indexed by $\sigma \in \Sigma_k$ by $\sigma \cdot \zeta: I^n \to I^k$. The top-right map is defined similarly. Note the maps in the pushout diagram are all $\Sigma_k$-equivariant, as required.

Similarly, the pullback square (4.3.7) is concentrated in degree $k$ and has the form

$$\begin{array}{ccc} I^m \times \Sigma_k \cup_{D \times \Sigma_k} D \times \Sigma_k \times I^k & \xrightarrow{\alpha \times \sigma \times 1} & I^n \times \Sigma_k \cup_{C \times \Sigma_k} C \times \Sigma_k \times I^k \\ \langle [\xi^{\Sigma_k}], d \times 1 \rangle & \downarrow & \downarrow \\ I^m \times \Sigma_k \times I^k & \xrightarrow{\alpha \times \sigma \times 1} & I^n \times \Sigma_k \times I^k \end{array}$$

47

where \(\sigma \colon \Sigma_k \to \Sigma_k\) is defined by right multiplication. Note these definitions make the map \(\alpha \times \sigma \times 1: I^m \times \Sigma_k \times I^k \to I^n \times \Sigma_k \times I^k\) into a \(\Sigma_k\)-equivariant map.

Definition 4.3.11. Garner's algebraic small object argument [Gar09] yields an algebraic weak factorization system on \(\mathsf{cSet}^{\mathbb{X}}\) which is algebraically free on \(J\colon \int \Omega \times \mathbb{I}\to (\mathsf{cSet}^{\mathbb{X}})^2\), i.e., whose category of monad algebras is given by \((\int \Omega \times \mathbb{I})^{\square}\). In particular, a right map is a morphism \(f\colon \mathbb{Y}\to \mathbb{X}\) of cubical species equipped with chosen lifts against open boxes that are uniform in pullback squares:

![img-53.jpeg](img-53.jpeg)

We call the left and right classes of the underlying weak factorization system the trivial cofibrations and fibrations respectively.

We now show that these fibrations are the unbiased fibrations.

Definition 4.3.12. Given a map \( f \colon \mathbb{Y} \to \mathbb{X} \) define the parametrized path space by forming the Leibniz exponential of \( f \) with \( \delta \) in the slice over \( \mathbb{I} \), as displayed below-left:

![img-54.jpeg](img-54.jpeg)

where \(\mathrm{ev}\colon \mathbb{Y}^{\mathbb{I}}\times \mathbb{I}\to \mathbb{Y}\) is evaluation. Equivalently, the map \(\mathrm{ev}\hat{\circ} f\) may be defined by the pullback above-right, which is not formed in the slice over \(\mathbb{I}\).

From the second of these characterizations, ev  \( \hat{o} f \)  is the Leibniz pullback application of the evaluation natural transformation to the map f, explaining our notation. This functor is not right adjoint, failing to preserve the terminal object. However, from the decomposition

\[
(\mathsf {c S e t} ^ {\mathbb {X}}) ^ {2} \xrightarrow [ f \mapsto \mathrm{ev} \hat {\circ} f ]{- \times \mathbb {I}} (\mathsf {c S e t} _ {/ \mathbb {I}} ^ {\mathbb {X}}) ^ {2} \xrightarrow [ f \mapsto \mathrm{ev} \hat {\circ} f ]{\widehat {\{\delta , - \}}} (\mathsf {c S e t} _ {/ \mathbb {I}} ^ {\mathbb {X}}) ^ {2} \xrightarrow [ f \mapsto \mathrm{ev} \hat {\circ} f ]{\Sigma} (\mathsf {c S e t} ^ {\mathbb {X}}) ^ {2},
\]

it is the composition of a right adjoint with the forgetful functor \(\Sigma\). In particular, it preserves pullbacks.

Theorem 4.3.14. The category of uniform fibrations \((\int \Omega \times \mathbb{I})^{\square}\) is the pullback of the category of uniform trivial fibrations \((\int \Omega)^{\square}\) along the parametrized path space functor:

![img-55.jpeg](img-55.jpeg)

48

In particular, a map \( f \colon \mathbb{Y} \to \mathbb{X} \) of cubical species is a fibration if and only if it is an unbiased fibration, i.e., the parametrized path space map

\[
\mathbb {Y} ^ {\mathrm{I}} \times \mathbb {I} \xrightarrow {\operatorname{ev} \hat {\circ} f} \mathbb {P} ^ {\mathrm{I}} \mathbb {Y}
\]

is a trivial fibration.

Proof. The category of uniform fibrations is defined by right lifting against the category of arrows \( J \colon \int \Omega \times \mathbb{I} \to (\mathsf{cSet}^{\mathbb{I}})^2 \) defined in Construction 4.3.6. In terms of the functor \( I \colon \int \Omega \to (\mathsf{cSet}^{\mathbb{I}})^2 \) of Construction 2.2.13, the functor \( J \) is the top horizontal composite:

\[
\begin{array}{c} \int \Omega \times \mathbb {I} \xrightarrow {\Sigma^ {*} I} (\mathsf {c S e t} _ {/ \mathbb {I}} ^ {\mathbb {I}}) ^ {2} \xrightarrow {- \hat {\times} \delta} (\mathsf {c S e t} _ {/ \mathbb {I}} ^ {\mathbb {I}}) ^ {2} \xrightarrow {\Sigma} (\mathsf {c S e t} ^ {\mathbb {I}}) ^ {2} \\ \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \int \Omega \xrightarrow [ I ]{} (\mathsf {c S e t} ^ {\mathbb {I}}) ^ {2} \end{array}
\]

Thus, by adjunction, \( f \in (\mathsf{cSet}^{\mathbb{I}})^2 \) is a uniform fibration if and only if \( \{\widehat{\delta, f \times \mathbb{I}}\}_{\mathbb{I}} \in (\mathsf{cSet}_{/ \mathbb{I}}^{\mathbb{I}})^2 \) lifts on the right against the category \( \Sigma^{*}I \colon \int \Omega \times \mathbb{I} \to (\mathsf{cSet}_{/ \mathbb{I}}^{\mathbb{I}})^2 \). As solutions to lifting problems in slice categories are created by the forgetful functor, this is the case if and only if \( \operatorname{ev} \hat{\circ} f \cong \Sigma \{\widehat{\delta, f \times \mathbb{I}}\}_{\mathbb{I}} \in (\mathsf{cSet}^{\mathbb{I}})^2 \) is a uniform trivial fibration as claimed.

The left maps of an algebraic weak factorization system satisfy additional closure properties, arising from the fact that comonadic functors create colimits [BG16]. In particular, colimits in the arrow category, of diagrams that factor through the generating category, are trivial cofibrations. The following lemma provides an example of this paradigm.

Lemma 4.3.15. For any of the \(2^{\omega}\) points \(\vec{\epsilon}\) of \(\mathbb{I}\), the map \(\vec{\epsilon} \colon \mathbb{1} \to \mathbb{I}\), is a trivial cofibration.

Proof. For any vertex \(\vec{v} \in I^k\) we have a triangle

\[
\begin{array}{c c c c c} \emptyset \xrightarrow {\quad ! \quad} 1 & \\ I ^ {k} & \sim & \mathbb {F} _ {k} 1 & \\ & \Biggl \downarrow [ \vec {v} ] & \leftrightarrow & \Biggl \downarrow_ {\mathbb {P} ^ {\Sigma_ {k}}} \\ & & \mathbb {F} _ {k} 1 \times \mathbb {I} & \\ & & & \Sigma_ {k} \times I ^ {k} \end{array} \tag {4.3.16}
\]

The map of \(\Sigma_{k}\)-cubical sets on the right sends \(\sigma \in \Sigma_{k}\) to the pair \((\sigma, \sigma \cdot \vec{v})\). However, recall from Remark 4.2.6 that a point of \(\mathbb{I}\) is specified by choosing either point \(\vec{0} \colon 1 \to I^{k}\) or \(\vec{1} \colon 1 \to I^{k}\) for each component. Note these are the only two points in the \(\Sigma_{k}\)-cubical set \(I^{k}\), since the other points in the underlying cubical set are permuted by the regular action. By contrast, since these points are fixed we have automorphisms

\[
\begin{array}{c c c} \emptyset & \text {   =   } & \emptyset \\ ! \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} \\ 1 & \text {   =   } & 1 \\ \vec {0} \Big \downarrow & \Big \downarrow^ {\vec {0}} & \\ I ^ {k} & \xleftarrow {\sigma} & I ^ {k} \end{array} \qquad \qquad \begin{array}{c c c} \emptyset & \text {   =   } & \emptyset \\ ! \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} & \Big \downarrow^ {\text {   }} \\ 1 & \text {   =   } & 1 \\ \vec {1} \Big \downarrow & \Big \downarrow^ {\vec {1}} & \\ I ^ {k} & \xleftarrow {\sigma} & I ^ {k} \end{array}
\]

for each \(\sigma \in \Sigma_k\). Thus \(\Sigma_k^{\mathrm{op}}\) acts on the open boxes \([\vec{0}] \colon \mathbb{F}_k 1 \mapsto \mathbb{F}_k 1 \times \mathbb{I}\) and \([\vec{1}] \colon \mathbb{F}_k 1 \mapsto \mathbb{F}_k 1 \times \mathbb{I}\) and these automorphisms lie in the generating category. The colimits yield the maps \(\vec{0} \colon 1 \to I^k\) and \(\vec{1} \colon 1 \to I^k\) in \(\Sigma_k\)-cubical sets, where the codomains have the regular action. Thus, these maps are

49

trivial cofibrations. Picking the appropriate trivial cofibration in each component and forming their coproduct in cubical species yields the point inclusion $\vec{v}: 1 \rightarrow \mathbb{I}$ in $\mathsf{cSet}^{\mathbb{Z}}$.

We have defined (cofibration, trivial fibration) and (trivial cofibration, fibration) algebraic weak factorization systems, each with an explicit category of generators. The trivial fibrations lift naturally against the generating category for the (trivial cofibration, fibration) awfs by Proposition 2.2.11, so trivial fibrations are fibrations and trivial cofibrations are cofibrations. The underlying weak factorization systems thus equip the category of cubical species with a premodel structure to be called the **interval premodel structure**. As in §3.1, we define the **weak equivalences** of cubical species to be those maps that factor as trivial cofibrations followed by trivial fibrations.

*Remark 4.3.17.* We would have a similar result if we had included the identity automorphism of the 0-cube in our definition of $\mathbb{Z}$, adding a $k = 0$ component to our cubical species. Had we done so, then note that in the $k = 0$ component, all maps would be fibrations, since the components of the exterior squares of (4.3.13) are both pullbacks. Consequently, in the $k = 0$ component, the only trivial cofibrations would be the isomorphisms, which means that the class of weak equivalences would coincide with the class of trivial fibrations, defined as in the other components to be those maps that lift against monomorphisms. But this class evidently fails to satisfy the 2-of-3 property, failing to be closed under left cancellation, so had we included a $k = 0$ component our premodel structure would have no chance of defining a model structure. However, the premodel structure would still suffice to define the model structure on equivariant cubical sets in Section 5.1.

We next verify that the interval premodel structure is cartesian monoidal. We expect that this property can be made structural: that the cartesian closed structure on the category of cubical species defines two variable adjunctions of algebraic weak factorization systems [Rie13], but as we have no application for that result, we decline to pursue it here.

**Proposition 4.3.18.** *Pushout products of cofibrations are cofibrations, while the pushout product of a cofibration and a trivial cofibration is a trivial cofibration.*

*Proof.* As the cofibrations are the monomorphisms in a presheaf category, the first property holds by Remark 2.2.2.

The remaining statement is equivalent to the assertion that the Leibniz exponential $\{c, f\}$ of a fibration $f: \mathbb{Y} \rightarrow \mathbb{X}$ and a monomorphism $c: \mathbb{C} \rightarrow \mathbb{Z}$ is a fibration. By Theorem 4.3.14, this is equivalent to the assertion that the Leibniz exponential in the slice over $\mathbb{I}$ of $\delta: \mathbb{I} \rightarrow \mathbb{I} \times \mathbb{I}$ and $\{c, f\} \times \mathbb{I}$ is a trivial fibration, lifting against all monomorphisms $u: \mathbb{J} \rightarrow \mathbb{K}$ in the slice over $\mathbb{I}$. Since the pullback of $\{c, f\}$ to the slice over $\mathbb{I}$ is isomorphic to the Leibniz exponential in the slice over $\mathbb{I}$ of the pullbacks $c \times \mathbb{I}$ and $f \times \mathbb{I}$, we are equivalently looking to solve lifting problems in the slice over $\mathbb{I}$ between the Leibniz product of $c \times \mathbb{I}$ and $u$ in the slice over $\mathbb{I}$ and the Leibniz exponential

$$\operatorname{ev} \hat{\circ} f := \{\widehat{\delta, f \times \mathbb{I}}\}_{\mathbb{I}}.$$

As we are working under the hypothesis that $f$ is a fibration, $\operatorname{ev} \hat{\circ} f$ is a trivial fibration so it suffices to verify that the pushout product of the monomorphisms $c \times \mathbb{I}$ and $u$ over $\mathbb{I}$ is a monomorphism. This again holds by Remark 2.2.2.

Finally, we observe that the interval premodel structure is cylindrical, satisfying the axioms of Definition 3.1.8, using the adjunction $(-) \times \mathbb{I} \dashv (-)^{\mathbb{I}}$ to define an adjoint functorial cylinder.

**Lemma 4.3.19.** *The interval premodel structure on cubical species is cylindrical.*

*Proof.* Since the endpoints $\vec{0}$ and $\vec{1}$ of the interval $\mathbb{I}$ are disjoint, the copairing $[\delta_0, \delta_1]: \mathbb{I} \to \mathbb{I} \mapsto \mathbb{I}$ is a monomorphism and thus a cofibration. By Lemma 4.3.15, the single endpoint inclusions $\delta_0, \delta_1: \mathbb{I} \not\to \mathbb{I}$ are trivial cofibrations. Now the result follows from Proposition 4.3.18.

50

4.4. The cubical species model of homotopy type theory. In this section, we apply the results of §3 to verify the type-theoretic properties of the interval premodel structure on cubical species that allow us to show it is a Quillen model structure with the extra features required of a model of homotopy type theory.

The cofibrations in the interval premodel structure are exactly the monomorphisms, which are closed under pushout products in all slices by Remark 2.2.2. Together with Lemma 4.3.19, this verifies the hypotheses of Theorem 3.3.3, and therefore:

Proposition 4.4.1. The interval premodel structure on cubical species satisfies the equivalence extension property. \(\square\)

Similarly, the definition of the fibrations is of the form considered by Proposition 3.4.2, and therefore:

Proposition 4.4.2. The interval premodel structure on cubical species has the Frobenius property. \(\square\)

The remaining properties require universes, which we now construct. By Theorem 4.3.14, the uniform fibrations are determined as a certain pullback of the trivial fibrations. We use this result to define a notion of fibred structure \(\mathbb{F}\) that is locally representable and relatively acyclic and classifies the uniform fibrations.

Lemma 4.4.3. There is a locally representable and relatively acyclic notion of fibred structure \(\mathbb{F}\), the notion of uniform fibration structure, whose underlying class of maps is the class of fibrations.

Proof. We apply Lemma 2.1.16. That is, we define a uniform fibration structure on \( f \colon \mathbb{Y} \to \mathbb{X} \) to be a uniform trivial fibration structure on \( \operatorname{ev} \hat{\circ} f \), the Leibniz pullback application of the evaluation natural transformation

\[
\mathrm{cSet} ^ {\mathbb {E}} \xrightarrow [ \Downarrow \mathrm{ev} ]{(-) ^ {\mathbb {I}} \times \mathbb {I}} \mathrm{cSet} ^ {\mathbb {E}}.
\]

Since the interval \(\mathbb{I}\) is tiny, the functor \(\mathbb{X} \mapsto \mathbb{X}^{\mathbb{I}} \times \mathbb{I}\) has a right adjoint:

\[
\mathrm{cSet} ^ {\mathbb {E}} \xrightarrow [ (-) _ {\mathbb {I}} ]{(-) ^ {\mathbb {I}}} \mathrm{cSet} ^ {\mathbb {E}} \xrightarrow [ (-) ^ {\mathbb {I}} ]{- \times \mathbb {I}} \mathrm{cSet} ^ {\mathbb {E}}.
\]

Since Lemma 2.2.10 tells us that the notion of fibred structure \(\mathbb{T}\mathbb{F}\) is locally representable and relatively acyclic, Lemma 2.1.16 tells us that the same is true for the uniform fibrations.

Instantiating Construction 2.3.3:

Construction 4.4.4. For sufficiently large \(\kappa\), we define a \(\kappa\)-small fibration classifier \(\pi: \dot{\mathbb{U}}_{\kappa} \to \mathbb{U}_{\kappa}\) by defining \(\mathbb{U}_{\kappa} := \mathbb{F}^{\kappa}(\varpi)\) and forming the pullback

\[
\begin{array}{c} \dot {\mathbb {U}} _ {\kappa} \longrightarrow \dot {\mathbb {V}} _ {\kappa} \\ \pi \Big \downarrow^ {\lrcorner} \quad \Big \downarrow^ {\lrcorner} \\ \mathbb {U} _ {\kappa} \xrightarrow [ \psi_ {\varpi} ]{} \mathbb {V} _ {\kappa} \end{array}
\]

where \(\varpi\colon\dot{\mathbb{V}}_{\kappa}\to\mathbb{V}_{\kappa}\) is the Hofmann–Streicher universe classifying \(\kappa\)-small families in the presheaf topos cSet\(^{\mathbb{E}}\).

By Proposition 2.3.5:

51

**Proposition 4.4.5.** *The interval premodel structure on cubical species has universes in the sense of Definition 2.3.6 for the fibrations given by the classifiers $\pi: \mathbb{U}_\kappa \to \mathbb{U}_\kappa$ for sufficiently large inaccessible cardinals $\kappa$.* □

With Propositions 4.4.5 and 4.4.2, we have satisfied the hypotheses of Proposition 3.5.5, so from Proposition 4.4.1 we may conclude:

**Proposition 4.4.6.** *The universes in the interval premodel structure on cubical species are univalent.* □

By Definition 4.3.12 and Theorem 4.3.14, our fibrations are characterized in the way demanded by Proposition 3.6.9. Thus Proposition 3.6.10 applies and we may conclude:

**Proposition 4.4.7.** *The bases of the universal fibrations for the interval premodel structure on cubical species are fibrant objects.* □

By applying Lemma 3.7.2, we see that:

**Proposition 4.4.8.** *The interval premodel structure satisfies the fibration extension property.* □

These results assemble into the main theorem of this section.

**Theorem 4.4.9.** *The category of cubical species admits a Quillen model structure in which the cofibrations are the monomorphisms and the fibrations are the unbiased fibrations of 3.6.7(ii). This model is cylindrical and cartesian closed and satisfies the Frobenius condition, equivalence extension property, and fibration extension property. Moreover, it has univalent universes whose bases are fibrant objects.*

*Proof.* The only result of the statement that we have not yet proven is the fact that the interval premodel structure is in fact a model structure, but this follows formally from Proposition 3.7.3, by Proposition 4.4.8 and the fact that all objects are cofibrant. □

Thus, the interval model structure on the topos of cubical species is a model of homotopy type theory.

## 5. THE EQUIVARIANT MODEL STRUCTURE ON CUBICAL SETS

Having established a model structure on the category of cubical species, we now transfer it to a model structure, and a model of homotopy type theory, on the category cSet of cartesian cubical sets. The results of §4 both provide conceptual justification for the constructions in this section and also simplify many of the proofs.

In §5.1, we introduce an adjoint triple of functors between cubical sets and cubical species and establish the basic properties of these functors. In §5.2, we lift the cylindrical premodel structure from cubical species to cubical sets by using the constant diagram functor $\Delta: \text{cSet} \to \text{cSet}^\times$ to create the fibrations and trivial fibrations. We give explicit characterizations of these classes that reveal that the trivial fibrations are again the trivial fibrations of §2.2, while the fibrations are novel, defining a class of maps we call *equivariant fibrations*.

As the cofibrations in the resulting premodel structure on cubical sets are again the monomorphisms, these are created by the functor $\Delta$ as well, but the trivial cofibrations and weak equivalences are not, so in particular it will again take work to prove that the right-lifted premodel structure in fact defines a Quillen model structure. This is achieved in §5.3, which proves the analogue of Theorem 4.4.9 for cubical sets. For some of the constituent results, the proofs are formal, specializing the results of §3; for other statements, the results of that section do not apply and we leverage the results of §4 instead.

52

5.1. From cubical species to equivariant cubical sets. The category of cubical sets embeds faithfully into the category of cubical species via the constant diagram functor

$$\Delta \colon \mathsf{cSet} \to \mathsf{cSet}^{\Sigma} \cong \prod_{k \geq 1} \mathsf{cSet}^{\Sigma_k},$$

which is fully faithful on each factor $\mathsf{cSet}^{\Sigma_k}$ though only faithful on the whole. Since the groupoid $\Sigma$ is small and $\mathsf{cSet}$ is bicomplete, this functor admits left and right adjoints:

![img-56.jpeg](img-56.jpeg)

The left adjoint L takes the colimit over the groupoid $\Sigma$, and the right adjoint $\Gamma$ takes the limit. Explicitly, for a cubical species $\mathbb{X} = (X^k)_{k \geq 1}$, we have

$$\mathrm{L}(\mathbb{X}) := \prod_{k \geq 1} X^k_{/\Sigma_k}$$

$$\Gamma(\mathbb{X}) := \prod_{k \geq 1} (X^k)^{\Sigma_k}$$

where $X^k_{/\Sigma_k}$ is the cubical set of **orbits**, the quotient of the $\Sigma_k$-cubical set $X^k$ by its action, and $(X^k)^{\Sigma_k}$ is the cubical set of $\Sigma_k$-**fixed points**.

As a category of actions by a groupoid, the topos $\mathsf{cSet}^{\Sigma}$ is well-known to be atomic over $\mathsf{cSet}$, and $\Delta \colon \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$ to be a logical functor, preserving (co)limits, the subobject classifier and the locally cartesian closed structure. We provide some explicit calculations of these.

**Example 5.1.1.** For $n, k \in \mathbb{N}$ and $k \geq 1$, we have $\mathrm{L}(\mathbb{F}_k I^n) \cong I^n$, reflecting the fact that left Kan extensions preserve representables. More generally, for any cubical set $X$, we have $\mathrm{L}(\mathbb{F}_k X) \cong X$, as $\mathrm{L} \cdot \mathbb{F}_k$ is left adjoint to the identity functor.

**Example 5.1.2.** We calculate

$$\mathrm{L}(\mathbb{I}) \cong \prod_{k \geq 1} I^k_{/\Sigma_k} \quad \text{and} \quad \Gamma(\mathbb{I}) \cong \prod_{k \geq 1} I \cong I^\omega$$

using the fact that $(I^k)^{\Sigma_k} \cong I$ for all $k > 0$.

The left adjoint L is far from being left exact, failing to preserve pullbacks (since 1-categorical quotients by a group action do not commute with pullbacks) and even finite products (since coproducts do not commute with finite products); in particular, $\mathrm{L}(\mathbb{1}) \cong \mathbb{N}$. It does, however, interact well with certain finite limits involving constant cubical species.

**Corollary 5.1.3.** *The constant diagram functor $\Delta \colon \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$ preserves pushforwards and exponentials.*

*Proof.* This is an instance of Corollary 4.1.4.

**Lemma 5.1.4.** *The constant diagram functor $\Delta \colon \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$ preserves the subobject classifier and creates monomorphisms.*

*Proof.* Preservation of the subobject classifier is an instance of Corollary 4.1.6. For creation of monomorphisms, recall that monomorphisms in $\mathsf{cSet}^{\Sigma}$ are defined pointwise and that $\Sigma$ is inhabited.

53

Corollary 5.1.5. The constant diagram functor \(\Delta\colon\mathsf{cSet}\to\mathsf{cSet}^{\Sigma}\) preserves the (relative) partial map classifiers \(\eta_{X}\colon X\to X^{+}\) of Section 2.2, and therefore also the (relative) +-algebras. Since it is faithful, \(\Delta\) also reflects the latter.

5.2. The cylindrical premodel structure on cubical sets. By a well-known transfer procedure, we may obtain a premodel structure on cubical sets from the premodel structure on cubical species by pulling back the right classes of the weak factorization systems along the right adjoint  \( \Delta: cSet \rightarrow cSet^{\Sigma} \) : we say f is a (trivial) fibration in cSet if  \( \Delta f \)  is a (trivial) fibration in  \( cSet^{\Sigma} \) . The transfer procedure gives us the left and right classes as well as generating categories, namely the images of the generating categories of the original weak factorization systems under the left adjoint  \( L: cSet^{\Sigma} \rightarrow cSet \) . Note, however, that we do not mechanically obtain the factorizations in cSet from those in  \( cSet^{\Sigma} \) ; we must construct these “by hand”, and we want in particular to do so constructively.

Construction 5.2.1. The trivial fibrations in cSet are generated by the category \(\int \Omega\) of Construction 2.2.13 and the top composite functor

\[
\begin{array}{c} \int \Omega \xrightarrow {I} (\mathrm{cSet} ^ {\Sigma}) ^ {2} \xrightarrow {\mathrm{L}} \mathrm{cSet} ^ {2} \\ \pi \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text {cod} \\ \square \times \Sigma^ {\mathrm{op}} \xrightarrow {\mathbb {1}} \mathrm{cSet} ^ {\Sigma} \xrightarrow {\mathrm{L}} \mathrm{cSet}. \end{array} \tag {5.2.2}
\]

Explicitly, by Example 5.1.1, the composite functor \( \mathsf{LI} \colon \int \Omega \to \mathsf{cSet}^2 \) sends an element \( \chi_c \colon \mathbb{F}_k I^n \to \Omega \) to the corresponding subobject \( c \colon C \mapsto I^n \) under Lemma 4.3.1, while morphisms in \( \int \Omega \) as below-left are carried to pullback squares between subobjects as below-right:

\[
\begin{array}{c c c} \mathbb {F} _ {k} I ^ {m} \xrightarrow {\alpha \times \sigma} \mathbb {F} _ {k} I ^ {n} & & D \xrightarrow {\alpha} C \\ \searrow_ {\chi_ {d}} \searrow_ {\Omega} \swarrow_ {\chi_ {c}} & \sim & d \Biggl \downarrow^ {\lrcorner} \Biggl \downarrow^ {\lrcorner} \Biggl \downarrow^ {c} \\ & & I ^ {m} \xrightarrow {\alpha} I ^ {n}. \end{array}
\]

Note the image of the functor  \( LI: \int \Omega \to cSet^{2} \)  on both objects and morphisms is independent of the parameter  \( k \in \Sigma \) . The isomorphism of Lemma 5.1.4 induces an isomorphism of categories  \( \int \Omega \cong (\int \Omega) \times \Sigma^{\mathrm{op}} \)  and, by the observations just made, the functor  \( LI \)  factors through the projection  \( \pi: \int \Omega \to \int \Omega \) . Thus, the composite rectangle of (5.2.2) also factors as follows:

\[
\begin{array}{c} \int \Omega \xrightarrow {\pi} \int \Omega \xrightarrow {I} \to \mathsf {c S e t} ^ {2} \\ \pi \Big \downarrow \qquad \qquad \qquad \pi \Big \downarrow \qquad \qquad \qquad \Big \downarrow^ {\mathrm{cod}} \\ \Box \times \Sigma^ {\mathrm{op}} \xrightarrow {\pi} \Box \xrightarrow [ ]{\quad} \mathsf {c S e t}. \end{array}
\]

Since the projection \(\pi\colon\int\Omega\to\int\Omega\) is an epimorphism, a generating category for the trivial fibrations on cSet can be given more simply as the category \(I\colon\int\Omega\to\mathsf{cSet}^{2}\) internally indexed by the subobject classifier \(\top\colon1\mapsto\Omega\) in cSet.

It now follows from Remark 2.2.6 and Proposition 2.2.14 that the cofibrations are precisely the monomorphisms and the trivial fibrations are the relative +-algebras, i.e. the algebras for the pointed polynomial endofunctors \( +_{X} \colon \mathsf{cSet}_{/X} \to \mathsf{cSet}_{/X} \), as can also be seen from Corollary 5.1.5. In particular, we have a (cofibration, trivial fibration) weak factorization system with functorial factorization given by the partial map factorization of Remark 2.2.6.

We next transfer the (trivial cofibration, fibration) weak factorization system. This case is more delicate, however, because the left class of trivial cofibrations is not simply reflected by the constant

54

diagram functor $\Delta \colon \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$. In order to characterize the maps in the image of the generating category, we pause to observe a result that will help us calculate orbits.

**Lemma 5.2.3.** *Let $G$ be a group and let $S$ be a $G$-set. Consider the $G$-set $G \times S$ where $G$ acts freely on $G$ and via its specified action on $S$. Then the map*

$$\begin{array}{l} G \times S \xrightarrow{\tau} S \\ (g, s) \longmapsto g^{-1} \cdot s \end{array}$$

*exhibits the set $S$ as the set of $G$-orbits in $G \times S$.*

*Proof.* First observe that the map in the statement defines a cone under the $G$-indexed diagram of sets defined by the $G$-set $G \times S$. For any $g, h \in G$ and $s \in S$, the action of $h$ sends the pair $(g, s)$ to $(h \cdot g, h \cdot s)$, and $\tau(h \cdot g, h \cdot s) = (h \cdot g)^{-1} \cdot (h \cdot s) = g^{-1} \cdot s = \tau(g, s)$. Given any other map $\phi \colon G \times S \to X$ to a set $X$ that is constant on $G$-orbits in the domain, we define a factorization through $\tau$ by:

$$\begin{array}{l} G \times S \xrightarrow{\tau} S \xrightarrow{\psi} X \\ (g, s) \longmapsto g^{-1} \cdot s \\ s \longmapsto \phi(e, s). \end{array}$$

Since $(g, s)$ and $(e, g^{-1} \cdot s)$ are in the same orbit, $\phi(g, s) = \phi(e, g^{-1} \cdot s) = \psi \cdot \tau(g, s)$. Uniqueness of this factorization is immediate since $\tau$ is an epimorphism. $\square$

**Construction 5.2.4.** The fibrations in $\mathsf{cSet}$, which we call **equivariant fibrations**, are generated by the image of the category $\int \Omega \times \mathbb{I}$ under the composition:

$$\begin{array}{c} \int \Omega \times \mathbb{I} \xrightarrow{J} (\mathsf{cSet}^{\Sigma})^2 \xrightarrow{\mathrm{L}} \mathsf{cSet}^2 \\ \pi \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \square \times \Sigma^{\mathrm{op}} \xrightarrow{\mathrm{L}} \mathsf{cSet}^{\Sigma} \xrightarrow{\mathrm{L}} \mathsf{cSet}. \end{array}$$

Recall, from Remark 4.3.4, that objects of $\int \Omega \times \mathbb{I}$ are pairs $(c, \zeta)$ as displayed vertically below while $(\alpha, \sigma) \colon (d, \xi) \to (c, \zeta)$ defines a morphism just when the diagrams of cubical sets commute and the top square is a pullback:

$$\begin{array}{c} D \xrightarrow{\alpha} C \\ d \downarrow \quad \downarrow \quad \downarrow^c \\ I^m \xrightarrow{\alpha} I^n \\ \xi \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ I^k \xleftarrow[\sigma]{} I^k. \end{array}$$

The functor $J$ sends an element $(c, \zeta)$ to the morphism of cubical species defined by pushout of cubical species below-left, which corresponds to the pushout of $\Sigma_k$-cubical sets below-right:

![img-57.jpeg](img-57.jpeg)

![img-58.jpeg](img-58.jpeg)

The image of the left-hand diagram under L is given by passing to orbits in the diagram of $\Sigma_k$-cubical sets above-right, and this can be calculated using Lemma 5.2.3. This results in the pushout diagram of cubical sets

![img-59.jpeg](img-59.jpeg)

We again refer to the subobjects in the image of the functor $J$ as **open boxes** though the nature of the gluing of the “lid” $I^n$ onto the “box” $C \times I^k$ is somewhat subtle because it involves the map $\zeta: I^n \to I^k$.

The functor $J$ sends morphisms (4.3.5) to the pullback square of cubical species below-left, which corresponds to the pullback square of $\Sigma_k$-cubical sets below-right:

$$\begin{array}{c c c} \mathbb{F}_k I^m \underset{\mathbb{F}_k D}{\cup} \mathbb{F}_k D \times \mathbb{I} \xrightarrow{\alpha \times \sigma \times 1} \mathbb{F}_k I^n \underset{\mathbb{F}_k C}{\cup} \mathbb{F}_k C \times \mathbb{I} & I^m \times \Sigma_k \underset{D \times \Sigma_k}{\cup} D \times \Sigma_k \times I^k \xrightarrow{\alpha \times \sigma \times 1} I^n \times \Sigma_k \underset{C \times \Sigma_k}{\cup} C \times \Sigma_k \times I^k \\ \langle [\xi], \mathbb{F}_k d \times 1 \rangle \Bigg\downarrow & \Bigg\downarrow \quad \Bigg\downarrow \langle [\zeta], \mathbb{F}_k c \times 1 \rangle & \langle [\xi^{\Sigma_k}], d \times 1 \rangle \Bigg\downarrow \\ \mathbb{F}_k I^m \times \mathbb{I} \xrightarrow{\alpha \times \sigma \times 1} \mathbb{F}_k I^n \times \mathbb{I} & I^m \times \Sigma_k \times I^k \xrightarrow{\alpha \times \sigma \times 1} I^n \times \Sigma_k \times I^k. \end{array}$$

Passing to orbits using Lemma 5.2.3 this becomes

$$\begin{array}{c c c} I^m \cup_D D \times I^k & \xrightarrow{\alpha \times \sigma^{-1}} & I^n \cup_C C \times I^k \\ \langle [\xi], d \times 1 \rangle \Bigg\downarrow & \Bigg\downarrow & \Bigg\downarrow \langle [\zeta], c \times 1 \rangle \\ I^m \times I^k & \xrightarrow{\alpha \times \sigma^{-1}} & I^n \times I^k. \end{array}$$

56

Thus, an equivariant fibration is a morphism \( f \colon Y \to X \) of cubical sets equipped with chosen lifts against open boxes that are uniform in pullback squares:

![img-60.jpeg](img-60.jpeg)

By Garner's algebraic small object argument, the functor  \( LJ: \int \Omega \times \mathbb{I} \to cSet^{2} \)  generates a (trivial cofibration, equivariant fibration) algebraic weak factorization system. Thus we have a functorial factorization for both weakly orthogonal classes, completing the definition of a premodel structure which we call the equivariant premodel structure. By construction:

Lemma 5.2.5. The adjunction

![img-61.jpeg](img-61.jpeg)

defines a Quillen adjunction of premodel structures between the equivariant premodel structure on cSet and the interval model structure on cSet \( ^{\Sigma} \) .

An argument similar to the proof of Lemma 4.3.15 can be used to identify explicit trivial cofibrations.

Lemma 5.2.6. For any \( k \geq 1 \) and subgroup \( G \subset \Sigma_k \) the inclusions \( \vec{0}, \vec{1} \colon 1 \to I_{/G}^k \) of the initial or final vertices into the quotient cubical set define trivial cofibrations.

Proof. By Construction 5.2.4, the triangle below-left gives rise to the generating trivial cofibration below-right:

![img-62.jpeg](img-62.jpeg)

When \(\vec{v}\) is the point \(\vec{0}\) or \(\vec{1}\), then any \(\sigma \in \Sigma_k\) defines a morphism of triangles, as below-left, giving rise to the morphism in the generating category of trivial cofibrations displayed below-right:

![img-63.jpeg](img-63.jpeg)

Thus, the maps \(\vec{0},\vec{1}\colon 1\to I_{/G}^{k}\) arise as colimits of diagrams valued in the subcategory of generating trivial cofibrations. Since the equivariant fibrations lift uniformly against the generating category, they lift against colimits of diagrams valued in there, proving that the inclusions \(\vec{0},\vec{1}\colon 1\to I_{/G}^{k}\) are trivial cofibrations.

In particular:

57

**Corollary 5.2.7.** *For any $k \geq 1$, the inclusions $\vec{0}, \vec{1}: 1 \to I^k$ of the initial or final vertices into the $k$-cube each define trivial cofibrations.* $\square$

We now verify that the equivariant premodel structure is cartesian monoidal.

**Proposition 5.2.8.** *Pushout products of cofibrations are cofibrations, while the pushout product of a cofibration and a trivial cofibration is a trivial cofibration.*

*Proof.* As the cofibrations are the monomorphisms in a topos, the first property is again immediate. The second statement is equivalent to the assertion that the Leibniz exponential $\widehat{\{c, f\}}$ of a uniform fibration $f: Y \to X$ and a monomorphism $c: C \mapsto Z$ is a uniform fibration. But uniform fibrations and monomorphisms are created by the functor $\Delta: \mathsf{cSet} \to \mathsf{cSet}^{\mathbb{Z}}$ from the corresponding classes of cubical species, by definition and Lemma 5.1.4, respectively, and in virtue of Corollary 5.1.3 the functor $\Delta$ also preserves Leibniz exponentials. So the result follows from Proposition 4.3.18. $\square$

We now observe that our premodel structure is cylindrical. Although the equivariant fibrations are not defined using a particular interval object, we will show that the naive interval object

$$1 \xrightarrow[1]{0} I \xrightarrow{!} 1$$

satisfies the axioms of Definition 3.1.8, using the adjunction $(-) \times I \dashv (-)^I$ to define our adjoint functorial cylinder.

**Lemma 5.2.9.** *The equivariant premodel structure on cubical sets is cylindrical.*

*Proof.* Since the endpoints 0 and 1 of our interval $I$ are disjoint, the map $\partial: 1 + 1 \mapsto I$ is a monomorphism and thus a cofibration. By Corollary 5.2.7, the single endpoint inclusions $\partial_0, \partial_1: 1 \xrightarrow{\sim} I$ are trivial cofibrations. Now the result follows from Proposition 5.2.8. $\square$

**5.3. The equivariant cubical sets model of homotopy type theory.** In this section, we establish the type-theoretic properties of the cylindrical premodel structure on cubical sets needed to infer that it defines a Quillen model structure with the extra features required of a model of homotopy type theory.

The cofibrations in the equivariant premodel structure are exactly the monomorphisms, which are closed under pushout products in all slices by Remark 2.2.2. Together with Lemma 5.2.9, this verifies the hypotheses of Theorem 3.3.3, and therefore:

**Proposition 5.3.1.** *The equivariant premodel structure on cubical sets satisfies the equivalence extension property.* $\square$

Unlike in the case of the interval premodel structure on cubical species, we cannot use the results of §3.4 to establish the Frobenius condition, as the equivariant fibrations are not the naive unbiased fibrations. Instead, it follows for the equivariant premodel structure on cubical sets by comparison with cubical species.

**Proposition 5.3.2.** *The equivariant fibrations satisfy the Frobenius condition.*

*Proof.* We must show that the pushforward of an equivariant fibration $g$ along an equivariant fibration $f$ defines an equivariant fibration, which is the case just when its image under the constant diagram functor is a fibration of cubical species. But since Corollary 5.1.3 tells us that this functor preserves pushforwards, this map is the pushforward of $\Delta g$ along $\Delta f$. Since the equivariant fibrations are pulled back along $\Delta$ from the fibrations, the result follows from Frobenius for the latter, Proposition 4.4.2. $\square$

58

The remaining properties require universes, which we now construct. Since the equivariant fibrations are created from the fibrations in $\mathsf{cSet}^{\mathbb{E}}$ via the functor $\Delta \colon \mathsf{cSet} \to \mathsf{cSet}^{\mathbb{E}}$, and since $\Delta$ preserves pullbacks and has a right adjoint, Example 2.1.17 applies to tell us that that the equivariant fibrations underlie a locally representable and relatively acyclic notion of fibred structure.

**Lemma 5.3.3.** *There is a locally representable and relatively acyclic notion of fibred structure $\mathcal{F}$ on cubical sets whose underlying class of maps is the class of equivariant fibrations.*

*Proof.* By Example 2.1.17 and Lemma 4.4.3, there is a locally representable and relatively acyclic notion of fibred structure $\mathcal{F}$ where an $\mathcal{F}$-algebra structure on a map $f \colon Y \to X$ of cubical sets is defined to be an $\mathbb{F}$-algebra structure on the map $\Delta f \colon \Delta Y \to \Delta X$ of cubical species. Then, by the proof of Lemma 2.1.16, the map $\psi_f \colon \mathcal{F}(f) \to X$ defined by the pullback

$$\begin{array}{c} \mathcal{F}(f) \longrightarrow \Gamma \mathbb{F}(\Delta f) \\ \Biggl\downarrow \Biggl\downarrow \psi_f \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Gamma \psi_{\Delta f} \\ X \xrightarrow{\quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

has the property that for any $g \colon Z \to X$, there is a natural bijection between equivariant fibration structures on $g^* f$ and lifts of $g$ across $\psi_f$. $\square$

The same line of reasoning tells us how to construct the universal equivariant fibration. By [Awo24, 8], the Hofmann–Streicher universe $\varpi \colon \dot{V}_\kappa \to V_\kappa$ for $\mathsf{cSet}$ and the Hofmann–Streicher universe $\varpi \colon \dot{\mathbb{V}}_\kappa \to \mathbb{V}_\kappa$ for $\mathsf{cSet}^{\mathbb{E}}$, defined with respect to the same regular cardinal $\kappa$, are related by a canonical pullback:

$$\begin{array}{c} \Delta \dot{V}_\kappa \longrightarrow \dot{\mathbb{V}}_\kappa \\ \Delta \varpi \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta V_\kappa \longrightarrow \mathbb{V}_\kappa. \end{array} \tag{5.3.4}$$

**Construction 5.3.5.** Define $\pi \colon \dot{U}_\kappa \to U_\kappa$ to be the map of cubical sets defined by the pullbacks in the top and bottom faces of the cube, whose back face is the transpose of (5.3.4) and whose right face is the image of the pullback square of Construction 4.4.4 under $\Gamma \colon \mathsf{cSet}^{\mathbb{E}} \to \mathsf{cSet}$:

$$\begin{array}{c} \dot{V}_\kappa \longrightarrow \Gamma \dot{\mathbb{V}}_\kappa \\ \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \dot{U}_\kappa \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

By pullback composition and cancelation, this makes the left face a pullback.

*Remark 5.3.6.* By Construction 2.3.3, we might have instead defined $U_\kappa \to V_\kappa$ to be the map $\mathcal{F}^\kappa(\varpi) \to V_\kappa$ classifying equivariant fibration structures associated to the Hofmann–Streicher universe $\varpi \colon \dot{V}_\kappa \to V_\kappa$. However, on account of the pullback square (5.3.4) we have a pullback

$$\begin{array}{c} \mathbb{F}^\kappa(\Delta \varpi) \longrightarrow \mathbb{F}^\kappa(\varpi) =: \mathbb{U}_\kappa \\ \psi_{\Delta \varpi} \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

59

of cubical species and thus a composable pair of pullbacks of cubical sets

$$\begin{array}{c} U _ {\kappa} \cong \mathcal {F} ^ {\kappa} (\varpi) \longrightarrow \Gamma \mathbb {F} ^ {\kappa} (\Delta \varpi) \longrightarrow \Gamma \mathbb {F} ^ {\kappa} (\varpi) =: \Gamma \mathbb {U} _ {\kappa} \\ \psi_ {\varpi} \Biggl \downarrow \quad \text {   } \quad \Gamma \psi_ {\Delta \varpi} \Biggl \downarrow \quad \text {   } \quad \Gamma \psi_ {\varpi} \\ V _ {\kappa} \xrightarrow [ \eta ]{} \Gamma \Delta V _ {\kappa} \xrightarrow {} \Gamma \mathbb {V} _ {\kappa} \end{array}$$

showing that both definitions agree (cf. [Awo24, 12]).

By Remark 5.3.6 and Proposition 2.3.5:

**Proposition 5.3.7.** *The equivariant premodel structure on cubical sets has universes in the sense of Definition 2.3.6 for the equivariant fibrations given by the classifiers $\pi: \dot{U}_{\kappa} \to U_{\kappa}$ for sufficiently large inaccessible cardinals $\kappa$.* $\square$

With Propositions 5.3.7 and 5.3.2, we have satisfied the hypotheses of Proposition 3.5.5, so from Proposition 5.3.1 we may conclude:

**Proposition 5.3.8.** *The universes in the equivariant premodel structure on cubical sets are univalent.* $\square$

We now leverage the results of §3.6 to prove that the bases of these universe are equivariantly fibrant objects. Note, however, that in contrast to the analogous result for cubical species, this is not a direct consequence of Proposition 3.6.10.

**Proposition 5.3.9.** *The bases of the universal fibrations for the equivariant premodel structure on cubical sets are fibrant objects.*

*Proof.* As in the proof of Proposition 4.4.7, we can use Proposition 3.6.9 to show that $U$ is fibrant, though in a more subtle way. First, we again equip $U$ with the reflexive relation defined by the object of equivalences constructed by Lemma 3.5.1:

$$\begin{array}{c} U \\ \downarrow \\ U \xleftarrow [ s ]{} \operatorname {E q} (\dot {U}) \xrightarrow [ t ]{} U. \end{array}$$

The map $(s, t): \operatorname{Eq}(\dot{U}) \to U \times U$ is again a fibration by its construction. By univalence, Proposition 5.3.8, the map $t: \operatorname{Eq}(\dot{U}) \to U$ is a trivial fibration and in particular a fibration.

Now the equivariant premodel structure lacks an interval $I$ as required by Proposition 3.6.9, but by the definition of the equivariant fibrations, the images of the maps $(s, t): \operatorname{Eq}(\dot{U}) \to U \times U$ and $t: \operatorname{Eq}(\dot{U}) \to U$ under $\Delta$ are uniform fibrations in $\mathsf{cSet}^{\mathbb{E}}$, and we are trying to show that $\Delta U$ is uniformly fibrant. Since the interval (pre)model structure on cubical species does have such an interval, and the remaining hypotheses of Proposition 3.6.9 are also satisfied for the reflexive relation $\Delta \operatorname{Eq}(\dot{U}) \rightrightarrows \Delta U$, we can conclude that $\Delta U$ is indeed uniformly fibrant. Thus, $U$ is equivariantly fibrant. $\square$

By applying Lemma 3.7.2, we see that:

**Proposition 5.3.10.** *The equivariant premodel structure satisfies the fibration extension property.* $\square$

These results assemble into the main theorem of this section.

**Theorem 5.3.11.** *The category of cubical sets admits a Quillen model structure in which the cofibrations are the monomorphisms and the fibrations are the equivariant fibrations. This model is cylindrical and cartesian closed and satisfies the Frobenius condition, equivalence extension property, and fibration extension property. Moreover, it has univalent universes whose bases are fibrant objects.*

60

*Proof.* Once more, the only result of the statement that we have not yet proven is the fact that the interval premodel structure is in fact a model structure, but this follows formally from Proposition 3.7.3, by Proposition 5.3.10 and the fact that all objects are cofibrant. □

Thus, the equivariant model structure on the topos of cubical sets is a model of homotopy type theory. In contrast to the model of Theorem 4.4.9, the equivariant model structure presents classical homotopy theory, as we demonstrate in the next section.

## 6. THE EQUIVALENCE WITH CLASSICAL HOMOTOPY THEORY

In this section we prove our final main result, that the equivariant cubical model category of Theorem 5.3.11 is equivalent to classical homotopy theory. More specifically, we demonstrate that the triangulation functor $T: \mathbb{C} \to \mathbb{S}$ defines a left Quillen equivalence from the equivariant model structure, whose fibrations are the equivariant fibrations, to Quillen's model structure on simplicial sets [Qui67], whose fibrations are the Kan fibrations. This argument makes use of classical reasoning; see §1.6.2 above.

Our proof makes central use of the fact that the indexing categories $\square$ and $\triangle$ are *Eilenberg–Zilber categories*, a special class of (generalized) Reedy categories introduced by Berger and Moerdijk [BM11]. We develop some general theory of Eilenberg–Zilber categories in §6.2 for that purpose. In particular, we prove in Corollary 6.2.16 that to check that a natural transformation between left Quillen functors with either $\mathbb{C}$ or $\mathbb{S}$ as domain is a natural weak equivalence, it will suffice to check this on those components indexed by quotients of representables by subgroups of their automorphism groups. And in fact, by the two-of-three property, this will follow automatically for terminal object preserving functors, provided these objects are weakly contractible—as is the case in both the equivariant model structure on $\mathbb{C}$ and the classical model structure on $\mathbb{S}$.

These results make it easy to prove that an opposing pair of left Quillen functors between $\mathbb{S}$ and $\mathbb{C}$ define a derived equivalence, and thus we seek a left Quillen functor from $\mathbb{S}$ to $\mathbb{C}$ to define a candidate inverse to triangulation. Our original proof proceeded along the following lines. In [Sat19], Sattler observes that the idempotent completion of the category of *Dedekind* cubes—the full subcategory of $\mathbb{C}$ on the posets $\{0 < 1\}^n$ for $n \geq 0$, which adds connections to the cartesian cubes $\square$—is the category $\triangle$ whose objects are the finite bounded lattices and whose morphisms are the monotone maps between them. Thus the category $\ell$ of presheaves on $\triangle$ is equivalent to the category of presheaves on the Dedekind cubes, which we can equip with the model structure defined in [Sat17], following [CCHM15]. The utility of this result is that the finite ordinals $[n] = \{0 < 1 < \dots < n\}$ are finite complete lattices; indeed, we have a fully faithful embedding $j: \triangle \hookrightarrow \triangle$, in addition to the evident (non-full) inclusion $k: \square \to \triangle$ of the cartesian cube category. These functors induce adjoint triples of functors

![img-64.jpeg](img-64.jpeg)

with the left and right adjoints defined by left and right Kan extension. The composite $j^*k_t: \mathbb{C}$ to $\mathbb{S}$ is the triangulation functor and one can verify that $k^*j_t: \mathbb{S}$ to $\mathbb{C}$ is a left Quillen homotopy inverse.

While this article was in preparation, Reid Barton observed that the triangulation functor in fact arises by restriction along a single functor $i: \triangle \to \square$, and in particular has a left adjoint, which is also left Quillen [Bar24b]. These results are verified in §6.1. In §6.2, we then apply the theory of

61

Eilenberg–Zilber categories sketched above to conclude that all three functors in the adjoint triple

![img-65.jpeg](img-65.jpeg)

are Quillen equivalences. Finally, in §6.3, we compare the equivariant model structure on cubical sets to the test model structure of Cisinski after Grothendieck and prove that they coincide.

6.1. Triangulation. As Barton observed, implicit in Joyal's proof that sSet is the classifying topos for a strict interval is the definition of a faithful dimension-preserving functor

\[
\begin{array}{c} \mathbb {A} \xrightarrow {i} \mathbb {D} \\ \{0 <   \dots <   n \} \longmapsto \{\bot , 1, \ldots , n, \top \} \end{array}
\]

from the simplex category to the cartesian cube category. This functor may be defined using Joyal's "interval representation" [Joy97], a contravariant isomorphism between \(\Delta\) and the opposite of the category of strict intervals, linearly ordered sets \(\{\top > 1 > \cdots > n > \top\}\) for \(n \geq 0\) with \(\bot \neq \top\), and endpoint-preserving ordered maps.\(^{10}\) The category of strict intervals is evidently a subcategory of finite bipointed sets \(\mathsf{Fin}_{\bot \neq \top} \cong \mathbb{D}^{\mathrm{op}}\), thus defining \(i: \Delta \to \mathbb{D}\).

The functor \(i\) sends sends outer face maps \(\delta^0, \delta^n: [n-1] \to [n]\) to the face maps \(I^{n-1} \to I^n\) that respectively fix the first cube coordinate to be \(\top\) and the last cube coordinate to be \(\bot\). The inner face maps \(\delta^i: [n-1] \to [n]\) are sent to the diagonal maps \(I^{n-1} \to I^n\) that identify the \(i\)th and \((i+1)\)th coordinates. The degeneracy maps \(\sigma^i: [n+1] \to [n]\) are sent to the projections \(I^{n+1} \to I^n\) away from the \((i+1)\)th coordinate.

Barton then observed:

Lemma 6.1.1 (Barton). Restriction along i defines the triangulation functor  \( i^{*}: cSet \to sSet \) .

Proof. The triangulation functor is the unique cocontinuous functor extending the product-preserving functor \(\square \to \mathsf{sSet}\) that carries the interval in \(\square\) to the interval in \(\mathsf{sSet}\):

\[
\begin{array}{c} \square \xrightarrow {\text {上}} \mathsf {c S e t} \xrightarrow {T} \mathsf {s S e t} \\ \{\bot , \top \} \longmapsto I ^ {0} \longmapsto \Delta^ {0} \\ \biguplus \mapsto \biguplus \mapsto \biguplus \\ \{\bot , 1, \top \} \longmapsto I ^ {1} \longmapsto \Delta^ {1}. \end{array}
\]

The restriction functor \( i^* \colon \mathsf{cSet} \to \mathsf{sSet} \) is cocontinuous and product-preserving, as is the Yoneda embedding \( \mathbb{1} \colon \square \hookrightarrow \mathsf{cSet} \), so it suffices to show that \( i^*(I^1) = \Delta^1 \) and similarly for the interval maps. Since \( i[1] := \{\bot, 1, \top\} \), \( i^*(I^1) \) is the functor \( \square(i[-], i[1]) \colon \Delta^{\mathrm{op}} \to \mathsf{Set} \). Now the claim follows because the inclusion \( i \) is fully faithful on maps with codomain [1], as in \( \mathsf{Fin}_{\bot \neq \top} \cong \square^{\mathrm{op}} \) any map of bipointed sets with domain \( \{\bot, 1, \top\} \) is order-preserving.

As a right adjoint, \( i^{*}(I^{0}) = \Delta^{0} \) and by inspection, \( i^{*} \) carries the maps \( 0,1\colon I^0\to I^1 \) and \( !\colon I^1\to I^0 \) in \( \square \) to the corresponding maps involving \( \Delta^1 \). Thus \( i^{*} \) coincides with the triangulation functor, as claimed.

\( ^{10} \) Our atypical choice of ordering on the interval coordinates is chosen to match the conventions used in [RS17], which uses the functor  \( i: \Delta \to \square \)  to give a syntactic encoding of the simplices as “shapes” embedded in cubes.

62

We now verify that both left adjoints in the adjoint triple

![img-66.jpeg](img-66.jpeg)

are left Quillen. To analyze the left Kan extension \(i_{!}\), it will be useful to establish the relationship between \(i\) and its augmented analogue. Let \(\Delta_{+}\) and \(\square_{+}\) denote the augmented simplex and augmented cube categories, obtained by freely adjoining initial objects, and write \(i_{+}:\Delta_{+}\to\square_{+}\) for the functor induced by \(i\) that preserves them. Write \(\mathsf{sSet}_{+}:=\mathsf{Set}^{\Delta_{+}^{\mathrm{op}}}\) and \(\mathsf{cSet}:=\mathsf{Set}^{\square_{+}^{\mathrm{op}}}\).

Lemma 6.1.2. The commutative square below-left is exact, defining a canonical natural isomorphism in the square of functors below-right:

![img-67.jpeg](img-67.jpeg)

Proof. Here the isomorphism in the square above-right is the Beck–Chevalley transformation associated to the identity natural transformation in the square above-left, and thus is invertible when the square is exact [Gui80]. Exactness of this square follows from the general observation that for any functor  \( k: C \to D \) , any commutative square of the form below is exact:

\[
\begin{array}{c} \text {C} \xrightarrow {k} \text {D} \\ \iota \Big \downarrow \quad \not \llcorner \quad \Big \downarrow \iota \\ \mathbb {1} * \text {C} \xrightarrow [ \mathbb {1} * k ]{} \mathbb {1} * \text {D}. \end{array}
\]

This in turn can be detected by pasting with exact squares into \(\iota\colon\mathsf{C}\hookrightarrow\mathbb{1}*\mathsf{C}\) over any family of jointly surjective functors into \(\mathbb{1}*\mathsf{C}\) [Mal12, 2.8 with \(\mathcal{W}=\mathcal{W}_{0}\)], such as the pair formed by the left and right inclusions \(\iota\colon\mathbb{1}\hookrightarrow\mathbb{1}*\mathsf{C}\) and \(\iota\colon\mathsf{C}\hookrightarrow\mathbb{1}*\mathsf{C}\). To that end we observe that

\[
\begin{array}{c c} \emptyset \xrightarrow {} \mathsf {C} \xrightarrow {k} \mathsf {D} & \emptyset \xrightarrow {} \mathsf {D} \\ \Big \downarrow \quad \not \llcorner \quad \iota \Big \downarrow \quad \not \llcorner \quad \Big \downarrow \iota \\ \mathbb {1} \xrightarrow [ \iota ]{} \mathbb {1} * \mathsf {C} \xrightarrow [ \mathbb {1} * k ]{} \mathbb {1} * \mathsf {D} & \mathbb {1} \xrightarrow [ \iota ]{} \mathbb {1} * \mathsf {D} \end{array}
\]

where both the left-hand square and the composite rectangle are comma squares, and thus exact. Similarly, the left-hand and right-hand squares in the pasting equation below are exact since the functors  \( \iota \)  are fully-faithful,

\[
\begin{array}{c c} \text {C} \xlongequal {} \text {C} \xrightarrow {k} \text {D} & \text {C} \xrightarrow {k} \text {D} \xlongequal {} \text {D} \\ \left\| \quad \not \llcorner \quad \iota \Big \downarrow \quad \not \llcorner \quad \Big \downarrow \iota \right. & = \\ \text {C} \xleftarrow [ \iota ]{} \mathbb {1} * \text {C} \xrightarrow [ \mathbb {1} * k ]{} \mathbb {1} * \text {D} & \text {C} \xrightarrow [ k ]{} \text {D} \xleftarrow [ \iota ]{} \mathbb {1} * \text {D}, \end{array}
\]

while the trivial square is trivially exact.

Using this, we now demonstrate:

63

# Lemma 6.1.3. The functors

![img-68.jpeg](img-68.jpeg)

preserve monomorphisms.

Proof. This is immediate for the right adjoint $i^*$. For the left adjoint $i_!$, we observe

$$i_! \cong i_! \iota^* \iota_* \cong \iota^* (i_+)_! \iota_*,$$

by Lemma 6.1.2 and fully faithfulness of $\iota: \Delta \hookrightarrow \Delta_+$. Thus, to prove that $i_!$ preserves monomorphisms it suffices to prove that $(i_+)_!$ does.

Monomorphisms in $\mathsf{sSet}_+$ decompose canonically as sequential colimits of pushouts of coproducts of maps of the form $\partial \Delta^n \hookrightarrow \Delta^n$. As a left adjoint, $(i_+)_!$ preserves cell complexes, so it suffices to show that this functor carries these generating maps to monomorphisms. Each boundary inclusion is the joint image of the family of monomorphisms $\delta: \Delta^m \hookrightarrow \Delta^n$ indexed by monomorphisms $\delta: [m] \hookrightarrow [n]$ in $\Delta_+$ with codomain $[n]$. Thus, it suffices to prove that $(i_+)_!$ preserves joint images of monomorphisms between representables. In a Grothendieck topos, the joint image of monomorphisms $(m_i: A_i \hookrightarrow B)_{i \in I}$ is given by the coequalizer of the following parallel pair of maps in the slice over $B$

$$\coprod_{i,j \in I} A_i \times_B A_j \longrightarrow \coprod_{k \in I} A_k$$

and thus a cocontinuous functor between Grothendieck toposes will preserve the joint image of a family of monomorphisms provided it preserves the pullbacks of cospans in the family. In the case of the functor $(i_+)_!$ and the family of monomorphisms $(\delta_i: \Delta^{m_i} \hookrightarrow \Delta^n)_i$, we'll demonstrate this by showing that $\Delta_+$ has pullbacks of face maps and $i_+: \Delta_+ \to \square_+$ preserves them.$^{11}$

The functor $i_+: \Delta_+ \to \square_+$ is the opposite of the functor $i_+: \mathsf{FinInt} \to \mathsf{Fin}_{\bot, \top}$ from the category of finite intervals $\{\bot > 1 > \cdots > n > \top\}$, now possibly with $\bot = \top$, to the category of finite bipointed sets, now dropping the requirement that the basepoints are distinct. We must show that $\mathsf{FinInt}$ has and $i_+: \mathsf{FinInt} \to \mathsf{Fin}_{\bot, \top}$ preserves pushouts of epimorphisms, or equivalently for any finite interval $A$ that the comma category $A \downarrow \mathsf{FinInt}$ has and the forgetful functor $i_+: A \downarrow \mathsf{FinInt} \to i_+ A \downarrow \mathsf{Fin}_{\bot, \top}$ preserves binary coproducts of epimorphisms. On account of the epimorphism–monomorphism orthogonal factorization systems, it suffices to restrict to the subcategories of epimorphisms $\mathsf{FinInt}^{\mathrm{epi}}$ and $\mathsf{Fin}_{\bot, \top}^{\mathrm{epi}}$ and show that binary coproducts exist in $A \downarrow \mathsf{FinInt}^{\mathrm{epi}}$ are preserved by the forgetful functor between comma categories $i_+: A \downarrow \mathsf{FinInt}^{\mathrm{epi}} \to i_+ A \downarrow \mathsf{Fin}_{\bot, \top}^{\mathrm{epi}}$.

For a finite interval $A$, the category $A \downarrow \mathsf{FinInt}^{\mathrm{epi}}$ is the poset whose objects are equivalence relations on the underlying set of $A$ whose equivalence classes are subintervals of $A$ (where the inclusion of a subinterval need not preserve endpoints). The category $i_+ A \downarrow \mathsf{Fin}_{\bot, \top}^{\mathrm{epi}}$ is the poset whose objects are equivalence relations on the underlying set of $A$. Using these descriptions, we see that the functor $i_+: A \downarrow \mathsf{FinInt}^{\mathrm{epi}} \to i_+ A \downarrow \mathsf{Fin}_{\bot, \top}^{\mathrm{epi}}$ is a coreflective embedding, whose right adjoint sends an equivalence relation on the underlying set of $A$ to the equivalence relation that relates elements $x$ and $y$ of $A$ if only if the closed subinterval spanned by these elements belongs to a single equivalence class. In particular, this forgetful functor creates the coproducts that exist in $i_+ A \downarrow \mathsf{Fin}_{\bot, \top}^{\mathrm{epi}}$, which demonstrates what we needed to show.

$^{11}$This is the advantage of working with $i_+$ rather than $i$; $\Delta$ does not have pullbacks of all face maps.

64

Remark 6.1.4. The closely-related criterion of [Sat19, 3.5] is not strong enough to demonstrate that $i_!$ or $(i_+)$! preserve monomorphisms since the pullback in $\Delta$

![img-69.jpeg](img-69.jpeg)

of the maps specified by preserving initial and terminal elements is not preserved by the inclusion into the cartesian cube category. Note however that only one of the maps in the original cospan is a monomorphism. The proof just given demonstrates that pullbacks of pairs of monomorphisms in $\Delta_+$ exist and are preserved by $i_+$.

Lemma 6.1.5. The functor $i_! \colon \mathsf{sSet} \to \mathsf{cSet}$ defines a left Quillen functor from the classical model structure to the equivariant model structure.

Proof. As in [Sat19, 3.6], it suffices to show that $i_!$ carries generalized horn inclusions—inclusions of the union of a proper subset of codimension-one faces into a simplex—to trivial cofibrations. Such generalized horn inclusions either have the form of a face map $\delta \colon \Delta^{n-1} \to \Delta^n$ or are pushouts of a generalized horn inclusion with one less face and in one smaller dimension. Thus, by the 2-of-3 property and induction over the dimension and the number of faces in the generalized horn inclusion, it suffices to show that $i_! \Delta^n \cong I^n$ is weakly contractible for each $n$, which holds because the cubes are weakly contractible in the equivariant model structure by Corollary 5.2.7.

We prove that the other left adjoint $i^* \colon \mathsf{sSet} \to \mathsf{cSet}$ is left Quillen by first demonstrating a result of independent interest: that Kan fibrations of simplicial sets are also equivariant fibrations, which we define as follows.

Definition 6.1.6. Let $\mathsf{E}$ be a locally cartesian closed category equipped with a product-preserving functor $\square \to \mathsf{E}$ from the cartesian cube category, which restricts along the inclusion $\Sigma \subset \square$ to define a symmetric sequence $\mathbb{I} \colon \Sigma \to \mathsf{E}$, specifying $k$-cubes $I^k$ in $\mathsf{E}$ for all $k \ge 1$ together with automorphisms for each $\sigma \in \Sigma_k$. Then an equivariant fibration is a map $f \colon Y \to X$ whose image under the constant diagram functor $\Delta \colon \mathsf{E} \to \mathsf{E}^{\Sigma}$ is an unbiased uniform fibration, i.e., a map which enjoys the uniform lifting property as below-left defined relative to the diagram in $\mathsf{E}$ below-right:

![img-70.jpeg](img-70.jpeg)

When $\mathsf{E}$ is a presheaf category, it suffices to consider uniform lifting against monomorphisms with representable codomain.

Proposition 6.1.7. Kan fibrations of simplicial sets are equivariant fibrations.

Proof. Since the classical model structure on simplicial sets is cartesian closed, any Kan fibration $f \colon Y \to X$ admits the structure of a biased uniform fibration, as in Definition 3.6.7i with respect to the interval $\Delta^1$; see [GS17, §9]. In fact, when $f \colon Y \to X$ is a Kan fibration, it also admits the structure of an unbiased uniform fibration by [CS25, 4.22–23].

65

Unpacking, this means that a Kan fibration $f \colon Y \twoheadrightarrow X$ can be equipped with a uniform lifting function $i_{c,\zeta}$ as below:

$$\begin{array}{c} B \cup D \times I \xrightarrow{\alpha \cup_{\alpha} \alpha \times I} A \cup C \times I \xrightarrow{\langle y, z \rangle} Y \\ \langle [\zeta \alpha], d \times 1 \rangle \Biggl \downarrow \quad \begin{array}{c} \lrcorner \\ \downarrow \\ i_{d,\zeta\alpha}(y\alpha, z(\alpha \times I), x(\alpha \times I)) \\ \downarrow \\ B \times I \xrightarrow{\alpha \times I} A \times I \xrightarrow{x} X. \end{array} \Biggl \downarrow f \end{array}$$

Our task is to equip a uniform fibration ($f \colon Y \twoheadrightarrow X, i_{c,e}$) with the structure of an equivariant fibration. To do so, we make use of a map

$$\gamma_{\wedge} \colon I^k \times I \to I^k \qquad \gamma_{\wedge}(x_1, \dots, x_k, e) := (x_1 \wedge e, \dots, x_k \wedge e),$$

that restricts along $\{0\} \mapsto I$ to the constant map at $\vec{0} \in I^k$ and restricts along $\{1\} \mapsto I$ to the identity. This “min connection” exists because we are working with triangulated cubes in the category of simplicial sets, rather than with cartesian cubes.$^{12}$ For any $\zeta \colon A \to I^k$, the composite

$$\gamma_{\wedge} \zeta := A \times I \xrightarrow{\zeta \times I} I^k \times I \xrightarrow{\gamma_{\wedge}} I^k$$

defines a homotopy from the constant map $\vec{0} \colon A \to I^k$ to $\zeta$. We frequently pair this contracting homotopy with the map that records the coordinates from $A$, which we abbreviate as:

$$\vec{\gamma_{\wedge}} \zeta := A \times I \xrightarrow{(\pi, \gamma_{\wedge} \zeta)} A \times I^k.$$

The uniform fibration structure of $f$ provides a solution to the lifting problem

$$\begin{array}{c} A \times \{1\} \cup_{C \times \{1\}} C \times I \xrightarrow{A \cup \vec{\gamma_{\wedge}} \zeta c} A \cup C \times I^k \xrightarrow{\langle y, z \rangle} Y \\ \downarrow_{c \times \partial_1} \quad \downarrow_{i_{c,1}(z\vec{\gamma_{\wedge}} \zeta c, y, x\vec{\gamma_{\wedge}} \zeta)} \quad \downarrow_{\langle [\zeta], c \times I^k \rangle} \\ A \times I \xrightarrow{\vec{\gamma_{\wedge}} \zeta} A \times I^k \xrightarrow{x} X. \end{array}$$

This gives rise to a new lifting problem

$$\begin{array}{c} A \cup C \times I^k \to \left( C \times I^k \times I \cup_{C \times I} A \times I \right) \bigcup_{C \times I^k \times \{0\} \cup_{C \times \{0\}} A \times \{0\}} A \times I^k \times \{0\} \xrightarrow{A \times ! \times I} A \times I \xrightarrow{i_{c,1}(\cdots)} Y \\ \langle [\zeta], c \times I^k \rangle \Biggl \downarrow \quad \begin{array}{c} \lrcorner \\ \downarrow \\ \langle [\zeta], c \times I^k \rangle \hat{\times} \partial_0 \\ \downarrow \\ A \times I^k \times \{1\} \xrightarrow{A \times I^k \times \partial_1} A \times I^k \times I \xrightarrow{i_{\langle c \times I^k, [\zeta] \rangle, 0} (i_{c,1}(\cdots)!, x\gamma_{\wedge})} A \times I^k \xrightarrow{x} X, \end{array} \Biggl \downarrow f \end{array}$$

which restricts to the original lifting problem. Thus, we define $j_{c,\zeta}(y, z, x)$ to be the composite

$$j_{c,\zeta}(y, z, x) := i_{\langle c \times I^k, [\zeta] \rangle, 0} (i_{c,1}(z\vec{\gamma_{\wedge}} \zeta c, y, x\vec{\gamma_{\wedge}} \zeta)!, x\gamma_{\wedge}) \cdot (A \times I^k \times \partial_1).$$

It remains to verify that

$$j_{c,\zeta}(y, z, x) \cdot (\alpha \times \sigma^{-1}) = j_{d,\sigma\zeta\alpha}(y\alpha, z(\alpha \times \sigma^{-1}), x(\alpha \times \sigma^{-1})).$$

$^{12}$We could equally use the “max connection” to obtain a map that restricts along $\{0\} \mapsto I$ to the identity and restricts along $\{1\} \mapsto I$ to the constant map at $\vec{1} \in I^k$.

66

On account of the commutative diagrams

$$\begin{array}{c c c} B \times I \xrightarrow {\sigma \zeta \alpha \times I} I ^ {k} \times I \xrightarrow {\gamma_ {\wedge}} I ^ {k} & & B \times I \xrightarrow {\gamma_ {\wedge} ^ {\prime} \sigma \zeta \alpha} B \times I ^ {k} \\ \alpha \times I \Biggl \downarrow & \sigma^ {- 1} \times I & \Biggl \downarrow \sigma^ {- 1} \\ A \times I \xrightarrow [ \zeta \times I ]{} I ^ {k} \times I \xrightarrow [ \gamma_ {\wedge} ]{} I ^ {k} & & A \times I \xrightarrow [ \gamma_ {\wedge} ^ {\prime} \zeta ]{} A \times I ^ {k}, \end{array}$$

we see that the outer rectangles in the following lifting problems coincide:

$$\begin{array}{c} B \times \{1 \} \underset {D \times \{1 \}} {\cup} D \times I \xrightarrow {B \cup \gamma_ {\wedge} ^ {\prime} \sigma \zeta \alpha d} B \underset {D} {\cup} D \times I ^ {k} \xrightarrow {\alpha \cup_ {\alpha} \alpha \times \sigma^ {- 1}} A \underset {C} {\cup} C \times I ^ {k} \xrightarrow {\langle y , z \rangle} Y \\ d \hat {\times} \partial_ {1} \Bigg \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \times I \xrightarrow [ \gamma_ {\wedge} ^ {\prime} \sigma \zeta \alpha ]{} B \times I ^ {k} \xrightarrow [ \alpha \times \sigma^ {- 1} ]{} A \times I ^ {k} \xrightarrow [ x ]{} X \end{array}$$

$$\begin{array}{c} B \times \{1 \} \underset {D \times \{1 \}} {\cup} D \times I \xrightarrow {\alpha \cup_ {\alpha} (\alpha \times I)} A \times \{1 \} \underset {C \times \{1 \}} {\cup} C \times I \xrightarrow {A \cup \gamma_ {\wedge} ^ {\prime} \zeta c} A \underset {C} {\cup} C \times I ^ {k} \xrightarrow {\langle y , z \rangle} Y \\ d \hat {\times} \partial_ {1} \Bigg \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \times I \xrightarrow [ \alpha \times I ]{} A \times I \xrightarrow [ \gamma_ {\wedge} ^ {\prime} \zeta ]{} A \times I ^ {k} \xrightarrow [ x ]{} X. \end{array}$$

By uniformity of $(f, i)$ in the left-hand pullback square of the second of these diagrams,

$$\begin{array}{l} i _ {c, 1} (y, z \vec {\gamma_ {\wedge}} \zeta c, x \vec {\gamma_ {\wedge}} \zeta) \cdot (\alpha \times I) = i _ {d, 1} (y \alpha , z \vec {\gamma_ {\wedge}} \zeta c (\alpha \times I), x \vec {\gamma_ {\wedge}} \zeta (\alpha \times I)) \\ = i _ {d, 1} (y \alpha , z (\alpha \times \sigma^ {- 1}) \vec {\gamma_ {\wedge}} \sigma \zeta \alpha d, x (\alpha \times \sigma^ {- 1}) \vec {\gamma_ {\wedge}} \sigma \zeta \alpha). \end{array}$$

By construction, the chosen lift $j_{d,\sigma \zeta \alpha}(y\alpha ,z(\alpha \times \sigma^{-1}),x(\alpha \times \sigma^{-1}))$ is the diagonal composite

$$\begin{array}{c} B \underset {D} {\cup} D \times I ^ {k} \to \left(D \times I ^ {k} \times I \underset {D \times I} {\cup} B \times I\right) \underset {D \times I ^ {k} \times \{0 \} \underset {D \times \{0 \}} {\cup} B \times \{0 \}} {\cup} B \times I ^ {k} \times \{0 \} \xrightarrow {B \times ! \times I} B \times I \xrightarrow {i _ {d , 1} (\cdots)} Y \\ \Bigg \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \langle [ \sigma \zeta \alpha ], d \times I ^ {k} \rangle \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Bigg \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \times I ^ {k} \times \{1 \} \xrightarrow [ B \times I ^ {k} \times \partial_ {1} ]{} B \times I ^ {k} \times I \xrightarrow [ B \times \gamma_ {\wedge} ]{} B \times I ^ {k} \xrightarrow [ x (\alpha \times \sigma^ {- 1}) ]{} X, \end{array}$$

while $j_{c,\zeta}(y,z,x)\cdot (\alpha \times \sigma^{-1})$ is the restriction of the diagonal composite

$$\begin{array}{c} A \underset {C} {\cup} C \times I ^ {k} \to \left(C \times I ^ {k} \times I \underset {C \times I} {\cup} A \times I\right) \underset {C \times I ^ {k} \times \{0 \} \underset {C \times \{0 \}} {\cup} A \times \{0 \}} {\cup} A \times I ^ {k} \times \{0 \} \xrightarrow {A \times ! \times I} A \times I \xrightarrow {i _ {c , 1} (\cdots)} Y \\ \langle [ \zeta ], c \times I ^ {k} \rangle \Bigg \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A \times I ^ {k} \times \{1 \} \xrightarrow [ A \times I ^ {k} \times \partial_ {1} ]{} A \times I ^ {k} \times I \xrightarrow [ A \times \gamma_ {\wedge} ]{} A \times I ^ {k} \xrightarrow [ x ]{} X \end{array}$$

67

along $\alpha \times \sigma^{-1} \colon B \times I^k \to A \times I^k$. Observe that we can perform these two restrictions needed to compute $j_{c,\zeta}(y, z, x) \cdot (\alpha \times \sigma^{-1})$ in either order, on account of the commutative cube

![img-71.jpeg](img-71.jpeg)

Thus:

$$\begin{array}{l} j_{c,\zeta}(y, z, x) \cdot (\alpha \times \sigma^{-1}) \\ = i_{\langle c \times I^k, [\zeta] \rangle, 0} (i_{c,1}(y, z\vec{\gamma}_{\wedge}\zeta c, x\vec{\gamma}_{\wedge}\zeta)!, x\gamma_{\wedge}) \cdot (A \times I^k \times \partial_1) \cdot (\alpha \times \sigma^{-1}) \\ = i_{\langle c \times I^k, [\zeta] \rangle, 0} (i_{c,1}(y, z\vec{\gamma}_{\wedge}\zeta c, x\vec{\gamma}_{\wedge}\zeta)!, x\gamma_{\wedge}) \cdot (\alpha \times \sigma^{-1} \times I) \cdot (B \times I^k \times \partial_1) \end{array}$$

Note further that the front face of this cube is a pullback, since it arises as the pushout product of the pullback in the back face with $\partial_1 \colon \{1\} \mapsto I$. By uniformity of $(f, i)$ in this pullback square:

$$= i_{\langle d \times I^k, [\sigma\zeta\alpha] \rangle, 0} (i_{c,1}(y, z\vec{\gamma}_{\wedge}\zeta c, x\vec{\gamma}_{\wedge}\zeta)(\alpha \times I)!, x\gamma_{\wedge}(\alpha \times \sigma^{-1})) \cdot (B \times I^k \times \partial_1)$$

By the uniformity calculation above, the domains of these lifting problems coincide. Thus:

$$\begin{array}{l} = i_{\langle d \times I^k, [\sigma\zeta\alpha] \rangle, 0} (i_{d,1}(y\alpha, z(\alpha \times \sigma^{-1})\vec{\gamma}_{\wedge}\sigma\zeta\alpha d, x(\alpha \times \sigma^{-1})\vec{\gamma}_{\wedge}\sigma\zeta\alpha)!, x(\alpha \times \sigma^{-1})\gamma_{\wedge}) \cdot (B \times I^k \times \partial_1) \\ = j_{d,\sigma\zeta\alpha}(y\alpha, z(\alpha \times \sigma^{-1}), x(\alpha \times \sigma^{-1})), \end{array}$$

which is the required equivariant uniformity condition.

**Lemma 6.1.8.** *The functor $i^* \colon \mathsf{cSet} \to \mathsf{sSet}$ defines a left Quillen functor from the equivariant model structure to the classical model structure.*

*Proof.* To prove that triangulation is left Quillen, it suffices to show that the right adjoint $i_*$ carries Kan fibrations to equivariant fibrations of cubical sets, for which it suffices to show that Kan fibrations lift against the image of the generating category of Construction 5.2.4 under the functor $i^*$. After triangulation, the objects and morphisms in this generating category have the form

$$\begin{array}{c} (\Delta^1)^m \cup_D D \times (\Delta^1)^k \xrightarrow{\alpha \times \sigma^{-1}} (\Delta^1)^n \cup_C C \times (\Delta^1)^k \\ \langle [\xi], d \times 1 \rangle \Big\downarrow \quad \text{↵} \quad \Big\downarrow \langle [\zeta], c \times 1 \rangle \\ (\Delta^1)^m \times (\Delta^1)^k \xrightarrow[\alpha \times \sigma^{-1}]{} (\Delta^1)^n \times (\Delta^1)^k \end{array}$$

where $C$ and $D$ are triangulations of cubical subsets of the $n$-cube and $m$-cube respectively. Thus, the equivariance of Kan fibrations established in Proposition 6.1.7 defines uniform lifts against these squares.

To prove that the left Quillen functors of Lemmas 6.1.5 and 6.1.8 define Quillen equivalences, we appeal to the general theory of Eilenberg–Zilber categories, which we now review.

68

6.2. **Eilenberg–Zilber categories.** The categories $\triangle$ and $\square$ are both *Reedy categories*—the former in Dan Kan's original 'strict' sense and the latter in the 'generalized' sense of [BM11]—that are moreover *Eilenberg–Zilber categories*, defined below. These properties enable inductive arguments concerning the monomorphisms in the presheaf categories **sSet** and **cSet** respectively.

A Reedy category $\mathsf{A}$ comes with classes of 'degree-decreasing' and 'degree-increasing maps,' defined relative to a degree function $\deg: \mathrm{ob}\mathsf{A} \rightarrow \mathbb{N}$. In the case of Eilenberg–Zilber categories, defined below, the degree-decreasing maps are the split epimorphisms, while the degree-increasing maps are the monomorphisms.

**Definition 6.2.1** ([BM11, 6.7]). An **Eilenberg–Zilber** category is a small category $\mathsf{A}$ equipped with a degree function $\deg: \mathrm{ob}\mathsf{A} \rightarrow \mathbb{N}$ so that

- (i) Isomorphisms preserve the degree, whereas non-invertible monomorphisms or split epimorphisms strictly raise and lower the degree, respectively, when moving from their domain to their codomain.
- (ii) Every $f \in \mathrm{mor}\mathsf{A}$ may be factored as a split epimorphism followed by a monomorphism.
- (iii) Any pair of split epimorphisms with common domain has an **absolute pushout**: a pushout in $\mathsf{A}$ that is preserved by the Yoneda embedding $\updownarrow: \mathsf{A} \hookrightarrow \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}}$.

Berger and Moerdijk observe that $\triangle$ is an Eilenberg–Zilber category [BM11, 6.8]. By [Cam23, Theorem 8.12(1)], the cartesian cube category is as well (as could also be checked by directly verifying that each pair of epimorphisms in $\square$ with common domain has an absolute pushout).

We review a few results from general Reedy category theory [RV14; Rie] and then explain what is special about Eilenberg–Zilber categories. Let $\mathsf{A}$ be an Eilenberg–Zilber category and write $\mathsf{A} \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}}$ for the hom bifunctor of arrows in $\mathsf{A}$. Let

$$\mathrm{sk}_n \mathsf{A} \hookrightarrow \mathsf{A} \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}}$$

denote the subfunctor of arrows of degree at most $n$, by which we mean arrows that factor through an object of degree $n$.

**Definition 6.2.2** (boundaries of representable functors). For $a \in \mathsf{A}$, write $\mathsf{A}_a \in \mathrm{Set}^{\mathsf{A}}$ and $\mathsf{A}^a \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}}$ for the co- and contravariant representable functors. If $a \in \mathsf{A}$ has degree $n$, write

$$\begin{aligned} \overleftarrow{\partial} \mathsf{A}_a &:= \mathrm{sk}_{n-1} \mathsf{A}_a & \in \mathrm{Set}^{\mathsf{A}} & \text{and} \\ \overrightarrow{\partial} \mathsf{A}^a &:= \mathrm{sk}_{n-1} \mathsf{A}^a & \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}}. \end{aligned}$$

The external (pointwise) product defines a bifunctor $\mathrm{Set}^{\mathsf{A}} \times \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}} \xrightarrow{-\times-} \mathrm{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}}$. For any $a \in \mathsf{A}$, the exterior Leibniz product

$$(6.2.3) \quad \mathsf{A}_a \times \overrightarrow{\partial} \mathsf{A}^a \cup \overleftarrow{\partial} \mathsf{A}_a \times \mathsf{A}^a \xrightarrow{(\overleftarrow{\partial} \mathsf{A}_a \hookrightarrow \mathsf{A}_a) \times (\overrightarrow{\partial} \mathsf{A}^a \hookrightarrow \mathsf{A}^a)} \mathsf{A}_a \times \mathsf{A}^a$$

defines the subfunctor of pairs of morphisms $h \cdot g$ with $\mathrm{dom}(h) = \mathrm{cod}(g) = a$ in which at least one of the morphisms $g$ and $h$ has degree less than the degree of $a$. There is a natural 'composition' map whose domain is the external product of the contravariant and covariant representables

$$(6.2.4) \quad \mathsf{A}_a \times \mathsf{A}^a \xrightarrow{\circ} \mathsf{A}.$$

Its image is the subfunctor of arrows in $\mathsf{A}$ that factor through $a$, but (6.2.4) is not in general a monomorphism: e.g., this fails to be the case whenever $a$ has non-identity automorphisms.

By Definition 6.2.1(i), the groupoid core $\mathsf{G} \subset \mathsf{A}$ of a Reedy category decomposes as a coproduct $\mathsf{G} = \coprod_{n \in \mathbb{N}} \mathsf{G}(n)$, where $\mathsf{G}(n)$ is the subgroupoid of isomorphisms between objects of degree $n$. Any

69

isomorphism in A restricts in the obvious way to a natural isomorphism between the boundaries of the corresponding representable functors, which thus assemble into profunctors

\[
\overleftarrow {\partial} \mathsf {A} _ {n} \hookrightarrow \mathsf {A} _ {n} \in \operatorname{Set} ^ {\mathsf {G} (n) ^ {\mathrm{op}} \times \mathsf {A}} \quad \text { and } \quad \overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} ^ {n} \in \operatorname{Set} ^ {\mathsf {A} ^ {\mathrm{op}} \times \mathsf {G} (n)}.
\]

When we compose these profunctors over  \( \mathsf{G}(n) \) , we obtain a profunctor from A to A which is the “generalized cell” attached to form  \( sk_{n}A \)  from  \( sk_{n-1}A \)  [Rie, §4]:

Theorem 6.2.5. The inclusion \(\emptyset \hookrightarrow A\) has a canonical presentation as a generalized cell complex:

\[
\begin{array}{c} \overleftarrow {\partial} \mathsf {A} _ {n} \underline {{\times}} _ {\mathsf {G} (n)} \mathsf {A} ^ {n} \cup \mathsf {A} _ {n} \underline {{\times}} _ {\mathsf {G} (n)} \overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} _ {n} \underline {{\times}} _ {\mathsf {G} (n)} \mathsf {A} ^ {n} \\ \circ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \emptyset \hookrightarrow \operatorname{sk} _ {0} \mathsf {A} \dots\dots\partial_ {\mathrm{sk} _ {n - 1}} \mathsf {A} \xleftarrow {} \operatorname{sk} _ {n} \mathsf {A} \dots\dots\partial_ {\mathrm{colim} _ {n}} \operatorname{sk} _ {n} \mathsf {A} \cong \mathsf {A}, \end{array}
\]

i.e., a composite of pushouts of cells constructed as coends of exterior Leibniz products

\[
(\overleftarrow {\partial} \mathsf {A} _ {n} \hookrightarrow \mathsf {A} _ {n}) \underline {{\times}} _ {\mathsf {G} (n)} (\overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} ^ {n}) := \int^ {a \in \mathsf {G} (n)} (\overleftarrow {\partial} \mathsf {A} _ {a} \hookrightarrow \mathsf {A} _ {a}) \underline {{\times}} (\overrightarrow {\partial} \mathsf {A} ^ {a} \hookrightarrow \mathsf {A} ^ {a}),
\]

attached at stage n.

As a corollary of Theorem 6.2.5, any natural transformation \( f \colon X \to Y \in \mathsf{E}^{\mathsf{A}^{\mathrm{op}}} \) valued in a cocomplete category \( \mathsf{E} \) admits a canonical presentation as a generalized cell complex, obtained by applying the Leibniz construction to the weighted colimit bifunctor \( *_{\mathsf{A}} \colon \mathsf{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}} \times \mathsf{E}^{\mathsf{A}^{\mathrm{op}}} \to \mathsf{E}^{\mathsf{A}^{\mathrm{op}}} \).

Corollary 6.2.6. Let A be a Reedy category and let E be bicomplete. Any morphism  \( f: X \to Y \in E^{A^{op}} \)  is a generalized cell complex

\[
X \to X \cup_ {\mathrm{sk} _ {0} X} \mathrm{sk} _ {0} Y \to \dots \to X \cup_ {\mathrm{sk} _ {n - 1} X} \mathrm{sk} _ {n - 1} Y \to X \cup_ {\mathrm{sk} _ {n} X} \mathrm{sk} _ {n} Y \to \dots \to \operatorname{colim} \cong Y
\]

with the generalized cell

\[
(\overrightarrow {\partial} \mathsf {A} ^ {n} \hookrightarrow \mathsf {A} ^ {n}) \stackrel {*} {\ast_ {\mathsf {G} (n)}} \widehat {\ell_ {n}} f \tag {6.2.7}
\]

attached at stage n.

Here \(\widehat{\ell}_n f \in \mathsf{E}^{\mathsf{G}(n)^{\mathrm{op}}}\) is the diagram formed by the Leibniz weighted colimit of \(f\) and \(\overleftarrow{\partial}\mathsf{A}_n \hookrightarrow \mathsf{A}_n\). Its component at \(a \in \mathsf{A}\) of degree \(n\) is the relative latching map, the Leibniz weighted colimit defined by the pushout of the map \(L_a f := \overleftarrow{\partial}\mathsf{A}_a *_{\mathsf{A}} f\):

\[
\widehat {\ell} _ {a} f := (\overleftarrow {\partial} \mathsf {A} _ {a} \hookrightarrow \mathsf {A} _ {a}) \stackrel {*} {\ast} _ {\mathsf {A}} f \qquad \qquad \begin{array}{c} L _ {a} X \xrightarrow {L _ {a} f} L _ {a} Y \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X _ {a} \xrightarrow {} \ell_ {a} f \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ f _ {a} \end{array}
\]

We now specialize to the case E = Set and impose the Eilenberg–Zilber hypothesis on A. Let X be a presheaf on an Eilenberg–Zilber category A. An element  \( x \in X_{a} \)  is degenerate if there exists a non-invertible split epimorphism  \( \pi: a \twoheadrightarrow b \)  and a  \( y \in X_{b} \)  so that  \( x = y\pi \) ; and non-degenerate otherwise. For degenerate x, we refer to the factorization  \( x = y\pi \)  as an Eilenberg–Zilber decomposition of x. As observed in [BM11, 6.9–10], the axioms of Definition 6.2.1 imply that Eilenberg–Zilber decompositions are essentially unique, which implies that the latching maps  \( L_{a}X \mapsto X_{a} \)  are monomorphisms whose images are the degenerate elements. Moreover, the following relative version of this result holds:

70

**Lemma 6.2.8.** Let $\mathsf{A}$ be an Eilenberg–Zilber category. Then for all $f: X \to Y$ in $\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ each relative latching map $\widehat{\ell}_a f$ is a monomorphism if and only if each component $f_a: X_a \hookrightarrow Y_a$ is a monomorphism, and either hypothesis implies that for each $a \in \mathsf{A}$, the latching square below is a pullback:

$$\begin{array}{ccc} L_a X & \xrightarrow{L_a f} & L_a Y \\ \downarrow & \downarrow & \downarrow \\ X_a & \xrightarrow{f_a} & Y_a. \end{array}$$

*Proof.* When $f: X \to Y$ is a monomorphism, each map in the latching square is a monomorphism, and it is easy to see that the latching square is a pullback. It suffices to show that $L_a X$ surjects onto the pullback $X_a \times_{Y_a} L_a Y$. If the image of $x \in X_a$ is degenerate, with $f(x) = y' \cdot \epsilon$, then we may choose a section $\delta$ of $\epsilon$ and observe that $x$ and $x \cdot \delta \cdot \epsilon$ have the same image under $f$, proving that $x$ is degenerate. Thus the latching square is a pullback and then the relative latching map is a monomorphism, the union of the subobjects of $Y_a$.

The converse implication holds for general Reedy categories without the Eilenberg–Zilber hypothesis [Rie, §8].

Lemma 6.2.8 may be summarized by saying that when $\mathsf{A}$ is an Eilenberg–Zilber category, the injective Reedy monomorphisms, defined below, are just the pointwise monomorphisms.

**Definition 6.2.9** (Berger–Moerdijk). A map $f: X \to Y$ in $\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ is an **injective Reedy monomorphism** if for all $a \in \mathsf{A}$, the map $\widehat{\ell}_a f$ is a monomorphism.

The injective Reedy monomorphisms form the left class of a weak factorization system that is left-lifted along the left adjoint $\widehat{\ell}_{\bullet -}$ displayed below from the (monomorphism, equivariant split epimorphism) weak factorization system on $\mathsf{Set}^{\mathsf{G}^{\mathrm{op}}}$, which in turn is the “injective” or left lifting of the (monomorphism, split epimorphism) weak factorization system on $\mathsf{Set}^{\mathrm{obA}}$.$^{13}$

$$\begin{array}{ccc} \mathcal{M}_{\mathrm{inj}}[\mathsf{A}] & \longrightarrow & \mathcal{M}_{\mathrm{inj}} \\ \downarrow & \downarrow & \downarrow \\ (\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}})^2 & \xrightarrow{\widehat{\ell}_{\bullet -}} & (\mathsf{Set}^{\mathsf{G}^{\mathrm{op}}})^2. \end{array}$$

When $\mathsf{A}$ is an Eilenberg–Zilber category, Corollary 6.2.6 tells us that any monomorphism $f$ factors as a transfinite composite of pushouts of maps of the form (6.2.7) where $\widehat{\ell}_n f \in \mathsf{Set}^{\mathsf{G}(n)^{\mathrm{op}}}$ is a monomorphism. The groupoid $\mathsf{G}(n)$ of isomorphisms between objects of degree $n$ is equivalent to the disjoint union of the 1-object groupoids associated to automorphism groups $\operatorname{Aut}(a)$, where the disjoint union is over the set of isomorphism classes of objects of degree $n$.$^{14}$ So $\mathsf{Set}^{\mathsf{G}(n)^{\mathrm{op}}}$ is equivalent to the product of categories of the form $\mathsf{Set}^{\operatorname{Aut}(a)^{\mathrm{op}}}$ where $\deg(a) = n$.

Thus, we study the (injective monomorphism, injective split epimorphism) weak factorization system on the category $\mathsf{Set}^{\mathsf{G}^{\mathrm{op}}}$ of right $G$-sets, for $G$ a group. In this category, the injective monomorphisms are just the monomorphisms, while the injective split epimorphisms are the $G$-split epimorphisms: maps of right $G$-sets that admit a $G$-equivariant section.

$^{13}$Projective Reedy weak factorization systems may be defined similarly using the “projective” or right lifting to $\mathsf{Set}^{\mathbb{C}}$ [BM11, 1.6, 1.8].

$^{14}$In both $\square$ and $\triangle$ there is a unique object of degree $n$, but this is not a requirement of the Eilenberg–Zilber axioms.

71

**Lemma 6.2.10.** *The monomorphisms in $\mathsf{Set}^{G^{\mathrm{op}}}$ are pushouts of coproducts of the maps*

$$\{\emptyset \hookrightarrow G/H\}_{H \subset G}$$

*where the right $G$-sets are the sets of right cosets $G/H$ of all subgroups $H$ of $G$.*

*Proof.* Objects in the category $\mathsf{Set}^{G^{\mathrm{op}}}$ of right $G$-sets decompose as coproducts of orbits, on which $G$ acts transitively. Each orbit is $G$-equivariantly isomorphic to $G/H$, the right $G$-set of right cosets by a subgroup $H$. The stabilizer groups of the elements in this orbit are then conjugate to $H$. By $G$-equivariance, monomorphisms in this category attach new orbits. Thus, each monomorphism may be expressed as a pushout of maps of the form $\emptyset \hookrightarrow G/H$, for each orbit with stabilizer group $H$ that is not in the image of the domain. $\square$

Putting this together we arrive at the following result:

**Proposition 6.2.11.** *Any monomorphism $f: X \to Y \in \mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ between presheaves indexed by an Eilenberg–Zilber category $\mathsf{A}$ is generalized cell complex*

$$X \to X \cup_{\mathrm{sk}_0 X} \mathrm{sk}_0 Y \to \cdots \to X \cup_{\mathrm{sk}_{n-1} X} \mathrm{sk}_{n-1} Y \to X \cup_{\mathrm{sk}_n X} \mathrm{sk}_n Y \to \cdots \to \mathrm{colim} \cong Y$$

*where the cells attached at stage $n$ are coproducts of cells of the form*

$$\overrightarrow{\partial} \mathsf{A}^a_{/H} \hookrightarrow \mathsf{A}^a_{/H} \quad (6.2.12)$$

*where $\deg(a) = n$ and $H \subset \mathrm{Aut}(a)$.*

*Proof.* By Lemma 6.2.10, the relative latching map $\widehat{\ell}_n f \in \mathsf{Set}^{\mathsf{G}(n)^{\mathrm{op}}}$ is a pushout of coproducts of maps of the form $\emptyset \hookrightarrow G(n)^a_{/H}$, where $a \in \mathsf{G}(n)$, $H \subset \mathrm{Aut}(a)$, and $G(n)^a$ is the contravariant representable. By cocontinuity of the weighted colimit functor and the coYoneda lemma, the cell $(\overrightarrow{\partial} \mathsf{A}^n \hookrightarrow \mathsf{A}^n) \stackrel{\star}{\star}_{\mathsf{G}(n)} \widehat{\ell}_n f$ of (6.2.7) is then a pushout of coproducts of cells of the form

$$(\overrightarrow{\partial} \mathsf{A}^n \hookrightarrow \mathsf{A}^n) \stackrel{\star}{\star}_{\mathsf{G}(n)} (\emptyset \hookrightarrow \mathsf{G}(n)^a_{/H}) \cong \overrightarrow{\partial} \mathsf{A}^a_{/H} \hookrightarrow \mathsf{A}^a_{/H}.$$

Thus, by Corollary 6.2.6, $X \cup_{\mathrm{sk}_{n-1} X} \mathrm{sk}_{n-1} Y \hookrightarrow X \cup_{\mathrm{sk}_n X} \mathrm{sk}_n Y$ is a pushout of coproducts of cells of this form. $\square$

**Lemma 6.2.13.** *Let $\mathsf{A}$ be an Eilenberg–Zilber category. Then the monomorphisms in $\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ are generated under coproduct, pushout, sequential composition, and right cancelation among monomorphisms by the maps $\emptyset \to \mathsf{A}^a_{/H}$ valued in the quotient of a representable presheaf at some $a \in \mathsf{A}$ by an arbitrary subgroup $H$ of its automorphism group.*

*Proof.* By Proposition 6.2.11, the monomorphisms are generated under coproduct, pushout, and sequential composition by the maps $\overrightarrow{\partial} \mathsf{A}^a_{/H} \to \mathsf{A}^a_{/H}$ for $a \in \mathsf{A}$ and $H \subset \mathrm{Aut}(a)$. Under right cancelation among monomorphisms

$$\begin{array}{c} \emptyset \longrightarrow \overrightarrow{\partial} \mathsf{A}^a_{/H} \\ \searrow \downarrow \stackrel{\vee}{\downarrow} \mathsf{A}^a_{/H}, \end{array}$$

these maps are generated by monomorphisms of the form $\emptyset \hookrightarrow \mathsf{A}^a_{/H}$ and $\emptyset \hookrightarrow \overrightarrow{\partial} \mathsf{A}^a_{/H}$. We prove that the latter class are generated by the former under coproduct, pushout, sequential composition, and right cancelation among monomorphisms by induction in the degree of the object $a \in A$.

When $a$ has degree zero, $\overrightarrow{\partial} \mathsf{A}^a$ is empty, covering the base case of the induction. So we may suppose that $a$ has degree $n$ and our task is to show that $\emptyset \hookrightarrow \overrightarrow{\partial} \mathsf{A}^a_{/H}$ may be generated under coproduct, pushout, transfinite composition, and right cancelation among monomorphisms by maps of the

72

form $\emptyset \mapsto \mathsf{A}_{/H}^{b}$ with $\deg(b) \leq n$ under the inductive hypothesis that when $\deg(b) < n$, the maps $\emptyset \mapsto \overrightarrow{\partial}\mathsf{A}_{/H}^{b}$ are in this class. From right cancelation, this tells us that the maps $\overrightarrow{\partial}\mathsf{A}_{/H}^{b} \to \mathsf{A}_{/H}^{b}$ are in this class when $\deg(b) < n$. The presheaf $\overrightarrow{\partial}\mathsf{A}_{/H}^{a} \in \mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ is $(n-1)$-skeletal, so from Proposition 6.2.11, we see that $j^{a} \colon \emptyset \mapsto \overrightarrow{\partial}\mathsf{A}_{/H}^{a}$ factors as a composite of pushouts of coproducts of the maps $\overrightarrow{\partial}\mathsf{A}_{/K}^{b} \hookrightarrow \mathsf{A}_{/K}^{b}$ for $K \subset \operatorname{Aut}(b)$, completing the induction.

We now return to the question of proving that the left Quillen functors $i_{!}$ and $i^{*}$ are Quillen equivalences. As the cofibrations are the monomorphisms, all objects in each of the categories sSet and cSet are cofibrant. By Ken Brown's lemma, left Quillen functors preserve weak equivalences between cofibrant objects. Consequently:

**Corollary 6.2.14.** *Each of the functors*

![img-72.jpeg](img-72.jpeg)

*preserves weak equivalences.*

To demonstrate that these functors are inverse left Quillen equivalences, it suffices to show that the total left derived functors define equivalences, for which it suffices to demonstrate that the unit $\eta \colon \mathrm{id} \Rightarrow i^{*}i_{!}$ and counit $\epsilon \colon i_{!}i^{*} \Rightarrow \mathrm{id}$ are natural weak equivalences. The advantage of working with an inverse pair of left adjoints is that we can use cocontinuity and the fact that both $\Delta$ and $\square$ are Eilenberg–Zilber to reduce to checking that certain components are weak equivalences. In fact, we can treat both cases at once, by an argument we now develop.

**Lemma 6.2.15.** *Let $U, V \colon \mathsf{K} \to \mathsf{M}$ be a cocontinuous pair of functors valued in a model category and $\alpha \colon U \Rightarrow V$ a natural transformation between them. Define the cofibrations in $\mathsf{K}$ to be the maps that are sent to cofibrations under both $U$ and $V$. Define $\mathcal{N}$ to be the class of cofibrations between cofibrant objects that are sent by Leibniz pushout application with $\alpha$ to weak equivalences in $\mathsf{M}$. Then $\mathcal{N}$ is closed under coproducts, pushouts, (transfinite) composition, and right cancelation among cofibrations.*

*Proof.* The claims all follow from the proofs of [RV14, §5], except for right cancelation, which is not mentioned there. We demonstrate this together with the closure under composition, as these are the most subtle closure properties. Consider a composable pair of monomorphisms and their Leibniz applications:

![img-73.jpeg](img-73.jpeg)

The diagram reveals that $\alpha \circ hg$ factors as a pushout of $\alpha \circ g$ followed by $\alpha \circ h$. When $g \in \mathcal{N}$ and $h$ is a cofibration, our hypotheses imply that the pushout of $\alpha \circ g$ is a pushout of a weak equivalence between cofibrant objects along a cofibration, hence again a weak equivalence. Thus, by the 2-of-3 properties for weak equivalences, $h \in \mathcal{N}$ if and only if $hg \in \mathcal{N}$.

73

**Corollary 6.2.16.** *Let A be an Eilenberg–Zilber category and consider a parallel pair of functors $U, V: \mathsf{Set}^{\mathsf{A}^{\mathsf{op}}} \to \mathsf{M}$ valued in a model category M together with a natural transformation $\alpha: U \Rightarrow V$. Suppose that U and V preserve colimits and send monomorphisms in K to cofibrations in M. Then if the components of $\alpha$ at quotients of representables by subgroups of their automorphism groups are weak equivalences, then all components of $\alpha$ are weak equivalences.*

*Proof.* Note that the components of $\alpha$ at a presheaf $X$ are obtained by Leibniz application of $\alpha$ at the monomorphism $\emptyset \to X$. The result now follows by combining Lemma 6.2.13, which says that the monomorphisms in $\mathsf{Set}^{\mathsf{A}^{\mathsf{op}}}$ are generated under coproduct, pushout, transfinite composition, and right cancelation among monomorphisms by the maps $\emptyset \to \mathsf{A}_{/H}^{\mathsf{a}}$, with Lemma 6.2.15, which says that the class of monomorphisms whose Leibniz applications are weak equivalences has these closure properties. $\square$

**Corollary 6.2.17.** *Let A be an Eilenberg–Zilber category for which $\mathsf{Set}^{\mathsf{A}^{\mathsf{op}}}$ admits a model structure whose cofibrations are the monomorphisms in which the quotients $\mathsf{A}_{/H}^{\mathsf{a}}$ of representables by subgroups of their automorphism groups are weakly contractible. Then if $U, V: \mathsf{Set}^{\mathsf{A}^{\mathsf{op}}} \to \mathsf{M}$ define a pair of left Quillen functors that preserve the terminal object, then any natural transformation $\alpha: U \Rightarrow V$ is a natural weak equivalence.*

*Proof.* By Ken Brown's lemma, left Quillen functors from $\mathsf{Set}^{\mathsf{A}^{\mathsf{op}}}$ that preserve the terminal object preserve weakly contractible cofibrant objects. Now from the naturality square associated to a weakly contractible cofibrant object $X$

$$\begin{array}{ccc} UX & \xrightarrow{\alpha_X} & VX \\ \updownarrow_{\downarrow} & & \updownarrow_{\downarrow} \\ U* & = & V* \end{array}$$

and the 2-of-3 property, we see that the component $\alpha_X$ is a weak equivalence. By Corollary 6.2.16, if the components of $\alpha$ at quotients of representables are weak equivalences, then $\alpha$ is a natural weak equivalence. So the result follows. $\square$

Note that $i^*$ preserves the terminal object, as a right adjoint, as does $i_!$, since in both domain and codomain it is representable and $i[0] := [0, 1]^0$.

**Proposition 6.2.18.** *The functors*

$$\begin{array}{ccc} & \xleftarrow{i_!} & \\ \mathsf{cSet} & \xleftarrow{\quad} & \mathsf{sSet} \\ & \searrow & \searrow \\ & i^* & \end{array}$$

*are left Quillen equivalences.*

*Proof.* The unit and counit of these adjunctions each define natural transformations between left Quillen adjoints that preserve the terminal object. As the domain and codomain of these functors are categories of presheaves for Eilenberg–Zilber categories equipped with model structures for which all objects are cofibrant and quotients of representables are contractible, Corollary 6.2.17 applies to prove that both the unit and counit are natural weak equivalences. $\square$

**6.3. The equivariant model structure is the test model structure.** Finally, we show that the equivariant model structure coincides with the test model structure.

The cartesian cube category is a *strict test category* [BM17], so cartesian cubical sets admits a model structure, conjectured to exist by Grothendieck [Gro84] and established at this level of generality by Cisinski [Cis06], that presents classical homotopy theory. In Cisinski's model structure on presheaves over a test category—referred to as a **test model structure** below—the cofibrations

74

are the monomorphisms and the weak equivalences are those maps of presheaves $f: X \to Y$ such that the map of simplicial sets defined by applying the functor $N\mathsf{e}\mathsf{l}$, which takes the nerve of the category of elements, is a weak homotopy equivalence.

**Definition 6.3.1.** A category is **aspherical** if its nerve is weakly contractible in Quillen's model structure. A functor $u: \mathsf{A} \to \mathsf{B}$ between small categories is **aspherical** if the comma category $u \downarrow b$ is aspherical for every $b \in \mathsf{B}$. A presheaf over a small category is **aspherical** if its category of elements is aspherical.

Note that, by definition, a presheaf over a test category is aspherical if and only if it is weakly contractible in the test model structure.

*Remark 6.3.2* ([CS25, 7.14]). The test model structure on sSet is the Kan–Quillen model structure. In particular, a simplicial set is aspherical if and only if it is weakly contractible in the Kan–Quillen model structure.

Now we can use the machinery of aspherical functors to relate the test model structure on cSet to the Kan–Quillen model structure.

**Proposition 6.3.3** ([Cis06, 4.2.24]). *Let $u: \mathsf{A} \to \mathsf{B}$ be an aspherical functor between test categories. Then the adjunction*

![img-74.jpeg](img-74.jpeg)

defines a Quillen equivalence between test model structures.

**Proposition 6.3.4** ([Cis06, 4.2.23]). *A functor $u: \mathsf{A} \to \mathsf{B}$ between small categories is aspherical if and only if $u^*(\updownarrow b)$ is aspherical for every $b \in \mathsf{B}$.*

*Proof.* The category of elements of $u^*(\updownarrow b)$ is equivalent to the comma category $u \downarrow b$.

**Corollary 6.3.5.** *The functor $i: \Delta \to \square$ is aspherical.*

*Proof.* By Proposition 6.3.4, we want to show that $i^*I^n \in \mathsf{sSet}$ is an aspherical presheaf for each $n \in \mathsf{N}$. By Remark 6.3.2, this means showing $i^*I^n$ is contractible in the Kan–Quillen model structure. We have $i^*I^n \cong (\Delta^1)^n$ by Lemma 6.1.1, so this is indeed the case.

**Theorem 6.3.6.** *The equivariant model structure on cSet coincides with the test model structure.*

*Proof.* These two model structures have the same cofibrations, so it suffices to show they have the same weak equivalences. Recall that a left Quillen equivalence preserves and reflects weak equivalences between cofibrant objects. Thus, by Proposition 6.2.18, a map $f$ is a weak equivalence in the equivariant model structure if and only if $i^*f$ is a weak equivalence. But by Proposition 6.3.3 and Corollary 6.3.5, $f$ is also a weak equivalence in the test model structure if and only if $i^*f$ is a weak equivalence. Thus the weak equivalences of the equivariant and test model structures coincide.

# APPENDIX A. TYPE-THEORETIC DEVELOPMENT AND FORMALIZATION

A.1. **Introduction.** This appendix provides a description of the equivariant cartesian cubical set model in the language of dependent type theory. The category of presheaves on any index category models an *extensional* dependent type theory, such as the one introduced by Martin-Löf [ML79], as observed by Hofmann [Hof97, §4] and detailed by Awodey, Gambino, and Hazratpour [AGH24]. Briefly, contexts are interpreted as presheaves, and a type $A$ in context $\Gamma$ is interpreted as a map

75

$A : \Gamma \rightarrow \mathcal{V}$, where $\dot{\mathcal{V}} \rightarrow \mathcal{V}$ is a classifier for small maps of presheaves as in §2.3 above.$^{15}$ Starting from type-theoretic axioms that capture the basic structure of cartesian cubical sets (e.g. an interval object), we can construct a translation, or *internal model*, of HoTT in extensional type theory, in such a way that the usual functorial, or *external*, notions are recovered under the interpretation into presheaves, again as detailed in *op.cit.* This was the approach used in the formalization by Orton and Pitts [OP18].

The internal homotopical model interprets contexts as types of the extensional theory, while types are interpreted as type families equipped with *equivariant filling structure*. Most of the required axioms can be formulated within plain extensional type theory, augmented by the cubical axioms; however, in order to interpret (univalent) universes, we follow Licata et al. [LOPS18] in using a modal operator to refer to the set of global sections of a presheaf, an external notion that falls outside the type theory of the category of presheaves itself.

This approach has the practical advantage that uniformity conditions on filling structures need not be stated and checked explicitly, as such conditions are in effect built into the presheaf interpretation (see [AGH24, §§7–8]). It has the theoretical benefit that the results can be interpreted in models of extensional type theory other than cubical sets. For example, Uemura [Uem18] constructs a model of HoTT in cubical assemblies in this way. Finally, this approach is amenable to direct formalization in a proof assistant. Beginning from an axiomatization similar to the one in [OP18; LOPS18], all of the material presented in this appendix has been formalized in the proof assistant Agda [Agda]. The formal development can be found at [ACCRS24], and we include references to relevant definitions from the formalization in our summary below.

Variations on this kind of internal model construction have been presented in detail elsewhere [OP18; LOPS18; Uem18; BT20; CMS20; ABCHFL21], so we limit ourselves to a high level description and some points that are not stressed in those references. For the sake of concision, we start from simpler but more restrictive axioms than in the formal development; the additional generality is not principally motivated by applications, but by ease of formalization. We refer readers interested in a more parsimonious axiomatization to the documentation at [ACCRS24].

A.1.1. *Metatheory.* The metatheory can be classical set theory with Grothendieck universes, or a constructive version such as Aczel's constructive set theory with universes [Acz98]. For each Grothendieck universe in the metatheory, we have a Hofmann–Streicher universe $\mathcal{V}$ in the extensional type theory that reflects all type forming operations (as in [ML79]). The notions of fibred structure represented by these universes satisfy a relative acyclicity property (as used in §2) which can be expressed inside the type theory (*axiom.realignment*); it is called the “strictness axiom” by Orton and Pitts [OP18, Theorem 8.4] and “realignment” by Gratzer, Shulman, and Sterling [GSS22b, Definition 1.1.4].

A.1.2. *Comparison with external proofs.* Since we are working in the internal language of cubical sets, rather than cubical species, we cannot transfer constructions from the latter to the former as is done in the external development (beginning in §4). This means that we must check equivariance conditions explicitly: e.g. compare the proof of the Frobenius condition in Proposition 5.3.2 to that in Proposition A.6.4 below. It might be possible to instead work internally to cubical species and then transfer the results to cubical sets by working in a type theory with modalities based on the adjoints $L \rightarrow \Delta \rightarrow \Gamma$ of §5.1, but we leave this for future work.

A.1.3. *Quillen model structure and fibrant replacement.* We formalize and describe here only an interpretation of HoTT; we do not build an associated Quillen model structure. Boulier and Tabareau [BT20] have extended Orton and Pitts' type-theoretic model of HoTT [OP18; LOPS18]

$^{15}$Alternatively, in the style of Hofmann, a type $A$ in context $\Gamma$ is interpreted as a presheaf on the category of elements $\int \Gamma$. Small types (presheaves valued in small sets) then correspond to maps $\Gamma \rightarrow \mathcal{V}$ as above.

76

(which axiomatizes cubical sets with connections) to obtain a model structure on the category of types in the universe $\flat\!\mathcal{V}$ of global presheaves (see §A.8 below for a discussion of the $\flat$ modality). We conjecture that their work adapts to the equivariant cartesian case.

One difference is in the definition of a fibrant replacement, or more generally the factorization for the (trivial cofibration, fibration) factorization system. In our external development, this is obtained via the algebraic small object argument from a generating category transferred from an algebraic weak factorization system on cubical species (§5.2). Boulier and Tabareau derive their fibrant replacement from a postulated quotient inductive type (QIT) [ACDKF18]. In our formalization we postulate a similar QIT for (trivial cofibration, fibration) factorization (axiom.fibrant-replacement) and derive a universal property (fibration.fibrant-replacement), though we do not need this construction for the interpretation of HoTT. It is worth noting that unlike fibrant replacement in non-equivariant cubical models, equivariant fibrant replacement does not seem to be expressible as a W-type with reductions in the sense of Swan [Swa18a]. The construction of fibrant replacement as a subset of an upper approximation in Coquand, Huber, and Mörtberg's constructions of higher inductive types [CHM18] has to be replaced by a quotient by a partial equivalence relation on this upper approximation.16

A.2. Judgments of the homotopical interpretation. From here forward, we work inside an extensional type theory, which we will call the ambient theory. We will introduce the necessary axioms as we go along, but first we can set up the judgmental structure of the homotopical interpretation. A context in the homotopical model is a type of the ambient theory. A substitution between contexts is a function between types. The unit type 1 serves as the empty context. A type of the homotopical model over a context $\Gamma$ is a family over $\Gamma$ paired with an equivariant filling structure, which we will define in §A.5 below. The terms of a type over $\Gamma$ in the model are the global sections of the family $A$ underlying the type, i.e. the elements of Elem $\Gamma A := \Pi_{\gamma:\Gamma}A \gamma$.

If $A$ is a family of types over $\Gamma$, we write $\Gamma.A$ for the type $\Sigma_{\gamma:\Gamma}A \gamma$. Thus an element of $\Gamma.A$ is a pair $\gamma, a$ with $\gamma$ in $\Gamma$ and $a$ in $A \gamma$. If $A$ is the underlying family of a type in the model, then we take $\Gamma.A$ as the interpretation of the context extension of $\Gamma$ by that type.

A.3. Cubes and cofibrations. We assume as given two special types: an interval type $\mathsf{I}$ with two distinct elements $0 \neq 1$ (axiom.shape.1) and a type of cofibrations $\Phi$ (axiom.cofibration). These types are in all universes: we have $\Phi : \mathcal{V}$ and $\mathsf{I} : \mathcal{V}$. For each $n : \mathbb{N}$, the $n$-cube $\mathsf{I}^n : \mathcal{V}$ is then the cartesian product of $n$ copies of the interval. To each cofibration $\psi$ is associated a proposition $[\psi] : \mathcal{V}$, where a type $A$ is a proposition if it is a subsingleton, i.e. we have $a_0 = a_1 : A$ for any $a_0$ and $a_1$ in $A$.

We assume that $[-]$ embeds $\Phi$ as a sublattice of the lattice of propositions. In particular, for $\psi, \phi : \Phi$ we have $\psi \vee \phi : \Phi$ such that $[\psi \vee \phi]$ is the union of $[\psi]$ and $[\phi]$, and we have a true cofibration $\top : \Phi$ inhabited by some $\mathsf{tt} : [\top]$. In this summary, we assume cofibration extensionality: if $[\psi]$ and $[\phi]$ are logically equivalent then $\psi = \phi$.17 In particular, given $x : [\psi]$ we have $\psi = \top$ and thus $x = \mathsf{tt}$.

The model in cartesian cubical sets described in the main article corresponds to taking the representable 1-cube as the interval and the subobject classifier $\Omega$ as the type of cofibrations; the decoding function $[-] : \Omega \to \mathcal{V}$ is the classifying map $\top : 1 \to \Omega$ regarded as a type family over $\Omega$. If working constructively, we can instead take the classifier for levelwise decidable subobjects, those monomorphisms $m : A \mapsto B$ in cSet such that the component $m_k : A_k \mapsto B_k$ is decidable for each $k \in \mathbb{N}$.

16We note that, in the case of the cartesian model, the upper approximation can be described by a finitary inductive definition, so choice is not needed for proving the required property of this quotient.

17In the formal development, we assume cofibration extensionality only to define Swan's strict identity types [CCHM15, §9.1] (type-former.swan-identity).

77

Remark A.3.1 (axiom.shape). In the formal development, we do not work with cubes defined explicitly as products of an interval. Instead, we assume an abstract type Shape and a decoding function giving $\langle S\rangle:\mathcal{V}$ for each $S:\text{Shape}$. We require that the interval $\mathsf{I}$ is coded by a shape, but not that every shape is a power of $\mathsf{I}$, nor that $\mathsf{I}^n$ is coded by a shape for $n\neq 1$. To obtain the equivariant fibration model, we would instantiate with Shape := $\mathbb{N}$ and $\langle n\rangle := \mathsf{I}^n$. We can also recover the non-equivariant model by taking $\mathsf{I}$ to be the only shape.

A.4. Partial elements and contractible types. The notion of partial elements and contractible types play a crucial role in this internal description. Both definitions use only the type of cofibrations $\Phi$ and not the interval type $\mathsf{I}$.

Definition A.4.1 (cofibration.$_{-+}$). To each type $A$ we associate a type $A^{+} := \Sigma_{\psi:\Phi} A^{[\psi]}$ of partial elements of $A$. A partial element of $A$ is thus a pair $\psi, u$ where $u$ is in $A^{[\psi]}$. The operation $A \mapsto A^{+}$ on types is reflected in all universes and so defines a function $\mathcal{V} \to \mathcal{V}$.

There is a canonical injection $i_A: A \to A^{+}$ which to any $a: A$ associates the element $\top, u$ in $A^{+}$ with $u \, x := a$. Viewed externally, $i_A$ is the partial map classifier introduced in §2.2, taken relative to the ambient context.

Definition A.4.2 (fibration.trivial.Contr). For any type $A$, we can consider the type Contr($A$) of contractibility structures on $A$. This is the type of operations $c_A$ which take a partial element $\psi, u$ in $A^{+}$ and build an element $c_A(\psi, u)$ in $A$ such that $[\psi]$ implies $c_A(\psi, u) = u \, \text{tt}$.

Remark A.4.3. Any contractibility structure $c_A$ is a left inverse of $i_A$: we have $c_A(i_A \, a) = a$ for any $a$ in $A$. Maybe surprisingly, the converse also holds: any left inverse $c_A$ of $i_A$ is in Contr($A$), because if $c_A$ is a left inverse of $i_A$ then for any $\psi, u$ in $A^{+}$ we have that $[\psi]$ implies $(\psi, u) = i_A(u \, \text{tt})$ and thus $c_A(\psi, u) = c_A(i_A(u \, \text{tt})) = u \, \text{tt}$.

Definition A.4.4 (fibration.trivial.TFibStr). A trivial fibration structure on a family of types $A$ over $\Gamma$ then consists of a family of contractibility structures on $A \, \gamma$ for each $\gamma: \Gamma$.

Viewed externally, such a family corresponds to a uniform trivial fibration structure in the sense of Definition 2.2.9.

A.5. Filling and equivariant filling. Next we finish defining the interpretation of types by defining equivariant filling structures. We first generalize the definition of fibration used by Angiuli et al. [ABCHFL21], replacing the interval by an arbitrary type.

Definition A.5.1 (fibration.fibration.LocalFillStr). Let $S$ be a type and $A$ be a family of types over $S$; we define the type LocalFill$_S$ $A$ of local $S$-filling structures on $A$. These are operations $c_A$ which take as argument $r_0: S$ and $a_0: A \, r_0$ and a partial section $\psi, u: (\Pi_{r:S} A \, r)^{+}$ compatible with $a_0$, i.e. such that $[\psi]$ implies $u \, \text{tt} \, r_0 = a_0$, and produce an element $c_A \, r_0 \, a_0 \, (\psi, u)$ in $\Pi_{r:S} A \, r$ which extends $\psi, u$ and such that $c_A \, r_0 \, a_0 \, (\psi, u) \, r_0 = a_0$.

Definition A.5.2 (fibration.fibration.FillStr). Let $S$ be a type and $A$ be a family of types over $\Gamma$. An $S$-filling structure $c_A$ on $A$ consists of a local $S$-filling structure $c_A \, \gamma: \text{LocalFill}_S \, (A \circ \gamma)$ for every $\gamma: \Gamma^S$. We write Fill$_S$ $A$ for the type of $S$-filling structures on $A$.

In the cartesian cubical set model of Angiuli et al. [ABCHFL21], a type is a family paired with an $\mathsf{I}$-filling structure. To define equivariant filling structures, we use the case where $S = \mathsf{I}^n$ for some $n: \mathbb{N}$. In this case the symmetric group $\Sigma_n$ acts in a canonical way on $S$. It then acts on $\Gamma^S$ by precomposition, with $\gamma \sigma := \gamma \circ \sigma$ for $\gamma: \Gamma^S$ and $\sigma: \Sigma_n$. We likewise have an action on partial elements: given $(\psi, u): (\Pi_{r:S} A \, r)^{+}$ define $(\psi, u) \sigma: (\Pi_{r:S} A \, (\sigma \, r))^{+}$ by $(\psi, u) \sigma := (\psi, u')$ where $u' \, x \, r := u \, x \, (\sigma \, r)$ for $x: [\psi]$ and $r: S$.

78

**Definition A.5.3** (fibration.fibration.FibStr). An *equivariant filling structure* on a family of types $A$ over $\Gamma$ is a family of operations $c_A^n$ in $\mathsf{Fill}_{\mathbb{P}^n} \Gamma A$ for $n : \mathbb{N}$ each of which is *equivariant*, meaning that for any $\sigma$ in $\Sigma_n$, we have the *equivariance equation*

$$c_A^n \gamma (\sigma r_0) a_0 a (\sigma r_1) = c_A^n (\gamma \sigma) r_0 a_0 (a \sigma) r_1 \tag{A.5.4}$$

for every $\gamma : \Gamma^S$, $r_0 : S$, $a_0 : A (\sigma (\gamma r_0))$, compatible partial section $a : (\Pi_{r:S} A (\gamma r))^+$, and $r_1 : S$.

We write $\mathsf{Fill} \Gamma A$ for the type of all equivariant filling structures on $A$. These types of structure are reflected in each universe, so we have e.g. $\mathsf{Fill} : \Pi_{\Gamma:\mathcal{V}} (\Gamma \to \mathcal{V}) \to \mathcal{V}$.

**Definition A.5.5** (fibration.fibration. $\vdash^{\mathsf{F}}\mathsf{Type}_-$). An *equivariant fibration* over $\Gamma$ is a family of types $A$ over $\Gamma$ paired with an equivariant filling structure.

In this setting, building the model of HoTT consists in showing that each operator on types lifts to an operator on equivariant filling structures, checking in each case that the output structure satisfies the equivariance equation (A.5.4). Let us check for instance that we can interpret substitution in types; the corresponding property in the external development is the stability of equivariant fibration structures under pullback.

**Definition A.5.6** (fibration.fibration. $\circ^{\mathsf{FS}}$). Let $A$ be a family of types over $\Gamma$ and let $\alpha : \Delta \to \Gamma$. Given $c_A$ in $\mathsf{Fill} \Gamma A$, we define $c_A \circ \alpha$ in $\mathsf{Fill} \Delta (A \circ \alpha)$ by

$$(c_A \circ \alpha)^n \gamma r_0 a_0 a r_1 := c_A^n (\alpha \circ \gamma) r_0 a_0 a r_1$$

and it is then clear that $c_A \circ \alpha$ is equivariant if $c_A$ is equivariant.

**A.6. The Frobenius condition.** Proving the Frobenius condition, Definition 3.4.1, amounts to defining the interpretation of $\Pi$-types. The corresponding result in the external, equivariant development is Proposition 5.3.2. A more detailed comparison between external and type-theoretic proofs of the Frobenius condition can be found in [HR24, Appendix B].

**Definition A.6.1.** Given a type family $A$ over $\Gamma$ and a type family $B$ over $\Gamma.A$, write $\Pi_A B$ for the family of types over $\Gamma$ defined by

$$(\Pi_A B) \gamma := \Pi_{a:A\gamma} B(\gamma, a).$$

To prove the Frobenius condition in this setting is to show that, given filling structures on $A$ and $B$, we have a filling structure on $\Pi_A B$. In fact the hypothesis of a filling structure on $A$ can be weakened: we only need a *transport structure* in the following sense.

**Definition A.6.2** (fibration.transport.TranspStr). Given a type $S$ and family of types $A$ over $\Gamma$, the type $\mathsf{Transp}_S \Gamma A$ of $S$-*transport structures* on $A$ is the type of operations $t_A$ which take $r_0 : S$ and $a_0 : A (\gamma r_0)$ and produce an element $t_A \gamma r_0 a_0$ in $\Pi_{r:S} A (\gamma r)$ such that $t_A \gamma r_0 a_0 r_0 = a_0$.

An *equivariant transport structure* on $A$ is a family of operations $t_A^n : \mathsf{Transp}_n \Gamma A$ for $n : \mathbb{N}$ each of which satisfies the equivariance equation

$$t_A^n \gamma (\sigma r_0) a_0 (\sigma r_1) = t_A^n (\gamma \sigma) r_0 a_0 r_1$$

for every $\gamma : \Gamma^S$, $r_0 : S$, $a_0 : A (\sigma (\gamma r_0))$, and $r_1 : S$. We write $\mathsf{Transp} \Gamma A$ for the type of equivariant transport structures on $A$.

*Remark A.6.3* (fibration.transport.transpAndFiberwiseToFibStr). It is immediate that any (equivariant) filling structure on a type induces an (equivariant) transport structure by restricting to the partial section whose cofibration is $\bot$. As in [ABCHFL21], one can conversely construct an equivariant filling structure on $A$ given an equivariant transport structure on $A$ and an equivariant filling structure on the constant family $A \gamma$ for every $\gamma : \Gamma$. This decomposition would be the key to interpreting higher inductive types following [CHM18; CH19], but we do not pursue this here.

79

**Proposition A.6.4** (Frobenius, `type-former.pi.IIFibStr`). Given a family of types $A$ over $\Gamma$ and $B$ over $\Gamma.A$, we have an operation

$$\text{Transp } \Gamma \ A \to \text{Fill } (\Gamma.A) \ B \to \text{Fill } \Gamma \ (\Pi_A B).$$

*Proof.* Let us write $T$ for $\Pi_A B$. Given $t_A$ in $\text{Transp } \Gamma \ A$ and $c_B$ in $\text{Fill } (\Gamma.A) \ B$, we define $c_T$ in $\text{Fill } \Gamma \ T$ by

$$c_T^n \ \gamma \ r_0 \ f_0 \ (\psi, f) \ r_1 \ a_1 := c_B^n \ \langle \gamma, \tilde{a} \rangle \ r_0 \ b_0 \ (\psi, b) \ r_1 \tag{A.6.5}$$

where

$$\begin{array}{rcl} \tilde{a} & := & t_A^n \ \gamma \ r_1 \ a_1 \quad \text{in} \quad \Pi_{r:S} A \ (\gamma \ r) \\ \langle \gamma, \tilde{a} \rangle \ r & := & (\gamma \ r, \tilde{a} \ r) \quad \text{in} \quad (\Gamma.A)^S \\ b \ x \ r & := & f \ x \ r \ (\tilde{a} \ r) \quad \text{in} \quad (\Pi_{r:S} B (\gamma \ r, \tilde{a} \ r))^{[\psi]} \\ b_0 & := & f_0 \ (\tilde{a} \ r_0) \quad \text{in} \quad B \ (\gamma \ r_0, \tilde{a} \ r_0). \end{array}$$

So far this is only a slight generalization of [ABCHFL21], having replaced $\mathsf{I}$ by $S = \mathsf{I}^n$.

It remains to check the equivariance equation (A.5.4) for the operation $c_T$, assuming that the operations $t_A$ and $c_B$ are equivariant. Let $\sigma$ be an element of $\Sigma_n$. Write $\tilde{a}, b, b_0$ for the auxiliary definitions associated to $c_T^n \ \gamma \ (\sigma \ r_0) \ t_0 \ (\psi, t) \ (\sigma \ r_1)$ and $\tilde{a}', b', b'_0$ for those associated to $c_T^n \ \gamma \sigma \ r_0 \ f_0 \ (\psi, f) \sigma \ r_1$. Then we have

$$c_T^n \ \gamma \ (\sigma \ r_0) \ t_0 \ (\psi, t) \ (\sigma \ r_1) \ a_1 := c_B^n \ \langle \gamma, \tilde{a} \rangle \ (\sigma \ r_0) \ b_0 \ (\psi, b) \ (\sigma \ r_1)$$

$$(\text{equivariance of } c_B) = c_B^n \ \langle \gamma, \tilde{a} \rangle \sigma \ r_0 \ b_0 \ (\psi, b) \sigma \ r_1$$

$$(\text{equivariance of } t_A) = c_B^n \ \langle \gamma \sigma, \tilde{a}' \rangle \ r_0 \ b'_0 \ (\psi, b') \ r_1$$

$$=: c_T^n \ \gamma \sigma \ r_0 \ f_0 \ (\psi, f) \sigma \ r_1 \ a_1$$

where we use equivariance of $t_A$ to see that $\tilde{a} \ (\sigma \ r) = t_A \ \gamma \ (\sigma \ r_1) \ a_1 \ (\sigma \ r) = t_A \ \gamma \sigma \ r_1 \ a_1 \ r = \tilde{a}' \ r. \quad \square$

The core of the argument for Frobenius in this type-theoretic setting is thus the defining equation (A.6.5).

*Remark A.6.6.* To interpret the law $(\Pi_A B)[\rho] = \Pi_{A[\rho]} B[\rho.A]$ for computing a substitution applied to a $\Pi$-type, it is also necessary to check that the operation defined in Proposition A.6.4 commutes with reindexing along any $\rho : \Delta \to \Gamma$; see `type-former.pi.reindexIIFibStr` in the formalization.

**A.7. Other type formers.** We can follow the pattern of the proof of Proposition A.6.4 to lift the other type-theoretic operations to filling structures: take the corresponding definition of Angiuli et al. [ABCHFL21], replace $\mathsf{I}$ by $S = \mathsf{I}^n$, and check the equivariance equation.

For instance (`type-former.sigma`), we define the $\Sigma$-type $\Sigma_A B$ of families $A$ over $\Gamma$ and $B$ over $\Gamma.A$ by $(\Sigma_A B)\gamma = \Sigma_{a:A\gamma} B(\gamma, a)$ and build an element of type

$$\text{Fill } \Gamma \ A \to \text{Fill } (\Gamma.A) \ B \to \text{Fill } \Gamma \ (\Sigma_A B).$$

This corresponds to the closure of fibrations under composition in the external development.

To interpret identity types, we first define path types (`type-former.path`) as an instance of extension types (`type-former.extension`) à la Riehl and Shulman [RS17]. Extension types correspond externally to the closure of fibrations under Leibniz exponentiation by cofibrations (Proposition 5.2.8). Path types suffice to interpret identity types with a propositional computational rule for the eliminator. To interpret identity types with a judgmental computation rule, we can apply a modification due to Swan to path types [CCHM15, §9.1] (`type-former.swan-identity`).

We establish fibrancy and univalence of universes using the Glue types introduced in [CCHM15, §6] and adapted to cartesian cubical type theory in [ABCHFL21, §2.11] (`type-former.glue`). Preliminary WeakGlue types correspond to the equivalence extension property for the equivariant premodel structure proven in Proposition 5.3.1. The Glue types and associated properties (`universe.univalence`) correspond to univalence of the universe of equivariantly fibrant types

80

proven in Proposition 5.3.8. Mirroring the forward direction of Proposition 3.5.5, this uses realignment for the universe of equivariantly fibrant types (fibration.realignment), which is deduced from realignment for the universe of the extensional type theory (axiom.realignment) and relative acyclicity of equivariant filling structures (fibration.realignment.realignFibStr); compare Proposition 2.3.5.

A.8. Tiny interval and universes. To interpret (univalent) universes, we follow Licata, Orton, Pitts, and Spitters [LOPS18] and work in an extension of extensional type theory by a modal type operator $\flat$. For the purposes of this summary, it suffices to understand the motivating semantics in cubical sets: if $A$ is a presheaf, then $\flat A$ is the constant presheaf of global sections of $A$. We refer to the documentation of the formalization for a precise description of this setting. We will sometimes refer to an element of $\flat A$ as a “global element of $A$”. In particular, we read $\flat \mathcal{V}$ as the type of external small presheaves. We leave the inclusion $\flat A \to A$ implicit in the following.

The use of this modality is to express internally that the interval is tiny, i.e. that exponentiation by the interval $(-)^\upharpoonright$ has a right adjoint root functor $\sqrt[-]{\upharpoonright}$ on (external) presheaves, as used in the proof of Lemma 4.2.7. Specifically, we require as an axiom a functorial operator $\sqrt[-]{\upharpoonright} : \flat \mathcal{V} \to \flat \mathcal{V}$ and an isomorphism

$$\flat(A^\upharpoonright \to B) \cong \flat(A \to \sqrt[\upharpoonright]{B})$$

natural in $A, B : \flat \mathcal{V}$, exhibiting $\sqrt[-]{\upharpoonright$ as right adjoint to exponentiation $(-)^\upharpoonright$ (axiom.tiny). The restriction to global types is necessary for this axiom to be consistent [LOPS18, Theorem 5.1]. By iterating, we also have a right adjoint $\sqrt[\upharpoonright]{}: \flat \mathcal{V} \to \flat \mathcal{V}$ to exponentiation by each cube $S = \upharpoonright^n$.

A.8.1. Dependent right adjoints (tiny.dependent). To construct the universe, it is useful to observe that each right adjoint $\sqrt[\upharpoonright]{}$ induces a dependent right adjoint (spelled out in [CHS19, Lemma 2.2]; see also Birkedal et al. [BCMMPS20] and [LOPS18, §5]). Note the appearance of similar structure in Lemma 2.1.16 of the external development, which is likewise used to construct universes.

Briefly, for each $\Gamma : \flat \mathcal{V}$ and global type family $B : \flat(\Gamma^S \to \mathcal{V})$ we have a family $\sqrt[\upharpoonright]{B}$ over $\Gamma$ and an isomorphism between dependent function types

$$\mathsf{shut}_S : \flat(\mathsf{Elem} \ \Gamma^S \ B) \cong \flat(\mathsf{Elem} \ \Gamma \ \sqrt[\upharpoonright]{B}) : \mathsf{open}_S$$

which is natural in $\Gamma$ and $B$ in an appropriate sense.

Remark A.8.1. Riley [Ril24] describes a type theory with a primitive dependent right adjoint of this kind and shows that this structure suffices to carry out the [LOPS18] universe construction without relying on a $\flat$ modality [Ril24, §5]. We use the same style of argument below; although our dependent right adjoint is not primitive, it remains a convenient abstraction, especially in the equivariant case where the universe construction is more involved than in [LOPS18].

A.8.2. Universe of non-equivariant fibrations. We now transpose the family $\mathsf{LocalFill}_S : \flat(\mathcal{V}^S \to \mathcal{V})$ from Definition A.5.1 to obtain $\sqrt[\upharpoonright]{\mathsf{LocalFill}_S}$ over $\mathcal{V}$ with the property that for any global family $A : \flat(\Gamma \to \mathcal{V})$ we have

$$\flat(\mathsf{Elem} \ \Gamma \ (\ \sqrt[\upharpoonright]{\mathsf{LocalFill}_S} \circ A)) \cong \flat(\mathsf{Elem} \ \Gamma^S \ (\mathsf{LocalFill}_S \circ A^S)) = \flat(\mathsf{Fill}_S \ A). \tag{A.8.2}$$

Definition A.8.3. Define $\mathcal{U}_S := \Sigma_{A:\mathcal{V}} \sqrt[\upharpoonright]{\mathsf{LocalFill}_S} \ A$.

From (A.8.2), we have an isomorphism for $\Gamma : \flat \mathcal{V}$ between global families $\Gamma \to \mathcal{U}_S$ and global $\mathcal{V}$-small families over $\Gamma$ paired with $S$-filling structures. Note that the type $\mathcal{U}_\upharpoonright$ is exactly the universe defined in [LOPS18].

Definition A.8.4. Leaving the first projection $\pi_1 : \mathcal{U}_S \to \mathcal{V}$ implicit, we transpose the projection $\pi_2 : \Pi_{A:\mathcal{U}_S} \sqrt[\upharpoonright]{\mathsf{LocalFill}_S} \ A$ to yield a map $\mathsf{open}_S \ \pi_2 : \Pi_{A:(\mathcal{U}_S)^S} \mathsf{LocalFill}_S \ A$ that associates a local filling structure to every $S$-cell in the universe.

81

A.8.3. Universe of equivariant fibrations. To further restrict to universes of equivariant fibrations, we introduce a another predicate on elements of $\mathcal{U}_S$.

Definition A.8.5 (universe.core.LocalEquivariance$\sqrt{}$). Fix $S = \mathsf{I}^n$ and let $A : (\mathcal{U}_S)^S$. Per Definition A.8.4, we have $\mathsf{open}_S \pi_2 A : \mathsf{LocalFill}_S A$. For each $\sigma$ in $\Sigma_n$, we also have $\mathsf{open}_S \pi_2 (A\sigma) : \mathsf{LocalFill}_S (A\sigma)$. We say $A$ is equivariant when for each $\sigma$ in $\Sigma_n$, we have

$$\mathsf{open}_S \pi_2 A (\sigma r_0) a_0 a (\sigma r_1) = \mathsf{open}_S \pi_2 (A\sigma) r_0 a_0 (a\sigma) r_1$$

for all $r_0 : S$, $a_0 : A (\sigma r_0)$, partial sections $a : (\Pi_{r:S} A r)^+$ compatible with $a_0$, and $r_1 : S$.

We write $\mathsf{Equivariant}_S A$ for the type of proofs that $A$ is equivariant.

Definition A.8.6 (universe.core.$\mathcal{U}$). Given $A : \mathcal{V}$, we define the type of equivariant fibration structures on $A$ by

$$\mathsf{Fib} A := \prod_{n:\mathbb{N}} \sum_{F: \sqrt[n]{\mathsf{LocalFill}_n} A} \prod_{\sigma:\Sigma_n} \sqrt[n]{\mathsf{Equivariant}_n} (A, F).$$

The universe of equivariant fibrations is then $\mathcal{U} := \sum_{A:\mathcal{V}} \mathsf{Fib} A$.

Proposition A.8.7 (universe.core). We have for each $\Gamma : \flat\mathcal{V}$ an isomorphism

$$\flat(\mathsf{Elem} \Gamma (\mathsf{Fib} \circ A)) \cong \flat(\mathsf{Fill} \Gamma A) \tag{A.8.8}$$

and therefore an isomorphism between global families $\Gamma \to \mathcal{U}$ and global $\mathcal{V}$-small equivariant fibrations over $\Gamma$.

The existence of such a predicate $\mathsf{Fib}$ corresponds to the local representability of equivariant fibrations (Lemma 5.3.3): for a family $A$ over $\Gamma$, the family $\mathsf{Fib} \circ A$ over $\Gamma$ corresponds to the representing morphism $\psi_\pi$ for the projection $\pi: \Gamma.A \to \Gamma$. In the external development, local representability of equivariant fibrations is derived from local representability of fibrations in cubical species (Lemma 4.4.3), which uses the tininess of the symmetric interval (Lemma 4.2.7) and thus, like the construction here, ultimately depends on the tininess of the cubes $\mathsf{I}^n$.

A.8.4. Fibrancy of the universe (universe.fibrant). As with the other type formers, we construct a fibrancy structure on the universe by generalizing the definition of Angiuli et al. [ABCHFL21, §2.12] from $\mathsf{I}$ to $\mathsf{I}^n$ and checking that this satisfies the equivariance equation. The construction relies on the Glue types mentioned in Section A.7. The corresponding argument in the external development is in 3.6, based on the same definition of Angiuli et al.; there it is conducted in cubical species and then transferred to cubical sets in Proposition 5.3.10.

When we have a larger universe $\mathcal{V}_1$ with $\mathcal{V} : \mathcal{V}_1$, we can repeat the definitions above to define a predicate $\mathsf{Fib}_1$ and universe of $\mathcal{V}_1$-small fibrations $\mathcal{U}_1 := \sum_{A:\mathcal{V}} \mathsf{Fib}_1 A$; the fibrancy of $\mathcal{V}$ then implies that $\mathcal{U}_1$ contains a code for $\mathcal{U}$. More generally, a hierarchy of universes $\mathcal{V}_n$ in the extensional type theory gives rise to a corresponding hierarchy of universes $\mathcal{U}_n$ in the homotopical interpretation.

A.8.5. Type formers (universe.type-former). Using the closure properties of the operation $\mathsf{Fill}$ established in Sections A.6 and A.7 and the bijection (A.8.8), we can build operations of types

$$\begin{array}{l} \Pi_{A:\mathcal{V}}\Pi_{B:A\to\mathcal{V}}\mathsf{Fib} A \to (\Pi_{a:A}\mathsf{Fib} (B a)) \to \mathsf{Fib} (\Pi_{A}B) \\ \Pi_{A:\mathcal{V}}\Pi_{B:A\to\mathcal{V}}\mathsf{Fib} A \to (\Pi_{a:A}\mathsf{Fib} (B a)) \to \mathsf{Fib} (\Sigma_{A}B) \\ \Pi_{A:\mathcal{V}}\Pi_{a_0:A}\Pi_{a_1:A}\mathsf{Fib} A \to \mathsf{Fib} (\mathsf{Path} A a_0 a_1). \end{array} \tag{A.8.9}$$

From these, we deduce that $\mathcal{U}$ is closed under $\Pi$-types, $\Sigma$-types, and $\mathsf{Path}$-types. We also have an alternative, isomorphic definition of the judgments of the homotopical interpretation: we can interpret types over $\Gamma$ as maps $\Gamma \to \mathcal{U}$ rather than as families over $\Gamma$ with equivariant filling structures. Because the type formers can then be defined pointwise by the operators shown in (A.8.9), the laws for computing substitutions such as mentioned in Remark A.6.6 become automatic;

82

this is the same technique exploited by Voevodsky to solve the coherence problem in the simplicial model [KL21].

A.8.6. Univalence (universe.univalence). Finally, the closure of the universe under Glue-types provides an element of

\[
\Pi_ {A: \mathcal {U}} \text { Contr } (\Sigma_ {X: \mathcal {U}} \text { Equiv   } A X)
\]

where Equiv A X is the type of homotopy equivalences and Contr is the type of contractibility structures from Section A.4. This corresponds to the equivalence extension property for V-small fibrations. Any family with a trivial fibration structure is contractible as a type in the homotopical interpretation, in the sense of [UF13, §3.11] (type-former.hlevels.TFibToIsContr). Thus the homotopical interpretation satisfies the axiom

\[
\Pi_ {A: \mathcal {U}} \text { isContr } (\Sigma_ {X: \mathcal {U}} \text { Equiv   } A X)
\]

where isContr  \( A := \Sigma_{a_{0}:A} \Pi_{a:A} (\text{Path } A a_{0} a) \) . This is an equivalent formulation of the univalence axiom (as observed by Escardó [Esc14]); compare the derivation of univalence from the equivalence extension property and Frobenius condition at the start of Section 3.5.

REFERENCES

|  [ABCHFL21] | Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Robert Harper, Kuen-Bang Hou (Favonia), and Daniel R. Licata. “Syntax and models of Cartesian cubical type theory”. In:Mathematical Structures in Computer Science 31.4 (2021), pp. 424–468. DOI: 10.1017/S0960129521000347 (cit. on pp. 3, 4, 7, 8, 10, 11, 32, 37, 76, 78–80, 82).  |
| --- | --- |
|  [ACCRS24] | Steve Awodey, Evan Cavallo, Thierry Coquand, Emily Riehl, and Christian Sattler. Formalization of an equivariant cartesian cubical set model of type theory. HTML:https://ecavallo.github.io/equivariant-cartesian, SOURCE:https://github.com/ecavallo/equivariant-cartesian. 2024 (cit. on pp. 9, 76).  |
|  [ACDKF18] | Thorsten Altenkirch, Paolo Capriotti, Gabe Dijkstra, Nicolai Kraus, and Fredrik Nordvall Forsberg. “Quotient Inductive-Inductive Types”. In:Foundations of Software Science and Computation Structures, FOSSACS 2018. Ed. by Christel Baier and Ugo Dal Lago. Vol. 10803. Lecture Notes in Computer Science. Springer, 2018, pp. 293–310. DOI: 10.1007/978-3-319-89366-2_16. URL:https://doi.org/10.1007/978-3-319-89366-2_16 (cit. on p. 77).  |
|  [Acz98] | Peter Aczel. “On Relating Type Theories and Set Theories”. In:Types for Proofs and Programs. Ed. by T. Altenkirch, B. Reus, and W. Naraschewski. Springer. 1998, pp. 33–46. DOI: 10.1007/3-540-48167-2_1 (cit. on p. 76).  |
|  [AFH18] | Carlo Angiuli, Kuen-Bang Hou (Favonia), and Robert Harper. “Cartesian Cubical Computational Type Theory: Constructive Reasoning with Paths and Equalities”. In:27th EACSL Annual Conference on Computer Science Logic, CSL 2018, September 4-7, 2018, Birmingham, UK. 2018, 6:1–6:17. DOI: 10.4230/LIPIcs.CSL.2018.6 (cit. on pp. 3, 11).  |
|  [Agda] | The Agda Team. Agda. Version 2.6.4. URL:https://agda.readthedocs.io/en/v2.6.4/index.html (cit. on p. 76).  |
|  [AGH24] | Steve Awodey, Nicola Gambino, and Sina Hazratpour. “Kripke-Joyal forcing for type theory and uniform fibrations”. In:Selecta Mathematica 30.4 (2024). DOI: 10.1007/s00029-024-00962-2 (cit. on pp. 75, 76).  |
|  [AW09] | Steve Awodey and Michael A. Warren. “Homotopy theoretic models of identity types”. In:Mathematical Proceedings of the Cambridge Philosophical Society 146.1 (2009), pp. 45–55. DOI: 10.1017/S0305004108001783 (cit. on pp. 2, 7).  |
|  [Awo18a] | Steve Awodey. “A cubical model of homotopy type theory”. In:Annals of Pure and Applied Logic 169.12 (2018). Logic Colloquium 2015, pp. 1270–1294. DOI: 10.1016/j.apal.2018.08.002 (cit. on p. 3).  |
|  [Awo18b] | Steve Awodey. “Natural models of homotopy type theory”. In:Mathematical Structures in Computer Science 28.2 (2018), pp. 241–286. DOI: 10.1017/S0960129516000268 (cit. on pp. 3, 7).  |
|  [Awo24] | Steve Awodey. “On Hofmann–Streicher universes”. In:Mathematical Structures in Computer Science 34.9 (2024), 894–910. DOI: 10.1017/S0960129524000203 (cit. on pp. 23, 59, 60).  |
|  [Awo26] | Steve Awodey. Cartesian cubical model categories. Vol. 2385. Lecture Notes in Mathematics. Springer, 2026. DOI: 10.1007/978-3-032-08730-0 (cit. on pp. 3–5, 7, 8, 10, 18–20, 32).  |

83

[Bar19] Reid William Barton. “A model 2-category of enriched combinatorial premodel categories”. PhD thesis. Harvard University, 2019. arXiv: 2004.12937 [math.CT] (cit. on pp. 4, 25).
[Bar24a] Reid Barton. “A short proof of Frobenius for generic fibrations”. 2024. arXiv: 2402.04227 [math.CT] (cit. on p. 32).
[Bar24b] Reid Barton. “Triangulation of cartesian cubical sets”. in preparation. 2024 (cit. on p. 61).
[BC15] Marc Bezem and Thierry Coquand. “A Kripke model for simplicial sets”. In: *Theor. Comput. Sci.* 574 (2015), pp. 86–91. DOI: 10.1016/j.tcs.2015.01.035 (cit. on pp. 2, 10).
[BCH14] Marc Bezem, Thierry Coquand, and Simon Huber. “A Model of Type Theory in Cubical Sets”. In: *19th International Conference on Types for Proofs and Programs, TYPES 2013, April 22-26, 2013, Toulouse, France*. 2014, pp. 107–128. DOI: 10.4230/LIPICS.TYPES.2013.107 (cit. on p. 3).
[BCH19] Marc Bezem, Thierry Coquand, and Simon Huber. “The Univalence Axiom in Cubical Sets”. In: *Journal of Automated Reasoning* 63 (2019), pp. 159–171. DOI: 10.1007/s10817-018-9472-6 (cit. on p. 3).
[BCMPS20] Lars Birkedal, Ranald Clouston, Bassel Manna, Rasmus Ejlers Møgelberg, Andrew M. Pitts, and Bas Spitters. “Modal dependent type theory and dependent right adjoints”. In: *Mathematical Structures in Computer Science* 30.2 (2020), pp. 118–138. DOI: 10.1017/S0960129519000197 (cit. on p. 81).
[BCP15] Marc Bezem, Thierry Coquand, and Erik Parmann. “Non-Constructivity in Kan Simplicial Sets”. In: *13th International Conference on Typed Lambda Calculi and Applications, TLCA 2015, July 1-3, 2015, Warsaw, Poland*. Ed. by Thorsten Altenkirch. Vol. 38. LIPICS. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2015, pp. 92–106. DOI: 10.4230/LIPICS.TLCA.2015.92 (cit. on pp. 2, 10).
[BF22] Benno van den Berg and Eric Faber. *Effective Kan Fibrations in Simplicial Sets*. Lecture Notes in Mathematics. Springer, 2022. DOI: 10.1007/978-3-031-18900-5 (cit. on p. 11).
[BG12] Benno van den Berg and Richard Garner. “Topological and Simplicial Models of Identity Types”. In: *ACM Trans. Comput. Log.* 13.1 (2012), 3:1–3:44. DOI: 10.1145/2071368.2071371 (cit. on pp. 2, 4, 7).
[BG16] John Bourke and Richard Garner. “Algebraic weak factorisation systems I: Accessible AWFS”. In: *Journal of Pure and Applied Algebra* 220.1 (2016), pp. 108–147. ISSN: 0022-4049. DOI: 10.1016/j.jpaa.2015.06.002 (cit. on pp. 22, 49).
[BM11] Clemens Berger and Ieke Moerdijk. “On an extension of the notion of Reedy category”. In: *Mathematische Zeitschrift* 269 (3 2011), pp. 977–1004. DOI: 10.1007/s00209-010-0770-x (cit. on pp. 61, 69–71).
[BM17] Ulrik Buchholtz and Edward Morehouse. “Varieties of Cubical Sets”. In: *Relational and Algebraic Methods in Computer Science, RAMICS 2017*. 2017, pp. 77–92. DOI: 10.1007/978-3-319-57418-9_5 (cit. on pp. 3, 4, 43, 74).
[Bro73] Kenneth Brown. “Abstract Homotopy Theory and Generalized Sheaf Cohomology”. In: *Transactions of the American Mathematical Society* 186 (1973), pp. 419–458. DOI: 10.1090/S0002-9947-1973-0341469-9 (cit. on p. 28).
[BT20] Simon Boulier and Nicolas Tabareau. “Model structure on the universe of all types in interval type theory”. In: *Mathematical Structures in Computer Science* (Oct. 2020), pp. 1–32. DOI: 10.1017/S0960129520000213 (cit. on p. 76).
[Cam23] Timothy Campion. *Cubical sites as Eilenberg-Zilber categories*. 2023. arXiv: 2303.06206 [math.CT] (cit. on pp. 10, 69).
[CCHM15] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. “Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom”. In: *21st International Conference on Types for Proofs and Programs, TYPES 2015*. 2015, 5:1–5:34. DOI: 10.4230/LIPICS.TYPES.2015.5 (cit. on pp. 3, 4, 9, 11, 32, 61, 77, 80).
[CH19] Evan Cavallo and Robert Harper. “Higher inductive types in cubical computational type theory”. In: *Proc. ACM Program. Lang.* 3.POPL (2019), 1:1–1:27. DOI: 10.1145/3290314 (cit. on p. 79).
[CHM18] Thierry Coquand, Simon Huber, and Anders Mörtberg. “On Higher Inductive Types in Cubical Type Theory”. In: *Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science*. LICS ’18. ACM, 2018, pp. 255–264. DOI: 10.1145/3209108.3209197 (cit. on pp. 3, 77, 79).
[CHS19] Thierry Coquand, Simon Huber, and Christian Sattler. “Homotopy Canonicity for Cubical Type Theory”. In: *4th International Conference on Formal Structures for Computation and Deduction, FSCD 2019*. Ed. by Herman Geuvers. Vol. 131. LIPICS. Schloss Dagstuhl, 2019, 11:1–11:23. DOI: 10.4230/LIPICS.FSCD.2019.11 (cit. on p. 81).
[Cis06] Denis-Charles Cisinski. *Les préfaçceaux comme modèles des types d’homotopie*. Astérisque 308. Société mathématique de France, 2006 (cit. on pp. 3, 4, 74, 75).

84

[Cis14] Denis-Charles Cisinski. *Univalent universes for elegant models of homotopy types*. 2014. arXiv: 1406.0058 [math.AT] (cit. on p. 23).
[CMS20] Evan Cavallo, Anders Mörtberg, and Andrew W. Swan. “Unifying Cubical Models of Univalent Type Theory”. In: *28th EACSL Annual Conference on Computer Science Logic, CSL 2020*. Vol. 152. LIPIcs. Schloss Dagstuhl, 2020. 14:1–14:17. DOI: 10.4230/LIPIcs.CSL.2020.14 (cit. on pp. 3, 5, 7, 8, 10, 76).
[Coq14] Thierry Coquand. *Variation on Cubical sets (diagonals version)*. Unpublished note. 2014. URL: http://www.cse.chalmers.se/~coquand/diag.pdf (cit. on p. 3).
[Coq18] Thierry Coquand. “Trivial cofibration-fibration factorization with one application”. Unpublished note. June 2018. URL: https://groups.google.com/g/homotopytypetheory/c/RQkLWZ_83kQ/m/tAyb3zYTBQAJ (cit. on p. 6).
[Coq+18] Thierry Coquand et al. “Quillen model structure”. Mailing list discussion. June 2018. URL: https://groups.google.com/g/homotopytypetheory/c/RQkLWZ_83kQ (cit. on p. 4).
[CS25] Evan Cavallo and Christian Sattler. “Relative elegance and Cartesian cubes with one connection”. In: *Canadian Journal of Mathematics* (2025), pp. 1–64. DOI: 10.4153/S0008414X25101466 (cit. on pp. 8, 10, 24, 26, 27, 41, 65, 75).
[Dyb96] Peter Dybjer. “Internal type theory”. In: *Types for Proofs and Programs*. Ed. by Stefano Berardi and Mario Coppo. Springer Berlin Heidelberg, 1996, pp. 120–134. DOI: 10.1007/3-540-61780-9_66 (cit. on p. 3).
[Esc14] Martín Escardó. “Contractible sums”. Mailing list post. Aug. 2014. URL: https://groups.google.com/g/homotopytypetheory/c/HfCB_b-PNEU/m/Ibb48LvUMeUJ (cit. on p. 83).
[Gar09] Richard Garner. “Understanding the small object argument”. In: *Applied Categorical Structures* 17 (2009), pp. 247–285. DOI: 10.1007/s10485-008-9137-4 (cit. on pp. 5, 22, 48).
[GH22] Nicola Gambino and Simon Henry. “Towards a constructive simplicial model of Univalent Foundations”. In: *Journal of the London Mathematical Society* 105 (2 2022), pp. 1073–1109. DOI: 10.1112/jlms.12532 (cit. on pp. 9–11).
[GM03] Marco Grandis and Luca Mauri. “Cubical sets and their site”. In: *Theory and Applications of Categories* 11 (2003), pp. 185–211. URL: http://www.tac.mta.ca/tac/volumes/11/8/11-08abs.html (cit. on p. 3).
[Gro84] Alexander Grothendieck. *À la poursuite des Champs*. 1984. arXiv: 2111.01000 [math.CT] (cit. on pp. 4, 74).
[GS17] Nicola Gambino and Christian Sattler. “The Frobenius condition, right properness, and uniform fibrations”. In: *Journal of Pure and Applied Algebra* 221.12 (2017), pp. 3027–3068. DOI: 10.1016/j.jpaa.2017.02.013 (cit. on pp. 4, 7, 18–20, 22, 32, 65).
[GSS22a] Nicola Gambino, Christian Sattler, and Karol Szumilo. “The Constructive Kan-Quillen Model Structure: Two New Proofs”. In: *The Quarterly Journal of Mathematics* 73.4 (Apr. 2022), pp. 1307–1373. ISSN: 0033-5606. DOI: 10.1093/qmath/haab057 (cit. on pp. 9, 10).
[GSS22b] Daniel Gratzer, Michael Shulman, and Jonathan Sterling. *Strict universes for Grothendieck topoi*. 2022. arXiv: 2202.12012 [math.CT] (cit. on pp. 24, 76).
[Gui80] René Guitart. “Relations et carrés exacts”. In: *Ann. Sc. Math. Qué.* IV.2 (1980), pp. 103–125. URL: https://www.labmath.uqam.ca/~annales/volumes/04-2/PDF/103-125.pdf (cit. on p. 63).
[Hen25] Simon Henry. “A constructive account of the Kan-Quillen model structure and of Kan’s Ex$^{∞}$ functor”. In: *Cahiers de topologie et géométrie différentielle catégoriques* LXVI (1 2025), pp. 65–124. URL: https://cahierstgdc.com/wp-content/uploads/2025/01/HENRY-SIMON-_-LXVI-1-1.pdf (cit. on pp. 9, 10).
[Hof97] Martin Hofmann. “Syntax and Semantics of Dependent Types”. In: *Semantics and Logics of Computation*. Ed. by Andrew M. Pitts and P. Dybjer. Publications of the Newton Institute. Cambridge University Press, 1997, pp. 79–130. DOI: 10.1017/CBO9780511526619.004 (cit. on p. 75).
[Hov99] Mark Hovey. *Model Categories*. Vol. 63. Mathematical surveys and monographs. American Mathematical Society, 1999. ISBN: 978-0-8218-4361-1. DOI: 10.1090/surv/063 (cit. on p. 5).
[HR24] Sina Hazratpour and Emily Riehl. “A 2-categorical proof of Frobenius for fibrations defined from a generic point”. In: *Mathematical Structures in Computer Science* 34.4 (2024), pp. 258–280. DOI: 10.1017/s0960129524000094 (cit. on pp. 14, 32, 79).
[HS97] Martin Hofmann and Thomas Streicher. “Lifting Grothendieck Universes”. 1997. URL: https://www2.mathematik.tu-darmstadt.de/~streicher/NOTES/lift.pdf (cit. on pp. 2, 23).
[Hub16] Simon Huber. “Cubical Interpretations of Type Theory”. PhD thesis. University of Gothenburg, 2016. URL: https://hdl.handle.net/2077/48890 (cit. on p. 3).

85

[Hub19] Simon Huber. “Canonicity for Cubical Type Theory”. In: *Journal of Automated Reasoning* 63.2 (2019), pp. 173–210. DOI: 10.1007/S10817-018-9469-1 (cit. on p. 11).
[Jar02] J. F. Jardine. *Cubical homotopy theory: a beginning*. Tech. rep. NI02030-NST. Cambridge, UK: Isaac Newton Institute for Mathematical Sciences, 2002. URL: https://api.newton.ac.uk/website/v0/events/preprints/NI02030 (cit. on p. 3).
[Joy97] André Joyal. “Disks, duality and Θ-categories”. AMS meeting in Montréal, 1997. URL: https://ncatlab.org/nlab/files/JoyalThetaCategories.pdf (cit. on p. 62).
[JT07] André Joyal and Myles Tierney. “Quasi-categories vs Segal spaces”. In: *Categories in algebra, geometry and mathematical physics*. Vol. 431. Contemporary Mathematics. Amer. Math. Soc., Providence, RI, 2007, pp. 277–326. DOI: 10.1090/conm/431/08278 (cit. on p. 25).
[Kan55] Daniel M. Kan. “Abstract Homotopy. I”. In: *Proceedings of the National Academy of Sciences of the United States of America* 41.12 (1955), pp. 1092–1096. ISSN: 00278424 (cit. on p. 3).
[KL21] Krzysztof Kapulkin and Peter LeFanu Lumsdaine. “The Simplicial Model of Univalent Foundations (after Voevodsky)”. In: *Journal of the European Mathematical Society* 23 (6 2021), pp. 2071–2126. DOI: 10.4171/JEMS/1050 (cit. on pp. 2, 30, 83).
[LOPS18] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. “Internal Universes in Models of Homotopy Type Theory”. In: *3rd International Conference on Formal Structures for Computation and Deduction, FSCD 2018*. Ed. by Hélène Kirchner. Vol. 108. LIPIcs. Schloss Dagstuhl, 2018, 22:1–22:17. DOI: 10.4230/LIPIcs.FSCD.2018.22 (cit. on pp. 76, 81).
[LS04] Stephen Lack and Paweł Sobociński. “Adhesive Categories”. In: *Foundations of Software Science and Computation Structures*. Ed. by Igor Walukiewicz. Springer Berlin Heidelberg, 2004, pp. 273–288. DOI: 10.1007/978-3-540-24727-2_20 (cit. on p. 18).
[Lur09] Jacob Lurie. *Higher Topos Theory*. Annals of Mathematics Studies 170. Princeton University Press, 2009. URL: https://www.math.ias.edu/~lurie/papers/HTT.pdf (cit. on p. 16).
[LW15] Peter LeFanu Lumsdaine and Michael A. Warren. “The Local Universes Model: An Overlooked Coherence Construction for Dependent Type Theories”. In: *ACM Trans. Comput. Logic* 16.3 (2015). DOI: 10.1145/2754931 (cit. on p. 7).
[Mal05] Georges Maltsiniotis. *La théorie de l’homotopie de Grothendieck*. Astérisque 301. Société mathématique de France, 2005. URL: https://webusers.imj-prg.fr/-georges.maltsiniotis/ps/prstnew.pdf (cit. on p. 4).
[Mal12] George Maltsiniotis. “Carrés exacts homotopiques et dérivateurs”. In: *Cahiers de topologie et géométrie différentielle catégoriques* LIII (1 2012), pp. 3–63. URL: https://cahierstgdc.com/wp-content/uploads/2017/03/Maltsiniotis.pdf (cit. on p. 63).
[ML75] Per Martin-Löf. “An intuitionistic theory of types: predicative part”. In: *Logic Colloquium ’73*. Ed. by H.E. Rose and J.C. Shepherdson. Vol. 80. Studies in Logic and the Foundations of Mathematics. North-Holland, 1975, pp. 73–118. DOI: 10.1016/S0049-237X(08)71945-1 (cit. on p. 2).
[ML79] Per Martin-Löf. *Constructive mathematics and computer programming*. Rep., Dep. Math., Univ. Stockholm, 1979 (cit. on pp. 75, 76).
[NPS01] Bengt Nordström, Kent Petersson, and Jan M. Smith. “Martin-Löf’s type theory”. In: *Handbook of Logic in Computer Science*. Vol. 5. Oxford University Press, 2001. DOI: 10.1093/oso/9780198537816.003.0001 (cit. on p. 2).
[OP18] Ian Orton and Andrew M. Pitts. “Axioms for Modelling Cubical Type Theory in a Topos”. In: *Log. Methods Comput. Sci.* 14.4 (2018). DOI: 10.23638/LMCS-14(4:23)2018. URL: https://doi.org/10.23638/LMCS-14(4:23)2018 (cit. on pp. 9, 23, 76).
[Par18] Erik Parmann. “Functional Kan Simplicial Sets: Non-Constructivity of Exponentiation”. In: *21st International Conference on Types for Proofs and Programs (TYPES 2015)*. Ed. by Tarmo Uustalu. Vol. 69. Leibniz International Proceedings in Informatics (LIPIcs). Dagstuhl, Germany: Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, 2018, 8:1–8:25. DOI: 10.4230/LIPIcs.TYPES.2015.8 (cit. on pp. 2, 10).
[PTJ02] Peter T. Johnstone. *Sketches of an elephant: A topos theory compendium (2 vols.)*. Oxford Logic Guides. Oxford University Press, 2002 (cit. on pp. 17, 18).
[Qui67] Daniel G. Quillen. *Homotopical Algebra*. Vol. 43. Lecture Notes in Mathematics. Springer-Verlag, 1967. DOI: 10.1007/BFb0097438 (cit. on pp. 2, 61).
[Rie] Emily Riehl. *Inductive presentations of generalized Reedy categories*. URL: https://emilyriehl.github.io/files/generalized-reedy.pdf (cit. on pp. 69–71).
[Rie13] Emily Riehl. “Monoidal algebraic model structures”. In: *Journal of Pure and Applied Algebra* 217.6 (2013), pp. 1069–1104. DOI: 10.1016/j.jpaa.2012.09.029 (cit. on p. 50).
[Ril24] Mitchell Riley. *A Type Theory with a Tiny Object*. 2024. arXiv: 2403.01939 [math.CT] (cit. on p. 81).

86

[RS17] Emily Riehl and Michael Shulman. “A type theory for synthetic $\infty$-categories”. In: *Higher Structures* 1.1 (2017), pp. 116–193. DOI: 10.21136/HS.2017.06 (cit. on pp. 62, 80).
[RV14] Emily Riehl and Dominic Verity. “The theory and practice of Reedy categories”. In: *Theory and Applications of Categories* 29.9 (2014), pp. 256–301. URL: http://www.tac.mta.ca/tac/volumes/29/9/29-09abs.html (cit. on pp. 16, 69, 73).
[Sat17] Christian Sattler. *The equivalence extension property and model structures*. 2017. arXiv: 1704.06911 [math.CT] (cit. on pp. 3, 4, 30, 61).
[Sat18] Christian Sattler. *Do cubical models of type theory also model homotopy types*. Lecture at the Hausdorff Trimester Program: Types, Sets and Constructions. 2018. URL: https://www.youtube.com/watch?v=wkPDyIGmEoA (cit. on p. 4).
[Sat19] Christian Sattler. *Idempotent completion of cubes in posets*. 2019. arXiv: 1805.04126 [math.CT] (cit. on pp. 61, 65).
[Sat20] Christian Sattler. *Cylindrical model structures*. 2020. URL: https://www.cse.chalmers.se/~sattler/docs/interval-model-structure.pdf (cit. on pp. 8, 24).
[Shu15] Michael Shulman. “The univalence axiom for elegant Reedy presheaves”. In: *Homology, Homotopy and Applications* 17.2 (2015), pp. 81–106. DOI: 10.4310/HHA.2015.v17.n2.a6 (cit. on pp. 30, 35, 40).
[Shu19] Michael Shulman. *All $(\infty, 1)$-toposes have strict univalent universes*. 2019. arXiv: 1904.07004 [math.AT] (cit. on pp. 4, 7, 10, 12–17, 20, 23, 24).
[Shu23] Michael Shulman. “The derivator of setoids”. In: *Cahiers de topologie et géométrie différentielle catégoriques* LXIV (1 2023), pp. 29–96. URL: https://cahierstgdc.com/wp-content/uploads/2023/01/SHULMAN-LXIV-1.pdf (cit. on p. 9).
[Swa16] Andrew Swan. “An Algebraic Weak Factorisation System on 01-Substitution Sets: A Constructive Proof”. In: *Journal of Logic & Analysis* 8.1 (2016), pp. 1–35. DOI: 10.4115/jla.2016.8.1 (cit. on p. 3).
[Swa18a] Andrew Swan. *W-Types with Reductions and the Small Object Argument*. 2018. arXiv: 1802.07588 [math.CT] (cit. on p. 77).
[Swa18b] Andrew W Swan. *Lifting Problems in Grothendieck Fibrations*. 2018. arXiv: 1802.06718 [math.CT] (cit. on pp. 3, 21).
[Uem18] Taichi Uemura. “Cubical Assemblies, a Univalent and Impredicative Universe and a Failure of Propositional Resizing”. In: *24th International Conference on Types for Proofs and Programs, TYPES 2018*. 2018, 7:1–7:20. DOI: 10.4230/LIPICS.TYPES.2018.7 (cit. on p. 76).
[UF13] The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study, 2013. URL: https://homotopytypetheory.org/book (cit. on pp. 2, 3, 11, 83).

DEPARTMENTS OF PHILOSOPHY AND MATHEMATICS, CARNEGIE MELLON UNIVERSITY, PITTSBURGH, PA 15213, USA
Email address: awodey@cmu.edu

DEPARTMENT OF COMPUTER SCIENCE AND ENGINEERING, CHALMERS UNIVERSITY OF TECHNOLOGY AND UNIVERSITY OF GOTHENBURG, 405 30 GÖTEBORG, SWEDEN
Email address: evan.cavallo@gu.se

DEPARTMENT OF COMPUTER SCIENCE AND ENGINEERING, CHALMERS UNIVERSITY OF TECHNOLOGY AND UNIVERSITY OF GOTHENBURG, 405 30 GÖTEBORG, SWEDEN
Email address: coquand@chalmers.se

DEPARTMENT OF MATHEMATICS, JOHNS HOPKINS UNIVERSITY, BALTIMORE, MD 21218 USA
Email address: eriehl@jhu.edu

DEPARTMENT OF COMPUTER SCIENCE AND ENGINEERING, CHALMERS UNIVERSITY OF TECHNOLOGY AND UNIVERSITY OF GOTHENBURG, S-412 96 GÖTEBORG, SWEDEN
Email address: sattler@chalmers.se

87