Logical Methods in Computer Science  
Volume 20, Issue 2, 2024, pp. 16:1–16:54  
<https://lmcs.episciences.org/>

Submitted Aug. 21, 2020  
Published Jun. 19, 2024

# TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

ANDREAS NUYTS AND DOMINIQUE DEVRIESE

DistriNet, KU Leuven, Belgium

*e-mail address:* andreas.nuyts@kuleuven.be, dominique.devriese@kuleuven.be

**ABSTRACT.** Presheaf models of dependent type theory have been successfully applied to model HoTT, parametricity, and directed, guarded and nominal type theory. There has been considerable interest in internalizing aspects of these presheaf models, either to make the resulting language more expressive, or in order to carry out further reasoning internally, allowing greater abstraction and sometimes automated verification. While the constructions of presheaf models largely follow a common pattern, approaches towards internalization do not. Throughout the literature, various internal presheaf operators ($\checkmark$, $\Phi$/extent, $\Psi$/Gel, Glue, Weld, mill, the strictness axiom and locally fresh names) can be found and little is known about their relative expressiveness. Moreover, some of these require that variables whose type is a shape (representable presheaf, e.g. an interval) be used affinely.

We propose a novel type former, the transpension type, which is right adjoint to universal quantification over a shape. Its structure resembles a dependent version of the suspension type in HoTT. We give general typing rules and a presheaf semantics in terms of base category functors dubbed multipliers. Structural rules for shape variables and certain aspects of the transpension type depend on characteristics of the multiplier. We demonstrate how the transpension type and the strictness axiom can be combined to implement all and improve some of the aforementioned internalization operators (without formal claim in the case of locally fresh names).

## 1. INTRODUCTION AND RELATED WORK

**1.1. The power of presheaves.** Presheaf semantics [Hof97, HS97] are an excellent tool for modelling relational preservation properties of (dependent) type theory. They have been applied to parametricity (which is about preservation of relations) [AGJ14, BCM15, ND18a, NVD17], univalent type theory (preservation of equivalences) [BCH14, CMS20, CCHM17, Hub16, KL18, Ort18, OP18], directed type theory (preservation of morphisms), guarded type theory (preservation of the stage of advancement of computation) [BM20] and even

*Key words and phrases:* dependent type theory, presheaf models, modal type theory, homotopy type theory, parametricity, directed type theory, guarded type theory.

Andreas Nuyts holds a Postdoctoral Fellowship from the Research Foundation - Flanders (FWO; 1247922N), and carried out most of this research holding a PhD Fellowship from the Research Foundation - Flanders (FWO; 1110817N). This research was partially conducted at Vrije Universiteit Brussel and funded by the Research Foundation - Flanders (FWO; G0G0519N). This research is partially funded by the Research Fund KU Leuven.

LOGICAL METHODS  
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-20(2:16)2024

© A. Nuyts and D. Devriese  
Creative Commons

16:2

A. NUYTS AND D. DEVRIESE

Vol. 20:2

combinations thereof [BBC$^{+}$19, CH21, RS17, WL20].$^{1}$ The presheaf models just cited almost all follow a common pattern: First one chooses a suitable base category $\mathcal{W}$. The presheaf category over $\mathcal{W}$ is automatically a model of dependent type theory with the important basic type formers [Hof97] as well as a tower of universes [HS97]. Next, one identifies a suitable notion of fibrancy and replaces or supplements the existing type judgement $\Gamma \vdash T$ type with one that classifies fibrant types:

**HoTT:** For homotopy type theory (HoTT, [Uni13]), one considers Kan fibrant types, i.e. presheaves in which edges can be composed and inverted as in an $\infty$-groupoid. The precise definition may differ in different treatments.

**Parametricity:** For parametric type theory, one considers discrete types [AGJ14, CH21, ND18a, NVD17]: essentially those that satisfy Reynolds' identity extension property [Rey83] which states that homogeneously related objects are equal. This can be expressed by requiring that any non-dependent function $\mathbb{I} \to A$ from the relational interval, is constant.

**Directed:** In directed type theory, one may want to consider Segal, covariant, discrete and Rezk types [RS17] and possibly also Conduché types [Gir64, Nuy18b][Nuy20a, ex. 8.1.27].

**Guarded:** In guarded type theory, one considers clock-irrelevant types [BM20]: types $A$ such that any non-dependent function $\odot \to A$ from the clock type, is constant.

**Nominal:** Nominal type theory [Che12, PMD15] can be modelled in the Schanuel topos [Pit13, §6.3]. This is the subcategory of nullary affine cubical sets (see Example 6.14 later on) that send pushouts in the base category to pullbacks in Set. This ensures that if a cell depending on names $\{i, j, k\}$ in fact only depends on $\{i, j\}$ and in fact also only depends on $\{i, k\}$, then it only depends on $\{i\}$.

To the extent possible, one subsequently proves that the relevant notions of fibrancy are closed under basic type formers, so that we can restrict to fibrant types and still carry out most of the familiar type-theoretic reasoning and programming. Special care is required for the universe U: it is generally straightforward to adapt the standard Hofmann-Streicher universe to classify only fibrant types, but the universe of fibrant types is in general not automatically fibrant itself.

**HoTT:** In HoTT, the Hofmann-Streicher universe of Kan types is usually automatically Kan.

**Parametricity:** In earlier work on parametricity with Vezzosi [NVD17, ND18a], we made the universe of discrete types discrete by modifying its presheaf structure and introduced a parametric modality in order to use that universe. In contrast, Atkey et al. [AGJ14] and Cavallo and Harper [CH21] simply accept that their universes of discrete types are not discrete.

**Directed:** In directed type theory, one could expect, perhaps via a directed univalence result [WL20], that the universe of covariant types is Segal.

**Guarded:** In guarded type theory, Bizjak et al. [BGC$^{+}$16] let the universe depend on a collection of in-scope clock variables lest the clock-indexed later modality $\triangleright : \forall (\kappa : \odot).U_{\Delta} \to U_{\Delta}$ (where $\kappa \in \Delta$) be non-dependent and therefore constant (not clock-indexed) by clock-irrelevance of $U \to U$ [BM20].

$^{1}$We omit models that are not explicitly structured as presheaf models [AHH18, LH11, Nor19].

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:3

1.2. Internalizing the power of presheaves. Purely metatheoretic results about type theory certainly have their value. Parametricity, for instance, has originated and proven its value as a metatheoretic technique for reasoning about programs. However, with dependent type theory being not only a programming language but also a logic, it is preferable to formulate results about it within the type system, rather than outside it. We highlight two particular motivations for doing so: to enlarge the end user's toolbox, and to be able to prove internally that a type is fibrant.

Enlarging the end user's toolbox. One motivation for internalizing metatheorems is to enlarge the toolbox of the end user of the proof assistant. If this is the only goal, then we can prove the desired results in the model on pen and paper and then internalize them ad hoc with an axiom with or without computation rules.

HoTT: Book HoTT [Uni13] simply postulates the univalence axiom without computational behaviour, as justified e.g. by the model of Kan-fibrant simplicial sets [KL18].

CCHM cubical type theory [CCHM17] provides the Glue type, which comes with introduction, elimination, β- and η-rules and which turns the univalence axiom into a theorem with computational behaviour. It also contains CCHM-Kan-fibrancy of all types as an axiom, in the form of the CCHM-Kan composition operator, with decreed computational behaviour that is defined by induction on the type.

Parametricity: Bernardy, Coquand and Moulin [BCM15, Mou16] (henceforth: BCM) internalize their (unary, but generalizable to k-ary) cubical set model of parametricity using two combinators Φ and Ψ [Mou16], a.k.a. extent and Gel [CH21]. Φ internalizes the presheaf structure of the function type, and Ψ that of the universe.

The combinator Φ and at first sight also Ψ require that the cubical set model lacks diagonals. Indeed, to construct a value over the primitive interval, Φ and Ψ each take one argument for every endpoint and one argument for the edge as a whole. Nested use of these combinators, e.g. to create a square, will take (k + 1)² arguments for k² vertices, 2k sides and 1 square as a whole but none for specifying the diagonal. For this reason, BCM's type system enforces a form of affine use of interval variables. Similarly, connections as in CCHM [CCHM17] are ruled out. In the current paper, we will see that these requirements are not absolute for Ψ: there is apparently a very natural 'automatic' way to define the behaviour on diagonals and connections where the Ψ-type is not explicitly specified by its arguments.

In earlier work with Vezzosi [NVD17], we have internalized parametricity instead using the Glue type [CCHM17] and its dual Weld. Later on, we added a primitive mill [ND18b] for swapping Weld and Π(i : 𝕀). These operations are sound in presheaves over any base category where we can multiply with 𝕀 – including cube categories with diagonals or connections – and are (therefore) strictly less expressive than Φ which is not. Discreteness of all types was internalized as a non-computing path degeneracy axiom.²

²It is worth noting that it was not possible to use affine interval variables in the setting of [NVD17]: The type system features parametric Π-types which are modelled as ordinary Π-types with non-discrete domain. Discreteness of the Π-type can be proven solely from discreteness of the codomain, simply by swapping interval variable and function argument. This is however not possible in the affine setting, where only variables introduced prior to an interval variable are taken to be fresh for that interval variable and the exchange rule with an interval variable only works one way.

16:4

A. NUYTS AND D. DEVRIESE

Vol. 20:2

**Directed:** Weaver and Licata [WL20] use a bicubical set model to show that directed HoTT [RS17] can be soundly extended with a directed univalence *axiom*.

**Guarded:** In guarded type theory [BM20], one axiomatizes Löb induction and clock-irrelevance.

**Nominal:** One version of nominal type theory [PMD15] provides the locally fresh name abstraction $\nu(i : \mathbb{I})$ which can be used anywhere (i.e. the goal type remains the same after we abstract over a fresh name). The operation introduces a name but requires a body that is fresh for the name (i.e. we do not get to use it). This would be rather useless, were it not that we are allowed to *capture* the fresh name (see Section 10).

*Internalizing fibrancy proofs.* Another motivation to internalize aspects of presheaf categories, is for building parts of the model inside the type theory, thus abstracting away certain categorical details such as the very definition of presheaves, and for some type systems enabling automatic verification of these constructions. Given the common pattern in models described in the previous section, it is particularly attractive to try and define fibrancy and prove results about it internally.

In the context of HoTT, Orton and Pitts [Ort18, OP18] study CCHM-Kan-fibrancy [CCHM17] in a type theory extended with a set of axioms, of which all but one serve to characterize the interval and the notion of cofibration. One axiom, *strictness*, provides a type former Strict for strictifying partial isomorphisms, which exists in every presheaf category. In order to construct a universe of fibrant types, Licata et al. postulate an “amazing right adjoint” $\mathbb{I} \setminus \sqcup$ to the non-dependent path functor $\mathbb{I} \to \sqcup$ [LOPS18, Ort18], which indeed exists in presheaves over cartesian base categories if $\mathbb{I}$ is representable. Since $\mathbb{I} \setminus \sqcup$ and its related axioms are global operations (only applicable to closed terms, unless you want to open Pandora’s box as we do in the current paper), they keep everything sound by introducing a judgemental comonadic *global* modality $\flat$.

Orton et al.’s formalization [LOPS18, Ort18, OP18] is only what we call *meta-internal*: the argument is internalized to *some* type theory which still only serves as a metatheory of the type system of interest. Ideally, we would also be able to define and prove fibrancy of types *within* the type theory of interest, which we call *auto-internal*. This has several advantages:

- A general approach to auto-internalization of notions of fibrancy saves us from a proliferation of type systems, each with axiomatic internal fibrancy operations with hard-coded computational behaviour that proceeds by case analysis on the construction of the type. Proving fibrancy auto-internally will in general be more typesafe than hard-coding it in a language implementation that is often written in a simply-typed language such as Haskell and OCaml.
- Given an auto-internal implementation, we can still pretend that we have a meta-internal situation by restricting ourselves to a subset of the language. But we automatically get a two-level type theory [Voe13, ACKS23], where we have access to non-fibrant types from within. (This does not prove conservativity of two-level type theory over the object system.)
- In directed type theory, there are various relevant notions of fibrancy, many of which are not well preserved by basic type formers, so access to non-fibrant types may be a necessity to get any work done at all.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:5

Auto-internal treatments exist of discrete types in parametricity [CH21], and discrete, fibrewise-Segal and Rezk types in directed type theory [RS17], but not yet for covariant, Segal or Kan fibrant types due to the need to consider paths in the context $\mathbb{I} \to \Gamma$.

1.3. The transpension type. What is striking about the previous section is that, while most authors have been able to solve their own problems, a common approach is completely absent. We have encountered $\Phi$ and $\Psi$ [Mou16], the amazing right adjoint $\sqrt{}$ [LOPS18], Glue [CCHM17, NVD17], Weld [NVD17], mill [ND18b], the strictness axiom [OP18] and locally fresh names [PMD15]. We have also seen that $\Phi$ and $\Psi$ presently require an affine base category, and that $\sqrt{}$ presently requires the global modality $\flat$.

The goal of the current paper is to develop a smaller collection of internal primitives that impose few restrictions on the choice of base category and allow the internal construction of the aforementioned operators when sound. To this end, we introduce the transpension type former $\Diamond[i] : \mathrm{Ty}(\Gamma) \to \mathrm{Ty}(\Gamma, i : \mathbb{I})$ which in cartesian settings is right adjoint to $\Pi(i : \mathbb{I}) : \mathrm{Ty}(\Gamma, i : \mathbb{I}) \to \mathrm{Ty}(\Gamma)$ and is therefore not a quantifier binding $i$, but a coquantifier that depends on it. This same operation was already considered in topoi by Yetter [Yet87], who named it $\nabla$. Using the transpension and Strict, we can construct $\Phi$ (when sound), $\Psi$, $\sqrt{}$ and Glue, and heuristically translate a subsystem of the nominal dependent type system FreshMLTT [PMD15] featuring variable capture and locally fresh names. Given a type former for certain pushouts, we can also construct Weld and mill.

The transpension coquantifier $\Diamond[u : \mathbb{U}] : \mathrm{Ty}(\Gamma) \to \mathrm{Ty}(\Gamma, u : \mathbb{U})$ is part of a sequence of adjoints $\Sigma u \dashv \Omega[u] \dashv \Pi u \dashv \Diamond[u]$, preceded by the $\Sigma$-type, weakening and the $\Pi$-type. Adjointness of the first three is provable from the structural rules of type theory. However, it is not immediately clear how to add typing rules for a further adjoint. Birkedal et al. [BCM$^+$20] explain how to add a single modality that has a left adjoint in the semantics. If we want to have two or more adjoint modalities internally, then we can use a multimodal type system such as MTT [GKNB21, GKNB20a]. Each modality in MTT needs a semantic left adjoint, so we can only internalize $\Omega[u]$, $\Pi u$ and $\Diamond[u]$. A drawback which we accept (as a challenge for future work), is that $\Omega[u]$ and $\Pi u$ become modalities which are a bit more awkward to deal with than ordinary weakening and $\Pi$-types.

A further complication is that the aforementioned modalities bind or depend on a variable, a phenomenon which is not supported by MTT. We solve this by grouping shape variables such as $u : \mathbb{U}$ in a shape context which is not considered part of the type-theoretic context but instead serves as the mode of the judgement. This way, we are also rid of the requirement that all internal operations commute with shape substitution; in fact, the transpension generally does not (Section 2.1.7, [Nuy20b]).

1.4. Contributions. Our central contribution is to reduce the plethora of internal presheaf operators in the literature to only a few operations.

- To this end, we formulate a type system MTraS featuring a transpension type $\Diamond[u : \mathbb{U}]$, right adjoint to $\Pi(u : \mathbb{U})$, with typing rules built on extensional MTT [GKNB21, GKNB20a]. We explain how it is reminiscent of the suspension type from HoTT [Uni13].
- More generally, the transpension type can be right adjoint to any quantifier-like operation $\forall(u : \mathbb{U})$ which need neither respect the exchange rule, nor weakening or contraction. In this setting, we also introduce the fresh weakening coquantifier $\exists[u : \mathbb{U}]$, which is left adjoint to $\forall(u : \mathbb{U})$ and therefore coincides with weakening $\Omega[u : \mathbb{U}]$ in cartesian settings.

16:6

A. NUYTS AND D. DEVRIESE

Vol. 20:2

- We provide a categorical semantics for $\mathbb{Q}[u : \mathbb{U}]$ in almost any presheaf category $\mathrm{Psh}(\mathcal{W})$ over base category $\mathcal{W}$, for almost any representable object $\mathbb{U} = \mathbf{y}U$, $U \in \mathcal{W}$. To accommodate non-cartesian variables, our system is not parametrized by a representable object $\mathbb{U} = \mathbf{y}U$, but by an arbitrary endofunctor $\sqcup \ltimes U$ on $\mathcal{W}$: the **multiplier**.$^3$ We introduce **criteria** for characterizing the multiplier (Definition 6.2) which we use as requirements for internal type theoretic features. We identify a complication for base categories (most notably in guarded and nominal type theory) that are not *objectwise pointable*, and define dimensionally split morphisms (a generalization of split epimorphisms) in order to include those base categories. We exhibit relevant multipliers in base categories found in the literature (Section 6.3).
- We show that **all general presheaf internalization operators** that we are aware of – viz. $\Phi$/extent (when sound), $\Psi$/Gel [Mou16, BCM15], the amazing right adjoint $\surd$ [LOPS18], Glue [CCHM17, NVD17], Weld [NVD17], mill [ND18b] and (with no formal claim) locally fresh names – can be **recovered** from just the transpension type, the strictness axiom and pushouts along $\mathsf{snd} : \varphi \times A \to A$ where $\varphi : \mathsf{Prop}$ (see Fig. 9 for a dependency graph). In the process, some of these operators can be **improved**: We generalize $\Psi$ from affine-like ($\top$-slice full) to arbitrary multipliers, including cartesian ones and we justify $\mathbb{U} \surd \sqcup$ without a global modality and get $\beta$- and $\eta$-rules for it. Moreover, since our system provides an operation $\widehat{\bullet}_{[u]}$ for quantifying contexts, we take a step towards auto-internalizing Orton et al.'s work [LOPS18, Ort18, OP18]. When $\Phi$ is not sound (e.g. in settings with diagonals or connections), we suggest the internal notion of **transpensive** types to retain some of its power. Finally, a form of higher dimensional pattern matching is enabled by exposing $\forall(u : \mathbb{U})$ internally as a left adjoint.
- In a technical report [Nuy20b], we investigate how the modalities introduced in this paper commute with each other, and with prior modalities (i.e. those already present before adding the transpension type). We also consider composite multipliers, and natural transformations between modalities (called 2-cells in MTT) arising from natural transformations between multipliers.

While MTT [GKNB21, GKNB20a] satisfies canonicity and even normalization insofar as its modality system (called the *mode theory*) does [Gra22], we will instantiate MTT on a mode theory for which we presently do not have a computational theory, and we will extend it with some additional typing rules. For this reason, we build on extensional MTT [GKNB20a], and defer canonicity and decidability of type-checking to future work.

1.5. **Overview of the paper.** In Section 2, we study in a simplified setting (a system called FFTraS) how the transpension type resembles the suspension type from HoTT and demonstrate how to put it in action. In Section 3, we give a brief overview of the typing rules of MTT and decorate the MTT syntax with *left adjoint reminders*. In Section 4, we define the mode theory of MTraS, an instantiation of MTT. This mode theory is extremely general and essentially contains all semantic adjoint pairs of a given domain and codomain as modalities between the corresponding modes. In the next two sections, we highlight a number of interesting modalities: in Section 5 we consider modalities related to shape substitutions, and in Section 6 we define and study multipliers and consider modalities arising from them, including the transpension modality. In Section 7, we pseudo-embed FFTraS in MTraS and generalize some of the results obtained for FFTraS. In Section 8,

$^3$In the technical report [Nuy20b], we generalize multipliers beyond *endofunctors*.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:7

we supplement MTraS with a few specialized typing rules. In Section 9, we investigate the structure of the transpension type in MTraS. In Section 10, we explain how to recover known internal presheaf operators. We conclude in Section 11.

## 2. FIRST STEPS: A FULLY FAITHFUL TRANSPENSION SYSTEM (FFTRAS)

In this section, for purposes of demonstration, we present simplified typing rules for the transpension type which apply in a specific setting (as proven in Section 7). Using these, we will already be able to exhibit the transpension type as similar to a dependent version of the suspension type in HoTT [Uni13], and to prove internally that it is right adjoint to universal quantification. Moreover, in order to showcase how the transpension type allows us to internalize the presheaf structure of other types, we will demonstrate a technique which we call higher-dimensional pattern matching and which has already been demonstrated by Pitts [Pit14] in nominal type theory using locally fresh names [PMD15].

2.1. Typing rules. To do this, we first present, in Fig. 1, typing rules for the transpension type in a specific setting: a dependent type system with linear or affine shape variables $u : \mathbb{U}$, where shape variable contraction is forbidden.

2.1.1. Linear/affine shape variables. Variables to the left of $u$ are understood to be fresh for $u$; variables introduced after $u$ may be substituted with terms depending on $u$. In particular, we have no contraction $(w/u, w/v) : (w : \mathbb{U}) \to (u, v : \mathbb{U})$, while exchange $(x : A, u : \mathbb{U}) \to (u : \mathbb{U}, x : A)$ only works in one direction. This is enforced by the special substitution rule for shape variables (FF:CTX-SHP:FMAP). Weakening of shape variables is optionally allowed (FF:CTX-SHP:WKN). The examples in which the type system will be put to use, are agnostic as to whether exchange of shape variables $(u : \mathbb{U}, v : \mathbb{U}) \to (v : \mathbb{U}, u : \mathbb{U})$ is possible and models of both situations exist.

2.1.2. Linear/affine function type. The system features a linear/affine function type $\forall u.A$ over $\mathbb{U}$, with unsurprising formation and introduction rules (FF:FORALL, FF:FORALL:INTRO). The rule for $f u$ (FF:FORALL:ELIM) requires that the function $f$ be fresh for $u$, i.e. that $f$ depend only on variables to the left of $u$ [BCM15, Mou16]. For simplicity, we require that $u$ is the last shape variable in the context.

2.1.3. Transpension type. Additionally, the system contains a transpension type $\Diamond[u] A$ over $\mathbb{U}$, with more unusual rules. Similar to the introduction rule of multimode type theory (MTT) (WDRA:INTRO in Fig. 4), the meridian constructor of the transpension type (FF:TRANSP:INTRO) works by dependent transposition [BCM$^+$20][Nuy18a, §2.1.3][Nuy20a, §5.1.3-5.2]: a term of type $\Diamond[u] A$ in a given context, is equivalent to a term of type $A$ in the context obtained by applying the left adjoint to $\Diamond[u]$ – which is universal quantification over $u$ – to the context. However, the situation is a bit more subtle than in MTT, in the sense that the left adjoint $\forall u$ is itself a binder and therefore acts on objects already living in a context. For this reason, we consider the entire situation in a further context $\Gamma$. So we start from a context $\Gamma$, a telescope $\delta : \Delta$ (where $\delta$ denotes the vector of variables in the telescope) in context $\Gamma, u : \mathbb{U}$ and a term $a : A$ that does not live in telescope $\Delta$ but in the universally quantified telescope $\forall u.(\delta : \Delta)$ [BV17, ND19], which extends $\Gamma$. The resulting meridian

16:8

A. Nuyts and D. Devriese

Vol. 20:2

Linear/affine shape variables:

|  FF:CTX-SHP\( \Gamma \) ctx\( \overline{\Gamma, u : \mathbb{U} \) ctx | FF:CTX-SHP:FMAP\( \sigma : \Gamma \to \Gamma' \)\( (\sigma, u/u') : (\Gamma, u : \mathbb{U}) \to (\Gamma', u' : \mathbb{U}) \) | FF:CTX-SHP:WKN (optional)\( \sigma : \Gamma \to \Gamma' \)\( \overline{\sigma : (\Gamma, u : \mathbb{U}) \to \Gamma'} \)  |
| --- | --- | --- |

Linear/affine function type:

|  FF:FORALL\( \Gamma, u : \mathbb{U} \vdash A \text{ type} \)\( \overline{\Gamma \vdash \forall u.A \text{ type}} \) | FF:FORALL:INTRO\( \Gamma, u : \mathbb{U} \vdash a : A \)\( \overline{\Gamma \vdash \lambda u.a : \forall u.A} \) | FF:FORALL:ELIM\( \Gamma \vdash f : \forall u.A \)No shape vars in \( \Delta \)\( \overline{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash f u : A} \)  |
| --- | --- | --- |

Telescope quantification:

|  FF:CTX-FORALL\( \Gamma, u : \mathbb{U}, \delta : \Delta \text{ ctx} \)No shape vars in \( \Delta \)\( \overline{\Gamma, \forall u.(\delta : \Delta) \text{ ctx}} \) | FF:CTX-FORALL:FMAP\( (\sigma, u/u', \tau/\delta') : (\Gamma, u : \mathbb{U}, \delta : \Delta) \to (\Gamma', u' : \mathbb{U}, \delta' : \Delta') \)\( (\sigma, \lambda u.\tau/\lambda u'.\delta') : (\Gamma, \forall u.(\delta : \Delta)) \to (\Gamma', \forall u'.(\delta' : \Delta')) \)  |
| --- | --- |

FF:CTX-FORALL:NIL

\[
(\Gamma , \forall u. ()) = \Gamma
\]

FF:CTX-FORALL:FMAP:NIL

\[
(\sigma , \lambda u. () / \lambda u ^ {\prime}. ()) = \sigma
\]

Telescope application

|  FF:CTX-APP\( \Gamma, u : \mathbb{U}, \delta : \Delta \text{ ctx} \)\( (v/u, (\lambda u.\delta) v/\delta) : (\Gamma, \forall u.(\delta : \Delta), v : \mathbb{U}) \to (\Gamma, u : \mathbb{U}, \delta : \Delta) \)  |
| --- |

FF:CTX-APP:NAT : The following diagram commutes:

\[
\begin{array}{c} (\Gamma , \forall u. (\delta : \Delta), v: \mathbb {U}) \xrightarrow {(v / u , (\lambda u . \delta)   v / \delta)} (\Gamma , u: \mathbb {U}, \delta : \Delta) \\ \Biggl \downarrow_ {(\sigma , \lambda u. \tau / \lambda u ^ {\prime}. \delta^ {\prime}, v / v ^ {\prime})} \\ (\Gamma^ {\prime}, \forall u ^ {\prime}. (\delta^ {\prime}: \Delta^ {\prime}), v ^ {\prime}: \mathbb {U}) \xrightarrow [ (v ^ {\prime} / u ^ {\prime} , (\lambda u ^ {\prime} . \delta^ {\prime})   v ^ {\prime} / \delta^ {\prime}) ]{(v / u , (\lambda u . \delta)   v / \delta)} (\Gamma^ {\prime}, u ^ {\prime}: \mathbb {U}, \delta^ {\prime}: \Delta^ {\prime}) \end{array}
\]

FF:CTX-APP:NIL

\[
(v / u, (\lambda u. ()) v / ()) = (v / u)
\]

FF:CTX-FORALL:FMAP:CTX-APP

\[
(\lambda v. (\lambda u. \delta) v / \lambda u. \delta) = 1 _ {(\Gamma , \forall u. (\delta : \Delta))}
\]

Transpension type:

|  FF:TRANSP\( \Gamma, u : \mathbb{U}, \delta : \Delta \text{ ctx} \)\( \frac{\Gamma, \forall u.(\delta : \Delta) \vdash A \text{ type}}{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash \Diamond[u] A \text{ type}} \) | FF:TRANSP:INTRO\( \frac{\Gamma, \forall u.(\delta : \Delta) \vdash a : A}{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash \text{mer}[u] a : \Diamond[u] A} \) | FF:TRANSP:ELIM\( \frac{\Gamma, u : \mathbb{U} \vdash t : \Diamond[u] A}{\Gamma \vdash \text{unmer}(u.t) : A} \)  |
| --- | --- | --- |

FF:TRANSP:BETA

\[
\frac {\Gamma \vdash a : A}{\Gamma \vdash \operatorname{unmer} (u . \operatorname{mer} [ u ] a) = a : A}
\]

FF:TRANSP:ETA

\[
\begin{array}{l} \Gamma , u: \mathbb {U}, \delta : \Delta \vdash t: \Diamond [ u: \mathbb {U} ] A \\ \overline {{\Gamma , u : \mathbb {U} , \delta : \Delta \vdash t =}} \\ \operatorname{mer} [ u ] (\operatorname{unmer} (v. t [ v / u, (\lambda u. \delta) v / \delta ])) : \Diamond [ u ] A \end{array}
\]

FF:TRANSP:NAT

\[
\Gamma^ {\prime}, \forall u ^ {\prime}. (\delta^ {\prime}: \Delta^ {\prime}) \vdash A \text { type }
\]

\[
(\sigma , u / u ^ {\prime}, \tau / \delta^ {\prime}):
\]

\[
(\Gamma , u: \mathbb {U}, \delta : \Delta) \rightarrow (\Gamma^ {\prime}, u ^ {\prime}: \mathbb {U}, \delta^ {\prime}: \Delta^ {\prime})
\]

\[
\Gamma , u: \mathbb {U}, \delta : \Delta \vdash (\Diamond [ u ^ {\prime} ] A) [ \sigma , u / u ^ {\prime}, \tau / \delta^ {\prime} ] =
\]

\[
\left. \left\langle [ u ] \left(A [ \sigma , \lambda u. \tau / \lambda u ^ {\prime}. \delta^ {\prime} ]\right) \text {type} \right. \right.
\]

FF:TRANSP:INTRO:NAT

\[
\Gamma^ {\prime}, \forall u ^ {\prime}. (\delta^ {\prime}: \Delta^ {\prime}) \vdash a: A
\]

\[
(\sigma , u / u ^ {\prime}, \tau / \delta^ {\prime}):
\]

\[
(\Gamma , u: \mathbb {U}, \delta : \Delta) \rightarrow (\Gamma^ {\prime}, u ^ {\prime}: \mathbb {U}, \delta^ {\prime}: \Delta^ {\prime})
\]

\[
\Gamma , u: \mathbb {U}, \delta : \Delta \vdash (\operatorname{mer} [ u ^ {\prime} ] a) [ \sigma , u / u ^ {\prime}, \tau / \delta^ {\prime} ] =
\]

\[
\operatorname{mer} [ u ] \left(a [ \sigma , \lambda u. \tau / \lambda u ^ {\prime}. \delta^ {\prime} ]\right): (\left. \left\langle [ u ^ {\prime} ] A\right) [ \sigma , u / u ^ {\prime}, \tau / \delta^ {\prime} ] \right.
\]

Figure 1: Selection of typing rules for a fully faithful transpension type.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:9

$\text{mer}[u] a : \Diamond[u] A$ then lives in telescope $\Delta$, which extends $\Gamma, u : \mathbb{U}$. Thus, we remark that both $\Diamond[u] A$ and $\text{mer}[u] a$ depend on $u$, whereas $A$ and $a$ do not, so in a way the transpension lifts data to a higher dimension, turning points into $\mathbb{U}$-cells.

The type formation rule FF:TRANSP is parallel to the modal type formation rule of MTT (WDRA in Fig. 4), which internalizes a (weak) dependent right adjoint; its premises are such that the introduction rule is well-typed.

The elimination rule FF:TRANSP:ELIM is equivalent to the existence of the function

$$\lambda f.\text{unmer}(u.f u) : (\forall u.\Diamond[u] A) \to A,$$

which is essentially the co-unit of the adjunction; this differs from the elimination rule of MTT (WDRA:ELIM in Fig. 4) which works by pattern-matching, but is parallel to the projection function in Proposition 3.3, as are the $\beta$- and $\eta$-rules which internalize the adjunction laws and to which we get back in Section 2.1.6. The elimination rule takes data again to a lower dimension: it turns a dependent $\mathbb{U}$-cell in the transpension into a point in $A$.

2.1.4. Admissibility of telescope rules. The typing rules for the transpension type rely on the unusual notions of telescope quantification and application, which remain to be discussed. Before doing so, we remark that one can take either of two viewpoints w.r.t. these rules. One can take a syntactic viewpoint, viewing each of the typing rules concerned as a formal typing rule, i.e. as a constructor of our generalized algebraic syntax [Car86, Car78, AK16]. Alternatively, it is possible to prove metatheoretically that each of these rules is admissible, by defining $\forall u.(\delta : \Delta)$ as a telescope of the same length as $\Delta$, but where each variable's type is universally quantified over $u : \mathbb{U}$. This latter view is the one that inspires most of our notations, but we make a point of not violating the former possibility, because that one allows a pseudo-embedding$^4$ of the current specialized system in the main system of this paper (Section 7).

2.1.5. Telescope quantification. Given a context $\Gamma, u : \mathbb{U}, \delta : \Delta$ with no shape variables in $\Delta$, the rule FF:CTX-FORALL creates a new context $\Gamma, \forall u.(\delta : \Delta)$, which is just $\Gamma$ again if $\Delta$ has zero variables (FF:CTX-FORALL:NIL). From the syntactic viewpoint, it would perhaps be cleaner to write something like $[\forall u](\Gamma, u : \mathbb{U}, \delta : \Delta)$, or more generally $[\forall u]\Theta$ for any context $\Theta$ featuring $u : \mathbb{U}$ as its last shape variable. However, the notation we have chosen is possible since every such context is of the form $\Theta = \Gamma, u : \mathbb{U}, \delta : \Delta$ for some context $\Gamma$ and telescope $\Delta$, and moreover it is justified by the admissibility proof as well as in the following sense:

(1) The variables in $\Gamma$ can be accessed in context $[\forall u](\Gamma, u : \mathbb{U}, \delta : \Delta)$,
(2) For every variable $y : B$ in $\Delta$, we get a term of type $\forall v.B[\sigma]$ in context $[\forall u](\Gamma, u : \mathbb{U}, \delta : \Delta)$ (for a suitable substitution $\sigma$).

To see (1), we make use of the functoriality rule FF:CTX-FORALL:FMAP, which from the syntactic viewpoint we could more cleanly write as $[\forall(u/u')]\rho : [\forall u]\Theta \to [\forall u']\Theta'$ for $\rho : \Theta \to \Theta'$. The alternative notation in the typing rule is again possible since any such $\rho$ is of the form $\rho = (\sigma, u/u', \tau/\delta')$ for some $\sigma : \Gamma \to \Gamma'$ and well-typed vector of terms $\tau$, and justified for similar reasons as above. By applying functoriality to the weakening substitution $(\Gamma, u : \mathbb{U}, \delta : \Delta) \to (\Gamma, u : \mathbb{U})$, we get a substitution $(\Gamma, \forall u.(\delta : \Delta)) \to (\Gamma, \forall u.()) = \Gamma$, which we can use to ignore $\forall u.(\delta : \Delta)$ altogether and thus get access to the variables in context $\Gamma$.

$^4$Pseudo, because FF:CTX-FORALL:NIL is only an isomorphism in the general system, but that would undidactically complicate notations in the current section.

16:10

A. NUYTS AND D. DEVRIESE

Vol. 20:2

To see (2), we need telescope application.

The transpension type and the meridian constructor respect substitution (FF:TRANSP:NAT, FF:TRANSP:INTRO:NAT), and this can only be stated thanks to functoriality (FF:CTX-FORALL:FMAP).

2.1.6. *Telescope application.* In Section 2.1.3 above, we noted that the formation and introduction rules of the transpension type are in line with those of the modal type in MTT (Fig. 4) and act by dependent transposition. In fact, the same is true for the formation and introduction rules of the linear/affine function type, which is a dependent right adjoint to shape variable extension of contexts (FF:CTX-SHP). In order for the types to be adjoints internally – which requires that we can define unit and co-unit functions and that the adjunction laws are statable and satisfied – we need their left adjoint operations to be adjoints, i.e. for any context $\Psi$ and any context $\Theta = (\Gamma, u : \mathbb{U}, \Delta)$, we need substitutions $\Psi \rightarrow [\forall u]\Theta = (\Gamma, \forall u.(\delta : \Delta))$ to be equivalent to substitutions $(\Psi, u : \mathbb{U}) \rightarrow \Theta = (\Gamma, u : \mathbb{U}, \delta : \Delta)$ respecting $u$.

One way to ensure this is by providing natural unit and co-unit substitutions. For the unit, we need substitutions $\Psi \rightarrow \forall u = (\Psi, \forall u.()) = \Psi$, so we can take the identity. In other words, the unit is given by FF:CTX-FORALL:NIL, with naturality given by FF:CTX-FORALL:FMAP:NIL.

For the co-unit, we need substitutions $(\Gamma, \forall u.(\delta : \Delta), v : \mathbb{U}) \rightarrow (\Gamma, u : \mathbb{U}, \Delta)$, which are given by FF:CTX-APP and made natural by FF:CTX-APP:NAT. Again, from the syntactic viewpoint it would be cleaner to write $\mathsf{app}_{\Theta} : ([\forall u]\Theta, v : \mathbb{U}) \rightarrow \Theta$. However, intuitively, semantically and in the admissibility proof, what it does is applying the 'function' $\lambda u.\delta : \forall u.\Delta$ to $v : \mathbb{U}$, which inspires the notation in the typing rule.

Since the unit is the identity, the adjunction laws simply require that whiskering the co-unit with either adjoint also yields the identity. The fact that $\mathsf{app}_{(\Gamma, u:\mathbb{U})} = 1_{(\Gamma, u:\mathbb{U})}$ is exactly what is asserted by FF:CTX-APP:NIL. The fact that $[\forall (v/u)]\mathsf{app}_{(\Gamma, u:\mathbb{U}, \delta:\Delta)} = 1_{(\Gamma, \forall u.(\delta:\Delta))}$ is exactly what is asserted by FF:CTX-FORALL:FMAP:CTX-APP.

With the unit and co-unit for the adjunction $(-, u : \mathbb{U}) \dashv [\forall u]$ on contexts in place, we can now state the $\beta$- and $\eta$-rules of the transpension type (FF:TRANSP:BETA, FF:TRANSP:ETA) parallel to those for the modal type in MTT (Proposition 3.3).

We now show (2) from above, i.e. assuming $\Delta$ lists a variable $y : B$, we seek to derive a term $\Gamma, \forall u.(\delta : \Delta) \vdash t : \forall v.B[\sigma]$. This can be done using FF:CTX-APP as follows:

$$\frac{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash y : B}{\Gamma, \forall u.(\delta : \Delta), v : \mathbb{U} \vdash y[v/u, (\lambda u.\delta) v/\delta] : B[v/u, (\lambda u.\delta) v/\delta]}\frac{\Gamma, \forall u.(\delta : \Delta) \vdash \lambda v.(y[v/u, (\lambda u.\delta) v/\delta]) : \forall v.(B[v/u, (\lambda u.\delta) v/\delta])}.$$

**Definition 2.1.** For any variable $y : B$ in telescope $\Delta$, we define $\Gamma, \forall u.(\delta : \Delta) \vdash \lambda u.y := \lambda v.(y[v/u, (\lambda u.\delta) v/\delta]) : \forall v.(B[v/u, (\lambda u.\delta) v/\delta])$.

**Proposition 2.2.** *For any variable $y : B$ in telescope $\Delta$ and any substitution $(1_\Gamma, u/u, \tau/\delta) : (\Gamma, u : \mathbb{U}, \delta' : \Delta') \rightarrow (\Gamma, u : \mathbb{U}, \delta : \Delta)$, we have*

$$\Gamma \vdash (\lambda u.y)[\lambda u.\tau/\lambda u.\delta] = \lambda u.(\tau_y[u/u, (\lambda u.\delta') u/\delta']) : \forall u.B[\tau/\delta],$$

*where $\tau_y = y[\tau/\delta]$ is the component of the vector $\tau$ for variable $y$.*

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:11

Proof. We have

$$\begin{array}{l} (\lambda u.y)[u/u, \tau/\delta] = (\lambda u.y[u/u, (\lambda u.\delta) u/\delta])[\lambda u.\tau/\lambda u.\delta] \quad \text{(Definition 2.1)} \\ = \lambda u.(y[u/u, (\lambda u.\delta) u/\delta][\lambda u.\tau/\lambda u.\delta, u/u]) \\ = \lambda u.(y[u/u, \tau/\delta][u/u, (\lambda u.\delta') u/\delta']) \quad \text{(FF:CTX-APP:NAT)} \\ = \lambda u.(\tau_y[u/u, (\lambda u.\delta') u/\delta']). \end{array}$$

Corollary 2.3. For any variable $y : B$ in telescope $\Delta$ and any substitution $(1_\Gamma, u/u, \tau/\delta) : (\Gamma, u : \mathbb{U}) \to (\Gamma, u : \mathbb{U}, \delta : \Delta)$, we have $\Gamma \vdash (\lambda u.y)[\lambda u.\tau/\lambda u.\delta] = \lambda u.\tau_y : \forall u.B[\tau/\delta]$, where $\tau_y = y[\tau/\delta]$ is the component of the vector $\tau$ for variable $y$.

Proof. This follows from FF:CTX-APP:NIL.

2.1.7. Discussion. The type system presented above is less general than the paper's main system MTraS. In Section 2.1.6, we saw that the unit of the adjunction on contexts is invertible. This is equivalent to the left adjoint $(-, u : \mathbb{U}) : \text{Ctx} \to \text{Ctx}/(u : \mathbb{U})$ being fully faithful [nLa23a], and the requirement on presheaf models to support the typing rules in the current section (with FF:CTX-FORALL:NIL an isomorphism) is exactly that: the multiplier functor interpreting $(-, u : \mathbb{U})$ has to be fully faithful w.r.t. the slice category over $(u : \mathbb{U})$.

By uniqueness of the adjoint, we can also conclude that the co-unit of the adjunction $\forall u \dashv \mathfrak{g}[u]$ is invertible,⁵ which is equivalent to the right adjoint $\mathfrak{g}[u]$ being fully faithful [nLa23c], whence the section title.

However, the current typing rules become unusable in a more general setting, as well as in more specific settings where we may start adding operations that we need in important applications. First, we have no story for substitutions which exist in cubical type systems such as endpoints $(0/i) : \Gamma \to (\Gamma, i : \mathbb{I})$ [BCM15, BCH14, CCHM17] or connections $(j \wedge k/i) : (\Gamma, j, k : \mathbb{I}) \to (\Gamma, i : \mathbb{I})$ [CCHM17], as there is no formation rule for $\mathfrak{g}[0]A$ or $\mathfrak{g}[j \wedge k]A$. Secondly, in non-fully-faithful generalizations featuring the contraction rule for shape variables, the transpension is not stable under substitution of the shape variables preceding $u$, so in those settings the way we internalized the transpension type here was too naïve.⁶ In order to obtain a type system that does not fail in the presence of endpoints, connections or shape variable contraction, in the rest of the paper we will rely on MTT, which we briefly summarize in Section 3.

2.2. Poles. We can still try to get a grasp on $\mathfrak{g}[0]A$ in cubical type systems, however. In general we have $T[0/i] \cong (\forall i.(i \equiv_{\mathbb{I}} 0) \to T)$. Assuming $T = \mathfrak{g}[i]A$ and onelsNotZero : $(1 \equiv_{\mathbb{I}} 0) \to \text{Empty}$, the latter type is inhabited by

$$\text{pole}_0 := \lambda i.\lambda e.\text{mer}[i] \text{ (case (onelsNotZero $((\lambda i.e) 1)$) of \{\})} : \forall i.(i \equiv_{\mathbb{I}} 0) \to \mathfrak{g}[i]A$$

where $\lambda i.e$ has type $\forall i.(i \equiv_{\mathbb{I}} 0)$. Moreover, using the $\eta$-rules for functions and the transpension type and a (provable propositional) $\eta$-rule for Empty, we can show that this is the only

⁵In fact, this is exactly what the $\beta$- and $\eta$-rules of the transpension type say (when $\Delta$ is empty).

⁶Indeed, write $\Omega[u]$ for the operation of cartesian weakening over a shape variable $u : \mathbb{U}$, which is an example of a substitution involving shape variables. If in general $\Omega[u] \circ \mathfrak{g}[v] \cong \mathfrak{g}[v] \circ \Omega[u]$, then by uniqueness of the left adjoint we would find that $\Pi v \circ \Sigma u \cong \Sigma u \circ \Pi v$. This is clearly false for cartesian shapes such as the interval $\mathbb{I}$ in HoTT. For more information on how the transpension type commutes with other operations, see the technical report [Nuy20b].

16:12

A. NUYTS AND D. DEVRIESE

Vol. 20:2

element. Thus we see that the transpension type essentially consists of one meridian $(i : \mathbb{I}) \to [i]T$ for every $t : T$, and that these meridians are all equal to $\mathsf{pole}_0$ at $i = 0$ and analogously to $\mathsf{pole}_1$ at $i = 1$. This makes the transpension type quite reminiscent of a dependent version of the suspension type from HoTT [Uni13], although the quantification of the context in the formation and construction rules is obviously a distinction.

2.3. **Internal transposition.** We can internally show that the following types are isomorphic:$^7$

$$(\forall(u : \mathbb{U}).A) \to B \cong \forall(u : \mathbb{U}).(A \to [u]B).$$

Indeed, given $f : (\forall(u : \mathbb{U}).A) \to B$, we can define $g : \forall(u : \mathbb{U}).(A \to [u]B)$ by

$$g\,u\,a = \mathsf{mer}[u](f(\lambda u.a)).$$

Conversely, given $g : \forall(u : \mathbb{U}).(A \to [u]B)$, we can define $f : (\forall(u : \mathbb{U}).A) \to B$ by

$$f\,\hat{a} = \mathsf{unmer}(u.g\,u\,(\hat{a}\,u)).$$

These constructions are mutually inverse. Indeed, plugging the definition of $f$ into that of $g$, we find in context $(\Gamma, u : \mathbb{U}, a : A)$:

$$\mathsf{mer}[u]\,(\mathsf{unmer}(u.g\,u\,(\lambda u.a)\,u))) = \mathsf{mer}[u]\,(\mathsf{unmer}(u.(g\,u\,a)[u/u,(\lambda u.(a))\,u/(a)])) = g\,u\,a$$

using the $\eta$-rule of the transpension type. Conversely, plugging $g$ into $f$, we find in context $(\Gamma, \hat{a} : \forall u.A)$:

$$\begin{aligned} &\mathsf{unmer}(u.\,(\mathsf{mer}[u]\,(f(\lambda u.a)))\,[u/u, \hat{a}\,u/a]\,) \\ &= \mathsf{unmer}(u.(\mathsf{mer}[u]\,(\,(f(\lambda u.a))[\lambda u.(\hat{a}\,u)/\lambda u.(a)]\,))) \quad \text{(FF:TRANSP:INTRO:NAT)} \\ &= \mathsf{unmer}(u.(\mathsf{mer}[u]\,(\,(f(\lambda u.\hat{a}\,u))\,))) \quad \text{(Corollary 2.3)} \\ &= f(\lambda u.(\hat{a}\,u)) = f\,\hat{a}. \quad \text{(FF:TRANSP:BETA)} \end{aligned}$$

2.4. **Higher-dimensional pattern matching.** Now that we know internally that $\forall u$ is a left adjoint (with internal right adjoint $[u]$), we can proceed to conclude that it preserves colimits, e.g. we can show $i : (\forall u.A \uplus B) \cong (\forall u.A) \uplus (\forall u.B)$. The map to the left is trivially defined by case analysis. The map to the right is equivalent by transposition to a function $\forall u.(A \uplus B \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,)))$. This is in turn constructed by case analysis from the transpositions of the coproduct's constructors $\mathsf{inl}$ and $\mathsf{inr}$.

By straightforward application of Section 2.3, the transpositions of the constructors are:

$$\lambda u.\lambda a.\mathsf{mer}[u]\,(\mathsf{inl}\,(\lambda u.a)) : \forall u.(A \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,)))$$

$$\lambda u.\lambda b.\mathsf{mer}[u]\,(\mathsf{inr}\,(\lambda u.b)) : \forall u.(B \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,)))$$

Pasting these together, we get

$$\begin{aligned} \lambda u.\lambda c.\mathsf{case}\,c\,\mathsf{of} &\left\{\begin{array}{ll} \mathsf{inl}\,a & \mapsto \mathsf{mer}[u]\,(\mathsf{inl}\,(\lambda u.a)) \\ \mathsf{inr}\,b & \mapsto \mathsf{mer}[u]\,(\mathsf{inr}\,(\lambda u.b)) \end{array}\right\} \\ &: \forall u.(A \uplus B \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,))). \end{aligned}$$

Transposing again as in Section 2.3, we find

$$i : (\forall u.A \uplus B) \to (\forall u.A) \uplus (\forall u.B)$$

$^7$This statement of internal transposition is not parallel to the general MTT one (Proposition 3.4). The current variation is provable from the general result because the right adjoint $[u]$ is fully faithful.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:13

$$i \hat{c} = \text{unmer} \left( u.\text{case} \hat{c} u \text{ of} \left\{ \begin{array}{l} \text{inl } a \mapsto \text{mer}[u] (\text{inl } (\lambda u.a)) \\ \text{inr } b \mapsto \text{mer}[u] (\text{inr } (\lambda u.b)) \end{array} \right\} \right).$$

Let us consider our categorically motivated creation from a more type-theoretical perspective. We obtain an argument $\hat{c} : \forall u.A \uplus B$ which we would like to pattern match on, in order to create an element of type $(\forall u.A) \uplus (\forall u.B)$. Of course we cannot pattern match on a function, so we call the unmer constructor which brings $u : \mathbb{U}$ in scope and changes the goal to $\langle [u] ((\forall v.A[v/u]) \uplus (\forall v.B[v/u]))$. We can then reduce $\hat{c}$ by one dimension by applying it to $u$, allowing a case analysis. The first case brings in scope $a : A$ (and the second case will be analogous), so we are in context $(\Gamma, \hat{c} : \forall u.A \uplus B, u : \mathbb{U}, a : A)$. We then use the meridian constructor, which again removes $u$ from scope, turns $a : A$ into a function $\lambda u.a : \forall u.A$ and again reduces the goal to $(\forall u.A) \uplus (\forall u.B)$, so that inl completes the proof. We have essentially pattern matched on a higher-dimensional object!

Let us now check that $i$ is indeed inverse to the trivial implementation of $i^{-1}$. We have:

$$\begin{array}{l} (i \circ i^{-1})(\text{inl } \hat{a}) = i(\lambda u.\text{inl } (\hat{a} u)) \\ = \text{unmer}(u. (\text{mer}[u] (\text{inl } (\lambda u.a)))[u/u, \hat{a} u/a] ) \\ = \text{unmer}(u.(\text{mer}[u] (\text{inl } (\lambda u.a)[\lambda u.\hat{a} u/\lambda u.a] )))) \quad \text{(FF:TRANSP:INTRO:NAT)} \\ = \text{unmer}(u.(\text{mer}[u] (\text{inl } (\lambda u.\hat{a} u)))) \quad \text{(Corollary 2.3)} \\ = \text{inl } \hat{a}. \quad \text{(FF:TRANSP:BETA)} \end{array}$$

and similar for $(i \circ i^{-1})(\text{inr } \hat{b})$. Using the technique of higher dimensional pattern matching just developed, we can prove the other equation also by pattern matching! By similar steps as before, we have:

$$\begin{array}{l} (i^{-1} \circ i)(\lambda u.\text{inl } (\hat{a} u)) = i^{-1}(\text{unmer}(u. (\text{mer}[u] (\text{inl } (\lambda u.a)))[u/u, \hat{a} u/a] )) \\ = i^{-1}(\text{unmer}(u.(\text{mer}[u] (\text{inl } \hat{a})))) = i^{-1}(\text{inl } \hat{a}) = \lambda u.\text{inl } (\hat{a} u), \end{array}$$

and a similar result for $(i^{-1} \circ i)(\lambda u.\text{inr } (\hat{b} u))$.

### 3. MULTIMODE TYPE THEORY

As announced, we will rely on the extensional version of Gratzer et al.'s multimode and multimodal dependent type system MTT [GKNB21, GKNB20a] in order to frame the transpension and its left adjoints as modal operators. We refer to the original work for details, but give a brief overview in the current section. In Section 3.4, we decorate the usual MTT notation with reminders of the modalities' semantic left adjoints, which are syntactically obscured by the lock notation.

3.1. The mode theory. MTT is parametrized by a mode theory, which is a strict 2-category whose objects, morphisms and 2-cells we will refer to as modes, modalities and, well, 2-cells respectively. Semantically, every mode $p$ will correspond to an entire model of dependent type theory $[[p]]$. A modality $\mu : p \to q$ will consist of a functor $[[\widehat{\bullet}_\mu] : [[q]] \to [[p]]$ acting on contexts and substitutions, and an operation $[[\mu]]$ that is almost a dependent right adjoint (DRA [BCM$^{+}$20]) to $[[\widehat{\bullet}_\mu]]$; for all our purposes it will be an actual DRA and even one arising from a weak CwF morphism [BCM$^{+}$20, lemma 17][Nuy18a]. A 2-cell $\alpha : \mu \Rightarrow \nu$ is interpreted as a natural transformation $[[\widehat{\bullet}_\alpha] : [[\widehat{\bullet}_\nu]] \to [[\widehat{\bullet}_\mu]]$ and hence also gives rise to an appropriate transformation $[[\alpha] : [[\mu]] \to [[\nu]]$.

16:14

A. Nuyts and D. Devriese

Vol. 20:2

Judgement forms:

| p | Γ ctx | Γ is a context at mode p, |
| --- | --- | --- |
| p | σ : Δ → Γ | σ is a simultaneous substitution from Δ to Γ at mode p, |
| p | Γ ⊢ T type | T is a type in context Γ at mode p, |
| p | Γ ⊢ t : T | t has type T in context Γ at mode p. |

Figure 2: Judgement forms of MTT [GKNB21].

#### The type theory at each mode:

Basic rules of dependent type theory (including all desired types) at each mode q, e.g.:

| CTX-EMPTY | CTX-EXT | CTX-EXT:INTRO |
| --- | --- | --- |
| q mode | q | Γ ⊢ T type | q | σ : Δ → Γ q | Δ ⊢ t : T[σ] |
| q | · ctx | q | Γ, x : T ctx | q | (σ, t/x) : Δ → (Γ, x : T)where τ = ((x/∅) ∘ τ, x[τ]/x)(σ, t/x) ∘ ρ = (σ ∘ ρ, t[ρ]/x) |

|  CTX-EXT:WKN | CTX-EXT:VAR | SIGMA  |
| --- | --- | --- |
|  \( q \mid \Gamma \text{ ctx} \quad q \mid \Gamma \vdash T \text{ type} \) | \( q \mid \Gamma \text{ ctx} \quad q \mid \Gamma \vdash T \text{ type} \) | \( q \mid \Gamma \vdash A \text{ type} \)  |
|  \( q \mid (x/\emptyset) : (\Gamma, x : T) \to \Gamma \) | \( q \mid \Gamma, x : T \vdash x : T[(x/\emptyset)] \) | \( q \mid \Gamma, x : A \vdash B \text{ type} \)  |
|  where \( (x/\emptyset) \circ (\sigma, t/x) = \sigma \) | where \( x[\sigma, t/x] = t \) | \( q \mid \Gamma \vdash (x : A) \times B \text{ type} \)  |
|  UNI | UNI:ELIM | UNI:INTRO  |
|  \( q \mid \Gamma \text{ ctx} \quad \ell \in \mathbb{N} \) | \( q \mid \Gamma \vdash t : \mathsf{U}_{\ell}^{q} \) | \( q \mid \Gamma \vdash T \text{ type}_{\ell} \)  |
|  \( q \mid \Gamma \vdash \mathsf{U}_{\ell}^{q} \text{ type}_{\ell+1} \) | \( q \mid \Gamma \vdash \mathsf{El}(t) \text{ type}_{\ell} \) | \( q \mid \Gamma \vdash \lceil T \rceil : \mathsf{U}_{\ell}^{q} \)  |
|   | where \( \mathsf{El}(\lceil T \rceil) = T \) | where \( \lceil \mathsf{El}(t) \rceil = t \)  |

Figure 3: MTT includes all rules of ordinary DTT at each mode.

3.2. Judgement forms. The judgement forms of MTT are listed in Fig. 2. All forms are annotated with a mode p which specifies in what category they are to be interpreted. Every judgement form also has a corresponding equality judgement, which is respected by everything as the typing rules are to be read as a specification of a generalized algebraic theory (GAT [Car86, AK16]). The statements p mode and  \( \mu: p \rightarrow q \)  and  \( \alpha: \mu \Rightarrow \nu \)  are simply requirements about the mode theory. This means we give no syntax or equality rules for modalities and 2-cells: these are fixed by the choice of mode theory.

3.3. Typing rules. The typing rules are listed in Figs. 3 to 6 and discussed below.

3.3.1. The type theory at each mode. Since every mode corresponds to a model of all of dependent type theory (DTT), we start by importing all the usual typing rules of DTT, to be applied in MTT at any given fixed mode. Some examples of such rules are given in Fig. 3, where we have consciously included rules for non-modal context extension, even though these will be generalized to modal rules later on. One reason to do so is that other rules of DTT, such as SIGMA, depend on these and therefore cannot be imported without. Another is that this way, we have a warm-up towards the modal rules and in particular we

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:15

WDRA

\[
\begin{array}{l} \mu : p \to q \\ \frac {p \mid \Gamma , \widehat {\mathbf {u}} _ {\mu} \vdash A \text {type} _ {\ell}}{q \mid \Gamma \vdash \langle \mu \mid A \rangle \text {type} _ {\ell}} \end{array}
\]

WDRA:ELIM

\[
\mu : p \to q \quad \nu : q \to r
\]

\[
q \mid \Gamma , \widehat {\mathbf {u}} _ {\nu} \vdash \hat {a}: \langle \mu \mid A \rangle
\]

\[
r \mid \Gamma , \nu \mid \hat {x}: \langle \mu \mid A \rangle \vdash C \text {type}
\]

WDRA:INTRO

\[
\begin{array}{l} \mu : p \to q \\ \frac {p \mid \Gamma , \widehat {\mathbf {u}} _ {\mu} \vdash a : A}{q \mid \Gamma \vdash \mathsf {m o d} _ {\mu} a : \langle \mu \mid A \rangle} \end{array}
\]

\[
r \mid \Gamma , \nu \circ \mu \mid x: A \vdash c: C [ \mathsf {m o d} _ {\mu} x / \hat {x} ]
\]

\[
r \mid \Gamma \vdash \operatorname{let} _ {\nu} (\operatorname{mod} _ {\mu} x = \hat {a}) \text {in} c: C [ \hat {a} / \hat {x} ]
\]

\[
\text { where } \operatorname{let} _ {\nu} (\operatorname{mod} _ {\mu} x = \operatorname{mod} _ {\mu} a) \text { in } c = c [ a / x ]
\]

Figure 4: Typing rules for MTT's modal types (weak DRAs) [GKNB21][Nuy20a, fig. 5.6].

can make a point about de Bruijn indices. Although variables in Fig. 3 are named, the rules CTX-EXT:WKN and CTX-EXT:VAR effectively enforce a de Bruijn discipline, where we can only name the last variable in the context and have to weaken explicitly if it is deeper down, e.g.

\[
x: A, y: B, z: C \vdash x [ (y / \emptyset) ] [ (z / \emptyset) ]: A [ (x / \emptyset) ] [ (y / \emptyset) ] [ (z / \emptyset) ].
\]

We take the viewpoint \( ^{8} \) that the official system is unnamed and uses this substitution-based de Bruijn discipline to refer to variables. In order to improve human communication, we will name variables anyway and use the resulting redundancy to leave weakening substitutions implicit unambiguously. This allows for the following unofficial admissible ‘rule’

CTX-EXT:VAR:LOOKUP

\[
\frac {q \mid \Gamma , x : T , \Delta \mathsf {c t x}}{q \mid \Gamma , x : T , \Delta \vdash x : T}.
\]

Furthermore, we use other common notational conventions such as writing \((t / x)\) instead of \((\mathrm{id}_{\Gamma}, t / x): \Gamma \to (\Gamma, x: T)\).

We assume that DTT has a universe à la Coquand with mutually inverse encoding and decoding operations (which we will henceforth suppress), and we ignore cumulativity-related hassle, referring to Gratzer et al. [GKNB21] for details.

3.3.2. Modal types, part 1. Before proceeding to the MTT-specific structural rules, let us first have a look at the formation and introduction rules WDRA and WDRA:INTRO of modal types \(\langle \mu |A\rangle\) in Fig. 4. These are not unlike the formation and introduction rules of the transpension type in Fig. 1 and work by transposition: we apply the left adjoint of the modality \(\mu\) (in the form of a lock) to the premise's context. As such, they behave like DRAs, but their elimination rule WDRA:ELIM (which we consider later) is weaker, so we call them weak DRAs.

3.3.3. Structural rules. The structural rules of MTT are listed in Fig. 5. Context formation starts with the empty context which exists at any mode, and proceeds by adding locks and variables.

\( ^{8} \) as is done in the MTT technical report [GKNB20a]; the paper [GKNB21] speaks from a more implementation-oriented perspective.

16:16

A. NUYTS AND D. DEVRIESE

Vol. 20:2

### Context locking:

Note: We write  \( (\sigma,\mathbf{\Phi}_{\mu}) \)  as shorthand for  \( (\sigma,\mathbf{Q}_{1:\mu\Rightarrow\mu}) \) , an instance of LOCK:FMAP.

|  LOCK\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \) | LOCK:FMAP\( q \mid \sigma : \Gamma \to \Delta \quad \mu, \nu : p \to q \quad \alpha : \mu \Rightarrow \nu \)  |
| --- | --- |
|  \( p \mid \Gamma, \mathbf{\Phi}_{\mu} \text{ ctx} \) | \( p \mid (\sigma, \mathbf{Q}_{\alpha}) : (\Gamma, \mathbf{\Phi}_{\nu}) \to (\Delta, \mathbf{\Phi}_{\mu}) \)  |
|  where \( \Gamma = (\Gamma, \mathbf{\Phi}_{1}) \) | where \( \sigma = (\sigma, \mathbf{Q}_{1:1 \Rightarrow 1}) \quad (\sigma, \mathbf{Q}_{\alpha'}, \mathbf{Q}_{\alpha}) = (\sigma, \mathbf{Q}_{(\alpha' \star \alpha)}) \)  |
|  \( (\Gamma, \mathbf{\Phi}_{\nu}, \mathbf{\Phi}_{\mu}) = (\Gamma, \mathbf{\Phi}_{\nu \circ \mu}) \) | \( 1 = (1, \mathbf{Q}_{1:\mu \Rightarrow \mu}) \quad (\sigma, \mathbf{Q}_{\alpha}) \circ (\tau, \mathbf{Q}_{\beta}) = (\sigma \circ \tau, \mathbf{Q}_{(\beta \circ \alpha)}) \)  |

### Modal context extension:

We consider the non-modal rule CTX-EXT and its introduction, elimination and computation rules as a special case of CTX-MODEXT for p = q and  \( \mu = 1 \) .

|  CTX-MODEXT\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \)\( p \mid \Gamma, \mathbf{\Phi}_{\mu} \vdash T \text{ type } \)\( \overline{q \mid \Gamma, \mu \mid x : T \text{ ctx}} \) | CTX-MODEXT:INTRO\( q \mid \sigma : \Delta \to \Gamma \quad \mu : p \to q \)\( p \mid \Delta, \mathbf{\Phi}_{\mu} \vdash t : T[\sigma, \mathbf{\Phi}_{\mu}] \)\( \overline{q \mid (\sigma, t/x) : \Delta \to (\Gamma, \mu \mid x : T)} \)where \( \tau = ((x/\emptyset) \circ \tau, x[\tau, \mathbf{\Phi}_{\mu}] / x) \)\( (\sigma, t/x) \circ \rho = (\sigma \circ \rho, t[\rho, \mathbf{\Phi}_{\mu}] / x) \)  |
| --- | --- |
|  CTX-MODEXT:WKN\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \)\( p \mid \Gamma, \mathbf{\Phi}_{\mu} \vdash T \text{ type } \)\( \overline{q \mid (x/\emptyset) : (\Gamma, \mu \mid x : T) \to \Gamma} \)where \( (x/\emptyset) \circ (\sigma, t/x) = \sigma \) | CTX-MODEXT:VAR\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \)\( p \mid \Gamma, \mathbf{\Phi}_{\mu} \vdash T \text{ type } \)\( \overline{q \mid \Gamma, \mu \mid x : T, \mathbf{\Phi}_{\mu} \vdash x : T[(x/\emptyset), \mathbf{\Phi}_{\mu}]} \)where \( \Delta, \mathbf{\Phi}_{\mu} \vdash x[\sigma, t/x, \mathbf{\Phi}_{\mu}] = t : T[\sigma, \mathbf{\Phi}_{\mu}] \)  |

Figure 5: Structural rules of MTT [GKNB21][Nuy20a, fig. 5.5].

Adding locks (LOCK) is strictly functorial: it preserves identity and composition of modalities. In fact, it is strictly 2-functorial: it also has an action on 2-cells (LOCK:FMAP, producing substitutions between locked contexts) that preserves identity and composition of 2-cells. It is also strictly bifunctorial: we can combine a substitution and a 2-cell to a substitution between locked contexts. If the 2-cell is the identity, then we write \(\mathbf{\Phi}_{\mu}\) for \(\mathbf{Q}_{1:\mu \Rightarrow \mu}\).

A modal variable  \( \mu \mid x : T \)  introduced by CTX-MODEXT is essentially the same as a non-modal variable  \( \hat{x} : \langle \mu \mid T \rangle \)  (which in turn is shorthand for  \( 1 \mid \hat{x} : \langle \mu \mid T \rangle \) ), but the judgemental modal annotation allows direct access to a variable of type A through the variable rule. Hence, the type T is checked the same way as it would be in  \( \langle \mu \mid T \rangle \) . Terms t substituted for a modal variable x are also checked in the locked context, as if we would be substituting  \( mod_{\mu} t \)  instead. The variable rule does not produce  \( x : \langle \mu \mid T \rangle \)  but instead uses transposition to move the modality  \( \mu \)  to the left in the form of a lock. As such, it can be seen as implicitly involving a co-unit.

By analogy with CTX-EXT:VAR:LOOKUP, we would like a more general unofficial variable 'rule' that allows accessing a variable \( x \) that is buried under a general telescope \( \Delta \) rather than a single lock. By LOCK:FMAP, we can weaken under locks (which, like ordinary weakening, we will leave notationally implicit), so we can easily remove all variables from \( \Delta \) and then apply strict functoriality of LOCK to fuse the remaining locks, obtaining a single lock \( \mathbf{\Phi}_{\mathrm{locks}(\Delta)} \), where the modality \( \mathrm{locks}(\Delta) \) is defined as follows:

\[
\operatorname{locks} (\cdot) = 1, \quad \operatorname{locks} (\Delta , \mathbf {\Phi} _ {\mu}) = \operatorname{locks} (\Delta) \circ \mu , \quad \operatorname{locks} (\Delta , \mu \mid x: T) = \operatorname{locks} (\Delta).
\]

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:17

MODPI

\[
\begin{array}{l} p \mid \Gamma , \widehat {\mathbf {a}} _ {\mu} \vdash A \text {type} _ {\ell} \quad \mu : p \to q \\ q \mid \Gamma , \mu \mid x: A \vdash B \text {type} _ {\ell} \\ \hline q \mid \Gamma \vdash (\mu \mid x: A) \rightarrow B \text {type} _ {\ell} \end{array}
\]

MODPI:INTRO

\[
\begin{array}{l} \mu : p \to q \\ q \mid \Gamma , \mu \mid x: A \vdash b: B \\ \hline q \mid \Gamma \vdash \lambda (\mu \mid x). b: (\mu \mid x: A) \to B \\ \text { where } \lambda (\mu \mid x). (f \cdot_ {\mu} x) = f \end{array}
\]

MODPI:ELIM

\[
\begin{array}{l} q \mid \Gamma \vdash f: (\mu \mid x: A) \rightarrow B \\ p \mid \Gamma , \widehat {\mathbf {a}} _ {\mu} \vdash a: A \quad \mu : p \to q \\ \hline q \mid \Gamma \vdash f \cdot_ {\mu} a: B [ a / x ] \\ \text { where } (\lambda (\mu \mid x). b) \cdot_ {\mu} a = b [ a / x ] \end{array}
\]

Figure 6: Typing rules for MTT's modal \(\Pi\)-types [GKNB21][Nuy20a, fig. 5.7] (of which non-modal \(\Pi\)-types are a special case for \(p = q\) and \(\mu = 1\)).

Then the only remaining thing we need is a 2-cell \(\alpha : \mu \Rightarrow \text{locks}(\Delta)\). This leads to the following admissible variable 'rule'

CTX-MODEXT:VAR:LOOKUP

\[
\begin{array}{l} q \mid \Gamma \text { ctx } \quad \mu : p \to q \\ p \mid \Gamma , \widehat {\mathbf {a}} _ {\mu} \vdash T \text {type} \quad \alpha : \mu \Rightarrow \operatorname{locks} (\Delta) \\ \hline q \mid \Gamma , \mu \mid x: T, \Delta \vdash x _ {\alpha}: T [ \mathrm{id} _ {\Gamma}, \widehat {\mathbf {a}} _ {\alpha} ] \end{array}
\]

where \(x_{\alpha}\) is defined as \(x[\mathrm{id}_{(\Gamma, \mu : x:T)}, \widehat{\mathbf{a}}_{\alpha : \mu \Rightarrow \mathrm{locks}(\Delta)}]\), leaving the necessary weakenings under locks implicit. Substitution is then given by

\[
\begin{array}{l} x _ {\alpha} \left[ \mathrm{id} _ {\Gamma}, a / x, \mathrm{id} _ {\Delta} \right] = x \left[ \mathrm{id} _ {(\Gamma , \mu : x: T)}, \widehat {\mathbf {a}} _ {\alpha} \right] \left[ \mathrm{id} _ {\Gamma}, a / x, \mathrm{id} _ {\Delta} \right] \\ = x \left[ \mathrm{id} _ {\Gamma}, a / x, \widehat {\mathbf {a}} _ {\mu} \right] \left[ \mathrm{id} _ {\Gamma}, \widehat {\mathbf {a}} _ {\alpha} \right] \\ = a [ \mathrm{id} _ {\Gamma}, \widehat {\mathbf {a}} _ {\alpha} ], \\ \end{array}
\]

or more briefly \(x_{\alpha}[a / x] = a[\widehat{\mathbf{a}}_{\alpha}]\).

3.3.4. Modal types, part 2. Modal elimination (WDRA:ELIM, Fig. 4) uses a let-syntax to turn the modal type into a judgemental annotation on a variable.

3.3.5. Modal function types. Modal function type formation and introduction (Fig. 6) are by simple abstraction. Modal function application checks the argument in a locked context, just like modal variable substitution does.

3.4. Left adjoint reminders. In MTT, we can on one hand apply a modality \(\mu : p \to q\) to a type \(T\) to obtain a modal type \(\langle \mu | T \rangle\), and on the other hand we can apply its left adjoint \(\widehat{\mathbf{a}}_{\mu}\) to a context \(\Gamma\) to obtain \(\Gamma, \widehat{\mathbf{a}}_{\mu}\). Type-theoretically, it is only sensible that the lock \(\widehat{\mathbf{a}}_{\mu}\) mentions \(\mu\) for \(\mu\) is a premise of the LOCK rule. From a semantic/categorical viewpoint however, the indirection of mentioning \(\mu\) when you are actually talking about some left adjoint functor \(K = [\widehat{\mathbf{a}}_{\mu}]\) to \(M = [\mu]\) can really get in the way of understanding what is going on.

16:18

A. NUYTS AND D. DEVRIESE

Vol. 20:2

For example, in Section 6, we will come up with a modality $\mathfrak{g}[u]$ for the transpension, and then the introduction rule WDRA:INTRO will take the form

$$\frac{p \mid \Delta, \mathbf{\Omega}_{\mathfrak{g}[u]} \vdash t : T}{q \mid \Delta \vdash \text{mod}_{\mathfrak{g}[u]} t : \langle \mathfrak{g}[u] \mid T \rangle}$$

for certain modes $p$ and $q$, which is quite reminiscent of the introduction rule of the transpension type in FFTraS (Section 2) if you bear in mind that $[\mathbf{\Omega}_{\mathfrak{g}[u]}]$ is essentially $\forall u$.

Instead of littering this paper with remarks of the form 'recall that $[\mathbf{\Omega}_{\mu}] = \ldots'$, we will decorate locks, keys and variables with superscript reminders of the left adjoints to the modalities (and 2-cells mediating them) that are already in subscript. Concretely, we will assign:

- to every modality $\mu : p \to q$ a left name $\kappa : q \to p$ (writing this succinctly as $\kappa \dashv \mu : p \to q$),
- to every 2-cell $\alpha : \mu \Rightarrow \mu'$ a left name $\omega : \kappa' \Rightarrow \kappa$ (where $\kappa \dashv \mu$ and $\kappa' \dashv \mu'$; writing succinctly $\kappa \Leftarrow \kappa' : \omega \dashv \alpha : \mu \Rightarrow \mu'$).

Of course if $\kappa' \dashv \mu'$ and $\kappa \dashv \mu$, then the composite will be $\kappa \circ \kappa' \dashv \mu' \circ \mu$. If a modality $\mu$ has a left adjoint modality $\nu$, then we will always use $\nu$ as the left name of $\mu$, and similar for 2-cells. Then, we can write $\mathbf{\Omega}_{\mu}^{\kappa}$ for $\mathbf{\Omega}_{\mu}$, and $\mathbf{\alpha}_{\alpha:\mu\Rightarrow\mu'}^{\omega:\kappa'\Rightarrow\kappa}$ or just $\mathbf{\alpha}_{\alpha}^{\omega}$ for $\mathbf{\alpha}_{\alpha:\mu\Rightarrow\mu'}$, and $x_{\alpha:\mu\Rightarrow\mu'}^{\omega:\kappa'\Rightarrow\kappa}$ or just $x_{\alpha}^{\omega}$ for $x_{\alpha:\mu\Rightarrow\mu'}$. Note that we have

$$(\Gamma, \mathbf{\Omega}_{\mu_1}^{\kappa_1}, \mathbf{\Omega}_{\mu_2}^{\kappa_2}) = (\Gamma, \mathbf{\Omega}_{\mu_1 \circ \mu_2}^{\kappa_2 \circ \kappa_1}), \quad (\sigma, \mathbf{\alpha}_{\alpha_1}^{\omega_1}, \mathbf{\alpha}_{\alpha_2}^{\omega_2}) = (\sigma, \mathbf{\alpha}_{\alpha_1 * \alpha_2}^{\omega_2 * \omega_1}), \quad a[\mathbf{\alpha}_{\alpha}^{\omega}][\mathbf{\alpha}_{\beta}^{\psi}] = a[\mathbf{\alpha}_{\beta \circ \alpha}^{\omega \circ \psi}]. \tag{3.1}$$

3.5. Results. We highlight some results about MTT that are relevant in the current paper.

Proposition 3.1. We have $\langle 1 \mid A \rangle \cong A$ and $\langle \nu \circ \mu \mid A \rangle \cong \langle \nu \mid \langle \mu \mid A \rangle \rangle$.

Proposition 3.2. For any 2-cell $\alpha : \mu \Rightarrow \nu$, we have $\langle \mu \mid A \rangle \to \langle \nu \mid A[\mathbf{\alpha}_{\alpha}] \rangle$.

Proposition 3.3 (Projection). If $\kappa \dashv \mu$ internal to the mode theory, with unit $\eta : 1 \Rightarrow \mu \circ \kappa$ and co-unit $\varepsilon : \kappa \circ \mu \Rightarrow 1$, then there is a function $\varepsilon : (\kappa \mid \langle \mu \mid A \rangle) \to A[\mathbf{\alpha}_{\varepsilon}]$, satisfying a $\beta$-and (thanks to extensionality) an $\eta$-law:

$$\varepsilon \cdot_{\kappa} (\text{mod}_{\mu} a) = a[\mathbf{\alpha}_{\varepsilon}], \qquad \hat{a} = \text{mod}_{\mu} (\varepsilon \cdot_{\kappa} (\hat{a}[\mathbf{\alpha}_{\eta}])).$$

Combined with these rules, $\varepsilon$ is equally expressive as the let-eliminator for $\langle \mu \mid \sqcup \rangle$.

Proposition 3.4 (Internal transposition). Let $\kappa \dashv \mu$ internal to the mode theory, with unit $\eta : 1 \Rightarrow \mu \circ \kappa$ and co-unit $\varepsilon : \kappa \circ \mu \Rightarrow 1$. Adding left names, we get $\zeta \dashv \kappa \dashv \mu$ with $1 \Leftarrow \zeta \circ \kappa : \varepsilon' \dashv \eta : 1 \Rightarrow \mu \circ \kappa$ and $\kappa \circ \zeta \Leftarrow 1 : \eta' \dashv \varepsilon : \kappa \circ \mu \Rightarrow 1$.

Then there is an isomorphism of contexts expressing that $\kappa$ respects context extension:

$$\sigma = (x_{\eta}^{\varepsilon'} / y) : (\Gamma, x : A, \mathbf{\Omega}_{\mu}^{\kappa}) \cong (\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, \kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}]).$$

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:19

*The inverse is given by:*

$$\begin{array}{c} (\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, \kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}]) \\ \downarrow (\mathrm{id}_{(\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, y)}, \mathbf{\alpha}_{\varepsilon}^{\eta'}) \\ (\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, \kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}], \mathbf{\Omega}_{\kappa}^{\zeta}, \mathbf{\Omega}_{\mu}^{\kappa}) \\ \downarrow (1_{\Gamma}, \mathbf{\alpha}_{\eta}^{\varepsilon'}, y/x, \mathbf{\Omega}_{\mu}^{\kappa}) \\ (\Gamma, x : A, \mathbf{\Omega}_{\mu}^{\kappa}) \end{array}$$

*Correspondingly, given $B$ in the codomain context of $\sigma$, there is an isomorphism of types*

$$(x : A) \rightarrow \langle \mu \mid B[\sigma] \rangle \quad \cong \quad \left\langle \mu \mid (\kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}]) \rightarrow B \right\rangle$$

*expressing internal transposition.*

#### 4. THE MODAL TRANSPENSION SYSTEM (MTRAS): GENERAL MODE THEORY AND SEMANTICS

As mentioned in Section 1.3, in our modal transpension system (MTraS), the transpension modality $\mathfrak{d}[u]$ will be part of an adjoint triple of internal modalities $\Omega[u] \dashv \Pi u \dashv \mathfrak{d}[u]$ together with weakening $\Omega[u]$ and universal quantification $\Pi u$ or, more generally in potentially non-cartesian systems, an adjoint triple $\lrcorner[u] \dashv \forall u \dashv \mathfrak{d}[u]$ together with fresh weakening $\lrcorner[u]$ and substructural (e.g. linear/affine) universal quantification $\forall u$. The further left adjoints $\Sigma u$ (cartesian) or $\exists u$ (potentially non-cartesian) cannot be internalized because every internal MTT modality needs to have a further semantic left adjoint; thus, they will only appear as left names.

Notably, the aforementioned modalities all bind or depend on a variable, a phenomenon which is not supported by MTT. We shall address this issue in the current section by grouping shape variables such as $u : \mathbb{U}$ in a **shape context** which is not considered part of the type-theoretic context but instead serves as the *mode* of the judgement.

We assume that there are no prior modalities, i.e. that the type system to which we wish to add a transpension type is non-modal in the sense that it has a single mode and only the identity modality. We assume that this single prior mode is modelled by the presheaf category $\mathrm{Psh}(\mathcal{W})$. Prior modalities and in particular their commutation with the modalities mentioned above, are considered in the technical report [Nuy20b].

**4.1. Shape contexts.** Assume we have in the prior system a context $\mathbb{X}$ modelled by a presheaf $\Xi$ over $\mathcal{W}$. Then the presheaves $\mathrm{Psh}(\mathcal{W}/\Xi)$ over the category of elements $\mathcal{W}/\Xi$ of the presheaf $\Xi$ are also a model of dependent type theory. Denoting the judgements of the latter system with a prefix $\mathbb{X} \mid$, it happens to be the case that judgements $\mathbb{X} \mid \Gamma \vdash J$ (i.e. $\Gamma \vdash J$ in $\mathrm{Psh}(\mathcal{W}/\Xi)$) have precisely the same meaning as judgements $\mathbb{X} \mid \Gamma \vdash J$ in $\mathrm{Psh}(\mathcal{W})$ (for a suitable but straightforward translation of $J$). Thus, we will group together all shape variables (variables for which we want a transpension type) in a **shape context** $\mathbb{X}$ in front of the typing context. Our judgements will then take the form $\mathbb{X} \mid \Gamma \vdash J$. Modal techniques will be used to signal what part of the context $\Gamma$ is fresh for a shape variable $u : \mathbb{U}$, as this can then no longer be signalled by the position of $u : \mathbb{U}$ in the context. All of this allows us

16:20

A. NUYTS AND D. DEVRIESE

Vol. 20:2

to frame the shape context $\mathbb{X}$ as the *mode* of the judgement, as it determines the category $\mathrm{Psh}(\mathcal{W}/\Xi)$ in which the judgement is modelled.

Concretely, we fix a set of **shapes** and generate shape contexts by the following rules:

|   | SHP-CTX-EXT  |
| --- | --- |
|  SHP-CTX-EMPTY | $\mathbb{X}$ shpctx $\mathbb{U}$ shape  |
|  · shpctx | $\mathbb{X}, u : \mathbb{U}$ shpctx  |

In Section 8.2, we will additionally add boundary variables. More generally, users of the current system could add shape context constructors at will, as long as they can be interpreted as presheaves over $\mathcal{W}$.

**4.2. Mode theory.** For simplicity, we take a highly general mode theory and will then only be able to say interesting things about specific modalities and 2-cells. In practice, and especially in implementations, one will want to select a more syntactic subtheory right away.

As **modes**, we take shape contexts. An interpretation function $[\sqcup]$ from shape contexts to presheaves over $\mathcal{W}$ will be defined in Section 6.1. The mode $\mathbb{X}$ is modelled in $\mathrm{Psh}(\mathcal{W}/[\mathbb{X}])$.$^9$

As **modalities** $\mu : \mathbb{X}_1 \to \mathbb{X}_2$, we take all functors $[\mathbf{\Omega}_\mu] : \mathrm{Psh}(\mathcal{W}/[\mathbb{X}_2]) \to \mathrm{Psh}(\mathcal{W}/[\mathbb{X}_1])$ which have a right adjoint $[\mu]$ that is then automatically a weak CwF morphism [Nuy20b] [Nuy20a, thm. 6.4.1] giving rise to a DRA [BCM$^+$20, lemma 17][Nuy18a, §2.1.3].$^{10}$

As **2-cells** $\alpha : \mu \Rightarrow \nu$, we take all natural transformations $[\mathbf{\Omega}_\alpha] : [\mathbf{\Omega}_\nu] \to [\mathbf{\Omega}_\mu]$, which automatically give rise to natural transformations $[\alpha] : [\mu] \to [\nu]$.

## 5. MTRAS MODALITIES FOR SUBSTITUTION

In the previous section, we have defined modalities as left adjoint functors and 2-cells as natural transformations. As such, we have neglected to provide an actual syntax; any syntax we use should be shallowly defined on semantic objects.

We take a similar approach to shape substitutions. A shape substitution from $\mathbb{X}_1$ to $\mathbb{X}_2$ is defined as a presheaf morphism $\sigma : [\mathbb{X}_1] \to [\mathbb{X}_2]$. We will consistently write the interpretation brackets so as to avoid confusion with modalities $\mathbb{X}_1 \to \mathbb{X}_2$. A presheaf morphism *is* not a modality but it gives rise to a pair of modalities:$^{11}$

**Theorem 5.1.** *Any presheaf morphism $\sigma : \Xi_1 \to \Xi_2$ gives rise to a triple of adjoint functors*

$$\Sigma^{\sigma|} \dashv \Omega^{\sigma|} \dashv \Pi^{\sigma|},$$

$$\Sigma^{\sigma|}, \Pi^{\sigma|} : \mathrm{Psh}(\mathcal{W}/\Xi_1) \to \mathrm{Psh}(\mathcal{W}/\Xi_2) \qquad \Omega^{\sigma|} : \mathrm{Psh}(\mathcal{W}/\Xi_2) \to \mathrm{Psh}(\mathcal{W}/\Xi_1)$$

$^9$As we will see later on, the available shapes must in some sense already be present in the base category, so that a context consisting purely of shapes will in general be representable. As such, we could alternatively interpret modes as *representable* presheaves over $\mathcal{W}$, which via the Yoneda-embedding are just the objects of $\mathcal{W}$. This is perfectly possible and would (again by inserting the Yoneda-embedding) require virtually no changes to our approach, although a number of intermediate results in the technical report [Nuy20b] would become unnecessary. However, the current approach is strictly more general, allows us to speak about boundaries (definitions 6.6 and 6.23) in the shape context, and did not require any compromise in the strength of our results.

$^{10}$A designated right adjoint can be retrieved from the left adjoint without the axiom of choice [Nuy20b, §2.3.6].

$^{11}$Note in particular that $\Omega[\sqcup]$ turns the arrow around: a presheaf morphism (shape substitution) $\sigma : [\mathbb{X}_1] \to [\mathbb{X}_2]$ gives rise to a substitution modality $\Omega[\sigma] : \mathbb{X}_2 \to \mathbb{X}_1$ sending types $T$ in shape context $\mathbb{X}_2$ to types $\langle \Omega[\sigma] \mid T \rangle$ in shape context $\mathbb{X}_1$.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:21

the latter two of which can be internalized as modalities (with an additional left name) $\Sigma \sigma \dashv \Omega[\sigma] \dashv \Pi \sigma$ with

$$\left[ \mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma} \right] = \Sigma^{\sigma|}, \qquad \left[ \Omega[\sigma] \right] = \Omega^{\sigma|}, \qquad \left[ \mathbf{\Theta}_{\Pi \sigma}^{\Omega[\sigma]} \right] = \Omega^{\sigma|}, \qquad \left[ \Pi \sigma \right] = \Pi^{\sigma|}.$$

We denote the units and co-units as

$$\text{copy}^{\sigma|} : 1 \to \Omega^{\sigma|} \circ \Sigma^{\sigma|} \qquad \text{drop}^{\sigma|} : \Sigma^{\sigma|} \circ \Omega^{\sigma|} \to 1$$

$$\text{const}^{\sigma|} : 1 \to \Pi^{\sigma|} \circ \Omega^{\sigma|} \qquad \text{app}^{\sigma|} : \Omega^{\sigma|} \circ \Pi^{\sigma|} \to 1$$

$$\text{drop}_{\sigma} \dashv \text{const}_{\sigma} : 1 \Rightarrow \Pi \sigma \circ \Omega[\sigma] \qquad \text{copy}_{\sigma} \dashv \text{app}_{\sigma} : \Omega[\sigma] \circ \Pi \sigma \Rightarrow 1$$

Under the correspondence of semantic contexts $\mathbb{X} \mid \Gamma \text{ctx}$ (i.e. presheaves over $\mathcal{W}/[\mathbb{X}]$) with semantic types $[\mathbb{X}] \vdash \Gamma \text{type}$, the functor $\Omega^{\sigma|}$ is exactly the semantics of ordinary type substitution in the standard presheaf model [Hof97] and hence, if $\sigma$ is a weakening substitution, then $\Sigma^{\sigma|}$ and $\Pi^{\sigma|}$ are naturally isomorphic to the semantics of ordinary $\Sigma$- and $\Pi$-types.

The functor $\Omega^{\sqcup}$ and the modality $\Pi \sqcup$ are strictly functorial (they respect identity and composition of presheaf morphisms on the nose) whereas the functors $\Sigma^{\sqcup}$, $\Pi^{\sqcup}$ and the modality $\Omega[\sqcup]$ are pseudofunctorial$^{12}$.

Proof. The morphism $\sigma$ gives rise to a functor $\Sigma^{\sigma/\sigma} : \mathcal{W}/\Xi_1 \to \mathcal{W}/\Xi_2 : (W, \psi) \to (W, \sigma \psi)$ and hence via left Kan extension, precomposition and right Kan extension [Sta19] to a triple of adjoint functors $\Sigma^{\sigma|} \dashv \Omega^{\sigma|} \dashv \Pi^{\sigma|}$ between the presheaf categories. The claim about type substitution follows from unfolding the definitions and the claims about $\Sigma$- and $\Pi$-types then follow from uniqueness of adjoints.

Strict functoriality of $\Omega^{\sqcup}$ follows immediately from the construction. Strict functoriality of $\Pi \sqcup$ then follows from the fact that a modality $\mu$ is fully defined by the semantic left adjoint $[\mathbf{\Theta}_{\mu}]$. Pseudofunctoriality of the others follows by uniqueness of the adjoint. $\square$

Remark 5.2 (Substitution as a DRA). In presheaf models, contexts are essentially the same thing as closed types (a property called democracy). The shape substitution operation for contexts $\mathbf{\Theta}_{\Pi \sigma}^{\Omega[\sigma]}$ is modelled by $\Omega^{\sigma|}$, i.e. by ordinary substitution. However, the shape substitution operation applicable to types is the modal type former $\langle \Omega[\sigma] \mid \sqcup \rangle$, which is not equivalent. Indeed, if $\langle \Omega[\sigma] \mid T \rangle$ is closed, i.e. $\mathbb{X}_1 \mid \cdot \vdash \langle \Omega[\sigma] \mid T \rangle$ type, then $T$ lives in context $\mathbb{X}_2 \mid \cdot, \mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma} \vdash T$ type, so it is not closed. The operation $\langle \Omega[\sigma] \mid \sqcup \rangle$ is in general still modelled as a substitution, but now it is one between the semantic contexts $[\mathbb{X}_1], [\Gamma]$ and $[\mathbb{X}_2], \Sigma^{\sigma|}[\Gamma]$ which are isomorphic. This is especially clear if $\sigma : [\mathbb{X}], [\Delta] \to [\mathbb{X}]$ is a weakening substitution for a context $\mathbb{X} \mid \Delta \text{ctx}$, in which case we are dealing with $[\mathbb{X}], [\Delta], [\Gamma]$ and $[\mathbb{X}], (\Sigma[\Delta][\Gamma])$. We can still let $\langle \Omega[\sigma] \mid \sqcup \rangle$ act on a closed type $\Xi_2 \mid \cdot \vdash S$ type, however, but we first have to weaken $S$ to bring it to context $\cdot, \mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$. The composite of these two operations – weakening over $\mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$ and then applying $\langle \Omega[\sigma] \mid \sqcup \rangle$ – is in fact equivalent with the operation $\mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$ on contexts.

This remark is relevant to the $\Omega[\sigma]$ modality specifically because its lock $\mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$ does not preserve the empty context, whereas most other modalities' locks do.

$^{12}$However, Gratzer et al. [GKNB20a] have a strictification theorem for models of MTT which could be used to strictly $\Omega[\sqcup]$.

16:22

A. NUYTS AND D. DEVRIESE

Vol. 20:2

Notation 5.3. We will use a slightly unconventional notation for substitutions in order to have them make maximal sense both as a substitution (as in \(\Omega[\sigma]\)) and as a function domain (as in \(\Pi\sigma\)):

- Every weakened variable (if weakening is available for the given shape) will be declared, e.g. we get a presheaf morphism \((u:\mathbb{U}):\llbracket \mathbb{X},u:\mathbb{U}\rrbracket \to \llbracket \mathbb{X}\rrbracket\) and hence \(\Omega [u:\mathbb{U}]:\mathbb{X}\to (\mathbb{X},u:\mathbb{U})\) and \(\Pi (u:\mathbb{U}):(\mathbb{X},u:\mathbb{U})\to \mathbb{X}\). Furthermore, we may omit the shape, writing just \(\Omega [u]\) and \(\Pi u\). Thus, this is what weakening and shape abstraction look like:

\[
\frac {\mathbb {X} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ u ]} ^ {\Sigma u} \vdash t : T}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {m o d} _ {\Omega [ u ]}   t : \langle \Omega [ u ] \mid T \rangle}, \qquad \frac {\mathbb {X} , u : \mathbb {U} \mid \Gamma , \widehat {\mathbf {0}} _ {\Pi   u} ^ {\Omega [ u ]} \vdash t : T}{\mathbb {X} \mid \Gamma \vdash \mathsf {m o d} _ {\Pi   u}   t : \langle \Pi   u \mid T \rangle}.
\]

The projection function (Proposition 3.3) for \(\Pi u\) is function application:

\[
\frac {\mathbb {X} , u : \mathbb {U} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ u ] \circ \Pi   u} ^ {\Omega [ u ] \circ \Sigma   u} \vdash A   \text {type}}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {a p p} _ {u} : (\Omega [ u ] \mid \langle \Pi   u \mid A \rangle) \to A \left[ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {u} : \Omega [ u ] \circ \Pi   u \Rightarrow 1} ^ {\mathsf {c o p y} _ {u} : 1 \Rightarrow \Omega [ u ] \circ \Sigma   u} \right]} \text {Proposition 3.3}
\]

The 2-cell \(\Omega[u] \circ \Sigma u \Leftarrow 1: \mathsf{copy}_u \dashv \mathsf{app}_u: \Omega[u] \circ \Pi u \Rightarrow 1\) signals a contraction of shape variables, namely of the one bound by the \(\Pi\)-modality and the one to which the function is applied.

- When a variable is substituted, we denote this as \( u := t \) instead of \( t / u \), e.g. in a cubical type theory we get a presheaf morphism \( (i := 0) : [\mathbb{X}] \to [\mathbb{X}, i : \mathbb{I}] \) and hence \( \Omega[i := 0] : (\mathbb{X}, i : \mathbb{I}) \to \mathbb{X} \) which binds \( i \) and \( \Pi(i := 0) : \mathbb{X} \to (\mathbb{X}, i : \mathbb{I}) \) which depends on \( i \), so we may substitute 0 for \( i \) but we may also abstract over the assumption that \( i \) is 0:

\[
\frac {\mathbb {X} , i : \mathbb {I} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ i : = 0 ]} ^ {\Sigma (i : = 0)} \vdash t : T}{\mathbb {X} \mid \Gamma \vdash \mathsf {m o d} _ {\Omega [ i : = 0 ]}   t : \langle \Omega [ i : = 0 ] \mid T \rangle}, \qquad \frac {\mathbb {X} \mid \Gamma , \widehat {\mathbf {0}} _ {\Pi (i : = 0)} ^ {\Omega [ i : = 0 ]} \vdash t : T}{\mathbb {X} , i : \mathbb {I} \mid \Gamma \vdash \mathsf {m o d} _ {\Pi (i : = 0)}   t : \langle \Pi (i : = 0) \mid T \rangle}.
\]

And apply:

\[
\frac {\mathbb {X} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ i : = 0 ] \circ \Pi (i : = 0)} ^ {\Omega [ i : = 0 ] \circ \Sigma (i : = 0)} \vdash A   \text {type}}{\mathbb {X} \mid \Gamma \vdash \mathsf {a p p} _ {i : = 0} : (\Omega [ i : = 0 ] \mid \langle \Pi (i : = 0) \mid A \rangle) \to A \left[ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {i : = 0} : \Omega [ i : = 0 ] \circ \Pi (i : = 0) \Rightarrow 1} ^ {\mathsf {c o p y} _ {i : = 0} : 1 \Rightarrow \Omega [ i : = 0 ] \circ \Sigma (i : = 0)} \right]} \text {prop. 3.3}
\]

- Finally, if \(\sigma\) involves weakening, then the codomain of the co-unit may be a variable renaming that is sugar for the identity, e.g.

\[
\mathsf {a p p} _ {(u / v: \mathbb {U})}: \Omega [ u: \mathbb {U} ] \circ \Pi (v: \mathbb {U}) \Rightarrow \Omega [ u: \mathbb {U}, v := u ]
\]

is exactly the same thing as

\[
\mathsf {a p p} _ {(u: \mathbb {U})}: \Omega [ u: \mathbb {U} ] \circ \Pi (u: \mathbb {U}) \Rightarrow 1.
\]

This way, we may adjust \(\mathsf{app}_{(u:\mathbb{U})}\) in order to be able to apply to a different variable:

\[
\frac {\mathbb {X} , v : \mathbb {U} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ u ] \circ \Pi   v} ^ {\Omega [ v ] \circ \Sigma   u} \vdash A   \text {type}}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {a p p} _ {u / v} : (\Omega [ u ] \mid \langle \Pi   v \mid A \rangle) \to \left\langle \Omega [ u , v : = u ] \mid A \left[ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {u / v}: \Omega [ u ] \circ \Pi   u \Rightarrow \Omega [ u , v : = u ]} ^ {\mathsf {c o p y} _ {v / u}: \Omega [ v , u : = v ] \Rightarrow \Omega [ u ] \circ \Sigma   u} \right] \right\rangle}
\]

Again, bear in mind that shape substitutions are in fact defined as presheaf morphisms and that therefore, notions such as weakening and contraction reflected by the syntax introduced here, need to be shallowly interpreted in presheaf morphisms.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:23

Example 5.4. If $\mathbb{U}$ is cartesian, i.e. $[\mathbb{X}, u : \mathbb{U}] = [\mathbb{X}] \times [\mathbb{U}]$, then there is a diagonal substitution $(w : \mathbb{U}, u := w, v := w) : [\mathbb{X}, w : \mathbb{U}] \to [\mathbb{X}, u : \mathbb{U}, v : \mathbb{U}]$. Writing

$$\begin{array}{l} \alpha = 1_{\Pi u} * 1_{\Pi v} * \operatorname{const}_{(w, u := w, v := w)} : \Pi u \circ \Pi v \Rightarrow \\ \quad \Pi u \circ \Pi v \circ \Pi(w, u := w, v := w) \circ \Omega[w, u := w, v := w] \\ \quad = \Pi((u : \mathbb{U}) \circ (v : \mathbb{U}) \circ (w, u := w, v := w)) \circ \Omega[w, u := w, v := w] \\ \quad = \Pi((u : \mathbb{U}) \circ (w, u := w)) \circ \Omega[w, u := w, v := w] \\ \quad = \Pi w \circ \Omega[w, u := w, v := w], \end{array}$$

where the equations use strict functoriality of $\Pi \sqcup$ and ordinary calculation of composition of substitutions, this allows us to type the naively typed function $\lambda f.\lambda w.f w w : (\Pi u.\Pi v.A) \to \Pi w.A[w/u, w/v]$ as

$$\langle \Pi(u : \mathbb{U}) \mid \langle \Pi(v : \mathbb{U}) \mid A \rangle \rangle \to \langle \Pi(w : \mathbb{U}) \mid \langle \Omega[w : \mathbb{U}, u := w, v := w] \mid A[\mathbf{Q}_{\alpha}] \rangle \rangle.$$

Remark 5.5. The reframing of shape substitutions as a modality, has the annoying consequence that substitution no longer reduces. However, both $\langle \Omega[\sigma] \mid \sqcup \rangle$ and $\operatorname{mod}_{\Omega[\sigma]}$ are semantically an ordinary substitution (along an isomorphism, see Remark 5.2). Thus, we could add computation rules such as:

$$\begin{array}{rcl} \langle \Omega[\sigma] \mid A \times B \rangle & = & \langle \Omega[\sigma] \mid A \rangle \times \langle \Omega[\sigma] \mid B \rangle, \quad \langle \Omega[\sigma] \mid \mathsf{U} \rangle = \mathsf{U}, \\ \operatorname{mod}_{\Omega[\sigma]}(a, b) & = & (\operatorname{mod}_{\Omega[\sigma]} a, \operatorname{mod}_{\Omega[\sigma]} b), \quad \operatorname{mod}_{\Omega[\sigma]} \lceil A \rceil = \lceil \langle \Omega[\sigma] \mid A \rangle \rceil. \end{array}$$

This is fine in an extensional type system, but would not play well with the $\beta$-rule for modal types in an intensional system. Indeed, $\beta$-reduction for $\langle \Omega[\sigma] \mid A \rangle$ requires a solution to the following problem: when $\hat{a} = \operatorname{mod}_{\Omega[\sigma]} a$ definitionally, then we need to be able to infer $a$ up to definitional equality from $\hat{a}$. Alternatively, the eliminator for $\langle \Omega[\sigma] \mid A \rangle$ should somehow proceed by induction on $A$, e.g. an element of $\langle \Omega[\sigma] \mid A \times B \rangle$ could be eliminated as an element of $\langle \Omega[\sigma] \mid A \rangle \times \langle \Omega[\sigma] \mid B \rangle$. A third possibility would be to abolish elimination of $\langle \Omega[\sigma] \mid \sqcup \rangle$ altogether, except when applied to type formers for which there is no definitional substitution-commutation law.

Remark 5.6. In type theory, we generally expect admissibility of substitution: given a derivable judgement $\Gamma \vdash J$ and a substitution $\sigma : \Delta \to \Gamma$, we expect derivability of $\Delta \vdash J[\sigma]$, where the operation $\sqcup[\sigma]$ can be applied to any term, type or other object in context and traverses its structure, leaving everything untouched except variables. A good way to guarantee admissibility of substitution is by making sure that every inference rule has a conclusion in a general context $\Gamma$ and that the context of any premise is obtained by applying a functorial operation to $\Gamma$.

There is no such result for shape substitutions. The conclusion of modal inference rules often has a non-general shape context, and the transpension type is in general not even respected by shape substitution [Nuy20b]. However, until we extend MTraS with additional rules in Sections 8 to 10,¹³ we do have a form of the usual result: given a derivable judgement $\mathbb{X} \mid \Gamma \vdash J$ and a substitution $\mathbb{X} \mid \sigma : \Delta \to \Gamma$, we can derive $\mathbb{X} \mid \Delta \vdash J[\sigma]$.

¹³And possibly even after, see Remark 9.4.

16:24

A. NUYTS AND D. DEVRIESE

Vol. 20:2

## 6. MULTIPLIERS

In this section, we introduce multipliers as a semantics for shapes, as well as the associated modalities $\lrcorner[u] \dashv \forall u \dashv \wr[u]$. In Section 6.1, we define multipliers and a number of criteria by which we can classify them. In Section 6.2, we deal with a technical complication that we dubbed *unpointability*$^{§A}$, which shows up especially in models of guarded and nominal type theory. In Section 6.3, we discuss an extensive number of examples. In Section 6.4, we consider how *copointed*$^{§A}$ multipliers give rise to *shape weakening* modalities that are a special instance of the modalities in Section 5. In Section 6.5, we discuss how a multiplier and its associated operations lift from acting on base and slice categories to acting on categories of elements of semantic shape contexts. Then in Section 6.6, we are finally ready to define the transpension modality and its adjoints and to state the quantification Theorem 6.31 that helps to understand them. In Section 6.7, we say a bit more on cartesian multipliers. In Section 6.8, we briefly list the matters that are not discussed in the current paper but can be found in the technical report [Nuy20b].

**6.1. Shapes and multipliers.** In Section 4, we defined shape contexts as lists of variables and announced that these would be modelled as presheaves over $\mathcal{W}$. Several times, we have hinted at the fact that these shape variables need not satisfy all the usual structural rules (weakening, exchange and contraction). In this section, we make these matters precise.

We associate to each shape $\mathbb{U}$ a functor $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ which extends by left Kan extension to a functor $\sqcup \ltimes \mathbf{y}U : \mathrm{Psh}(\mathcal{W}) \to \mathrm{Psh}(\mathcal{W})$. $^{14}$ We define the semantics of shape contexts $[\sqcup] : \mathrm{ShpCtx} \to \mathrm{Obj}(\mathrm{Psh}(\mathcal{W}))$ as follows:

$$[\cdot] = \top, \qquad [\mathbb{X}, u : \mathbb{U}] = [\mathbb{X}] \ltimes \mathbf{y}U.$$

Of course, if we model shape context extension with $u : \mathbb{U}$ by an *arbitrary* functor, then we will not be able to prove many results. Depending on the properties of the functor, the variable $u$ will obey different structural rules and the $\Phi$-combinator [Mou16, BCM15] (Section 10.2) will or will not be sound for $\mathbb{U}$. For this reason, we introduce some criteria that help us classify shapes. Some of these criteria concern in fact the *fresh weakening functor* for the given multiplier, which is essentially an instance of the following construction:

**Definition 6.1.** Given a functor $F : \mathcal{V} \to \mathcal{W}$ and $V_0 \in \mathrm{Obj}(\mathcal{V})$, we define the action of $F$ on slice objects over $V_0$ as the functor

$$F/V_0 : \mathcal{V}/V_0 \to \mathcal{W}/FV_0 : (V, \varphi) \mapsto (FV, F\varphi).$$

**Definition 6.2.** Assume $\mathcal{W}$ has a terminal object $\top$. A **multiplier** for an object $U$ is an endofunctor$^{15}$ $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ such that $\top \ltimes U \cong U$. This gives us a natural second projection $\pi_2 : (\sqcup \ltimes U) \to U$.

We define the **fresh weakening functor** to the slice category as $\lrcorner_U : \mathcal{W} \to \mathcal{W}/U : W \mapsto (W \ltimes U, \pi_2)$, which is essentially the action of the multiplier on slice objects over $\top$.

We say that a multiplier (as well as its shape) is:

$^{14}$Both $\sqcup \ltimes U$ and $\sqcup \ltimes \mathbf{y}U$ are to be regarded as single-character symbols, i.e. $\ltimes$ in itself is meaningless. In most concrete applications, however, the multiplier is defined as some monoidal product $\sqcup \otimes U$ with a given object $U$, in which case the left Kan extension is naturally isomorphic to Day convolution with $\mathbf{y}U$. For this reason, we also refrain from defining $U := \top \ltimes U$ because we may not have $\top \otimes U = U$ on the nose for the object of interest $U$.

$^{15}$In the technical report [Nuy20b], we generalize beyond endofunctors.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:25

- **Copointed**$^{\S A}$ if it is equipped with a natural first projection $\pi_1 : (\sqcup \ltimes U) \to \text{Id}$.

*This property carries over to $\sqcup \ltimes \mathbf{y}U$ and thus allows for shape weakening.*

- A **comonad**$^{\S A}$ if it is additionally equipped with a natural diagonal $\delta : (\sqcup \ltimes U) \to ((\sqcup \ltimes U) \ltimes U)$ such that $\pi_1 \circ \delta = (\pi_1 \ltimes U) \circ \delta = 1_{(\sqcup \ltimes U)}$ and $\delta \circ \delta = (\delta \ltimes U) \circ \delta : (\sqcup \ltimes U) \to (\sqcup \ltimes U)^3$. *This property carries over to $\sqcup \ltimes \mathbf{y}U$ and thus allows for shape variable contraction.*

- **Cartesian** if it is naturally isomorphic to the cartesian product with $U$.

*This property carries over to $\sqcup \ltimes \mathbf{y}U$ and is thus a sufficient condition for allowing exchange. Additionally, it will erase the distinction between weakening $\Omega[u]$ (Section 6.4) and fresh shape weakening $\lrcorner[u]$ (Section 6.6), see Theorem 6.31.*

- $\top$-**slice faithful**$^{\S A}$ if $\lrcorner_U$ is faithful.

*This is a basic well-behavedness property that is satisfied by all examples of interest. Example 6.20 is a counterexample.*

- $\top$-**slice full**$^{\S A}$ if $\lrcorner_U$ is full.

*For multipliers for objects other than $\top$, this property precludes the exchange rule (Proposition 6.3). $\top$-slice fully faithful multipliers will give rise to fully faithful modalities for fresh weakening $\lrcorner[u]$ and transpension $\Diamond[u]$ (Theorem 6.31).*

- $\top$-**slice shard-free**$^{\S A}$ if $\lrcorner_U$ is essentially surjective on slice objects $(V, \psi)$ such that $\psi : V \to U$ is dimensionally split (Definition 6.6). A **shard**$^{\S A}$ is a slice object $(V, \psi)$ that is not up to isomorphism in the image of $\lrcorner_U$ even though $\psi$ is dimensionally split.

*Intuitively, a shard is a shape over $\mathbb{U}$ that covers all of $\mathbb{U}$ (as expressed by the fact that $\psi$ is dimensionally split, which just means split epi in most applications), but that is not prism-shaped in the direction of $\mathbb{U}$ (as it would then be in the image of $\lrcorner_U$). Shard-freedom will be a requirement for the $\Phi$-rule [Mou16] to hold (Theorem 10.1) and for elimination of the transpension type by pattern matching to be sound (Theorem 9.3).*

- $\top$-**slice right adjoint** if $\lrcorner_U$ has a left adjoint $\exists_U : \mathcal{W}/U \to \mathcal{W}$.$^{16}$

**Proposition 6.3.** *If a $\top$-slice full multiplier for $U$ is:*

- a *comonad*, then $U$ is terminal,
- *cartesian*, then it is naturally isomorphic to the identity functor.

*Proof.* The second statement clearly follows from the first, so we only prove the first. Consider the following diagram:

$$\top \ltimes U \xrightarrow{\delta} (\top \ltimes U) \ltimes U \tag{6.1}$$

It commutes, because $\pi_2 = \pi_2 \circ (\pi_1 \ltimes U) : (\top \ltimes U) \ltimes U \to U$ and $(\pi_1 \ltimes U) \circ \delta = 1$. So it is a morphism of slice objects $\delta : \lrcorner_U \top \to \lrcorner_U (\top \ltimes U)$ and thus, since $\lrcorner_U$ is full, of the form $\lrcorner_U v$ for some $v : \top \to \top \ltimes U$. This means in particular that

$$\text{id}_{\top \ltimes U} = \pi_1 \circ \delta = \pi_1 \circ (v \ltimes U) = v \circ \pi_1 : \top \ltimes U \to \top \ltimes U, \tag{6.2}$$

so the identity on $\top \ltimes U$ factors over $\top$. Then $\top \ltimes U \cong U$ is terminal.

$^{16}$A functor $\sqcup \ltimes U$ with this property is usually called a *parametric* or *local right adjoint*, but the word 'local' is overloaded [nLa23b] and so is 'parametric', and we wanted uniform terminology.

16:26

A. NUYTS AND D. DEVRIESE

Vol. 20:2

6.2. **Pointability, dimensional splitness and boundaries.** Before we move on to a list of examples, we owe the reader a definition for dimensional splitness (although the impatient reader may first read the example Section 6.3, ignoring shard-freedom, pointability and boundaries). In most popular base categories, namely all the *objectwise pointable* ones, we could have gotten away with saying 'split epi' instead of 'dimensionally split' (Proposition 6.8).

**Definition 6.4.** Let $\mathcal{W}$ be a category with terminal object $\top$. An object $W$ is **pointable**$^{\S A}$ if $() : W \to \top$ is split epi, i.e. if there exists at least one morphism $\top \to W$. A category is **objectwise pointable**$^{\S A}$ if each object is pointable.

We have carefully chosen the above terminology to emphasize (1) that pointability is a property, not structure (the corresponding structure is called *pointed*), and (2) that objectwise pointability does *not* require that the pointings can be chosen naturally.

**Proposition 6.5.** *Let $\sqcup \ltimes U$ be a multiplier on an objectwise pointable category $\mathcal{W}$. Then for any object $W$, the slice object $\lhd_U W$ is split epi.*

*Proof.* Any functor preserves split epimorphisms. We have $\lhd_U W = (W \ltimes U, \pi_2)$ and $\pi_2 : W \ltimes U \to U \cong \top \ltimes U$ is essentially the image of $W \to \top$. $\square$

When dealing with a category that is not objectwise pointable, the above theorem does not hold and the definition of shard-freedom w.r.t. split epi slice objects would not make sense, so we need a somewhat more general notion:

**Definition 6.6.** Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$, we say that a morphism $\varphi : V \to U$ is **dimensionally split** if there is some $W \in \mathcal{W}$ such that $\pi_2 : W \ltimes U \to U$ factors over $\varphi$. The other factor $\chi : W \ltimes U \to V$ such that $\pi_2 = \varphi \circ \chi$ will be called a **(dimensional) section** of $\varphi$. We write $\mathcal{W} // U$ for the full subcategory of $\mathcal{W} / U$ of dimensionally split slice objects.

We define the **boundary** $\partial U$ as the subpresheaf of the Yoneda-embedding $\mathbf{y} U$ consisting of those morphisms that are *not* dimensionally split.

Thus, a multiplier is $\top$-slice shard-free if and only if every dimensionally split slice object has an invertible dimensional section.

**Proposition 6.7.** *Let $\sqcup \ltimes U$ be a multiplier on $\mathcal{W}$. Then for any object $W$, the slice object $\lhd_U W$ is dimensionally split with section $\operatorname{id}_{W \ltimes U}$.* $\square$

**Proposition 6.8.** *If $\mathcal{W}$ is objectwise pointable, then a morphism $\varphi : V \to U$ is split epi if and only if it is dimensionally split.* [Nuy20b]

The notion of dimensionally split morphisms lets us consider the boundary and shard-freedom (a requirement for modelling $\Phi$) also in base categories that are not objectwise pointable, where the output of $\lhd_U$ may not be split epi.

**Remark 6.9.** $\top$-slice shard-freedom can also be formulated using (co)sieves [nLa23d]. A **sieve in $\mathcal{W}$** is a full subcategory $\mathcal{S}$ such that if $W \in \mathcal{S}$ and $\varphi : V \to W$, then $V \in \mathcal{S}$. The dual (where $\varphi$ points the other way) is called a **cosieve in $\mathcal{W}$**. Being full subcategories, (co)sieves can be regarded as subsets of $\operatorname{Obj}(\mathcal{W})$. A **sieve on $U \in \mathcal{W}$** is a sieve in $\mathcal{W} / U$ or, equivalently, a subpresheaf of $\mathbf{y} U$.

A multiplier is $\top$-slice shard-free if either of the following equivalent criteria is satisfied:
- The objects in the essential image of $\lhd_U$ constitute a cosieve in $\mathcal{W} / U$ [Nuy23a].

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:27

- The objects *outside* the essential image of $\mathbb{J}_U$ constitute a sieve in $\mathcal{W}/U$, i.e. a sieve on $U$. The slice objects of the cosieve generated by objects of the essential image of $\mathbb{J}_U$, are called dimensionally split. The boundary $\partial U$ is the largest sieve on $U$ that is disjoint with the objects of the essential image of $\mathbb{J}_U$.

If $\sqcup \ltimes U$ is $\top$-slice fully faithful, then the above conditions are furthermore equivalent to $\mathbb{J}_U$ being a Street opfibration.

6.3. **Examples.** Let us look at some examples of multipliers. Their properties are listed in Fig. 7. Most properties are easy to verify, so we omit the proofs.

**Example 6.10** (Identity). The identity functor on an arbitrary category $\mathcal{W}$ is a multiplier for $\top$. All slice objects $(W, ()$ are dimensionally split with invertible section $\mathrm{id}_W : \mathrm{Id} \, W \cong W$; hence the boundary is empty and there are no shards. It is $\top$-slice right adjoint, with $\exists_\top : \mathcal{W}/\top \to \mathcal{W} : (W, ()) \mapsto W$.

**Example 6.11** (Cartesian product). Let $\mathcal{W}$ be a category with finite products and $U \in \mathcal{W}$. Then $\sqcup \ltimes U$ is a multiplier for $U$, which is $\top$-slice full if and only if it is the identity (i.e. $U$ is terminal, cf. Proposition 6.3 and Example 6.10). It is $\top$-slice right adjoint with $\exists_U : \mathcal{W}/U \to \mathcal{W} : (W, \psi) \mapsto W$. Hence, we have $\exists_U \mathbb{J}_U = \sqcup \ltimes U$.

**Definition 6.12.** Let RG be the category generated by the following diagram and equations:

$$\begin{array}{rcl} \mathbb{N} & \xrightarrow[\mathbf{t}]{\mathbf{s}} & \mathbf{r} \circ \mathbf{s} = \mathrm{id}_{\mathbb{N}}, \\ & \mathbf{r} \circ \mathbf{t} & = \mathrm{id}_{\mathbb{N}}. \end{array}$$

A presheaf over RG is a reflexive graph. More generally, let $^a$RG (with $a \ge 0$) be the category generated by the following:

$$\begin{array}{rcl} \mathbb{N} & \xrightarrow[\mathbf{r}]{\mathbf{e}_0, \dots, \mathbf{e}_{a-1}} & \mathbf{r} \circ \mathbf{e}_i = \mathrm{id}_{\mathbb{N}}. \end{array}$$

**Example 6.13** (Cartesian cubes). Let $^a$Cube be the category of cartesian $a$-ary cubes. It is the free cartesian monoidal category with same terminal object over $^a$RG. Concretely:

- Its objects take the form $(i_1 : \mathbb{I}, \dots, i_n : \mathbb{I})$ (the names are desugared to de Bruijn indices, i.e. the objects are really just natural numbers),
- Its morphisms $(i_1 : \mathbb{I}, \dots, i_n : \mathbb{I}) \to (j_1 : \mathbb{I}, \dots, j_m : \mathbb{I})$ are arbitrary functions

$$\varphi : \{j_1, \dots, j_m\} \to \{i_1, \dots, i_n\} \cup \{0, \dots, a-1\} : j \mapsto j\langle \varphi \rangle.$$

We also write $\varphi = (j_1\langle \varphi \rangle / j_1, \dots, j_m\langle \varphi \rangle / j_m)$. If a variable $i$ is not used, we may write $i/\oslash$ to emphasize this.

This category is objectwise pointable if and only if $a \ne 0$. On this category, we consider the multiplier $\sqcup \ltimes (i : \mathbb{I})$, which is an instance of Example 6.11 and therefore inherits all properties of cartesian multipliers. A slice $(V, \varphi)$ where $\varphi : V \to (i : \mathbb{I})$ is dimensionally split if $i\langle \varphi \rangle$ is not an endpoint, i.e. $i\langle \varphi \rangle \not\in \{0, \dots, a-1\}$, and in that case it is isomorphic to $\mathbb{J}_{(i:\mathbb{I})}V'$ where $V'$ is $V$ with $i\langle \varphi \rangle$ removed, so there are no shards. Clearly then, any morphism on the boundary factors through one of $a$ morphisms $(\varepsilon/i) : \top \to (i : \mathbb{I})$ where $\varepsilon \in \{0, \dots, a-1\}$, so $\partial \mathbb{I} \cong \bigsqcup_{k=0}^{a-1} \top$.

16:28

A. NUYTS AND D. DEVRIESE

Vol. 20:2

|  Example | Base category | Multiplier | Objectwise pointable category | Copointed/ Weakening | Exchange | Comonad/ Contraction | Cartesian | T-s. faithful | T-s. full | T-s. shard-free | T-s. right adjoint  |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
|  6.10 | W | Id | ? | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ☑  |
|  6.11 | W | (⊔ × U) ⊕ Id | ? | ☑ | ☑ | ☑ | ☑ | ? | ✗ | ? | ☑  |
|  6.13 | ^{a}Cube | ⊔ × (i : I) | a ≠ 0 | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.14 | ^{a}Cube_{□} | ⊔ × (i : I) | a ≠ 0 | ☑ | ☑ | ✗ | ✗ | ☑ | ☑ | ☑ | ☑  |
|  6.15 | CCHM | ⊔ × (i : I) | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ✗ | ☑  |
|  6.16 | DCube_{d} | ⊔ × (i : (k)) | ☑ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.17 | Clock | ⊔ × (i : ⊕_{k}) | ✗ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.18 | TwCube | ⊔ × I | ☑ | ✗ | ✗ | ✗ | ✗ | ☑ | ☑ | ☑ | ☑  |
|  6.19 | n | min(⊔, i) | ✗ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ☑ | ☑  |
|  6.20 | ^{2}Cube_{⊥} | ⊔ × ⊥ | ☑ | ☑ | ☑ | ☑ | ☑ | ✗ | ✗ | ☑ | ☑  |

Figure 7: Some interesting multipliers and their properties. Properties that follow from being cartesian are greyed out.

**Example 6.14** (Affine cubes). Let $^a\text{Cube}_\square$ be the category of affine $a$-ary cubes as used in [BCH14] (binary) or [BCM15] (unary). It is the free semicartesian monoidal category with same terminal unit over $^a\text{RG}$. Concretely:

- • Objects are as in $^a\text{Cube}$,
- • Morphisms are as in $^a\text{Cube}$ such that if $j\langle\varphi\rangle = k\langle\varphi\rangle \notin \{0, \dots, a-1\}$, then $j = k$. This rules out diagonal maps.

This category is objectwise pointable if and only if $a \neq 0$. On this category, we consider the functor $\cup \cdot (i : \mathbb{I}) : W \mapsto (W, i : \mathbb{I})$, which is a multiplier for $(i : \mathbb{I})$. Dimensional splitness and the boundary are as in $^a\text{Cube}$. This functor is T-slice right adjoint with $\exists_{(i:\mathbb{I})}((W, j : \mathbb{I}), (j/i)) = W$ and $\exists_{(i:\mathbb{I})}(W, (\varepsilon/i)) = W$ for each of the $a$ endpoints $\varepsilon$.

In the nullary case, $^0\text{Cube}_\square$ is the base category of the Schanuel topos, a sheaf topos equivalent to the category of nominal sets [Pit13]. In that case, $\exists_{(i:\mathbb{I})}$ is not just left adjoint to $\perp_{(i:\mathbb{I})}$, but in fact an inverse and hence also right adjoint. This is in line with the fact that in nominal type theory [PMD15], there is a single name quantifier which can be read as either existential or universal quantification.

**Example 6.15** (CCHM cubes). Let CCHM be the category of CCHM cubes [CCHM17], which is objectwise pointable. Its objects are as in $^2\text{Cube}$ and its morphisms $(i_1 : \mathbb{I}, \dots, i_n : \mathbb{I}) \to (j_1 : \mathbb{I}, \dots, j_m : \mathbb{I})$ are functions from $\{j_1, \dots, j_m\}$ to the free de Morgan algebra over $\{i_1, \dots, i_n\}$. We again consider $\cup \times (i : \mathbb{I})$, another instance of Example 6.11. A slice object $(V, \varphi)$ is now (dimensionally) split if $i\langle\varphi\rangle$ is not an endpoint, so the boundary is again $\top \uplus \top$. The so-called *connections* $(j \vee k/i), (j \wedge k/i) : (j : \mathbb{I}, k : \mathbb{I}) \to (i : \mathbb{I})$ are shards, because they have sections $(i/j, 0/k) : (i : \mathbb{I}) \to (j : \mathbb{I}, k : \mathbb{I})$ and $(i/j, 1/k) : (i : \mathbb{I}) \to (j : \mathbb{I}, k : \mathbb{I})$ respectively but are not in the image of $\perp_{(i:\mathbb{I})}$.

**Example 6.16** (Depth $d$ cubes). Let DCube$_{d}$ with $d \geq -1$ be the category of depth $d$ cubes, used as a base category in degrees of relatedness [ND18a, Nuy18a]. This is a generalization of the category of binary cartesian cubes Cube, where instead of typing every dimension with

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:29

the interval $\mathbb{I}$, we type them with the $k$-interval $(\lVert k \rVert)$, where $k \in \{0, \dots, d\}$ is called the degree of relatedness of the edge. Its objects take the form $(i_1 : (\lVert k_1 \rVert), \dots, i_n : (\lVert k_n \rVert))$. Conceptually, we have a map $(\lVert k \rVert) \to (\lVert \ell \rVert)$ if $k \geq \ell$. Thus, morphisms $\varphi : (i_1 : (\lVert k_1 \rVert), \dots, i_n : (\lVert k_n \rVert)) \to (j_1 : (\lVert \ell_1 \rVert), \dots, j_m : (\lVert \ell_m \rVert))$ send every variable $j : (\lVert \ell \rVert)$ of the codomain to a value $j \langle \varphi \rangle$, which is either 0, 1 or a variable $i : (\lVert k \rVert)$ of the domain such that $k \geq \ell$.

- If $d = -1$, then there is only one object $(\cdot)$ and only the identity morphism, i.e. we have the point category.
- If $d = 0$, we just get Cube.
- If $d = 1$, we obtain the category of bridge/path cubes BPCube := DCube$_1$. We write $\mathbb{P}$ for $(\lVert 0 \rVert)$ (the path interval) and $\mathbb{B}$ for $(\lVert 1 \rVert)$ (the bridge interval). Bridge/path cubical sets are used as a model for parametric quantifiers [NVD17, Nuy18a].

On this category, we consider $\sqcup \times (i : (\lVert k \rVert))$, which is another instance of Example 6.11. A slice object $(V, \varphi)$ is dimensionally split w.r.t. this multiplier if $i \langle \varphi \rangle$ is a variable of type $(\lVert k \rVert)$ (and not $k' > k$), in which case a preimage is obtained as in Cube (so there are no shards). Hence, a slice object is on the boundary if it factors over $(0/i), (1/i) : (\cdot) \to (i : (\lVert k \rVert))$ or over $(i/i) : (i : (\lVert k' \rVert)) \to (i : (\lVert k \rVert))$ for $k' > k$. These morphisms correspond to the cells of $\mathbf{y}(i : (\lVert k + 1 \rVert))$ for $k < d$, so $\partial(i : (\lVert k \rVert)) \cong \mathbf{y}(i : (\lVert k + 1 \rVert))$ for $k < d$ and $\partial(i : (\lVert d \rVert)) \cong \top \uplus \top$.

Example 6.17 (Clocks). Let Clock be the category of clocks, used as a base category in guarded type theory [BM20]. It is the free cartesian category over $\omega$. Concretely:

- Its objects take the form $(i_1 : \odot_{k_1}, \dots, i_n : \odot_{k_n})$ where all $k_j \geq 0$. We can think of a variable of type $\odot_k$ as representing a clock (i.e. a time dimension) paired up with a certificate that we do not care what happens after the time on this clock exceeds $k$.
- Correspondingly, we should have a map $\odot_k \to \odot_\ell$ if $k \leq \ell$, because if the time exceeds $\ell$, then it certainly exceeds $k$ so our certificate can be legitimately adjusted. Then morphisms $\varphi : (i_1 : \odot_{k_1}, \dots, i_n : \odot_{k_n}) \to (j_1 : \odot_{\ell_1}, \dots, j_m : \odot_{\ell_m})$ are functions that send (de Bruijn) variables $j : \odot_\ell$ of the codomain to a variable $j \langle \varphi \rangle : \odot_k$ of the domain such that $k \leq \ell$.

This category is not objectwise pointable; indeed, the only pointable object is $(\cdot)$. On this category we consider $\sqcup \times (i : \odot_k)$, which is another instance of Example 6.11. A slice object $(V, \varphi)$ is dimensionally split w.r.t. this multiplier if $i \langle \varphi \rangle$ is a variable of type $\odot_k$ (and not $k' < k$), in which case a preimage is obtained as in Cube (so there are no shards). Thus, $\partial(i : \odot_k) \cong \mathbf{y}(i : \odot_{k-1})$ for $k > 0$ and $\partial(i : \odot_0) \cong \bot$.

Example 6.18 (Twisted cubes). Pinyo and Kraus's category of twisted cubes TwCube [PK20] can be described as a subcategory of the category of non-empty finite linear orders (or, if you want, of its skeletalization: the category of simplices Simplex). On Simplex, we can define a functor $\sqcup \ltimes \mathbb{I}$ such that $W \ltimes \mathbb{I} = W^{\mathrm{op}} \uplus_{<} W$, where we consider elements from the left smaller than those from the right. Now TwCube is the subcategory of Simplex whose objects are generated by $\top$ and $\sqcup \ltimes \mathbb{I}$ (note that every object then also has an opposite since $\top^{\mathrm{op}} = \top$ and $(V \ltimes \mathbb{I})^{\mathrm{op}} \cong V \ltimes \mathbb{I}$), and whose morphisms are given by

- $(\varphi, 0) : \mathrm{Hom}_{\mathrm{TwCube}}(V, W \ltimes \mathbb{I})$ for all $\varphi : \mathrm{Hom}_{\mathrm{TwCube}}(V, W^{\mathrm{op}})$,
- $(\varphi, 1) : \mathrm{Hom}_{\mathrm{TwCube}}(V, W \ltimes \mathbb{I})$ for all $\varphi : \mathrm{Hom}_{\mathrm{TwCube}}(V, W)$,
- $\varphi \ltimes \mathbb{I} : \mathrm{Hom}_{\mathrm{TwCube}}(V \ltimes \mathbb{I}, W \ltimes \mathbb{I})$ for all $\varphi : \mathrm{Hom}_{\mathrm{TwCube}}(V, W)$,
- $(\cdot) : \mathrm{Hom}_{\mathrm{TwCube}}(V, \top)$.

Note that this collection automatically contains all identities, composites, and opposites. Isomorphism to Pinyo and Kraus's category of twisted cubes can be seen from their ternary representation [PK20, def. 34]. We now consider the multiplier $\sqcup \ltimes \mathbb{I} : \mathrm{TwCube} \to \mathrm{TwCube}$,

16:30

A. NUYTS AND D. DEVRIESE

Vol. 20:2

which Pinyo and Kraus call the twisted prism functor. A slice object $(V, \varphi)$ is dimensionally split if and only if it is of the form $\varphi = \psi \ltimes I$ (so there are no shards). Hence, all slice objects on the boundary factor over $(((), 0) : () \to () \ltimes \mathbb{I}$ or $(((), 1) : () \to () \ltimes \mathbb{I}$, so that $\partial \mathbb{I} \cong \top \uplus \top$. The multiplier is $\top$-slice right adjoint with

$$\exists_{\mathbb{I}} : \begin{cases} (W, ((), 0)) & \mapsto W^{\text{op}} \\ (W, ((), 1)) & \mapsto W \\ (W \ltimes \mathbb{I}, () \ltimes \mathbb{I}) & \mapsto W, \end{cases} \quad (6.3)$$

with the obvious action on morphisms.

**Example 6.19** (Finite ordinals). In the base category $\omega$ of the topos of trees, used in guarded type theory [BMSS12], where $\text{Hom}(i, j) = \{ * \mid i \leq j \}$, a cartesian product is given by $i \times j = \min(i, j)$. However, this category lacks a terminal object. Instead, on the subcategory $n$ with terminal object $n-1$, which is endowed with the same cartesian product, we consider the multiplier $\sqcup \times i$, which is again an instance of Example 6.11. Any slice object $(j, *)$ (where necessarily $j \leq i$) is dimensionally split with section $*: \min(i, j) = j \to j$; hence there are no shards and $\partial i = \bot$.

**Example 6.20** (Counterexample for $\top$-slice faithful). Let $^2\text{Cube}_{\bot}$ be the category of binary cartesian cubes extended with an initial object. We consider the cartesian product $\sqcup \times \bot$ which sends everything to $\bot$. This is not $\top$-slice faithful, as $\bot_{\bot}$ sends both $(0/i)$ and $(1/i) : () \to (i : \mathbb{I})$ to $[] : (\bot, []) \to (\bot, [])$. It is not $\top$-slice full, as there is no $\psi : () \to \bot$ such that $\psi \times \bot = [] : \bot_{\bot}() \to \bot_{\bot} \bot$.

**6.4. MTraS Modalities for weakening.** Recall that we write $\sqcup \ltimes \mathbf{y}U$ for the left Kan extension of a multiplier $\sqcup \ltimes U$. For any **copointed** multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ and any presheaf $\Xi \in \text{Psh}(\mathcal{W})$, we get a presheaf morphism $\pi_1 : \Xi \ltimes \mathbf{y}U \to \Xi$. In this situation, the notations in Theorem 5.1 are not very illuminating as they would only mention $\pi_1$ and not $\Xi$ or $U$. Instead, we use the following notations:

**Notation 6.21.** A functor acting on elements:

- $\Sigma_U^{\mathbb{I}} := \Sigma^{\pi_1} : \mathcal{W}/\Xi \ltimes \mathbf{y}U \to \mathcal{W}/\Xi$
- Functors acting on presheaves:
- $\Sigma_{\mathbf{y}U}^{\Xi} := \Sigma^{\pi_1} : \text{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U) \to \text{Psh}(\mathcal{W}/\Xi)$
- $\Omega_{\mathbf{y}U}^{\Xi} := \Omega^{\pi_1} : \text{Psh}(\mathcal{W}/\Xi) \to \text{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U)$
- $\Pi_{\mathbf{y}U}^{\Xi} := \Pi^{\pi_1} : \text{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U) \to \text{Psh}(\mathcal{W}/\Xi)$

Natural transformations:

$$\begin{aligned} \text{copy}_{\mathbf{y}U}^{\Xi} &:= \text{copy}^{\pi_1} : 1 \to \Omega_{\mathbf{y}U}^{\Xi} \circ \Sigma_{\mathbf{y}U}^{\Xi} & \quad \text{drop}_{\mathbf{y}U}^{\Xi} &:= \text{drop}^{\pi_1} : \Sigma_{\mathbf{y}U}^{\Xi} \circ \Omega_{\mathbf{y}U}^{\Xi} &\to 1 \\ \text{const}_{\mathbf{y}U}^{\Xi} &:= \text{const}^{\pi_1} : 1 \to \Pi_{\mathbf{y}U}^{\Xi} \circ \Omega_{\mathbf{y}U}^{\Xi} & \quad \text{app}_{\mathbf{y}U}^{\Xi} &:= \text{app}^{\pi_1} : \Omega_{\mathbf{y}U}^{\Xi} \circ \Pi_{\mathbf{y}U}^{\Xi} &\to 1 \end{aligned}$$

For modalities, we use the weakening notations already introduced in Notation 5.3: for $\Xi = [\![\mathbb{X}\!]\!]$, we internalize the above functors as $\Sigma(u : \mathbb{U}) \dashv \Omega[u : \mathbb{U}] : \mathbb{X} \to (\mathbb{X}, u : \mathbb{U})$ and $\Pi(u : \mathbb{U}) : (\mathbb{X}, u : \mathbb{U}) \to \mathbb{X}$, sometimes abbreviating to $\Sigma u \dashv \Omega[u]$ and $\Pi u$, and the above natural transformations as $\text{drop}_u \dashv \text{const}_u$ and $\text{copy}_u \dashv \text{app}_u$.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:31

6.5. Acting on elements. A $\top$-slice right adjoint multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ as defined in Definition 6.2 gives rise to a pair of adjoint functors $\exists_U \dashv \bot_U$ between $\mathcal{W}$ and the slice category $\mathcal{W}/U$, and hence a pair of adjoint functors $\exists_U^{\top} \dashv \bot_U^{\top}$ between the categories of elements $\mathcal{W}/\top$ and $\mathcal{W}/(\top \ltimes \mathbf{y}U)$ of the empty shape context $[\cdot] := \top$ and the single variable shape context $[[u : \mathbb{U}]] := \top \ltimes \mathbf{y}U \cong \mathbf{y}U$ respectively. As any functor between base categories gives rise to a triple of adjoint functors between presheaf categories, the adjoint pair $\exists_U \dashv \bot_U$ gives rise to an adjoint quadruple $\exists_{\mathbf{y}U}^{\top\!|} \dashv \bot_{\mathbf{y}U}^{\top\!|} \dashv \forall_{\mathbf{y}U}^{\top\!|} \dashv \emptyset_{\mathbf{y}U}^{\top\!|}$ between the categories $\mathrm{Psh}(\mathcal{W}/\top)$ and $\mathrm{Psh}(\mathcal{W}/\mathbf{y}U)$ that model the modes $( )$ and $( u : \mathbb{U} )$ respectively. Thus, we are presently well-equipped to study the transpension type in a setting with at most one shape variable. Deeming this unsatisfactory, in the current section we intend to generalize the above functors, so that everywhere we mentioned $\top$ above we can instead have an arbitrary presheaf $\Xi$.

Definition 6.22. Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ and a presheaf $\Xi \in \mathrm{Obj}(\mathrm{Psh}(\mathcal{W}))$, we define:

$$\bot_U^{\prime\Xi} : \mathcal{W}/\Xi \to \mathcal{W}/(\Xi \ltimes \mathbf{y}U) : (W, \xi) \mapsto (W \ltimes U, \xi \ltimes \mathbf{y}U),$$

where $\xi \ltimes \mathbf{y}U$ denotes the $(W \ltimes U)$-shaped cell of $\Xi \ltimes \mathbf{y}U$ obtained from $\xi$.

We say that $\sqcup \ltimes U$ is:

- **Presheafwise faithful**$^{\S\!A}$ if for all $\Xi$, the functor $\bot_U^{\prime\Xi}$ is faithful,
- **Presheafwise full**$^{\S\!A}$ if for all $\Xi$, the functor $\bot_U^{\prime\Xi}$ is full,
- **Presheafwise shard-free**$^{\S\!A}$ if for all $\Xi$, the functor $\bot_U^{\prime\Xi}$ is essentially surjective on elements $(V, \varphi) \in \mathcal{W}/(\Xi \ltimes \mathbf{y}U)$ such that $\varphi$ is directly dimensionally split (Definition 6.23). A **direct shard**$^{\S\!A}$ is an element $(V, \xi) \in \mathcal{W}/\Xi \ltimes \mathbf{y}U$ that is not up to isomorphism in the image of $\bot_U^{\prime\Xi}$ even though $\xi$ is directly dimensionally split.
- **Presheafwise right adjoint**$^{\S\!A}$ if for all $\Xi$, the functor $\bot_U^{\prime\Xi}$ has a left adjoint $\exists_U^{\prime\Xi} : \mathcal{W}/(\Xi \ltimes \mathbf{y}U) \to \mathcal{W}/\Xi$. We denote the unit as $\mathrm{copy}_U^{\prime\Xi} : \mathrm{Id} \to \bot_U^{\prime\Xi}\exists_U^{\prime\Xi}$ and the co-unit as $\mathrm{drop}_U^{\prime\Xi} : \exists_U^{\prime\Xi}\bot_U^{\prime\Xi} \to \mathrm{Id}$.

Definition 6.23. Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$, we say that a $V$-shaped presheaf cell $\varphi$ of $\Xi \ltimes \mathbf{y}U$ is **directly dimensionally split**$^{\S\!A}$ with direct dimensional section $\chi : W \ltimes U \to V$ if $\varphi\chi$ is of the form $\xi \ltimes \mathbf{y}U$. The section can alternatively be presented as a morphism of elements $\chi : \bot_U^{\prime\Xi}(W, \xi) \to (V, \varphi)$. We write $\mathcal{W}//(\Xi \ltimes \mathbf{y}U)$ for the full subcategory of $\mathcal{W}/(\Xi \ltimes \mathbf{y}U)$ of directly dimensionally split cells.

We define the **(direct) boundary**$^{\S\!A}$ $\Xi \ltimes \partial U$ as the subpresheaf of $\Xi \ltimes \mathbf{y}U$ consisting of those cells that are not directly dimensionally split.

Remark 6.24. Just like $\top$-slice shard-freedom (Remark 6.9), presheafwise shard-freedom can be formulated using (co)sieves. A multiplier is presheafwise shard-free if either of the following equivalent criteria is satisfied:

- The objects in the essential image of $\bot_U^{\prime\Xi}$ constitute a cosieve in $\mathcal{W}/(\Xi \ltimes \mathbf{y}U)$.
- The objects outside the essential image of $\bot_U^{\prime\Xi}$ constitute a sieve in $\mathcal{W}/(\Xi \ltimes \mathbf{y}U)$.

The objects of the cosieve generated by objects of the essential image of $\bot_U^{\prime\Xi}$, are called directly dimensionally split. The boundary $\Xi \ltimes \partial U$ is the largest sieve in $\mathcal{W}/(\Xi \ltimes \mathbf{y}U)$ (largest subpresheaf of $\Xi \ltimes \mathbf{y}U$) that is disjoint with the objects of the essential image of $\bot_U^{\prime\Xi}$.

If $\sqcup \ltimes U$ is presheafwise fully faithful, then the above conditions are furthermore equivalent to $\bot_U^{\prime\Xi}$ being a Street opfibration.

16:32

A. NUYTS AND D. DEVRIESE

Vol. 20:2

Since we can instantiate $\Xi$ with the terminal presheaf $\top \cong \mathbf{y}\top$, we see that each of the presheafwise criteria implies the $\top$-slice criterion from Definition 6.2. Below we give *sufficient* conditions for a multiplier to satisfy the presheafwise criteria:

**Proposition 6.25.** *The multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ is:*

- *presheafwise faithful if it is $\top$-slice faithful,*
- *presheafwise full if it is $\top$-slice fully faithful,*
- *presheafwise shard-free if it is $\top$-slice full and shard-free,*
- *presheafwise right adjoint if it is $\top$-slice right adjoint.*

*Proof.* See [Nuy20b].

**Example 6.26.** Continuing Example 6.14 about $a$-ary affine cubes, let $\Xi = \mathbf{y}W$. Then $\Xi \ltimes \mathbf{y}(i : \mathbb{I}) \cong \mathbf{y}(W, i : \mathbb{I})$. Pick $(V, \varphi)$ in the category of elements, which is essentially the slice category over $(W, i : \mathbb{I})$, i.e. we view $\varphi$ as a morphism $V \to (W, i : \mathbb{I})$. Then $\varphi$ is directly dimensionally split if $i\langle \varphi \rangle$ is not an endpoint, and in that case $(V, \varphi)$ is isomorphic to $\lrcorner_{\lrcorner_i(\mathbb{I})}^{(yW)}(V', \varphi')$ where $\varphi' : V' \to W$ is obtained by removing $i\langle \varphi \rangle$ and $i$ from the domain and codomain respectively. Thus, there are no direct shards, and the boundary cells are the ones where $i\langle \varphi \rangle$ is an endpoint, i.e. $\mathbf{y}W \ltimes \partial \mathbb{I} \cong \bigoplus_{i=0}^{a-1} \mathbf{y}W$.

**Example 6.27.** Continuing Example 6.13 about $a$-ary *cartesian* cubes, let $\Xi = \mathbf{y}W$. Then $\Xi \ltimes \mathbf{y}(i : \mathbb{I}) \cong \mathbf{y}(W, i : \mathbb{I})$. Pick $(V, \varphi)$ in the category of elements, again we view $\varphi$ as a morphism $V \to (W, i : \mathbb{I})$. Then $\varphi$ is directly dimensionally split if $i\langle \varphi \rangle$ is not an endpoint, *nor equal to $j\langle \varphi \rangle$ for some variable $j$ in $W$, and in that case $(V, \varphi)$ is isomorphic to $\lrcorner_{\lrcorner_i(\mathbb{I})}^{(yW)}(V', \varphi')$ where $\varphi' : V' \to W$ is obtained by removing $i\langle \varphi \rangle$ and $i$ from the domain and codomain respectively. Thus, there are no direct shards, and the boundary cells are the ones where $i\langle \varphi \rangle$ is an endpoint or equal to $j\langle \varphi \rangle$ for some variable in $W$.*

The following (fairly obvious) theorem is paramount to the semantics of transpension elimination (Section 9.3) and the $\Phi$-rule (Section 10.2):

**Theorem 6.28** (Quotient$^{\S A}$ theorem). *If a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ is $\top$-slice fully faithful and shard-free (hence presheafwise fully faithful and shard-free), then $\lrcorner_{\mathbb{I}}^{(j\Xi)} : \mathcal{W}/\Xi \to \mathcal{W}/(\Xi \ltimes \mathbf{y}U)$ is an equivalence of categories.*

**6.6. MTraS Modalities for multipliers.** We are now well-equipped to study the transpension type in a setting with multiple shape variables.

**Theorem 6.29.** *Any $\top$-slice right adjoint$^{17}$ multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ and any presheaf $\Xi \in \mathrm{Psh}(\mathcal{W})$ give rise to a quadruple of adjoint functors*

$$\exists_{\mathbf{y}U}^{\Xi} \dashv \lrcorner_{\mathbf{y}U}^{\Xi} \dashv \forall_{\mathbf{y}U}^{\Xi} \dashv \Diamond_{\mathbf{y}U}^{\Xi},$$

$$\exists_{\mathbf{y}U}^{\Xi}, \forall_{\mathbf{y}U}^{\Xi} : \mathrm{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U) \to \mathrm{Psh}(\mathcal{W}/\Xi) \quad \lrcorner_{\mathbf{y}U}^{\Xi}, \Diamond_{\mathbf{y}U}^{\Xi} : \mathrm{Psh}(\mathcal{W}/\Xi) \to \mathrm{Psh}(\mathcal{W}/\Xi \ltimes \mathbf{y}U).$$

*If $\Xi = [\![\mathbb{X}\!]\!]$, the latter three can be internalized as modalities (with an additional left name) $\exists(u : \mathbb{U}) \dashv \lrcorner[u : \mathbb{U}] \dashv \forall(u : \mathbb{U}) \dashv \Diamond[u : \mathbb{U}]$ with*

$$\llbracket \widehat{\blacksquare}_{\lrcorner[u]}^{\exists u} \rrbracket = \exists_{\mathbf{y}U}^{\Xi}, \quad \llbracket \lrcorner[u] \rrbracket = \llbracket \widehat{\blacksquare}_{\forall u}^{\lrcorner[u]} \rrbracket = \lrcorner_{\mathbf{y}U}^{\Xi}, \quad \llbracket \forall u \rrbracket = \llbracket \widehat{\blacksquare}_{\Diamond[u]}^{\forall u} \rrbracket = \forall_{\mathbf{y}U}^{\Xi}, \quad \llbracket \Diamond[u] \rrbracket = \Diamond_{\mathbf{y}U}^{\Xi}.$$

$^{17}$Without $\top$-slice right adjointness, we lose the leftmost adjoint functor $\exists_{\mathbf{y}U}^{\Xi}$ and the leftmost adjoint modality $\lrcorner[u]$.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:33

Overloading some notations from Theorem 5.1 we denote the units and co-units as

$$\begin{array}{l} \mathsf {c o p y} _ {\mathbf {y} U} ^ {\Xi}: 1 \rightarrow \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \circ \exists_ {\mathbf {y} U} ^ {\Xi} \\ \operatorname {c o n s t} _ {\mathbf {y} U} ^ {\Xi}: 1 \rightarrow \forall_ {\mathbf {y} U} ^ {\Xi} \circ \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \\ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Xi}: 1 \rightarrow \mathbb {Q} _ {\mathbf {y} U} ^ {\Xi} \circ \forall_ {\mathbf {y} U} ^ {\Xi} \\ \mathsf {d r o p} _ {u} \vDash \mathsf {c o n s t} _ {u}: 1 \Rightarrow \forall u \circ \lrcorner [ u ] \\ \mathsf {a p p} _ {u} \vDash \operatorname{reidx} _ {u}: 1 \Rightarrow \mathbb {Q} [ u ] \circ \forall u \\ \mathsf {d r o p} _ {\mathbf {y} U} ^ {\Xi}: \exists_ {\mathbf {y} U} ^ {\Xi} \circ \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \rightarrow 1 \\ \mathsf {a p p} _ {\mathbf {y} U} ^ {\Xi}: \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} \circ \forall_ {\mathbf {y} U} ^ {\Xi} \rightarrow 1 \\ \mathsf {u n m e r} _ {\mathbf {y} U} ^ {\Xi}: \forall_ {\mathbf {y} U} ^ {\Xi} \circ \mathbb {Q} _ {\mathbf {y} U} ^ {\Xi} \rightarrow 1 \\ \mathsf {c o p y} _ {u} \vDash \mathsf {a p p} _ {u}: \lrcorner [ u ] \circ \forall u \Rightarrow 1 \\ \mathsf {c o n s t} _ {u} \vDash \mathsf {u n m e r} _ {u}: \forall u \circ \mathbb {Q} [ u ] \Rightarrow 1 \\ \end{array}$$

where reidx stands for reindex and unmer is the negation of mer which stands for meridian.

Proof. Via left Kan extension, precomposition and right Kan extension [Sta19], the pair of adjoint functors $\exists_U^{\Xi} \dashv \mathbb{J}_U^{\Xi}$ gives rise to a quadruple of adjoint functors $\exists_{\mathbf{y}U}^{\Xi} \dashv \mathbb{J}_{\mathbf{y}U}^{\Xi} \dashv \mathbb{V}_{\mathbf{y}U}^{\Xi} \dashv \mathbb{Q}_{\mathbf{y}U}^{\Xi}$ between the presheaf categories. (For the middle two, we can choose whether we derive them from $\exists_U^{\Xi}$ or from $\mathbb{J}_U^{\Xi}$; the resulting functors are naturally isomorphic. We will specify our choice when relevant.)

Notation 6.30. Again, due to the (purely sugarous) usage of shape variables, we may end up with variable renamings that are sugar for the identity, e.g.

$$\mathsf {a p p} _ {(v / u: \mathbb {U})}: \mathbb {J} [ v: \mathbb {U} ] \circ \forall (u: \mathbb {U}) \Rightarrow \Omega [ v: \mathbb {U}, u := v ]$$

$$\operatorname{reidx} _ {(v / u: \mathbb {U})}: \Omega [ v: \mathbb {U}, u := v ] \Rightarrow \mathbb {Q} [ v: \mathbb {U} ] \circ \forall (u: \mathbb {U})$$

are exactly the same 2-cells as

$$\mathsf {a p p} _ {(u: \mathbb {U})}: \mathbb {J} [ u: \mathbb {U} ] \circ \forall (u: \mathbb {U}) \Rightarrow 1$$

$$\operatorname{reidx} _ {(u: \mathbb {U})}: 1 \Rightarrow \mathbb {Q} [ u: \mathbb {U} ] \circ \forall (u: \mathbb {U}).$$

Whereas Theorem 5.1 clearly states the meaning of the functors introduced there, little can be said about the meaning of the functors introduced in Theorem 6.29 without knowing more about the multiplier involved. The following theorem clarifies the leftmost three functors:

Theorem 6.31 (Quantification). If $\sqcup \ltimes U$ is

(1) $\top$-slice fully faithful, then $\mathsf{drop}_{\mathbf{y}U}^{\Xi}$, $\mathsf{const}_{\mathbf{y}U}^{\Xi}$ and $\mathsf{unmer}_{\mathbf{y}U}^{\Xi}$ are natural isomorphisms.
(2) copointed, then we have

(a) $\mathsf{hide}_{\mathbf{y}U}^{\Xi}: \Sigma_{\mathbf{y}U}^{\Xi} \to \exists_{\mathbf{y}U}^{\Xi}$ (if $\top$-slice right adjoint),
(b) $\mathsf{spoil}_{\mathbf{y}U}^{\Xi}: \mathbb{J}_{\mathbf{y}U}^{\Xi} \to \Omega_{\mathbf{y}U}^{\Xi}$, which can be internalized (if $\top$-slice right adjoint) as $\exists u \Leftarrow \Sigma u: \mathsf{hide}_u \vDash \mathsf{spoil}_u: \mathbb{J}[u] \Rightarrow \Omega[u]$,
(c) $\mathsf{cospoil}_{\mathbf{y}U}^{\Xi}: \Pi_{\mathbf{y}U}^{\Xi} \to \forall_{\mathbf{y}U}^{\Xi}$, which can be internalized as $\Omega[u] \Leftarrow \mathbb{J}[u]: \mathsf{spoil}_u \vDash \mathsf{cospoil}_u: \Pi u \Rightarrow \forall u$.

(3) cartesian, then we have:

$$\exists_ {\mathbf {y} U} ^ {\Xi} = \Sigma_ {\mathbf {y} U} ^ {\Xi}, \qquad \mathbb {J} _ {\mathbf {y} U} ^ {\Xi} = \Omega_ {\mathbf {y} U} ^ {\Xi}, \qquad \forall_ {\mathbf {y} U} ^ {\Xi} = \Pi_ {\mathbf {y} U} ^ {\Xi}.$$

The equalities assume that $\exists_U: \mathcal{W}/U \to \mathcal{W}$ is defined on the nose by $\exists_U(W, \psi) = W$ and that $\mathbb{J}_{\mathbf{y}U}^{\Xi}$ and $\forall_{\mathbf{y}U}^{\Xi}$ are constructed from $\exists_U^{\Xi}$ by precomposition and right Kan extension, respectively. Failing this, we only get natural isomorphisms.

Let us try to interpret this on a more intuitive level:

16:34

A. NUYTS AND D. DEVRIESE

Vol. 20:2

(1) For $\top$-slice fully faithful $\mathbb{U}$, invertibility of $\text{const}_u$ means that any 'function' $f$ of type $\langle \forall u \mid \langle \exists[u] \mid T \rangle \rangle$ is necessarily constant, i.e. elements of $\langle \exists[u] \mid T \rangle$ cannot depend on the shape variable $u$ and are instead *fresh* for $u$. With that in mind, invertibility of $\text{drop}_{\mathbf{y}U}^{\Xi}$ indicates that the $\Sigma$-like operation $\exists_{\mathbf{y}U}^{\Xi}$ hides its first component $u : \mathbb{U}$. Indeed, knowing that the second component of $\exists_{\mathbf{y}U}^{\Xi} \exists_{\mathbf{y}U}^{\Xi} \Gamma$ is fresh for $u$, one might expect that $\exists_{\mathbf{y}U}^{\Xi} \exists_{\mathbf{y}U}^{\Xi} \Gamma$ behaves somewhat like a non-dependent product (which is exactly what happens in the cartesian setting). Instead, $\exists_{\mathbf{y}U}^{\Xi}$ cancels out $\exists_{\mathbf{y}U}^{\Xi}$, so apparently if the second component does not depend on $u$, then $u$ is lost altogether. Finally function application, which is basically the projection operation from Proposition 3.3,

$$\text{app}_u : (\exists[u] \mid \langle \forall u \mid T \rangle) \rightarrow T[\mathbf{a}_{\text{app}_u}]. \quad (6.4)$$

requires that the applied function of type $\langle \forall u \mid T \rangle$ be fresh for $u$, as one would expect in linear and affine systems and as we saw in FF:FORALL:ELIM in Fig. 1.

(2) If $\mathbb{U}$ is copointed (which is perfectly combinable with being $\top$-slice fully faithful), i.e. if weakening is allowed for $u : \mathbb{U}$, then we get three additional operations. The 2-cell $\text{spoil}_u$ allows us to forget that something is fresh for $u$. This would not be possible without weakening because then the modality $\Omega[u]$ expressing potential non-freshness would not even be available. The 2-cell $\text{cospoil}_u$ allows us to unnecessarily restrict a function's usage to variables w.r.t. which the function is fresh. The semantic substitution $\text{hide}_{\mathbf{y}U}^{\Xi} : \Sigma_{\mathbf{y}U}^{\Xi}[\Gamma] \rightarrow \exists_{\mathbf{y}U}^{\Xi} \Gamma$ at mode $\Xi$ which is internally available as $\mathbf{a}_{\text{spoil}_u}^{\text{hide}_u} : (\Gamma, \mathbf{a}_{\Omega[u]}^{\Xi u}) \rightarrow (\Gamma, \mathbf{a}_{\exists[u]}^{\Xi u})$ allows us to hide the first component $u : \mathbb{U}$. The effect of applying this substitution is effectively a weakening over $u : \mathbb{U}$, in the sense that the context $\exists_{\mathbf{y}U}^{\Xi} \Gamma$ can be regarded as not containing the variable $u$ except in the form of a hidden mention necessary to make the dependencies of $\Gamma$ work out. Note that for shapes that are not $\top$-slice fully faithful, the words 'hidden' and 'fresh' need to be taken with a grain of salt. Indeed, for cartesian shapes we should ignore them altogether:
(3) If $\mathbb{U}$ is cartesian, then the leftmost three functors become identical to the ones in Section 6.4. In particular, fresh weakening and weakening coincide and the word 'fresh' becomes meaningless.

In order to have some general terminology, we will speak of the **hiding** existential $\exists u$, **fresh** weakening $\exists[u]$ and **substructural** (e.g. linear/affine) functions $\forall u$ even when the specifics of the multiplier are unclear and it is potentially cartesian.

**6.7. Cartesian multipliers.** The cartesian case of the quantification Theorem 6.31 may look like all our efforts with multipliers are useless, but let's not forget that there is now a further right adjoint to these well-known functors:

$$\Sigma_{\mathbf{y}U}^{\Xi} \dashv \Omega_{\mathbf{y}U}^{\Xi} \dashv \Pi_{\mathbf{y}U}^{\Xi} \dashv \Diamond_{\mathbf{y}U}^{\Xi}.$$

What we have proven for cartesian shapes is that, for any representable presheaf $\mathbf{y}U \in \text{Psh}(\mathcal{W})$ such that cartesian products with $U$ exist in the base category $\mathcal{W}$ (yielding a cartesian multiplier $\sqcup \times U : \mathcal{W} \rightarrow \mathcal{W}$), there is a right adjoint to the $\Pi$-type! Licata et al. [LOPS18] have used a right adjoint to the non-dependent function type functor $(\mathbf{y}U \rightarrow \sqcup) = \Pi_{\mathbf{y}U}^{\Xi} \circ \Omega_{\mathbf{y}U}^{\Xi}$, called the *amazing right adjoint* and necessarily given by $(\mathbf{y}U \nmid \sqcup) = \Pi_{\mathbf{y}U}^{\Xi} \circ \Diamond_{\mathbf{y}U}^{\Xi}$, but the current result appears stronger.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:35

Remarkably, it is not, and it is not novel either. As conjectured by Lawvere, proven by Freyd and published by Yetter [Yet87], for an arbitrary object $\mathbb{U}$ in an arbitrary topos, the transpension functor (there unnamed and denoted $\nabla$) over $\mathbb{U}$ exists if the amazing right adjoint exists. Indeed, in that case it can be constructed by the following pullback:

$$\begin{array}{ccc} \Sigma(u : \mathbb{U}).\circ[u]T & \longrightarrow & \mathbb{U} \surd (\Sigma(P : \text{Prop}).(P \to T)) \\ \downarrow_{\text{fst}} & & \downarrow_{\mathbb{U}\surd\text{fst}} \\ \mathbb{U} & \xrightarrow{(\lambda f.f \equiv \text{id}_{\mathbb{U}})^\top} & \mathbb{U} \surd \text{Prop} \end{array}$$

where $g^\top$ denotes the transpose of $g$ under $(\mathbb{U} \to \sqcup) \dashv (\mathbb{U} \surd \sqcup)$.

**6.8. Further reading.** We refer to the technical report [Nuy20b] for more information on

- composite multipliers $\sqcup \ltimes (U \ltimes U') := (\sqcup \ltimes U) \ltimes U'$,
- morphisms of multipliers $\sqcup \ltimes v : \sqcup \ltimes U \to \sqcup \ltimes U'$ (together with the previous point one could formalize the exchange rule),
- acting on slice objects as opposed to acting on elements (Section 6.5),
- properties of $\sqcup \ltimes \mathbf{y}U : \text{Psh}(\mathcal{W}) \to \text{Psh}(\mathcal{W})$, the left Kan extension along $\sqcup \ltimes U$, again viewed as a multiplier for $\mathbf{y}U$,
- non-endo multipliers $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$,
- rules for commuting (co)quantifiers for multipliers, (co)quantifiers for substitution, and (when adding the transpension type to an already modal type system) prior modalities.

## 7. THE FULLY FAITHFUL TRANSPENSION SYSTEM (FFTRAS) REVISITED

In Section 7.1, we give a pseudo-embedding of FFTraS (Section 2) into MTraS instantiated on a $\top$-slice fully faithful shape $\mathbb{U}$. In Sections 7.2 and 7.3, we revisit the results about internal transposition and higher-dimensional pattern-matching from Sections 2.3 and 2.4, as these also work for other shapes. Poles (Section 2.2) will be revisited in Section 9.1.

**7.1. Pseudo-Embedding of FFTraS in MTraS.** We give a pseudo-embedding of FFTraS into MTraS instantiated on a $\top$-slice fully faithful shape $\mathbb{U}$. Pseudo, in the sense that FF:CTX-FORALL:NIL will be only an isomorphism and some commutation properties w.r.t. shape substitution will only hold up to isomorphism, implying that a few other rules will need some adjustments before their translation is well-typed. We do not pay too much attention to those matters: the purpose of Section 2 was didactical and the purpose of the embedding is to show that it was also morally correct.

**7.1.1. Metatype of the embedding.** The judgement forms are translated as follows:

- A context $\Gamma \text{ctx}$ is translated as a pair consisting of a shape context $\{\Gamma\} \text{shpctx}$ listing the shape variables in $\Gamma$ and an internal context $\{\Gamma\} \mid \langle \Gamma \rangle \text{ctx}$.

16:36

A. NUYTS AND D. DEVRIESE

Vol. 20:2

- • A substitution $\sigma : \Delta \to \Gamma$ is translated as a pair consisting of a shape substitution $\{\sigma\} : [\![\Gamma]\!] \to [\![\Delta]\!]$ and an internal substitution $\{\Gamma\} \mid \langle \sigma \rangle : \langle \Gamma \rangle \to (\langle \Delta \rangle, \mathbf{\Omega}_{\Omega[\{\sigma\}]}^{\Omega[\{\sigma\}]})$. We point out that if $\{\sigma\} \neq 1$, then translating $t[\sigma] : T[\sigma]$ is far from trivial. Since FF:CTX-SHP:WKN is the only source of such substitutions, we will generally assume that $\{\sigma\} = 1$ and not worry about the general case. Then, we have $\{\Gamma\} = \{\Delta\} \mid \langle \sigma \rangle : \langle \Gamma \rangle \to \langle \Delta \rangle$.
- • A type $\Gamma \vdash T$ type is translated to $\{\Gamma\} \mid \langle \Gamma \rangle \vdash \langle T \rangle$ type.
- • A term $\Gamma \vdash t : T$ is translated to $\{\Gamma\} \mid \langle \Gamma \rangle \vdash \langle t \rangle : \langle T \rangle$.

7.1.2. *Structural rules of MLTT.* The shape interpretation $\{\sqcup\}$ ignores non-shape variables, and the internal interpretation $\langle \sqcup \rangle$ respects the structural rules of MLTT:

$$\begin{array}{l} \{\cdot\} = \cdot \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \langle \cdot \rangle = \cdot \\ \{\Gamma, x : A\} = \{\Gamma\} \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \langle \Gamma, x : A\rangle = \langle \Gamma\rangle, x : \langle A\rangle \\ \{1, t/x\} = 1 \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \langle t/x\rangle = \langle t\rangle/x \\ \{x/\oslash\} = 1 \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \langle x/\oslash\rangle = x/\oslash \\ \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \langle x\rangle = x \end{array}$$

7.1.3. *Linear/affine shape variables.* The shape interpretation $\{\sqcup\}$ retains shape variables. In the fully faithful system, if a variable occurred to the left of $u : \mathbb{U}$, this meant that it was fresh for $u$. In MTraS, the shape variable $u : \mathbb{U}$ is of course added to the shape context, so we cannot use its position to signal which variables in $\Gamma$ are and are not fresh for $u$. Instead, we keep track of this using the fresh weakening operation on contexts $\mathbf{\Omega}_{\forall u}^{\mathbb{I}[u]}$.

$$\begin{array}{l} \{\Gamma, u : \mathbb{U}\} = \{\Gamma\}, u : \mathbb{U} \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \langle \Gamma, u : \mathbb{U} \rangle = \langle \Gamma\rangle, \mathbf{\Omega}_{\forall u}^{\mathbb{I}[u]} \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \quad \begin{array}{l} (\text{FF:CTX-SHP}) \\ \{\sigma, u/u\} = \{\sigma\}, u/u \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \quad \begin{array}{l} (\text{FF:CTX-SHP:FMAP}) \\ \{\sigma, u/\oslash\} = \{\sigma\}, u/\oslash \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \quad \begin{array}{l} \langle \sigma, u/\oslash\rangle = \langle \sigma\rangle, \mathbf{\alpha}_{\text{cospoil}_u: \Pi u \Rightarrow \forall u}^{\text{spoil}_u: \mathbb{I}[u] \Rightarrow \Omega[u]} \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \quad (\text{FF:CTX-SHP:WKN})$$

7.1.4. *Linear/affine function type.* The $\forall$-type translates to a modal type:

$$\begin{array}{l} \text{FF:FORALL} \\ \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \quad \begin{array}{l} \text{FF:FORALL:INTRO} \\ \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \quad \begin{array}{l} \{ \Gamma\}, u : \mathbb{U} \mid \langle \Gamma\rangle, \mathbf{\Omega}_{\forall u}^{\mathbb{I}[u]} \vdash \langle a\rangle : \langle A\rangle \\ \hline \{ \Gamma\} \mid \langle \Gamma\rangle \vdash \text{mod}_{\forall u} \langle a\rangle : \langle \forall u \mid \langle A\rangle \rangle \end{array}$$

$^{18}$Note that the latter is equivalent to an internal substitution $\{\Delta\} \mid \langle \sigma \rangle' : (\langle \Gamma\rangle, \mathbf{\Omega}_{\Omega[\{\sigma\}]}^{\Sigma[\{\sigma\}]} \to \langle \Delta\rangle$, but the advantage of $\mathbf{\Omega}_{\Omega[\{\sigma\}]}^{\Omega[\{\sigma\}]}$ is that it is strictly functorial.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:37

Application is translated using Proposition 3.3. Let \(\Theta = \Gamma, u: \mathbb{U}, \delta: \Delta\) with no shape variables in \(\Delta\). Then \(\{\Theta\} = \{\Gamma\}, u: \mathbb{U}\) and \(\langle \Theta \rangle = \langle \Gamma \rangle, \widehat{\mathbf{a}}_{\forall u}^{\exists [u]}, \langle \Delta \rangle\).

FF:FORALL:ELIM

\[
\begin{array}{l} \{\Gamma \} \mid \langle \Gamma \rangle \vdash f: \langle \forall u \mid \langle A \rangle \rangle \\ \frac {\{\Gamma \} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u \circ \exists [ u ]} ^ {\exists u \circ \exists [ u ]} \vdash f [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}} ] : \left\langle \forall u \mid \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} ] \right\rangle}{\{\Gamma \} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} , \langle \Delta \rangle , \widehat {\mathbf {a}} _ {\exists [ u ]} ^ {\exists u} \vdash f [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}} ] : \left\langle \forall u \mid \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} ] \right\rangle} \\ \frac {\{\Gamma \} , u : \mathbb {U} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} , \langle \Delta \rangle \vdash \mathsf {a p p} _ {u} \cdot_ {\exists [ u ]} f [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}} ] : \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]} ] [ \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}, \widehat {\mathbf {a}} _ {\text {app} _ {u}} ^ {\text {copy} _ {u}} ] = \langle A \rangle}{\end{array}
\]

Observe that, lacking existential quantification for contexts in Section 2, the application rule FF:FORALL:ELIM simply discarded the non-fresh part \(\Delta\). In the target language, variables under \(\widehat{\mathbf{a}}_{\exists [u]}^{\exists u}\) can only be used if they are annotated with a modality \(\mu\) from which there is a 2-cell \(\alpha : \mu \Rightarrow \exists [u]\), i.e. if they are fresh for \(u\). However, recall that the word 'fresh' needs to be taken with a grain of salt when we are not dealing with a \(\top\)-slice fully faithful shape. For example, if \(\mathbb{U}\) is cartesian, then \(\widehat{\mathbf{a}}_{\exists [u]}^{\exists u} = \widehat{\mathbf{a}}_{\Omega [u]}^{\Sigma u}\), so that the aggregation of shape and type context in the premise and conclusion of the app\(_u\)-rule

\[
\frac {\mathbb {X} , \mid \Gamma , \widehat {\mathbf {a}} _ {\Omega [ u ]} ^ {\Sigma u} \vdash f : \langle \Pi   u \mid A \rangle}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {a p p} _ {u} \cdot_ {\Omega [ u ]} f : A [ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {u}} ^ {\mathsf {c o p y} _ {u}} ]}
\]

are isomorphic: \(\llbracket \mathbb{X}\rrbracket .(\Sigma (\mathbf{y}U).\llbracket \Gamma \rrbracket)\cong (\llbracket \mathbb{X}\rrbracket \times \mathbf{y}U).\llbracket \Gamma \rrbracket .\)

7.1.5. Telescope quantification. Let \(\Theta = (\Gamma, u: \mathbb{U}, \delta: \Delta)\) with no shape variables in \(\Delta\). Then \([\forall u] \Theta = (\Gamma, \forall u. (\delta: \Delta))\). We translate this as follows:

\[
\{[ \forall u ] \Theta \} = \{\Gamma , \forall u. (\delta : \Delta) \} = \{\Gamma \} \quad \langle [ \forall u ] \Theta \rangle = \langle \Theta \rangle , \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u} \quad (\text {FF:CTX - FORALL})
\]

Let \(\rho = (\sigma, u / u, \tau / \delta') : \Theta = (\Gamma, u : \mathbb{U}, \delta : \Delta) \to \Theta' = (\Gamma', u : \mathbb{U}, \delta' : \Delta')\). Then \([\forall (u / u)]\rho = (\sigma, \lambda u.\tau / \lambda u.\delta')\). We translate this as follows:

\[
\{[ \forall (u / u) ] \rho \} = \left\{\sigma , \lambda u. \tau / \lambda u. \delta^ {\prime} \right\} = \{\sigma \} \quad \langle [ \forall (u / u) ] \rho \rangle = \langle \rho \rangle , \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u} \quad (\text {FF:CTX - FORALL:FMAP})
\]

The rule FF:CTX-FORALL:NIL concerns  \( (\Gamma,\forall u.())=\forall u \)  which translates to  \( \{\Gamma\}\mid\langle\Gamma\rangle,\widehat{\mathbf{a}}_{\forall u}^{\exists[u]},\widehat{\mathbf{a}}_{\{u\}}\forall u \)  ctx, which is isomorphic to  \( \{\Gamma\}\mid\langle\Gamma\rangle \)  ctx by the 2-cell  \( (1_{\Gamma},\widehat{\mathbf{a}}_{\text{unmer}_{u}:\forall u\circ\{u\}\Rightarrow1}^{\text{const}_{u}:1\Rightarrow\forall u\circ\exists[u]}) \)  because U is T-slice fully faithful (quantification Theorem 6.31). Naturality of  \( a_{unmer_{u}}^{const_{u}} \)  models FF:CTX-FORALL:FMAP:NIL.

7.1.6. Telescope application. Let \(\Theta = (\Gamma, u: \mathbb{U}, \delta: \Delta)\) with no shape variables in \(\Delta\). Then \(\mathsf{app}_{\Theta} = (u / u, (\lambda u.\delta) u / \delta): ([\forall u] \Theta, u: \mathbb{U}) = (\Gamma, \forall u. (\delta: \Delta), u: \mathbb{U}) \to \Theta\). We translate this using the 2-cell

\[
\{\Gamma \}, u: \mathbb {U} \mid \langle \mathsf {a p p} _ {\Theta} \rangle = (\widehat {\mathbf {a}} _ {\text {reidx} _ {u}: 1 \Rightarrow \{u \} \circ \forall u} ^ {\text {app} _ {u}: \exists [ u ] \circ \forall u \Rightarrow 1}): (\langle \Theta \rangle , \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u}, \widehat {\mathbf {a}} _ {\{u \}} ^ {\exists [ u ]}) \to \langle \Theta \rangle \quad (\text {FF:CTX - APP})
\]

naturality of which models FF:CTX-APP:NAT.

If \(\Delta\) is empty, then \(\langle \Theta \rangle = (\langle \Gamma \rangle ,\widehat{\mathbf{a}}_{\forall u}^{\exists [u]})\), so that

\[
\begin{array}{l} \{\Gamma \}, u: \mathbb {U} \mid \left\langle \mathsf {a p p} _ {(\Gamma , u: \mathbb {U})} \right\rangle = (\widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}, \widehat {\mathbf {a}} _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}}) = (\widehat {\mathbf {a}} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}}, \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}) \\ : (\langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}, \widehat {\mathbf {a}} _ {\{u \}} ^ {\forall u}, \widehat {\mathbf {a}} _ {\{u \}} ^ {\exists [ u ]}) \to (\langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\forall u} ^ {\exists [ u ]}) \\ \end{array}
\]

16:38

A. Nuyts and D. Devriese

Vol. 20:2

Now \(\mathbf{Q}_{\mathrm{unmer}_u}^{\mathrm{const}_u}\) models the equation in FF:CTX-FORALL:NIL which well-typedness of FF:CTX-APP:NIL relies on, so it can be regarded as the identity and the above essentially models FF:CTX-APP:NIL.

Similarly, the rule FF:CTX-FORALL:FMAP:CTX-APP concerns  \( [\forall u/u]app_{\Theta} \) , which translates to

\[
\{\Gamma \} \mid (\langle \mathsf {a p p} _ {\Theta} \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}) = (\mathbf {a} _ {\text {reid} x _ {u}} ^ {\text {app} _ {u}}, \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}) = (\widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}, \mathbf {a} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}})
\]

\[
: (\langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}, \widehat {\mathbf {a}} _ {\forall u} ^ {\mathbb {Q} [ u ]}, \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}) \to (\langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u}),
\]

essentially modelling FF:CTX-FORALL:FMAP:CTX-APP.

7.1.7. Transpension type. Let \(\Theta = (\Gamma, u : \mathbb{U}, \delta : \Delta)\) with no shape variables in \(\Delta\). The transpension type translates to a modal type:

FF:TRANSP

\[
\frac {\{\Gamma \} \mid \langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \vdash \langle A \rangle \text {type}}{\{\Gamma \} , u : \mathbb {U} \mid \langle \Theta \rangle \vdash \langle \mathbb {Q} [ u ] \mid \langle A \rangle \rangle \text {type}}
\]

FF:TRANSP:INTRO

\[
\frac {\{\Gamma \} \mid \langle \Theta \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \vdash \langle a \rangle : \langle A \rangle}{\{\Gamma \} , u : \mathbb {U} \mid \langle \Theta \rangle \vdash \operatorname{mod} _ {\mathbb {Q} [ u ]} a : \langle \mathbb {Q} [ u ] \mid \langle A \rangle \rangle}
\]

The eliminator is translated using Proposition 3.3.

FF:TRANSP:ELIM

\[
\frac {\{\Gamma \} , u : \mathbb {U} \mid \langle \Gamma \rangle , \widehat {\mathbf {a}} _ {\mathbb {U}} ^ {\mathbb {Q} [ u ]} \vdash t : \left\langle \forall u \mid \langle A \rangle [ \widehat {\mathbf {a}} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}} ] \right\rangle}{\{\Gamma \} \mid \langle \Gamma \rangle \vdash \text {unmer} _ {u} \cdot_ {\forall u} t : \langle A \rangle}
\]

Again \(\mathbf{Q}_{\mathrm{unmer}_u^{-1}}^{\mathrm{const}_u^{-1}}\) just models FF:CTX-FORALL:NIL and can be ignored. The \(\beta\)- and \(\eta\)-rules are the ones form Proposition 3.3, and the naturality rules amount to

\[
(\mathsf {m o d} _ {\forall u} \langle a \rangle) [ \langle \rho \rangle ] = \mathsf {m o d} _ {\forall u} \left(\langle a \rangle \Big [ \langle \rho \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \Big ]\right), \qquad \langle \forall u | \langle A \rangle \rangle [ \langle \rho \rangle ] = \Big \langle \forall u | \langle A \rangle \Big [ \langle \rho \rangle , \widehat {\mathbf {a}} _ {\mathbb {Q} [ u ]} ^ {\forall u} \Big ] \Big \rangle .
\]

This concludes the embedding for the selected typing rules in Fig. 1.

7.2. Internal transposition. In Section 2.3, we proved the isomorphism

\[
(\forall (u: \mathbb {U}). A) \rightarrow B \quad \cong \quad \forall (u: \mathbb {U}). (A \rightarrow \mathbb {Q} [ u ] B). \tag {7.1}
\]

The MTraS equivalent,

\[
(\forall u \mid A) \to B ^ {\prime} \quad \cong \quad \left\langle \forall u \mid A \to \left\langle \mathbb {Q} [ u ] \mid B ^ {\prime} [ \mathbf {a} _ {\text {unmer} _ {u} ^ {- 1}} ^ {\text {const} _ {u} ^ {- 1}} ] \right\rangle \right\rangle
\]

is not in general true (or even statable) but for \(\top\)-slice fully faithful multipliers it follows from the following instance of Proposition 3.4 (which holds in general)

\[
\left\langle \mathbb {Q} [ u ] \mid (\forall u \mid A [ \mathbf {a} _ {\text {reid} x _ {u}} ^ {\text {app} _ {u}} ]) \rightarrow B \right\rangle \quad \cong \quad (A \rightarrow \langle \mathbb {Q} [ u ] \mid B \rangle) \tag {7.2}
\]

by applying \(\langle \forall u\mid \sqcup \rangle\) to both sides, redefining \(B^{\prime} = B[\mathbf{a}_{\mathrm{unmer}_u}^{\mathrm{const}_u}]\) and using the quantification Theorem 6.31.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:39

7.3. Higher-dimensional pattern matching. Deriving HDPM from internal transposition for general multipliers is a bit more involved than it was for FFTraS (Section 2.4) because we have to use Eq. (7.2) instead of Eq. (7.1). However, we can construct an isomorphism \( i: \langle \forall u | A \uplus B \rangle \cong \langle \forall u | A \rangle \uplus \langle \forall u | B \rangle \) directly by translating from Section 2.4. Again, the map to the left is trivial by pattern matching (which is still the original eliminator for modal types!). The map to the right is given in either system by:

\[
\begin{array}{l} i: (\forall u. A \uplus B) \rightarrow (\forall u. A) \uplus (\forall u. B) \quad \boxed {\text {FFTraS}} \\ i \hat {c} = \text {unmer} \left(u. \text {case} \hat {c} u \text {of} \left\{ \begin{array}{l l} \text {inl} a & \mapsto \quad \text {mer} [ u ] (\text {inl} (\lambda u. a)) \\ \text {inr} b & \mapsto \quad \text {mer} [ u ] (\text {inr} (\lambda u. b)) \end{array} \right\}\right) \\ i: \langle \forall u | A \uplus B \rangle \rightarrow \langle \forall u | A \rangle \uplus \langle \forall u | B \rangle \quad \boxed {\text { MTraS }} \\ i \hat {c} = \text {unmer} _ {u} \cdot_ {\forall u} \text {case} (\text {app} _ {u} \cdot_ {\exists [ u ]} \hat {c} _ {\text {const} _ {u}} ^ {\text {drop} _ {u}}) \text {of} \left\{ \begin{array}{l} \text {inl} a \mapsto \text {mod} _ {\langle [ u ]} (\text {inl} (\text {mod} _ {\forall u} (a _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}}))) \\ \text {inr} b \mapsto \text {mod} _ {\langle [ u ]} (\text {inr} (\text {mod} _ {\forall u} (b _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}}))) \end{array} \right\}. \\ \end{array}
\]

## 8. ADDITIONAL TYPING RULES

In this section, we add a few extensions to MTraS in order to reason about boundaries, and in order to recover all known presheaf operators in Section 10.

8.1. Subobject classifier. We add a universe of propositions (semantically the subobject classifier) Prop :  \( U_{0} \) , with implicit encoding and decoding operations à la Coquand. This universe is closed under logical operators and weak DRAs [Nuy20a, §6.5]. This is necessary to talk about  \( \Psi \)  and  \( \Phi \) . We identify all proofs of the same proposition.

8.2. Boundary predicate. We add the following shape context constructor:

|  SHP-CTX-BOUNDARY  |   |
| --- | --- |
|  X shpctx | U shape  |
|  X, u : ∂U shpctx  |   |

modelling \(\llbracket \mathbb{X}, u : \partial \mathbb{U} \rrbracket = \llbracket \mathbb{X} \rrbracket \ltimes \partial U\) (Definition 6.23). Write \((u \in \partial \mathbb{U})\) for the presheaf morphism that includes \(\llbracket \mathbb{X}, u : \partial \mathbb{U} \rrbracket\) in \(\llbracket \mathbb{X}, u : \mathbb{U} \rrbracket\). We add a predicate of the same name \(\mathbb{X}, u : \mathbb{U} \mid \cdot \vdash u \in \partial \mathbb{U} : \text{Prop}\) corresponding in the model to this subobject \(\llbracket \mathbb{X}, u : \partial \mathbb{U} \rrbracket \subseteq \llbracket \mathbb{X}, u : \mathbb{U} \rrbracket\). Note that, since the direct boundary was not defined by pullback, the boundary predicate is not preserved by shape substitution \(\sigma : \llbracket \mathbb{X}_1 \rrbracket \to \llbracket \mathbb{X}_2 \rrbracket\), i.e. \(\langle \Omega[\sigma, u := u] | (u \in \partial \mathbb{U})_{\mathbb{X}_2} \rangle\) is not in general isomorphic to \((u \in \partial \mathbb{U})_{\mathbb{X}_1}\).

If we had modal type formers for left adjoints, then we could define the boundary predicate as  \( (\top,\mathbf{\Omega}_{[u\in\partial\mathbb{U}]}^{\Sigma(u\in\partial\mathbb{U})}) \) . However, MTT does not support such type formers and we do not know how to do this \( ^{19} \)  so we simply axiomatize the predicate by decreeing for every type X, u : U |  \( \Gamma\vdash A \)  type an isomorphism

\[
(u \in \partial \mathbb {U}) \rightarrow A \cong \left\langle \Pi (u \in \partial \mathbb {U}) \mid \left\langle \Omega [ u \in \partial \mathbb {U} ] \mid A [ \mathbf {\alpha} _ {\text { const } (u \in \partial \mathbb {U})} ^ {\text { drop } (u \in \partial \mathbb {U})} ] \right\rangle\right\rangle . \tag {8.1}
\]

\( ^{19} \) It is worth noting that  \( \Sigma^{\sigma\dagger} \)  is a parametric right adjoint so the work by Gratzer et al. [GCK \( ^{+} \) 22] could be relevant.

16:40

A. NUYTS AND D. DEVRIESE

Vol. 20:2

In practice, for concrete systems, we will want axioms based on our findings in Section 6.3, e.g. in a binary cubical system we would decree $\cdot \mid (i \in \partial \mathbb{I}) \leftrightarrow (i \equiv_{\mathbb{I}} 0) \vee (i \equiv_{\mathbb{I}} 1)$ where the latter two predicates could be axiomatized similarly to (8.1).

8.3. **Strictness axiom.** The strictness axiom [OP18] allows to extend a partial type $T$ to a total type if $T$ is isomorphic to a total type $A$, effectively strictifying the isomorphism:

$$\begin{array}{l} \mathbb{X} \mid \Gamma \vdash \varphi : \text{Prop} \quad \mathbb{X} \mid \Gamma \vdash A : \mathsf{U}_{\ell} \quad \mathbb{X} \mid \Gamma,_{-} : \varphi \vdash T : \mathsf{U}_{\ell} \quad \mathbb{X} \mid \Gamma,_{-} : \varphi \vdash i : A \cong T \\ \hline \mathbb{X} \mid \Gamma \vdash \text{Strict}\{A \cong (\varphi ? T ; i)\} : \mathsf{U}_{\ell} \quad \mathbb{X} \mid \Gamma \vdash \text{strict}\{\varphi ? i\} : A \cong \text{Strict}\{A \cong (\varphi ? T ; i)\} \\ \text{where } \Gamma,_{-} : \varphi \vdash \text{Strict}\{A \cong (\varphi ? T ; i)\} = T : \mathsf{U}_{\ell} \quad \Gamma,_{-} : \varphi \vdash \text{strict}\{\varphi ? i\} = i : A \cong T \end{array}$$

## 9. INVESTIGATING THE TRANSPENSION TYPE

In Section 2.2, we have briefly investigated the structure of a fully faithful transpension type in FFTraS. In this section, we investigate the structure of the general transpension type $\langle \langle [u] \mid A \rangle$ in MTraS.

9.1. **Poles.** Our first observation is that on the boundary, the transpension type is trivial. Let $\top : \mathbb{X}_1 \to \mathbb{X}_2$ be the modality, between any two modes, which maps any presheaf to the terminal presheaf. We clearly have $\top \circ \mu = \top$ for any $\mu$, but also $\mu \circ \top \cong \top$ because all internal modalities are right adjoints and therefore preserve the terminal object.

**Theorem 9.1** (Pole). *We have $\Omega[u \in \partial \mathbb{U}] \circ [\langle [u] \cong \top$. We can thus postulate a term $\mathbb{X}, u : \mathbb{U} \mid \Gamma,_{-} : u \in \partial \mathbb{U} \vdash \text{pole} : \langle [\langle [u] \mid T \rangle \text{ for any } \mathbb{X} \mid \Gamma, \widehat{\mathbf{Q}}_{[\langle [u] \mid T \rangle \text{ type}}, \text{ with an } \eta\text{-rule } \mathbb{X}, u : \mathbb{U} \mid \Gamma,_{-} : u \in \partial \mathbb{U} \vdash t = \text{pole} : \langle [\langle [u] \mid T \rangle$.*

*Sketch of proof.* The left adjoints $\forall (u : \mathbb{U}) \circ \Sigma(u \in \partial \mathbb{U})$ and $\perp$ of the concerned modalities are isomorphic because $\forall (u : \mathbb{U}).(u \in \partial \mathbb{U})$ is false. We give a full proof in the technical report [Nuy20b].

Definition 6.6 of the boundary relied on the notion of dimensional splitness. The following result shows that it was a good one: the transpension is *only* trivial on the boundary:

**Theorem 9.2** (Boundary). *In the model, we have* [Nuy20b]

$$\mathbb{X}, u : \mathbb{U} \mid \Gamma \vdash (u \in \partial \mathbb{U}) \cong \langle [\langle [u : \mathbb{U}] \mid \text{Empty} \rangle.$$

9.2. **Meridians.** As all our modalities are proper DRAs [BCM$^{+}$20], the modal introduction rule is invertible in the model. This immediately shows that sections$^{20}$ of the transpension type

$$\mathbb{X} \mid \Gamma \vdash f : \langle \forall (u : \mathbb{U}) \mid \langle [\langle [u : \mathbb{U}] \mid T \rangle \rangle$$

(which we call meridians) are in 1-1 correspondence with terms

$$\mathbb{X} \mid \Gamma, \widehat{\mathbf{Q}}_{[\langle [u] \mid T \rangle \vee u \circ [\langle [u] \mid T \rangle]} \vdash t : T.$$

If it were not for the locking of the context, this characterization in terms of poles and meridians would make the transpension type look quite similar to a dependent version of the suspension type in HoTT [Uni13], whence our choice of name. If $\mathbb{U}$ is $\top$-slice (hence

$^{20}$By a section of a dependent type, we mean a dependent function with the same domain as the type.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:41

TRANSP:ELIM

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \text{ctx}\)

\(\mathbb{X} \mid \Gamma, \widehat{\mathbb{Q}}_u^{\forall u} \vdash A \text{type}\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, r: \langle \langle \langle u \mid A \rangle \vdash C \text{type}\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, -: u \in \partial \mathbb{U} \vdash c_{\text{pole}}: C[\text{pole}/r]\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_u^{\forall u}, x: A, \widehat{\mathbb{Q}}_u^{\exists [u]} \vdash c_{\text{mer}}: C[\text{id}_\Gamma, \widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}, \text{mod}_{\langle [u]} (x_{\text{unmer}_u^{-1}}^ {-1})/r]\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_u^{\forall u}, x: A, \widehat{\mathbb{Q}}_u^{\exists [u]}, -: u \in \partial \mathbb{U} \vdash c_{\text{mer}} = c_{\text{pole}}[\text{id}_\Gamma, \widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}]: C[\text{id}_\Gamma, \widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}, \text{pole}/r]\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash t: \langle \langle [u] | A\rangle\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash c := \text{case } t \text{ of } \{\text{pole} \mapsto c_{\text{pole}} | \text{mer } x \mapsto c_{\text{mer}}\}: C[t/r]\)

where \(c[\text{pole}/t] = c_{\text{pole}}\)

\(\mathbb{X}, u: \mathbb{U} \mid \Delta, \widehat{\mathbb{Q}}_u^{\exists [u]} \vdash c = c_{\text{mer}}[\text{id}_\Delta, \widehat{\mathbb{Q}}_{\text{unmer}_u}^{\text{const}_u}, \text{unmer}_u \sim_{\forall u} t/x, \widehat{\mathbb{Q}}_u^{\exists [u]}]: C\)

Figure 8: Transpension elimination by pattern matching (sound if U is T-slice fully faithful and shard-free). Recall Eq. (3.1).

presheafwise) fully faithful, then the applied locks are actually isomorphic to the identity lock (Theorem 6.31). In any case, regardless of the properties of U, Proposition 3.3 tells us that the let-rule for  \( \langle[u:U] \)  has the same power as

\[
\operatorname{unmer} _ {u}: (\forall (u: \mathbb {U}) \mid \langle \langle [ u: \mathbb {U} ] \mid T \rangle) \rightarrow T [ \widehat {\mathbf {Q}} _ {\text { unmer } _ {u}} ^ {\text { const } _ {u}} ]
\]

which extracts meridians. If U is T-slice fully faithful, then the 2-cell unmer \( _{u} \) is invertible (Theorem 6.31) and we can also straightforwardly create meridians from elements of \( T[\widehat{\mathbf{Q}}_{\text{unmer}_{u}}^{\text{const}_{u}}] \).

9.3. Pattern matching. The eliminator  \( unmer_{u} \)  is only capable of eliminating sections of the transpension type. If the quotient Theorem 6.28 applies to U, we can eliminate locally by pattern matching:

Theorem 9.3. If U is T-slice (hence presheafwise) fully faithful and shard-free, then the rule TRANSP:ELIM in Fig. 8 is sound [Nuy20b].

The elimination rule is best understood by looking at the left names. We get a context \(\Gamma\) depending on \(u: \mathbb{U}\), a type \(A\) depending on sections of \(\Gamma\) (as represented by \(\Gamma, \widehat{\mathbb{Q}}_u^{\forall u}\)), a type \(C\) depending on \(u\) and \(r: \langle \langle [u] | A \rangle\), and an argument \(t\) of type \(\langle [u] | A \rangle\). To obtain a value of type \(C\), we need to give an action \(c_{\text{pole}}\) on the boundary, where \(t\) is necessarily pole (pole Theorem 9.1), and a compatible action on sections of the transpension type, i.e. meridians, which live over sections of \(\Gamma\) but are themselves essentially elements of \(A\) (quantification Theorem 6.31), producing sections of \(C\) (but the quantifier \(\forall u\) has been brought to the left as \(\widehat{\mathbb{Q}}_u^{\exists [u]}\)). Thanks to shard-freedom, we know that everything that is not a section\(^{21}\), is on the boundary, so this suffices.

The computation rule for meridians fires when all of \(\Gamma\) is fresh for \(u\). In this situation, the judgement for \(t\) is \(\mathbb{X}, u: \mathbb{U} \mid \Delta, \widehat{\mathbb{Q}}_u^{\exists [u]} \vdash t: \langle \langle [u] \mid A \rangle\) which by transposition boils down to \(\mathbb{X} \mid \Delta \vdash t': \langle \forall a \mid \langle [u] \mid A \rangle \rangle\), i.e. it fires when \(t\) can actually be seen as a full section of the transpension type, so that we can apply the action on sections given by \(c_{\mathrm{mer}}\).

\( ^{21} \) or a ‘dimensional section’ in case of base categories that are not objectwise pointable

16:42

A. NUYTS AND D. DEVRIESE

Vol. 20:2

![img-0.jpeg](img-0.jpeg)

Figure 9: Recovering known operators: Dependency graph

**Remark 9.4.** This computation rule for TRANSP:ELIM is in a non-general context and needs to be forcibly closed under substitution. We could not find a better way to phrase this computation rule at the time of writing, but while preparing the camera-ready version of this paper, we believe the rule can be mended using the fact that $\bullet_{\forall u}^{u}$ has a further left adjoint $\bullet_{\exists u}^{u}$ so that an arbitrary context $\Theta$ can be universally approximated in the image of $\bullet_{\forall u}^{u}$ as $(\Theta, \bullet_{\exists u}^{u}, \bullet_{\forall u}^{u})$, not unlike how the modal formation and introduction rules of MTT itself were conceived (Fig. 4).

## 10. RECOVERING KNOWN OPERATORS

In this section, we explain how to recover the amazing right adjoint $\surd$ [LOPS18], BCM's $\Phi$ and $\Psi$ combinators [BCM15, Mou16], Glue [CCHM17, NVD17], Weld [NVD17] and mill [ND18b] and (without formal claims) locally fresh names [PMD15] from the transpension type, the strictness axiom [OP18] and certain pushouts. Figure 9 gives an overview of the dependencies.

10.1. **The amazing right adjoint $\surd$**. Licata et al. [LOPS18] use presheaves over a cartesian base category of cubes and introduce $\surd$ as the right adjoint to the non-dependent exponential $\mathbb{I} \to \sqcup$. We generalize to *semicartesian* base categories (indeed to copointed multipliers) and look for a right adjoint to $\mathbb{U} \to \sqcup$, which decomposes as substructural quantification after cartesian weakening $\forall(u : \mathbb{U}) \circ \Omega[u : \mathbb{U}]$. Then the right adjoint is obviously $\surd_{\mathbb{U}} := \Pi(u : \mathbb{U}) \circ \Omega[u : \mathbb{U}]$. The type constructor has type $\langle \surd_{\mathbb{U}} | \sqcup \rangle : (\surd_{\mathbb{U}} \upharpoonright \mathbb{U}_{\ell}) \to \mathbb{U}_{\ell}$ and the transposition rule is as in Proposition 3.4. This is an improvement in two ways: First, we have introduction, elimination and computation rules, so that we do not need to postulate functoriality of $\surd_{\mathbb{U}}$ and invertibility of transposition. Secondly, we have no need for a global sections modality $\flat$. Instead, we use the modality $\surd_{\mathbb{U}}$ to escape Licata et al.'s no-go theorems.

Our overly general mode theory does contain a global sections modality $\flat : \cdot \to \cdot$ acting in the empty shape context, and we can use this to recover Licata et al.'s axioms for the

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:43

amazing right adjoint. Let us write $1 \Leftarrow \Sigma u \circ \lrcorner[u] : \text{spdrop}_u \rrcorner \text{spconst}_u : 1 \Rightarrow \forall u \circ \Omega[u]$ and $\text{spunmer}_u : \Pi u \circ \Diamond[u] \Rightarrow 1$ for the 2-cells built by partial transposition from either $\text{hide}_u \rrcorner \text{spoil}_u$ or $\text{cospoil}_u$ (Theorem 6.31), which are each other's transposite. The following are isomorphisms:

$$\kappa := \text{spconst}_u \star 1_b : b \cong \forall u \circ \Omega[u] \circ b,$$

$$\zeta := 1_b \star \text{spunmer}_u : b \circ \Pi u \circ \Diamond[u] \cong b.$$

For $\kappa$, this is intuitively clear from the fact that we are considering $\mathbb{U}$-cells in a discrete presheaf produced by $b$. For $\zeta$, this is similarly clear after taking the left adjoints:

$$\text{spconst}_u \star 1_{\int} : \int \cong \forall u \circ \Omega[u] \circ \int$$

where $\int$, the left name of $b$, is semantically the connected components functor which also produces discrete presheaves. Write $\int \Leftarrow 1 : \eta \rrcorner \varepsilon : b \Rightarrow 1$ for the co-unit of the comonad $b$. We can define

$$\mathbb{U} \surd \sqcup : (b \mid \mathsf{U}) \to \mathsf{U}$$

$$\mathbb{U} \multimap \sqcup : \mathsf{U} \to \mathsf{U}$$

$$\mathbb{U} \surd A = \left\langle \Pi u \circ \Diamond[u] \mid A[\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$\mathbb{U} \multimap A = \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\text{spconst}_u}^{\text{spdrop}_u}] \right\rangle.$$

Let two global types $\cdot \mid \Gamma, \mathbf{a}_{\zeta} \vdash A, B$ type be given. Applying the non-dependent version of Proposition 3.4 to the adjunction $\forall u \circ \Omega[u] \dashv \surd_{\mathbb{U}} = \Pi u \circ \Diamond[u]$ with unit $(1_{\Pi u} \star \text{reidx}_u \star 1_{\Omega[u]}) \circ \text{const}_u : 1 \Rightarrow \Pi u \circ \Diamond[u] \circ \forall u \circ \Omega[u]$ yields:

$$(A[\mathbf{a}_{\zeta}^{\eta}] \to \mathbb{U} \surd B)$$

$$\cong \left\langle \surd_{\mathbb{U}} \mid \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\zeta}^{\eta}][\mathbf{a}_{\text{const}_u}^{\text{drop}_u}][\mathbf{a}_{\Pi u}^{\Omega[u]}, \mathbf{a}_{\text{reidx}_u}^{\text{app}_u}, \mathbf{a}_{\Omega[u]}^{\Sigma u}] \right\rangle \to B[\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$= \left\langle \surd_{\mathbb{U}} \mid \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\text{spconst}_u}^{\text{spdrop}_u}] \right\rangle [\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \to B[\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$= \left\langle \surd_{\mathbb{U}} \mid \left( \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\text{spconst}_u}^{\text{spdrop}_u}] \right\rangle \to B \right) [\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$= \mathbb{U} \surd ((\mathbb{U} \multimap A) \to B).$$

Equality of the substitutions applied to $A$ is proven by transposing $\forall u \circ \Omega[u]$ to the left as $\Pi u \circ \Diamond[u]$. Then the unit $\text{const}_u \circ (1_{\Pi u} \star \text{reidx}_u \star 1_{\Omega[u]}) : 1 \Rightarrow \Pi u \circ \Diamond[u] \circ \forall u \circ \Omega[u]$ becomes $1_{\Pi u \circ \Diamond[u]}$, leaving just $\varepsilon : b \Rightarrow 1$, whereas $\text{spconst}_u : 1 \Rightarrow \forall u \circ \Omega[u]$ becomes $\text{spunmer}_u : \Pi u \circ \Diamond[u] \Rightarrow 1$ and cancels against $\zeta^{-1}$, again leaving just $\varepsilon$.

Applying the $b$ modality to both sides of the isomorphism and using $\zeta$ to get rid of the amazing right adjoint on the right, yields transposition functions as given by Licata et al. [LOPS18].

We refer back to Section 6.7 for the opposite construction: a transpension type for a cartesian multiplier can be constructed from an amazing right adjoint [Yet87].

10.2. The $\Phi$-combinator. In Fig. 10, we state BCM's $\Phi$-rule [BCM15, Mou16], also known as extent [CH21]; both a slight reformulation adapted to FFTraS and the rule PHI adapted to MTraS.

In the binary version of the BCM system, or in FFTraS with an interval shape as in cubical type theory, the $\Phi$-combinator allows us to define functions of type $\forall i.(y : B i) \to C i y$ from an action $c_\epsilon$ at every endpoint $\epsilon$ and a compatible action $c_\forall$ on sections $\forall i.B i$. When the resulting function $\Phi c_0 c_1 c_\forall$ is applied to an endpoint $\epsilon : \mathbb{I}$ it just reduces to the corresponding action $\lambda y.c_\epsilon$. When it is applied to an interval variable $i : \mathbb{I}$ and expression $b$ that depends

16:44

A. Nuyts and D. Devriese

Vol. 20:2

Binary and destrictified reformulation of the original \(\Phi\)-rule [BCM15, Mou16, CH21]:

\(\Delta, i: \mathbb{I} \vdash B \text{ type}\)

\(\Delta, i: \mathbb{I}, y: B \vdash C \text{ type}\)

\(\Delta, y: B[\epsilon / i] \vdash c_{\epsilon}: C[\epsilon / i]\) (\(\epsilon \in \{0, 1\}\))

\(\Delta, h: \forall (i: \mathbb{I}).B, i: \mathbb{I} \vdash c_{\forall}: C[h i / y]\)

\(\Delta, h: \forall (i: \mathbb{I}).B \vdash c_{\forall}[\epsilon / i] = c_{\epsilon}[h \epsilon / y]: C[h \epsilon / y]\) (\(\epsilon \in \{0, 1\}\))

\(\Delta \vdash \Phi c_0 c_1 c_{\forall}: \forall i.(y: B) \to C\)

where \(\Phi c_0 c_1 c_{\forall} \epsilon b = c_{\epsilon}[b / y]\) (\(\epsilon \in \{0, 1\}\))

\(\Delta, i: \mathbb{I} \vdash \Phi c_0 c_1 c_{\forall} i b = c_{\forall}[\lambda i.b / h]\)

\(\Phi\) -rule in MTraS (recall Eq. (3.1)):

PHI
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash C \text{ type}\)
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, -: u \in \partial \mathbb{U} \vdash c_{\partial}: C\)
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_{[u]}^{\forall u}, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]} \vdash c_{\forall}: C[\widehat{\mathbb{Q}}_{\text{reidx}_u: 1 \Rightarrow [u] \circ \forall u \Rightarrow 1}]\)
\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_{[u]}^{\forall u}, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]}, -: u \in \partial \mathbb{U} \vdash c_{\forall} = c_{\partial}[\widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}] : C[\widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}]\)
\(\overline{\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash \Phi_u c_\partial c_\forall}: C}\)
where \(\mathbb{X}, u: \mathbb{U} \mid \Gamma, -: u \in \partial \mathbb{U} \vdash \Phi_u c_\partial c_\forall = c_{\partial}: C\)
\(\mathbb{X}, u: \mathbb{U} \mid \Delta, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]} \vdash \Phi_u c_\partial c_\forall = c_{\forall}[\widehat{\mathbb{Q}}_{\text{unmer}_u: \forall u \circ [u] \Rightarrow 1}^{\text{const}_u: 1 \Rightarrow \forall u \circ [u]}, \widehat{\mathbb{Q}}_{[u]}^{\exists [u]}] : C\)

Figure 10: The \(\Phi\)-rule (sound if \(\mathbb{U}\) is \(\top\)-slice fully faithful and shard-free).

only on i and variables fresh for i, then the variable i can be captured in b yielding a section  \( \lambda i.b : \forall i.Bi \)  to which we can apply the action on sections  \( c_{\forall} \) .

A few remarks are necessary in order to move to MTraS. First of all, note that the fully applied conclusion of the \(\Phi\)-rule is \(\Delta, i: \mathbb{I}, y: B \vdash \Phi c_0 c_1 c_\forall i y: C\). Of course the endpoints together constitute the boundary of the interval, so if we want to generalize away from cubical type theory, we can expect something like \(\Delta, u: \mathbb{U}, y: B \vdash \Phi c_\partial c_\forall u y: C\). We will assume that the shape \(\mathbb{U}\) is \(\top\)-slice fully faithful and shard-free. In order to translate the context (\(\Delta, u: \mathbb{U}, y: B\)) to MTraS, recall that in FFTraS (as well as in the BCM system) the variables to the left of \(u\) are fresh for \(u\), whereas those to the right need not be. In MTraS we put the shape variables in the shape context, so the context translates to (\(\Delta, \widehat{\mathbb{Q}}_{[u]}^{\exists[u]}, y: B\)). In MTraS we will treat this entire thing as a single abstract context \(\Gamma\), so we do not grant the domain of the \(\Phi\)-function any special status; in a way all of \(\Gamma\) takes the role of \(B\).

Then, completely analogously to BCM, we need a type C in context  \( \Gamma \) , an object  \( c_{\partial}:C \)  whenever u is on the boundary, and a compatible action  \( c_{\forall} \)  that acts on sections of  \( \Gamma \)  and produces sections of C, but the quantifier  \( \forall u \)  has been brought to the left as  \( \widehat{\mathbb{Q}}_{[u]}^{\exists[u]} \) . Again the resulting term  \( \Phi_{u}c_{\partial}c_{\forall} \)  reduces to  \( c_{\partial} \)  when on the boundary, and to  \( c_{\forall} \)  when all variables in use are fresh for u. Again, the computation rule for sections is in a non-general context and needs to be forcibly closed under substitution, but see Remark 9.4.

Note that the FFTraS/BCM substitutions \(hi / b\) and \(h\epsilon /b\) (i.e. \(hi / b\) where \(i\) is on the boundary) involving applications, all turn into usages of \(\widehat{\mathbb{Q}}_{\mathrm{reidx}_u}^{\mathrm{app}_u}\) whereas the variable capturing substitution \(\lambda i.b / h\) has turned into \((\widehat{\mathbb{Q}}_{\mathrm{unmer}_u}^{\mathrm{const}_u},\widehat{\mathbb{Q}}_{[u]}^{\exists [u]}):(\Delta ,\widehat{\mathbb{Q}}_{[u]}^{\exists [u]})\to (\Delta ,\widehat{\mathbb{Q}}_{[u]}^{\exists [u]},\widehat{\mathbb{Q}}_{[u]}^{\forall u},\widehat{\mathbb{Q}}_{[u]}^{\exists [u]})\) which

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:45

for \(\top\)-slice fully faithful multipliers is inverse to \((\widehat{\mathbf{a}}_{\forall u}^{j[u]}, \widehat{\mathbf{a}}_{\mathrm{reid}x_u}^{\mathrm{app}_u})\) and therefore denotes an inverse of application: variable capture. Furthermore, regarding the context of \(c_{\forall}\), we remark that for \(\top\)-slice fully faithful multipliers there is an isomorphism of contexts

\[
\begin{array}{l} (\Delta , \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}, y: B, \widehat {\mathbf {a}} _ {\forall [ u ]} ^ {\forall u}) \cong_ {3. 4} \left(\Delta , \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}, \widehat {\mathbf {a}} _ {\forall [ u ]} ^ {\forall u}, \forall u \mid y: B \left[ \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}, \widehat {\mathbf {a}} _ {\text {reid} x _ {u}} ^ {\text {app} _ {u}} \right]\right) \\ \cong_ {6. 3 1} \left(\Delta , \forall u \mid y: B, \widehat {\mathbf {a}} _ {\forall u} ^ {j [ u ]}\right) \tag {10.1} \\ \end{array}
\]

so, recalling from Section 7.1.3 that \(i:\mathbb{I}\) translates to \(\widehat{\mathbf{a}}_{\forall i}^{j[i]}\) in the internal context, there really is a close correspondence to what happens in the BCM system.

We remark that if \(\mathbb{U}\) is \(\top\)-slice fully faithful but not necessarily shard-free, then the \(\Phi\)-rule remains valid for creating terms of a transpension type \(C = \langle \langle [u] \mid D \rangle\). Indeed, using pole Theorem 9.1 we can then define:

\[
\Phi_ {u} \text {   pole   } c _ {\forall} := \text { mod } _ {\langle [ u ]} (\text { unmer } _ {u} \cdot_ {\forall u} c _ {\forall}): \langle \langle [ u ] \mid D \rangle .
\]

The non-trivial computation rule follows from the \(\eta\)-rule for projections (Proposition 3.3) and quantification Theorem 6.31.

Theorem 10.1. If \(\mathbb{U}\) is \(\top\)-slice fully faithful and shard-free, then the \(\Phi\)-rule (Fig. 10) is sound and indeed derivable from TRANSP:ELIM for all \(C\).

Proof. Use the case-eliminator for  \( \langle\langle[u]\mid Unit\rangle \)  (Theorem 9.3):

\[
\Phi_ {u} c _ {\partial} c _ {\forall} := \text { case } (\text { mod } _ {\langle [ u ]} \text { unit }) \text { of } \left\{\text { pole } \mapsto c _ {\partial} \mid \text { mer } _ {-} \mapsto c _ {\forall} \right\}.
\]

□

10.3. The \(\Psi\)-type. BCM's \(\Psi\)-combinator (Fig. 11, also known as Gel [CH21]) constructs a line \(\forall (i:\mathbb{I}).\mathsf{U}\) in the universe with endpoints \(A_{\epsilon}\) from a relation \(R:A_0\to A_1\to \mathsf{U}\). A section of the \(\Psi\)-type with endpoints \(a_{\epsilon}\) is a proof of \(Ra_0a_1\). The constructor in \(\Psi\) creates a section \(\forall (i:\mathbb{I}).\Psi_iA_0A_1(x_0.x_1.R)\) from the expected inputs. The disappearance of \(\Theta\) in the premises of \(\Psi\) and in \(\Psi\) is entirely analogous to the shape application rule FF:FORALL:ELIM in Fig. 1. The eliminator out \(\Psi\) extracts from a section of the \(\Psi\)-type the proof that its endpoints satisfy the relation \(R\).

In fact, using the typing rules of FFTraS and a strictness axiom as in Section 8.3 we can already implement a stronger  \( \Psi \) -type, also given in Fig. 11, where  \( \Theta \)  does not disappear but gets universally quantified. This is done by strictifying the right hand sides below: \( ^{22} \)

\[
\alpha : \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R) := (\hat {x} _ {0}: (\operatorname{refl}: i \equiv_ {\mathbb {I}} 0) \rightarrow A _ {0}) \times (\hat {x} _ {1}: (\operatorname{refl}: i \equiv_ {\mathbb {I}} 1) \rightarrow A _ {1}) \times
\]

\[
\langle [ i ] (R [ (\lambda i. \hat {x} _ {0}) 0 \operatorname{refl} / x _ {0}, (\lambda i. \hat {x} _ {1}) 1 \operatorname{refl} / x _ {1} ])
\]

\[
\operatorname{in} \Psi_ {i} a _ {0} a _ {1} r := \alpha^ {- 1} (\lambda \operatorname{refl}. a _ {0}, \lambda \operatorname{refl}. a _ {1}, \operatorname{mer} [ i ] r)
\]

\[
\operatorname{out} \Psi (i. q) := \operatorname{unmer} (i. \pi_ {3} (\alpha (q)))
\]

The fact that this construction is isomorphic to \( A_{\epsilon} \) at endpoint \( \epsilon \) follows from our findings about poles in Section 2.2.

When we move to MTraS, once again we translate the context \((\Delta, u : \mathbb{U}, \Theta)\) to \((\Delta, \widehat{\mathbf{a}}_{\forall u}^{j[u]}, \Theta)\), which we treat as a single abstract context \(\Gamma\). By a reasoning identical to that in Eq. (10.1), applying \(\widehat{\mathbf{a}}_{\forall u}^{j[u]}\) only affects the non-fresh part \(\Theta\) if the shape \(\mathbb{U}\) is \(\top\)-slice fully faithful. This leads to the MTraS rules listed in Fig. 11. Note again how substitutions

\( ^{22} \) For the identity type, we use pattern-matching abstractions to abbreviate the usage of the J-rule. We are in an extensional type system anyway.

16:46

A. NUYTS AND D. DEVRIESE

Vol. 20:2

Binary and destrictified reformulation of the original \(\Psi\)-type [BCM15, Mou16, CH21]:

\[
\Delta \vdash A _ {\epsilon} \text { type } \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , x _ {0}: A _ {0}, x _ {1}: A _ {1} \vdash R \text { type }
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R) \text { type }
\]

\[
\text { where } \Psi_ {\epsilon} A _ {0} A _ {1} R = A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta \vdash a _ {\epsilon}: A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta \vdash r: R [ a _ {0} / x _ {0}, a _ {1} / x _ {1} ]
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \operatorname{in} \Psi_ {i} a _ {0} a _ {1} r: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\text { where } \operatorname{in} \Psi_ {\epsilon} a _ {0} a _ {1} r = a _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , i: \mathbb {I} \vdash q = \operatorname{in} \Psi_ {i} q [ 0 / i ] q [ 1 / i ] (\operatorname{out} \Psi (j. q [ j / i ]))
\]

\[
\Delta , i: \mathbb {I} \vdash q: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\Delta \vdash \operatorname{out} \Psi (i. q): R [ q [ 0 / i ] / x _ {0}, q [ 1 / i ] / x _ {1} ]
\]

\[
\text { where } \operatorname{out} \Psi (i. \text { in } \Psi_ {i} a _ {0} a _ {1} r) = r
\]

#### Ψ-type in FFTraS:

\[
\Delta , \theta : \Theta [ \epsilon / i ] \vdash A _ {\epsilon} \text { type } \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , \forall i. (\theta : \Theta), x _ {0}: A _ {0} [ (\lambda i. \theta) 0 / \theta ], x _ {1}: A _ {1} [ (\lambda i. \theta) 1 / \theta ] \vdash R \text { type }
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R) \text { type }
\]

\[
\text { where } \Psi_ {\epsilon} A _ {0} A _ {1} R = A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , \theta : \Theta [ \epsilon / i ] \vdash a _ {\epsilon}: A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , \forall i. (\theta : \Theta) \vdash
\]

\[
r: R [ a _ {0} [ (\lambda i. \theta) 0 / \theta ] / x _ {0}, a _ {1} [ (\lambda i. \theta) 1 / \theta ] / x _ {1} ]
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \operatorname{in} \Psi_ {i} a _ {0} a _ {1} r: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\text { where } \operatorname{in} \Psi_ {\epsilon} a _ {0} a _ {1} r = a _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
q = \operatorname{in} \Psi_ {i} q [ 0 / i ] q [ 1 / i ] (\operatorname{out} \Psi (j. q [ j / i, (\lambda i. \theta) j / \theta ]))
\]

\[
\Delta , i: \mathbb {I} \vdash q: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\Delta \vdash \operatorname{out} \Psi (i. q): R [ q [ 0 / i ] / x _ {0}, q [ 1 / i ] / x _ {1} ]
\]

\[
\text { where } \operatorname{out} \Psi (i. \text { in } \Psi_ {i} a _ {0} a _ {1} r) = r
\]

#### Ψ-type in MTraS:

PSI

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma , _ {-}: u \in \partial \mathbb {U} \vdash A \text { type }
\]

\[
\mathbb {X} \mid \Gamma , \hat {x}: (-: u \in \partial \mathbb {U}) \rightarrow A, \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} \vdash R \text { type }
\]

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma \vdash \Psi_ {u} A (\hat {x}. R) \text { type }
\]

\[
\text { where } \_: u \in \partial \mathbb {U} \vdash \Psi_ {u} A (\hat {x}. R) = A
\]

PSI:INTRO

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma , _ {-}: u \in \partial \mathbb {U} \vdash a: A
\]

\[
\mathbb {X} \mid \Gamma , \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} \vdash r: R [ \lambda .. a / \hat {x}, \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} ]
\]

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma \vdash \operatorname{in} \Psi_ {u} (- a) r: \Psi_ {u} A (\hat {x}. R)
\]

\[
\text { where } \_: u \in \partial \mathbb {U} \vdash \operatorname{in} \Psi_ {u} (- a) r = a
\]

\[
q = \operatorname{in} \Psi_ {u} (- q) \left(\operatorname{out} \Psi_ {\neg \forall u} q [ \widehat {\mathbf {a}} _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}} ]\right)
\]

PSI:ELIM

\[
\mathbb {X}, u: \mathbb {U} \mid \Delta , \widehat {\mathbf {u}} _ {\forall u} ^ {\exists [ u ]} \vdash q: \Psi_ {u} A (\hat {x}. R)
\]

\[
\mathbb {X} \mid \Delta \vdash \operatorname{out} \Psi_ {\neg \forall u} q: R [ \lambda .. q / \hat {x}, \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} ] [ \widehat {\mathbf {a}} _ {\text {unmer} _ {u}} ^ {\text {const} _ {u}} ]
\]

\[
\text { where } \operatorname{out} \Psi_ {\neg \forall u} \operatorname{in} \Psi_ {u} (- a) r = r [ \widehat {\mathbf {a}} _ {\text { unmer } _ {u}} ^ {\text { const } _ {u}} ]
\]

Figure 11: Typing rules for the  \( \Psi \) -type.

\((\lambda i.\theta)j / \theta\) in FFTraS give rise to usages of \(\widehat{\mathbf{a}}_{\mathrm{reidx}_u}^{\mathrm{app}_u}\) in MTraS. The usages of \(\widehat{\mathbf{a}}_{\mathrm{unmer}_u}^{\mathrm{const}_u}\) are entirely absent in FFTraS, but for \(\top\)-slice fully faithful multipliers, this is an isomorphism anyway.

The eliminator out \( \Psi \) only eliminates sections. For T-slice fully faithful and shard-free multipliers, the \( \Phi \)-rule provides a pattern-matching eliminator which lets us treat the boundary and section cases separately.

Theorem 10.2. For any multiplier, the \(\Psi\)-type in Fig. 11 is implementable from the transpension type and the strictness axiom.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:47

Proof. We strictly the right hand sides below:

$$\begin{array}{l} \alpha : \Psi_{u} A (\hat{x}.R) : \cong (\hat{x} : (. : u \in \partial U) \to A) \times \langle \langle [u] \mid R \rangle, \\ \text{in} \Psi_{u} (.a) r := \alpha^{-1}(\lambda..a, \text{mod}_{[u]} r), \\ \text{out} \Psi \cdot_{\forall u} q := \text{unmer}_{u} \cdot_{\forall u} \pi_{2}(\alpha(q)). \end{array}$$

The fact that this is isomorphic to $A$ on the boundary follows from pole Theorem 9.1

Obviously then the transpension type $\langle [u] \mid T \rangle$ is also implementable from the $\Psi$-type as $\Psi_{u} \text{Unit} (.T)$.

10.4. Transpensivity. The $\Phi$-rule is extremely powerful but not available in all systems. However, when the codomain $C$ is a $\Psi$-type, then the in$\Psi$-rule is actually quite similar to the $\Phi$-rule if we note that sections of the $\Psi$-type are essentially elements of $R$. As such, we take an interest in types that are very $\Psi$-like. We have a monad (idempotent if $\mathbb{U}$ is $\top$-slice fully faithful)

$$\bar{\Psi}_{u} A := \Psi_{u} (.A) \left( \hat{x}. \langle \forall u \mid A \text{ext} \{ u \in \partial \mathbb{U} \ ? \ \hat{x} \ . \} [\mathbb{A}_{\text{reidx}_{u}}^{\text{app}_{u}}] \rangle \right),$$

where $A \text{ext} \{ \varphi \ ? \ a \}$ is the type of elements of $A$ that are equal to $a$ when $\varphi$ holds:

$$A \text{ext} \{ \varphi \ ? \ a \} := (x : A) \times ((. : \varphi) \to (x \equiv_{A} a)).$$

Definition 10.3. A type is transpensive over $u$ if it is a monad-algebra for $\bar{\Psi}_{u}$.

For $\top$-slice fully faithful and shard-free multipliers, $\Phi$ entails that all types are transpensive. For other systems, the universe of $u$-transpensive types will still be closed at least semantically under many interesting type formers, allowing to eliminate to these types in a $\Phi$-like way.

10.5. Glue, Weld, mill. Glue$\{A \leftarrow (\varphi \ ? \ T \ ; \ f)\}$ and Weld$\{A \to (\varphi \ ? \ T \ ; \ g)\}$ are similar to Strict but extend unidirectional functions. Orton and Pitts [OP18] already show that Glue [CCHM17, NVD17] can be implemented by strictifying a pullback along $A \to (\varphi \to A)$ [ND18b] which is definable internally using a $\Sigma$-type. Dually, Weld [NVD17] can be implemented if there is a type former for pushouts along $\varphi \times A \to A$ where $\varphi : \text{Prop}$ [Nuy20a, §6.3.3], which is sound in all presheaf categories.

Finally, mill [ND18b] states that $\forall (u : \mathbb{U})$ preserves Weld and is provable by higher-dimensional pattern matching (where $\circledast$ is the applicative operation of the modal type):

$$\begin{array}{l} \text{mill} : \langle \forall u \mid \text{Weld} \{ A \to (\varphi \ ? \ T \ ; \ g) \} \rangle \\ \quad \to \text{Weld} \{ \langle \forall u \mid A \rangle \to (\langle \forall u \mid \varphi \rangle \ ? \ \langle \forall u \mid T \rangle \ ; \ (\text{mod}_{\forall u} g) \circledast \sqcup) \} \end{array}$$

$$\text{mill } \hat{w} = \text{unmer}_{u} \cdot_{\forall u}$$

$$\text{case } (\text{app}_{u} \cdot_{[u]} (\hat{w}_{\text{const}_{u}}^{\text{drop}_{u}})) \text{ of } \left\{ \begin{array}{l} \text{weld } a \mapsto \text{mod}_{[u]} (\text{weld } (\text{mod}_{\forall u} (a_{\text{reidx}_{u}}^{\text{app}_{u}}))) \\ \varphi \ ? \ t \mapsto \text{mod}_{[u]} (\text{mod}_{\forall u} (t_{\text{reidx}_{u}}^{\text{app}_{u}})) \end{array} \right\}.$$

In the first clause, we get an element $a : A$ and can proceed as in Section 7.3. In the second clause, we are asserted that $\varphi$ holds (call the witness $p$) so that the left hand Weld-type equals $T$, and we are given $t : T$. Then inside the meridian constructor $\text{mod}_{[u]}$ we know that $\langle \forall u \mid \varphi \rangle$ holds as this is proven by $\text{mod}_{\forall u} (p_{\text{reidx}_{u}}^{\text{app}_{u}})$; hence the Weld-type in the codomain

16:48

A. NUYTS AND D. DEVRIESE

Vol. 20:2

|  name | FreshMLTT | MTraS  |
| --- | --- | --- |
|  name quantification | \( \mathsf{N}[i:N].T \) | \( \langle \mathsf{N}(i:\mathbb{I})\mid [T]\rangle \)  |
|  name abstraction | \( \alpha[i:N].t \) | \( \mathsf{mod}_{\mathsf{N}(i:\mathbb{I})}[[t]] \)  |
|  name application | \( t@i \) | \( \mathsf{app}_{i}\cdot_{\mathbb{I}[i]}[[t]] \)  |
|  non-binding quant. | \( \langle \langle i:N\rangle\rangle.T \) | \( \langle \mathbb{I}[i]\mid \langle \mathsf{N}i\mid [T][\mathsf{R}_{\mathsf{copy}_i}^{\mathsf{app}_i}]\rangle \rangle \)  |
|  non-binding abs. | \( \langle i:N\rangle.t \) | \( \mathsf{copy}_i[[t]]:= \mathsf{mod}_{\mathbb{I}[i]}(\mathsf{mod}_{\mathsf{N}i}([t][\mathsf{R}_{\mathsf{copy}_i}^{\mathsf{app}_i}])) \)  |
|  locally fresh name | \( \nu[i:N].t \) | \( \mathsf{drop}_{i}\cdot_{\mathsf{N}i}(\mathsf{mod}_{\mathbb{I}[i]}[[t]]) \)  |

Figure 12: A heuristic for translating FreshMLTT [PMD15] to the current system.

simplifies to  \( \langle\forall u\mid T\rangle \) . When  \( \varphi \)  holds and t = weld a = ga, then the weld-constructor of the right hand Weld-type reduces to  \( (\text{mod}_{\forall u}g)\circledast\sqcup \)  which effectively applies g under the  \( mod_{\forall u} \) -constructor, so that both clauses match as required.

10.6. Locally fresh names. Nominal type theory is modelled in the Schanuel topos [Pit14] which is a subcategory of nullary affine cubical sets  \( \mathrm{Psh}(^{0}\mathrm{Cube}_{\square}) \)  (Example 6.14). As fibrancy is not considered in this paper, we will work directly in  \( \mathrm{Psh}(^{0}\mathrm{Cube}_{\square}) \) . Names can be modelled using the multiplier  \( \sqcup*(i:\mathbb{I}) \) . Interestingly, the fresh weakening functor  \( \mathbb{I}_{(i:\mathbb{I})} \)  is then inverse to its left adjoint  \( \exists_{(i:\mathbb{I})} \) . By consequence, we get  \( \exists i\cong\forall i=:N i \)  (the fresh name quantifier) with inverse  \( \mathbb{I}[i]\cong\mathbb{I}[i] \) . For consistency, we will only use N i and  \( \mathbb{I}[i] \) , and these will be each other's left names. The relevant 2-cells are  \( app_{i}:\mathbb{I}[i]\circ N i\Rightarrow1 \)  and its inverse  \( copy_{i}:1\Rightarrow\mathbb{I}[i]\circ N i \)  (these are each other's left names), as well as  \( const_{i}:1\Rightarrow N i\circ\mathbb{I}[i] \)  and its inverse  \( drop_{i}:N i\circ\mathbb{I}[i]\Rightarrow1 \)  (these are each other's left names).

The nominal dependent type system FreshMLTT [PMD15] used in Pitts's examples of interest [Pit14] is substantially different from ours:

- It features a name swapping operation that is semantically not merely a substitution.
- Freshness for a name \( i \) is not a modality or a type, but a judgement that can be derived for an expression \( t \) if and only if \( t \) is invariant under swapping \( i \) with a newly introduced name \( j \). As a consequence, freshness propagates through type and term constructors.
- Many equalities are strict where we can only guarantee an isomorphism.

For these reasons, we do not try to formally state that we can support locally fresh names in the sense of FreshMLTT. Nevertheless, in Fig. 12 we give at least a heuristic \(\llbracket \sqcup \rrbracket\) for translating programs in a subsystem of FreshMLTT to programs in the current system. This subsystem does not feature name swapping, but it does feature the non-binding abstractions originally defined in terms of it, as well as locally fresh names.

Ordinary name quantification is simply translated to the modality \(\mathcal{N}i\), and as usual application corresponds to the modal projection function (Proposition 3.3). The non-binding abstraction in FreshMLTT abstracts over a name that is already in scope, without shadowing, i.e. it is a variable capturing operation. This is translated essentially to the 2-cell \(\mathrm{copy}_i:1\Rightarrow \mathbb{I}[i]\circ \mathcal{N}i\), which is inverse to \(\mathrm{app}_i\) as we have seen earlier for a variable capturing operation (Section 10.2). Finally, a locally fresh name abstraction \(\nu [i:N].t\) brings a name \(i\) into scope in its body \(t\), but requires that \(t\) be fresh for \(i\); in our system we would say that \(t\) is a subterm of modality \(\mathcal{N}i\circ \mathbb{I}[i]\). The type of \(\nu [i:N].t\) is the same as the type of \(t\), which we can justify with the isomorphism \(\mathrm{drop}_i:\mathcal{N}i\circ \mathbb{I}[i]\cong 1\). This isomorphism is essentially the content of the modal projection function of \(\mathbb{I}[i]\), which we use to translate locally fresh name abstractions.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:49

Note that for general multipliers, $\mathbb{J}[i]$ does not have an internal left adjoint and hence not a modal projection function either. For the nullary affine interval, however, $\mathbb{J}[i] \cong \mathbb{Q}[i]$, so the projection function is essentially unmer$_{i}$!

Example 10.4. Consider Pitts's implementation of higher dimensional pattern matching [Pit14]:

$$j : (\mathsf{M}[i : N].A \uplus B) \to (\mathsf{M}[i : N].A) \uplus (\mathsf{M}[i : N].B)$$

$$j \, \hat{c} = \nu[i : N].\text{case } \hat{c}@i \text{ of } \left\{ \begin{array}{l l l} \text{inl } a & \mapsto & \text{inl } (\langle i : N \rangle . a) \\ \text{inr } b & \mapsto & \text{inr } (\langle i : N \rangle . b) \end{array} \right\}$$

A brainless translation using Fig. 12 yields a type mismatch, because the non-binding abstractions will put the freshness constructor inside the coproduct constructors, whereas the translation of the locally fresh name abstraction mentions it again on the outside. This is related to our earlier remark that in FreshMLTT, freshness silently propagates through type and term constructors, so here we have to manually intervene. This is also necessary to insert invertible 2-cell substitutions in some places, and to check whether we need a modal argument (i.e. the modality is handled at the judgemental level) or we need to explicitly use the modal constructor as is always done in Fig. 12. Doing so, we find

$$j : \langle \mathsf{M} \, i \mid A \uplus B \rangle \to \langle \mathsf{M} \, i \mid A \rangle \uplus \langle \mathsf{M} \, i \mid B \rangle$$

$$j \, \hat{c} = \text{drop}_i \cdot_{\mathsf{M} \, i} \text{case } (\text{app}_i \cdot_{\mathbb{J}[i]} (\hat{c}_{\text{const}_i}^{\text{drop}_i})) \text{ of } \left\{ \begin{array}{l} \text{inl } a \mapsto \text{mod}_{\mathbb{J}[i]} (\text{inl } (\text{mod}_{\mathsf{M} \, i} (a_{\text{copy}_i}^{\text{app}_i}))) \\ \text{inr } b \mapsto \text{mod}_{\mathbb{J}[i]} (\text{inr } (\text{mod}_{\mathsf{M} \, i} (b_{\text{copy}_i}^{\text{app}_i}))) \end{array} \right\},$$

which is exactly what we found in Section 7.3 adapted to our convention that we only want to mention $\mathbb{J}[i]$ and $\forall \, i$, $\text{app}_i$, $\text{copy}_i$, $\text{const}_i$ and $\text{drop}_i$.

Example 10.5. Consider Pitts et al.'s implementation [PMD15, ex. 2.2] of what is essentially BCM's $\Phi$-rule [Mou16, BCM15] since the boundary is empty:

$$g : ((\mathsf{M}[i : N].A) \to \mathsf{M}[i : N].B) \to \mathsf{M}[i : N].(A \to B)$$

$$g \, f = \alpha[i : N].(\lambda x. f \, (\langle i : N \rangle . x) \, @ \, i.$$

We can translate this to the current system using Fig. 12:

$$g : (\langle \mathsf{M} \, i \mid A \rangle \to \langle \mathsf{M} \, i \mid B \rangle) \to \langle \mathsf{M} \, i \mid A \to B \rangle$$

$$g \, f = \text{mod}_{\mathsf{M} \, i} \left( \lambda x. \text{app}_i \cdot_{\mathbb{J}[i]} (f[\mathbf{a}_{\text{const}_i}^{\text{drop}_i}] (\text{mod}_{\mathsf{M} \, i} (x_{\text{copy}_i}^{\text{app}_i}))) \right).$$

The effect of conflating $\mathbf{a}_{\mathbb{J}[i]}^{\exists \, i}$ with $\mathbf{a}_{\mathbb{J}[i]}^{\forall \, i}$ is that affine function application no longer renders the non-fresh part of the context inaccessible using $\mathbf{a}_{\mathbb{J}[i]}^{\exists \, i}$ but instead universally quantifies it using $\mathbf{a}_{\mathbb{J}[i]}^{\forall \, i}$, so that we can capture variables as in FreshMLTT. Remarkably, we do not need the $\Phi$-rule (Fig. 10) for this nor pattern-matching for the transpension type (Fig. 8), although these rules hold as the affine cubical interval is $\top$-slice fully faithful and shard-free (Example 6.14).

## 11. CONCLUSION

To summarize, the transpension type can be defined in a broad class of presheaf models and generalizes previous internalization operators. For now, we only present an extensional type system without an algorithmic typing judgement. The major hurdles towards producing an intensional version with decidable type-checking, are the following:

16:50

A. NUYTS AND D. DEVRIESE

Vol. 20:2

- We need to decide equality of 2-cells. Solutions may exist in the literature on higher-dimensional rewriting. Alternatively, we need to extend MTT with a language to reason about 2-cell equality [Nuy23b].
- The substitution modality should ideally reduce like ordinary substitution. Remark 5.5 explores what is needed for this to work.
- We need a syntax-directed way to close the section computation rules of $\Phi$ (Fig. 10) and transpension elimination (Section 9) under substitution, but see Remark 9.4.
- We need to be able to decide whether the boundary predicate, or any similar predicate about shape variables such as $i \equiv_1 0$ in cubical type theory, is true. This problem has been dealt with in special cases, e.g. in implementations of cubical type theory [VMA19].

Applications include all applications (discussed in Section 1) of the presheaf internalization operators recovered from the transpension type in Section 10. Moreover, our modal approach to shape variables via multipliers allows the inclusion of Pinyo and Kraus's twisted prism functor [PK20] as a semantics of an interval variable, which we believe is an important advancement towards higher-dimensional directed type theory.

# ACKNOWLEDGEMENTS

We thank Jean-Philippe Bernardy, Lars Birkedal, Daniel Gratzer, Alex Kavvos, Magnus Baunsgaard Kristensen, Daniel Licata, Rasmus Ejlers Møgelberg and Andrea Vezzosi for relevant discussions, and the anonymous reviewers for their feedback which has been a great guidance in improving the clarity of this paper.

# APPENDIX A. CHANGELOG

The first preprint of this paper appeared in 2020 and is subsumed in [Nuy20a, ch. 7]. Since then, there have been significant changes, primarily terminological ones. To help out readers coming back to this paper after having consulted earlier versions (or associated presentations), we list the most important changes here.

# A.1. Terminology.

# A.1.1. Definition 6.2.

- **Copointed** multipliers were formerly called **semicartesian**,
- Multipliers that are **comonads** were formerly called **3/4-cartesian**,
- **T-slice faithful** multipliers were formerly called **cancellative**,
- **T-slice full** multipliers were formerly called **affine**,
- **T-slice shard-free** multipliers were formerly called **connection-free**, and **shards** were formerly called **connections**,
- **T-slice right adjoint** multipliers were formerly called **quantifiable**.

# A.1.2. Definition 6.4.

- **Unpointable** objects were formerly called **spooky**,
- **Not objectwise pointable** categories were formerly called **spooky**.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:51

A.1.3. *Definition 6.22.* **Presheafwise** faithful/full/shard-free/right adjoint multipliers were formerly called **providently** cancellative/affine/connection-free/quantifiable.

A previous version of the paper featured a different definition of shards/connections and presheafwise shard-freedom / provident connection-freedom, that was based on the *indirect* boundary and *indirectly* dimensionally split morphisms (Appendix A.1.4). These notions are obsolete and are retained in the technical report [Nuy20b] under the names **indirect shard** and **indirect shard-freedom** (alongside the direct notions from Definition 6.22) solely for consistency with [Nuy20a, ch. 7].

A.1.4. *Definition 6.23.* A previous version of this paper had a different definition of boundary and of dimensionally split cells which was defined using the pullback of $\Xi \times \mathbf{y}U \rightarrow \mathbf{y}U \supseteq \partial U$. These notions are obsolete and are retained in the technical report [Nuy20b] under the name **indirect boundary** and **indirectly dimensionally split** cells (alongside the direct notions) solely for consistency with [Nuy20a, ch. 7].

As the notions coincide for $\Xi = \top$, Theorem 9.2 holds w.r.t. the indirect boundary if $\Xi = \top$. By construction, the indirect boundary is respected by substitution, while the transpension type is generally not if the multiplier is not $\top$-slice fully faithful (Section 2.1.7). Hence, the indirect notions generally diverge from the direct ones and the indirect version of Theorem 9.2 breaks down if $\Xi \neq \top$ and the multiplier is not $\top$-slice fully faithful.

A.1.5. *Theorem 6.28.* The **quotient theorem** was formerly called **kernel theorem**.

A.2. **Ticks.** A previous version of this paper assigned names to locks, called *ticks*, after the tick of the (c)lock in [BGM17]. The usage of this notation is orthogonal to the introduction of MTraS; a version of the original MTT paper [GKNB20b] in tick notation is included in [Nuy20a, §5.3]. An improved notation is proposed in [Nuy23b].

A.3. **Lockless notation.** A previous version of this paper supplemented the MTT notation with a so-called *lockless* notation in which $(\Gamma, \widehat{\bullet}_0)$ was denoted as $\kappa(\Gamma)$. This notation was abolished in favour of *left adjoint reminders* (Section 3.4).

## REFERENCES

- [ACKS23] Danil Annenkov, Paolo Capriotti, Nicolai Kraus, and Christian Sattler. Two-level type theory and applications. *Math. Struct. Comput. Sci.*, 33(8):688–743, 2023. doi:10.1017/S0960129523000130.
- [AGJ14] Robert Atkey, Neil Ghani, and Patricia Johann. A relationally parametric model of dependent type theory. In *Principles of Programming Languages*, 2014. doi:10.1145/2535838.2535852.
- [AHH18] Carlo Angiuli, Kuen-Bang Hou (Favonia), and Robert Harper. Cartesian Cubical Computational Type Theory: Constructive Reasoning with Paths and Equalities. In Dan Ghica and Achim Jung, editors, *Computer Science Logic (CSL 2018)*, volume 119 of *LIPIcs*, pages 6:1–6:17, Dagstuhl, Germany, 2018. Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik. doi:10.4230/LIPIcs.CSL.2018.6.
- [AK16] Thorsten Altenkirch and Ambrus Kaposi. Type theory in type theory using quotient inductive types. In Rastislav Bodík and Rupak Majumdar, editors, *Proceedings of the 43rd Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages, POPL 2016, St. Petersburg, FL, USA, January 20 - 22, 2016*, pages 18–29. ACM, 2016. doi:10.1145/2837614.2837638.

16:52

A. NUYTS AND D. DEVRIESE

Vol. 20:2

[BBC+19] Lars Birkedal, Aleš Bizjak, Ranald Clouston, Hans Bugge Grathwohl, Bas Spitters, and Andrea Vezzosi. Guarded cubical type theory. Journal of Automated Reasoning, 63(2):211–253, 8 2019. doi:10.1007/s10817-018-9471-7.
[BCH14] Marc Bezem, Thierry Coquand, and Simon Huber. A Model of Type Theory in Cubical Sets. In 19th International Conference on Types for Proofs and Programs (TYPES 2013), volume 26, pages 107–128, Dagstuhl, Germany, 2014. doi:10.4230/LIPICS.TYPES.2013.107.
[BCM15] Jean-Philippe Bernardy, Thierry Coquand, and Guilhem Moulin. A presheaf model of parametric type theory. Electron. Notes in Theor. Comput. Sci., 319:67 – 82, 2015. doi:10.1016/j.entcs.2015.12.006.
[BCM+20] Lars Birkedal, Ranald Clouston, Bassel Manna, Rasmus Ejlers Møgelberg, Andrew M. Pitts, and Bas Spitters. Modal dependent type theory and dependent right adjoints. Mathematical Structures in Computer Science, 30(2):118–138, 2020. doi:10.1017/S0960129519000197.
[BGC+16] Aleš Bizjak, Hans Bugge Grathwohl, Ranald Clouston, Rasmus Ejlers Møgelberg, and Lars Birkedal. Guarded dependent type theory with coinductive types. In FOSSACS '16, 2016. doi:10.1007/978-3-662-49630-5\_2.
[BGM17] Patrick Bahr, Hans Bugge Grathwohl, and Rasmus Ejlers Møgelberg. The clocks are ticking: No more delays! In 32nd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS 2017, Reykjavik, Iceland, June 20-23, 2017, pages 1–12, 2017. doi:10.1109/LICS.2017.8005097.
[BM20] Aleš Bizjak and Rasmus Ejlers Møgelberg. Denotational semantics for guarded dependent type theory. Math. Struct. Comput. Sci., 30(4):342–378, 2020. doi:10.1017/S0960129520000080.
[BMSS12] Lars Birkedal, Rasmus Møgelberg, Jan Schwinghammer, and Kristian Støvring. First steps in synthetic guarded domain theory: step-indexing in the topos of trees. Logical Methods in Computer Science, 8(4), 2012. doi:10.2168/LMCS-8(4:1)2012.
[BV17] Jean-Philippe Bernardy and Andrea Vezzosi. Parametric application. Private communication, 2017.
[Car78] John Cartmell. Generalised Algebraic Theories and Contextual Categories. PhD thesis, Oxford University, 1978. URL: https://ncatlab.org/nlab/files/Cartmell-Thesis.pdf.
[Car86] John Cartmell. Generalised algebraic theories and contextual categories. Ann. Pure Appl. Logic, 32:209–243, 1986. doi:10.1016/0168-0072(86)90053-9.
[CCHM17] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. Cubical type theory: A constructive interpretation of the univalence axiom. FLAP, 4(10):3127–3170, 2017. URL: http://www.cse.chalmers.se/~simonhu/papers/cubicaltt.pdf.
[CH21] Evan Cavallo and Robert Harper. Internal parametricity for cubical type theory. Log. Methods Comput. Sci., 17(4), 2021. doi:10.46298/lmcs-17(4:5)2021.
[Che12] James Cheney. A dependent nominal type theory. Log. Methods Comput. Sci., 8(1), 2012. doi:10.2168/LMCS-8(1:8)2012.
[CMS20] Evan Cavallo, Anders Mörtberg, and Andrew W Swan. Unifying Cubical Models of Univalent Type Theory. In Maribel Fernández and Anca Muscholl, editors, Computer Science Logic (CSL 2020), volume 152 of LIPics, pages 14:1–14:17, Dagstuhl, Germany, 2020. Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik. doi:10.4230/LIPICS.CSL.2020.14.
[GCK+22] Daniel Gratzer, Evan Cavallo, G. A. Kavvos, Adrien Guatto, and Lars Birkedal. Modalities and parametric adjoints. ACM Trans. Comput. Logic, 23(3), apr 2022. doi:10.1145/3514241.
[Gir64] Jean Giraud. Méthode de la descente. Bull. Soc. Math. Fr., Suppl., Mém., 2:115, 1964. doi:10.24033/msmf.2.
[GKNB20a] Daniel Gratzer, Alex Kavvos, Andreas Nuyts, and Lars Birkedal. Type theory à la mode. Pre-print, 2020. URL: https://anyuts.github.io/files/mtt-techreport.pdf.
[GKNB20b] Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. Multimodal dependent type theory. In Holger Hermanns, Lijun Zhang, Naoki Kobayashi, and Dale Miller, editors, LICS '20: 35th Annual ACM/IEEE Symposium on Logic in Computer Science, Saarbrücken, Germany, July 8-11, 2020, pages 492–506. ACM, 2020. doi:10.1145/3373718.3394736.
[GKNB21] Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. Multimodal Dependent Type Theory. Logical Methods in Computer Science, Volume 17, Issue 3, July 2021. doi:10.46298/lmcs-17(3:11)2021.

Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:53

[Gra22] Daniel Gratzer. Normalization for multimodal type theory. In Christel Baier and Dana Fisman, editors, LICS '22: 37th Annual ACM/IEEE Symposium on Logic in Computer Science, Haifa, Israel, August 2 - 5, 2022, pages 2:1-2:13. ACM, 2022. doi:10.1145/3531130.3532398.
[Hof97] Martin Hofmann. Syntax and Semantics of Dependent Types, chapter 4, pages 79-130. Cambridge University Press, 1997.
[HS97] Martin Hofmann and Thomas Streicher. Lifting grothendieck universes. Unpublished note, 1997. URL: https://www2.mathematik.tu-darmstadt.de/-streicher/NOTES/lift.pdf.
[Hub16] Simon Huber. Cubical Interpretations of Type Theory. PhD thesis, University of Gothenburg, Sweden, 2016. URL: http://www.cse.chalmers.se/~simonhu/misc/thesis.pdf.
[KL18] Chris Kapulkin and Peter LeFanu Lumsdaine. The simplicial model of univalent foundations (after Voevodsky), 2018. arXiv:1211.2851.
[LH11] Daniel R. Licata and Robert Harper. 2-dimensional directed type theory. Electr. Notes Theor. Comput. Sci., 276:263-289, 2011. doi:10.1016/j.entcs.2011.09.026.
[LOPS18] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. Internal universes in models of homotopy type theory. In 3rd International Conference on Formal Structures for Computation and Deduction, FSCD 2018, July 9-12, 2018, Oxford, UK, pages 22:1-22:17, 2018. doi:10.4230/LIPICS.FSCD.2018.22.
[Mou16] Guilhem Moulin. Internalizing Parametricity. PhD thesis, Chalmers University of Technology, Sweden, 2016. URL: publications.lib.chalmers.se/records/fulltext/235758/235758.pdf.
[ND18a] Andreas Nuyts and Dominique Devriese. Degrees of relatedness: A unified framework for parametricity, irrelevance, ad hoc polymorphism, intersections, unions and algebra in dependent type theory. In Logic in Computer Science (LICS) 2018, Oxford, UK, July 09-12, 2018, pages 779-788, 2018. doi:10.1145/3209108.3209119.
[ND18b] Andreas Nuyts and Dominique Devriese. Internalizing Presheaf Semantics: Charting the Design Space. In Workshop on Homotopy Type Theory / Univalent Foundations, 2018. URL: https://hott-uf.github.io/2018/abstracts/HoTTUF18_paper_1.pdf.
[ND19] Andreas Nuyts and Dominique Devriese. Dependable atomicity in type theory. In TYPES, 2019. URL: https://lirias.kuleuven.be/retrieve/540872.
[nLa23a] nLab authors. coreflective subcategory. https://ncatlab.org/nlab/show/coreflective+subcategory, January 2023. Revision 18.
[nLa23b] nLab authors. locally. https://ncatlab.org/nlab/show/locally, February 2023. Revision 3.
[nLa23c] nLab authors. reflective subcategory. https://ncatlab.org/nlab/show/reflective+subcategory, January 2023. Revision 106.
[nLa23d] nLab authors. sieve. https://ncatlab.org/nlab/show/sieve, February 2023. Revision 49.
[Nor19] Paige Randall North. Towards a directed homotopy type theory. Proceedings of the Thirty-Fifth Conference on the Mathematical Foundations of Programming Semantics, MFPS 2019, London, UK, June 4-7, 2019, pages 223-239, 2019. doi:10.1016/j.entcs.2019.09.012.
[Nuy18a] Andreas Nuyts. Presheaf models of relational modalities in dependent type theory. CoRR, abs/1805.08684, 2018. arXiv:1805.08684.
[Nuy18b] Andreas Nuyts. Robust notions of contextual fibrancy. In Workshop on Homotopy Type Theory / Univalent Foundations, 2018. URL: https://hott-uf.github.io/2018/abstracts/HoTTUF18_paper_2.pdf.
[Nuy20a] Andreas Nuyts. Contributions to Multimode and Presheaf Type Theory. PhD thesis, KU Leuven, Belgium, 8 2020. URL: https://anuyts.github.io/files/phd.pdf.
[Nuy20b] Andreas Nuyts. The transpension type: Technical report, 2020. Version 4 (2024). URL: https://arxiv.org/abs/2008.08530, arXiv:2008.08530.
[Nuy23a] Andreas Nuyts. Functor whose essential image is a cosieve? MathOverflow, 2023. (version: 2023-02-08). URL: https://mathoverflow.net/q/440372.
[Nuy23b] Andreas Nuyts. A lock calculus for multimode type theory. In TYPES, 2023. URL: https://anuyts.github.io/files/2023/mtt-lc-types.pdf.
[NVD17] Andreas Nuyts, Andrea Vezzosi, and Dominique Devriese. Parametric quantifiers for dependent type theory. PACMPL, 1(ICFP):32:1-32:29, 2017. doi:10.1145/3110276.
[OP18] Ian Orton and Andrew M. Pitts. Axioms for modelling cubical type theory in a topos. Logical Methods in Computer Science, 14(4), 2018. doi:10.23638/LMCS-14(4:23)2018.

16:54

A. NUYTS AND D. DEVRIESE

Vol. 20:2

[Ort18] Ian Orton. Cubical Models of Homotopy Type Theory - An Internal Approach. PhD thesis, University of Cambridge, 2018. doi:10.17863/CAM.36690.

[Pit13] A. M. Pitts. Nominal Sets: Names and Symmetry in Computer Science, volume 57 of Cambridge Tracts in Theoretical Computer Science. Cambridge University Press, 2013.

[Pit14] Andrew Pitts. Nominal sets and dependent type theory. In TYPES, 2014. URL: https://www.irif.fr/~letouzey/types2014/slides-inv3.pdf.

[PK20] Gun Pinyo and Nicolai Kraus. From Cubes to Twisted Cubes via Graph Morphisms in Type Theory. In Marc Bezem and Assia Mahboubi, editors, 25th International Conference on Types for Proofs and Programs (TYPES 2019), volume 175 of Leibniz International Proceedings in Informatics (LIPIcs), pages 5:1–5:18, Dagstuhl, Germany, 2020. Schloss Dagstuhl–Leibniz-Zentrum für Informatik. doi:10.4230/LIPIcs.TYPES.2019.5.

[PMD15] Andrew M. Pitts, Justus Matthiesen, and Jasper Derikx. A dependent type theory with abstractable names. Electronic Notes in Theoretical Computer Science, 312:19 – 50, 2015. Ninth Workshop on Logical and Semantic Frameworks, with Applications (LSFA 2014). doi: 10.1016/j.entcs.2015.04.003.

[Rey83] John C. Reynolds. Types, abstraction and parametric polymorphism. In IFIP Congress, pages 513–523, 1983.

[RS17] E. Riehl and M. Shulman. A type theory for synthetic ∞-categories. ArXiv e-prints, May 2017. arXiv:1705.07442.

[Sta19] The Stacks Project Authors. Stacks project. http://stacks.math.columbia.edu, 2019. Tags 00VC and 00XF.

[Uni13] The Univalent Foundations Program. Homotopy Type Theory: Univalent Foundations of Mathematics. http://homotopytypetheory.org/book, IAS, 2013.

[VMA19] Andrea Vezzosi, Anders Mörtberg, and Andreas Abel. Cubical Agda: a dependently typed programming language with univalence and higher inductive types. PACMPL, 3(ICFP):87:1–87:29, 2019. doi:10.1145/3341691.

[Voe13] Vladimir Voevodsky. A simple type system with two identity types. unpublished note, 2013. URL: https://ncatlab.org/homotopytypetheory/files/HTS.pdf.

[WL20] Matthew Z. Weaver and Daniel R. Licata. A constructive model of directed univalence in bicubical sets. In Holger Hermanns, Lijun Zhang, Naoki Kobayashi, and Dale Miller, editors, LICS '20: 35th Annual ACM/IEEE Symposium on Logic in Computer Science, Saarbrücken, Germany, July 8-11, 2020, pages 915–928. ACM, 2020. doi:10.1145/3373718.3394794.

[Yet87] David Yetter. On right adjoints to exponential functors. Journal of Pure and Applied Algebra, 45(3):287–304, 1987. doi:10.1016/0022-4049(87)90077-6.

This work is licensed under the Creative Commons Attribution License. To view a copy of this license, visit https://creativecommons.org/licenses/by/4.0/ or send a letter to Creative Commons, 171 Second St, Suite 300, San Francisco, CA 94105, USA, or Eisenacher Strasse 2, 10777 Berlin, Germany