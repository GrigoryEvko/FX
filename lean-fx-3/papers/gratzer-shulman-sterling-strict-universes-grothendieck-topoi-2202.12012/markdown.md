arXiv:2202.12012v3 [math.CT] 16 May 2024

# STRICT UNIVERSES FOR GROTHENDIECK TOPOI

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

ABSTRACT. Hofmann and Streicher famously showed how to lift Grothendieck universes into presheaf topoi, and Streicher has extended their result to the case of sheaf topoi by sheafification. In parallel, van den Berg and Moerdijk have shown in the context of algebraic set theory that similar constructions continue to apply even in weaker metatheories. Unfortunately, sheafification seems not to preserve an important *realignment* property enjoyed by presheaf universes that plays a critical role in models of univalent type theory as well as synthetic Tait computability. When multiple universes are present, realignment also implies a *coherent* interpretation of connectives across all universes that justifies the cumulativity laws present in popular formulations of Martin-Löf type theory.

We observe that a slight adjustment to an argument of Shulman lifts a well-behaved cumulative universe hierarchy in the category of sets to a cumulative universe hierarchy satisfying the realignment property at every level in any Grothendieck topos. Hence one has direct interpretations of Martin-Löf type theory with cumulative universes into all Grothendieck topoi. A further implication is to extend the reach of recent synthetic methods in the semantics of cubical type theory and the syntactic metatheory of type theory and programming languages to all Grothendieck topoi.

# Contents

|  1 | Introduction | 2  |
| --- | --- | --- |
|  1.1 | Elementary axioms for universes in a topos | 3  |
|  1.2 | From realignment to cumulative hierarchies | 6  |
|  1.3 | Structure of the paper | 6  |
|  2 | Reviewing Hofmann and Streicher's universes | 7  |
|  2.1 | Universes of sets | 7  |
|  2.2 | Hofmann and Streicher's universe of presheaves | 8  |
|  2.3 | Streicher's universe of sheaves | 11  |
|  3 | Generalities on descent and $\kappa$-compactness | 13  |
|  3.1 | Descent in a Grothendieck topos | 13  |
|  3.2 | Compact objects and relatively compact maps | 18  |
|  3.3 | Relating small and relatively compact maps | 21  |
|  4 | Main result: a universe satisfying realignment | 25  |
|  4.1 | Saturation of solvable realignment problems | 25  |
|  4.2 | A small object argument | 29  |
|  4.3 | Realignment for the universe | 30  |
|  4.4 | A cumulative universe hierarchy | 32  |

© Daniel Gratzer and Michael Shulman and Jonathan Sterling, 2022–2024. Permission to copy for private use granted.

1

2

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

|  5 | Relating internal formulations of realignment | 33  |
| --- | --- | --- |
|  5.1 | Internal realignment à la Orton and Pitts . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 33  |
|  5.2 | Realignment and recollement . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 35  |
|  6 | Applications of realignment | 38  |
|  6.1 | Independence results for Martin-Löf type theory . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 38  |
|  6.2 | Semantics of the univalent universes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 39  |
|  6.3 | Artin gluing and synthetic Tait computability . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 44  |
|  7 | Conclusions and future work | 47  |
|  7.1 | Prospects for a constructive version . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 48  |

## 1. Introduction

Grothendieck introduced the language of *universes* to control the size issues that plague a naïve categorical development of algebraic geometry [AGV72]. In a somewhat different line of research, Martin-Löf introduced universes into dependent type theory as a *reflection principle* [Mar71; Mar75; Mar79; Mar84]. In either case a universe parameterizes a class of maps that are closed under enough operations to do mathematics, including dependent product/sum, quotients, *etc.*

Grothendieck's use of universes was located in the ambient set theory; each universe $\mathcal{U}$ determines a category of $\mathcal{U}$-small sets and functions that serves as a base for both enrichment and internalization, generalizing the notions of locally small and small category respectively. The past three decades have however seen an increased interest in the adaptation of universes to categories other than **Set**:

1. Universes play a central role in the *algebraic set theory* of Joyal and Moerdijk [JM95], which explores the relationship between sets and classes from a categorical viewpoint.
2. Voevodsky's elucidation of the univalence principle [Voe06], foreshadowed by Hofmann and Streicher [HS98], has reinvigorated the study of universes in topoi. Closely related to Voevodsky's univalent universes are the *object classifiers* of $\infty$-topos theory in the Joyal–Lurie–Rezk tradition [Lur09; Rez10].
3. It is of practical interest to employ Martin-Löf type theory (MLTT) as an internal language for a variety of categories. In addition to the standard applications of internal methods to mathematics, the existence of topos models of MLTT is a critical ingredient for a number of recent results in type theory and programming languages, including the generalized abstraction theorem of Sterling and Harper [SH21] and the proofs of normalization for cubical type theory and multi-modal dependent type theory [Gra22; SA21].

Unfortunately some doubt has proliferated in the type theoretic literature (*e.g.* Coquand, Manna, and Ruch [CMR17], Xu [Xu15], and Xu and Escardó [XE16]) as to when sufficiently well-adapted universes exist in a topos. It is a well-known result of Hofmann

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

3

and Streicher [HS97] that Grothendieck universes can be lifted pointwise into presheaf topoi, and it is slightly less well-known that sheafification preserves all the properties of this universe that do not involve strict equality of codes [Ber11; Str05]. Such a sheafified universe is already sufficient for nearly all mathematical purposes, but falls short in applications to the semantics and metatheory of dependent type theory, where certain strict laws not preserved by sheafification remain important.

In this paper we expose an alternative universe construction that applies in an arbitrary Grothendieck topos, using nothing but the cocompleteness and exactness properties of Grothendieck topoi. Ours is a variant of a construction of a universe of presheaves due to Shulman [Shu15]; we demonstrate that the resulting universe satisfies an important *realignment* property, which suffices in particular to obtain models of Martin-Löf type theory with a cumulative hierarchy of universes in any Grothendieck topos. The realignment condition is also an important ingredient in the construction of *univalent* universes for models of homotopy type theory [Uni13].

1.1. ELEMENTARY AXIOMS FOR UNIVERSES IN A TOPOS. Inspired by the definitions of classes of open and small maps from algebraic set theory, Streicher [Str05] has given a definition of a universe in an elementary topos $\mathcal{E}$ which we review in Definition 1.1.2 below.

1.1.1. NOTATION. Given morphisms $f: A \rightarrow B$ and $g: C \rightarrow D$, a morphism $\alpha: f \rightarrow g$ refers to a commuting square from $f$ to $g$:

$$\begin{array}{c} A \xrightarrow{\partial_0 \alpha} C \\ f \Biggl\downarrow \quad \alpha \quad \Biggl\downarrow g \\ B \xrightarrow{\partial_1 \alpha} D \end{array}$$

We shall also freely write $f \rightarrow g$ for an *anonymous* square from $f$ to $g$.

1.1.2. DEFINITION. A class of arrows $\mathcal{S} \subseteq \operatorname{Hom}_{\mathcal{E}}$ is called a universe by Streicher [Str05] when it satisfies the following axioms:

- (U1) $\mathcal{S}$ is *pullback-stable*, i.e. if $f \in \mathcal{S}$ and $g \rightarrow f$ is a cartesian square, then $g \in \mathcal{S}$.
- (U2) $\mathcal{S}$ contains all monomorphisms in $\mathcal{E}$.
- (U3) $\mathcal{S}$ is closed under composition.
- (U4) If $f: A \rightarrow I$ and $g: B \rightarrow A$ are in $\mathcal{S}$, then the pushforward $f_*g: B \rightarrow I$ lies in $\mathcal{S}$.
- (U5) There exists a generic morphism, i.e. a morphism $\pi: E \rightarrow U \in \mathcal{S}$ such that for any $f \in \mathcal{S}$ there exists a cartesian map $f \rightarrow \pi$.

4

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The axioms of Definition 1.1.2 ensure the closure of $\mathcal{S}$ under several type theoretic operations, if we view an element $f: A \rightarrow B \in \mathcal{S}$ as a dependent type $x: B \vdash A[x]$. Then (U1) corresponds to the substitution action for dependent types and terms; (U2) states that all propositions are small; (U3-4) provide for dependent sums and dependent products, and (U5) provides a generic dependent type $x: U \vdash E[x]$ of which every other dependent type in $\mathcal{S}$ is a substitution instance.

In the type-theoretic literature, it is the base of this family $U$ which is called the universe and the generic family is the dependent type $\mathsf{EI}$ rendering an element of this universe as a genuine type. We occasionally adopt this terminology and blur the distinction between a universe and its generic map by referring to $E \rightarrow U$ simply as a universe. Some caution is required: while a generic map uniquely determines a universe, the converse is not necessarily true and a universe can have multiple distinct generic maps.

In the context of Martin-Löf type theory, it is common to study classes of maps that may not satisfy all the axioms above; for instance, type theory is often used in settings that do not have a single well-behaved notion of proposition, so (U2) loses some significance. We therefore define a notion of *pre-universe* below.

### 1.1.3. DEFINITION. A pre-universe is a class of arrows satisfying axioms (U1, U3-5).

Streicher [Str05] discusses some additional useful but optional axioms for universes.

(U6) (Propositional subuniverse) $\mathcal{S}$ contains the terminal map $\Omega \rightarrow \mathbf{1}_{\bar{k}}$.^1

(U7) (Descent) If $g \in \mathcal{S}$ and $g \rightarrow f$ is a cartesian epimorphism, then $f \in \mathcal{S}$.

A Grothendieck universe $\mathsf{V}$ in $\mathbf{Set}$ is readily seen to induce a universe $\mathcal{S}_{\mathsf{V}}$ in the sense of Definition 1.1.2 where $\mathcal{S}_{\mathsf{V}}$ consists of the collection of maps with $\mathsf{V}$-small fibers. Hofmann and Streicher [HS97] and Streicher [Str05] have shown that $\mathcal{S}_{\mathsf{V}}$ can be lifted systematically to presheaves and sheaves. The first result in particular has been widely used in the semantics of type theory, because the generic morphism satisfies a number of strict equations specific to its construction. These additional equations are crucial for modeling *e.g.* strict cumulative universes. Other more novel applications of this strictness have emerged in models of Voevodsky's univalence axiom and homotopy type theory. Only more recently has an axiomatic basis for these stricter Hofmann–Streicher universes been isolated:

### 1.1.4. DEFINITION. A universe $\mathcal{S}$ is said to have realignment with respect to a class $\mathcal{M}$ of monomorphisms when axiom (U8) below is satisfied:^2

(U8) A chosen cartesian morphism $h \rightarrow \pi$ into the generic morphism can be extended along any cartesian monomorphism $h \mapsto f$ lying horizontally over an element of $\mathcal{M}$

^1 Streicher [Str05] refers to this property as impredicativity, but we wish to avoid confusion with a different notion of impredicativity that involves the existence of dependent products along maps *not* in $\mathcal{S}$, which has its prototype in the full internal subcategory of the category of assemblies spanned by modest sets [Hyl88; HRR90; Str17].

^2 Our axiom (U8) is denoted (2') by Shulman [Shu15].

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

5

where $f \in \mathcal{S}$:

![img-0.jpeg](img-0.jpeg)

Unless otherwise specified, $\mathcal{M}$ is the class of all monomorphisms.

1.1.5. REMARK. While Shulman [Shu15] extracted (U8) from the construction of the universal Kan fibration given by Kapulkin, Lumsdaine, and Voevodsky [KL21], similar properties have since appeared in the construction of the universal left fibration [Cis19, Corollary 5.2.6] and the universal cocartesian fibration [Lur22, Tag 0293].
1.1.6. REMARK. Unfolding the fibrational language, Definition 1.1.4 can be stated more explicitly. We require that given $m: A \mapsto B \in \mathcal{M}$ and $f: Q \mapsto B \in \mathcal{S}$, any cartesian square $m^*f \mapsto \pi$ extends along $m$ to a cartesian square $f \mapsto \pi$:

![img-1.jpeg](img-1.jpeg)

Intuitively, (U8) extends (U5) to provide a more refined generic map where a representation $f \mapsto \pi$ of an arrow $f \in \mathcal{S}$ can be chosen to strictly extend a representation of $g$ where $g \mapsto f \in \mathcal{M}$. In practice, one often exhibits a representation $f \mapsto \varpi$ to show $f \in \mathcal{S}$ only to discard this square to obtain a realigned representation of $f$ which coheres with a previously chosen representation of $g \mapsto f$ using (U8).

We note that (U8) subsumes (U5) under appropriate conditions on $\mathcal{M}$.

1.1.7. LEMMA. Suppose $\mathcal{S}$ is a pullback-stable class of maps and $\pi \in \mathcal{S}$ is a morphism satisfying (U8) with $\mathcal{M}$ containing all maps of the form $\mathbf{0}_{\mathcal{E} \to} \longrightarrow f$, where $\mathbf{0}_{\mathcal{E} \to}$ is the identity map on $\mathbf{0}_{\mathcal{E}}$; then the pair $(\mathcal{S}, \pi)$ satisfies (U5).

PROOF. Fixing an element $f \in \mathcal{S}$, we must construct a cartesian morphism $f \longrightarrow \pi$; this is achieved by realigning $\mathbf{0}_{\mathcal{E} \to} \longrightarrow \pi$ along $\mathbf{0}_{\mathcal{E} \to} \longmapsto f$:

![img-2.jpeg](img-2.jpeg)

6

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

1.2. FROM REALIGNMENT TO CUMULATIVE HIERARCHIES. The true utility of (U8) is the ability to choose a representation for a morphism $f \in \mathcal{S}$ subject to a strict equation. For instance, (U8) is sufficient to 'strictify' a hierarchy of universes so that the choices of codes for connectives commute with the coercion maps from one universe to another [Shu15]. In particular, let $\mathcal{S} \subseteq \mathcal{T}$ be two universes equipped with a choice of cartesian monomorphism $i: \pi_{\mathcal{S}} \mapsto \pi_{\mathcal{T}}$. Further assume that $\mathcal{T}$ satisfies realignment for the class of all monomorphisms.

1.2.1. NOTATION. Given a morphism $f: X \longrightarrow Y$, we write $P_f: \mathcal{E} \longrightarrow \mathcal{E}$ for the polynomial endofunctor given by the composite $Y \circ f_* \circ X^*$.

Both $\mathcal{S}, \mathcal{T}$ are closed under dependent products, hence there exist cartesian morphisms $\Pi_{\mathcal{S}}: P_{\pi_{\mathcal{S}}}(\pi_{\mathcal{S}}) \longrightarrow \pi_{\mathcal{S}}$ and $\Pi_{\mathcal{T}}: P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}}) \longrightarrow \pi_{\mathcal{T}}$, but Diagram 1 below need not commute:

$$\begin{array}{ccc} P_{\pi_{\mathcal{S}}}(\pi_{\mathcal{S}}) & \xrightarrow{\Pi_{\mathcal{S}}} & \pi_{\mathcal{S}} \\ P_i(i) & \downarrow & \downarrow \\ P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}}) & \xrightarrow{\Pi_{\mathcal{T}}} & \pi_{\mathcal{T}} \end{array} \quad (1)$$

We can replace $\Pi_{\mathcal{S}}, \Pi_{\mathcal{T}}$ with new codes $\Pi_{\mathcal{S}}', \Pi_{\mathcal{T}}'$ for which the analogue to Diagram 1 commutes. We set $\Pi_{\mathcal{S}}' := \Pi_{\mathcal{S}}$ and define $\Pi_{\mathcal{T}}'$ by realigning $i \circ \Pi_{\mathcal{S}}'$ along $P_i(i)$:

$$\begin{array}{ccc} P_{\pi_{\mathcal{S}}}(\pi_{\mathcal{S}}) & \xrightarrow{\Pi_{\mathcal{S}}'} & \pi_{\mathcal{S}} \\ P_i(i) & \downarrow & \downarrow \\ P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}}) & \xrightarrow{\Pi_{\mathcal{T}}'} & \pi_{\mathcal{T}} \end{array} \quad (2)$$

If we further assume that $\mathcal{E}$ is sufficiently cocomplete, *e.g.*, if it is a Grothendieck topos, the technique above easily extends to infinite and even transfinite hierarchies of universes. In the latter case, one realigns along the *join* of all the subobjects $P_{\pi_{\mathcal{S}}'}(\pi_{\mathcal{S}}') \mapsto P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}})$ pertaining to the formation data for dependent product type codes at lower universes. Then a coherent hierarchy of such codes is built 'from the ground up' by induction.

1.3. STRUCTURE OF THE PAPER. We survey the landscape of universe constructions available in Grothendieck toposes and show that they inherit a plentiful supply of well-behaved universes from **Set**.

**Section 2.** We revisit the presheaf-theoretic universe construction of Hofmann and Streicher [HS97], lifting a Grothendieck universe in **Set** to a universe of pointwise small families of presheaves satisfying (U1–8). Presenting a sheaf topos as a subcategory of a presheaf topos, we recall from Streicher [Str05] that the Hofmann–Streicher construction

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

7

also produces universes of sheaves satisfying (U1–6), as the sheafification of the generic small family of presheaves is generic for small families of sheaves.

**Section 3.** We review a number of categorical preliminaries to our main result involving descent and $\kappa$-compactness.

**Section 4.** Adapting a construction of Shulman [Shu15], we prove our main result (Corollary 4.3.3): the universe of relatively $\kappa$-compact sheaves for a strongly inaccessible cardinal $\kappa$ satisfies all the universe axioms including (U8). We deduce that cumulative hierarchies of strict universes lift from **Set** to any Grothendieck topos.

**Section 5.** We discuss and compare two equivalent formulations of the realignment property employing the internal language of a topos.

**Section 6.** The results of Section 4 have important consequences for the syntax and semantics of type theory; we review a few of these applications in Section 6. For instance, we have already shown that (U8) is sufficient to construct strictly cumulative hierarchies of universes, and with the existence of these hierarchies in arbitrary Grothendieck topoi the independence of several logical principles of Martin-Löf type theory immediately follows; contrary to some claims, sheaf semantics is sufficient and there is no need to move from sheaves to stacks. We outline applications to independence results in Section 6.1.

We also illustrate the general utility of (U8) through two specific examples: the semantics of univalence in homotopy type theory (Section 6.2) and the construction of glued models of type theory (Section 6.3) for proving syntactic metatheorems such as canonicity, normalization, and decidability. In both cases, (U8) allows us to leverage existing categorical machinery while still maintaining the required strict equations.

**FOUNDATIONAL ASSUMPTIONS.** Throughout, we work in a sufficiently strong metatheory to ensure that **Set** comes equipped with a collection of universes *e.g.*, ZFC with the Grothendieck universe axiom; we make use of the axiom of choice. We return to this topic briefly in Section 7.1.

**Acknowledgments** We are grateful to Steve Awodey, Thomas Streicher, and the anonymous referees for helpful feedback and corrections to an earlier draft of this paper. This research was supported by the United States Air Force Office of Scientific Research under award numbers FA9550-21-1-0009 and FA9550-23-1-0728 (Tristan Nguyen, program officer).

## 2. Reviewing Hofmann and Streicher’s universes

We begin by recalling constructions from Hofmann and Streicher [HS97] and Streicher [Str05] lifting universes from **Set** to Grothendieck topoi. To begin with, fix a *Grothendieck universe* $\mathsf{V}$, a transitive non-empty set closed under Kuratowski pairing, power-sets, and $I$-indexed unions for each $I \in \mathsf{V}$.

2.1. UNIVERSES OF SETS. Each Grothendieck universe defines a universe as in Definition 1.1.2.

8

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

2.1.1. CONSTRUCTION. Define the universe $\mathcal{S}_{\mathsf{V}} \subseteq \operatorname{Hom}_{\mathbf{Set}}$ to be the collection of all morphisms $f \colon X \longrightarrow Y$ with $\mathsf{V}$-small fibers: explicitly for each $y \in Y$, there exists a $u \in \mathsf{V}$ such that $u \cong f^{-1}(y)$.

Showing that $\mathcal{S}_{\mathsf{V}}$ satisfies axioms (U1–4,6,7) is a standard exercise. Setting $\widetilde{\mathsf{V}} = \sum_{u:\mathsf{V}} u$, the generic map is given by the projection $\mathbf{v} \colon \widetilde{\mathsf{V}} \longrightarrow \mathsf{V}$. The proof that $\mathbf{v}$ is generic mostly unsurprising but we note that the axiom of choice is required—essentially to produce an assignment of $\mathsf{V}$ representatives for the fibers of a morphism in $\mathcal{S}_{\mathsf{V}}$ which are known only to be isomorphic to elements of $\mathsf{V}$.

2.1.2. LEMMA. *The universe $\mathcal{S}_{\mathsf{V}}$ satisfies the realignment axiom (U8).*

PROOF. Recalling the characterization of (U8) given by Remark 1.1.6, we fix a realignment problem of the following form:

![img-3.jpeg](img-3.jpeg)

Suppose further that $f \in \mathcal{S}_{\mathsf{V}}$ and, through (U5), pick some morphism $q_0 \colon B \longrightarrow \mathsf{V}$ classifying $f$. While $q_0$ does not necessarily fit into the above diagram, we use it to define a map $q \colon B \longrightarrow \mathsf{V}$ that does:

$$q(b) = \begin{cases} p(a) & \text{when } b = m(a) \\ q_0(b) & \text{otherwise} \end{cases}$$

This definition is well-defined as $m$ is a monomorphism; there is at most one $a$ such that $m(a) = b$. By definition $q$ fits into the triangle above, and an identical procedure extends it to the required cartesian square $f \longrightarrow \mathbf{v}$.

2.1.3. REMARK. The above proof can be generalized to show that any universe in a boolean topos satisfying (U5) satisfies (U8).

2.1.4. REMARK. In the category of sets, any universe in the sense of the present axioms determines a universe in the sense of Grothendieck. Streicher's axioms for universes can therefore be thought of as a more *direct* alternative to Grothendieck's axioms, emphasizing ordinary mathematical constructions (*e.g.* dependent product, sum, quotient) rather than set theoretical considerations (transitive membership, power sets, *etc.*).

2.2. HOFMANN AND STREICHER'S UNIVERSE OF PRESHEAVES. Given a $\mathsf{V}$-small category $\mathcal{C}$, the universe $\mathcal{S}_{\mathsf{V}}$ induces a suitable universe $\hat{\mathcal{S}}_{\mathsf{V}}$ on $\operatorname{Pr}(\mathcal{C})$ that we explore below.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

9

2.2.1. DEFINITION. We define $\hat{S}_{\vee}$ to consist of morphisms $f: X \longrightarrow Y$ such that for each cartesian square of the following shape, the presheaf $y^*X$ is (essentially) $\vee$-valued:

$$\begin{array}{c} y^*X \longrightarrow X \\ \downarrow \quad \downarrow f \\ y(C) \longrightarrow Y \end{array}$$

Explicitly, for each $D: \mathcal{C}$ the set $(y^*X)_D$ must be $\vee$-small.

2.2.2. REMARK. We may equivalently describe $\hat{S}_{\vee}$ as the class of maps $f: X \longrightarrow Y$ such that the fibers of $f$ over representables are $\vee$-small.

Again, it remains to show that this class satisfies the expected axioms. (U1–4,6,7) follow through calculation (taking advantage of the standard construction of $f_*g$ for (U4) and $\Omega$ for (U6)). Hofmann and Streicher [HS97] show that $\hat{S}_{\vee}$ satisfies (U5) with a generic map $\varpi: \tilde{U} \longrightarrow U$. The construction of $\varpi$ is highly dependent on $\Pr(\mathcal{C})$ being a presheaf category, taking advantage of the correspondence $\Pr(\mathcal{C})_{/y(C)} \simeq \Pr(\mathcal{C}_{/C})$ which represents the codomain fibration as a strict 2-functor rather than the usual pseudofunctor. This correspondence restricts to presheaves valued in the full subcategory of Set spanned by elements of $\vee$ to induce an equivalence $\Pr_{\vee}(\mathcal{C})_{/y(C)} \simeq \Pr_{\vee}(\mathcal{C}_{/C})$. We use this to define $U_C$ as follows:

$$U_C = \Pr_{\vee}(\mathcal{C}_{/C})$$

The generic family $\varpi$ is most directly defined as a presheaf over $\mathsf{Elt}(U)$, again taking advantage of the equivalence $\Pr(\mathcal{C})_{/U} \simeq \Pr(\mathsf{Elt}(U))$

$$\varpi_{(C,X)} = X_{(C,\mathsf{id})}$$

The following is a result of Hofmann and Streicher [HS97].

2.2.3. THEOREM. $\varpi$ satisfies (U5).

PROOF. Fix a map $f: Q \longrightarrow X \in \hat{S}_{\vee}$. We must show that there exists some cartesian square $f \longrightarrow \varpi$. First, let us note that $f: Q \longrightarrow X$ induces a presheaf $F: \Pr(\mathsf{Elt}(X))$ and our assumption that $f \in \hat{S}_{\vee}$ ensures that $F$ is essentially $\vee$-small. In particular, we may choose $F' \cong F$ such that $F'$ belongs to the subcategory $\Pr_{\vee}(\mathsf{Elt}(X))$.

We will now construct a cartesian square $f \longrightarrow \varpi$ by defining a morphism explicitly $q: X \longrightarrow U$ and then argue that $q^*\varpi = f$. To this end, let us fix $C: \mathcal{C}$ along with $x \in X_C$ and define $q_C(x) \in U_C = \Pr_{\vee}(\mathcal{C}_{/C})$:

$$q_C(x)_{(D,c)} = F'(D, x \cdot c)$$

The computation that $q$ organizes into a natural transformation is routine.

It remains only to argue that $q^*\varpi$ is isomorphic to $f$. Examining the definition of $\varpi$, it is easiest to argue this by once more passing to $\Pr(\mathsf{Elt}(X))$ and showing that $q^*\varpi \cong F$. However, by definition $q^*\varpi$ is isomorphic to $F'$ which is in turn isomorphic to $F$. ■

10

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The generic map $\mathfrak{m}$ satisfies a number of strict equations and, in particular, it satisfies (U8). The proof is similar to Lemma 2.1.2, but the additional indexing over $\mathcal{C}$ obscures this similarity. Accordingly, we introduce a small amount of machinery beforehand.

Observe first that we may view both $\mathsf{V}$ and $\widetilde{\mathsf{V}}$ as categories, respectively the categories of $\mathsf{V}$-sets and pointed $\mathsf{V}$-sets; this viewpoint is exposed in detail by Awodey, Gambino, and Hazratpour [AGH21, Section 1]. Given that both $\mathsf{V}$ and $\widetilde{\mathsf{V}}$ are small, we may view them as categories internal to $\mathbf{Set}$. For formal reasons, the projection $\mathbf{v}: \widetilde{\mathsf{V}} \longrightarrow \mathsf{V}$ is then a category internal to $\mathbf{Set}^{\rightarrow}$. From this perspective, each $\mathfrak{m}_C = \operatorname{Pr}_{\widetilde{\mathsf{V}}}(\mathcal{C}_{/C}) \longrightarrow \operatorname{Pr}_{\mathsf{V}}(\mathcal{C}_{/C}): \mathbf{Set}^{\rightarrow}$ (the component of the presheaf morphism $\mathfrak{m}$ at $C: \mathcal{C}$) is precisely the objects of the category $\mathbf{v}$-valued presheaves on $\mathbf{id}: \mathcal{C}_{/C} \longrightarrow \mathcal{C}_{/C}$ internal to $\mathbf{Set}^{\rightarrow}$.

Next, let $\alpha: f \longrightarrow \mathfrak{m}$ be a cartesian map in $\operatorname{Pr}(\mathcal{C})^{\rightarrow}$; there is a canonical cartesian map $\hat{\alpha}_C: f_C \longrightarrow \mathbf{v}$ in $\mathbf{Set}^{\rightarrow}$ defined like so:

$$\hat{\alpha}_C(x) = \alpha_C(x)(\mathbf{id}_C)$$

Returning to the perspective of $\mathbf{Set}^{\rightarrow}$, the element $\alpha_C(x)$ is a $\mathbf{v}$-valued presheaf on $\mathcal{C}_{/C}$, hence evaluating at $\mathbf{id}_C$ yields an element of $\mathbf{v}$.

### 2.2.4. THEOREM. The universe $\hat{\mathcal{S}}_{\mathsf{V}}$ satisfies realignment (U8).

PROOF. Fix a realignment problem of the following form in which $\phi$ and $\alpha$ are cartesian, and there exists some cartesian map $\chi: f \longrightarrow \mathfrak{m}$ that we wish to realign as the dotted lift depicted below:

![img-4.jpeg](img-4.jpeg)

For each $C: \mathcal{C}$, we transform the above into a realignment problem for the universe $\mathbf{v}: \widetilde{\mathsf{V}} \longrightarrow \mathsf{V}$ of sets in terms of the cartesian map $\hat{\alpha}_C: h_C \longrightarrow \mathbf{v}$. This yields a cartesian lift $\beta_C: f_C \longrightarrow \mathbf{v}$ in the following configuration.

![img-5.jpeg](img-5.jpeg)

The above is possible because $f_C$ is classified by $\mathbf{v}$. Hence we may define a natural transformation $\tilde{\beta}: f \longrightarrow \mathfrak{m}$ fitting into Diagram 3 as follows:

$$\tilde{\beta}_C(x)(z: D \longrightarrow C) = \beta_D(z \cdot x)$$

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

11

The functorial action on morphisms of $z' \longrightarrow z : \mathcal{C}_{/C}$ is obtained from the fact that each $\beta_D(z \cdot x)$ is isomorphic to $\chi_D(z \cdot x)(\mathbf{id}_D)$, which is a fiber of a $\mathbf{v}$-valued presheaf and hence has the needed functorial action. To check that $\check{\beta}$ restricts along $\phi$ to $\alpha$, we fix $z: D \longrightarrow C$ and compute:

$$\begin{array}{l} \check{\beta}_C(\phi_C(x))(z) = \beta_D(z \cdot \phi_D(x)) \\ = \beta_D(\phi_C(z \cdot x)) \\ = \hat{\alpha}_D(z \cdot x) \\ = \alpha_D(z \cdot x)(\mathbf{id}_D) \\ = \alpha_C(x)(z) \end{array}$$

2.2.5. THEOREM. The class of morphisms $\hat{\mathcal{S}}_{\mathsf{V}}$ in $\Pr(\mathcal{C})$ is a universe satisfying (U1–8).

2.3. STREICHER'S UNIVERSE OF SHEAVES. Fixing a Grothendieck topology $J$ on $\mathcal{C}$, we show that the universe $\hat{\mathcal{S}}_{\mathsf{V}}$ induces a universe on $\operatorname{Sh}(\mathcal{C}, J)$. Let $i: \operatorname{Sh}(\mathcal{C}, J) \to \Pr(\mathcal{C})$ denote the inclusion geometric morphism, so that $i_*$ is the inclusion functor and $i^*$ is sheafification.

2.3.1. DEFINITION. We define $\tilde{\mathcal{S}}_{\mathsf{V}}$ to be the collection of all maps $f$ such that $i_* f \in \hat{\mathcal{S}}_{\mathsf{V}}$.

This collection of maps is easily shown to satisfy (U1–4) because $i_*$ preserves finite limits. The existence of a generic map (U5) has been the source of controversy within the type-theoretic literature; one potential candidate is the restriction of $\pi_{\hat{\mathcal{S}}_{\mathsf{V}}}$ to the presheaf of pointwise V-small sheaves, but this is not actually a sheaf as pointed out by Xu and Escardó [XE16]. Streicher [Str05] proposed a more direct approach: the generic map for $\tilde{\mathcal{S}}_{\mathsf{V}}$ is the sheafification of the generic map for $\hat{\mathcal{S}}_{\mathsf{V}}$. To prove this, we recall Proposition 5.4.4 of van den Berg [vdB11]:

2.3.2. PROPOSITION. If $f \in \hat{\mathcal{S}}_{\mathsf{V}}$ then $i^* f \in \tilde{\mathcal{S}}_{\mathsf{V}}$.

With this to hand, we immediately conclude that $i^* \varpi \in \tilde{\mathcal{S}}_{\mathsf{V}}$.

2.3.3. COROLLARY. The family $i^* \varpi$ is generic for $\tilde{\mathcal{S}}_{\mathsf{V}}$.

PROOF. Fix $f: X \longrightarrow Y \in \tilde{\mathcal{S}}_{\mathsf{V}}$. By definition, $i_* f \in \hat{\mathcal{S}}_{\mathsf{V}}$ so by (U5) the following cartesian square exists:

$$\begin{array}{c} i_* X \longrightarrow \widetilde{\mathrm{U}} \\ \downarrow \quad \downarrow \\ i_* Y \longrightarrow \mathrm{U} \end{array} \tag{5}$$

The image of this cartesian square under $i^*$ remains cartesian and thus shows that $f \cong i^* i_* f$ is classified by $i^* \varpi$.

12

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

### 2.3.4. THEOREM. *The class of maps $\tilde{S}_{\vee}$ is a universe satisfying (U1–6).*

It is natural to wonder whether this universe satisfies (U8), but unfortunately this does not seem to be the case. Fix a realignment problem in $\mathrm{Sh}(\mathcal{C})$:

![img-6.jpeg](img-6.jpeg)

By definition, $i_{*}f$ and $i_{*}h$ both belong to $\tilde{S}_{\vee}$. Moreover, since $i_{*}i^{*}\varpi \in \tilde{S}_{\vee}$ we obtain a cartesian morphism $u: i_{*}i^{*}\varpi \longrightarrow \varpi$ and so Diagram 6 induces a realignment problem in $\mathrm{Pr}(\mathcal{C})$ that can then be solved:

![img-7.jpeg](img-7.jpeg)

While this appears promising, there is no obvious way to relate this realignment problem in $\varpi$ to a solution in $i^{*}\varpi$. In particular, $i^{*}u$ is not the counit $\epsilon: i^{*}i_{*}i^{*}\varpi \longrightarrow i^{*}\varpi$ so $i^{*}\beta \circ \epsilon^{-1}$ does not satisfy the correct boundary condition.

Indeed, one can produce counterexamples to the claim. We are indebted to the reviewer who suggested the following counterexample.

### 2.3.5. LEMMA. *There exists a V-small site $(\mathcal{C}, J)$ such that $i^{*}\varpi$ does not satisfy (U8).*

PROOF. Define $\mathcal{C} = \{0 \leq 1\} \times \{0 \leq 1\}$ and let $J$ be such that $(0, 1)$, $(1, 0)$, and $(1, 1)$ have no non-trivial covers while $(0, 0)$ is covered by the empty sieve. The sheafification functor $i^{*}: \mathrm{Pr}(\mathcal{C}) \longrightarrow \mathrm{Sh}(\mathcal{C}, J)$ sends a presheaf $X: \mathcal{C}^{\mathrm{op}} \longrightarrow \mathbf{Set}$ to the following sheaf:

$$\begin{aligned} (i^{*}X)_{(0,0)} &= \mathbf{1} & (i^{*}X)_{(0,1)} &= X_{(0,1)} \\ (i^{*}X)_{(1,0)} &= X_{(1,0)} & (i^{*}X)_{(1,1)} &= X_{(1,1)} \end{aligned}$$

In particular, both $i^{*}\mathsf{U}_{0,1}$ and $i^{*}\mathsf{U}_{0,1}$ are isomorphic to $\mathrm{Ob}(\mathsf{V}^{\rightarrow})$. Let us consider the arrows $\mathbf{0} \longrightarrow \mathbf{1}$ and $\mathbf{1} \longrightarrow \mathbf{2}$ in $\mathsf{V}$ and write $f_{01}: \mathsf{y}(0,1) \longrightarrow \mathsf{U}$ for the map induced by the former and $f_{10}: \mathsf{y}(1,0) \longrightarrow \mathsf{U}$ for the map induced by the latter. We note that $f_{01}$ and $f_{10}$ classify $\mathbf{id}_{\mathsf{y}(0,1)}$ and $\mathbf{id}_{\mathsf{y}(1,0)}$, respectively.

Fix $P = \mathsf{y}(1,0) \amalg \mathsf{y}(0,1)$ and notice that $i^{*}P$ is the coproduct $i^{*}\mathsf{y}(0,1) \amalg i^{*}\mathsf{y}(1,0)$. We therefore amalgamate $i^{*}f_{01}$ and $i^{*}f_{10}$ into a single morphism:

$$f = i^{*}f_{01} \amalg i^{*}f_{10}: i^{*}P \longrightarrow i^{*}\mathsf{U}$$

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

13

Next, observe that $f$ classifies $i^*P \rightarrow i^*P$ and this family extends along the monomorphism $m: i^*P \rightarrow \mathbf{1}$ to the family $\mathbf{1} \rightarrow \mathbf{1}$. However, there is no morphism classifying $\mathbf{1} \rightarrow \mathbf{1}$ that restricts to $f$ along $m$. Such a morphism would correspond to a $\mathsf{V}$-small presheaf $G: \mathcal{C}^{\mathsf{op}} \rightarrow \mathsf{V}$. If such a presheaf were to restrict correctly to both $i^*f_{01}$ and $i^*f_{10}$ correctly, it would need to satisfy $G_{00} = \mathbf{2}$ and $G_{00} = \mathbf{1}$, which is an impossibility. ■

### 3. Generalities on descent and $\kappa$-compactness

In preparation for our universe construction, we recall notions of descent and compactness together and develop the required theory. Accordingly, fix a Grothendieck topos $\mathcal{E}$. Unless specifically mentioned otherwise, we shall assume that all regular cardinals are infinite.

In Section 1 we observed that the natural notion of morphism between generic maps $\pi$, $\rho$ for a universe is not a merely a commuting square $\pi \rightarrow \rho$ but rather a *cartesian* square; only the latter ensures that a family classified by $\pi$ is also classified by $\rho$. While $\mathcal{E} \rightarrow$ readily adopts the essential characteristics of $\mathcal{E}$ (for instance, it is also a Grothendieck topos) the wide subcategory restricting to cartesian squares is not even cocomplete. We first recall the descent properties of $\mathcal{E}$ to show that this subcategory is closed under coproducts, filtered colimits and pushouts along monomorphisms (Lemma 3.1.4).

In Section 2 we worked with a universe of presheaves valued in small sets. While convenient, this definition of smallness relies on a choice of presentation of a topos as a particular category of presheaves. Under mild restrictions, however, $\tilde{S}_{\mathsf{V}}$ coincides with the class of relatively *compact* morphisms. Compactness is a 'presentation-invariant' notion and thereby readily available in $\mathcal{E}$. We recall the theory of $\kappa$-compactness in $\mathcal{E}$. We show that for sufficiently large $\kappa$, the class of relatively $\kappa$-compact morphisms form a universe satisfying (U1–7) closed under certain colimits (Lemma 3.2.7 and Theorem 3.3.9).

#### 3.1. DESCENT IN A GROTHENDIECK TOPOS.

3.1.1. DEFINITION. A diagram $J: \mathcal{D} \rightarrow \mathcal{E}$ is said to satisfy descent when for any cartesian natural transformation $\alpha: K \rightarrow J$, the induced morphisms $\alpha_d \rightarrow \operatorname{colim}_{d \in \mathcal{D}} \alpha_d$ in $\mathcal{E} \rightarrow$ are cartesian for each $d \in \mathcal{D}$, i.e. the following square is cartesian:

$$\begin{array}{c} K(d) \longrightarrow \operatorname{colim}_{\mathcal{D}} K \\ \downarrow \quad \downarrow \\ J(d) \longrightarrow \operatorname{colim}_{\mathcal{D}} J \end{array}$$

3.1.2. REMARK. We caution the reader that the usages of the word *descent* here and in (U7) are not identical. A diagram $F: \mathcal{D} \rightarrow \mathcal{E}$ satisfying descent essentially stipulates that we may fully characterize families over $\operatorname{colim} F$ by considering cartesian diagrams of families over $F(i)$. In particular, all categorical structures from the latter *descend* to the former. In contrast, (U7) states that a specific property—that of being $\mathcal{S}$-small—is

14

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

amenable to such descent arguments since, in particular, pullback along $\coprod_i F(i) \longrightarrow \operatorname{colim}_F$ induces a suitable cartesian epimorphism.

We will often speak metonymically of a colimit having descent, to mean that the diagram of which it is the colimit has descent.

3.1.3. NOTATION. Write $\mathcal{E}_{\text{cart}} \subseteq \mathcal{E}^\to$ for the wide subcategory spanned by cartesian maps.

3.1.4. LEMMA. Let $J: \mathcal{D} \longrightarrow \mathcal{E}_{\text{cart}}$ be a diagram whose base $J_1: \mathcal{D} \longrightarrow \mathcal{E}$ satisfies descent in the sense of Definition 3.1.1. Then the colimit $\operatorname{colim}_{\mathcal{D}} J$ exists in $\mathcal{E}_{\text{cart}}$.

PROOF. We may first compute the colimit of $J$ in the ordinary arrow category $\mathcal{E}^\to$. Next we must show that each map $J(d) \longrightarrow \operatorname{colim}_{\mathcal{D}} J$ is cartesian, but this is exactly the content of $J_1$ enjoying descent. We must now check that the factorizations induced by the universal property of this colimit in $\mathcal{E}^\to$ are cartesian.

Fixing a cartesian natural transformation $h: J \longrightarrow \{X\}$, we must check that the induced map $h^\sharp: \operatorname{colim}_{\mathcal{D}} J \longrightarrow X$ is cartesian. We may cover $\operatorname{colim}_{\mathcal{D}} J$ by the coproduct $\coprod_{\mathcal{D}} J$; by the descent property of effective epimorphisms, it suffices to check that $\coprod_{\mathcal{D}} J \twoheadrightarrow \operatorname{colim}_{\mathcal{D}} J$ and $\coprod_{\mathcal{D}} J \longrightarrow X$ are both cartesian. To see that $\coprod_{\mathcal{D}} J \twoheadrightarrow \operatorname{colim}_{\mathcal{D}} J$ is cartesian, it suffices to recall that each $J(d) \longrightarrow \operatorname{colim}_{\mathcal{D}} J$ is cartesian by assumption. Likewise to check that $\coprod_{\mathcal{D}} J \longrightarrow X$ is cartesian, it suffices to recall our assumption that each component $h_d: J(d) \longrightarrow X$ is cartesian. ■

While all diagrams satisfy descent in an $\infty$-topos, only some diagrams in 1-topos theory have descent. The following classes of colimits do enjoy descent:

1. Coproducts enjoy descent: this is one phrasing of the traditional disjointness condition that for each $i \neq j$, the fiber product $X_i \times_{\coprod_k X_k} X_j$ is the initial object:

![img-8.jpeg](img-8.jpeg)

2. While pushouts do not generally enjoy descent (see Rezk [Rez10, Example 2.3] for a counterexample), pushouts along monomorphisms do enjoy descent; this property is commonly referred to as *adhesivity* [GL12b].
3. Filtered colimits enjoy descent.

The final condition (verified in Lemma 3.1.6) is a generalization of the *exhaustivity* condition identified by [Shu15].

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

15

PROOF. We must show that for any object $e \in \mathcal{D}$, the comma category $e \downarrow p$ is connected. Fixing $x, y \in {}^{d}/\mathcal{D}$ and $i: e \longrightarrow p(x)$ and $j: e \longrightarrow p(y)$, we must find a zig-zag of morphisms connecting $i$ to $j$ in $e \downarrow p$. Because ${}^{d}/\mathcal{D}$ is filtered, we may find $w \in {}^{d}/\mathcal{D}$ with $m: x \longrightarrow w$ and $n: y \longrightarrow w$. We have two triangles that cannot yet be pasted into a zig-zag:

![img-9.jpeg](img-9.jpeg)

Using the fact that $\mathcal{D}$ is filtered, we may find an arrow $p(w) \longrightarrow z$ that unites the two morphisms $e \longrightarrow p(w)$; because $w$ is under $d$ so is $z$, so in fact we have an arrow $o: w \longrightarrow z$ in ${}^{d}/\mathcal{D}$ with which we may complete the connection between $i$ and $j$:

![img-10.jpeg](img-10.jpeg)

Lemma 3.1.6 below is verified in greater generality by Garner and Lack [GL12a, Proposition 5.10]; we provide a direct proof for expository purposes.

3.1.6. LEMMA. Any filtered diagram $F: \mathcal{D} \longrightarrow \mathcal{E}$ enjoys descent.

PROOF. We fix a cartesian natural transformation $G \longrightarrow F$ and must check for each $d \in \mathcal{D}$ the following square is cartesian:

![img-11.jpeg](img-11.jpeg)

Because $\mathcal{D}$ is filtered, we may replace the indexing category with the coslice ${}^{d}/\mathcal{D}$ by

16

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

Lemma 3.1.5, noting that $\operatorname{colim}_{d/\mathcal{D}} H = \operatorname{colim}_{\mathcal{D}} H$ for any diagram $H: \mathcal{D} \to \mathcal{E}$.

$$\begin{array}{ccc} G(d) & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} G \\ \downarrow & & \downarrow \\ F(d) & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} F \end{array} \tag{8}$$

We observe that any object is the colimit of the constant $d/\mathcal{D}$-diagram it determines as $d/\mathcal{D}$ is connected; therefore we may rewrite Diagram 8 as follows:

$$\begin{array}{ccc} \operatorname{colim}_{d/\mathcal{D}} \{G(d)\} & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} G \\ \downarrow & & \downarrow \\ \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} F \end{array}$$

Recall that filtered colimits commute with finite limits, so it suffices to check that the following square below is cartesian for $d \to e$:

$$\begin{array}{ccc} G(d) & \longrightarrow & G(e) \\ \downarrow & & \downarrow \\ F(d) & \longrightarrow & F(e) \end{array} \tag{9}$$

But Diagram 9 is cartesian because we have assumed that $G \to F$ is cartesian. ■

We recall the notion of *ideal diagram* from Awodey and Forssell [AF05].

3.1.7. DEFINITION. *An ideal diagram in a category $\mathcal{E}$ is a functor $\mathcal{D} \to \mathcal{E}$ where $\mathcal{D}$ is a small filtered preorder and the image of each $d \leq e$ is a monomorphism in $\mathcal{E}$.*

3.1.8. LEMMA. *If $F: \mathcal{D} \to \mathcal{E}$ is an ideal diagram, then each edge $F(d) \to \operatorname{colim}_{\mathcal{D}} F$ in its colimit cocone is a monomorphism.*

PROOF. This follows for essentially the same reason as Lemma 3.1.6. Fixing $d \in \mathcal{D}$, to see that $F(d) \to \operatorname{colim}_{\mathcal{D}} F$ is a monomorphism it suffices to check that the following diagram is cartesian:

$$\begin{array}{ccc} F(d) & = & F(d) \\ \downarrow & & \downarrow \\ F(d) & \longrightarrow & \operatorname{colim}_{\mathcal{D}} F \end{array} \tag{10}$$

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

17

Because $\mathcal{D}$ is filtered, by Lemma 3.1.5 we may replace Diagram 10 as follows:

$$\begin{array}{c} \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} \xleftarrow{\quad} \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} \xrightarrow{\quad} \operatorname{colim}_{d/\mathcal{D}} F \end{array}$$

Because filtered colimits commute with finite limits, it suffices to check that each of the following squares is cartesian for $e \geq d$:

$$\begin{array}{c} F(d) \xleftarrow{\quad} F(d) \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ F(d) \longrightarrow F(e) \end{array}$$

But we have already assumed $F(d) \longrightarrow F(e)$ to be a monomorphism. ■

3.1.9. REMARK. For any regular cardinal $\kappa \geq \omega$, a $\kappa$-filtered diagram [AR94, Remark 1.21] is filtered. Accordingly, both Lemmas 3.1.6 and 3.1.8 hold for $\kappa$-filtered diagrams.

3.1.10. LEMMA. Let $F, G: \mathcal{D} \longrightarrow \mathcal{E}$ be two diagrams such that $G$ satisfies descent, and let $F \longmapsto G$ be a cartesian monomorphism. Then the induced map $\operatorname{colim}_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} G$ is a monomorphism.

PROOF. We need to check that the following square is cartesian:

$$\begin{array}{c} \operatorname{colim}_{\mathcal{D}} F \xleftarrow{\quad} \operatorname{colim}_{\mathcal{D}} F \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \operatorname{colim}_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} G \end{array}$$

We can cover $\operatorname{colim}_{\mathcal{D}} F$ by $\coprod_{\mathcal{D}} F$; by descent of cartesian squares along covers, it suffices to prove that the outer square below is cartesian:

$$\begin{array}{c} \coprod_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} F \xleftarrow{\quad} \operatorname{colim}_{\mathcal{D}} F \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \coprod_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} G \\ \searrow \searrow \searrow \searrow \searrow \searrow \searrow \\ \coprod_{\mathcal{D}} G \end{array} \tag{11}$$

18

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

We have factored the downstairs map of Diagram 11 using the universal property of the coproduct. Our strategy to show that Diagram 11 is cartesian is to exhibit it as the pasting of two cartesian squares, as hinted by our factorization. In particular, by pasting pullbacks it is enough to prove that the right-hand square below is cartesian:

$$\begin{array}{ccc} \coprod_{\mathcal{D}} F & \longrightarrow & \coprod_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} F \\ \updownarrow & & \downarrow \\ \coprod_{\mathcal{D}} F & \longmapsto & \coprod_{\mathcal{D}} G \longrightarrow \operatorname{colim}_{\mathcal{D}} G \end{array} \quad (12)$$

The left-hand square of Diagram 12 can be seen to be cartesian using our assumption that $F \longmapsto G$ is a monomorphism. To see that the right-hand square is cartesian, we will use our descent hypothesis for $G$. In particular, it suffices to check that each of the squares below is cartesian:

$$\begin{array}{ccc} F(d) & \longrightarrow & \operatorname{colim}_{\mathcal{D}} F \\ \updownarrow & & \updownarrow \\ G(d) & \longrightarrow & \operatorname{colim}_{\mathcal{D}} G \end{array}$$

But this is exactly the condition that $G: \mathcal{D} \longrightarrow \mathcal{E}$ have descent.

3.2. COMPACT OBJECTS AND RELATIVELY COMPACT MAPS. We recall some of the theory of compact objects. We refer the reader to Adámek and Rosický [AR94] for a detailed exposition of compact objects and locally presentable categories.

3.2.1. DEFINITION. An object $X \in \mathcal{E}$ is said to be $\kappa$-compact when the functor $\operatorname{Hom}_{\mathcal{E}}(X, -)$ preserves $\kappa$-filtered colimits. Following Lurie [Lur09], a morphism $X \longrightarrow Y$ is said to be relatively $\kappa$-compact if for each $\kappa$-compact object $Z$ and morphism $Z \longrightarrow Y$, the pullback $Z \times_Y X$ is $\kappa$-compact:

$$\begin{array}{ccc} Z \times_Y X & \longrightarrow & X \\ \updownarrow & & \updownarrow \\ Z & \longrightarrow & Y \end{array}$$

More tersely, the fibers of $X \longrightarrow Y$ over $\kappa$-compact objects are $\kappa$-compact.

3.2.2. REMARK. We note that the requirement that $X \longrightarrow \mathbf{1}$ be relatively $\kappa$-compact is a priori stronger than merely asking $X$ to be $\kappa$-compact. Their equivalence amounts to requiring $\kappa$-compact objects to be closed under products, which will hold in all cases of importance for us.

3.2.3. NOTATION. We will write $\mathcal{S}_\kappa$ for the class of relatively $\kappa$-compact maps in $\mathcal{E}$.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

19

3.2.4. DEFINITION. A category $\mathcal{C}$ is locally $\kappa$-presentable when $\mathcal{C}$ is cocomplete and there is a set of $\kappa$-compact objects that generates $\mathcal{C}$ under $\kappa$-filtered colimits.

3.2.5. NOTATION. As a Grothendieck topos, $\mathcal{E}$ is locally $\kappa$-presentable for some regular cardinal $\kappa$. For the remainder of this subsection, we fix $\kappa$ to be such a cardinal.

The colimit of a diagram in $\mathcal{E}^\rightarrow$ of relatively $\kappa$-compact morphisms is not necessarily relatively $\kappa$-compact. For a simple counterexample, consider an object $X$ that is *not* $\kappa$-compact; then the following pushout of relatively $\kappa$-compact morphisms is not relatively $\kappa$-compact:

![img-12.jpeg](img-12.jpeg)

More can be said when the diagram is cartesian (*i.e.* valued in $\mathcal{E}_{cart}^\rightarrow$). In particular, relatively $\kappa$-compact morphisms are closed under colimits of cartesian diagrams whose bases satisfy descent in the sense of Definition 3.1.1, which we verify in Lemma 3.2.7. We first recall Proposition 4.18 of Shulman [Shu19].

3.2.6. PROPOSITION. Let $J: \mathcal{D} \rightarrow \mathcal{E}$ be a diagram and let $Y$ be its colimit; a morphism $X \rightarrow Y$ is relatively $\kappa$-compact if and only if for each $d \in \mathcal{D}$, the pullback $X \times_Y J(d) \rightarrow J(d)$ depicted below is relatively $\kappa$-compact:

![img-13.jpeg](img-13.jpeg)

PROOF. The only if direction is clear, so suppose for each $d \in \mathcal{D}$, $X \times_Y J(d) \rightarrow J(d)$ is relatively $\kappa$-compact. We must show that $X \rightarrow Y$ is relatively $\kappa$-compact. Recall that any diagram can be presented as a $\kappa$-filtered diagram of colimits of $\kappa$-small sub-diagrams [Mac98, Theorem IX.1.1]. Therefore, it suffices to show that this holds when $J$ is $\kappa$-filtered and when $J$ is $\kappa$-small.

First suppose $J$ is $\kappa$-filtered. Fix a $\kappa$-compact object $Z$ together with a morphism $Z \rightarrow Y$, we must show that the pullback $Z \times_Y X$ is $\kappa$-compact. As $Y$ is the colimit of a

20

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

$\kappa$-filtered diagram, the morphism $Z \longrightarrow Y$ must factor through some $J(d) \longrightarrow Y$:

![img-14.jpeg](img-14.jpeg)

By assumption, $J(d) \times_Y X \longrightarrow J(d)$ is relatively $\kappa$-compact so $Z \times_Y X$ is $\kappa$-compact.

Next, suppose that $J$ is a $\kappa$-small diagram. In this case, the diagram category $\mathcal{E}^\mathcal{D}$ is also locally $\kappa$-presentable [AR94, Corollary 1.54]. Accordingly, $D = \operatorname{colim}_{i \in \mathcal{I}} E_i$, where each $E_i$ is a $\kappa$-compact object in $\mathcal{E}^\mathcal{D}$ and $\mathcal{I}$ is $\kappa$-filtered. Each $E_i(d)$ is $\kappa$-compact [Shu19, Lemma 4.2] and by commutation of colimits $Y = \operatorname{colim}_{i \in \mathcal{I}} \operatorname{colim}_{d \in \mathcal{D}} E_i(d)$.

By assumption $\mathcal{I}$ is $\kappa$-filtered so by the already proven case it suffices to show that $X \times_Y \operatorname{colim}_d E_i(d) \longrightarrow \operatorname{colim}_d E_i(d)$ is relatively $\kappa$-compact for each $i \in \mathcal{I}$. As the $\kappa$-small colimit of $\kappa$-small objects, $\operatorname{colim}_d E_i(d)$ is $\kappa$-compact so this morphism is relatively $\kappa$-compact if and only if $X \times_Y \operatorname{colim}_d E_i(d)$ is $\kappa$-compact. By universality of colimits, we have a sequence of identifications:

$$X \times_Y \operatorname{colim}_d E_i(d) = \operatorname{colim}_d X \times_Y E_i(d) = \operatorname{colim}_d((X \times_Y J(d)) \times_{J(d)} E_i(d))$$

Thus, this object is $\kappa$-compact as the $\kappa$-small colimit of $\kappa$-compact objects. ■

3.2.7. LEMMA. The colimit of a diagram $J: \mathcal{D} \longrightarrow \mathcal{E}_{\text{cart}}^\rightarrow$ of relatively $\kappa$-compact morphisms is relatively $\kappa$-compact if the base $J_1: \mathcal{D} \longrightarrow \mathcal{E}$ satisfies descent in the sense of Definition 3.1.1.

PROOF. By Proposition 3.2.6 it suffices to check that each fiber $i_d^* \operatorname{colim}_\mathcal{D} J_0: \mathcal{E}^\rightarrow$ below is relatively $\kappa$-compact:

![img-15.jpeg](img-15.jpeg)

Because $J_1$ satisfies descent, the cartesian square depicted in Diagram 13 is actually $J(d) \longrightarrow \operatorname{colim}_\mathcal{D} J$; but we have already assumed that $J(d)$ is relatively $\kappa$-compact. ■

3.2.8. LEMMA. The class of maps $\mathcal{S}_\kappa$ satisfies the descent axiom (U7).

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

21

PROOF. Let $g$ be a relatively $\kappa$-compact morphism equipped with a cartesian epimorphism $g \to f$ as below:

$$\mathcal{S}_\kappa \ni g \begin{array}{c} C \xrightarrow{a} A \\ \downarrow \\ D \xrightarrow{b} B \end{array} \begin{array}{c} f \\ \downarrow \\ \end{array}$$

We must show that $f$ is relatively $\kappa$-compact. We will use the fact that both $a: C \to A$ and $b: D \to B$ are coequalizers of their kernel pairs, and that kernel pairs are stable:

$$\begin{array}{c} C \times_A C \xrightarrow[q_1]{q_2} C \xrightarrow[a]{a} A \\ \downarrow \\ D \times_B D \xrightarrow[p_2]{p_1} D \xrightarrow[b]{b} B \end{array} \begin{array}{c} f \\ \downarrow \\ \end{array} \tag{14}$$

By Proposition 3.2.6 it suffices to check that $b^*f$, $(b \circ p_0)^*f$, and $(b \circ p_1)^*f$ are relatively $\kappa$-compact. But each of these is a pullback of $g$ (Diagram 14) and therefore by stability (U1), $f$ is relatively $\kappa$-compact. ■

3.3. RELATING SMALL AND RELATIVELY COMPACT MAPS. For this subsection, fix a presentation $\mathcal{E} = \text{Sh}(\mathcal{E}, J)$ and write $i^* \dashv i_*$ for the geometric embedding $\text{Sh}(\mathcal{E}, J) \hookrightarrow \text{Pr}(\mathcal{E})$. Recall that a presheaf $P \in \text{Pr}(\mathcal{E})$ is $\kappa$-small when each $P(C)$ is a $\kappa$-small set. Under mild assumptions, small presheaves precisely correspond to compact presheaves. We reproduce a proof due to Adámek and Rosický [AR94, Example 1.31]:

3.3.1. LEMMA. Given a regular cardinal $\kappa > |\mathcal{E}|$ and a presheaf $P \in \text{Pr}(\mathcal{E})$, the latter is $\kappa$-compact if and only if it is valued in $\kappa$-small sets.

PROOF. First express $P$ as the colimit of representables: $P = \text{colim}_{(c,p) \in \text{Elt}(P)} \mathbf{y}(c) = \text{colim}_{\text{Elt}(P)} \mathbf{y} \circ \pi$. On one hand, if $P$ is valued in $\kappa$-small sets, then $\text{Elt}(P)$ is $\kappa$-small, while each $\mathbf{y}(c)$ is $\kappa$-compact. Thus, $P$ is a $\kappa$-small colimit of $\kappa$-compact objects, hence $\kappa$-compact.

On the other hand, suppose instead that $P$ is $\kappa$-compact; we will show that it is valued in $\kappa$-small sets. By completing $\text{Elt}(P)$ under $\kappa$-small colimits and extending $\mathbf{y} \circ \pi$ by colimits, we obtain a $\kappa$-filtered diagram $\mathcal{D}$ and a map $F: \mathcal{D} \to \text{Pr}(\mathcal{E})$ which sends a formal colimit to a $\kappa$-small colimit of representables. Observe that each $F(d)$ is $\kappa$-small as a $\kappa$-small colimit of representables. Moreover, the canonical map $p: \text{colim}_{\mathcal{D}} F \to P$ is an isomorphism [AR94, Theorem 1.20] so that, in particular, $P$ is the $\kappa$-filtered colimit of $\kappa$-small objects.

22

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

As $P$ is $\kappa$-compact, we obtain a map $r: P \longrightarrow F(d)$ for some $d: \mathcal{D}$ fitting into the following diagram:

![img-16.jpeg](img-16.jpeg)

It follows immediately that $r$ is monic, and so $P$ is a subobject of $F(d)$. As $F(d)$ is valued in $\kappa$-small sets, so is $P$.

3.3.2. LEMMA. *For any $\kappa > |\mathcal{C}|$, a morphism $f: P \longrightarrow Q$ is relatively $\kappa$-compact in $\Pr(\mathcal{C})$ if and only if the fibers of $f$ over representable presheaves are $\kappa$-compact.*

PROOF. The only-if direction is immediate, so it suffices to show that $f$ is relatively compact provided that its fibers over representable presheaves are compact. To this end, fix a $\kappa$-compact presheaf $R$ and a morphism $g: R \longrightarrow Q$:

![img-17.jpeg](img-17.jpeg)

We must show that $g^*P$ is $\kappa$-compact. Viewing $R$ as a colimit of representables, universality ensures that $g^*P = \text{colim}_{(C,r) \in \text{Elt}(R)} f^*\mathbf{y}(C)$. By assumption, each $f^*\mathbf{y}(C)$ is $\kappa$-compact, and by Lemma 3.3.1 $\text{Elt}(R)$ is a $\kappa$-small category. Accordingly, as a $\kappa$-small colimit of $\kappa$-compact objects, $g^*P$ is $\kappa$-compact.

For the next sequence of results, we shall require some results from the theory of accessible categories and accessible functors. In order to state them, we require a small amount of set-theoretic bureaucracy in the form of the $\triangleright$ relation:

3.3.3. DEFINITION. *A cardinal $\lambda > \kappa$ is sharply larger than $\kappa$, notated $\lambda \triangleright \kappa$, if each $\kappa$-accessible category is $\lambda$-accessible.*

We emphasize that $\lambda \triangleright \kappa$ is not the same as $\lambda > \kappa$ nor does it mean anything akin to “$\lambda$ is much larger than $\kappa$”. We refer the reader to Adámek and Rosický [AR94, Theorem 2.11] for more information about $\triangleright$. For our purposes it suffices to know that if $\lambda$ is strongly inaccessible then $\kappa < \lambda$ is equivalent to $\kappa \triangleleft \lambda$.

3.3.4. LEMMA. *There exists a cardinal $\lambda_0$ such that for any $\lambda \triangleright \lambda_0$, both $i_*$ and $i^*$ preserve $\lambda$-filtered colimits and $\lambda$-compact objects.*

PROOF. As adjoints $i_*$ and $i^*$ are both accessible functors. Therefore, the result follows immediately from the uniformization result (2.19) of Adámek and Rosický [AR94].

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

23

3.3.5. LEMMA. If $i^*$ preserves $\lambda$-compact objects, then $i_*$ reflects them.

PROOF. Let $E \in \operatorname{Sh}(\mathcal{C}, J)$ be such that $i_*E$ is $\lambda$-compact; because $i^*$ preserves $\lambda$-compact objects, $i^*i_*E \cong E$ is $\lambda$-compact.

Combining the above result with the characterization of $\kappa$-compact objects given by Lemma 3.3.1, we deduce the following.

3.3.6. COROLLARY. Given a regular cardinal $\lambda$ sharply larger than both $\lambda_0$ and $|\mathcal{C}|$, the following properties hold:

1. $\mathcal{E}$ is locally $\lambda$-presentable.
2. The $\lambda$-compact objects in $\mathcal{E}$ are closed under finite limits.

If $\lambda$ is further assumed to be strongly inaccessible, then we additionally have:

3. The set $\operatorname{Hom}_{\mathcal{E}}(X, Y)$ between two $\lambda$-compact objects $X, Y$ is $\lambda$-small.

3.3.7. LEMMA. Given a regular cardinal $\lambda$ sharply larger than both $\lambda_0$ and $|\mathcal{C}|$, the direct image functor $i_*$ preserves and reflects relatively $\lambda$-compact morphisms.

PROOF. We handle preservation and reflection separately.

Preservation. Let $X \longrightarrow Y$ be a relatively $\lambda$-compact morphism in $\mathcal{E}$. We must check that $i_*X \longrightarrow i_*Y$ is relatively $\lambda$-compact. Fixing a $\lambda$-compact object $Z \in \operatorname{Pr}(\mathcal{C})$ along with a map $Z \longrightarrow i_*Y$, it suffices to argue that the fiber product $W = Z \times_{i_*Y} i_*X$ is $\lambda$-compact:

![img-18.jpeg](img-18.jpeg)

Observe that $Z \longrightarrow i_*Y$ factors uniquely through $\eta_Z: Z \longrightarrow i_*i^*Z$. As $i_*$ preserves cartesian squares, we can factor the above cartesian square as follows:

![img-19.jpeg](img-19.jpeg)

Recalling that $i^*$ preserves $\lambda$-compact objects (Lemma 3.3.4), $i^*Z$ is $\lambda$-compact and consequently so too is $i^*Z \times_Y X$. By Lemma 3.3.4 again, both $i_*i^*Z$ and $i_*(i^*Z \times_Y X)$ are $\lambda$-compact. Finally, $W$ is $\lambda$-compact as the finite limit of $\lambda$-compact objects (Corollary 3.3.6).

24

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

*Reflection.* Let $X \rightarrow Y$ be a morphism in $\mathcal{E}$ such $i_*X \rightarrow i_*Y$ is relatively $\lambda$-compact in $\Pr(\mathcal{C})$. Fixing a morphism $Z \rightarrow Y$ with $Z$ a $\lambda$-compact object, we must check that the fiber product $W$ below is $\lambda$-compact:

![img-20.jpeg](img-20.jpeg)

The right adjoint $i_*$ preserves $\lambda$-compact objects by assumption (Lemma 3.3.4) and hence $i_*Z$ is $\lambda$-compact; because $i_*$ also preserves pullbacks, we deduce that $i_*W$ is a $\lambda$-compact object in $\Pr(\mathcal{C})$:

![img-21.jpeg](img-21.jpeg)

Finally, Lemma 3.3.5 implies $W$ is $\lambda$-compact. ■

3.3.8. REMARK. The proof of Lemma 3.3.7 establishes a more general result: a right adjoint $G: \mathcal{C} \rightarrow \mathcal{D}$ between finitely complete categories preserves relatively $\kappa$-compact families provided both adjoints preserve $\kappa$-compact objects and $\kappa$-compact objects in $\mathcal{D}$ are closed under finite limits. If $G$ is additionally assumed to reflect $\kappa$-compact objects, it reflects $\kappa$-compact families.

Combining the above results with Theorem 2.3.4, we obtain the following result:

3.3.9. THEOREM. *There exists a cardinal $\kappa$ such that for any strongly inaccessible $\lambda \triangleright \kappa$, $\mathcal{E}$ is locally $\lambda$-presentable and the class of relatively $\lambda$-compact maps in $\mathcal{E}$ form a universe $\mathcal{S}_\lambda$ satisfying (U1–7) and $\lambda$-compact objects are closed under finite limits.*

PROOF. We define $\kappa$ to be any regular cardinal sharply larger than both $\lambda_0$ and $|\mathcal{C}|$. We first recall that $\mathcal{E}$ is locally $\lambda$-presentable and that $\lambda$-compact objects are closed under finite limits by Corollary 3.3.6. Next, Theorem 2.3.4 combined with Lemmas 3.3.1, 3.3.2 and 3.3.7 ensures that for any $\lambda \triangleright \kappa$, the universe $\mathcal{S}_\lambda$ satisfies (U1–6). Finally, we have established that $\mathcal{S}_\lambda$ satisfies (U7) in Lemma 3.2.8. ■

3.3.10. DEFINITION. *We write $\mathfrak{c}(\mathcal{E})$ for the cardinal $\kappa$ provided by Theorem 3.3.9.*

3.3.11. COROLLARY. *For any strongly inaccessible $\lambda \triangleright \mathfrak{c}(\mathcal{E})$, the full subcategory of $\mathcal{E}/Y$ spanned by relatively $\lambda$-compact maps is essentially small.*

PROOF. Writing $\mathfrak{w}_\lambda: \tilde{\mathrm{U}}_\lambda \rightarrow \mathrm{U}_\lambda$ for the generic map of $\mathcal{S}_\lambda$, this subcategory of $\mathcal{E}/Y$ is bounded by $\mathrm{Hom}(Y, \mathrm{U}_\lambda)$. ■

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

25

3.3.12. LEMMA. For any strongly inaccessible $\lambda \triangleright \mathfrak{c}(\mathcal{E})$, there exists a $\lambda$-small set of monomorphisms $\mathcal{I}$ generating all monomorphisms in $\mathcal{E}$ under pushout, transfinite composition, and retracts. Moreover, the domains and codomains of morphisms in $\mathcal{I}$ are $\lambda$-compact.

PROOF. Beke [Bek00, Proposition 1.12] shows that the collection of sub-quotients of representables $J$ generate all monomorphisms in $\operatorname{Pr}(\mathcal{C})$. Explicitly, $J$ is the collection of monomorphisms $A \mapsto B$ where $B$ is the quotient of a representable $\mathbf{y}(C)$. As $\operatorname{Pr}(\mathcal{C})$ is both well-powered and co-well-powered there is essentially a set of such monomorphisms.

A quotient of a representable $\mathbf{y}(C)$ is determined by a morphism $\mathbf{y}(C) \times \mathbf{y}(C) \longrightarrow \Omega$. As $\lambda > |\mathcal{C}|$, $\Omega$ is $\lambda$-small and there is a $\lambda$-small set of representables therefore $J$ may be chosen to be $\lambda$-small. Finally, the domains and codomains of monomorphisms in $J$ are $\lambda$-small, since they are subquotients of representables which are $\lambda$-small; and by Lemma 3.3.1, this implies they are $\lambda$-compact.

We now define $\mathcal{I} \subset \operatorname{Hom}_{\mathcal{E}}$ as the image of $J$ under $i^*$. As $i_*$ preserves monomorphisms and $i^*$ preserves all colimits, $\mathcal{I}$ generates all monomorphisms in $\mathcal{E}$ under pushout, transfinite composition, and retracts. The domains and codomains of morphisms in $\mathcal{I}$ are seen to be $\lambda$-compact by Lemma 3.3.4.

## 4. Main result: a universe satisfying realignment

Let $\mathcal{E}$ be a Grothendieck topos and fix a strongly inaccessible cardinal $\kappa \triangleright \mathfrak{c}(\mathcal{E})$. We have previously shown that $\mathcal{S}_\kappa$ satisfies (U1–7). We construct a new generic map for this class and thereby conclude that $\mathcal{S}_\kappa$ satisfies (U8).

4.1. SATURATION OF SOLVABLE REALIGNMENT PROBLEMS. In Definition 1.1.4 we specified what it means for a universe to have realignment for a class of monomorphisms $\mathcal{M}$. On the other hand, any pullback-stable class of maps $\mathcal{S}$ and morphism $\pi \colon E \longrightarrow U \in \mathcal{S}$ determines a class $\mathcal{J}_\pi$ of monomorphisms along which realignment problems can be solved (regardless of whether $\mathcal{S}$ is a universe and whether $\pi$ is generic).

4.1.1. NOTATION. We will write $\mathcal{J}_\pi$ for the set of all monomorphisms in $\mathcal{E}$ with respect to which $(\mathcal{S}, \pi)$ satisfies the realignment property.

We will establish the closure of $\mathcal{J}_\pi$ under pushout, transfinite composition, and retracts.

4.1.2. LEMMA. The class of realignable monomorphisms $\mathcal{J}_\pi$ is stable under pushout.

PROOF. Fix $A \mapsto B \in \mathcal{J}_\pi$ and a pushout diagram in the following configuration:

$$\begin{array}{c} A \longrightarrow C \\ \updownarrow \\ B \longrightarrow D \end{array} \tag{15}$$

26

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

We must show that $C \rightharpoonup D \in \mathcal{J}_{\pi}$; to that end, we fix a realignment problem $f \longleftarrow h \longrightarrow \pi$ whose extent lies over $C \rightharpoonup D$.

![img-22.jpeg](img-22.jpeg)

We will transform the realignment problem of Diagram 16 into one that we can already solve; first we fill in the cartesian lifts over the pushout square in the base.

![img-23.jpeg](img-23.jpeg)

By the universality of colimits, the upper face is a pushout; therefore to solve our realignment problem, it suffices to find a map $B^*f \longrightarrow \pi$ making the following square commute:

![img-24.jpeg](img-24.jpeg)

Because $\mathcal{S}$ is stable under pullback, we have $B^*f \in \mathcal{S}$; therefore Diagram 18 is itself a realignment problem whose extent lies over an element of $\mathcal{J}_{\pi}$.

4.1.3. NOTATION. We will write $\mathcal{O}_{<\alpha}$ for the filtered poset of ordinal numbers $\beta < \alpha$.
4.1.4. LEMMA. The class of realignable monomorphisms $\mathcal{J}_{\pi}$ is stable under transfinite composition.

PROOF. Let $F: \mathcal{O}_{<\alpha} \longrightarrow \mathcal{E}$ be a cocontinuous functor such that each $F(\beta) \longrightarrow F(\beta + 1)$ is an element of $\mathcal{J}_{\pi}$. We must show that the transfinite composition $F(0) \longrightarrow \operatorname{colim}_{\mathcal{O}_{<\alpha}} F$ is an ele-

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

27

ment of $\mathcal{J}_{\pi}$. We fix a realignment situation whose extent lies over some $F(0) \mapsto \operatorname{colim}_{\mathcal{O}_{<\alpha}} F$:

![img-25.jpeg](img-25.jpeg)

By the universality of colimits, we may replace $f$ with $\operatorname{colim}_{\mathcal{O}_{<\alpha}} f_{\bullet}$ where we define $f_{\bullet}: \mathcal{O}_{<\alpha} \longrightarrow \mathcal{E}_{cart}^{\rightarrow}$ to extend $f_0$ by sending each $f_{\beta}$ to the following cartesian lift:

![img-26.jpeg](img-26.jpeg)

Our realignment problem can therefore be rewritten as follows:

![img-27.jpeg](img-27.jpeg)

We will define the natural transformation $\operatorname{colim}_{\mathcal{O}_{<\alpha}} f_{\bullet} \longrightarrow \pi$ by transfinite induction on $\beta \leq \alpha$. In the zero case, we use our existing map $f_0 \longrightarrow \pi$. In the successor case, we assume a map $f_{\beta} \longrightarrow \pi$ extending $f_0 \mapsto f_{\beta}$ and glue $f_{\beta} \longrightarrow \pi$ along $f_{\beta} \mapsto f_{\beta+1} \in \mathcal{J}_{\pi}$:

![img-28.jpeg](img-28.jpeg)

The limit case is trivial, as we may assemble all the prior solutions into a single one

28

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

using the universal property of $f_\beta$ as $\operatorname{colim}_{\mathcal{O}_{<\beta}} f_\bullet$:

![img-29.jpeg](img-29.jpeg)

We note that $\operatorname{colim}_{\mathcal{O}_{<\beta}} f_\bullet \longrightarrow \pi$ remains cartesian by the universality of colimits.

The extension to Diagram 23 remains natural because we have merely combined the solutions to the smaller realignment problems. ■

4.1.5. LEMMA. *The class of realignable monomorphisms $\mathcal{J}_\pi$ is closed under retracts.*

PROOF. We fix $j: A \rightharpoonup B \in \mathcal{J}_\pi$ and a retract $i: C \rightharpoonup D$ of $j$ in $\mathcal{E}^\to$:

![img-30.jpeg](img-30.jpeg)

To check that $i \in \mathcal{J}_\pi$, we fix a realignment problem whose extent lies over $i: C \rightharpoonup D$:

![img-31.jpeg](img-31.jpeg)

We restrict Diagram 25 along Diagram 24:

![img-32.jpeg](img-32.jpeg)

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

29

We first glue $A^*h \longrightarrow \pi$ along $A^*h \succ B^*f$ which lies over $j \in \mathcal{J}_\pi$:

![img-33.jpeg](img-33.jpeg)

The dotted map of Diagram 27 restricts along the left-most square of $f \longrightarrow B^*f$ to a solution to our original realignment problem (Diagram 25):

![img-34.jpeg](img-34.jpeg)

4.2. A SMALL OBJECT ARGUMENT. In this section we construct a candidate for the generic family of $\mathcal{S}_\kappa$, using a variant of the small object argument. Our construction is very similar to that of Shulman [Shu15; Shu19] but relies on different assumptions.

By Lemma 3.3.12, there is a $\kappa$-small set of monomorphisms $\mathcal{I} \subseteq \mathcal{E}^-$ generating all the monomorphisms of $\mathcal{E}$ under pushout, transfinite composition, and retracts, and whose domains and codomains are $\kappa$-compact.

4.2.1. DEFINITION. Let $\pi: E \longrightarrow U$ be a relatively $\kappa$-compact map. A realignment datum for $\pi$ is defined to be a relatively $\kappa$-compact map $f$ together with a span of the following form in $\mathcal{E}_{\text{cart}}$, in which $h \succ f$ lies horizontally over an element of $\mathcal{I}$:

$$f \longleftarrow h \longrightarrow \pi$$

There is of course a proper class of realignment data in the sense of Definition 4.2.1, but Corollary 3.3.11 ensures that up to isomorphism there is only a set of realignment data.

4.2.2. NOTATION. We will write $\mathsf{D}_\kappa(\pi)$ for the chosen set of representatives of isomorphism classes of realignment data for $\pi$; for any $d \in \mathsf{D}_\kappa(\pi)$, we will write $f_d \longleftarrow h_d \longrightarrow \pi$ for the span it represents.

We record the following lemma for use in Section 4.4.

4.2.3. LEMMA. Given a strongly inaccessible cardinal $\mu > \kappa$ and a relatively $\kappa$-compact morphism $\pi: E \longrightarrow U$ such that $U$ is $\mu$-compact, the set $\mathsf{D}_\kappa(\pi)$ is $\mu$-small.

PROOF. Given $A \succ B \in \mathcal{I}$, there is a $\mu$-small set of morphisms $B \longrightarrow U$ by Corollary 3.3.6. As $\mathcal{I}$ is $\kappa$-small, the conclusion then follows.

30

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

4.2.4. CONSTRUCTION. We will define an ideal diagram $\pi_\kappa^\bullet: \mathcal{O}_{<\kappa} \longrightarrow \mathcal{E}_{cart}^\rightarrow$ by well-founded induction, finally defining the family $\pi_\kappa: \mathcal{E}_{cart}^\rightarrow$ to be $\operatorname{colim}_{\mathcal{O}_{<\kappa}} \pi_\kappa^\bullet$:

![img-35.jpeg](img-35.jpeg)

We initialize the iteration by setting $\pi_\kappa^0 := \mathbf{0}_{\mathcal{E}_{cart}^\rightarrow}$. In the successor case, we assume $\pi_\kappa^\alpha \in \mathcal{E}_{cart}^\rightarrow$ and define $\pi_\kappa^{\alpha+1}$ to be the following pushout computed in $\mathcal{E}_{cart}^\rightarrow$ using Lemma 3.1.4.

![img-36.jpeg](img-36.jpeg)

At a limit ordinal $\alpha$, fix an ideal diagram $\pi_\kappa^\bullet: \mathcal{O}_{<\alpha} \longrightarrow \mathcal{E}_{cart}^\rightarrow$ and define $\pi_\kappa^\alpha := \operatorname{colim}_{\mathcal{O}_{<\alpha}} \pi_\kappa^\bullet$.

4.2.5. LEMMA. *The ideal diagram $\pi_\kappa^\bullet: \mathcal{O}_{<\kappa} \longrightarrow \mathcal{E}_{cart}^\rightarrow$ from Construction 4.2.4 is valued in relatively $\kappa$-compact morphisms.*

PROOF. We proceed by induction on ordinals $\alpha \leq \kappa$. The base case $\pi_\kappa^0 = \mathbf{0}_{\mathcal{E}_{cart}^\rightarrow}$ is relatively $\kappa$-compact by Lemma 3.2.7. Next we check that $\pi_\kappa^{\alpha+1}$ is relatively $\kappa$-compact assuming $\pi_\kappa^\alpha$ is relatively $\kappa$-compact. We may apply Lemma 3.2.7 because Diagram 28 enjoys descent as a pushout along a monomorphism, so it suffices to check that each node of Diagram 28 is relatively $\kappa$-compact. We have already assumed that $\pi_\kappa^\alpha$ is relatively $\kappa$-compact; both $\coprod_{d \in \mathsf{D}_\kappa(\pi_\kappa^\alpha)} f_d$ and $\coprod_{d \in \mathsf{D}_\kappa(\pi_\kappa^\alpha)} h_d$ are relatively $\kappa$-compact again by Lemma 3.2.7 because coproducts enjoy descent and both $f_d, h_d$ are relatively $\kappa$-compact as pullbacks of $\pi_\kappa^\alpha$. In the limit case we assume $\pi_\kappa^\beta$ relatively $\kappa$-compact for each $\beta < \alpha$, and observe that $\operatorname{colim}_{\mathcal{O}_{<\alpha}} \pi_\kappa^\bullet$ is relatively $\kappa$-compact by Lemma 3.2.7 again, since $\mathcal{O}_{<\alpha}$ is a filtered preorder and therefore its diagrams enjoy descent (Lemma 3.1.6).

4.2.6. LEMMA. *The transfinite composition $\pi_\kappa := \operatorname{colim}_{\mathcal{O}_{<\kappa}} \pi_\kappa^\bullet$ is relatively $\kappa$-compact.*

PROOF. By Lemmas 3.2.7 and 4.2.5 using the fact that transfinite compositions enjoy descent (Lemma 3.1.6).

4.3. REALIGNMENT FOR THE UNIVERSE. In Section 4.2 we have constructed a relatively $\kappa$-compact map $\pi_\kappa: E_\kappa \longrightarrow U_\kappa$ using the small object argument. We wish to show that this map exhibits $\mathcal{S}_\kappa$ as a universe satisfying (U5,8), *i.e.* $\pi_\kappa$ is generic for relatively $\kappa$-compact maps and satisfies the realignment condition. Because realignment is stronger than genericity (Lemma 1.1.7), we will focus on the former.

We recall from Notation 4.1.1 that $\mathcal{J}_{\pi_\kappa}$ denotes the largest class of monomorphisms relative to which $(\mathcal{S}, \pi_\kappa)$ supports realignment. From Lemma 3.3.12 we recall that $\mathcal{I}$ is a

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

31

set of monomorphisms generating $\mathcal{E}$ under pushout, transfinite composition, and retracts, and we have assumed that the domain of any $m \in \mathcal{I}$ is $\kappa$-compact.

4.3.1. LEMMA. Every generating monomorphism is realignable, i.e. we have $\mathcal{I} \subseteq \mathcal{J}_{\pi}$.

PROOF. Let $i: A \mapsto B$ be an element of $\mathcal{I}$; to check that $i \in \mathcal{J}_{\pi_{\kappa}}$, we fix a realignment problem in $\mathcal{S}_{\kappa}$ whose extent lies over $i: A \mapsto B$.

![img-37.jpeg](img-37.jpeg)

Because $A \mapsto B \in \mathcal{I}$, we know that $A$ is $\kappa$-compact; this is the same as to say that $\operatorname{Hom}_{\mathcal{E}}(A, -)$ commutes with $\kappa$-filtered colimits, in particular the colimit $U_{\kappa} = \operatorname{colim}_{\mathcal{O}_{<\kappa}} U_{\kappa}^{\bullet}$. Thus, using the construction of colimits in the category of sets, there exists some $\alpha$ such that $h \to \pi_{\kappa}$ factors through $\pi_{\kappa}^{\alpha} \mapsto \pi_{\kappa}$; the successor case of the small object argument adjoins realignments along generating monomorphisms, so it is appropriate to factor our realignment problem like so:

![img-38.jpeg](img-38.jpeg)

The intermediate realignment span $f \longleftrightarrow h \longrightarrow \pi_{\kappa}^{\alpha}$ can be represented by a realignment datum $d \in \mathsf{D}_{\kappa}(\pi_{\kappa}^{\alpha})$. We may therefore compose the induced injections to obtain a solution $f \longrightarrow \pi_{\kappa}$ to the realignment problem Diagram 29.

![img-39.jpeg](img-39.jpeg)

4.3.2. COROLLARY. All monomorphisms are realignable, i.e. we have $\mathcal{J}_{\pi_{\kappa}} = \mathcal{E}^{\rightarrow}$.

PROOF. We have assumed that $\mathcal{I}$ generates $\mathcal{E}^{\rightarrow}$ under pushout, transfinite composition, and retracts; but $\mathcal{J}_{\pi_{\kappa}}$ is saturated (Section 4.1), so our result follows from the fact that generating monomorphisms are realignable (Lemma 4.3.1).

32

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

4.3.3. COROLLARY. $S_\kappa$ is a universe satisfying (U1-8).

4.4. A CUMULATIVE UNIVERSE HIERARCHY. Fix a second strongly inaccessible cardinal $\mu > \kappa$. We obtain a generic map $\pi_\mu$ for $S_\mu$ satisfying (U8) by the same small object argument detailed in Section 4.2.

Genericity of $\pi_\mu$ implies that we automatically obtain a cartesian morphism $\pi_\kappa \longrightarrow \pi_\mu$ but this map is not generally a monomorphism. On the other hand, we can choose our own cartesian monomorphism $\pi_\kappa \longmapsto \pi_\mu$ by means of a pointwise construction.

4.4.1. LEMMA. There exists a cartesian monomorphism $\pi_\kappa \longmapsto \pi_\mu$.

PROOF. We recall that each $\pi_\lambda$ is $\operatorname{colim}_{\mathcal{O}_{<\kappa}} \pi_\lambda^\bullet$. Because filtered colimits enjoy descent, by Lemma 3.1.10 to construct a cartesian monomorphism $\operatorname{colim}_{\mathcal{O}_{<\kappa}} \pi_\kappa^\bullet \longmapsto \operatorname{colim}_{\mathcal{O}_{<\kappa}} \pi_\mu^\bullet$, it suffices to define a cartesian monomorphism of diagrams $\ell: \pi_\kappa^\bullet \longmapsto \pi_\mu^\bullet$:

![img-40.jpeg](img-40.jpeg)

We construct our natural transformation $\pi_\kappa^\bullet \longmapsto \pi_\mu^\bullet$ step-wise; the only interesting case is to define $\pi_\kappa^{\alpha+1} \longmapsto \pi_\mu^{\alpha+1}$ given $\pi_\kappa^\alpha \longmapsto \pi_\mu^\alpha$. By Lemma 3.1.10 it suffices to define a cartesian monomorphism between the defining spans of $\pi_\kappa^{\alpha+1}, \pi_\mu^{\alpha+1}$, since they are pushouts along monomorphisms and hence enjoy descent in $\mathcal{E}^\to$. Such a morphism is trivially induced by the embedding that sends a realignment span $f \longleftarrow h \longrightarrow \pi_\kappa^\alpha$ to $f \longleftarrow h \longrightarrow \pi_\kappa^{\alpha+1}$ by postcomposition with $\pi_\kappa^\alpha \longmapsto \pi_\kappa^{\alpha+1}$.

4.4.2. LEMMA. $U_\kappa$ is $\mu$-compact.

PROOF. We argue that $U_\kappa$ is $\mu$-compact by showing that it is the $\mu$-small colimit of $\mu$-small objects. Recall that $U_\kappa = \operatorname{colim}_{\mathcal{O}_{<\kappa}} U_\kappa^\bullet$, so it suffices to argue that $U_\kappa^\alpha$ is $\mu$-compact for each $\alpha < \kappa$.

We show this by transfinite induction on $\alpha < \kappa$. The limit case is immediate: $U_\kappa^\alpha$ is then a $\mu$-small colimit of $\mu$-compact objects. Fix $\alpha < \kappa$ and assume that $U_\kappa^\alpha$ is $\mu$-small. $U_\kappa^{\alpha+1}$ is defined as the following pushout:

![img-41.jpeg](img-41.jpeg)

By Lemmas 3.3.12 and 4.2.3 together with our assumption that $U_\kappa^\alpha$ is $\mu$-compact, this is a $\mu$-small colimit of $\mu$-compact objects so $U_\kappa^{\alpha+1}$ is $\mu$-compact.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

33

Given a poset $(I, \leq)$ and conservative functor $\lambda \colon I \to {}^{\kappa/}\mathbf{Card}$ of strongly inaccessible cardinals, these results extend to a hierarchy of universes indexed in $I$:

4.4.3. COROLLARY. *Each universe $S_{\lambda_i}$ satisfies (U1–8) and for each $i < j$, there is a cartesian monomorphism $\pi_{\lambda_i} \hookrightarrow \pi_{\lambda_j}$ and $\operatorname{cod}(\pi_{\lambda_i})$ is $\lambda_j$-compact.*

## 5. Relating internal formulations of realignment

We have focused on the external formulation of realignment as a property of a class of maps; recent years have seen several applications of type-theoretic formulation of realignment that employs the internal language of a topos. In Section 5.1 we discuss a logical formulation popularized by Orton and Pitts, which we compare with a more geometrical formulation due to Sterling in Section 5.2 that mirrors the recollement of a space from open and closed subspaces, completing the latent analogy with Artin gluing.

5.1. INTERNAL REALIGNMENT À LA ORTON AND PITTS. In another guise, Cohen, Coquand, Huber, and Mörtberg [Coh+17] has employed the realignment property in the cubical set model of cubical type theory, later rephrased into the internal language of topoi by Birkedal, Bizjak, Clouston, Grathwohl, Spitters, and Vezzosi [Bir+16] and employed by Orton and Pitts [OP16] to give more abstract and general constructions of models of cubical type theory in presheaf topoi.

In what follows, we fix a universe $\mathcal{S}$ satisfying (U1–5) such that, in particular, there is a generic map $\pi \colon E \to U$ for $\mathcal{S}$. We recall the internal version of the realignment axiom for $U$ below as presented by Orton and Pitts [OP16, Axiom 9 $(\mathsf{ax}_9)$], using informal type theoretic notations.

5.1.1. NOTATION. For any $B : U$, an *isomorph* of $B$ is defined to be a type $A : U$ together with an isomorphism $f : A \cong B$. We will write $\operatorname{Iso}_{\mathcal{S}}(B) := \sum_{A:U} A \cong B$ for the type of isomorphs of $B$, and $\operatorname{Iso}_{\mathcal{S}} := \sum_{B:U} \operatorname{Iso}_{\mathcal{S}}(B)$ for the object of isomorphisms.

5.1.2. NOTATION. We will write $X^+$ for the partial map classifier $\sum_{\phi: \Omega} X^\phi$, and $\eta^+ : X \to X^+$ for its unit.

5.1.3. DEFINITION. *A realignment structure is defined to be an element of the dependent type $\prod_{B:U} \prod_{A: \operatorname{Iso}_{\mathcal{S}}(B)^+} \{G : \operatorname{Iso}_{\mathcal{S}}(B) \mid A \downarrow \to A = \eta^+(G)\}$. The realignment axiom on $U$ postulates the existence of a realignment structure.*

Combining the application described in Section 6.3 with the internal perspective of Orton and Pitts [OP16], the realignment operation is included as an axiom of *synthetic Tait computability* [Ste21], the mathematical framework behind the recent normalization result for cubical type theory [SA21].

We demonstrate in Lemmas 5.1.5 and 5.1.6 that the existence of realignment structures in the sense of Definition 5.1.3 is equivalent to the realignment property of Definition 1.1.4.

34

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

5.1.4. NOTATION. We will write $\mathsf{Iso}_S^* : \mathcal{E}_{/\mathsf{Iso}_S}$ for the dependent type $I : \mathsf{Iso}_S \vdash \pi_1(I)$ of pointed isomorphisms. We define the type $\mathsf{Desc}_S$ of $S$-realignment data to be the dependent sum $\sum_{B:U} \mathsf{Iso}_S(B)^+$. We will write $\mathsf{Desc}_S^* : \mathcal{E}_{/\mathsf{Desc}_S}$ for the dependent type $D : \mathsf{Desc}_S \vdash \pi_1(D)$ of pointed realignment data.

5.1.5. LEMMA. Let $S$ be a universe satisfying (U8) for the class of all monomorphisms; then $S$ has a realignment structure.

PROOF. We have a cartesian monomorphism $\mathsf{Iso}_S^* \hookrightarrow \mathsf{Desc}_S^*$ that turns an isomorphism into the corresponding total realignment datum with $\phi := \top$. Taking the domain of an isomorphism corresponds to a cartesian map $\mathsf{Iso}_S^* \to \pi$. Combining these, we may rephrase Definition 5.1.3 as the existence of a cartesian morphism $\mathsf{Desc}_S^* \to \pi$ in the following configuration:

![img-42.jpeg](img-42.jpeg)

The dotted map of Diagram 32 exists by the realignment axiom because $\mathsf{Desc}_S^* \in S$. ■

5.1.6. LEMMA. Suppose that $S$ has a realignment structure; then $S$ satisfies (U8) for the class of all monomorphisms.

PROOF. We transform external realignment problems into internal ones. Fix a span of cartesian maps as below such that $f \in S$:

![img-43.jpeg](img-43.jpeg)

Because $f \in S$, we additionally have:

![img-44.jpeg](img-44.jpeg)

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

35

We take the characteristic map of \(\Phi\):

\[
\begin{array}{c} \Phi \longrightarrow \mathbf {1} _ {\varepsilon} \\ p _ {\phi} \Biggl \downarrow \quad \Biggl \downarrow \quad \Biggl \downarrow \quad \Biggl \downarrow \quad \Biggl \downarrow \quad \Biggl \uparrow \\ \Gamma \xrightarrow [ \phi ]{} \Omega \end{array} \tag {35}
\]

We have a map \(\Phi \longrightarrow \mathsf{Iso}_S(B \circ p_\phi)\) determined by \(A\), which we observe forms the base of a cartesian map \(h \longrightarrow \mathsf{Iso}_S^*\). On the other hand, we have a map \(\Gamma \longrightarrow \mathsf{Iso}_S(B)^+\), i.e. a partial isomorphism with support \(\phi\) between \(A\) and \(B \circ p_\phi\). Therefore we have a realignment datum \(\Gamma \longrightarrow \mathsf{Desc}_S\) determined by \(B\) and our partial isomorphism; in fact, this is the base of a cartesian map \(f \longrightarrow \mathsf{Desc}_S^*\) which we may compose with the realignment structure to obtain the desired factorization:

![img-45.jpeg](img-45.jpeg)

In short, we solved the realignment problem by restricting from the generic case.

5.2. REALIGNMENT AND RECOLLEMENT. Sterling has recently advanced an alternative [SH22] to the internal characterization of Orton and Pitts (Section 5.1) based on the recollement of a sheaf from its components over complementary open and closed subspaces. We recall the basics of the theory from SGA 4 [AGV72].

When \(\mathcal{X}\) is a topos, a subterminal object \(J\mapsto\mathbf{1}_{\mathcal{X}}\) corresponds to an open subtopos \(\mathcal{X}_{/J}\) such that the open inclusion geometric morphism \(j_{*}:\mathcal{X}_{/J}\hookrightarrow\mathcal{X}\) is the right adjoint to the pullback functor \(j^{*}:\mathcal{X}\longrightarrow\mathcal{X}_{/J}\) that sends \(E\) to \(E\times J\longrightarrow J\). Meanwhile we may form the complementary closed subtopos \(\mathcal{X}_{\star U}=\mathcal{X}\setminus\mathcal{X}_{/J}\) by considering the subcategory of \(\mathcal{X}\) spanned by objects \(E\) for which the canonical map \(E\times J\longrightarrow J\) is an isomorphism. The closed inclusion \(i_{*}:\mathcal{X}_{\star J}\hookrightarrow\mathcal{X}\) then has a left exact left adjoint \(i^{*}:\mathcal{X}\longrightarrow\mathcal{X}_{\star J}\) taking \(E\) to the join \(E\star J\), i.e. the following pushout:

![img-46.jpeg](img-46.jpeg)

36

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The Grothendieck school then develops both a *global* and a *local* recollement theory for the open-closed partition $(\mathcal{X}_{/J}, \mathcal{X}_{*J})$ of $\mathcal{X}$:

5.2.1. GLOBAL RECOLLEMENT [AGV72]. The topos $\mathcal{X}$ may be reconstructed from its open and closed subtopoi as the comma category $\mathcal{X}_{*J} \downarrow i^* j_*$, i.e. the Artin gluing of $i^* j_*$. In other words, the diagram below is pseudocartesian in the (very large) bicategory of all categories, in which the upper functor $q: \mathcal{X} \longrightarrow \mathcal{X}_{*J}$ sends an object $E$ to the morphism $i^*(\eta_E: E \longrightarrow j_* j^* E)$ in $\mathcal{X}_{*J}$.

$$\begin{array}{ccc} \mathcal{X} & \xrightarrow{q} & \mathcal{X}_{*J} \\ j^* & \downarrow & \downarrow \text{cod}_{\mathcal{X}_{*J}} \\ \mathcal{X}_{/J} & \xrightarrow{i^* j_*} & \mathcal{X}_{*J} \end{array} \blacksquare$$

From the global recollement of the topos $\mathcal{X}$ from its open and closed subtopoi, the Grothendieck school concludes a *local* recollement or *fracture theorem* that reconstructs an object of the topos from its components over the open and closed subtopoi.³

5.2.2. LOCAL RECOLLEMENT [AGV72]. Under the same assumptions, any object $E$ of $\mathcal{X}$ may be reconstructed from its restrictions $j^* E, i^* E$ to the open and closed subtopoi respectively. In particular, the following diagram is cartesian in $\mathcal{X}$:

$$\begin{array}{ccc} E & \xrightarrow{\eta_E} & i_* i^* E \\ \eta_E & \downarrow & \downarrow i_* i^* \eta_E = i_* q E \\ j_* j^* E & \xrightarrow{\eta_{j_* j^* E}} & i_* i^* j_* j^* E \end{array} \blacksquare$$

The above follows immediately from the global recollement (Section 5.2.1); conversely, if $O: \mathcal{X}_{/J}$ is an object of the open subtopos and $p: K \longrightarrow i^* O: \mathcal{X}_{*J}$ is a family of objects in the closed subtopos, then the pullback of the latter along $O \longrightarrow i_* j^* O$ in $\mathcal{X}$ is a morphism $E \longrightarrow j_* O$ that is *isomorphic* to the unit $E \longrightarrow j_* j^* E$:

$$\begin{array}{ccc} E & \longrightarrow & i_* K \\ \downarrow & \downarrow & \downarrow i_* p \\ j_* j^* E & \eta_{j_* O}^*(i_* p) & \downarrow \\ \downarrow & \downarrow & \downarrow i_* i^* j_* O \\ j_* O & \xrightarrow{\eta_{j_* O}} & \end{array} \tag{37}$$

³Such a fracture theorem is developed in much greater generality for left exact modalities by Rijke, Shulman, and Spitters [RSS20].

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

37

5.2.3. QUESTION. Can $E$ be chosen in Diagram 37 to make the isomorphism $j_*j^*E \rightarrow j_*O$ an *identity* map?

Although identity of objects is not properly part of the language of category theory, it becomes meaningful when considering *internal categories* as we do in Section 5.2.4 below. We will see that the realignment axiom (U8) for a full internal subtopos corresponds to the ability to construct a version of Diagram 37 in which $j_*j^*E = j^*O$ strictly.

5.2.4. INTERNAL RECOLLEMENT. Let $\mathcal{U}$ be a universe in $\mathcal{X}$ and let $p: E \rightarrow U$ be a generic family for $\mathcal{U}$; then $U$ constitutes a *full internal subtopos* of $\mathcal{X}$ in the sense of Bénabou [Bén73]. Consequently we may think of $\mathcal{U}$ as a topos $C^*U$ in every slice $\mathcal{X}_{/C}$ of $\mathcal{X}$; hence any monomorphism $J \rightarrow C$ in $\mathcal{X}$ corresponds to a subterminal object in $\mathcal{X}_{/C}$, *i.e.* an open subtopos of $C^*U$. Therefore we may replay the global and local recollement for each $C^*U$ using the same constructions.

Letting $J: \Omega$ be a proposition in $\mathcal{X}$, we note that the exponential family $E^J \rightarrow U^J$ is generic for the *open* subtopos of $U$ determined by the proposition $J$. We will write $J_*: U^J \rightarrow U$ for the function that sends a family $O: U^J$ to its dependent product $\prod_{z:J} Oz$; the left adjoint $J^*: U \rightarrow U^J$ takes a type $A$ to the constant family $\lambda_*: J.A$. Likewise we may obtain a generic family for the *closed* subtopos by considering the subobject $U_{\star J} \subseteq U$ spanned by types $A$ such that $p[A] \times J \rightarrow J$ is an isomorphism; following Rijke, Shulman, and Spitters [RSS20], we will refer to such types as $J$-connected.

We may now revisit our Question 5.2.3 concerning Diagram 37 in the internal language. Let $O: U^J$ be an object of the open subtopos and let $K: J_*O \rightarrow U_{\star J}$ be a family of $J$-connected objects. Then an affirmative answer to Question 5.2.3 would produce some $E: U$ together with an isomorphism $f_E: (\sum_{x:J_*O} Kx) \rightarrow E$ in $U$ such that $j^*E = O$ strictly and $j^*f_E$ is strictly equal to $\lambda z: J.\lambda(x,y).xz$. In other words, we are asking for a type constructor Glue on $U$ with the following interface:

$$\text{Glue}: \prod_{J:\Omega} \prod_{O:U^J} \prod_{K:J_*O \rightarrow U_{\star J}} \{G: U \mid \forall z: J.G = Oz\}$$

$$\text{glue}: \prod_{J:\Omega} \prod_{O:U^J} \prod_{K:J_*O \rightarrow U_{\star J}} \{f: (\sum_{x:J_*O} Kx) \cong \text{Glue } O K \mid \forall z: J.\forall x,y.f(x,y) = xz\}$$

It is not difficult to verify that the existence of such a type constructor is equivalent to the internal realignment axiom discussed in Section 5.1.

5.2.5. LEMMA. *Let $G$ be a realignment structure for $U$ in the sense of Definition 5.1.3; then there exists a Glue connective satisfying the described rules.*

PROOF. Let $O, K$ as above and consider the application of $G$ to $B := \sum_{x:J_*O} Kx$ and the partial isomorphism $z: J \vdash B \cong Oz$, which exists because each fiber of $K$ is $J$-connected. From this pair we thus obtain both Glue $JOK$ and glue $JOK$. ■

5.2.6. LEMMA. *Conversely, suppose that we have a Glue connective in the sense described above; then there exists a realignment structure in the sense of Definition 5.1.3.*

PROOF. Given a type $B$ and a partial isomorph $(J, A): \text{Iso}_\mathcal{U}(B)^+$, we let $O := \lambda z: J.\pi_1(Az)$ and $K := \lambda x: J_*O.\{y: B \mid \forall z: J.(\pi_2(Az))(xz) = y\}$. Then we consider the total isomorph given by the pair $(\text{Glue } JOK, \pi_2 \circ (\text{glue } JOK)^{-1})$. ■

38

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The benefit of the present axiomatization is that a family of types being fiberwise $J$-connected is a *property*; in contrast, the Orton–Pitts axiomatization (Definition 5.1.3) requires every use of realignment to be accompanied by a chosen isomorphism. We have gained significant experience with both axiomatizations in the context of synthetic Tait computability [Gra22; Niu+22; Ste21; SA21; SH21; SH22], and found that the present one is substantially simpler to use in practice.

## 6. Applications of realignment

An immediate consequence of Section 4 is an interpretation of Martin-Löf type theory with a cumulative hierarchy of universes in arbitrary Grothendieck topoi (recall that we have assumed a hierarchy of Grothendieck universes). In fact, the new interpretation of Martin-Löf type theory in Grothendieck topoi enables more direct independence proofs for various axioms such as Markov's principle. But the realignment property itself has played an important role in the semantics of homotopy type theory as developed by Awodey [Awo21], Kapulkin, Lumsdaine, and Voevodsky [KL21], Shulman [Shu15; Shu19], Stenzel [Ste19], and Streicher [Str14]. In particular, realignment appears to be a necessary ingredient for constructing a fibrant and univalent universe. The same principle is employed by Sterling, Angiuli, and Gratzer [SAG22, Lemma 5.33] in their proof of *canonicity* for XTT, a variant of cubical type theory: in particular, *op. cit.* used a special case of (U8) to realign codes in the universe of an Artin gluing over chosen codes in the universe of its open subtopos.

### 6.1. INDEPENDENCE RESULTS FOR MARTIN-LÖF TYPE THEORY.

Sheaf semantics has historically been employed to prove independence results for various forms of logic; the use of sheaf semantics to verify the analogous results for dependent type theory with universes has been hampered by the (now-resolved) difficulties in constructing well-behaved universes in sheaf topoi. These difficulties have motivated two somewhat less direct methods for proving independence results: constructing *operational* or *relational* models of type theory using the Beth–Kripke–Joyal sheaf semantics of predicate logic [CM16], or by constructing denotational models of type theory in *stacks* rather than sheaves [CMR17]. The present work provides a more direct approach, as the presence of universes validating (U1–8) ensures a simple and direct denotational semantics of dependent type theory in sheaves. We illustrate this through a concrete example and sketch a simpler proof of the independence of Markov's principle.

#### 6.1.1. INDEPENDENCE OF MARKOV'S PRINCIPLE.

Markov's principle states that for any decidable property $P(x)$ of natural numbers, the proposition $\exists x.Px$ is $\neg\neg$-stable:

$$\forall P : \mathbb{N} \rightarrow \mathbf{2}.\neg\neg\exists x.Px = 0 \rightarrow \exists x.Px = 0$$

Formalized in the language of dependent type theory, Markov's principle is rendered by Coquand and Manna [CM16] equivalently as the existence of a global element of the following type:

$$\prod_{P:\mathbb{N}\rightarrow\mathbf{2}} (\neg\neg\sum_{x:\mathbb{N}} Px = 0 \rightarrow \sum_{x:\mathbb{N}} Px = 0)$$

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

39

The independence of Markov's principle from intuitionistic higher-order logic is established easily by considering the internal logic of the topos of sheaves on Cantor space $\mathcal{C}$, *i.e.* the space of infinite binary sequences equipped with the product topology. If $\mathrm{Sh}(\mathcal{C})$ did not model universes, we would not however be able to use it directly to verify the independence of Markov's principle from Martin-Löf type theory with universes. Our result concerning universes in Grothendieck topoi, however, allows one to immediately deduce the independence of Markov's principle from Martin-Löf type theory with universes without needing to pass to the significantly more complex stack semantics of Coquand, Mannaa, and Ruch [CMR17], bypassing as well the detour through operational semantics of Coquand and Mannaa [CM16].

6.1.2. COROLLARY. *Neither Markov's principle nor its negation is derivable in Martin-Löf type theory with a cumulative hierarchy of strict universes.*

6.2. SEMANTICS OF THE UNIVALENT UNIVERSES. The semantics of univalent universes has proved to be a crucial technical difficulty in models of homotopy type theory and cubical type theory; in particular, it is necessary to translate facts between the language of model category theory and the language of universes. We briefly illustrate how judicious application of (U8) has been used in the literature to entirely eliminate these difficulties [Awo21; KL21; Shu15; Shu19; Str14]. In fact, this observation was the original motivation for Shulman [Shu15] to isolate (U8).

We illustrate the utility of (U8) by tracing through the salient aspects of the model given by Kapulkin, Lumsdaine, and Voevodsky [KL21] and defer to Shulman [Shu15; Shu19] for a more systematic approach. Concretely, we will work in **sSet** and fix a pair of strongly inaccessible cardinals $\kappa_0 < \kappa_1$ inducing universes $\mathcal{V}_0 \subseteq \mathcal{V}_1$ each satisfying (U1–8). Moreover, by Section 4.4, we can choose a generic map for $\mathcal{V}_0$ whose base lies in $\mathcal{V}_1$.

Let $\mathcal{U}_i \subseteq \mathcal{V}_i$ be the class of Kan fibrations in $\mathcal{V}_i$.

6.2.1. LEMMA. *The class of maps $\mathcal{U}_i$ satisfies (U1,3,4,8).*

PROOF. (U1,3) follow immediately from the fact that $\mathcal{V}_i$ satisfies (U1,3) and that any right-orthogonal class is closed under composition and pullback. (U4) is an immediate consequence of the right-properness of the Kan-Quillen model structure.

To show that $\mathcal{U}_i$ satisfies (U8), we being by fixing a generic family $\pi_{\mathcal{V}_i} \colon E_{\mathcal{V}_i} \longrightarrow U_{\mathcal{V}_i}$ for $\mathcal{V}_i$ and defining the following restriction of $U_{\mathcal{V}_i}$:

$$U_{\mathcal{U}_i} = \{X : U_{\mathcal{V}_i} \mid X \text{ is a Kan complex}\}$$

More precisely, a point $\alpha \colon \Delta^n \longrightarrow U_{\mathcal{V}_i}$ factors through $U_{\mathcal{U}_i}$ if $\pi^*(\alpha)$ is a Kan fibration. This is a well-defined simplicial set because Kan fibrations are stable under pullback. We define $\pi_{\mathcal{U}_i}$ (resp. $E_{\mathcal{U}_i}$) as the restriction of $\pi_{\mathcal{V}_i}$ (resp. $E_{\mathcal{V}_i}$) to $U_{\mathcal{U}_i}$. We first prove that $\pi_{\mathcal{U}_i} \in \mathcal{U}_i$, and then verify (U8).

40

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

By (U1) we conclude that $\pi_{\mathcal{U}_i}$ lies in $\mathcal{V}_i$, and it is moreover a Kan fibration almost by definition. Fix a commutative diagram of the following shape:

$$\begin{array}{ccc} \Lambda_i^n & \longrightarrow & E_{\mathcal{U}_i} \\ \updownarrow & & \updownarrow \\ \Delta^n & \xrightarrow[\alpha]{} & U_{\mathcal{U}_i} \end{array}$$

By definition of $\pi_{\mathcal{U}_i}$, pulling back along $\alpha$ yields a Kan fibration, whereby we obtain the necessary lift:

$$\begin{array}{ccc} \Lambda_i^n & \dashrightarrow & E_{\mathcal{U}_i} \\ \updownarrow & & \updownarrow \\ \Delta^n & \xrightarrow{\quad} & \Delta^n \end{array} \xrightarrow{\quad} \begin{array}{c} E_{\mathcal{U}_i} \\ \updownarrow \\ \downarrow \\ U_{\mathcal{U}_i} \end{array}$$

Consequently, $\pi_{\mathcal{U}_i} \in \mathcal{U}_i$. It remains to show that $\pi_{\mathcal{U}_i}$ satisfies (U8). Accordingly, fix a pair of cartesian squares $\alpha: f \longrightarrow \pi_{\mathcal{U}_i}$ and $i: f \longmapsto g$. We apply (U8) for $\mathcal{V}_i$ to obtain a cartesian square $\beta: g \longrightarrow \pi_{\mathcal{V}_i}$ fitting into the following commutative diagram:

$$\begin{array}{ccc} f & \xrightarrow{\alpha} & \pi_{\mathcal{U}_0} \longmapsto \pi_{\mathcal{V}_0} \\ \updownarrow & & \updownarrow \\ g & & \beta \end{array}$$

To complete the proof, it suffices to show that $\beta$ factors through $\pi_{\mathcal{U}_i}$ i.e. that for any cartesian square $h \longrightarrow g$ such that $h$ has a representable base, $h$ is a Kan fibration. This, however, follows immediately because $g$ is a Kan fibration. ■

We recall a purely homotopy-theoretic fact, referred to by Awodey [Awo21] as the fibration extension property.

6.2.2. LEMMA. Given a Kan fibration $f: X \longrightarrow A$ and a trivial cofibration $i: A \longmapsto B$, there is a Kan fibration $g: Y \longrightarrow B$ such that $i^*g = f$. Additionally, if $f \in \mathcal{V}_i$ then $g \in \mathcal{V}_i$.

This result is proved by Kapulkin, Lumsdaine, and Voevodsky [KL21] using Quillen's theory of minimal fibrations. An alternative approach is given by Lurie [Lur22, Tag 00ZS] using Kan's $\mathsf{Ex}_\infty$ functor. A near immediate consequence of Lemma 6.2.2 and (U8) is the fibrancy of the $U_{\mathcal{U}_0}$:

6.2.3. THEOREM. The object $U_{\mathcal{U}_0}$ lies within $\mathcal{U}_1$.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

41

PROOF. As a subobject of $\mathcal{V}_0$, (U2) implies that $U_{\mathcal{U}_0}$ lies within $\mathcal{V}_1$, so it suffices to show that $U_{\mathcal{U}_0}$ is a Kan complex. Accordingly, we fix a lifting problem for $U_{\mathcal{U}_0}$:

$$\begin{array}{c} \Lambda_i^n \xrightarrow{\alpha} U_{\mathcal{U}_0} \\ \Big\downarrow \\ \Delta^n \end{array}$$

We must extend $\alpha$ along the inclusion $\Lambda_i^n \to \Delta^n$. We begin by pulling back $\pi_{\mathcal{U}_0}$ along $\alpha$, obtaining a Kan fibration $[\alpha] \to \Lambda_i^n$ and a cartesian map $h: [\alpha] \to \pi_{\mathcal{U}_0}$. Applying Lemma 6.2.2, we can extend $[\alpha]$ along $\Lambda_i^n \to \Delta^n$ to another Kan fibration $[\beta] \to \Delta^n$. Next, we apply (U8) to extend $h$ along the induced cartesian monomorphism $[\alpha] \to [\beta]$:

$$\begin{array}{c} [\alpha] \xrightarrow{h} \pi_{\mathcal{U}_0} \\ \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{[}\beta\text{]} \end{array}$$

The downstairs component of $\beta: [\beta] \to \pi_{\mathcal{U}_0}$ then solves the original lifting problem. ■

Notice that in the above proof, the application of (U8) allows us to rephrase a property of the generic family (“$U_{\mathcal{U}_0}$ is a Kan complex”) as a property of the class of maps $\mathcal{U}_0$ (“Kan fibrations extend along trivial cofibrations”) to which the standard tools of homotopy theory apply. While the setup is more complex, the same is true of the proof that $\pi_{\mathcal{U}_0}$ is univalent. Prior to discussing the proof of univalence, we must fix a few definitions.

6.2.4. DEFINITION. Given Kan fibrations $E_0, E_1 \to B$, we define $\mathsf{Equiv}(E_0, E_1) \to B$ to be the fibration of weak equivalences between $E_0$ and $E_1$, i.e. the subobject of the local exponential $E_1^{E_0} \to B$ spanned by weak equivalences.

Explicitly, a simplex $\alpha: \Delta^n \to E_1^{E_0}$ factors through $\mathsf{Equiv}(E_0, E_1)$ if the corresponding morphism $\alpha^* E_0 \to \alpha^* E_1$ over $\Delta^n$ is a weak equivalence. In fact, a map $X \to \mathsf{Equiv}(E_0, E_1)$ is determined by a pair of maps $f_i: X \to B$ along with a weak equivalence $f_0^* E_0 \to f_1^* E_1$ over $X$.

We have avoided a number of subtle points in this definition e.g., that weak equivalences between fibrations are stable under pullback to show that it is well-defined. These are addressed thoroughly by Kapulkin, Lumsdaine, and Voevodsky [KL21]. See Shulman [Shu15] for a less analytic definition of the object of equivalences.

Given a Kan fibration $X \to B$, we define $\langle \partial_0, \partial_1 \rangle: \mathsf{Eq}(X) \to B \times B$ to be $\mathsf{Equiv}(\pi_1^* X, \pi_2^* X)$, i.e. the object of equivalences between two specified fibers of $X$. We observe that there is a canonical monomorphism $\delta_X: B \mapsto \mathsf{Eq}(X)$ lying over the diagonal map $B \mapsto B \times B$

42

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

sending $b : B$ to the identity equivalence $X[b] \to X[b]$:

$$\begin{array}{c} B \xrightarrow{\delta_X} \mathsf{Eq}(X) \\ \Bigg\downarrow \quad \Bigg\downarrow \langle \partial_0, \partial_1 \rangle \\ B \xrightarrow[\delta]{} B \times B \end{array}$$

6.2.5. DEFINITION. A Kan fibration $X \to B$ is called univalent when $\delta_X : B \to \mathsf{Eq}(X)$ is a trivial cofibration.

We will now sketch the proof that $\pi_{\mathcal{U}_0}$ is univalent. Just as with Theorem 6.2.3, the proof decomposes into two pieces: a homotopy-theoretic result and a careful analysis and application of (U8) to parlay this result into the appropriate result on the universe. For univalence, the relevant homotopy-theoretic fact is the equivalence extension property, apparently first isolated by Kapulkin, Lumsdaine, and Voevodsky [KL21], named by Awodey, and further developed by several authors including Awodey, Coquand, Sattler, and Shulman [Awo21; Coh+17; Sat17; Shu15; Shu19].

6.2.6. LEMMA (EQUIVALENCE EXTENSION PROPERTY). We consider a diagram of the following shape, in which the downward maps are Kan fibrations, $i : A \to B$ is a cofibration, and $w : X \to i^*Y$ is a weak equivalence:

$$\begin{array}{c} X \xrightarrow{w} i^*Y \xrightarrow{} Y \\ A \xrightarrow{i} B \end{array} \tag{38}$$

Then Diagram 38 can be extended to a diagram of the following shape, in which $\bar{w} : \bar{X} \to Y$ is a weak equivalence and $\bar{X} \to B$ is a fibration, and all three squares are cartesian:

$$\begin{array}{c} X \xrightarrow{w} i^*Y \xrightarrow{} \bar{X} \xrightarrow{\bar{w}} Y \\ A \xrightarrow{i} B \end{array}$$

Moreover, if $X \to A$ and $Y \to B$ both belong to $\mathcal{U}_0$, so does $\bar{X} \to B$.

6.2.7. THEOREM. The family $\pi_{\mathcal{U}_0} : E_{\mathcal{U}_0} \to U_{\mathcal{U}_0}$ is univalent.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

43

PROOF. Unfolding definitions, we must show that $\delta_{E_{\mathcal{U}_0}} : U_{\mathcal{U}_0} \longrightarrow \mathsf{Eq}(E_{\mathcal{U}_0})$ is a trivial cofibration; as it is already a cofibration, it is enough to check that it is a weak equivalence. Consider Diagram 39 below exhibiting $\delta_{E_{\mathcal{U}_0}}$ as a section of the fibration $\partial_1 : \mathsf{Eq}(E_{\mathcal{U}_0}) \longrightarrow U_{\mathcal{U}_0}$:

$$\begin{array}{c} U_{\mathcal{U}_0} \xrightarrow{\delta_{E_{\mathcal{U}_0}}} \mathsf{Eq}(E_{\mathcal{U}_0}) \\ \Biggl\downarrow \quad \Biggl\downarrow \partial_1 \\ U_{\mathcal{U}_0} \end{array} \tag{39}$$

By the 2-out-of-3 property of weak equivalances, it therefore suffices to show that fibration $\partial_1 : \mathsf{Eq}(E_{\mathcal{U}_0}) \longrightarrow U_{\mathcal{U}_0}$ is a trivial fibration. To this end we fix a cofibration $A \longmapsto B$ to check the right lifting property for $\partial_1$:

$$\begin{array}{c} A \xrightarrow{(\beta, \alpha, w)} \mathsf{Eq}(E_{\mathcal{U}_0}) \\ \Biggl\downarrow \quad \Biggl\downarrow \partial_1 \\ B \xrightarrow{\bar{\alpha}} U_{\mathcal{U}_0} \end{array} \tag{40}$$

In Diagram 40 above, we have written $\beta, \alpha$ for the two codes $A \longrightarrow U_{\mathcal{U}_0}$ and $w : [\beta] \longrightarrow [\alpha]$ for the weak equivalence between the corresponding fibers of $\pi_{\mathcal{U}_0}$, writing $[\alpha]$ for the pullback of $\pi_{\mathcal{U}_0}$ along $\alpha$, etc.; then $\bar{\alpha}$ is an extension of the code $\alpha$ along the cofibration $A \longmapsto B$. Our goal is to provide similar extensions of $\beta, w$ to produce an equivalence between $B$-valued fibers of $\pi_{\mathcal{U}_0}$. Considering the fiber of $\pi_{\mathcal{U}_0}$ at $\bar{\alpha}$, we have a Kan fibration $[\bar{\alpha}] \longrightarrow B$ whose pullback along $A \longmapsto B$ is $[\alpha] \longrightarrow A$. We summarize the situation as follows:

$$\begin{array}{c} [\beta] \\ \searrow w \\ \searrow [\alpha] \\ \searrow g \\ \searrow \\ A \longmapsto B \end{array} \longrightarrow \begin{array}{c} [\bar{\alpha}] \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \seend{array} \tag{41}$$

Using Lemma 6.2.6, we can complete Diagram 41 as follows:

$$\begin{array}{c} [\beta] \xrightarrow{f} [\bar{\beta}] \\ \searrow w \\ \searrow [\alpha] \\ \searrow g \\ \searrow \\ A \longmapsto B \end{array} \longrightarrow \begin{array}{c} [\bar{\beta}] \\ \searrow \\ \bar{w} \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \end{array} \tag{42}$$

44

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

By (U8) we solve the following realignment problem to obtain an extension of the code $\beta: A \longrightarrow U_{\mathcal{U}_0}$ along $A \longmapsto B$, using the fact that $[\bar{\beta}]$ lies in $\mathcal{U}_0$ by assumption:

$$\begin{array}{c} [\beta] \xrightarrow{\beta} \pi_{\mathcal{U}_0} \\ f \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \tag{43}$$

The indicated lift of Diagram 43 then supplies in conjunction with the weak equivalence $\bar{w}: [\bar{\beta}] \longrightarrow [\bar{\alpha}]$ the required lift for Diagram 40:

$$\begin{array}{c} A \xrightarrow{(\beta, \alpha, w)} \mathsf{Eq}(E_{\mathcal{U}_0}) \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \begin{array}{c} \downarrow \\ B \xrightarrow{(\bar{\beta}, \bar{\alpha}, \bar{w})} \\ \downarrow \\ \bar{\alpha} \end{array} \begin{array}{c} \downarrow \\ \downarrow \\ U_{\mathcal{U}_0} \end{array} \partial_1$$

Therefore $\partial_1$ is a trivial fibration and thus $\pi_{\mathcal{U}_0}$ is univalent.

6.3. ARTIN GLUING AND SYNTHETIC TAIT COMPUTABILITY. Artin gluing is used by computer scientists to prove metatheorems for type theories and programming languages such as normalization, canonicity, decidability, parametricity, conservativity, and computational adequacy. Sterling and Harper [SH21] have introduced synthetic Tait computability as an abstraction for working in the internal language of glued topoi, taking the realignment law (U8) in its internal form (see Section 5) as a basic axiom.

6.3.1. HISTORY AND MOTIVATION. Synthetic Tait computability (or STC) was first employed in op. cit. to prove a generalized abstraction/parametricity theorem for a language of software packages (“modules”) in the style of Standard ML; subsequently, Sterling and Angiuli [SA21] used STC to positively resolve the long-standing normalization conjecture for cubical type theory [Ang+21].⁴ Building on these results, Gratzer [Gra22] adapted STC to verify the analogous conjecture for multimodal type theory [Gra+20]. In their original formulation, all of these results relied heavily on (U8), but the glued topoi in the cited results were all of presheaf type and hence the presheaf-theoretic universes of Hofmann and Streicher [HS97] could be brought to bear without broaching the question of strict universes in sheaf topoi.

More recently, synthetic Tait computability has been employed in scenarios where the glued topos is not known to be of presheaf type. For example, Gratzer and Birkedal

⁴See also Sterling’s dissertation [Ste21] for a more detailed treatment of both this result and synthetic Tait computability in general.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

45

[GB22] proved a canonicity result for a version of guarded dependent type theory for which the necessary instance of STC involved a Grothendieck topology. It has therefore become a matter of some urgency to verify the existence of universes satisfying (U1-8) in arbitrary Grothendieck topoi.

6.3.2. UNIVERSES IN ARTIN GLUINGS. Let $F: \mathcal{E} \longrightarrow \mathcal{F}$ be a left exact functor between topoi such that $\mathcal{E}$ carries the structure of a model of Martin-Löf type theory, i.e. a pre-universe $\mathcal{T}$ in the sense of Definition 1.1.3. Write $\mathcal{G} := \mathcal{F} \downarrow F$ for the Artin gluing of $F$, and let $j: \mathcal{E} \hookrightarrow \mathcal{G}$ be the corresponding open immersion of topoi. Fixing a universe $\mathcal{S}$ in $\mathcal{G}$ (i.e. a class of maps satisfying (U1-7)) that contains $j_*\mathcal{T}$, we may define a new pre-universe $\mathcal{U}$ consisting of the subclass of $\mathcal{S}$ spanned by maps $f$ with $j^*f \in \mathcal{T}$.

We wish to verify that $\mathcal{U}$ likewise carries the structure of a model of Martin-Löf type theory in the same sense of satisfying (U1,3-5); results of this kind are used to prove important syntactic metatheorems for type theories, such as canonicity (a type theoretic analogue to the existence property), normalization, decidability of judgmental equality, and conservativity.

6.3.3. LEMMA. The class of maps $\mathcal{U} \subseteq \operatorname{Hom}_{\mathcal{G}}$ satisfies (U1,3,4).

PROOF. This is a straightforward consequence of the fact that $j^*$ is a logical functor, using the fact that $\mathcal{T}$ and $\mathcal{S}$ satisfy (U1,3,4).

To show that $\mathcal{U}$ is a pre-universe it remains to verify (U5), i.e. show that $\mathcal{U}$ has a generic family. It will turn out that the most elegant way to achieve this factors through an additional assumption that $\mathcal{S}$ satisfies the realignment property (U8).

6.3.4. CONSTRUCTION. We begin by constructing a putative generic family for $\mathcal{U}$ in $\mathcal{G}$, which we will subsequently verify to be generic as an application of the realignment property for $\mathcal{S}$. Because $j_*\mathcal{T} \subseteq \mathcal{S}$, we have in particular a cartesian morphism $j_*\pi_{\mathcal{T}} \longrightarrow \pi_{\mathcal{S}}$ in $\mathcal{G}^\rightarrow$; restricting into the open subtopos, we have $\pi_{\mathcal{T}} \cong j^*j_*\pi_{\mathcal{T}} \longrightarrow j^*\pi_{\mathcal{S}}$ in $\mathcal{E}^\rightarrow$; writing $q: U_{\mathcal{T}} \longrightarrow j^*U_{\mathcal{S}}$ for the base of this morphism, we may define the base of a putative generic family for $\mathcal{U}$ by cartesian lift in the gluing fibration:

$$\begin{array}{c c c} U_{\mathcal{U}} \xrightarrow{\bar{q}} U_{\mathcal{S}} & \mathcal{G} \\ \updownarrow \quad \updownarrow & j^* \\ U_{\mathcal{T}} \xrightarrow{q} j^*U_{\mathcal{S}} & \mathcal{E} \end{array} \tag{44}$$

The remainder of the family is defined by pullback:

$$\begin{array}{c c c} \pi_{\mathcal{U}} \xrightarrow{\quad} \pi_{\mathcal{S}} & \mathcal{G}^\rightarrow \\ \updownarrow \quad \updownarrow & \text{cod} \\ U_{\mathcal{U}} \xrightarrow{\bar{q}} U_{\mathcal{S}} & \mathcal{G} \end{array} \tag{45}$$

46

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

6.3.5. AN ABORTIVE ATTEMPT AT GENERICITY. Prior to verifying that Construction 6.3.4 gives rise to a generic family for $\mathcal{U}$ under the assumption of realignment for $\mathcal{S}$ in Section 6.3.6 below, it is useful to understand intuitively why realignment is needed. Fixing a morphism $f: X \longrightarrow Y \in \mathcal{U}$, we wish to construct a cartesian map $f \longrightarrow \pi_{\mathcal{U}}$. By definition, we have $f \in \mathcal{S}$ and $j^*f \in \mathcal{T}$, hence there exist a pair of cartesian morphisms $x': f \longrightarrow \pi_{\mathcal{S}}$ and $x_0: j^*f \longrightarrow \pi_{\mathcal{T}}$. Naively, we might hope to take advantage of the universal property of $U_{\mathcal{U}}$ *qua* cartesian lift to obtain a cartesian map $f \longrightarrow \pi_{\mathcal{U}}$:

![img-47.jpeg](img-47.jpeg)

Unfortunately the configuration of Diagram 46 is not valid: we do not have $j^*x' = q \circ x$. If $\mathcal{S}$ satisfies (U8), however, we may choose a *different* upper map $Y \longrightarrow U_{\mathcal{S}}$ that makes the analogous configuration commute.

6.3.6. GENERICITY VIA REALIGNMENT. Now we assume that $\mathcal{S}$ satisfies the realignment axiom (U8), and continue under the same assumptions as Section 6.3.5 to verify that Construction 6.3.4 exhibits a generic family for $\mathcal{U}$.

PROOF. We will employ the following realignment in which the upper map is defined by adjoint transpose in $j_! \dashv j^*$, and the left-hand map is a monomorphism because $j_!j^*E \cong j_!\mathbf{1}_{\mathcal{E}} \times E$ by Frobenius reciprocity and $j_!$ preserves subterminals:

![img-48.jpeg](img-48.jpeg)

*Remark.* To see that the upper and left-hand maps are cartesian, we recall from Taylor [Tay99, Proposition 7.7.1] that the left adjoint $j_! \dashv j^*$ creates non-empty limits and the counit $\epsilon: j_!j^* \longrightarrow \mathbf{id}_{\mathcal{G}}$ is a cartesian natural transformation, *i.e.* its naturality squares are cartesian; these facts follow immediately from the strictness of the initial object in the closed subtopos $\mathcal{F}$. Hence the transpose of a cartesian square from $\mathcal{E}$ under the adjunction $j_! \dashv j^*$ is a cartesian square in $\mathcal{G}$.

It is a consequence of the commutativity of Diagram 47 that $x$ lies over $x_0$:

$$j^*(x) = j^*(x \circ \epsilon) \circ \eta = j^*(q \circ x_0)^\sharp \circ \eta = q \circ x_0$$

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

47

We may use the base $x: Y \longrightarrow U_S$ of the glued morphism from Diagram 47 to extend $x_0$ to $\mathcal{U}$ as desired, repairing our failed attempt from Diagram 46:

![img-49.jpeg](img-49.jpeg)

In fact, this construction above gives a slightly stronger result than (U5).

6.3.7. THEOREM. Given $f: X \longrightarrow Y \in \mathcal{U}$ together with a cartesian map $x_0: j^*f \longrightarrow \pi_{\mathcal{T}}$, there exists a cartesian map $x: f \longrightarrow \pi_{\mathcal{U}}$ lying over $x_0$:

![img-50.jpeg](img-50.jpeg)

This property is particularly useful in proofs of metatheorems of type theories based on Artin gluing [Gra22; SA21; SAG22]. In this context, one typically requires not only that $\mathcal{U}$ be a pre-universe, but that the chosen codes witnessing (U3,4) are moreover preserved by $j^*$. Without Theorem 6.3.7, these strict equations would preclude a conceptual construction of these codes.

6.3.8. REMARK. Uemura [Uem17] presents an alternative construction for a pre-universe in $\mathcal{G}$ satisfying Theorem 6.3.7. Rather than relying on (U8), Uemura begins with separate pre-universes from $\mathcal{E}$ and $\mathcal{F}$ and combines them directly. This explicit decomposition ensures that the resultant universe satisfies the special case of (U8) necessary for Theorem 6.3.7.

## 7. Conclusions and future work

We have shown that every Grothendieck topos can be equipped with a cumulative hierarchy of universes satisfying (U1–8) assuming sufficient universes in the background set theory. This result is important because it extends the Hofmann–Streicher interpretation of Martin-Löf type theory in presheaf topoi to arbitrary sheaf topoi.

48

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

7.1. PROSPECTS FOR A CONSTRUCTIVE VERSION. Our constructions are highly classical; in particular, we rely on the theory of locally presentable categories and $\kappa$-compactness, both of which make heavy use of choice. Developing a constructively acceptable version of Section 4 remains an open problem. We briefly survey the landscape of universes within a particular constructive metatheory: the internal language of an elementary topos $\mathcal{E}$.

Although the literal definition of a Grothendieck universe is meaningless in $\mathcal{E}$, we can proceed analogously and fix a generic map $\tilde{\mathsf{V}} \rightarrow \mathsf{V}$ satisfying the appropriate version of (U2–4,6). The class $\mathcal{S}_{\mathsf{V}}$ classified by this map then satisfies (U1–6). Already some care must be taken; without choice, a family with $\mathsf{V}$-small fibers need not be classified by a map into $\mathsf{V}$. Absent the law of the excluded middle, (U8) is satisfied for at least the class of decidable monomorphisms $A \mapsto B$.

The Hofmann–Streicher construction exposed in Section 2 works over $\mathcal{E}$ without modification. In particular, the standard generic family of $\mathcal{S}_{\mathsf{V}}$ lifts to a universe in the category of internal presheaves $\Pr_{\mathcal{E}}(\mathcal{C})$ for any $\mathsf{V}$-small internal category $\mathcal{C}$. The class of maps $\tilde{\mathcal{S}}_{\mathsf{V}}$ classified by this map satisfies (U1–6). (U8) is satisfied only for the class of level-wise decidable monomorphisms: monomorphisms $A \mapsto B$ whose components $A(c) \mapsto B(c) \in \operatorname{Hom}_{\mathcal{E}}$ are all decidable [OP16]. In fact, Swan [Swa18] shows that this result is sharp: it is possible to choose a base topos in such a way that this generic map cannot satisfy (U8) for all monomorphisms, though it remains possible that there is another generic map satisfying (U8) for all monomorphisms. Finally, this universe induces a universe $\tilde{\mathcal{S}}_{\mathsf{V}}$ in any sheaf subtopos $\operatorname{Sh}_{\mathcal{E}}(\mathcal{C}, J)$. The construction is identical to that of Section 2 and $\tilde{\mathcal{S}}_{\mathsf{V}}$ satisfies (U1–6) just as in the classical setting. In this setting, however, the status of (U8) remains entirely open for this universe.

Over a base topos $\mathcal{E}$ not satisfying the axiom of choice, it is reasonable to hope that properties such as (U7) or (U8) might lift from $\mathcal{E}$ to any topos bounded over $\mathcal{E}$; this lifting is verified for (U7) in the context of algebraic set theory [JM95; vdB11], but the corresponding lifting for (U8) remains a conjecture.

# References

[AR94] Jiří Adámek and Jiří Rosický. Locally Presentable and Accessible Categories. London Mathematical Society Lecture Note Series 189. Cambridge University Press, 1994.

[Ang+21] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Kuen-Bang Hou (Favonia), Robert Harper, and Daniel R. Licata. “Syntax and models of Cartesian cubical type theory”. In: Mathematical Structures in Computer Science 31.4 (2021), pp. 424–468. DOI: 10.1017/S0960129521000347.

[AGV72] Michael Artin, Alexander Grothendieck, and Jean-Louis Verdier. Théorie des topos et cohomologie étale des schémas. Vol. 269, 270, 305. Lecture Notes in Mathematics. Séminaire de Géométrie Algébrique du Bois-Marie 1963–1964 (SGA 4), Dirigé par M. Artin, A. Grothendieck, et J.-L. Verdier. Avec la

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

49

collaboration de N. Bourbaki, P. Deligne et B. Saint-Donat. Berlin: Springer-Verlag, 1972.

[Awo21] Steve Awodey. “A Quillen model structure on the category of cartesian cubical sets”. Unpublished notes. 2021. URL: https://github.com/awodey/math/blob/e8c715cc5cb6a966e736656bbe54d0483f9650fc/QMS/qms.pdf.

[AF05] Steve Awodey and Henrik Forssell. “Algebraic models of intuitionistic theories of sets and classes.” In: Theory and Applications of Categories 15 (2005), pp. 147–163. URL: http://eudml.org/doc/125871.

[AGH21] Steve Awodey, Nicola Gambino, and Sina Hazratpour. Kripke-Joyal forcing for type theory and uniform fibrations. Unpublished manuscript. 2021. arXiv: 2110.14576 [math.LO].

[Bek00] Tibor Beke. “Sheafifiable homotopy model categories”. In: Math. Proc. Cambridge Philos. Soc. 129.3 (2000), pp. 447–475. ISSN: 0305-0041.

[Bén73] Jean Bénabou. Problèmes dans les topos : d’après le cours de Questions spéciales de mathématique. Séminaires de mathématique pure : Rapport, no 34. 34. Louvain-la-Neuve : Institut de mathématique pure et appliquée, Université catholique de Louvain, 1973.

[Ber11] Benno van den Berg. “Categorical semantics of constructive set theory”. Habilitation. Technische Universität Darmstadt, 2011.

[Bir+16] Lars Birkedal, Aleš Bizjak, Ranald Clouston, Hans Bugge Grathwohl, Bas Spitters, and Andrea Vezzosi. “Guarded Cubical Type Theory: Path Equality for Guarded Recursion”. In: 25th EACSL Annual Conference on Computer Science Logic (CSL 2016). Ed. by Jean-Marc Talbot and Laurent Regnier. Vol. 62. Leibniz International Proceedings in Informatics (LIPIcs). Dagstuhl, Germany: Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, 2016, 23:1–23:17. ISBN: 978-3-95977-022-4. DOI: 10.4230/LIPIcs.CSL.2016.23.

[Cis19] Denis-Charles Cisinski. Higher Categories and Homotopical Algebra. Cambridge Studies in Advanced Mathematics. Cambridge University Press, 2019. DOI: 10.1017/9781108588737. URL: http://www.mathematik.uni-regensburg.de/cisinski/CatLR.pdf.

[Coh+17] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. “Cubical Type Theory: a constructive interpretation of the univalence axiom”. In: IfCoLog Journal of Logics and their Applications 4.10 (Nov. 2017), pp. 3127–3169. arXiv: 1611.02108 [cs.LO].

[CMR17] T. Coquand, B. Manna, and F. Ruch. “Stack semantics of type theory”. In: 2017 32nd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS). June 2017, pp. 1–11. DOI: 10.1109/LICS.2017.8005130.

50

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

[CM16] Thierry Coquand and Bassel Mannaa. “The Independence of Markov’s Principle in Type Theory”. In: *1st International Conference on Formal Structures for Computation and Deduction (FSCD 2016)*. Ed. by Delia Kesner and Brigitte Pientka. Vol. 52. Leibniz International Proceedings in Informatics (LIPIcs). Dagstuhl, Germany: Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, 2016, 17:1–17:18. ISBN: 978-3-95977-010-1. DOI: 10.4230/LIPIcs.FSCD.2016.17. URL: http://drops.dagstuhl.de/opus/volltexte/2016/5993.

[GL12a] Richard Garner and Stephen Lack. “Lex colimits”. In: *Journal of Pure and Applied Algebra* 216.6 (2012), pp. 1372–1396. ISSN: 0022-4049. DOI: 10.1016/j.jpaa.2012.01.003.

[GL12b] Richard Garner and Stephen Lack. “On the axioms for adhesive and quasi-adhesive categories”. In: *Theory and Applications of Categories* 27.3 (2012), pp. 27–46.

[Gra22] Daniel Gratzer. “Normalization for Multimodal Type Theory”. In: *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science*. New York, NY, USA: Association for Computing Machinery, 2022. DOI: 10.1145/3531130.3532398.

[GB22] Daniel Gratzer and Lars Birkedal. “A Stratified Approach to Löb Induction”. In: *7th International Conference on Formal Structures for Computation and Deduction (FSCD 2022)*. Ed. by Amy P. Felty. Vol. 228. Leibniz International Proceedings in Informatics (LIPIcs). Dagstuhl, Germany: Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, Aug. 2022. ISBN: 978-3-95977-233-4. DOI: 10.4230/LIPIcs.FSCD.2022.3.

[Gra+20] Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. “Multimodal Dependent Type Theory”. In: *Proceedings of the 35th Annual ACM/IEEE Symposium on Logic in Computer Science*. Saarbrücken, Germany: Association for Computing Machinery, 2020, pp. 492–506. ISBN: 978-1-4503-7104-9. DOI: 10.1145/3373718.3394736.

[HS97] Martin Hofmann and Thomas Streicher. “Lifting Grothendieck Universes”. Unpublished note. 1997. URL: https://www2.mathematik.tu-darmstadt.de/~streicher/NOTES/lift.pdf.

[HS98] Martin Hofmann and Thomas Streicher. “The groupoid interpretation of type theory”. In: *Twenty-five years of constructive type theory (Venice, 1995)*. Vol. 36. Oxford Logic Guides. New York: Oxford Univ. Press, 1998, pp. 83–111. DOI: 10.1093/oso/9780198501275.001.0001.

[Hyl88] J. M. E. Hyland. “A small complete category”. In: *Annals of Pure and Applied Logic* 40.2 (1988), pp. 135–165. ISSN: 0168-0072. DOI: 10.1016/0168-0072(88)90018-8.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

51

[HRR90] J. M. E. Hyland, E. P. Robinson, and G. Rosolini. “The Discrete Objects in the Effective Topos”. In: Proceedings of the London Mathematical Society s3-60.1 (Jan. 1990), pp. 1–36. ISSN: 0024-6115. DOI: 10.1112/plms/s3-60.1.1.
[JM95] André Joyal and Ieke Moerdijk. Algebraic Set Theory. London Mathematical Society Lecture Note Series. Cambridge University Press, 1995. DOI: 10.1017/CB09780511752483.
[KL21] Chris Kapulkin and Peter LeFanu Lumsdaine. “The Simplicial Model of Univalent Foundations (after Voevodsky)”. In: Journal of the European Mathematical Society 23 (6 Mar. 8, 2021), pp. 2071–2126. DOI: 10.4171/JEMS/1050. arXiv: 1211.2851 [math.LO].
[Lur09] Jacob Lurie. Higher Topos Theory. Princeton University Press, 2009. ISBN: 978-0-691-14049-0. arXiv: math/0608040 [math.CT].
[Lur22] Jacob Lurie. Kerodon. https://kerodon.net. 2022.
[Mac98] Saunders Mac Lane. Categories for the Working Mathematician. 2nd. Springer-Verlag New York, 1998.
[Mar71] Per Martin-Löf. “A Theory of Types”. 1971.
[Mar75] Per Martin-Löf. “An Intuitionistic Theory of Types: Predicative Part”. In: Logic Colloquium ’73. Ed. by H. E. Rose and J. C. Shepherdson. Vol. 80. Studies in Logic and the Foundations of Mathematics. Elsevier, 1975, pp. 73–118. DOI: 10.1016/S0049-237X(08)71945-1.
[Mar79] Per Martin-Löf. “Constructive Mathematics and Computer Programming”. In: 6th International Congress for Logic, Methodology and Philosophy of Science. Published by North Holland, Amsterdam. 1982. Hanover, Aug. 1979, pp. 153–175.
[Mar84] Per Martin-Löf. Intuitionistic type theory. Notes by Giovanni Sambin. Vol. 1. Studies in Proof Theory. Bibliopolis, 1984, pp. iv+91. ISBN: 88-7088-105-9.
[Niu+22] Yue Niu, Jonathan Sterling, Harrison Grodin, and Robert Harper. “A Cost-Aware Logical Framework”. In: Proceedings of the ACM on Programming Languages 6.POPL (Jan. 2022). DOI: 10.1145/3498670. arXiv: 2107.04663 [cs.PL].
[OP16] Ian Orton and Andrew M. Pitts. “Axioms for Modelling Cubical Type Theory in a Topos”. In: 25th EACSL Annual Conference on Computer Science Logic (CSL 2016). Ed. by Jean-Marc Talbot and Laurent Regnier. Vol. 62. Leibniz International Proceedings in Informatics (LIPIcs). Dagstuhl, Germany: Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, 2016, 24:1–24:19. ISBN: 978-3-95977-022-4. DOI: 10.4230/LIPIcs.CSL.2016.24.
[Rez10] Charles Rezk. “Toposes and homotopy toposes (version 0.15)”. Unpublished note. 2010. URL: https://faculty.math.illinois.edu/~rezk/homotopy-topos-sketch.pdf.

52

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

[RSS20] Egbert Rijke, Michael Shulman, and Bas Spitters. “Modalities in homotopy type theory”. In: Logical Methods in Computer Science 16 (1 Jan. 2020). DOI: 10.23638/LMCS-16(1:2)2020.

[Sat17] Christian Sattler. The Equivalence Extension Property and Model Structures. 2017. arXiv: 1704.06911 [math.CT].

[Shu15] Michael Shulman. “The Univalence Axiom for Elegant Reedy Presheaves”. In: Homology, Homotopy and Applications 17 (2 2015), pp. 81–106. DOI: 10.4310/HHA.2015.v17.n2.a6. arXiv: 1307.6248 [math.AT].

[Shu19] Michael Shulman. All (∞, 1)-toposes have strict univalent universes. Unpublished manuscript. Apr. 2019. arXiv: 1904.07004.

[Ste19] Raffael Stenzel. “On univalence, Rezk Completeness and presentable quasi-categories”. PhD thesis. University of Leeds, Mar. 2019. URL: https://etheses.whiterose.ac.uk/24342/.

[Ste21] Jonathan Sterling. “First Steps in Synthetic Tait Computability: The Objective Metatheory of Cubical Type Theory”. Version 1.1, revised May 2022. PhD thesis. Carnegie Mellon University, 2021. DOI: 10.5281/zenodo.6990769.

[SA21] Jonathan Sterling and Carlo Angiuli. “Normalization for Cubical Type Theory”. In: 2021 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS). Los Alamitos, CA, USA: IEEE Computer Society, July 2021, pp. 1–15. DOI: 10.1109/LICS52264.2021.9470719. arXiv: 2101.11479 [cs.LO].

[SAG22] Jonathan Sterling, Carlo Angiuli, and Daniel Gratzer. “A Cubical Language for Bishop Sets”. In: Logical Methods in Computer Science 18 (1 Mar. 2022). DOI: 10.46298/lmcs-18(1:43)2022. arXiv: 2003.01491 [cs.LO].

[SH21] Jonathan Sterling and Robert Harper. “Logical Relations as Types: Proof-Relevant Parametricity for Program Modules”. In: Journal of the ACM 68.6 (Oct. 2021). ISSN: 0004-5411. DOI: 10.1145/3474834. arXiv: 2010.08599 [cs.PL].

[SH22] Jonathan Sterling and Robert Harper. “Sheaf semantics of termination-insensitive noninterference”. In: 7th International Conference on Formal Structures for Computation and Deduction (FSCD 2022). Ed. by Amy P. Felty. Vol. 228. Leibniz International Proceedings in Informatics (LIPIcs). Dagstuhl, Germany: Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik, Aug. 2022, 5:1–5:19. ISBN: 978-3-95977-233-4. DOI: 10.4230/LIPIcs.FSCD.2022.5. arXiv: 2204.09421 [cs.PL].

[Str05] Thomas Streicher. “Universes in toposes”. In: From Sets and Types to Topology and Analysis: Towards practical foundations for constructive mathematics. Ed. by Laura Crosilla and Peter Schuster. Vol. 48. Oxford Logical Guides. Oxford: Oxford University Press, 2005, pp. 78–90. ISBN: 978-0-19-856651-9. DOI: 10.1093/acprof:oso/9780198566519.001.0001.

STRICT UNIVERSES FOR GROTHENDIECK TOPOI

53

[Str14] Thomas Streicher. “A model of type theory in simplicial sets: A brief introduction to Voevodsky’s homotopy type theory”. In: Journal of Applied Logic 12.1 (2014), pp. 45–49. DOI: 10.1016/j.jal.2013.04.001.
[Str17] Thomas Streicher. Realizability. Lecture notes. 2017. URL: https://www2.mathematik.tu-darmstadt.de/~streicher/REAL/REAL.pdf.
[Swa18] Andrew Swan. Separating Path and Identity Types in Presheaf Models of Univalent Type Theory. 2018. arXiv: 1808.00920.
[Tay99] Paul Taylor. Practical Foundations of Mathematics. Cambridge studies in advanced mathematics. Cambridge, New York (N. Y.), Melbourne: Cambridge University Press, 1999. ISBN: 0-521-63107-6.
[Uem17] Taichi Uemura. “Fibred Fibration Categories”. In: Proceedings of the 32nd Annual ACM/IEEE Symposium on Logic in Computer Science. Reykjavik, Iceland: IEEE Press, June 2017, 24:1–24:12. ISBN: 978-1-5090-3018-7. DOI: 10.1109/lics.2017.8005084.
[Uni13] The Univalent Foundations Program. Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study: https://homotopytypetheory.org/book, 2013.
[vdB11] Benno van den Berg. “Categorical semantics of constructive set theory”. Habilitation. Technische Universität Darmstadt, 2011.
[Voe06] Vladimir Voevodsky. “A very short note on homotopy λ-calculus”. Unpublished note. Sept. 2006. URL: https://www.math.ias.edu/Voevodsky/files/files-annotated/Dropbox/Unfinished_papers/Dynamic_logic/Stage_9_2012_09_01/2006_09_Hlambda.pdf.
[Xu15] Chuangjie Xu. “A continuous computational interpretation of type theories”. PhD thesis. University of Birmingham, July 2015. URL: http://etheses.bham.ac.uk/5967/.
[XE16] Chuangjie Xu and Martín Escardó. Universes in sheaf models. Unpublished note. 2016. URL: https://cj-xu.github.io/notes/sheaf_universe.pdf.

Department of Computer Science, Aarhus University

Department of Mathematics, San Diego University

Department of Computer Science and Technology, University of Cambridge

Email: gratzer@cs.au.dk

shulman@sandiego.edu

js2878@cl.cam.ac.uk