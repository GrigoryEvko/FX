arXiv:2605.15080v1 [cs.LO] 14 May 2026

# Eliminating reversals from cubical type theories

Evan Cavallo ✉ 🚩

Department of Computer Science and Engineering, University of Gothenburg and Chalmers University of Technology, Sweden

Christian Sattler ✉ 🚩

Department of Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg, Sweden

## Abstract

Cubical type theories are designed around an abstract unit interval from which types of paths, used to represent equalities, are defined. Varying the operations available on this interval yields different type theories. A reversal is an involutive operator on the interval that swaps its two endpoints. We show that for cubical type theories with self-dual interval theories, such as the minimal theory of two endpoints or the theory of a bounded distributive lattice, the extension of the theory with a reversal that internalizes the duality is a conservative extension. The key tool is a “twist construction”: the product of an interval and its dual is again an interval with a reversal given by swapping coordinates.

Our conservativity result applies to “opaque” cubical type theories, without strict equations reducing the filling operator at concrete type formers or eliminators from higher inductive types at path constructors. Using the same twist construction, we also construct models of strict cubical type theory with reversals in categories of cubical sets without reversals. We thereby give the first model of a theory with reversals whose homotopy theory corresponds to that of topological spaces.

**2012 ACM Subject Classification** Theory of computation → Type theory; Theory of computation → Constructive mathematics

**Keywords and phrases** Dependent type theory, univalence, cubical type theory

**Funding** *Evan Cavallo*: Knut and Alice Wallenberg Foundation (KAW), Grant No. 2019.0116
*Christian Sattler*: US Air Force Office of Scientific Research, award number FA9550-24-1-0302

## 1 Introduction

Cubical type theories [12, 3, 2] extend Martin-Löf’s dependent type theory [24] with an abstract unit interval $\mathbb{I}$ which behaves much like a type. Types of *paths* $a_0 \sim^A a_1$, i.e., of terms $i : \mathbb{I} \vdash a(i) : A$ varying over the interval with fixed endpoints $a(0) = a_0$ and $a(1) = a_1$, play the role of equality types. As equality types, path types are remarkably well-behaved. For example, they natively satisfy function extensionality: equalities of functions correspond to families of pointwise equalities. With additional type formers, cubical type theories can also support Voevodsky’s univalence axiom and higher inductive types (HITs) [13, 9], making them models of homotopy type theory (HoTT) [39].

Path types satisfy different strict equations than Martin-Löf’s identity types. On the one hand, they do not support a J eliminator with a strict computation rule [12, §9.1]. On the other hand, for example, one has an operator witnessing that functions $f : A \rightarrow B$ preserve paths, $\text{cong}_f := \lambda p.\lambda i.f(p(i)) : (a_0 \sim^A a_1) \rightarrow (f(a_0) \sim^B f(a_1))$, that commutes *strictly* with function composition: $\text{cong}_g \circ \text{cong}_f = \text{cong}_{g \circ f}$. Such equations make cubical type theory a convenient setting for *synthetic homotopy theory* (see, e.g., Mörtberg and Pujet [25]), homotopy theory developed in the language of type theory, which can involve complicated manipulations with iterated identity/path types.

The range of strict equations satisfied by a cubical type theory’s path types depends on its *interval theory*, the collection of operations available on $\mathbb{I}$. Given a *reversal* operator

2

Eliminating reversals from cubical type theories

$i:\mathbb{I}\vdash\neg i:\mathbb{I}$ such that $\neg 0=1$, $\neg 1=0$, and $\neg\neg i=i$, we can define a path inversion operator

$$\mathsf{sym} := \lambda p.\lambda i.p(\neg i) : (a_0 \sim^A a_1) \to (a_1 \sim^A a_0)$$

that is strictly involutive ($\mathsf{sym} \circ \mathsf{sym} = \mathsf{id}$) and commutes strictly with the action of functions ($\mathsf{cong}_f \circ \mathsf{sym} = \mathsf{sym} \circ \mathsf{cong}_f$). Connections $i:\mathbb{I}, j:\mathbb{I}\vdash i \land j:\mathbb{I}$ and $i:\mathbb{I}, j:\mathbb{I}\vdash i \lor j:\mathbb{I}$ behaving like the min and max functions on the topological interval are similarly useful for higher-dimensional manipulations. Cohen, Coquand, Huber, and Mörtberg's original cubical type theory [12] includes $\neg$, $\land$, and $\lor$ with the equational theory of the free De Morgan algebra. On the other hand, Angiuli, Favonia, and Harper's theory [3] demonstrates that none of these operators is necessary to set up a well-behaved cubical type theory.

While convenient for the user of the type theory, additional operations on the interval are less convenient for the semanticist. To justify the project of synthetic homotopy theory, a cubical type theory should at least have a model in $\infty$-groupoids, an abstract description of the homotopy theory of topological spaces. Constructive models classically equivalent to $\infty$-groupoids were found first for cubical type theory without any interval operations by Awodey, Cavallo, Coquand, Riehl, and Sattler [6] and then for the theory with one connection $\lor$ by Cavallo and Sattler [11]. Most recently, the second-named author announced [32] a model constructively equivalent to $\infty$-groupoids that can interpret cubical type theory with two connections, $\land$ and $\lor$, and the equations of a bounded distributive lattice. However, none of these models interpret a reversal. This is a particularly unfortunate state of affairs because Cubical Agda [41], the most widely used proof assistant for cubical type theory, is based on Cohen et al.'s type theory and thus includes $\neg$ along with $\lor$ and $\land$, and its substantial standard library [36] relies extensively on these operators.

## 1.1 Contributions

We show that a reversal is an essentially harmless extension to cubical type theory.

The key fact is that when $\mathbb{I}$ is an interval object with endpoints 0 and 1, its square $\mathbb{I} \times \mathbb{I}$ is an interval object with endpoints $(0,1)$ and $(1,0)$ and a reversal $\neg(i_0, i_1) := (i_1, i_0)$ that swaps the axes of the square. When $\mathbb{I}$ has connections defining a distributive lattice $(\mathbb{I}, \land, \lor, 0, 1)$, $\mathbb{I} \times \mathbb{I}$ is a De Morgan algebra with connections given by $(i_0, i_1) \land (j_0, j_1) := (i_0 \land j_0, i_1 \lor j_1)$ and $(i_0, i_1) \lor (j_0, j_1) := (i_0 \lor j_0, i_1 \land j_1)$. In general, when $\mathbb{I}$ has some self-dual algebraic structure (in a sense we make precise in Section 4.1), $\mathbb{I} \times \mathbb{I}$ has the same structure as well as a reversal. A variety of constructions in this mold appear in the algebraic literature (e.g., in lattice and order theory), where they are called twist constructions. This name originates with Kracht [23], who applies it to a construction of Nelson algebras from Heyting algebras taken from Vakarelov [40]. Fidel and Brignole [17] and Rivieccio [30, §7] consider the case of building De Morgan algebras from distributive lattices, which is of particular interest to us.

We derive two main results from this simple construction.

### 1.1.1 Conservativity for opaque cubical type theory

First, we prove that a reversal is a conservative extension for "opaque" cubical type theories with self-dual interval theories. Similar to a theory considered by Coquand, Huber, and Sattler [14], these opaque theories are cubical type theories where certain strict equations are either omitted or replaced with terms of path type. Specifically, we

- (a) omit equations that reduce uses of the filling operator at concrete type formers, and
- (b) weaken equations for the reduction of HIT eliminators on path constructors to paths.

E. Cavallo and C. Sattler

3

The equations of (a) always hold up to paths, by higher dimensional-instances of filling, so omitting them also amounts to weakening them to paths.

Building on the twist construction, we define a twist interpretation from opaque cubical type theories with reversals to corresponding theories without reversals, interpreting judgments $\Gamma \vdash i : \mathbb{I}$ as pairs $(\Gamma \vdash i_0 : \mathbb{I}, \Gamma \vdash i_1 : \mathbb{I})$ and path types as square types—encoded as iterated path types—with fixed values at the points $(0, 1)$ and $(1, 0)$. We use this translation to prove a conservativity result: for a context of term variables $\Gamma$ and type $\Gamma \vdash A$ in the base theory and a term $\Gamma \vdash \neg N : A$ in the extended theory, there is a term $\Gamma \vdash M : A$ in the base theory with a path $\Gamma \vdash \neg P : M \sim^A N$. Similarly, if $\Gamma \vdash \neg B$ is a type in the extended theory, then there is a type $\Gamma \vdash A$ with an equivalence $\Gamma \vdash \neg E : A \simeq B$.

Coquand, Huber, and Sattler [14] prove homotopy canonicity for their opaque cubical type theory: every closed term of natural number type is connected by a path to a concrete numeral. Our hope is that similar techniques can be used to show that strict cubical type theories may be conservative over their opaque counterparts in general. Some progress towards a framework for coherence theorems dealing with strictification of equations has been made by Bocquet [7]. With such a result, the program of relating cubical theories with different interval structure could be conducted in the simpler world of opaque theories, as we do here for reversals, then mechanically extended to strict theories.

### 1.1.2 Models for strict cubical type theory with reversals in spaces

In lieu of a hoped-for conservativity result for strict over opaque cubical type theories, we separately use the same basic twist construction to build concrete models of strict cubical type theory with reversals. We work with the parameterized model construction of Angiuli, Brunerie, Coquand, Harper, Favonia, and Licata (ABCHFL) [2], showing that any model of cubical type theory given by this construction can be upgraded to a model of a cubical type theory with reversals in the same target category.

Combining this with our prior work showing that the homotopy theory of a certain ABCHFL model is classically equivalent to $\infty$-groupoids [11], we obtain a model of strict cubical type theory with a reversal whose homotopy theory is classically equivalent to $\infty$-groupoids. This is the first known model of its kind. Although Cohen, Coquand, Huber, and Mörtberg [12] give a model of their type theory, which includes reversals, this model and others like it have pathological homotopy theories [31]. Our models avoid these pathologies.

To obtain a similar model for strict cubical type theory with reversals and connections, we would need an input ABCHFL model of the theory with connections in $\infty$-groupoids. At present, no such model is known: while the theory with connections has an ABCHFL model in cartesian cubical sets with connections, it is an open problem to characterize its homotopy theory, as discussed by Streicher and Weinberger [33]. The second-named author has claimed a model of cubical type theory with connections whose homotopy theory is that of $\infty$-groupoids [32], but it is not a direct instance of the ABCHFL construction. We expect that our work adapts to this model, but we leave this for future work.

### 1.2 Outline

In §2, we set the stage to study cubical type theories in generality by reviewing Uemura's framework of second-order generalized algebraic theories and their semantics based on representable map categories [37, 38]. We recall Kapulkin and Lumsdaine's definition of weak equivalence for models of type theory with $\Sigma$ and identity types [22], which we will use to state our conservativity theorem. In §3, we define cubical type theory in these terms.

4

Eliminating reversals from cubical type theories

We begin studying opaque cubical type theory in §4, where we define the extension of a self-dual interval theory with a reversal and the twist interpretation from a cubical type theory extended with a reversal back to the original theory. In §5, we define the representable map category of spans and develop tools to relate pairs of interpretations between cubical type theories. We use these in §6 to prove a general theorem for deriving weak equivalences from interpretations; we apply it with the twist interpretation to deliver the conservativity of reversals over opaque cubical type theories with self-dual interval theories. In §7, we construct a model of strict cubical type theory with reversals whose homotopy theory is classically that of ∞-groupoids.

## 2 Type theories and models

### 2.1 SOGATs

We use Uemura's framework of second-order generalized algebraic theories (SOGATs) [37, Chapter 4] and their semantic counterparts, representable map categories [37, Chapter 4] [38] (also called categories with representable maps). The language of SOGATs is a logical framework (cf. Harper, Honsell, and Plotkin [18]) with which we can specify type theories themselves in type-theoretic language. In a SOGAT, we specify the judgment forms of a type theory while marking some as hypothesizable or representable. To begin with an example, basic dependent type theory MLTT [37, Example 4.6.1] is specified by two sorts, one for types and one for terms:

$$\mathsf{Ty} : () \Rightarrow \square$$

$$\mathsf{Tm} : (\mathsf{A} : () \rightarrow \mathsf{Ty}) \Rightarrow \star$$

The type sort Ty takes no parameters (() ⇒ ... ) and is non-representable (□), so hypotheses “A : Ty” cannot appear in the contexts of the type theory being specified. The term sort Tm takes one type (A : () → Ty) as a parameter and is representable (★), meaning we allow hypotheses “a : Tm(A)”.

In general, a SOGAT consists of declarations Φ ⇒ s where Φ is an environment and s is either □, ★, a previously introduced sort, or an equation between expressions such a sort. An environment is a list (A₁ : Γ₁ → e₁, ..., Aₙ : Γₙ → eₙ) of metavariables Aᵢ that take a context Γᵢ and output an eᵢ which is either a previously defined sort or an equation between expressions in such a sort. Finally, a context is a list (a₁ : A₁, ..., aₙ : Aₙ) of variables aᵢ of representable sorts Aᵢ. Everything can depend on what precedes it. We refer to Uemura [37, Chapter 4] for a much more precise description.

▶ Notation 1. We omit empty contexts (() → ...) and environments (() ⇒ ...), writing, e.g., Ty : □ and Tm : (A : Ty) ⇒ ★. We also omit variable names when what follows does not depend on them, as in Tm : Ty ⇒ ★. We surround arguments in square brackets when we intend to leave them implicit, as in the following example of Σ types. Specifically to MLTT: we leave the Tm operator implicit and write a : A rather than a : Tm(A).

▶ Notation 2 (cf. [37, Remark 5.4.6]). Any context can be treated as an environment; one level up, any environment Φ over a SOGAT T can be treated as an extension of T with new declarations. We write T[Φ] for the extended SOGAT combining T with Φ.

Uemura gives encodings of standard type formers of Martin-Löf type theory such as (negative) unit types, (negative) dependent sums, and dependent products [37, §4.6.1]. For

E. Cavallo and C. Sattler

5

example, dependent sums are specified by the declarations

\(\Sigma : (\mathsf{A}:\mathsf{Ty},\mathsf{B}:\mathsf{A}\to \mathsf{Ty})\Rightarrow \mathsf{Ty}\)   
fst : ([A:Ty,B:A \(\rightarrow\) Ty], \(\Sigma (\mathsf{A},\mathsf{B}))\Rightarrow \mathsf{A}\)   
snd : ([A:Ty,B:A \(\rightarrow\) Ty], \(\Sigma (\mathsf{A},\mathsf{B}))\Rightarrow \mathsf{B}(\mathsf{a})\)   
pair : ([A:Ty,B:A \(\rightarrow\) Ty],a:A,b:B(a)) \(\Rightarrow \Sigma (\mathsf{A},\mathsf{B})\)

and, over \(\Phi_{\Sigma} = (\mathsf{A}:\mathsf{Ty},\mathsf{B}:\mathsf{A}\to \mathsf{Ty})\) , equations

\(\begin{array}{ll} & : & (\Phi_{\Sigma}, \mathsf{a}: \mathsf{A}, \mathsf{b}: \mathsf{B}(\mathsf{a})) \Rightarrow \mathsf{fst}(\mathsf{pair}(\mathsf{a}, \mathsf{b})) \equiv \mathsf{a}: \mathsf{A}\\ & : & (\Phi_{\Sigma}, \mathsf{a}: \mathsf{A}, \mathsf{b}: \mathsf{B}(\mathsf{a})) \Rightarrow \mathsf{snd}(\mathsf{pair}(\mathsf{a}, \mathsf{b})) \equiv \mathsf{b}: \mathsf{B}(\mathsf{a})\\ & : & (\Phi_{\Sigma}, \mathsf{s}: \Sigma(\mathsf{A}, \mathsf{B})) \Rightarrow \mathsf{s} \equiv \mathsf{pair}(\mathsf{fst}(\mathsf{s}), \mathsf{snd}(\mathsf{s})): \Sigma(\mathsf{A}, \mathsf{B}) \end{array}\)

▶ Notation 3. We write  \( MLTT_{\Sigma,ld} \)  for the extension of MLTT with  \( \Sigma \)  types, unit types (which we think of as nullary  \( \Sigma \)  types), and identity types [37, Examples 4.6.4–4.6.6]. We write  \( MLTT_{\Sigma,ld,\Pi} \)  for its further extension with  \( \Pi \)  types [37, Example 4.6.3].

▶ Notation 4. We write  \( \Sigma a:A \) . B as shorthand for  \( \Sigma(A,\langle\mathsf{a}\rangle B) \) , where  \( \langle\mathsf{a}\rangle \)  denotes abstraction over the variable a. If B does not depend on a, we write  \( A\times B \) . We write  \( (a,b) \)  for the pairing pair  \( (a,b) \)  and s.1 and s.2 for fst(s) and snd(s), respectively. For  \( \Pi \)  types, we write  \( \Pi a:A \) . B for  \( \Pi(A,\langle\mathsf{a}\rangle B) \)  and  \( A\to B \)  when B does not depend on a. For identity types, we write the type  \( \operatorname{Id}(A,a_{0},a_{1}) \)  of identities in A from  \( a_{0} \)  to  \( a_{1} \)  as  \( a_{0}\asymp^{A}a_{1} \)  or  \( a_{0}\asymp a_{1} \) .

▶ Notation 5. The unit type and dependent sums justify types of dependent n-tuples for  \( n \geq 0 \) . We write these with tupling  \( (a_{1}, \ldots, a_{n}) \)  and projections  \( s.1, \ldots, s.n \) .

### 2.2 Representable map categories

To specify the notion of model of a SOGAT, Uemura first introduces representable map categories, also called categories with representable maps.

▶ Definition 6 (Uemura [37, Definition 3.2.1]). A representable map category (RMC) is a finite limit category R equipped with a class of morphisms, the representable maps, such that (a) the representable maps are closed under pullback, and
(b) for each representable map  \( f: Y \to X \) , the pullback functor  \( f^{*}: R/X \to R/Y \)  has a right adjoint  \( f_{*}: R/Y \to R/X \)  (called pushforward).

We use the arrow style  \( \rightarrow \)  to indicate representable maps. A representable map functor or RMC functor  \( F: R \rightarrow S \)  between representable map categories is a functor that preserves finite limits, representable maps, and pushforwards along representable maps.

▶ Example 7 (Uemura [37, Example 3.2.2]). Let C be a small category. The category of presheaves PSh(C) becomes an RMC when equipped with the class of morphisms  \( f: B \to A \)  such that for every map  \( a: \&c \to A \)  from a representable presheaf, there is a pullback square

![img-0.jpeg](img-0.jpeg)

for some \(d\in \mathcal{C}\)

The collection of representable map categories, representable map functors between them, and natural isomorphisms defines a  \( (2,1) \) -category RMC. Each SOGAT T induces

6

Eliminating reversals from cubical type theories

a “syntactic” RMC  \( \mathbb{C}\mathrm{L}(T) \)  [37, §4.8] whose objects are environments  \( \Phi \)  over T and whose morphisms are instantiations: an instantiation  \( I\colon\Phi\to\Psi \)  where  \( \Psi=(\mathbb{A}_{1}:\Gamma_{1}\to e_{1},\ldots,\mathbb{A}_{n}:\Gamma_{n}\to e_{n}) \)  is an assignment  \( (\mathbb{A}_{1}:=\langle\vec{\mathbf{a}_{1}}\rangle t_{1},\ldots,\mathbb{A}_{n}:=\langle\vec{\mathbf{a}_{n}}\rangle t_{n}) \)  sending each metavariable  \( A_{i} \)  in the target to an expression  \( t_{i}:e_{i} \)  in context  \( \vec{a}_{i}:\Gamma_{i} \)  over  \( T[\Phi] \) . An instantiation is representable when it is isomorphic to the projection  \( \Phi:\Gamma\to\Phi \)  for an extension of an environment  \( \Phi \)  by a context  \( \Gamma \) . For concrete SOGATs, we usually suppress  \( \mathbb{C}\mathrm{L}(-) \)  and use the same name for the SOGAT and its induced RMC.

The RMC \(\mathbb{C}\mathrm{L}(T)\) has a (2, 1)-categorical universal property that characterizes RMC functors \(\mathbb{C}\mathrm{L}(T) \to \mathbb{R}\) up to isomorphism as interpretations [37, Theorem 4.8.18]. An interpretation of \(T\) in \(\mathbb{S}\) is a specification of the image of each declaration of \(T\) inside \(\mathbb{S}\). For example, an RMC functor \(F: \mathbb{M}\mathrm{LTT} \to \mathbb{S}\) is determined up to isomorphism by an object \(FTy \in \mathbb{S}\) and a representable map \(F\pi_{\mathrm{Tm}}: FTm \to FTy\), which specifies the image of \(\pi_{\mathrm{Tm}}: (\mathbb{A}: Ty, \mathbb{a}: Tm(\mathbb{A})) \to (\mathbb{A}: Ty)\). As a special case, we can speak of interpretations of a SOGAT \(T\) in another SOGAT \(S\) as interpretations of \(T\) in \(\mathbb{C}\mathrm{L}(S)\).

### 2.3 Models

An interpretation  \( \mathbb{C}\mathrm{L}(T)\to\mathbb{S} \)  is a model of a SOGAT as a second-order theory. To recover a notion of first-order model, corresponding for example to categories with families [16] for MLTT, Uemura uses presheaf categories with representable maps:

▶ Definition 8 ([37, §3.2.4]). A model  \( \mathcal{M} = (\mathcal{C}, M) \)  of an RMC R is a category C with a terminal object and an RMC functor  \( M: R \to \mathrm{PSh}(\mathcal{C}) \)  to the presheaf RMC of Example 7. We write  \( \mathcal{M}(\star) \)  for C and  \( \mathcal{M}(X) := MX \in \mathrm{PSh}(\mathcal{M}(\star)) \)  for  \( X \in R \) .

A morphism \(\mathcal{F} = (F, \alpha) \colon \mathcal{M} \to \mathcal{N}\) between models is a functor \(F \colon \mathcal{M}(\star) \to \mathcal{N}(\star)\) and family of natural transformations \(\alpha_X \colon \mathcal{M}(X) \to F^*\mathcal{N}(X)\), natural in \(X \in \mathbb{R}\), such that for each representable \(f \colon Y \to X\), the naturality square for \(\alpha\) at \(f\) satisfies a Beck-Chevalley condition. For \(c \in \mathcal{M}(\star)\), we write \(\mathcal{F}(c) \in \mathcal{N}(\star)\) for \(Fc\). For \(x \colon \& c \to \mathcal{M}(X)\) in \(\mathrm{PSh}(\mathcal{C})\), we write \(\mathcal{F}_X(x) \colon \& \mathcal{F}(c) \to \mathcal{N}(X)\) for the map corresponding by Yoneda to \(\alpha_X \circ x \colon \& c \to F^*\mathcal{N}(X)\).

Models of MLTT in this sense correspond directly to natural models as defined by Awodey [4], and thereby to categories with families:  \( \mathcal{M}(\star) \)  interprets the context judgment, and  \( \mathcal{M}(\mathrm{Ty}) \)  and  \( \mathcal{M}(\mathrm{Tm}) \)  the type and term judgments over a context. With an appropriate notion of 2-morphism, the collection of models of an RMC R forms a (2,1)-category  \( \mathbf{Mod}(\mathbb{R}) \) .

▶ Definition 9 ([37, Definitions 5.1.4 & 5.1.6]). The class of contextual objects in  \( \mathcal{M}(\star) \)  for a model  \( \mathcal{M} \in \text{Mod}(\mathbb{R}) \)  is inductively generated as follows:

1. terminal objects \(1 \in \mathcal{M}(\star)\) are contextual;
2. for each contextual \( c \in \mathcal{M}(\star) \), representable \( f: Y \to X \) in \( \mathbb{R} \), and pullback square

\[
\begin{array}{c} \mathbb {A} d \longrightarrow \mathcal {M} (Y) \\ \Big \downarrow^ {\perp} \qquad \qquad \qquad \Big \downarrow_ {\mathcal {M} (f)} \\ \mathbb {A} c \longrightarrow \mathcal {M} (X) \end{array}
\]

with \(d\in \mathcal{M}(\star)\) , the object \(d\) is contextual.

A model is democratic when all of its objects are contextual. The heart (or contextual core) \(\mathcal{M}^{\heartsuit}\in\mathbf{Mod}(\mathbb{R})\) of \(\mathcal{M}\) is defined by taking \(\mathcal{M}^{\heartsuit}(\star)\) to be the full subcategory of contextual objects in \(\mathcal{M}(\star)\) and \(\mathcal{M}^{\heartsuit}(X)\) to be the restriction of \(\mathcal{M}(X)\) to a presheaf on \(\mathcal{M}^{\heartsuit}(\star)\).

E. Cavallo and C. Sattler

7

### 2.4 Weak equivalences

Kapulkin and Lumsdaine [22, Definition 3.1] define weak equivalences of contextual categories with identity types. We translate their definition into Uemura's framework as a property of morphisms in \(\mathbf{Mod}(\mathbb{MLTT}_{\Sigma,\mathrm{Id}})\). First, we define the environment \(\mathsf{Ty}^{\simeq}\) of 1-to-1 correspondences, pairs of types connected by a type-valued relation that associates each element of one type with a unique element of the other. This is one way of defining equivalence between types [39, Exercise 4.2]. Similarly, we have an environment \(\mathsf{Tm}^{\simeq}\) of pairs of identified elements within a type.

▶ Definition 10. Over A : Ty, define  \( \Phi_{\text{isContr}}(A) := (a_0: A, p : (a_1: A) \to a_0 \asymp^A a_1) \) . Write  \( Ty^{\simeq} \in MLTT_{\Sigma, Id} \)  for

\[
\begin{array}{l} (\mathsf {A}: \mathsf {T y}, \mathsf {A} ^ {\prime}: \mathsf {T y}, \overline {{\mathsf {A}}}: (\mathsf {a}: \mathsf {A}, \mathsf {a} ^ {\prime}: \mathsf {A} ^ {\prime}) \to \mathsf {T y}, \\ \_ : (\mathsf {a}: \mathsf {A}) \to \Phi_ {\text {isContr}} (\Sigma \mathsf {a} ^ {\prime}: \mathsf {A} ^ {\prime}. \overline {{\mathsf {A}}} (\mathsf {a}, \mathsf {a} ^ {\prime})), \_ : (\mathsf {a} ^ {\prime}: \mathsf {A} ^ {\prime}) \to \Phi_ {\text {isContr}} (\Sigma \mathsf {a}: \mathsf {A}. \overline {{\mathsf {A}}} (\mathsf {a}, \mathsf {a} ^ {\prime}))) \\ \end{array}
\]

and \(d^0, d^1: \mathsf{Ty}^\simeq \to \mathsf{Ty}\) for the maps projecting \(\mathsf{A}\) and \(\mathsf{A}'\) respectively.

▶ Definition 11. Set \(\mathsf{Tm}^{\simeq} := (\mathsf{A} : \mathsf{Ty}, \mathsf{a} : \mathsf{A}, \mathsf{a}' : \mathsf{A}, \overline{\mathsf{a}} : \mathsf{a} \asymp^{\mathsf{A}} \mathsf{a}')\) and write \(d^{0}, d^{1} : \mathsf{Tm}^{\simeq} \to \mathsf{Tm}\) for the maps projecting \((\mathsf{A}, \mathsf{a})\) and \((\mathsf{A}, \mathsf{a}')\).
▶ Definition 12. A morphism \(\mathcal{F}\colon\mathcal{M}\to\mathcal{N}\) in \(\mathbf{Mod}(\mathbb{MLTT}_{\Sigma,\mathrm{Id}})\) is a weak equivalence if the following hold for all \(\Gamma\in\mathcal{M}(\star)\):

(a) weak type lifting: for every \(B\colon \mathcal{F}(\Gamma)\to \mathcal{N}(\mathsf{Ty})\) , there exist \(A\colon \mathcal{F}\Gamma \to \mathcal{M}(\mathsf{Ty})\) and \(E\colon \mathcal{F}(\Gamma)\to \mathcal{N}(\mathsf{Ty}^{\simeq})\) fitting in a commutative diagram

![img-1.jpeg](img-1.jpeg)

(b) weak term lifting: for every \(A\colon \mathcal{F}(\Gamma)\to \mathcal{N}(\mathsf{Ty})\) and \(b\colon \mathcal{F}\Gamma \to \mathcal{M}(\mathsf{Tm})\) with \(\pi_{\mathsf{Tm}}b = \mathcal{F}_{\mathsf{Ty}}(A)\), there exist \(a\colon \mathcal{F}\Gamma \to \mathcal{M}(\mathsf{Tm})\) with \(\pi_{\mathsf{Tm}}a = A\) and \(p\colon \mathcal{F}(\Gamma)\to \mathcal{N}(\mathsf{Tm}^{\simeq})\) fitting in a commutative diagram

![img-2.jpeg](img-2.jpeg)

Though we state Definition 12 for arbitrary models, it is generally only well-behaved for democratic models. In informal turnstile notation, \(\mathcal{F}\colon \mathcal{M}\to \mathcal{N}\) is a weak equivalence when (a) for every type \(\mathcal{F}(\Gamma)\vdash_{\mathcal{N}}B\) in the target model, there is a type \(\Gamma \vdash_{\mathcal{M}}A\) in the source model whose image by \(\mathcal{F}\) is equivalent to \(B\), and (b) for every term \(\mathcal{F}(\Gamma)\vdash_{\mathcal{N}}b:\mathcal{F}_{\mathrm{Ty}}(A)\) in the target model, there is a term \(\Gamma \vdash_{\mathcal{M}}a:A\) whose image by \(\mathcal{F}\) is identified with \(b\).

We apply the notion of weak equivalence to “syntactic” models of  \( MLTT_{\Sigma,Id} \) , coming from extensions of the SOGAT of  \( MLTT_{\Sigma,Id} \) , in order to speak about conservativity relations between type theories (cf. for example Isaev [20], Bocquet [7], Kapulkin and Li [21]).

▶ Definition 13. For an RMC functor \(F\colon\mathbb{R}\to\mathbb{S}\), we write \(\mathbf{0}_{F}:=(\mathbb{R},\mathcal{F}\circ F)^{\heartsuit}\in\mathbf{Mod}(\mathbb{R})\) for the heart of the model of \(\mathbb{R}\) given by the RMC functor \(\mathbb{R}\xrightarrow{F}\mathbb{S}\xrightarrow{\mathcal{F}}\mathrm{PSh}(\mathbb{S})\). When \(F\) is understood from context, we write \(\mathbf{0}_{\mathbb{S}}\in\mathbf{Mod}(\mathbb{R})\).

8

Eliminating reversals from cubical type theories

A morphism \( G \colon (\mathbb{S}, F) \to (\mathbb{S}', F') \) in the coslice (2,1)-category \( \mathbb{R} / \mathbf{RMC} \) induces a morphism \( \mathbf{0}_G \colon \mathbf{0}_F \to \mathbf{0}_{F'} \) of models of \( \mathbb{R} \). A special case of the above construction is its application to the identity \( \operatorname{Id} \colon \mathbb{R} \to \mathbb{R} \): the model \( \mathbf{0}_{\mathbb{R}} \in \mathbf{Mod}(\mathbb{R}) \) is a bi-initial object in \( \mathbf{Mod}(\mathbb{R}) \), the initial model of \( \mathbb{R} \) [37, §5.4.1].

## 3 Cubical type theories

### 3.1 The interval

Before defining cubical type theory, we first introduce a simple SOGAT specifying the interval alone. This will let us easily speak about cubical type theories with different interval theories.

▶ Definition 14. The SOGAT INT of an interval has one representable sort with two points:

\[
\mathbb {I}: () \Rightarrow \star \quad 0, 1: () \Rightarrow \mathbb {I}
\]

▶ Definition 15. An interval theory is an environment \(\Phi \in \mathbb{INT}\).

Per §2.1, a context in \(\mathbb{INT}\) is simply a list \((\mathbf{i}_1:\mathbb{I},\ldots ,\mathbf{i}_n:\mathbb{I})\). An environment \(\Phi\) consists of declarations of the form \(\mathbf{r}:\Gamma \to \mathbb{I}\) and \(\_ :\Gamma \to r_1\equiv r_2:\mathbb{I}\). In other words, \(\Phi\) specifies a single-sorted algebraic theory extending the theory of two points 0, 1.

▶ Example 16. The cartesian interval theory  \( \Phi_{cart} \)  is the trivial environment  \( 1 := () \in \mathbb{INT} \) . The distributive lattice interval theory  \( \Phi_{DL} \)  is the environment beginning with

\[
\begin{array}{l l}(- \wedge -), (- \vee -)&: (\mathbf {i}: \mathbb {I}, \mathbf {j}: \mathbb {I}) \to \mathbb {I}\\_ {-}&: (\mathbf {i j k}: \mathbb {I}) \to \mathbf {i} \wedge (\mathbf {j} \vee \mathbf {k}) \equiv (\mathbf {i} \wedge \mathbf {j}) \vee (\mathbf {i} \wedge \mathbf {k}): \mathbb {I}\end{array}
\]

and continuing with the other equations of a bounded distributive lattice, as enumerated for example by Buchholtz and Morehouse [8, Table 1]: associativity and commutativity of \(\wedge\) and \(\vee\), unit laws \(\mathbf{i} \wedge \mathbf{l} \equiv \mathbf{i}\) and \(\mathbf{i} \vee \mathbf{0} \equiv \mathbf{i}\), and absorption laws \(\mathbf{i} \wedge (\mathbf{i} \vee \mathbf{j}) \equiv \mathbf{i}\) and \(\mathbf{i} \vee (\mathbf{i} \wedge \mathbf{j}) \equiv \mathbf{i}\).

### 3.2 Cofibrations

In addition to Ty, Tm, and I, cubical type theory has a sort of cofibrations and, over the sort of cofibrations, a representable sort for cofibration truth:

\[
\text { Cof } \quad : \quad \square \quad \text { True } \quad : \quad (\mathrm{P}: \mathrm{Cof}) \Rightarrow \star
\]

We write \(\mathbb{C}\mathrm{OF}\) for the SOGAT consisting of these two sorts. In fact we have \(\mathbb{C}\mathrm{OF} \cong \mathbb{M}\mathrm{LTT}\), but it will be useful to have distinct notation for this sub-SOGAT of our cubical type theories.

### 3.3 Opaque cubical type theory

We define opaque cubical type theory, \(\mathbb{C}\mathrm{TT}\), as a mutual extension of the SOGATs of Martin-Löf type theory with \(\Sigma\), \(\Pi\), and identity types (\(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{M},\Pi}\)), an interval (\(\mathbb{INT}\)), and a cofibration classifier (\(\mathbb{COF}\)). We roughly follow Uemura's encodings of cubical type theory [37, §4.6.3] [38, Example 5.14]. We introduce the declarations of \(\mathbb{C}\mathrm{TT}\) (beyond those of \(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{M},\Pi}\), \(\mathbb{INT}\), and \(\mathbb{COF}\)) in stages over the course of this section (§3.3).

▶ Remark 17. Given that path types serve as equality types in cubical type theories, it may seem strange that we include Martin-Löf's identity types in CTT, though their coexistence is semantically justified [12, §9.1] [9, §3.3] [2, §2.16]. We do so partly in order to reuse Kapulkin

E. Cavallo and C. Sattler

9

and Lumsdaine's tools for comparing type theories [22], though we could have redeveloped these with path types. The more technical reason is that we want to include (higher) inductive types in \(\mathbb{C}\Pi\). The span interpretation (§5) that we use to prove conservativity interprets inductive types as inductive families [15], and we use identity types to define these families. This is the one place where identities cannot straightforwardly be replaced with paths.

#### 3.3.1 Cofibrations

In CTT, we add new operators and equations for the sorts of COF. A cofibration can be thought of as a constraint on interval terms. Cofibration truth is a strict proposition in the sense that any two witnesses to truth of a cofibration are strictly equal:

\[
\_ \quad : \quad (P: \text { Cof }, u v: \text { True } (P)) \Rightarrow u \equiv v: \text { True } (P)
\]

As with Tm, we will leave the True operator implicit. Cofibrations are closed under finite conjunction  \( (\top, \cap) \)  and disjunction  \( (\bot, \cup) \) :

\[
\begin{array}{l} \top , \bot : \text {Cof} \quad -: (P Q: \text {Cof}, P, Q) \Rightarrow P \cap Q \\ (- \cap -): (P Q: \text {Cof}) \Rightarrow \text {Cof} \quad -: (P Q: \text {Cof}, P \cap Q) \Rightarrow P \\ (- \cup -): (P Q: \text {Cof}) \Rightarrow \text {Cof} \quad -: (P Q: \text {Cof}, P \cap Q) \Rightarrow Q \\ \_ \quad : \quad \top \quad \_ \quad : \quad (P Q: C o f, P) \Rightarrow P \cup Q \\ \_ \quad : \quad (P: \text {Cof}, \bot) \Rightarrow P \quad \_ \quad : \quad (P Q: \text {Cof}, Q) \Rightarrow P \cup Q \\ -: (P Q R: \text {Cof}, P \to R, Q \to R, P \cup Q) \Rightarrow R \\ \end{array}
\]

Eliminators for the nullary and binary disjunction \((\mathrm{elim}_{\perp}^{\mathrm{Ty}},\mathrm{elim}_{\perp}^{\mathrm{Tm}},\mathrm{elim}_{\cup}^{\mathrm{Ty}},\mathrm{elim}_{\cup}^{\mathrm{Tm}})\) allow us to define types and terms by case analysis. We abbreviate

\[
\Phi_ {\cup \mathrm{Ty}} = (P Q: \text {Cof}, A: [ P ] \rightarrow \mathrm{Ty}, B: [ Q ] \rightarrow \mathrm{Ty}, [ P \cap Q \rightarrow A \equiv B: \mathrm{Ty} ])
\]

\[
\Phi_ {\cup \mathrm{Tm}} = (P Q: \text {Cof}, A: [ P \cup Q ] \rightarrow \mathrm{Ty}, a: [ P ] \rightarrow A, b: [ Q ] \rightarrow A, [ P \cap Q \rightarrow a \equiv b: A ])
\]

and specify

\[
\begin{array}{l} \operatorname{elim} _ {\perp} ^ {\mathrm{Ty}}: [ \bot ] \Rightarrow \mathrm{Ty} \\ \operatorname{elim} _ {\perp} ^ {\mathrm{Tm}}: (A: [ \bot ] \rightarrow \mathrm{Ty}, [ \bot ]) \Rightarrow A \\ \operatorname{elim} _ {\cup} ^ {\mathrm{Ty}}: \left(\Phi_ {\cup \mathrm{Ty}}, [ \mathrm{P} \cup \mathrm{Q} ]\right) \Rightarrow \mathrm{Ty} \\ \_ \quad : \quad (\Phi_ {\cup T y}, P) \Rightarrow \operatorname{elim} _ {\cup} ^ {T y} (P, Q, A, B) \equiv A: T y \\ \_ \quad : \quad (\Phi_ {\cup T y}, Q) \Rightarrow \operatorname{elim} _ {\cup} ^ {T y} (P, Q, A, B) \equiv B: T y \\ \operatorname{elim} _ {\cup} ^ {\mathrm{Tm}}: \left(\Phi_ {\cup \mathrm{Tm}}, [ \mathrm{P} \cup \mathrm{Q} ]\right) \Rightarrow \mathrm{A} \\ \_ \quad : \quad (\Phi_ {\cup T m}, P) \Rightarrow \operatorname{elim} _ {\cup} ^ {T m} (P, Q, A, a, b) \equiv a: A \\ \_ \quad : \quad (\Phi_ {\cup T m}, Q) \Rightarrow \operatorname{elim} _ {\cup} ^ {T m} (P, Q, A, a, b) \equiv b: A \\ \end{array}
\]

The basic cofibrations are equations on interval terms, which we write with \(\approx\). The two endpoints 0 and 1 are distinct, and we can convert between \(\approx\) and strict equality \(\equiv\).

\[
\begin{array}{l} - \approx -: (i j: \mathbb {I}) \Rightarrow \text {Cof} \quad -: (i: \mathbb {I}) \Rightarrow i \approx i \\ -: (0 \approx 1) \Rightarrow \bot -: (i j: \mathbb {I}, i \approx j) \Rightarrow i \equiv j: \mathbb {I} \\ \end{array}
\]

▶ Remark 18. We could have included various algebraic laws for cofibrations, such as  \( P \cap Q \equiv Q \cap P \) , or cofibration extensionality (P : Cof, Q : Cof,  \( P \to Q \) ,  \( Q \to P \) ) →  \( P \equiv Q : Cof \) . Our proofs go through for such variations without much change.

10

Eliminating reversals from cubical type theories

#### 3.3.2 Filling

Cofibrations are used to specify the filling operator. We first introduce the abbreviation \(\Phi_{\mathrm{fill}}\) for the environment

\[
(\mathrm{A}: \mathbb {I} \to \mathrm{Ty}, \mathrm{P}: \mathrm{Cof}, \mathrm{a}: ([ \mathrm{P} ], \mathrm{i}: \mathbb {I}) \to \mathrm{A} (\mathrm{i}), \mathrm{j}: \mathbb {I}, \mathrm{a} _ {0}: \mathrm{A} (\mathrm{j}), [ \mathrm{P} \to \mathrm{a} (\mathrm{j}) \equiv \mathrm{a} _ {0}: \mathrm{A} (\mathrm{j}) ]).
\]

This environment specifies a line ( \( \mathbb{I} \) -indexed family) of types A and a “partial” line of terms a over it, defined whenever some cofibration P is true, together with a fully-defined term  \( a_{0} \)  at some index  \( \mathsf{A}(\mathsf{j}) \)  that coincides with  \( \mathsf{a}(\mathsf{j}) \)  when P holds. Given this input, the filling operator outputs a line  \( (\mathsf{k}:\mathbb{I})\to\mathsf{A}(\mathsf{k}) \)  that “extends” both a and  \( a_{0} \)  in the following sense.

\[
\begin{array}{l} \text { fill } \quad : \quad (\Phi_ {\text { fill }}, k: \mathbb {I}) \Rightarrow A (k) \\ \_ \quad : \quad (\Phi_ {\text {fill}}, k: \mathbb {I}, P) \Rightarrow \operatorname{fill} (A, P, a, j, a _ {0}, k) \equiv a (k): A (k) \\ \_ \quad : \quad (\Phi_ {\text {fill}}) \Rightarrow \operatorname{fill} (A, P, a, j, a _ {0}, j) \equiv a _ {0}: A (j) \\ \end{array}
\]

The special case where \(\mathsf{P} = \bot\) is called coercion by Angiuli et al. [2, §2.7] and converts a term at some index \(\mathsf{a}_0:\mathsf{A}(\mathsf{j})\) to a term at any other index \(\mathsf{A}(\mathsf{k})\).

▶ Notation 19. Over the environment (A : (i : I) → Ty, j : I, a₀ : A(j), k : I), write coe(A, j, a₀, k) := fill(A, ⊥, ⟨i⟩elim⊥ᵀᵐ(A(i)), j, a₀, k) : A(k).
▶ Notation 20. We write  \( \text{fill}^{j\to k}(A,[P_{1}\mapsto a_{1},\ldots,P_{n}\mapsto a_{n}],a_{0}) \)  for  \( \text{fill}(A,P,a,j,a_{0},k) \)  where  \( P=P_{1}\cup\cdots\cup P_{n} \)  (with some choice of parentheses) and a is defined from  \( a_{1},\ldots,a_{n} \)  by cases using  \( \text{elim}_{\cup}^{Tm} \) . We write  \( \text{coe}^{j\to k}(A,a_{0}) \)  for  \( \text{coe}(A,j,a_{0},k) \) .
▶ Remark 21. This definition of fill is a suitable base for strict cubical type theory over arbitrary interval theories. In the presence of certain interval structure, it can be reduced to special cases. For theories with connections,  \( fill^{0\to1} \)  and  \( fill^{1\to0} \)  suffice; see Cavallo, Mörtberg, and Swan [10, Theorem 14 with Lemma 8]. With two connections and a reversal, this can be further reduced to  \( fill^{0\to1} \), as in Cohen et al.'s type theory [12]; see Angiuli et al. [2, §3.4]. We refer to Cavallo, Mörtberg, and Swan [10] for more detailed comparisons.

#### 3.3.3 Paths

A path is an \(\mathbb{I}\)-indexed term taking two fixed values at the endpoints \(0,1:\mathbb{I}\). Path types internalize paths:

\[
\begin{array}{l} \text { Path } \quad : \quad (\mathrm{A}: (\mathrm{i}: \mathbb {I}) \to \mathrm{Ty}, \mathrm{a} _ {0}: \mathrm{A} (0), \mathrm{a} _ {1}: \mathrm{A} (1)) \Rightarrow \mathrm{Ty} \\ \lambda^ {\mathbb {I}} \quad : \quad ([ \mathrm{A}: (\mathrm{i}: \mathbb {I}) \rightarrow \mathrm{Ty} ], \mathrm{a}: (\mathrm{i}: \mathbb {I}) \rightarrow \mathrm{A} (i)) \Rightarrow \operatorname{Path} (\mathrm{A}, \mathrm{a} (0), \mathrm{a} (1)) \\ - \mathbb {Q} -: ([ \mathrm{A}: (\mathrm{i}: \mathbb {I}) \rightarrow \mathrm{Ty}, \mathrm{a} _ {0}: \mathrm{A} (0), \mathrm{a} _ {1}: \mathrm{A} (1) ], \mathrm{p}: \operatorname{Path} (\mathrm{A}, \mathrm{a} _ {0}, \mathrm{a} _ {1}), \mathrm{i}: \mathbb {I}) \Rightarrow \mathrm{A} (\mathrm{i}) \\ \end{array}
\]

The equations for path types state that \(\lambda^{\mathbb{I}}(\mathsf{a})\mathbb{O}\mathsf{i}\equiv \mathsf{a}(\mathsf{i})\) and \(\mathsf{p}\equiv \lambda^{\mathbb{I}}(\langle \mathsf{i}\rangle \mathsf{p}\mathbb{O}\mathsf{i})\), as for function types, as well as that \(\mathsf{p}\mathbb{O}0\equiv \mathsf{a}_0\) and \(\mathsf{p}\mathbb{O}1\equiv \mathsf{a}_1\) for \(\mathsf{p}:\operatorname {Path}(\mathsf{A},\mathsf{a}(0),\mathsf{a}(1))\). See Uemura [37, §4.6.3, Type constructors] for a fully formal presentation.

▶ Notation 22. We write \(\lambda\mathbf{i}.a\) as shorthand for \(\lambda^{\mathbb{I}}\langle\mathbf{i}\rangle a\). We abbreviate “non-dependent” path types \(\text{Path}(\langle\_\rangle A, a_0, a_1)\), where the line of types is constant, as \(a_0 \sim^A a_1\) or simply \(a_0 \sim a_1\).

#### 3.3.4 Glue types

In cubical type theories, univalence is not an axiom but is instead derived from a type former that can construct \(\mathbb{I}\)-indexed types from equivalences. Universes closed under this type

E. Cavallo and C. Sattler

11

former can be shown to be univalent. Following Cohen et al. [12], Angiuli et al. implement univalence using so-called glue types [2, §2.11]; Angiuli, Favonia, and Harper's V-types are an alternative solution [3, §5.6].

First, we define equivalences [39, Definition 4.4.1] using path types. Over A : Ty, define isContr(A) := Σa₀:A. Πa₁:A. a₀ ∼^A a₁ : Ty. Over ([A B : Ty], f : A → B), define isEquiv(f) := Πb : B.isContr(Σa : A. f(a) ∼ b) : Ty. Finally, over (A B : Ty), define the type of equivalences (A ≃ B) := Σf : A → B. isEquiv(f). The Glue type former takes a type A, a cofibration P, and a partial type T and equivalence e : T ≃ A defined when P holds. Its output is a total type that reduces to T when P holds.

Glue : (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃ A) ⇒ Ty
_ : (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃ A, P) ⇒ Glue(A, P, T, e) ≡ T : Ty

We now abbreviate Φ_Glue = (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃ A). The Glue type has an introduction form glue and an elimination form unglue. Each reduces when P holds, and we have computation and uniqueness equations.

glue : ([Φ_Glue], a : A, t : [P] → T, [P → e.l(t) ≡ a : A]) ⇒ Glue(A, P, T, e)
_ : ([Φ_Glue], a : A, t : [P] → T, [P → e.l(t) ≡ a : A], P) ⇒ glue(a, t) ≡ t : T
unglue : ([Φ_Glue], g : Glue(A, P, T, e)) ⇒ A
_ : ([Φ_Glue], g : Glue(A, P, T, e), P) ⇒ unglue(g) ≡ e.l(g) : A
_ : ([Φ_Glue], a : A, t : [P] → T, [P → e.l(t) ≡ a : A]) ⇒ unglue(glue(a, t)) ≡ a : A
_ : ([Φ_Glue], g : Glue(A, P, T, e)) ⇒ g ≡ glue(unglue(g), g) : Glue(A, P, T, e)

The eliminator unglue can be shown to be an equivalence Glue(A, P, T, e) ≃ A that reduces to e when P holds. Univalence is derived using an instance where P is (i ≈ 0 ∪ i ≈ 1) for some i : ∥; see Cohen et al. [12, §7.2] or Angiuli et al. [2, §2.12].

### 3.3.5 Universe

We include one universe: a type U whose elements are regarded as types via a decoding function El.

U : Ty El : (A : U) ⇒ Ty

We often leave the coercion El from U to types implicit. For a universe to be useful, it should be closed under type formers such as Σ and Π; for it to be univalent, it should be closed under Glue. We refer to Uemura [37, Example 4.6.11] for an example formulation of these closure conditions, but we omit cases for type formers in the universe in our proofs: handling them always amounts to repeating the construction used for the type formers outside of the universe.

### 3.3.6 Higher inductive types

We include suspension types [39, §6.5] as a representative example of an HIT. See [13, 9] for general descriptions of HITs in cubical type theory. We specify the formation and introduction forms as follows:

Susp : (A : Ty) ⇒ Ty north, south : [A : Ty] ⇒ Susp(A)
merid : ([A : Ty], a : A) ⇒ north ∼^Susp(A) south

12

Eliminating reversals from cubical type theories

For elimination, we fix the environment

\[
\begin{array}{r c l} \Phi_ {\text {elim}} & = & ([ A: T y ], C: (t: S u s p (A)) \to T y, \\ & & n: C (\text {north}), s: C (\text {south}), m: (a: A) \to \text {Path} (\langle i \rangle C (\text {merid} (a) @ i), n, s)) \end{array}
\]

and specify

\[
\begin{array}{l} \text { elim } \quad : \quad (\Phi_ {\text { elim }}, t: \text { Susp } (A)) \Rightarrow C (t) \\ - \quad : \quad (\Phi_ {\text {elim}}) \Rightarrow \operatorname{elim} (C, n, s, m, \text {north}) \equiv n: C (\text {north}) \\ - \quad : \quad (\Phi_ {\text {elim}}) \Rightarrow \operatorname{elim} (C, n, s, m, \text {south}) \equiv s: C (\text {south}) \\ \text { merid } \beta : (\Phi_ {\text { elim }}, a: A) \Rightarrow \lambda i. \text { elim } (C, n, s, m, \text { merid } (a) @ i) \sim m \\ \end{array}
\]

This is an “opaque” suspension type in that merid \( \beta \) constructor is a path rather than a strict equality. This is how HITs are usually formulated in Book HoTT [39, §6.2], strict computation rules being characteristic of cubical type theory.

### 3.4 Strict cubical type theory

Strict cubical type theories—i.e., cubical type theories as they are usually defined—are designed to satisfy strict canonicity [19, 3], the property that every closed term of type N is strictly equal to a numeral. This requires two adjustments to our opaque cubical type theory, which we sketch here. A full description of the specific strict theory we model in §7 can be found in Angiuli et al. [2]. We write  \( C_{TT_{s}} \)  for the extension of the SOGAT CTT with the symbols and equations indicated below, following Angiuli et al.'s specification.

First, we add equations for each concrete type former for evaluating applications of the filling operator at that type. For  \( \Sigma \)  types, for example, we have an equation reducing  \( \text{fill}(\langle i\rangle\Sigma a:A(i).B(i,a),P,s,j,s_{0},k) \)  to a pair of two calls to the filling operator, one over A and one over an instance of B. For higher inductive types such as Susp, some applications of the filling operator are treated as values (i.e., not reduced), and equations are instead introduced for reducing the eliminator at these values [2, §2.15].

Second, we strictify the path  \( merid\beta \) , replacing it with a strict equation or, to express strict cubical type theory as an extension of opaque cubical type theory, introducing the strict equation and equating  \( merid\beta \)  with the reflexive path.

## 4 The twist interpretation

To prove conservativity of opaque cubical type theories with reversals over the corresponding theories without reversals, we first construct interpretations from the former to the latter. In §§5–6 we show that the existence of these interpretations abstractly implies conservativity. As sketched in §1.1, we exploit twist constructions: the fact that the “square” environment  \( \mathbb{I} \times \mathbb{I} = (\mathbf{i}_{0} : \mathbb{I}, \mathbf{i}_{1} : \mathbb{I}) \in \mathbb{C}\mathbb{T}\mathbb{T} \)  is an interval object with a reversal and inherits certain algebraic structure from I. Thus, we call our translation the twist interpretation.

### 4.1 Extension by a reversal

We have an interpretation Flip of INT in itself by taking  \( \text{Flip}(\mathbb{I}) := \mathbb{I} \) ,  \( \text{Flip}(0) := 1 \) , and  \( \text{Flip}(1) := 0 \) . By the (2, 1)-categorical universal property of  \( \mathbb{CL}(\mathbb{INT}) \)  [37, Theorem 4.8.18], this determines (up to isomorphism) an RMC functor  \( \text{Flip} \colon \mathbb{INT} \to \mathbb{INT} \)  with an isomorphism  \( \theta \colon \text{Flip} \circ \text{Flip} \cong \text{Id} \)  satisfying  \( \theta \circ \text{Flip} = \text{Flip} \circ \theta \)  and  \( \theta_{I} = id \) .

▶ Definition 23. A self-dual interval theory  \( (\Phi,\phi) \)  is an interval theory  \( \Phi \)  equipped with an isomorphism  \( \phi\colon\operatorname{Flip}(\Phi)\cong\Phi \)  such that  \( \operatorname{Flip}(\phi)\circ\phi=\theta_{\Phi}:\operatorname{Flip}(\operatorname{Flip}(\Phi))\cong\Phi \) .

E. Cavallo and C. Sattler

13

In a self-dual interval theory \((\Phi, \phi)\), the value of \(\phi\) at an operator \(\mathbf{r}: \mathbb{I}^n \to \mathbb{I}\) in \(\Phi\) is an expression \(\phi(\mathbf{r}): \mathbb{I}^n \to \mathbb{I}\) over \(\Phi\): the dual of \(\mathbf{r}\).

▶ Example 24. The cartesian theory  \( \Phi_{cart} \)  is self-dual with the trivial isomorphism  \( 1 \cong 1 \) . The theory  \( \Phi_{DL} \)  is self-dual with  \( \phi \)  defined by  \( \phi(-\wedge -)(i,j) = i \vee j \)  and vice versa.

▶ Definition 25. Given a self-dual interval theory ( \( \Phi, \phi \) ), its extension by a reversal  \( Rev_{\phi}\Phi \in INT \)  is the extension of  \( \Phi \)  with

(a) an operator  \( \neg: I \rightarrow I \) ,
(b) equations  \( \neg0\equiv1:\mathbb{I},\neg1\equiv0:\mathbb{I}, \)  and  \( (\mathbf{i}:\mathbb{I})\to\neg(\neg(\mathbf{i}))\equiv\mathbf{i}:\mathbb{I}, \)  and
(c) for each \(\mathbf{r}:(\mathbf{i}_1:\mathbb{I},\ldots ,\mathbf{i}_n:\mathbb{I})\to \mathbb{I}\) in \(\Phi\) , an equation

\[
(\mathbf {i} _ {1}: \mathbb {I}, \dots , \mathbf {i} _ {n}: \mathbb {I}) \rightarrow \neg (\mathbf {r} (\mathbf {i} _ {1}, \dots , \mathbf {i} _ {n})) \equiv \phi (\mathbf {r}) (\neg (\mathbf {i} _ {1}), \dots , \neg (\mathbf {i} _ {n})): \mathbb {I}.
\]

▶ Example 26. The interval theory  \( Rev_{\phi}\Phi_{cart} \)  for  \( \phi:1\cong1 \)  consists simply of the operator  \( \neg:I\to I \)  and equations  \( \neg0\equiv1:I,\neg1\equiv0:I \) , and  \( (\mathbf{i}:\mathbb{I})\to\neg(\neg(\mathbf{i}))\equiv\mathbf{i}:\mathbb{I} \) . The interval theory  \( Rev_{\phi}\Phi_{DL} \) , for the isomorphism  \( \phi:\Phi_{DL}\cong\Phi_{DL} \)  from Example 24, is the algebraic theory of a De Morgan algebra bounded by 0 and 1.
▶ Definition 27 (Twist interpretation of the interval). For a self-dual interval theory  \( (\Phi, \phi) \) , we define a representable map functor  \( T: \mathbb{INT}[\mathrm{Rev}_{\phi}\Phi] \to \mathbb{INT}[\Phi] \)  by the following interpretation:

1. On sorts, we set  \( T\mathbb{I} := I \times I \) .

2. We interpret 0 as (0,1) and 1 as (1,0).

3. We interpret each \(\mathbf{r}:(\mathbf{i}_1:\mathbb{I},\ldots ,\mathbf{i}_n:\mathbb{I})\to \mathbb{I}\) in \(\Phi\) by

\[
\operatorname{Tr} \left(\left(\mathrm{i} _ {1 0}, \mathrm{i} _ {1 1}\right), \dots , \left(\mathrm{i} _ {n 0}, \mathrm{i} _ {n 1}\right)\right) := \left(\mathbf {r} \left(\mathrm{i} _ {1 0}, \dots , \mathrm{i} _ {n 0}\right), \phi (\mathbf {r}) \left(\mathrm{i} _ {1 1}, \dots , \mathrm{i} _ {n 1}\right)\right).
\]

4. We interpret  \( \neg \)  by  \( \mathrm{T}\neg((\mathbf{i}_{0},\mathbf{i}_{1})) := (\mathbf{i}_{1},\mathbf{i}_{0}) \) .

### 4.2 Interpreting cubical type theory

Cubical type theory being an extension of the theory of an interval, any environment  \( \Phi \)  over INT can also be regarded as an environment  \( \iota\Phi \)  over CTT, from which we can produce a new SOGAT CTT[ \( \iota\Phi \) ]: cubical type theory with the interval theory  \( \Phi \) .

We now extend T:  \( \mathbb{INT}[\mathrm{Rev}_{\phi}\Phi] \to \mathbb{INT}[\Phi] \)  for a self-dual interval theory  \( (\Phi,\phi) \)  to an interpretation T:  \( \mathbb{CTT}[\iota\mathrm{Rev}_{\phi}\Phi] \to \mathbb{CTT}[\iota\Phi] \) . The specification of this interpretation occupies the remainder of this section; we summarize in Theorem 42.

▶ Component 28 (T, sorts). We set Tl := I × I and interpret all other sorts by themselves: TTy := Ty, (TTm)(A) := Tm(A), TCof := Cof, (TTrue)(P) := True(P).
▶ Notation 29. For infix operators, we use a subscript to denote interpretation, for example writing  \( \approx_{T} \)  instead of  \( T(-\approx-) \) .
▶ Component 30 (T, interval theory). We interpret the operations of  \( Rev_{\phi}\Phi \)  in  \( CTT[\iota\Phi] \)  as in Definition 27.
▶ Component 31 (T, cofibration theory). We interpret the cofibration-forming operations as follows.

\[
\left(\mathbf {i} _ {0}, \mathbf {i} _ {1}\right) \approx_ {\mathrm{T}} \left(\mathbf {j} _ {0}, \mathbf {j} _ {1}\right) := \left(\mathbf {i} _ {0} \approx \mathbf {j} _ {0}\right) \cap \left(\mathbf {i} _ {1} \approx \mathbf {j} _ {1}\right)
\]

\[
\mathrm{T} \top := \top
\]

\[
\mathrm{P} \cap_ {\mathrm{T}} \mathrm{Q} := \mathrm{P} \cap \mathrm{Q}
\]

\[
\mathrm{T} \bot := \bot
\]

\[
\mathrm{P} \cup_ {\mathrm{T}} \mathrm{Q} := \mathrm{P} \cup \mathrm{Q}
\]

These definitions validate the associated axioms for the True judgment. We interpret the  \( elim_{\perp}^{Ty} \) ,  \( elim_{\perp}^{Tm} \) ,  \( elim_{\cup}^{Ty} \) , and  \( elim_{\cup}^{Tm} \)  eliminators as themselves.

14

Eliminating reversals from cubical type theories

▶ Component 32 (T, filling). We interpret filling by iterated filling, first in one component of the interval variable and then in the other, defining  \( \text{Tfill}(A, P, a, (j_0, j_1), a_0, (k_0, k_1)) \)  to be

\[
\operatorname{fill} ^ {\mathrm{j} _ {1} \rightarrow \mathrm{k} _ {1}} (\langle \mathrm{i} _ {1} \rangle \mathrm{A} (\mathrm{k} _ {0}, \mathrm{i} _ {1}), [ \mathrm{P} \mapsto \langle \mathrm{i} _ {1} \rangle \mathrm{a} (\mathrm{k} _ {0}, \mathrm{i} _ {1}) ], \operatorname{fill} ^ {\mathrm{j} _ {0} \rightarrow \mathrm{k} _ {0}} (\langle \mathrm{i} _ {0} \rangle \mathrm{A} (\mathrm{i} _ {0}, \mathrm{j} _ {1}), [ \mathrm{P} \mapsto \langle \mathrm{i} _ {0} \rangle \mathrm{a} (\mathrm{i} _ {0}, \mathrm{j} _ {1}) ], \mathrm{a} _ {0})).
\]

We interpret type formers that do not involve the interval, namely  \( \Sigma \)  and  \( \Pi \)  types, identity types, and U and El, as themselves. This leaves path types, glue types, and suspensions. We interpret the path type as a type of squares with fixed values at the coordinates  \( T0 = (0, 1) \)  and  \( T1 = (1, 0) \) , encoded as an iterated path type consisting of the two unfixed points at  \( (0, 0) \)  and  \( (1, 1) \) , four 1-dimensional paths forming a boundary, and a 2-dimensional path relating them.

▶ Component 33 (T, path types). We define TPath(A, a01, a10) to be the iterated path type

\[
\begin{array}{l} \Sigma \mathrm{a} _ {0 0}: \mathrm{A} (0, 0). \Sigma \mathrm{a} _ {1 1}: \mathrm{A} (1, 1). \\ \Sigma \mathrm{p} _ {\bullet 0}: \text {Path} (\langle \mathrm{i} _ {0} \rangle \mathrm{A} (\mathrm{i} _ {0}, 0), \mathrm{a} _ {0 0}, \mathrm{a} _ {1 0}). \Sigma \mathrm{p} _ {\bullet 1}: \text {Path} (\langle \mathrm{i} _ {0} \rangle \mathrm{A} (\mathrm{i} _ {0}, 1), \mathrm{a} _ {0 1}, \mathrm{a} _ {1 1}). \\ \Sigma \mathrm{p} _ {0 \bullet}: \text {Path} (\langle \mathrm{i} _ {1} \rangle \mathrm{A} (0, \mathrm{i} _ {1}), \mathrm{a} _ {0 0}, \mathrm{a} _ {0 1}). \Sigma \mathrm{p} _ {1 \bullet}: \text {Path} (\langle \mathrm{i} _ {1} \rangle \mathrm{A} (1, \mathrm{i} _ {1}), \mathrm{a} _ {1 0}, \mathrm{a} _ {1 1}). \\ \operatorname{Path} \left(\left\langle \mathrm{i} _ {0} \right\rangle \operatorname{Path} \left(\left\langle \mathrm{i} _ {1} \right\rangle \mathrm{A} \left(\mathrm{i} _ {0}, \mathrm{i} _ {1}\right), \mathrm{p} _ {\bullet 0} @ \mathrm{i} _ {0}, \mathrm{p} _ {\bullet 1} @ \mathrm{i} _ {0}\right), \mathrm{p} _ {0 \bullet}, \mathrm{p} _ {1 \bullet}\right) \\ \end{array}
\]

and set  \( \mathrm{T}\lambda^{\mathbb{I}}(\mathbf{a}):=(\_,\_,\_,\_,\_,\lambda\mathbf{i}_{0}.\lambda\mathbf{i}_{1}.\mathbf{a}(\mathbf{i}_{0},\mathbf{i}_{1})) \)  and  \( t\otimes_{T}(\mathbf{i}_{0},\mathbf{i}_{1}):=t.6\otimes\mathbf{i}_{0}\otimes\mathbf{i}_{1} \) , where the first five components in  \( T\lambda^{I} \)  are determined by the final one.

We write \(\mathrm{T}\lambda \mathrm{i}_0,\mathrm{i}_1.a\) as shorthand for \(\mathrm{T}\lambda^{\mathbb{I}}(\langle \mathrm{i}_0,\mathrm{i}_1\rangle a)\).

Remark 34. This iterated path type could be naturally expressed as an extension type. Introduced by Riehl and Shulman for simplicial type theory [28, §2.2] and discussed by Angiuli [1, §3.5] in the context of cubical type theory, these are types of \( n \)-cubes with fixed values on some cofibration. In a theory with these types, TPath could be defined as an extension type over the cofibration in two variables \( \mathbf{i}_0: \mathbb{I}, \mathbf{i}_1: \mathbb{I} \vdash (\mathbf{i}_0 \approx 0 \cap \mathbf{i}_1 \approx 1) \cup (\mathbf{i}_0 \approx 1 \cap \mathbf{i}_1 \approx 0) \).

To interpret glue and suspension types, we need to convert between inhabitants of  \( \text{Path}(\mathbb{C}, \mathbb{c}_{0}, \mathbb{c}_{1}) \)  and inhabitants of  \( \text{TPath}(\langle\mathbf{i}_{0}, \mathbf{i}_{1}\rangle\mathbb{C}(\mathbf{i}_{0}), \mathbb{c}_{0}, \mathbb{c}_{1}) \) . First, the easy direction:

▶ Notation 35. Over the environment ( \( [C: I \to Ty, c_{0}: C(0), c_{1}: C(1)], p: Path(C, c_{0}, c_{1}) \) ), we define thicken(p) := Tλi₀, i₁.p @ i₀ : TPath( \( \langle i_{0}, i_{1} \rangle C(i_{0}), c_{0}, c_{1} \) ).

For the inverse, we extract the “anti-diagonal” of a square by inverting it along one axis—a standard construction using the filling operation—and then extracting the diagonal.

▶ Definition 36 (Path inversion). Over the environment ([C : Ty, c₀ c₁ : C], p : c₀ ∼ᶜ c₁), we define sym(p) := λi.fill¹→⁰(⟨_)C, [i ≈ 0 ↦ ⟨_)c₁, i ≈ 1 ↦ ⟨j⟩p @ j], c₁) : c₁ ∼ᶜ c₀.

▶ Definition 37. Over ([C : I → Ty, c₀ : C(0), c₁ : C(1)], q : TPath(⟨i₀, i₁⟩C(i₀), c₀, c₁)), we define anti(q) := λi.sym(⟨j⟩q @T (i, j)) @ i : Path(C, c₀, c₁).

To show that these constitute an equivalence, we use the contractibility of dependent singleton types:

▶ Proposition 38. Over the environment (C : I → Ty, c₀ : C(0)), we have a term of type isContr(Σc₁:C(1).Path(C, c₀, c₁)).

Proof (cf. [1, §3.2]). For the center of contraction, take the pair  \( s_{0} := (\_, \lambda i.\text{coe}^{0 \to i}(C, c_{0})) \)  (whose first component is determined by its second). Given a singleton s, we have a path  \( \lambda j.(\_, \lambda i.\text{fill}^{0 \to i}(C, [j \approx 0 \mapsto \langle k \rangle s_{0} @ k, j \approx 1 \mapsto \langle k \rangle s @ k], c_{0})) \)  from  \( s_{0} \)  to s.

E. Cavallo and C. Sattler

15

▶ Lemma 39. Over the environment (C : Ty, c₀ : C, c₁ : C), the function λp.thicken(p) : Path(C, c₀, c₁) → TPath(⟨i₀, i₁⟩C(i₀), c₀, c₁) is an equivalence.

Proof. Our proof of Proposition 38 uses only constructs on which we have already defined T. Thus we can mechanically derive from it a term of type TisContr(Σd₁:D(1,0).TPath(D,d₀,d₁)) over (D : I × I → Ty, d₀ : D(0,1)). Using Definition 37, we can go from TisContr to isContr. Taking D(i₀,i₁) := C(i₀) and d₀ := c₀ gives isContr(Σc₁:C(1).TPath(⟨i₀,i₁⟩C(i₀),c₀,c₁)). Thus λs.(s.1,thicken(s.2)) : Σc₁:C(1).Path(C,c₀,c₁) → Σc₁:C(1).TPath(⟨i₀,i₁⟩C(i₀),c₀,c₁) is a map between contractible types and therefore an equivalence. It follows [39, Theorem 4.7.7] that it is also a fiberwise equivalence.

We can use Lemma 39 inside the definition of equivalence to construct TGlue.

▶ Component 40 (T, glue). Over (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃_T A), define TGlue(A, P, T, e) := Glue(A, P, T, ê) where ê is derived from e by using Lemma 39 to replace each use of TPath with Path. Set Tglue(a, t) := glue(a, t) and Tunglue(g) := unglue(g).

The interpretation of suspensions is similar, but we use thicken and anti more directly.

▶ Component 41 (T, suspension). Define

|  TSusp(A) | := | Susp(A) | Tmerid(a) | := | thicken(merid(a))  |
| --- | --- | --- | --- | --- | --- |
|  Tnorth | := | north | Telim(C, n, s, m, t) | := | elim(C, n, s, ⟨a⟩anti(m(a)), t)  |
|  Tsouth | := | south |  |  |   |

For Tmeridβ(C, n, s, m, a), we compose cong_thicken(meridβ(C, n, s, ⟨a⟩thicken⁻¹(m(a)), a)) with the path thicken(thicken⁻¹(q)) ∼ q, using that thicken is an equivalence, then thicken the composed path to get a T-path.

This completes the definition of T, as summarized in the following theorem. We record that it preserves the constructs of MLTT_Σ,Id and the cofibration judgments for future use.

▶ Theorem 42. For every self-dual interval theory (Φ, φ), there is a representable map functor T: CTT[ℓRev_φΦ] → CTT[ℓΦ] in the coslice (MLTT_Σ,Id,U + COF)/RMC.

## 5 Spans

Abstracting from the particular case of T, we now develop tools—span RMCs and the span interpretation between suitable RMC functors F, G: CTT[ℓΦ] → CTT[ℓΨ]—that we use in §6 to prove that certain morphisms of models induced by RMC functors are weak equivalences. This construction at the level of RMCs is inspired by and resembles path object constructions at the level of models [22, §5], as well as Tabareau, Tanter, and Sozeau's univalent parametricity translation for the Calculus of Inductive Constructions [35].

### 5.1 The representable map category of spans

We write Span(C) for the category of spans in a category C, i.e., the category of functors from the diagram category {0 ← r → 1} into C. Given X ∈ Span(C), we write d⁰: X_r → X₀ and d¹: X_r → X₁ for its two projections.

▶ Proposition 43. If ℝ is an RMC, then Span(ℝ) is an RMC when equipped with the class of levelwise representable maps.

16

Eliminating reversals from cubical type theories

Proof. As a functor category, R has finite limits computed pointwise in R. In particular, the fact that representable maps are closed under pullback in R implies the same of Span(R).

It remains to show that the representable maps in Span(R) are exponentiable. Let f: Z → Y and p: Y → X be maps in Span(R) and suppose p is representable. As p₀ and p₁ are exponentiable, we have dependent products g₀ := (p₀)₊f₀: Πₚ₀Z₀ → X₀ and g₁ := (p₁)₊f₁: Πₚ₁Z₁ → X₁. Write k for the composite

$$\begin{array}{c} Y_{\mathrm{r}} \times_{X_0 \times X_1} (\Pi_{p_0} Z_0 \times \Pi_{p_1} Z_1) \\ \Biggl\downarrow^g \\ Y_{\mathrm{r}} \times_{Y_0 \times Y_1} ((Y_0 \times_{X_0} \Pi_{p_0} Z_0) \times (Y_1 \times_{X_1} \Pi_{p_1} Z_1)) \xrightarrow{Y_{\mathrm{r}} \times_{Y_0 \times Y_1} (\epsilon_{Z_0} \times \epsilon_{Z_1}))} Y_{\mathrm{r}} \times_{Y_0 \times Y_1} Z_0 \times Z_1 \end{array}$$

induced by the counits of the (pullback, pushforward) adjunction, and write q for the (representable) pullback

$$\begin{array}{c} Y_{\mathrm{r}} \times_{X_0 \times X_1} (\Pi_{p_0} Z_0 \times \Pi_{p_1} Z_1) \longrightarrow Y_{\mathrm{r}} \\ \downarrow^q \\ X_{\mathrm{r}} \times_{X_0 \times X_1} (\Pi_{p_0} Z_0 \times \Pi_{p_1} Z_1) \longrightarrow X_{\mathrm{r}}. \end{array}$$

Writing the components of q₊k*(fᵣ, (d⁰, d¹)): Π_q k* Zᵣ → Xᵣ ×_{X₀×X₁} (Πₚ₀Z₀ × Πₚ₁Z₁) as ⟨gᵣ, d⁰, d¹⟩, the morphism of spans

$$\begin{array}{c} \Pi_{p_0} Z_0 \xleftarrow{d^0} \Pi_q k^* Z_r \xrightarrow{d^1} \Pi_{p_1} Z_1 \\ \downarrow^g \\ X_0 \xleftarrow{d^0} X_r \xrightarrow{d^1} X_1 \end{array}$$

is a pushforward of f along p.

By definition, the projections π₀, π₁: Span(R) → R are RMC functors. Restricting our attention now to MLTTΣ,Id, we define an RMC functor Refl fitting in the diagram

$$\begin{array}{c} \text{MLTT}_{\Sigma,\text{Id}} \\ \downarrow^1 \\ \text{Refl} \\ \text{MLTT}_{\Sigma,\text{Id}} \xleftarrow{\pi_0} \text{Span}(\text{MLTT}_{\Sigma,\text{Id}}) \xrightarrow{\pi_1} \text{MLTT}_{\Sigma,\text{Id}} \end{array}$$

by giving an interpretation. For Φ ∈ MLTTΣ,Id, we write the span ReflΦ as Φ ← dΦ⁰ → PΦ → Φ, i.e., with P: MLTTΣ,Id → MLTTΣ,Id denoting the composite of Refl with the apex projection.

To interpret the type and term judgments, we will use the environment Ty^∞ of 1-to-1 correspondences from Definition 10.

- ▶ Definition 44. Write Tm^∞ := ((A, A', A̅, ···) : Ty^∞, a : A, a' : A', ā : Ā(a, a')) ∈ MLTTΣ,Id and d⁰, d¹: Tm^∞ → Tm for the instantiations projecting (A, a) and (A', a') respectively.
- ▶ Component 45 (Refl, sorts). For sorts, we define ReflTy := {Ty ← d⁰ → Ty^∞ → d¹ → Ty} and ReflTm := {Tm ← d⁰ → Tm^∞ → d¹ → Tm}, with ReflπTm: ReflTy → ReflTm the evident projection.

Defining Refl for a type former T: Φ ⇒ Ty now amounts to giving, over the environment (p : PΦ), a 1-to-1 correspondence R(p, −, −) between T(dΦ⁰(p)) and T(dΦ¹(p)). Similarly, interpreting a term former t: (x : Φ) ⇒ Tm(I(x)) amounts to giving over (p : PΦ) an inhabitant of R(p, t(dΦ⁰(p)), t(dΦ¹(p))).

E. Cavallo and C. Sattler

17

▶ Component 46 (Refl, unit type). We interpret the unit type former by the 1-to-1 correspondence RUnit(_, _, _) = Unit and its unique inhabitant by the unique witness.
▶ Component 47 (Refl, Σ types). In the environment consisting of A : Ty, A' : Ty, a 1-to-1 correspondence  \( \overline{A} : (A, A') \to Ty \) , families B : A → Ty, B' : A' → Ty, and a family of 1-to-1 correspondences  \( \overline{B} : ([a : A, a' : A'], \overline{a} : \overline{A}(a, a'), b : B(a), b' : B'(a')) \to Ty \) , we define RΣ at s : Σ(A, B) and s' : Σ(A', B') to be Σ \( \overline{a} \) :  \( \overline{A}(s.1, s'.1) \) .  \( \overline{B}(\overline{a}, s.2, s'.2) \) . We interpret pairing and projection by pairing and projection in this Σ type.
▶ Component 48 (Refl, identity types). In the environment consisting of A : Ty, A' : Ty, a 1-to-1 correspondence  \( \overline{A} : (A, A') \to Ty \) , terms  \( a_{0} \)   \( a_{1} : A \)  and  \( a_{0}' \)   \( a_{1}' : A' \) , and  \( \overline{a}_{0} : \overline{A}(a_{0}, a_{0}') \)  and  \( \overline{a}_{1} : \overline{A}(a_{1}, a_{1}') \) , we define RId at p :  \( a_{0} \asymp a_{1} \)  and  \( p' : a_{0}' \asymp a_{1}' \)  to be the type of identities between  \( \overline{a}_{0} : \overline{A}(a_{0}, a_{0}') \)  and  \( \overline{a}_{1} : \overline{A}(a_{1}, a_{1}') \)  over p and  \( p' \) , i.e., the type of identities between the transport of  \( \overline{a}_{0} \)  along these identities and  \( \overline{a}_{1} \) .

This completes the definition of Refl:  \( MLTT_{\Sigma,Id} \to \text{Span}(\text{MLTT}_{\Sigma,\text{Id}}) \) . Given an RMC  \( i: MLTT_{\Sigma,Id} \to R \)  under  \( MLTT_{\Sigma,Id} \) , we can now regard  \( \text{Span}(\mathbb{R}) \)  as an RMC under  \( MLTT_{\Sigma,Id} \)  by way of the composite  \( \text{Span}(i) \circ \text{Refl}: MLTT_{\Sigma,Id} \to \text{Span}(\mathbb{R}) \) . In particular, we have  \( \mathbf{0}_{\text{Span}(\mathbb{R})} \in \text{Mod}(\text{MLTT}_{\Sigma,\text{Id}}) \)  as in Definition 13.

▶ Proposition 49. For any \(i\colon \mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}}\to \mathbb{R}\), the morphisms \(\mathbf{0}_{\pi_0},\mathbf{0}_{\pi_1}\colon \mathbf{0}_{\mathrm{Span}(\mathbb{R})}\to \mathbf{0}_{\mathbb{R}}\) in \(\mathbf{Mod}(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}})\) are weak equivalences.

Proof. We consider \(\pi_0\colon \mathrm{Span}(\mathbb{R})\to \mathbb{R}\), the case of \(\pi_1\) being symmetric. An object of \(\Gamma \in \mathbf{0}_{\mathrm{Span}(\mathbb{R})}(\star)\) is a span \(\{\Gamma_0\stackrel {d^0}{\leftarrow}\Gamma_{\mathrm{r}}\stackrel {d^1}{\rightarrow}\Gamma_1\}\) obtained by iterated context extension of the terminal span with respect to the representable map \(\mathsf{Tm}^{\simeq}\to \mathsf{Ty}^{\simeq}\) as described in Definition 9. It follows that \(\Gamma_0,\Gamma_1\), and \(\Gamma_{\mathrm{r}}\) are contexts in \(\mathbb{R}\), i.e., environments of term hypotheses, and that we have instantiations \(\eta^0\colon \Gamma_0\to \Gamma_{\mathrm{r}}\) and \(\eta^1\colon \Gamma_1\to \Gamma_{\mathrm{r}}\) that are homotopy inverses of \(d^0\colon \Gamma_{\mathrm{r}}\to \Gamma_0\) and \(d^{1}\colon \Gamma_{\mathrm{r}}\to \Gamma_{1}\) at each entry. To show weak type lifting for \(\pi_0\colon \mathrm{Span}(\mathbb{R})\to \mathbb{R}\), we are given \(B\colon \Gamma_0\to \mathsf{Ty}\) in \(\mathbb{R}\) and must construct an \(A\colon \Gamma \to \mathrm{ReflTy}\) in \(\mathrm{Span}(\mathbb{R})\) for which \(A_0\) is equivalent to \(B\). We have

\[
\begin{array}{c} \Gamma_ {0} \xleftarrow {d ^ {0}} \Gamma_ {\mathrm{r}} \xrightarrow {d ^ {1}} \Gamma_ {1} \\ B \Big \downarrow \\ \mathsf {T y} \xleftarrow [ d ^ {0} ]{} \mathsf {T y} ^ {\simeq} \xrightarrow [ d ^ {1} ]{} \mathsf {T y} \end{array}
\]

and, since  \( d^{0}\eta^{1}d^{1} \)  is homotopic to  \( d^{0} \)  at each component, we can find a map  \( \Gamma_{r}\to Ty^{\simeq} \)  that makes the diagram commute. Taking the result as our A, we have not only an equivalence from  \( A_{0} \)  to B but an equality. The construction of term lifting is analogous.

### 5.2 Relating interpretations using spans

For this section, we fix two RMC functors \(F, G\colon \mathbb{C}\mathrm{TT}[\iota \Phi] \to \mathbb{C}\mathrm{TT}[\iota \Psi]\) in the coslice under the combined sub-SOGAT \(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id},\mathrm{U}} + \mathrm{COF}\), where \(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id},\mathrm{U}}\) is the extension of \(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}}\) by a universe \(\mathsf{U}\) with \(\mathsf{EI}\). We construct a third RMC functor \(\mathrm{S}_G^F\colon \mathbb{C}\mathrm{TT}[\iota \Phi] \to \mathrm{Span}(\mathbb{C}\mathrm{TT}[\iota \Psi])\) in the coslice under \(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}}\) that fits in the diagram

\[
\begin{array}{c} \mathbb {C} \mathrm{TT} [ \iota \Phi ] \\ \Big \downarrow_ {F} \quad \Big \downarrow_ {\mathrm{S} _ {G} ^ {F}} \quad \Big \downarrow_ {G} \\ \mathbb {C} \mathrm{TT} [ \iota \Psi ] \xleftarrow [ \pi_ {0} ]{} \operatorname{Span} (\mathbb {C} \mathrm{TT} [ \iota \Psi ]) \xrightarrow [ \pi_ {1} ]{} \mathbb {C} \mathrm{TT} [ \iota \Psi ]. \end{array}
\]

18

Eliminating reversals from cubical type theories

The effect of this functor, which we exploit in §6, is to show that \( F \) and \( G \) are approximately "the same". Note that we need to know very little about \( F \) and \( G \) to obtain \( S_G^F \): this reflects that the constructs of \( \mathbb{C}\mathrm{TT}[\iota \Phi] \) are all characterized up to equivalence by their universal properties, so an interpretation has little choice in where to send them. It is key here that we are looking at second-order models, i.e., RMC functors; we would not have the same result for morphisms of first-order models.

For \(\Theta \in \mathbb{C}\mathrm{TT}\), we write the span \(S_G^F\Theta\) as \(F\Theta \stackrel{d_0}{\leftrightarrow} M_G^F\Theta \stackrel{d_1}{\rightarrow} G\Theta\). Because we intend \(S_G^F\) to be a morphism in the coslice under \(\mathbb{MLTT}_{\Sigma,\mathrm{Id}}\), the interpretations of the constructs of \(\mathbb{MLTT}_{\Sigma,\mathrm{Id}}\) are determined by the definition of Refl from the previous section.

From this point until the summary statement Theorem 62, we omit the annotations on \(\mathrm{S}_G^F\) and \(\mathrm{M}_G^F\) and simply write S and M.

▶ Component 50 (S, sorts). Set STy := {Ty \( \stackrel{d^{0}}{\leftarrow} \) Ty \( \stackrel{d^{1}}{\rightarrow} \) Ty} and STm := {Tm \( \stackrel{d^{0}}{\leftarrow} \) Tm \( \stackrel{d^{1}}{\rightarrow} \) Tm} as required by the definition of Refl. For the remaining sorts:

1. Set \(\mathrm{S}\mathbb{I}:=\{F\mathbb{I}\stackrel{d^{0}}{\leftarrow}F\mathbb{I}\times G\mathbb{I}\stackrel{d^{1}}{\rightarrow}G\mathbb{I}\}\).
2. Set MCof := (P P' \(\overline{\mathbb{P}}\): Cof, [\(\overline{\mathbb{P}}\to\mathbb{P},\overline{\mathbb{P}}\to\mathbb{P}'\)]) with \(d_{\mathrm{Cof}}^{0}, d_{\mathrm{Cof}}^{1}\) projecting P and P' respectively.
3. Set MTrue := ((P, P', \(\overline{\mathbb{P}}\)): MCof, \(\overline{\mathbb{P}}\)) with \(d_{\text{True}}^{0}, d_{\text{True}}^{1}\) applying the implications \(\overline{\mathbb{P}} \to \mathbb{P}\) and \(\overline{\mathbb{P}} \to \mathbb{P}'\), and define \(\mathrm{M}\pi_{\text{True}}\) to be the evident projection.

▶ Component 51 (S, interval theory). By definition of SⅡ, the interpretation of the interval theory is forced by F and G. Unfolding, the interpretation Mf of each operation  \( f: I^{n} \to I \)  of the interval theory is  \( (F\mathbb{I} \times G\mathbb{I})^{n} \cong F\mathbb{I}^{n} \times G\mathbb{I}^{n} \stackrel{Ff \times Gf}{\longrightarrow} F\mathbb{I} \times G\mathbb{I} \) .

▶ Component 52 (S, cofibration theory). We interpret the cofibration operations as follows.

\[
\begin{array}{l} (\mathrm{i}, \mathrm{x}) \approx_ {\mathrm{M}} (\mathrm{j}, \mathrm{y}) := (\mathrm{i} \approx_ {F} \mathrm{j}, \mathrm{x} \approx_ {G} \mathrm{y}, (\mathrm{i} \approx_ {F} \mathrm{j}) \cap (\mathrm{x} \approx_ {G} \mathrm{y})) \\ \mathrm{M} \top := (F \top , G \top , \top) \\ (\mathrm{P}, \mathrm{P} ^ {\prime}, \overline {{\mathrm{P}}}) \cap_ {\mathrm{M}} (\mathrm{Q}, \mathrm{Q} ^ {\prime}, \overline {{\mathrm{Q}}}) := (\mathrm{P} \cap_ {F} \mathrm{Q}, \mathrm{P} ^ {\prime} \cap_ {G} \mathrm{Q} ^ {\prime}, \overline {{\mathrm{P}}} \cap \overline {{\mathrm{Q}}}) \\ \mathrm{M} \bot := (F \bot , G \bot , \bot) \\ (\mathrm{P}, \mathrm{P} ^ {\prime}, \overline {{\mathrm{P}}}) \cup_ {\mathrm{M}} (\mathrm{Q}, \mathrm{Q} ^ {\prime}, \overline {{\mathrm{Q}}}) := (\mathrm{P} \cup_ {F} \mathrm{Q}, \mathrm{P} ^ {\prime} \cup_ {G} \mathrm{Q} ^ {\prime}, \overline {{\mathrm{P}}} \cup \overline {{\mathrm{Q}}}) \\ \end{array}
\]

The axioms for cofibrations ensure that these definitions preserve the implicit requirement that for  \( (\mathsf{P},\mathsf{P}^{\prime},\overline{\mathsf{P}}) \) : MCof we have  \( \overline{P}\to P \)  and  \( \overline{P}\to P^{\prime} \) . We use this to interpret the  \( elim_{\cup}^{Ty} \)  and  \( elim_{\cup}^{Tm} \)  eliminators. For  \( elim_{\cup}^{Ty} \) , for example, we are given  \( (\mathsf{P},\mathsf{P}^{\prime},\overline{\mathsf{P}}) \) : MCof,  \( (\mathsf{Q},\mathsf{Q}^{\prime},\overline{\mathsf{Q}}) \) : MCof, compatible A: [P] → Ty and B: [Q] → Ty, compatible A': [P'] → Ty and B': [Q'] → Ty, and compatible 1-to-1 correspondences  \( \overline{\mathsf{A}} \) : ([P], A, A') → Ty and  \( \overline{\mathsf{B}} \) : ([Q], B, B') → Ty, and we need to extend these to a 1-to-1 correspondence between  \( Felim_{\cup}^{Ty}(P,Q,A,B) \)  and  \( Gelim_{\cup}^{Ty}(P^{\prime},Q^{\prime},A^{\prime},B^{\prime}) \)  assuming  \( \overline{P}\cup\overline{Q} \) . To do so we case on  \( \overline{P}\cup\overline{Q} \)  and use that we either have both P and P' or both Q and Q' as a consequence.

▶ Component 53 (S, filling). To define Sfill, we are given inputs

|  A | : \( F\mathbb{I} \to \text{Ty} \) | \( (j, y) \) | : \( \text{M}\mathbb{I} \)  |
| --- | --- | --- | --- |
|  \( A' \) | : \( G\mathbb{I} \to \text{Ty} \) | \( a_0 \) | : \( A(j) \)  |
|  \( \overline{A} \) | : \( (i : F\mathbb{I}, x : G\mathbb{I}, a : A(i), a' : A'(x)) \to \text{Ty} \) | \( a'_0 \) | : \( A'(y) \)  |
|  \( (P, P', \overline{P}) \) | : \( \text{MCof} \) | \( \overline{a}_0 \) | : \( \overline{A}(j, y, a_0, a'_0) \)  |
|  \( a \) | : \( (i : F\mathbb{I}, P) \to A(i) \) | \( (k, z) \) | : \( \text{M}\mathbb{I} \)  |
|  \( a' \) | : \( (x : G\mathbb{I}, P') \to A'(x) \) |  |   |
|  \( \overline{a} \) | : \( (i : F\mathbb{I}, x : G\mathbb{I}, \overline{P}) \to \overline{A}(i, x, a(i), a'(x)) \) |  |   |

E. Cavallo and C. Sattler

19

satisfying $\mathsf{P} \to \mathsf{a}(j) \equiv \mathsf{a}_0 : \mathsf{A}(j)$, $\mathsf{P}' \to \mathsf{a}'(y) \equiv \mathsf{a}_0' : \mathsf{A}'(y)$, and $\overline{\mathsf{P}} \to \overline{\mathsf{a}}(j, y) \equiv \overline{\mathsf{a}}_0 : \overline{\mathsf{A}}(\mathsf{a}_0, \mathsf{a}_0')$. Abbreviating $\mathsf{a}_+(\mathsf{k}) := F\mathrm{fill}^{\mathrm{j} \to \mathrm{k}}(\mathsf{A}, [\mathsf{P} \mapsto \mathsf{a}], \mathsf{a}_0)$ and $\mathsf{a}_+'(\mathsf{z}) := G\mathrm{fill}^{\mathrm{y} \to \mathrm{z}}(\mathsf{A}', [\mathsf{P}' \mapsto \mathsf{a}'], \mathsf{a}_0')$, we must exhibit a term of type $\overline{\mathsf{A}}(\mathsf{k}, \mathsf{z}, \mathsf{a}_+(\mathsf{k}), \mathsf{a}_+'(\mathsf{z}))$. We take the iterated filling expression

$$
\begin{array}{l}
G\mathrm{fill}^{\mathrm{y} \to \mathrm{z}}(\langle \mathrm{x} \rangle \overline{\mathsf{A}}(\mathrm{k}, \mathrm{x}, \mathrm{a}_+(\mathrm{k}), \mathrm{a}_+'(\mathrm{x})), [\overline{\mathsf{P}} \mapsto \langle \mathrm{x} \rangle \overline{\mathsf{a}}(\mathrm{k}, \mathrm{x})], \\
F\mathrm{fill}^{\mathrm{j} \to \mathrm{k}}(\langle \mathrm{i} \rangle \overline{\mathsf{A}}(\mathrm{i}, \mathrm{y}, \mathrm{a}_+(\mathrm{i}), \mathrm{a}_0'), [\overline{\mathsf{P}} \mapsto \langle \mathrm{i} \rangle \overline{\mathsf{a}}(\mathrm{i}, \mathrm{y})], \overline{\mathsf{a}}_0)).
\end{array}
$$

▶ **Component 54** (S, $\Pi$ types). In the environment consisting of $\mathsf{A} : \mathsf{Ty}$, $\mathsf{A}' : \mathsf{Ty}$, a 1-to-1 correspondence $\overline{\mathsf{A}} : (\mathsf{A}, \mathsf{A}') \to \mathsf{Ty}$, families $\mathsf{B} : \mathsf{A} \to \mathsf{Ty}$, $\mathsf{B}' : \mathsf{A}' \to \mathsf{Ty}$, and 1-to-1 correspondences $\overline{\mathsf{B}} : ([\mathsf{a} : \mathsf{A}, \mathsf{a}' : \mathsf{A}'], \overline{\mathsf{a}} : \overline{\mathsf{A}}(\mathsf{a}, \mathsf{a}'), \mathsf{b} : \mathsf{B}(\mathsf{a}), \mathsf{b}' : \mathsf{B}'(\mathsf{a}')) \to \mathsf{Ty}$, we take the relation sending $\mathsf{f} : F\Pi(\mathsf{A}, \mathsf{B})$ and $\mathsf{f}' : G\Pi(\mathsf{A}', \mathsf{B}')$ to $\Pi\mathsf{a} : \mathsf{A}$. $\Pi\mathsf{a}' : \mathsf{A}'$. $\Pi\overline{\mathsf{a}} : \overline{\mathsf{A}}(\mathsf{a}, \mathsf{a}')$. $\overline{\mathsf{B}}(\overline{\mathsf{a}}, \mathsf{f}(\mathsf{a}), \mathsf{f}'(\mathsf{a}'))$.

For Path types, we exploit the fact that we can convert between non-dependent Path, $F$Path, and $G$Path types, which follows from the fact that both types support coercion.

▶ **Lemma 55.** Over $([\mathsf{C} : \mathsf{Ty}, \mathsf{c}_0 : \mathsf{C}, \mathsf{c}_1 : \mathsf{C}], \mathsf{p} : F\mathrm{Path}(\langle \_\rangle \mathsf{C}, \mathsf{c}_0, \mathsf{c}_1))$, we have a term $\mathrm{decode}^F(\mathsf{p}) : \mathsf{c}_0 \sim^{\mathsf{C}} \mathsf{c}_1$.

**Proof.** We have $F\mathrm{coe} : (\mathsf{A} : (\mathsf{x} : F\mathbb{I}) \to \mathsf{Ty}, \mathsf{y} : F\mathbb{I}, \mathsf{a}_0 : \mathsf{A}(\mathsf{y}), \mathsf{z} : F\mathbb{I}) \Rightarrow \mathsf{A}(\mathsf{z})$, and instantiating with the arguments $(\langle \mathsf{x} \rangle (\mathsf{c}_0 \sim^{\mathsf{C}} \mathsf{p} \otimes_F \mathsf{x}), F0, (\lambda_-, \mathsf{c}_0), F1)$ yields the desired expression.

▶ **Corollary 56.** Over $(\mathsf{C} : F\mathbb{I} \to \mathsf{Ty}, \mathsf{c}_0 : \mathsf{C}(F0))$, $\Sigma\mathsf{c}_1 : \mathsf{C}(F1).F\mathrm{Path}(\mathsf{C}, \mathsf{c}_0, \mathsf{c}_1)$ is contractible.

**Proof.** Applying $F$ to singleton contractibility (Proposition 38), we get over the environment $(\mathsf{C} : F\mathbb{I} \to \mathsf{Ty}, \mathsf{c}_0 : \mathsf{C}(F0))$ a term of type $F\mathrm{isContr}(F\Sigma\mathsf{c}_1 : \mathsf{C}(F1).F\mathrm{Path}(\mathsf{C}, \mathsf{c}_0, \mathsf{c}_1))$. The type formers $F\Sigma$ and $F\Pi$ satisfy the rules for $\Sigma$- and $\Pi$-types, so we can define equivalences $F\Sigma(A, B) \simeq \Sigma(A, B)$ and $F\Pi(A, B) \simeq \Pi(A, B)$. Combined with Lemma 55, we can therefore derive $\mathrm{isContr}(\Sigma\mathsf{c}_1 : \mathsf{C}(F1).F\mathrm{Path}(\mathsf{C}, \mathsf{c}_0, \mathsf{c}_1))$.

Of course, Corollary 56 also holds when we replace $F$ with $G$.

▶ **Component 57** (S, path types). To define SPath, we are given $\mathsf{A} : F\mathbb{I} \to \mathsf{Ty}$ and $\mathsf{A}' : G\mathbb{I} \to \mathsf{Ty}$ with a 1-to-1 correspondence $\overline{\mathsf{A}} : (\mathsf{i} : F\mathbb{I}, \mathsf{x} : G\mathbb{I}, \mathsf{a} : \mathsf{A}(\mathsf{i}), \mathsf{a}' : \mathsf{A}'(\mathsf{x})) \to \mathsf{Ty}$, terms $\mathsf{a}_0 : \mathsf{A}(F0)$ and $\mathsf{a}_0' : \mathsf{A}'(G0)$ with $\overline{\mathsf{a}}_{00} : \overline{\mathsf{A}}(F0, G0, \mathsf{a}_0, \mathsf{a}_0')$, and terms $\mathsf{a}_1 : \mathsf{A}(F1)$ and $\mathsf{a}_1' : \mathsf{A}'(G1)$ with $\overline{\mathsf{a}}_{11} : \overline{\mathsf{A}}(F1, G1, \mathsf{a}_1, \mathsf{a}_1')$.

We need to define a 1-to-1 correspondence between $F\mathrm{Path}(\mathsf{A}, \mathsf{a}_0, \mathsf{a}_1)$ and $G\mathrm{Path}(\mathsf{A}', \mathsf{a}_0', \mathsf{a}_1')$. We take the relation sending $\mathsf{p}$ and $\mathsf{p}'$ to the iterated $\Sigma$-type with components

$$
\begin{array}{l}
\overline{\mathsf{a}}_{10} : \overline{\mathsf{A}}(F1, G0, \mathsf{a}_1, \mathsf{a}_0'). \\
\overline{\mathsf{a}}_{01} : \overline{\mathsf{A}}(F0, G1, \mathsf{a}_0, \mathsf{a}_1'). \\
\overline{\mathsf{a}}_{\bullet 0} : F\mathrm{Path}(\langle \mathsf{i} \rangle \overline{\mathsf{A}}(\mathsf{i}, G0, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{a}_0'), \overline{\mathsf{a}}_{00}, \overline{\mathsf{a}}_{10}). \\
\overline{\mathsf{a}}_{\bullet 1} : F\mathrm{Path}(\langle \mathsf{i} \rangle \overline{\mathsf{A}}(\mathsf{i}, G1, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{a}_1'), \overline{\mathsf{a}}_{01}, \overline{\mathsf{a}}_{11}). \\
\overline{\mathsf{a}}_{0\bullet} : G\mathrm{Path}(\langle \mathsf{x} \rangle \overline{\mathsf{A}}(F0, \mathsf{x}, \mathsf{a}_0, \mathsf{p}' \otimes_G \mathsf{x}), \overline{\mathsf{a}}_{00}, \overline{\mathsf{a}}_{01}). \\
\overline{\mathsf{a}}_{1\bullet} : G\mathrm{Path}(\langle \mathsf{x} \rangle \overline{\mathsf{A}}(F1, \mathsf{x}, \mathsf{a}_1, \mathsf{p}' \otimes_G \mathsf{x}), \overline{\mathsf{a}}_{10}, \overline{\mathsf{a}}_{11}). \\
\overline{\mathsf{a}}_{\bullet\bullet} : F\mathrm{Path}(\langle \mathsf{i} \rangle G\mathrm{Path}(\langle \mathsf{x} \rangle \overline{\mathsf{A}}(\mathsf{i}, \mathsf{x}, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{p}' \otimes_G \mathsf{x}), \overline{\mathsf{a}}_{\bullet 0} \otimes_F \mathsf{i}, \overline{\mathsf{a}}_{\bullet 1} \otimes_F \mathsf{i}), \overline{\mathsf{a}}_{0\bullet}, \overline{\mathsf{a}}_{1\bullet}).
\end{array}
$$

An element consists effectively of a family of witnesses $\overline{\mathsf{a}}_{\bullet\bullet} \otimes_F \mathsf{i} \otimes_G \mathsf{x} : \overline{\mathsf{A}}(\mathsf{i}, \mathsf{x}, \mathsf{p} \otimes_F \mathsf{i}, \mathsf{p}' \otimes_G \mathsf{x})$ satisfying $\overline{\mathsf{a}}_{\bullet\bullet} \otimes_F F0 \otimes_G G0 \equiv \overline{\mathsf{a}}_{00}$ and $\overline{\mathsf{a}}_{\bullet\bullet} \otimes_F F1 \otimes_G G1 \equiv \overline{\mathsf{a}}_{11}$. We define $\mathrm{M}\lambda^{\mathbb{I}}$ and $\otimes_{\mathrm{M}}$ to be abstraction and application of such families.

It remains to check that this relation is a 1-to-1 correspondence. Fix $\mathsf{p} : F\mathrm{Path}(\mathsf{A}, \mathsf{a}_0, \mathsf{a}_1)$ and consider the type of pairs of $\mathsf{p}' : G\mathrm{Path}(\mathsf{A}', \mathsf{a}_0', \mathsf{a}_1')$ with the data (1). Given the preceding

20

Eliminating reversals from cubical type theories

data, the types of pairs  \( (\overline{\mathbf{a}}_{10},\overline{\mathbf{a}}_{\bullet0}) \)  and  \( (\overline{\mathbf{a}}_{1\bullet},\overline{\mathbf{a}}_{\bullet\bullet}) \)  as in (1) are dependent F-singletons, so contractible by Corollary 56. The type of pairs  \( (\overline{\mathbf{a}}_{01},\overline{\mathbf{a}}_{0\bullet}) \)  is likewise a dependent G-singleton and thus contractible. After contracting all of these, we are left with  \( p^{\prime}:GPath(A^{\prime},a_{0}^{\prime},a_{1}^{\prime}) \)  and  \( \overline{a}_{0\bullet}:GPath(\langle x\rangle\overline{A}(0,x,a_{0},p^{\prime}\otimes_{G}x),\overline{a}_{00},\widehat{a}_{01}) \)  where  \( \widehat{a}_{01} \)  is some expression. The type of such pairs is equivalent to  \( GPath(\langle x\rangle\Sigma a^{\prime}:A^{\prime}(x),\overline{A}(0,x,a_{0},a^{\prime}),(a_{0}^{\prime},\widehat{a}_{00}),(a_{1}^{\prime},\widehat{a}_{01})) \) , which is a GPath-type over a contractible type and thus contractible. A symmetric argument deals with the case where we fix  \( p^{\prime} \)  and allow p to vary freely.

▶ Component 58 (S, universes). Using the assumption that  \( FU = GU = U \) , we interpret the universe U by the relation sending A : U and  \( A' : U \)  to the type of U-valued 1-to-1 correspondences between A and  \( A' \) . That this relation is itself a 1-to-1 correspondence is a consequence of univalence of U [39, Theorem 5.8.4(iv)⇒(v)]. We interpret EI, again using the assumption  \( FEI(A) = GEI(A) = EI(A) \) , as extracting the 1-to-1 correspondence.

▶ Component 59 (S, glue). To define SGlue, we are given inputs

\((\mathsf{A},\mathsf{A}^{\prime},\overline{\mathsf{A}})\) : MTy e : \([\mathsf{P}]\to \mathsf{T}\simeq_{F}\mathsf{A}\)   
\((\mathsf{P},\mathsf{P}^{\prime},\overline{\mathsf{P}})\) : MCof e' : \([\mathsf{P}^{\prime}]\to \mathsf{T}^{\prime}\simeq_{G}\mathsf{A}^{\prime}\)   
T : \([\mathsf{P}]\to \mathsf{Ty}\) \(\overline{\mathsf{e}}\) : \([\overline{\mathsf{P}} ]\to \mathsf{R}_{\simeq}(\overline{\mathsf{A}},\overline{\mathsf{T}},\mathsf{e},\mathsf{e}^{\prime})\)   
\(\mathsf{T}^{\prime}\) : \([\mathsf{P}^{\prime}]\to \mathsf{Ty}\)   
\(\overline{\mathsf{T}}\) : \(([\overline{\mathsf{P}} ],\mathsf{t}:\mathsf{T},\mathsf{t}^{\prime}:\mathsf{T}^{\prime})\to \mathsf{Ty}\)

where  \( \overline{A} \)  and  \( \overline{T} \)  are 1-to-1 correspondences and  \( R_{\simeq}(\overline{A},\overline{T},-,-) \)  is the 1-to-1 correspondence between  \( T\simeq_{F}A \)  and  \( T'\simeq_{G}A' \)  given by the span interpretation of  \( (-\simeq-) \)  at  \( \overline{T} \)  and  \( \overline{A} \) . We need to define a 1-to-1 correspondence between  \( FGlue(A,P,T,e) \)  and  \( GGlue(A',P',T',e') \) . We take the relation sending g:  \( FGlue(A,P,T,e) \)  and  \( g':GGlue(A',P',T',e') \)  to

\[
\operatorname{Glue} \left(\overline {{\mathrm{A}}} \left(F \text {unglue} (\mathrm{g}), G \text {unglue} \left(\mathrm{g} ^ {\prime}\right)\right), \overline {{\mathrm{P}}}, \overline {{\mathrm{T}}} \left(\mathrm{g}, \mathrm{g} ^ {\prime}\right), \overline {{\mathrm{e}}}\right)
\]

where it remains to define \(\widehat{\mathbf{e}}:\overline{\mathrm{T}} (\mathbf{g},\mathbf{g}^{\prime})\simeq \overline{\mathrm{A}} (F\mathrm{unglue}(\mathbf{g}),G\mathrm{unglue}(\mathbf{g}^{\prime}))\) under \(\overline{\mathrm{P}}\)

By the reduction equations for \( F \) unglue(g) and \( G \) unglue(g') under P and P', the type for \( \widehat{\mathbf{e}} \) simplifies to \( \overline{\mathrm{T}}(\mathbf{g},\mathbf{g}') \simeq \overline{\mathrm{A}}(\mathbf{e}.1(\mathbf{g}),\mathbf{e}'.1(\mathbf{g}')) \). Per the interpretations of \( \Sigma \) and \( \Pi \) (Components 47 and 54), \( \widehat{\mathbf{e}} \) contains a map \( (\mathbf{t}:\mathbf{T},\mathbf{t}':\mathbf{T}') \to \overline{\mathrm{T}}(\mathbf{t},\mathbf{t}') \to \overline{\mathrm{A}}(\mathbf{e}.1(\mathbf{t}),\mathbf{e}'.1(\mathbf{t}')) \) as its first component. We take this map, instantiated at g and g', as the forward function of \( \widehat{\mathbf{e}} \). To see that it is an equivalence, it suffices [29, Theorem 11.1.6] to check that the induced map on total spaces \( (\Sigma \mathbf{t}:\mathbf{T}.\overline{\mathrm{T}}(\mathbf{t},\mathbf{g}')) \to (\Sigma \mathbf{a}:\mathbf{A}.\overline{\mathrm{A}}(\mathbf{a},\mathbf{e}'.1(\mathbf{g}'))) \) is an equivalence, as the base map e.l: T → A is an F-equivalence and thus an equivalence. This is the case because \( \overline{\mathrm{A}} \) and \( \overline{\mathrm{T}} \) are 1-to-1 correspondences and thus both sides are contractible.

With this interpretation of Glue, we can give the interpretations of glue and unglue as glue and unglue.

To interpret suspension, we make essential use of identity types.

▶ Definition 60. Over the environment ([A : Ty, A' : Ty], f : A → A'), define the type-valued relation Graph(f) := ⟨a, a'⟩(f(a) ≍ a') : (a : A, a' : A') → Ty.

For a map \( \mathbf{f} \) that is an equivalence, \( \text{Graph}(\mathbf{f}) \) is a 1-to-1 correspondence. Conversely, a 1-to-1 correspondence \( \overline{\mathbf{A}} \) between \( \mathbf{A} \) and \( \mathbf{A}' \) contains a map \( \text{fwd}_{\overline{\mathbf{A}}} : \mathbf{A} \to \mathbf{A}' \) that is an equivalence.

Over the environment ([A : Ty, A' : Ty], f : A → A'), define map(f) : FSusp(A) → GSusp(A') by FSusp-elimination so that map(f)(Fnorth) = Gnorth, map(f)(Fsouth) = Gsouth, and cong_map(f)(Fmerid(a)) ∼ Gmerid(a'). If f : A → A' is an equivalence, then map(f) is an equivalence, by the elimination principles for FSusp(A) and GSusp(A').

E. Cavallo and C. Sattler

21

▶ Component 61 (S, suspension). Over an environment with A A': Ty and a 1-to-1 correspondence $\bar{A}: (A, A') \to Ty$, we must construct a 1-to-1 correspondence between $FSusp(A)$ and $GSusp(A')$; we take $Graph(map(fwd_{\bar{A}}))$. We interpret north and south by the reflexive identities $map(fwd_{\bar{A}})(north) \asymp north$ and $map(fwd_{\bar{A}})(south) \asymp south$.

To interpret merid applied to a : A, a' : A', and $\bar{a} : \bar{A}(a, a')$, we first convert the path $\text{cong}_{\text{map}(fwd_{\bar{A}})}(Fmerid(a)) \sim Gmerid(fwd_{\bar{A}}(a))$ to an identity, then rewrite along the identity $fwd_{\bar{A}}(a) \asymp a'$ obtained from $\bar{a}$ to get an identity $\text{cong}_{\text{map}(fwd_{\bar{A}})}(Fmerid(a)) \asymp Gmerid(a')$. Using $M\lambda^{\overline{i}}$, we convert this to an M-path in the necessary identity type.

Now we interpret the eliminator. Over the environment

$$(A : Ty, C : Susp(A) \to Ty, n : C(north), s : C(south), m : (a : A) \to Path(\langle i \rangle C(merid(a) @ i), n, s))$$

we have a type

$$D := \Sigma f : (\Pi t : Susp(A).C(t)). \Sigma p_n : f(north) \sim n. \Sigma p_s : f(south) \sim s.$$
$$Path(\langle j \rangle Path(\langle i \rangle C(merid(a) @ i), p_n @ j, p_s @ j), (\lambda i.f(merid(a) @ i)), m)$$

of dependent functions into C defined on the constructors north, south, and merid by n, s, and m respectively, up to homotopy. By virtue of the eliminator, D is contractible, as are FD and GD. Thus every pair of elements from FD and GD is related in SD, in particular the pair obtained from Felim and Gelim. This gives us an almost-interpretation of elim: we have an eliminator that may satisfy the point constructor computation rules only up to paths.

We then correct our almost-interpretation on the point constructors. To interpret the eliminator, we are given type families C and C' and, over $(t : FSusp(A), t' : GSusp(A'), \bar{t} : map(fwd_{\bar{A}})(t) \asymp t')$, 1-to-1 correspondences $\bar{C}(t, t', \bar{t}) : (C(t), C'(t')) \to Ty$. We want to relate $Felim(C, n, s, m, t)$ and $Gelim(C', n', s', m', t')$ in $\bar{C}(t, t', \bar{t})$ for all related inputs. We go by $FSusp$-elimination from t and identity elimination from $\bar{t}$. For the point cases $t = Fnorth$ and $t = Fsouth$, we choose the values that the point computation rules require. For the Fmerid case, we apply the almost-eliminator to the input data to get a section of $\bar{C}$, evaluate it at the corresponding meridian, then coerce the result along the almost-eliminator's point computation paths to get a path of the correct type.

This completes the definition of $S_G^F: \mathbb{C}TT[\iota\Phi] \to Span(\mathbb{C}TT[\iota\Psi])$. In summary:

▶ Theorem 62. Let $F, G: \mathbb{C}TT[\iota\Phi] \to \mathbb{C}TT[\iota\Psi]$ in the coslice under $\text{MLTT}_{\Sigma, Id, U} + \mathbb{C}OF$. There is a $S_G^F: \mathbb{C}TT[\iota\Phi] \to Span(\mathbb{C}TT[\iota\Psi])$ in $\text{MLTT}_{\Sigma, Id}/\text{RMC}$ such that $\pi_0 S_G^F \cong F$ and $\pi_1 S_G^F \cong G$.

## 6 Conservativity

▶ Proposition 63 (2-out-of-6). Weak equivalences of democratic models of $\text{MLTT}_{\Sigma, Id}$ are closed under 2-out-of-6. That is, given morphisms of democratic models of $\text{MLTT}_{\Sigma, Id}$ $\mathcal{M} \xrightarrow{\mathcal{F}} \mathcal{N} \xrightarrow{\mathcal{G}} \mathcal{O} \xrightarrow{\mathcal{H}} \mathcal{P}$ where $\mathcal{GF}$ and $\mathcal{HG}$ are weak equivalences, the maps $\mathcal{F}$, $\mathcal{G}$, $\mathcal{H}$, and the composite $\mathcal{HGF}$ are weak equivalences.

Proof. See Kapulkin and Lumsdaine [22, Corollary 3.4].

A corollary of 2-out-of-6 is 2-out-of-3: given composable morphisms $\mathcal{G}$ and $\mathcal{F}$ between democratic models of $\text{MLTT}_{\Sigma, Id}$, if two of the three morphisms $\mathcal{F}$, $\mathcal{G}$, and $\mathcal{GF}$ are weak equivalences, then so is the third.

▶ Theorem 64. For $F: \mathbb{C}TT[\iota\Phi] \to \mathbb{C}TT[\iota\Psi]$ and $G: \mathbb{C}TT[\iota\Psi] \to \mathbb{C}TT[\iota\Phi]$ in the coslice under $\text{MLTT}_{\Sigma, Id} + \mathbb{C}OF$, the induced morphisms $\mathbf{0}_F: \mathbf{0}_{\mathbb{C}TT[\iota\Phi]} \to \mathbf{0}_{\mathbb{C}TT[\iota\Psi]}$ and $\mathbf{0}_G: \mathbf{0}_{\mathbb{C}TT[\iota\Psi]} \to \mathbf{0}_{\mathbb{C}TT[\iota\Phi]}$ are weak equivalences.

22

Eliminating reversals from cubical type theories

Proof. By Theorem 62, we have an RMC functor fitting in the diagram in \(\mathbb{M}\mathrm{LTT}_{\Sigma ,\mathrm{Id}} / \mathbf{RMC}\) to the left below.

![img-3.jpeg](img-3.jpeg)

![img-4.jpeg](img-4.jpeg)

This induces a diagram in  \( \mathbf{Mod}(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}}) \)  as shown to the right, where the morphisms marked  \( \sim \)  are weak equivalences by Proposition 49. By two applications of 2-out-of-3, first in the right triangle and then in the left, it follows that  \( O_{GF} \)  is a weak equivalence.

By the same argument, \(\mathbf{0}_{FG}\colon \mathbf{0}_{\mathbb{C}\mathrm{TT}[\iota \Phi ]}\to \mathbf{0}_{\mathbb{C}\mathrm{TT}[\iota \Phi ]}\) is a weak equivalence. The claim now follows by 2-out-of-6 applied to the string of morphisms \(\mathbf{0}_F\circ \mathbf{0}_G\circ \mathbf{0}_F\)

Theorem 65 (Conservativity of reversals). For every self-dual interval theory \((\Phi, \phi)\), the inclusion \(\mathbb{C}\mathrm{TT}[\iota\Phi] \to \mathbb{C}\mathrm{TT}[\iota\mathrm{Rev}_{\phi}\Phi]\) induces a weak equivalence \(\mathbf{0}_{\mathbb{C}\mathrm{TT}[\iota\Phi]} \to \mathbf{0}_{\mathbb{C}\mathrm{TT}[\iota\mathrm{Rev}_{\phi}\Phi]}\) in \(\mathbf{Mod}(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}})\).

Proof. By Theorem 64 with Theorem 42.

## 7 Interpreting strict cubical type theory with reversals in spaces

Kapulkin and Lumsdaine [22] show that every democratic model  \( \mathcal{M} \in \mathbf{Mod}(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{Id}}) \)  induces a fibration category structure on its category of contexts  \( \mathcal{M}(\star) \) . Such a structure, which is specified by two classes of morphisms in  \( \mathcal{M}(\star) \)  called fibrations and weak equivalences, induces in turn an  \( (\infty,1) \) -category [34] or “homotopy theory”. It is in this way that we judge the kind of higher structure described by a model of  \( M_{LTT_{\Sigma,Id}} \) . The homotopy theory of topological spaces corresponds to one such  \( (\infty,1) \) -category, that of  \( \infty \) -groupoids.

Awodey et al. [6] and Cavallo and Sattler [11] exhibit constructive models \(\mathcal{M}\) of strict cubical type theories without reversals whose induced \((\infty, 1)\)-categories are classically equivalent to the \((\infty, 1)\)-category of \(\infty\)-groupoids. These models are not themselves democratic, so here we mean that their hearts \(\mathcal{M}^{\heartsuit}\) present these \((\infty, 1)\)-categories in the above sense (Definition 9). Typically, however, these models are analyzed by means of a Quillen model structure, another form of presentation of an \((\infty, 1)\)-category, on \(\mathcal{M}\) itself. Such a structure is defined by three classes of maps: cofibrations, weak equivalences, and fibrations.

▶ Definition 66. The Quillen model structure presented by  \( \mathcal{M} \in \text{Mod}(\mathbb{M}\text{LTT}_{\Sigma,\text{Id}}) \) , if it exists, is the unique model structure on  \( \mathcal{M}(\star) \)  such that

(a) the fibrations are the retracts in \(\mathcal{M}(\star)\to\) of context extensions, i.e., of morphisms \(p_A\colon \Gamma .A\to \Gamma\) arising as pullbacks in \(\mathrm{PSh}(\mathcal{M}(\star))\) of \(\mathcal{M}(\pi_{\mathsf{Tm}})\);
(b) the unique map \(0 \to \Gamma\) is a cofibration for all \(\Gamma \in \mathcal{M}(\star)\).

The uniqueness follows from a result of Joyal [27, Theorem 15.3.1]. A model structure on a category \(\mathcal{E}\) induces a fibration category structure on the full subcategory of \(X\in \mathcal{E}\) such that \(X\to 1\) is a fibration; for a model structure presented by \(\mathcal{M}\in \mathbf{Mod}(\mathbb{M}\mathrm{LTT}_{\Sigma ,\mathrm{Id}})\), this is exactly \(\mathcal{M}^{\heartsuit}(\star)\), and the induced fibration category is exactly Kapulkin and Lumsdaine's.

Theorem 65 allows us to translate proofs in “opaque” cubical type theory with reversals into proofs that do not use reversals, which can then be interpreted in  \( \infty \) -groupoids via the aforementioned models. However, it does not allow us to translate proofs in strict cubical type theories. Fortunately, we can also use the twist construction to directly construct models of strict cubical type theory with reversals in  \( \infty \) -groupoids. In fact, we can reuse existing model constructions of the kind pioneered by Orton and Pitts [26] out of the box.

E. Cavallo and C. Sattler

23

## 7.1 Orton–Pitts models

Orton and Pitts [26] give an abstract description of Cohen, Coquand, Huber, and Mörtberg's model of cubical type theory in De Morgan cubical sets [12]. Abstracting from the case of cubical sets, they fix a topos $\mathcal{E}$ equipped with an interval object $I$ and a suitable subobject $\Omega_{\mathrm{cof}} \mapsto \Omega$ of the subobject classifier and isolate axioms on this data sufficient to construct a model of a strict cubical type theory in $\mathcal{E}$ where the interval is interpreted by $I$ and the cofibrations by $\Omega_{\mathrm{cof}}$. They assume that the interval $I$ has connections, but Angiuli, Brunerie, Coquand, Harper, Favonia, and Licata (ABCHFL) [2] subsequently gave a similar construction for intervals without such structure. Extracting what we need from their main result and rephrasing in our language, we have:

▶ Proposition 67 ([2, Theorem 2]). Let $\mathcal{E} = \mathrm{PSh}(\mathcal{C})$ be a presheaf category on a finite product category $\mathcal{C}$, let $I \in \mathcal{E}$ be a representable object with distinct points $0, 1: 1 \to I$, and let $\Omega_{\mathrm{cof}} \mapsto \Omega_{\mathrm{dec}}$ be a subobject of the levelwise decidable subobject classifier in $\mathrm{PSh}(\mathcal{C})$ that classifies the diagonal $I \to I \times I$ and is closed under finite conjunction, finite disjunction, and universal quantification over $I$. Then there is a model $\mathcal{M}$ of $\mathbb{C}\mathrm{TT}_s$ such that

(a) $\mathcal{M}(\star) = \mathcal{E}$.
(b) $\mathcal{M}(\mathbb{I}) = \mathcal{K}I \in \mathrm{PSh}(\mathcal{E})$.
(c) the maps $p_A: \Gamma.A \to \Gamma$ arising as pullbacks in $\mathrm{PSh}(\mathcal{E})$ of $\mathcal{M}(\pi_{\mathrm{Tm}})$ are those equipped with a diagonal Kan composition structure [2, Definition 1].

This model interprets the interval theory of all $f: I^n \to I$ in $\mathcal{C}$ and equations between them.

We call $(\mathcal{C}, I, 0, 1, \Omega_{\mathrm{cof}})$ satisfying the conditions of Proposition 67 an ABCHFL setup and write $\mathcal{M}(\mathcal{C}, 0, 1, I, \Omega_{\mathrm{cof}})$ for the resulting model. The maps with diagonal Kan composition structure can be described by a simple lifting property. Awodey proves the following for cartesian cubical sets, but the same proof applies in the setting of Proposition 67.

▶ Proposition 68 ([5, Proposition 4.15(2)⇔(3)]). Let $(\mathcal{C}, I, 0, 1, \Omega_{\mathrm{cof}})$ be an ABCHFL setup. A morphism $f: Y \to X$ admits a diagonal Kan composition structure if and only if it has the right lifting property against the unique dashed map

![img-5.jpeg](img-5.jpeg)

for every $m: A \mapsto B$ classified by $\Omega_{\mathrm{cof}}$ and $z: B \to I$.

We call a map an $(I, \Omega_{\mathrm{cof}})$-fibration when it satisfies the property in Proposition 68. As a lifting property, it is closed under retracts [27, Lemma 11.1.4].

▶ Proposition 69. If $(\mathcal{C}, I, 0, 1, \Omega_{\mathrm{cof}})$ is an ABCHFL setup, then $(\mathcal{C}, I \times I, r, s, \Omega_{\mathrm{cof}})$ is an ABCHFL setup for every $r \neq s: 1 \to I \times I$. Moreover, the classes of $(I \times I, \Omega_{\mathrm{cof}})$- and $(I, \Omega_{\mathrm{cof}})$-fibrations coincide.

Proof. Because $\mathcal{C}$ is a finite product category by assumption, $I \times I$ is also representable. The diagonal $\Delta_{I \times I}: I \times I \to (I \times I) \times (I \times I)$ is the conjunction of $(\pi_0 \times \pi_0)^* \Delta_I$ and $(\pi_1 \times \pi_1)^* \Delta_I$, the pullbacks of $\Delta_I: I \to I \times I$ along the projections $\pi_0 \times \pi_0, \pi_1 \times \pi_1: (I \times I) \times (I \times I) \to I \times I$. Thus it is classified by $\Omega_{\mathrm{cof}}$. Universal quantification of $I \times I$ is iterated universal quantification over $I$, so $\Omega_{\mathrm{cof}}$ is closed under this operation. This completes the proof of the first claim.

24

Eliminating reversals from cubical type theories

For the second claim, recall that the class of maps with the left lifting property against a map is closed under retracts, composition, and pushouts along arbitrary maps [27, Lemma 11.1.4]. Given \( m \colon A \mapsto B \) classified by \( \Omega_{\mathrm{cof}} \) and \( z \colon B \to I \), we can write \( m \otimes_z \delta \) as a retract of \( m \otimes_{z \times 0} \delta \) where \( z \times 0 \colon B \to I \times I \):

\[
\begin{array}{c} B \sqcup_ {A} (A \times I) \longrightarrow B \sqcup_ {A} (A \times (I \times I)) \longrightarrow B \sqcup_ {A} (A \times I) \\ m \otimes_ {z} \delta \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \times I \xrightarrow [ B \times (I \times 0) ]{} B \times (I \times I) \xrightarrow [ B \times \pi_ {0} ]{} B \times I. \end{array}
\]

Thus every \((I\times I,\Omega_{\mathrm{cof}})\)-fibration is an \((I,\Omega_{\mathrm{cof}})\)-fibration. For the converse, given \(m\colon A\mapsto B\) classified by \(\Omega_{\mathrm{cof}}\) and \(z\colon B\to I\times I\), we read off the commutative diagram

![img-6.jpeg](img-6.jpeg)

that \(m \otimes_z \delta\) is a composite of a pushout of \(m \otimes_{\pi_0 z} \delta\) and \((m \times I) \otimes_{\pi_1 z \pi_1} \delta\). This semantic counterpart to Component 32 shows that all \((I, \Omega_{\mathrm{cof}})\)-fibrations are \((I \times I, \Omega_{\mathrm{cof}})\)-fibrations.

Using Proposition 69, we can turn any ABCHFL model that presents \(\infty\)-groupoids into an ABCHFL model with reversals that also presents \(\infty\)-groupoids. A suitable input is the category of presheaves on the semilattice cube category \(\square_{\vee}\), i.e., the cartesian cube category with one connection. This is the algebraic theory generated by an object \(I\) with points \(0,1:1\to I\) and a connection \(\vee:I\times I\to I\) satisfying the axioms of a bounded join-semilattice.

▶ Proposition 70 ([11, Theorems 4.34 & 7.8]). The ABCHFL model  \( \mathcal{M}(\Box_{\vee}, I, 0, 1, \Omega_{\mathrm{dec}}) \)  presents a Quillen model structure. Assuming classical logic, this model structure presents the  \( (\infty, 1) \) -category of  \( \infty \) -groupoids.
Theorem 71. The ABCHFL model \(\mathcal{M}(\square_{\vee}, I \times I, (0,1), (1,0), \Omega_{\mathrm{dec}})\) interprets strict cubical type theory with reversals and presents a Quillen model structure. Assuming classical logic, this model structure presents the \((\infty,1)\)-category of \(\infty\)-groupoids.

Proof. Propositions 67 and 69 give the existence of the model of type theory. The existence of the model structure can be established by following Awodey's construction [5], but he considers only the cartesian cube category with its canonical interval object. The necessary components appear in generality in Awodey et al. [6, Lemma 3.7.2, Proposition 3.7.3] (compare [6, Theorem 4.4.9]). By Proposition 69 and the uniqueness of the model structure presented by a model of type theory, this model structure is the same as that presented by \(\mathcal{M}(\square_{\vee}, I, 0, 1, \Omega_{\mathrm{dec}})\), so Proposition 70 proves the final claim.

Although the original interval \( I \) in \( \square_{\vee} \) has a connection, this is not the case for \( I \times I \) with the endpoints \( (0,1) \) and \( (1,0) \): in order to give the definition \( (i_0,i_1)\vee (j_0,j_1):= (i_0\vee j_0,i_1\wedge j_1) \) from §1.1, we need both connections in the base model. Thus we only model cubical type theory with a reversal, not with a connection. We expect that we can apply the procedure in this section to the second author's model of cubical type theory with two connections [32], even though it is not an ABCHFL model, but we leave this to future work.

E. Cavallo and C. Sattler

25

# References

1 Carlo Angiuli. Computational Semantics of Cartesian Cubical Type Theory. PhD thesis, Carnegie Mellon University, 2019. doi:10.1184/R1/16860013.
2 Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Robert Harper, Kuen-Bang Hou (Favonia), and Daniel R. Licata. Syntax and models of Cartesian cubical type theory. Mathematical Structures in Computer Science, 31(4), 2021. doi:10.1017/S0960129521000347.
3 Carlo Angiuli, Kuen-Bang Hou (Favonia), and Robert Harper. Cartesian cubical computational type theory: Constructive reasoning with paths and equalities. In 27th EACSL Annual Conference on Computer Science Logic, CSL 2018, September 4-7, 2018, Birmingham, UK, pages 6:1-6:17, 2018. doi:10.4230/LIPIcs.CSL.2018.6.
4 Steve Awodey. Natural models of homotopy type theory. Mathematical Structures in Computer Science, 28(2):241-286, 2018. doi:10.1017/S0960129516000268.
5 Steve Awodey. Cartesian Cubical Model Categories. Springer Nature Switzerland, 2026. doi:10.1007/978-3-032-08730-0.
6 Steve Awodey, Evan Cavallo, Thierry Coquand, Emily Riehl, and Christian Sattler. The equivariant model structure on cartesian cubical sets. Advances in Mathematics, 495:110965, 2026. doi:10.1016/j.aim.2026.110965.
7 Rafaël Bocquet. Towards coherence theorems for equational extensions of type theories, 2023. arXiv:2304.10343.
8 Ulrik Buchholtz and Edward Morehouse. Varieties of cubical sets. In Relational and Algebraic Methods in Computer Science - 16th International Conference, RAMICS 2017, Lyon, France, May 15-18, 2017, Proceedings, pages 77-92, 2017. doi:10.1007/978-3-319-57418-9_5.
9 Evan Cavallo and Robert Harper. Higher inductive types in cubical computational type theory. Proceedings of the ACM on Programming Languages, 3(POPL):1:1-1:27, 2019. doi:10.1145/3290314.
10 Evan Cavallo, Anders Mörtberg, and Andrew W. Swan. Unifying cubical models of univalent type theory. In 28th EACSL Annual Conference on Computer Science Logic, CSL 2020, January 13-16, 2020, Barcelona, Spain, volume 152 of LIPIcs, pages 14:1-14:17. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2020. doi:10.4230/LIPIcs.CSL.2020.14.
11 Evan Cavallo and Christian Sattler. Relative elegance and cartesian cubes with one connection. Canadian Journal of Mathematics, pages 1-64, 2025. doi:10.4153/S0008414X25101466.
12 Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. Cubical type theory: A constructive interpretation of the univalence axiom. In 21st International Conference on Types for Proofs and Programs, TYPES 2015, May 18-21, 2015, Tallinn, Estonia, pages 5:1-5:34, 2015. doi:10.4230/LIPIcs.TYPES.2015.5.
13 Thierry Coquand, Simon Huber, and Anders Mörtberg. On higher inductive types in cubical type theory. In Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS '18, pages 255-264, 2018. doi:10.1145/3209108.3209197.
14 Thierry Coquand, Simon Huber, and Christian Sattler. Canonicity and homotopy canonicity for cubical type theory. Logical Methods in Computer Science, 18(1):28:1-28:35, 2022. doi:10.46298/lmcs-18(1:28)2022.
15 Peter Dybjer. Inductive families. Formal Aspects of Computing, 6(4):440-465, 1994. doi:10.1007/BF01211308.
16 Peter Dybjer. Internal type theory. In Stefano Berardi and Mario Coppo, editors, Types for Proofs and Programs: International Workshop, TYPES '95 Torino, Italy, June 5-8, 1995 Selected Papers, pages 120-134. Springer Berlin Heidelberg, Berlin, Heidelberg, 1996. doi:10.1007/3-540-61780-9_66.
17 Manuel Fidel and Diana Brignole. Estudio algebraico de ciertas lógicas no clásicas mediante producto de álgebras. In Actas del I Congreso Dr. Antonio A. R. Monteiro, Bahía Blanca, pages 23-38, 1991. URL: https://www.inmabb-conicet.gob.ar/static/publicaciones/actas/1/03_Brignole.pdf.

26 Eliminating reversals from cubical type theories

18 Robert Harper, Furio Honsell, and Gordon Plotkin. A framework for defining logics. Journal of the ACM, 40(1):143–184, 1993. doi:10.1145/138027.138060.
19 Simon Huber. Canonicity for cubical type theory. Journal of Automated Reasoning, 63(2):173–210, 2018. doi:10.1007/s10817-018-9469-1.
20 Valery Isaev. Morita equivalences between algebraic dependent type theories, 2020. arXiv:1804.05045.
21 Krzysztof Kapulkin and Yufeng Li. Extensional concepts in intensional type theory, revisited. Theoretical Computer Science, 1029:115051, 2025. doi:10.1016/j.tcs.2024.115051.
22 Krzysztof Kapulkin and Peter LeFanu Lumsdaine. The homotopy theory of type theories. Advances in Mathematics, 337:1–38, 2018. doi:10.1016/j.aim.2018.08.003.
23 Marcus Kracht. On extensions of intermediate logics by strong negation. Journal of Philosophical Logic, 27(1):49–73, 1998. doi:10.1023/a:1004222213212.
24 Per Martin-Löf. An intuitionistic theory of types: predicative part. In H.E. Rose and J.C. Shepherdson, editors, Logic Colloquium '73, volume 80 of Studies in Logic and the Foundations of Mathematics, pages 73–118. North-Holland, 1975. doi:10.1016/S0049-237X(08)71945-1.
25 Anders Mörtberg and Loïc Pujet. Cubical synthetic homotopy theory. In Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, pages 158–171, New York, NY, USA, 2020. Association for Computing Machinery. doi:10.1145/3372885.3373825.
26 Ian Orton and Andrew M. Pitts. Axioms for modelling cubical type theory in a topos. Logical Methods in Computer Science, 14(4), 2018. doi:10.23638/LMCS-14(4:23)2018.
27 Emily Riehl. Categorical Homotopy Theory. Cambridge University Press, 2014. doi:10.1017/cbo9781107261457.
28 Emily Riehl and Michael Shulman. A type theory for synthetic ∞-categories. Higher Structures, 1(1):116–193, 2017. doi:10.21136/HS.2017.06.
29 Egbert Rijke. Introduction to Homotopy Type Theory. Cambridge Studies in Advanced Mathematics. Cambridge University Press, 2025. doi:10.1017/9781108933568.
30 Umberto Rivieccio. Representation of De Morgan and (semi-)Kleene lattices. Soft Computing, 24(12):8685–8716, 2020. doi:10.1007/s00500-020-04885-w.
31 Christian Sattler. Do cubical models of type theory also model homotopy types, 2018. Lecture at the Hausdorff Trimester Program: Types, Sets and Constructions. URL: https://www.youtube.com/watch?v=wkPDyIGmEoA.
32 Christian Sattler. A constructive ∞-groupoid model of homotopy type theory. Invited talk at TYPES 2025. Slides: https://msp.cis.strath.ac.uk/types2025/slides/TYPES2025-slidesSattler.pdf, video: https://youtu.be/eV9y6I2QHEk, 2025.
33 Thomas Streicher and Jonathan Weinberger. Simplicial sets inside cubical sets. Theory Appl. Categ., 37(10):276–286, 2021. doi:10.70930/tac/ob3pmmyi.
34 Karol Szumilo. Frames in cofibration categories. Journal of Homotopy and Related Structures, 12(3):577–616, 2016. doi:10.1007/s40062-016-0139-x.
35 Nicolas Tabareau, Éric Tanter, and Matthieu Sozeau. The marriage of univalence and parametricity. Journal of the ACM, 68(1):1–44, 2021. doi:10.1145/3429979.
36 The Agda Community. Cubical Agda Library. URL: https://github.com/agda/cubical.
37 Taichi Uemura. Abstract and Concrete Type Theories. PhD thesis, University of Amsterdam, 2021. URL: https://eprints.illc.uva.nl/id/eprint/2195/.
38 Taichi Uemura. A general framework for the semantics of type theory. Mathematical Structures in Computer Science, 33(3):134–179, 2023. doi:10.1017/s0960129523000208.
39 The Univalent Foundations Program. Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study, 2013.
40 Dimiter Vakarelov. Notes on N-lattices and constructive logic with strong negation. Studia Logica, 36(1-2):109–125, 1977. doi:10.1007/bf02121118.

E. Cavallo and C. Sattler

27

41 Andrea Vezzosi, Anders Mörtberg, and Andreas Abel. Cubical Agda: A dependently typed programming language with univalence and higher inductive types. *Journal of Functional Programming*, 31, 2021. doi:10.1017/s0956796821000034.