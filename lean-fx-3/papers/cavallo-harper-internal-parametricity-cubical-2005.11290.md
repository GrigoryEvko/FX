Logical Methods in Computer Science
Volume 17, Issue 4, 2021, pp. 5:1–5:60
https://lmcs.episciences.org/

Submitted May 25, 2020
Published Nov. 03, 2021

# INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

EVAN CAVALLO AND ROBERT HARPER

Department of Computer Science, Carnegie Mellon University, Pittsburgh, Pennsylvania, USA
e-mail address: {ecavallo,rwh}@cs.cmu.edu

ABSTRACT. We define a computational type theory combining the contentful equality structure of cartesian cubical type theory with internal parametricity primitives. The combined theory supports both univalence and its relational equivalent, which we call relativity. We demonstrate the use of the theory by analyzing polymorphic functions between higher inductive types, observe how cubical equality regularizes parametric type theory, and examine the similarities and discrepancies between cubical and parametric type theory, which are closely related. We also abstract a formal interface to the computational interpretation and show that this also has a presheaf model.

# INTRODUCTION

In the past decade or so, the study of dependent type theory has been transformed by a growing recognition of the importance of contentful (or proof-relevant) equality. At its root, the idea is simple: a proof of an equality is a piece of data. To go a bit a farther, a proof of equality may play a non-trivial role in computation. From the type-theoretic perspective, where the computational content of proofs has always been emphasized (“proofs as programs”), it is completely natural to think of equality this way. Nevertheless, it has been common to treat proofs of equality as irrelevant: we prove equalities to check code correctness or to prove a theorem, but we do not expect those proofs to influence how our code runs.

That expectation was shaken by Hofmann and Streicher’s groupoid model [HS98] of Martin-Löf’s intensional type theory (ITT) [ML75]. Intensional type theory includes the identity type: for every type A and elements M, N ∈ A, there is a type Id_A(M, N) whose elements are proofs that M and N are “equal”. (We henceforth call these elements identities or identifications.) Hofmann and Streicher’s model is designed to falsify the principle of uniqueness of identity proofs, which states that all proofs of a given identity are themselves identical. They thereby show that this principle is, oddly enough, independent of ITT. Far

Key words and phrases: cubical type theory, parametricity, computational type theory, modal type theory.

* This article is an extended version of [CH20].

This material is based on research sponsored by Air Force Office of Scientific Research through MURI grants FA9550-15-1-0053 and FA9550-21-0009 (Tristan Nguyen, program manager). Any opinions, findings and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of the AFOSR.

LOGICAL METHODS
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-17(4:5)2021

© E. Cavallo and R. Harper
Creative Commons

5:2

E. CAVALLO AND R. HARPER

Vol. 17:4

from being a contrived counter-model, the groupoid model demonstrates that contentful equality arises quite naturally in mathematics. Hofmann and Streicher highlight isomorphism as the premiere example: two isomorphic sets are essentially “the same”, but the same two sets can be isomorphic in many different ways. Awodey and Warren [War08, AW09] and van den Berg and Garner [vdBG12] generalized the groupoid model construction to produce models where there are not only distinct proofs of identities, but distinct proofs of identities between proofs of identities and so on. Voevodsky, who was separately developing a simplicial model with similar properties [KL12], proposed to extend ITT with his univalence axiom, which asserts precisely that identifications between types correspond to isomorphisms.

Voevodsky’s univalence axiom codifies a kind of reasoning that is already ubiquitous in informal mathematics, that of treating isomorphic objects as interchangeable. In fact, the axiom has far-reaching consequences, as subsequently explored in the fields of homotopy type theory [Uni13] and univalent foundations [Voe15, VAG+]. As a simple but characteristic example, it implies function extensionality as a corollary: functions are identical when they are identical on all arguments [Uni13, §4.9]. Analogous extensionality principles for equality in conductive types (e.g., [ACS15]) and quotients (e.g., [KvR19]) follow as well. In short, univalence regularizes the behavior of equality throughout type theory.

Of course, there is one sense in which univalent ITT is spectacularly ill-behaved: by introducing an axiom, we destroy the computational content of type theory. There is no way to run a program written in ITT that uses the univalence axiom, because the “proof” of the axiom does not compute. This was finally addressed by the development of cubical type theories [CCHM15, AFH18, OP18, ABC+19, CMS20], a family of univalent type theories (with constructive models) where the univalence axiom follows from more fundamental primitives that do compute. The central principle of cubical type theory is that equalities in a type A—now called paths—are represented by maps from an interval object I into A.

Cubical type theory will be our starting point, our setting to explore contentful equality. In this work, we develop internal parametricity as an effective tool to reason about contentful equality, which—despite its remarkable usefulness—presents new difficulties as well.

The challenges of contentful equality. As users of ITT have long known, a lack of uniqueness of identity proofs has some frustrating consequences. To put it pithily, when equalities are not always equal, we sometimes need to prove that they are. For example, we typically need to know that composition of equalities (i.e., transitivity) is associative. When we have contentful equality in mind, these “coherence” proofs are mathematically significant, but their proofs are often tedious, uninteresting, and difficult to conceptualize, especially as one gets to the point of proving equalities between equalities between equalities.

The problem is most acute when we work with quotients. In cubical type theory, as in homotopy type theory and the univalent foundations, inductive types and quotient types both arise as specializations of higher inductive types [Uni13, CHM18, CH19a]. Where an inductive type is defined by constructors that generate elements of the type, a higher inductive type is defined by a specification of element and path constructors. As a simple example, we can specify the type $\mathbb{Z}/2\mathbb{Z}$ of integers mod 2 in cubical type theory as the following higher inductive type.

data $\mathbb{Z}/2\mathbb{Z}$ where
| in(n : $\mathbb{Z}$) $\in$ $\mathbb{Z}/2\mathbb{Z}$
| mod(n : $\mathbb{Z}$, x : $\mathbb{I}$) $\in$ $\mathbb{Z}/2\mathbb{Z}$ [x = 0 $\hookrightarrow$ in(n) | x = 1 $\hookrightarrow$ in(n + 2)]

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:3

The first constructor of this type is standard: whenever we have an integer $n : \mathbb{Z}$, we get $\mathfrak{in}(n) \in \mathbb{Z}/2\mathbb{Z}$. The second is a path constructor: whenever we have $n : \mathbb{Z}$, we get a path from $\mathfrak{in}(n)$ to $\mathfrak{in}(n + 2)$. That path is represented by a term $\mathsf{mod}(n, x)$ depending on an interval variable $x$, together with equations declaring that $\mathsf{mod}(n, 0)$ is $\mathfrak{in}(n)$ and $\mathsf{mod}(n, 1)$ is $\mathfrak{in}(n + 2)$. The interval is to be thought of roughly as the real interval from analysis: as $x : \mathbb{I}$ varies from 0 to 1, the constructor $\mathsf{mod}(n, x)$ draws a line from $\mathfrak{in}(n)$ to $\mathfrak{in}(n + 2)$. Pictorially, we have something like the following.

![img-0.jpeg](img-0.jpeg)

To construct a map from $\mathbb{Z}/2\mathbb{Z}$ to another type, we simply explain where to send $\mathfrak{in}(n)$ and $\mathsf{mod}(n, x)$, just as in ordinary induction. For example, the increment map $\mathfrak{inc} \in \mathbb{Z}/2\mathbb{Z} \to \mathbb{Z}/2\mathbb{Z}$ is defined by the clauses $\mathfrak{inc}(\mathfrak{in}(n)) := \mathfrak{in}(n + 1)$ and $\mathfrak{inc}(\mathsf{mod}(n, x)) := \mathsf{mod}(n + 1, x)$. In order for the definition to be sensible, we need to check that $\mathfrak{inc}(\mathsf{mod}(n, 0)) = \mathfrak{inc}(\mathfrak{in}(n))$ and $\mathfrak{inc}(\mathsf{mod}(n, 1)) = \mathfrak{inc}(\mathfrak{in}(n + 2))$. Similarly, we can define addition by an iterated induction of the following form.

$$\begin{array}{l} \mathfrak{in}(m) \quad + \quad \mathfrak{in}(n) \quad := \quad \mathfrak{in}(m + n) \\ \mathsf{mod}(m, x) \quad + \quad \mathfrak{in}(n) \quad := \quad \cdots \\ \mathfrak{in}(m) \quad + \quad \mathsf{mod}(n, y) \quad := \quad \cdots \\ \mathsf{mod}(m, x) \quad + \quad \mathsf{mod}(n, y) \quad := \quad \cdots \end{array}$$

The final clause of this definition depends on two interval variables $x, y : \mathbb{I}$. We can visualize it as a square with a boundary determined by the other clauses.

$$y \overset{x}{\longmapsto} \mathfrak{in}(m) + \mathsf{mod}(n, y) \overset{\bullet}{\longmapsto} \mathsf{mod}(m, x) + \mathfrak{in}(n) \overset{\bullet}{\longmapsto} \mathsf{ind}(m + 2) + \mathsf{mod}(n, y)$$

Finding a term to fill this square is not so simple, particularly if the edge clauses are already defined in a complicated way.

Iterated induction on higher inductive types is a frequent source of such coherence obligations. Particularly notorious instances, which will serve as a test case in this paper, are proofs establishing the algebraic structure of the smash product [Uni13, §6.8]. The smash product $\wedge_*$ is a binary operator on pointed types, pairs $A_* = \langle A, a_0 \rangle$ of types $A$ equipped with a chosen "basepoint" element $a_0 \in A$. We will define the product in Section 3.4; for now, it suffices to know that we define its underlying type as a higher inductive type. The smash product is a natural notion of tensor product for the category of pointed types. In particular, suppose we write $A_* \to B_*$ for the type of basepoint-preserving functions between pointed types $A_*$ and $B_*$, which we can make into a pointed type $A_* \to_* B_*$ by taking the unique basepoint-preserving constant function as its basepoint. Then we have a (pointed) isomorphism $A_* \to_* (B_* \to_* C_*) \simeq (A_* \wedge_* B_*) \to_* C_*$. The smash product appears as a

5:4

E. CAVALLO AND R. HARPER

Vol. 17:4

basic tool in synthetic homotopy theory, the study of higher-dimensional structure (homotopy theory) through the lens of univalent type theory.

We would like to know that the smash product is commutative, associative, and so on. To construct a commutator $A_* \wedge_* B_* \to B_* \wedge_* A_*$, we naturally go by induction on elements of $A_* \wedge_* B_*$; to construct an associator $(A_* \wedge_* B_*) \wedge_* C_* \to A \wedge_* (B \wedge_* C)$, we need iterated induction on the two instances of $\wedge_*$ in the domain. This is already quite non-trivial, but it gets worse. If we want to prove that our associator is an isomorphism, then we need to prove equalities between elements of $(A_* \wedge_* B_*) \wedge_* C_*$ (and $A_* \wedge_* (B_* \wedge_* C_*)$) by induction. This increases the dimension by another notch, forcing us to reason with 3-dimensional terms. Going further, we can ask whether the associator satisfies the pentagon identity, which equates the two a priori distinct ways of re-associating from $((A_* \wedge_* B_*) \wedge_* C_*) \wedge_* D_*$ to $A_* \wedge_* (B_* \wedge_* (C_* \wedge_* D_*))$.

$$\begin{array}{c} ((A_* \wedge_* B_*) \wedge_* C_*) \wedge_* D_* \\ \xleftarrow{\cong} \\ (A_* \wedge_* (B_* \wedge_* C_*)) \wedge_* D_* \\ \xrightarrow{\cong} \\ A_* \wedge_* ((B_* \wedge_* C_*) \wedge_* D_*) \xrightarrow{\cong} A_* \wedge_* (B_* \wedge_* (C_* \wedge_* D_*)) \end{array}$$

This is an equality between elements of a thrice-iterated smash product, so its proof requires constructing 4-dimensional terms. Going further, we might also want to check that these proofs are natural in the arguments $A_*$, $B_*$, $C_*$, and $D_*!$ There is, in fact, an infinite tower of coherence conditions that we expect the smash product to satisfy, making it into an $\infty$-coherent symmetric monoidal product.

Sadly, it quickly becomes first painful and then infeasible to construct these proofs by hand. In homotopy type theory, Van Doorn verifies that the smash product is a 1-coherent symmetric monoidal product by first proving the isomorphism $A_* \to_* (B_* \to_* C_*) \simeq (A_* \wedge_* B_*) \to_* C_*$ and using this to obtain the other results [vD18, §4.3]. (1-coherence goes as far as the pentagon and its cousin the hexagon identity, which relates the associator and unit laws.) As Van Doorn notes [vD18, Remark 4.3.29], there is a gap in the argument: roughly, the proofs use that the above is a pointed isomorphism natural in $A_*$, $B_*$, $C_*$, but only proves that it is natural as an unpointed isomorphism. Once again, there is no doubt that the gap can be filled, but to do so involves a prohibitive amount of path manipulation. Seeking to avoid all this, Brunerie suggests automating coherence proofs, using a simple strategy of searching for opportunities to apply the elimination principle for the equality type [Bru18]. Unfortunately, this approach also reaches its practical limit around the 1-coherence mark. In either case, while it might be possible to reach the 2-coherences with enough effort and optimization, there is little hope of handling general $n$-coherences.

**Parametricity.** We propose a novel approach to these problems using a well-established tool from computer science: Reynolds' parametricity [Rey83]. Parametricity is a versatile technique used to prove uniformity properties of terms constructed in type theory; these are popularly known as "theorems for free!" after Wadler [Wad89]. Reynolds' original results concerned the simply typed $\lambda$-calculus with type variables. Since his seminal paper, parametricity has been extended in innumerable directions—most notably for our purposes, to dependent type theory [Tak01, BJP10, KD13, AGJ14].

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:5

To motivate Reynolds' insight, suppose we have been given a family of functions $F \in (A:\mathcal{U}) \to A \to A$. There is one obvious term that $F$ could be: the polymorphic identity function $\lambda A.\lambda a.a$. Moreover, this would appear to be the *only* term $F$ could be: if we are given a type $A$ we know nothing about except that it has an element $a : A$, then the only way we can produce an element of $A$ is by using the one given to us. This kind of reasoning relies on the fact that there is no *type-case* function in the type theory; there is no way to write a function like the following that inspects the shape of $A$.

$$\lambda A.\lambda a.(\text{if } A \text{ is bool then } \mathfrak{ff} \text{ else } a) \in (A:\mathcal{U}) \to A \to A$$

Reynolds translated this apparently syntactic property—the lack of constructs for inspecting types—into a semantic one: if we take a term in type theory and interpret it in set theory, it has an action on relations. In the case of a term $F \in (A:\mathcal{U}) \to A \to A$, its set-theoretic interpretation $[\![F]\!]$ has the following property.

**Fact 0.1.** Let a pair of sets $A, B$ and a relation $R \subseteq A \times B$ be given. If $R(a, b)$ for some $a \in A$ and $b \in B$, then $R([\![F]\!]Aa, [\![F]\!]Bb)$.

This property actually suffices to show that $[\![F]\!]$ is the polymorphic identity function. Briefly, for any set $A$ and $a \in A$, we can define the relation $R \subseteq A \times 1$ by $R(a', \_) := (a' = a)$; then we have $R(a, *)$, so $R([\![F]\!]Aa, [\![F]\!]1*)$. Note that Fact 0.1 also immediately implies (though trivially in this case) that $[\![F]\!]$ is *natural*: for any function of sets $f \in A \to B$ and $a \in B$, we have $f \circ [\![F]\!]A = [\![F]\!]B \circ f$.

In essence, Reynolds' proof consists in defining a relational model of type theory, which Robinson and Rosolini [RR94] reinterpret as a model in the category of *reflexive graphs*. Each type is modeled by a reflexive graph, with vertices representing elements in the ordinary sense and edges defining a relation on those elements. Functions take vertices to vertices and edges to edges. Fact 0.1 is then the action of $[\![F]\!]$ on edges. Atkey, Ghani, and Johann extend the reflexive graph model to dependent type theory [AGJ14]. In particular, Atkey *et al.* define a universe whose vertices are sets (discrete reflexive graphs) and edges are relations between those sets. The astute reader will notice a similarity to Hofmann and Streicher's groupoid model; note that a groupoid is simply a reflexive graph supporting composition and inverse operations. (Atkey *et al.* make this comparison themselves.)

Can parametricity be used to conquer the problem of smash product coherences? Suppose we have managed to define an associator $F \in (A_* \wedge_* B_*) \wedge_* C_* \to A_* \wedge_* (B_* \wedge_* C_*)$ and a candidate inverse $G \in A_* \wedge_* (B_* \wedge_* C_*) \to (A_* \wedge_* B_*) \wedge_* C_*$. (Let us quantify implicitly over $A_*, B_*, C_*$ for the moment.) For one, we certainly expect parametricity to guarantee that these functions are natural in their type arguments. To show that they form an isomorphism, we would need to show $G \circ F$ is the identity function (likewise for $F \circ G$). This is a pointed function $(A_* \wedge_* B_*) \wedge_* C_* \to (A_* \wedge_* B_*) \wedge_* C_*$; perhaps parametricity can show that the identity is the *only* such function. (In truth, there is the possibility that it is a constant function, but we can exclude that case by testing it at $A = B = C = \mathsf{bool}$.) The pentagon identity establishes the equality of two isomorphisms $E, E' \in ((A_* \wedge_* B) \wedge_* C_*) \wedge_* D_* \simeq A_* \wedge_* (B_* \wedge_* (C_* \wedge_* D_*))$; this we can recast as showing that the composite $E^{-1} \circ E$, regarded as a pointed function $((A_* \wedge_* B_*) \wedge_* C_*) \wedge_* D_* \to ((A_* \wedge_* B_*) \wedge_* C_*) \wedge_* D_*$, is the identity. Ultimately, all the higher coherences can be expressed as properties of types of the following form, where $A_*^1, \dots, A_*^n$ are universally quantified type variables.

$$(A_*^1 \wedge_* \dots \wedge_* A_*^n) \to_* (A_*^1 \wedge_* \dots \wedge_* A_*^n)$$

5:6

E. CAVALLO AND R. HARPER

Vol. 17:4

We will indeed be able to use parametricity to characterize types of this form, showing that their only inhabitants are identity and constant functions.

**Internalizing parametricity.** Rather than constructing a model and showing that the denotations of terms satisfy parametricity properties, as Reynolds did, we follow Bernardy, Coquand, and Moulin's recent work [BM12, BM13, BCM15, Mou16] by *internalizing* parametricity as part of our type theory. Bernardy and Moulin introduce so-called *parametricity primitives*, new type and term formers that make it possible to prove theorems such as the following.

$$(f:(A\mathcal{U}) \to A \to A) (A\mathcal{U}) (a:A) \to \mathsf{Id}_A(fAa, a)$$

Notably, these primitives have a computational interpretation. We take the ideas of internal parametricity and apply them to contentful equality, producing a *parametric cubical type theory*.

Internalizing parametricity has the advantage of allowing us to use parametricity results without going outside the theory. It is, moreover, coherent with the perspective that leads us to the univalence axiom. From one angle, univalence serves to internalize the action of type-theoretic constructions on isomorphisms. In much the same way, internal parametricity expresses the action of constructions on relations. We are not the first to remark on the similarity between the two—both Atkey *et al.* and Bernardy *et al.* make the observation—but we will endeavor here to sharpen the comparison. Parametric type theory bears a strong resemblance to cubical type theory, particularly as presented by Bernardy, Coquand, and Moulin (BCM) [BCM15]. We will explore that resemblance here, with special attention to the points at which cubical and parametric type theory diverge.

**Contributions.** Our results can be divided into several camps, depending on how they relate to the interplay between internal parametricity and cubical equality.

First, we establish that parametricity primitives can in fact be added to cubical type theory. Our combined type theory is grounded in a computational interpretation in the style of Allen [All87], following the work of Angiuli *et al.* for cubical type theory [AFH18]. Starting from the computational interpretation, we abstract a formal, generalized algebraic type theory. We show that this theory also has interpretation in (some variety of) Kan bicubical sets. In all these constructions, the cubical side is already fairly well understood, so we focus on the parametricity primitives.

Next, we come to applications. On the one hand, we use internal parametricity as a tool for proving theorems in cubical type theory. Here, the smash product is our representative example of a higher inductive type with complex algebraic structure. We show that in internally parametric type theory, we can obtain the higher coherence properties of the smash product in a uniform way. While the proofs are still not trivial, they are distinguished from the prior work by their scalability: it is not much more difficult to obtain $n$-coherent structure than 1-coherent structure.

On the other hand, we use the well-behaved equality of cubical type theory to regularize parametric type theory. Just as cubical equality produces an extensionality principle for function types, it implies extensionality principles for the parametricity primitives. In the presence of univalence, we can also make do with a weaker version of Gel-types, the other parametricity primitive, than is used in the BCM theory. This allows us to give a simpler

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:7

model of the theory, avoiding the technical device of *refined presheaves* used in the BCM model.

Finally, we compare the design principles underlying cubical and parametric type theory. In both cases, some kind of structures on pairs of types are represented by maps out of an interval object. In cubical type theory, the structures are isomorphisms; in parametric type theory, they are relations. As we will see, parametric type theory has its own analogue of the univalence axiom. However, in parametric type theory it is key that relations are represented by *affine*, not structural, maps out of the interval object. This puts parametric type theory in especially close correspondence with the Bezem-Coquand-Huber (BCH) cubical set model [BCH13], the first constructive model of univalent type theory. Conversely, an affine path interval does not give rise to a particularly well-behaved contentful equality, being particularly problematic for modeling higher inductive types; the BCH model has largely been supplanted by structural cubical type theories and models.

**Outline.** We begin by informally reviewing cubical type theory in Section 1, closely following the presentations of Angiuli *et al.* [AFH18, ABC$^{+}$19, Ang19]. In Section 2, we mix in the parametricity primitives. As we go, we compare the components of internal parametricity to their cubical counterparts.

In Section 3, we put the theory to work, going through a variety of examples that display first ordinary internal parametricity, then the regularizing effects of cubical equality, and finally the application of parametricity to the problem of the smash product. In particular, we show how the interaction between the parametricity primitives and inductive types can be characterized using the relational equivalence of univalence. We also define and explore the properties of the *sub-universe of bridge-discrete types*, which plays a role in internal parametricity analogous to that of the *identity extension lemma* in external parametricity. Some of our results are already valid in non-cubical parametric type theory but are observed for the first time here.

We get precise about the theory beginning in Section 4, where we lay out its computational interpretation. In Section 5 we abstract a generalized algebraic formal type theory which has the computational interpretation as a model, and in Section 6 we describe a second model in Kan cartesian-affine bicubical sets. We consider related work and future directions in Section 7.

## 1. CUBICAL TYPE THEORY

Cubical type theory is an extension of Martin-Löf type theory with an explicitly contentful equality. These equalities are called *paths*, as they intuitively mimic the notion of path from topology. To wit, a path in a topological space $X$ is a function $p : \mathbb{I} \to X$ from the unit interval $\mathbb{I} = [0, 1]$ into $X$. Such a path connects the endpoints $p(0), p(1) \in X$. In cubical type theory, we likewise have a type-like object, the interval “$\mathbb{I}$”, which contains two distinguished constants $0, 1$. We express paths by hypothesizing *interval variables*: a path in a type $\Gamma \gg A$ type is a term $\Gamma, x : \mathbb{I} \gg P \in A$ depending on an interval variable $x$. The path connects two endpoints, $\Gamma \gg P[0/x] \in A$ and $\Gamma \gg P[1/x] \in A$, obtained by substituting the constants $0, 1$ for the interval variable. This judgmental notion of path is internalized by *path types*. Beyond this basic apparatus, every type in cubical type theory supports *Kan operations*, called *coercion* and *composition*, which are used to manipulate paths. Coercion transports terms between types that are connected by a path; composition implements

5:8

E. CAVALLO AND R. HARPER

Vol. 17:4

operations such as transitivity and symmetry of paths. Finally, additional machinery is required to obtain univalence, the correspondence between paths of types and isomorphisms.

We follow Angiuli et al.'s account of cubical type theory [AFH18, ABC$^{+}$19], known as *cartesian cubical type theory*. Other cubical type theories and models [BCH13, CCHM15, Awo18, OP18, CMS20] vary in their treatment of the interval and formulation of the Kan operations. Although we commit to one theory here for simplicity, we expect that this paper can be replayed without difficulty using any other.

To begin at the beginning, cubical type theory is—like Martin-Löf's type theories [ML75, ML82]—based on four judgments: *A is a type, A and B are equal types, M has type A, and M and N are equal elements of type A*, all relative to a context $\Gamma$ of typed variables.

$$\Gamma \gg A \text{ type} \qquad \Gamma \gg A = B \text{ type} \qquad \Gamma \gg M \in A \qquad \Gamma \gg M = N \in A$$

A final judgment $\Gamma \text{ ctx}$ ($\Gamma$ is a context) specifies the well-formed variable contexts, which are lists of assumptions of the form $a : A$ (a ranges over terms of type $A$) among others we will introduce in a moment. (We will follow standard practice in omitting the prefix $\Gamma \gg$ from judgments when the context is irrelevant to the discussion.) Note that the equality judgments express an external, contentless equality, which is distinct from the contentful path equality. The external 'exact' equality is necessary on the judgmental level, but it need not be accessible from within the theory.

It is useful to further introduce a *substitution* judgment $\Gamma' \gg \gamma \in \Gamma$ (with equality counterpart $\Gamma' \gg \gamma = \gamma' \in \Gamma$); a substitution is a list $\gamma = (M_1/a_1, \dots, M_n/a_n)$ instantiating each variable in $\Gamma$ with a term over the variables in $\Gamma'$. We write $N\gamma$ for the application of $\gamma$ to a term $N$, that is, the result of replacing each occurrence of $a_i$ in $N$ with $M_i$. Each of the judgments above is preserved by substitution; for example, if $\Gamma' \gg \gamma \in \Gamma$ and $\Gamma \gg M \in A$, then $\Gamma' \gg M\gamma \in A\gamma$.

We think of these judgments as speaking about programs $A, B, M, N$ in some untyped language with an operational semantics. They are *behavioral specifications*: $\Gamma \gg A$ type means that for any instantiation of the hypotheses $\Gamma$, the program $A$ computes a value that names some specification. Likewise, $\Gamma \gg M \in A$ means that $M$ computes to a value satisfying the specification computed by $A$. We use the notation $\gg$ and $\in$ (as opposed to the typical $\vdash$ and $\cdot$) to indicate that we are speaking about this computational interpretation; we will develop a purely formal counterpart for the theory in Section 5. For the moment, we will be vague about the exact meaning of 'computes' in the cubical setting, in the interest of first giving a sense of the shape of cubical and parametric type theory. We lay out the computational interpretation in detail in Section 4. Until that point, we describe the system by presenting inference rules that will turn out to be true in the semantics; note that these are theorems, not definitions.

1.1. **The interval.** Cubical type theory adds a new form of judgment, $\Gamma \gg r \in \mathbb{I}$ ($r$ is an interval term), and its associated equality judgment $\Gamma \gg r = s \in \mathbb{I}$. The two endpoints are interval terms, and we can add interval variables to the context.

$$\overline{\Gamma \gg 0 \in \mathbb{I}} \qquad \overline{\Gamma \gg 1 \in \mathbb{I}} \qquad \overline{\Gamma \text{ ctx}} \qquad \overline{\Gamma, x : \mathbb{I} \text{ ctx}} \qquad \overline{\Gamma, x : \mathbb{I} \gg x \in \mathbb{I}}$$

Interval variables behave just like term variables, at least in the sense that they are *structural*: we have weakening, contraction, and exchange principles, as embodied by the following

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:9

PATH-FORM

\[
\frac {\Gamma , x : \mathbb {I} \gg A \text {type} \qquad \Gamma \gg M _ {0} \in A [ 0 / x ] \qquad \Gamma \gg M _ {1} \in A [ 1 / x ]}{\Gamma \gg \operatorname{Path} _ {x . A} (M _ {0} , M _ {1}) \text {type}}
\]

PATH-INTRO

\[
\frac {\Gamma , x : \mathbb {I} \gg M \in A}{\Gamma \gg \lambda^ {\mathbb {I}} x . M \in \operatorname{Path} _ {x . A} (M [ 0 / x ] , M [ 1 / x ])}
\]

PATH-ELIM

\[
\frac {\Gamma \gg P \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1}) \qquad \Gamma \gg r \in \mathbb {I}}{\Gamma \gg P @ r \in A [ r / x ]}
\]

PATH- \( \beta \)

\[
\frac {\Gamma , x : \mathbb {I} \gg M \in A}{\Gamma \gg (\lambda^ {\mathbb {I}} x . M) @ r = M [ r / x ] \in A [ r / x ]}
\]

PATH- \( \partial \)

\[
\frac {\Gamma \gg P \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1}) \qquad \varepsilon \in \{0 , 1 \}}{\Gamma \gg P @ \varepsilon = M _ {\varepsilon} \in A [ \varepsilon / x ]}
\]

PATH-η

\[
\frac {\Gamma \gg P \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1})}{\Gamma \gg P = \lambda^ {\mathbb {I}} x . P @ x \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1})}
\]

Figure 1: Rules for Path-types

substitution rules defined for any \(\Gamma\) ctx.

I-WEAKENING

\[
\overline {{\Gamma , x : \mathbb {I} \gg \mathsf {p} _ {\mathbb {I}} \in \Gamma}}
\]

I-CONTRACTION

\[
\overline {{\Gamma , z : \mathbb {I} \gg (\mathrm{id} _ {\Gamma} , z / x , z / y) \in (\Gamma , x : \mathbb {I} , y : \mathbb {I})}}
\]

I-EXCHANGE

\[
\overline {{\Gamma , y : \mathbb {I} , x : \mathbb {I} \gg (\mathrm{id} _ {\Gamma} , x / x , y / y) \in (\Gamma , x : \mathbb {I} , y : \mathbb {I})}}
\]

We may also exchange interval variable assumptions with term variable assumptions when it makes type sense to do so. The contraction and exchange substitutions may be derived from the following more fundamental rule, which allows us to extend a substitution by a path interval term.

I-SUBST

\[
\frac {\Gamma^ {\prime} \gg \gamma \in \Gamma \qquad \Gamma^ {\prime} \gg r \in \mathbb {I}}{\Gamma^ {\prime} \gg (\gamma , r / x) \in (\Gamma , x : \mathbb {I})}
\]

Finally, cubical type theory includes one more way to extend the context: with a constraint, an assumption that two interval terms are (exactly) equal. These become relevant when we introduce composition below.

\[
\frac {\Gamma \gg r \in \mathbb {I} \quad \Gamma \gg s \in \mathbb {I}}{\Gamma \gg r = s \text {   constraint }}
\]

\[
\frac {\Gamma \gg \xi \text {   constraint }}{(\Gamma , \xi) \text {   ctx }}
\]

\[
\frac {\Gamma \gg r \in \mathbb {I} \qquad \Gamma \gg s \in \mathbb {I}}{\Gamma , r = s \gg r = s \in \mathbb {I}}
\]

Once again, we have weakening, exchange, and contraction for constraints.

Aside from these additions, the judgmental apparatus of cubical type theory matches ordinary Martin-Löf type theory. We take standard type formers (functions, products, universes) for granted and proceed to the novel components: Path-types, the Kan operations, V-types (which underlie univalence), and higher inductive types.

5:10

E. CAVALLO AND R. HARPER

Vol. 17:4

1.2. Path-types. Path-types simply internalize dependence on an interval variable, much as function types internalize dependence on a term variable. When we have a type $x : \mathbb{I} \gg A$ type depending on an interval variable $x$ and elements $M_0 \in A[0/x]$ and $M_1 \in A[1/x]$ inhabiting its endpoints, we can form the type $\mathsf{Path}_{x.A}(M_0, M_1)$ of paths from $M_0$ to $M_1$ over $x.A$. Recall that the univalence axiom, which we will validate in due time, identifies paths between types with isomorphisms. With that intuition in mind, we think of an element of $\mathsf{Path}_{x.A}(M_0, M_1)$ as a proof that $M_0$ corresponds to $M_1$ along the isomorphism between $A[0/x]$ and $A[1/x]$ represented by $x.A$. In the special case that $A$ does not depend on $x$, an element of $\mathsf{Path}_{\_A}(M_0, M_1)$ is simply an identification between $M_0$ and $M_1$ in $A$. (In that case, we generally write $\mathsf{Path}_A(M_0, M_1)$ rather than $\mathsf{Path}_{\_A}(M_0, M_1)$.)

Rules for Path-types are displayed in Figure 1. Like functions, we introduce paths by abstraction: if $x : \mathbb{I} \gg M \in A$, then $\lambda^{\mathbb{I}}x.M$ is a path from $M[0/x]$ to $M[1/x]$. Conversely, if we have a path $P \in \mathsf{Path}_{x.A}(M_0, M_1)$, we can apply it to any interval term $r$ to get an element $P@r \in A[r/x]$. (Moreover, we have $P@0 = M_0$ and $P@1 = M_1$.) Abstraction and application interact via the usual $\beta$- and $\eta$-rules for function types.

Although many theorems rely on the Kan operations introduced in the next section, we can observe some basic facts about paths already. First, we have reflexive paths given by interval variable weakening.

$$\frac{M \in A}{\lambda^{\mathbb{I}}x.M \in \mathsf{Path}_A(M, M)}$$

Second, functions act on paths. Note that we also use weakening here when we apply $F$ in a context extended with $x : \mathbb{I}$.

$$\frac{F \in (a:A) \to B \qquad P \in \mathsf{Path}_A(M_0, M_1)}{\lambda^{\mathbb{I}}x.F(P@x) \in \mathsf{Path}_{x.B[P@x/a]}(FM_0, FM_1)}$$

Finally, we have function extensionality: functions are path-equal when they are point-wise path-equal. Although function extensionality is a (non-trivial) consequence of univalence [Uni13, §4.9], cubically it follows more directly from exchange of term and interval variables.

$$\frac{F_0, F_1 \in (a:A) \to B \qquad H \in (a:A) \to \mathsf{Path}_B(F_0a, F_1a)}{\lambda^{\mathbb{I}}x.\lambda a.Ha@x \in \mathsf{Path}_{(a:A)\to B}(F_0, F_1)}$$

It is easy to see that this function is an isomorphism—its inverse simply exchanges the arguments in the opposite order.

The preceding argument can more generally characterize $\mathsf{Path}_{x.(a:A)\to B}(F_0, F_1)$ when $B$ depends on $x$, but not when $A$ does: if $A$ depends on $x$, then the type “$(a:A) \to \mathsf{Path}_{x.B}(F_0a, F_1a)$” is nonsensical. In the most general case, we can instead construct a map taking paths between functions to functions from paths to paths: “equal functions take equal arguments to equal results.”

Lemma 1.1. Let $x : \mathbb{I} \gg A$ type, $x : \mathbb{I}, a : A \gg B$ type, $F_0 \in ((a:A) \to B)[0/x]$, and $F_1 \in ((a:A) \to B)[1/x]$ be given. Then we have the following principle.

$$\frac{Q \in \mathsf{Path}_{x.(a:A)\to B}(F_0, F_1)}{\mathsf{funapp}(Q) \in (a_0:A[0/x])(a_1:A[1/x])(p:\mathsf{Path}_{x.A}(a_0, a_1)) \to \mathsf{Path}_{x.B[p@x/a]}(F_0a_0, F_1a_1)}$$

Proof. $\mathsf{funapp}(Q) := \lambda a_0.\lambda a_1.\lambda p.\lambda^{\mathbb{I}}x.(Q@x)(p@x)$.

□

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:11

COERCION

$$\begin{array}{l} \Gamma , x: \mathbb {I} \gg A \text {type} \quad \Gamma \gg r, s \in \mathbb {I} \quad \Gamma \gg M \in A [ r / x ] \\ \hline \Gamma \gg \operatorname {c o e} _ {x. A} ^ {r \rightsquigarrow s} (M) \in A [ s / x ] \\ \Gamma \gg \operatorname {c o e} _ {x. A} ^ {r \rightsquigarrow r} (M) = M \in A [ r / x ] \end{array}$$

HOMOGENEOUS COMPOSITION

$$\Gamma \gg A \text {type} \quad \Gamma \gg r, s \in \mathbb {I} \quad \Gamma \gg M \in A$$

$$(\forall i) \Gamma \gg \xi_ {i} \text {constraint} \quad (\forall i) \Gamma , \xi_ {i}, x: \mathbb {I} \gg N _ {i} \in A$$

$$(\forall i) \Gamma , \xi_ {i} \gg M = N _ {i} [ r / x ] \in A \quad (\forall i, j) \Gamma , \xi_ {i}, \xi_ {j}, x: \mathbb {I} \gg N _ {i} = N _ {j} \in A$$

$$\Gamma \gg \mathsf {h c o m} _ {A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) \in A$$

$$(\forall j) \Gamma , \xi_ {j} \gg \mathsf {h c o m} _ {A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = N _ {j} [ s / x ] \in A$$

$$\Gamma \gg \mathsf {h c o m} _ {A} ^ {r \rightsquigarrow r} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = M \in A$$

HETEROGENEOUS COMPOSITION

$$\Gamma , x: \mathbb {I} \gg A \text {type} \quad \Gamma \gg r, s \in \mathbb {I} \quad \Gamma \gg M \in A [ r / x ]$$

$$(\forall i) \Gamma \gg \xi_ {i} \text {constraint} \quad (\forall i) \Gamma , \xi_ {i}, x: \mathbb {I} \gg N _ {i} \in A$$

$$(\forall i) \Gamma , \xi_ {i} \gg M = N _ {i} [ r / x ] \in A [ r / x ] \quad (\forall i, j) \Gamma , \xi_ {i}, \xi_ {j}, x: \mathbb {I} \gg N _ {i} = N _ {j} \in A$$

$$\Gamma \gg \mathsf {c o m} _ {x. A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) \in A [ s / x ]$$

$$(\forall j) \Gamma , \xi_ {j} \gg \mathsf {c o m} _ {x. A} ^ {r \rightsquigarrow s} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = N _ {j} [ s / x ] \in A [ s / x ]$$

$$\Gamma \gg \mathsf {c o m} _ {x. A} ^ {r \rightsquigarrow r} (M; \overline {{\xi_ {i} \hookrightarrow x . N _ {i}}}) = M \in A [ r / x ]$$

Figure 2: Rules for coercion, homogeneous composition, and heterogeneous composition

Constructing an inverse to this function will require the coercion operator introduced in the following section.

1.3. Kan operations: coercion and composition. The judgmental path structure of cubical type theory endows each type with a "path" relation. So far, this relation is not quite a proper notion of equality. For one, while it is reflexive, it need not be symmetric or transitive. Perhaps more importantly, we do not know that type families respect paths in the following sense. If we have some family $a: A \gg B$ type and a path $P \in \mathsf{Path}_A(M_0, M_1)$, we expect that for every element of $BM_0$, there is a corresponding element of $BM_1$. If we think of $B$ as a predicate on elements of $A$, we are saying that $M_1$ should satisfy the same properties as $M_0$. In fact, we would expect that $BM_0$ and $BM_1$ are isomorphic. At the moment, however, we only know that there is a path $x.B(P@x)$ from $BM_0$ to $BM_1$. What we need, then, is one direction of the univalence axiom: the ability to transform paths between types into isomorphisms. This is effected by the coercion operator coe, which satisfies the first rule in Figure 2.

Given a term at some index $r$ of a type path $x.A$, coercion produces an element at any other $s$. We can show that $\mathsf{coe}_{x.A}^{r\rightsquigarrow s}(-\in A[r/x]\to A[s/x])$ is in fact an isomorphism. The full proof relies on composition, which we have not yet introduced, but we can at least see

5:12

E. CAVALLO AND R. HARPER

Vol. 17:4

that $\mathsf{coe}_{x.A}^{1\rightharpoonup 0}(-)$ is inverse to $\mathsf{coe}_{x.A}^{0\rightharpoonup 1}(-)$ up to a path.

$$\frac{M \in A[0/x]}{\lambda^{\mathbb{I}} y.\mathsf{coe}_{x.A}^{y\rightharpoonup 0}(\mathsf{coe}_{x.A}^{0\rightharpoonup y}(M)) \in \mathsf{Path}_{A[0/x]}(M, \mathsf{coe}_{x.A}^{1\rightharpoonup 0}(\mathsf{coe}_{x.A}^{0\rightharpoonup 1}(M)))}$$

Operationally, coercion evaluates by cases on the shape of the type path $x.A$. For example, the following equation describes the behavior of coercion at a product type $x.(a:A) \times B$.

$$\frac{x:\mathbb{I}\gg A\text{ type}\quad x:\mathbb{I},a:A\gg B\text{ type}\quad M\in((a:A)\times B)[r/x]}{\mathsf{coe}_{x.(a:A)\times B}^{r\rightharpoonup s}(M)=\langle\mathsf{coe}_{x.A}^{r\rightharpoonup s}(\mathsf{fst}(M)),\mathsf{coe}_{x.B[\mathsf{coe}_{x.A}^{r\rightharpoonup s}(\mathsf{fst}(M))/a]}^{r\rightharpoonup s}(\mathsf{snd}(M))\rangle\in((a:A)\times B)[s/x]}$$

Homogeneous composition (which we will often just call composition) serves a more technical purpose: to evaluate coercions along lines of the form $x.\mathsf{Path}_{y.A}(N_0,N_1)$. For the moment, let us assume that $A$ does not depend on $x$. In order to execute such a coercion, we must be able to adjust the endpoints of a given path by another pair of paths. That is, given $M\in\mathsf{Path}_{y.A}(M_0,M_1)$ and lines $x.N_0$, $x.N_1$ fitting into the following shape, we should be able to produce a new, “adjusted” path shown as a dashed line below.

![img-1.jpeg](img-1.jpeg)

Homogeneous composition, written hcom, is a generalized form of this operation that adjusts the boundary of a term, a boundary being specified by a sequence of constraints on interval variables. As an example, the adjusted path above is obtained as the following composite.

$$y:\mathbb{I}\gg\mathsf{hcom}_{A}^{0\rightharpoonup 1}(M\@y;y=0\hookrightarrow x.N_{0},y=1\hookrightarrow x.N_{1})\in A$$

The general operator has the form $\mathsf{hcom}_{A}^{r\rightharpoonup s}(M;\overline{\xi_{i}\hookrightarrow x.N_{i}})$; it is characterized by the second rule of Figure 2. We use the notation $\overline{\xi_{i}\hookrightarrow x.N_{i}}$ to denote a finite list of constraint-line pairs $\xi_{1}\hookrightarrow x.N_{1},\ldots,\xi_{n}\hookrightarrow x.N_{n}$, implicitly quantifying over an indexing variable $i$. Like coercion, we define homogeneous composition by case analysis of the type argument. Where the special case involving a pair of constraints $y=0$ and $y=1$ on a single interval variable is enough for coercion in the path type, the general form becomes necessary to implement composition in the path type; the general form thus represents a “strengthened induction hypothesis”.

To handle coercion along $x.\mathsf{Path}_{y.A}(N_0,N_1)$ when $A$ does depend on $x$, we can combine coercion and composition into a unified heterogeneous composition operator, com, which coerces an input across a type line while simultaneously adjusting by a boundary path along that line. Defined as follows, com satisfies the third rule shown in Figure 2.

$$\mathsf{com}_{x.A}^{r\rightharpoonup s}(M;\overline{\xi_{i}\hookrightarrow x.N_{i}}):=\mathsf{hcom}_{A[s/x]}^{r\rightharpoonup s}(\mathsf{coe}_{x.A}^{r\rightharpoonup s}(M);\overline{\xi_{i}\hookrightarrow x.\mathsf{coe}_{x.A}^{x\rightharpoonup s}(N_{i})})$$

Both hcom and coe can be recovered from com, so the latter is may be taken as primitive instead, as in [CCHM15, AFH18]. Either way, the ability to decompose com into hcom and coe plays a key role in defining Kan operations for higher inductive types [CHM18, CH19a].

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:13

Coercion and composition are together referred to as the Kan operations, being inspired by the Kan condition of algebraic topology [Kan55]. For each type we wish to introduce to cubical type theory, we must explain how the Kan operations evaluate at that type. This can be carried out for all the standard type formers of Martin-Löf type theory (functions, products, inductive types, universes); we refer to Angiuli [Ang19] for a thorough accounting of those results.

Using coercion, we can prove the converse to Lemma 1.1: if two functions take equal arguments to equal results, then they are equal as functions.

Lemma 1.2. Let $x : \mathbb{I} \gg A$ type, $x : \mathbb{I}, a : A \gg B$ type, $F_0 \in ((a:A) \to B)[0/x]$, and $F_1 \in ((a:A) \to B)[1/x]$ be given. Then we have the following.

$$\frac{H \in (a_0 : A[0/x]) (a_1 : A[1/x]) (p : \mathsf{Path}_{x.A}(a_0, a_1)) \to \mathsf{Path}_{x.B[p \otimes x/a]} (F_0 a_0, F_1 a_1)}{\mathsf{funext}(H) \in \mathsf{Path}_{x.(a:A) \to B}(F_0, F_1)}$$

Proof. $\mathsf{funext}(H) := \lambda^\mathbb{I}x.\lambda a.H(\mathsf{coe}_{x.A}^{x \to 0}(a))(\mathsf{coe}_{x.A}^{x \to 1}(a))(\lambda^\mathbb{I}y.\mathsf{coe}_{x.A}^{x \to y}(a))$.

Essentially, given an interval variable $x : \mathbb{I}$ and an element $a$ of $A$ (at index $x$), we can extend the point $a$ to a path over $x.A$ by coercion.

Coercion and composition also give us an analogue of the Martin-Löf identity type elimination principle (often called “J”) for paths.

Lemma 1.3. Let $A$ type and $M \in A$ be given. Suppose we are given the following:

$\triangleright a : A, p : \mathsf{Path}_A(M, a) \gg C$ type,

$\triangleright N \in C[M, \lambda^\mathbb{I}...M/a, p]$,

$\triangleright M' \in A$ and $P \in \mathsf{Path}_A(M, M')$.

Then there is some $\mathsf{J}_{a.p.C}(N, P) \in C[M', P/a, p]$.

Proof. Define an auxiliary $x : \mathbb{I}, y : \mathbb{I} \gg Q \in A$ as follows.

$$Q := \mathsf{hcom}_A^{0 \to y} (P \otimes 0; x = 0 \hookrightarrow ...P \otimes 0, x = 1 \hookrightarrow y.P \otimes y)$$

Set $\mathsf{J}_{a.p.C}(N, P) := \mathsf{coe}_{x.C[Q[1/y], \lambda^\mathbb{I}y.Q/a, p]}^{0 \to 1}(N)$.

This is slightly weaker than the elimination principle enjoyed by Martin-Löf’s elimination principle, as it is not the case that $\mathsf{J}_{a.p.C}(N, \lambda^\mathbb{I}...M) = N \in C[M, \lambda^\mathbb{I}...M/a, p]$ in general; this equation may be shown to hold up to a path, but does not hold up to exact equality. One may separately introduce identity types to cubical type theory that do satisfy this principle, either via a special construction [CCHM15, ABC$^+$19] or as particular indexed inductive types [CH19a], and in this case one has $\mathsf{Id}_A(M, M') \simeq \mathsf{Path}_A(M, M')$. By univalence, this isomorphism implies that path and identity types satisfy the same theorems; in particular, it justifies our citing theorems about identity types in homotopy type theory as theorems about path types going forward. Of course, these theorems are often more easily proven in cubical type theory by reasoning directly with paths.

1.4. V-types and univalence. The Kan operations account for one direction of the univalence axiom: the mapping from paths between types to isomorphisms. The inverse is defined using V-types, which produce paths in the universe from isomorphisms.$^1$

First, let us take the opportunity to define isomorphism precisely.

$^1$Some formulations of cubical type theory instead use Glue-types, which have V-types as a special case. The points we make here about V-types apply equally well to Glue-types.

5:14

E. CAVALLO AND R. HARPER

Vol. 17:4

V-FORM

$$\frac{\Gamma, r = 0 \gg A \text{ type} \quad \Gamma \gg B \text{ type} \quad \Gamma, r = 0 \gg I \in \text{Iso}(A, B)}{\Gamma \gg V_r(A, B, I) \text{ type}}$$

V-FORM-$\partial_0$

$$\frac{\Gamma \gg A \text{ type} \quad \Gamma \gg B \text{ type} \quad I \in \text{Iso}(A, B)}{\Gamma \gg V_0(A, B, I) = A \text{ type}}$$

V-FORM-$\partial_1$

$$\frac{\Gamma \gg B \text{ type}}{\Gamma \gg V_1(A, B, I) = B \text{ type}}$$

V-INTRO

$$\frac{\Gamma, r = 0 \gg M \in A \quad \Gamma \gg N \in B \quad \Gamma, r = 0 \gg \text{fst}(I)(M) = N \in B}{\Gamma \gg \text{vin}_r(M, N) \in V_r(A, B, I)}$$

V-INTRO-$\partial_0$

$$\frac{\Gamma \gg M \in A \quad \Gamma \gg N \in B \quad \Gamma \gg \text{fst}(I)(M) = N \in B}{\Gamma \gg \text{vin}_0(M, N) = M \in A}$$

V-INTRO-$\partial_1$

$$\frac{\Gamma \gg N \in B}{\Gamma \gg \text{vin}_1(M, N) = N \in B}$$

V-ELIM

$$\frac{\Gamma \gg P \in V_r(A, B, I)}{\Gamma \gg \text{vproj}_r(P, I) \in B}$$

V-ELIM-$\partial_0$

$$\frac{\Gamma \gg P \in A \quad I \in \text{Iso}(A, B)}{\Gamma \gg \text{vproj}_0(P, I) = \text{fst}(I)(P) \in B}$$

V-ELIM-$\partial_1$

$$\frac{\Gamma \gg P \in B}{\Gamma \gg \text{vproj}_1(P, I) = P \in B}$$

Figure 3: Rules for V-types. See [Ang19] for $\beta$- and $\eta$-rules.

**Definition 1.4.** Let a function $F \in A \to B$ be given. The types $\text{Linv}(A, B, F)$ and $\text{Rinv}(A, B, F)$ of left and right inverses to $F$ are defined as follows.

$$\text{Linv}(A, B, F) := (g : B \to A) \times ((a : A) \to \text{Path}_A(g(Fa), a))$$

$$\text{Rinv}(A, B, F) := (g : B \to A) \times ((b : B) \to \text{Path}_B(F(gb), b))$$

We say $F$ is an isomorphism when it is equipped with a left and right inverse.

$$\text{islso}(A, B, F) := \text{Linv}(A, B, F) \times \text{Rinv}(A, B, F)$$

The type of isomorphisms between $A$ and $B$ is then $\text{Iso}(A, B) := (f : A \to B) \times \text{islso}(A, B, f)$.

Isomorphisms are frequently known as *equivalences* in the literature on univalent type theory. There are several isomorphic formulations of the type $\text{Iso}(A, B)$; we refer to [Uni13, Chapter 4] for more details. (Our definition is there called a *bi-invertible map*). A key property of $\text{islso}(A, B, F)$ is that it is a proposition in the following sense [Uni13, Theorem 4.3.2].

**Definition 1.5.** *A* type is a *proposition* if any two elements of $A$ are equal up to a path, as captured by the following type.

$$\text{isProp}(A) := (a : A) (b : A) \to \text{Path}_A(a, b)$$

While the V-type is used principally to convert isomorphisms to paths, it is a bit more general: it takes a path and an isomorphism and composes them to produce a new path. That is, if we have a path of types $B$ in a direction $x$ and an isomorphism $I$ between some

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:15

A and B[0/x], their V-type fits into the following (“V-shaped”) diagram.

$$\begin{array}{c} A \\ I \downarrow \\ B_0 \xrightarrow{} B \\ x \to \end{array} \xrightarrow{} B_1$$

Rules for V-types are shown in Figure 3. We convert isomorphisms to paths in the universe by applying V with a degenerate path.

$$\frac{A \in \mathcal{U} \quad B \in \mathcal{U} \quad I \in \text{Iso}(A, B)}{\text{ua}(A, B, I) := \lambda^{\mathbb{I}} x . \mathsf{V}_x(A, B, I) \in \text{Path}_{\mathcal{U}}(A, B)}$$

Here, x does not appear in B, so we are composing the isomorphism I with the reflexive path ...B. This reflexive path corresponds to the identity isomorphism on B, so when we pre-compose with I we simply get a path corresponding to I.

We will not be using V-types directly in the future, only the univalence axiom that they enable. Rather, we introduce them here in order to make a comparison with their parametric equivalent in Section 2.4. For that purpose, let us give some intuition as to why V is formulated as it is. Univalence involves a “dimension shift”: it takes a point in the type of isomorphisms and produces a path in the universe, which is an element one dimension higher. However, we cannot impose in the typing rule for $\mathsf{V}_x(A, B, I)$ that A, B, I live “one dimension lower,” i.e., are degenerate in x, because this property is not stable under substitution. For example, mod(M, x) may be degenerate in some y, but mod(M, x)[y/x] is certainly not degenerate in y[y/x]. All aspects of type theory should be stable under substitution, so this is a non-starter. Instead, we structure $\mathsf{V}_r$ in such a way that it does not involve a dimension shift; both the input and the output vary in the direction r.

1.5. Higher inductive types. Finally, cubical type theory can include a variety of higher inductive types. These can be seen as a mutual generalization of inductive types and quotients; they are inductive definitions that permit path constructors in addition to ordinary constructors.

It is beyond the scope of this work to give a comprehensive account of higher inductive types in cartesian cubical type theory; for that, we refer to [CH19a]. We will instead go by way of example, expanding on the type $\mathbb{Z}/2\mathbb{Z}$ of integers mod 2 specified in the introduction.

data $\mathbb{Z}/2\mathbb{Z}$ where

| in(n : $\mathbb{Z}$) $\in \mathbb{Z}/2\mathbb{Z}$

| mod(n : $\mathbb{Z}$, x : $\mathbb{I}$) $\in \mathbb{Z}/2\mathbb{Z}$ [x = 0 $\hookrightarrow$ in(n) | x = 1 $\hookrightarrow$ in(n + 2)]

The mod constructor exemplifies the format of a path constructor: it takes one or more interval variables as arguments, and it has a specified boundary which can refer to its arguments and previous construtors. This specification indicates the following introduction and boundary rules for in and mod.

$$\frac{\Gamma \gg N \in \mathbb{Z}}{\Gamma \gg \text{in}(N) \in \mathbb{Z}/2\mathbb{Z}}$$

$$\frac{\Gamma \gg N \in \mathbb{Z} \quad \Gamma \gg r \in \mathbb{I}}{\Gamma \gg \text{mod}(N, r) \in \mathbb{Z}/2\mathbb{Z}}$$

$$\frac{\Gamma \gg N \in \mathbb{Z}}{\Gamma \gg \text{mod}(N, 0) = \text{in}(N) \in \mathbb{Z}/2\mathbb{Z}}$$

$$\frac{\Gamma \gg N \in \mathbb{Z}}{\Gamma \gg \text{mod}(N, 1) = \text{in}(N + 2) \in \mathbb{Z}/2\mathbb{Z}}$$

5:16

E. CAVALLO AND R. HARPER

Vol. 17:4

The eliminator for $\mathbb{Z}/2\mathbb{Z}$ naturally takes clauses to handle the in and mod cases. The mod case is required to cohere with the in case on its boundary, which ensures that every function out of $\mathbb{Z}/2\mathbb{Z}$ takes $\text{in}(n)$ and $\text{in}(n+2)$ to path-equal results.

$$\begin{array}{l} \Gamma, a: \mathbb{Z}/2\mathbb{Z} \gg C \text{ type} \quad \Gamma \gg M \in \mathbb{Z}/2\mathbb{Z} \\ \Gamma, n: \mathbb{Z} \gg Q_{\text{in}} \in C[\text{in}(n)/a] \quad \Gamma, n: \mathbb{Z}, x: \mathbb{I} \gg Q_{\text{mod}} \in C[\text{mod}(n, x)/a] \\ \Gamma, n: \mathbb{Z} \gg Q_{\text{mod}}[0/x] = Q_{\text{in}} \in C[\text{in}(n)/a] \\ \Gamma, n: \mathbb{Z} \gg Q_{\text{mod}}[1/x] = Q_{\text{in}}[n+2/n] \in C[\text{in}(n+2)/a] \\ \hline \Gamma \gg \text{mod-elim}_{a.C}(M, n.Q_{\text{in}}, n.x.Q_{\text{mod}}) \in C[M/a] \end{array}$$

When applied to a constructor, the eliminator steps accordingly as shown below.

$$\text{mod-elim}_{a.C}(\text{in}(N), n.Q_{\text{in}}, n.x.Q_{\text{mod}}) = Q_{\text{in}}[N/n] \in C[\text{in}(N)/a]$$

$$\text{mod-elim}_{a.C}(\text{mod}(N, r), n.Q_{\text{in}}, n.x.Q_{\text{mod}}) = Q_{\text{mod}}[N/n][r/x] \in C[\text{mod}(N, r)/a]$$

## 2. PARAMETRIC TYPE THEORY

We now proceed to add parametricity primitives to our cubical type theory. We follow the blueprint of Bernardy, Coquand, and Moulin (BCM) [BCM15], which is a substantial simplification of Bernardy and Moulin's original parametric theory [BM12]. The BCM parametric type theory has the same basic shape as cubical type theory: relatedness is represented by maps out of an interval object I. We henceforth refer to $\mathbb{I}$ as the path interval and I as the bridge interval; we call maps out of I bridges, following [NVD17]. (As a general rule, we use boldface to distinguish bridge constructs from their path equivalents.) The connection between internal parametricity and cubical type theory has never been a secret; Bernardy and Moulin already remark on the similarity in [BM12], and later iterations of their work resemble cubical type theory even more strongly.

We go a bit further and compare the two in detail over the course of this section. First, there is the obvious difference: parametric type theory has no analogues of coercion and composition. More subtle is the difference between the two intervals $\mathbb{I}$ and I: the path interval behaves structurally, but the bridge interval is affine. This has two essential effects on the theory. First, it enables a "function extensionality" principle analogous to Lemma 1.2 that does not rely on coercion. Second, it means that we can avoid the V-shape of V-types, instead supporting a type former (Gel) that directly converts relations to bridges.

On a more mundane level, we present the parametricity elements using a notation more similar to that of cubical type theory. For a translation to Bernardy et al.'s (substantially different) notation, see Figure 10 on page 51.

2.1. The bridge interval. Recall our intuition for a term $x: \mathbb{I} \gg M \in A$: the path $x.A$ stands for an isomorphism $A[0/x] \simeq A[1/x]$ via univalence, and $x.M$ is a proof that $M[0/x]$ corresponds to $M[1/x]$ across this isomorphism. Likewise, a bridge of types $\boldsymbol{x}: \mathbf{I} \gg A$ type stands for a binary relation on $A[\mathbf{0}/\boldsymbol{x}]$ and $A[\mathbf{1}/\boldsymbol{x}]$, and a term $\boldsymbol{x}: \mathbf{I} \gg M \in A$ is a proof that $M[\mathbf{0}/\boldsymbol{x}]$ and $M[\mathbf{1}/\boldsymbol{x}]$ stand in this relation.

We start with a judgment $\Gamma \gg \boldsymbol{r} \in \mathbf{I}$. Like the path interval, it is populated by two endpoint $\mathbf{0}$ and $\mathbf{1}$, and we can suppose bridge interval variables.

$$\overline{\Gamma \gg \mathbf{0} \in \mathbf{I}} \qquad \overline{\Gamma \gg \mathbf{1} \in \mathbf{I}} \qquad \overline{\Gamma \text{ ctx}} \qquad \overline{\Gamma, \boldsymbol{x}: \mathbf{I} \text{ ctx}} \qquad \overline{\Gamma, \boldsymbol{x}: \mathbf{I} \gg \boldsymbol{x} \in \mathbf{I}}$$

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:17

Unlike path variables, however, we will only have weakening and exchange for the bridge interval: the contraction principle fails. The bridge interval is thus substructural, in particular affine.

The lack of contraction means that we cannot always apply a bridge variable substitution $-[\boldsymbol{y}/\boldsymbol{x}]$ to a term $M$: if $M$ already mentions $\boldsymbol{y}$, this amounts to contracting $\boldsymbol{y}$ and $\boldsymbol{x}$. What we have is fresh substitution: we can substitute a variable $\boldsymbol{y}$ for $\boldsymbol{x}$ in $M$ when $\boldsymbol{y}$ does not occur in $M$ (i.e., is apart from $M$). To formulate fresh substitution for open terms, we define the following context restriction operation, roughly following Cheney's approach to nominal type theory [Che12]. Intuitively, given a context $\Gamma$ and interval term $\boldsymbol{r}$ in that context, $\Gamma\backslash\boldsymbol{r}$ is the part of $\Gamma$ guaranteed to be apart from $\boldsymbol{r}$: when $\boldsymbol{r}$ is a variable $\boldsymbol{x}$, it includes all other bridge variables, all path variables, constraints that do not involve $\boldsymbol{r}$, and those term variables that are introduced before $\boldsymbol{r}$. The constants $\mathbf{0}$ and $\mathbf{1}$ are considered to be apart from everything. That is, we define $\Gamma\backslash\boldsymbol{r} := \Gamma$ when $\Gamma \gg \boldsymbol{r} = \boldsymbol{\varepsilon} \in \mathbf{I}$ for some $\boldsymbol{\varepsilon} \in \{\mathbf{0}, \mathbf{1}\}$ and as follows otherwise.

$$(\Gamma, y : \mathbb{I})\backslash\boldsymbol{x} := \Gamma\backslash\boldsymbol{x}, y : \mathbb{I}$$

$$(\Gamma, a : A)\backslash\boldsymbol{x} := \Gamma\backslash\boldsymbol{x}$$

$$(\Gamma, \boldsymbol{y} : \mathbf{I})\backslash\boldsymbol{x} := \begin{cases} \Gamma & \text{if } \boldsymbol{x} = \boldsymbol{y} \\ \Gamma\backslash\boldsymbol{x}, \boldsymbol{y} : \mathbf{I} & \text{if } \boldsymbol{x} \neq \boldsymbol{y} \end{cases}$$

$$(\Gamma, \xi)\backslash\boldsymbol{x} := \begin{cases} \Gamma\backslash\boldsymbol{x} & \text{if } \boldsymbol{x} \text{ occurs in } \xi \\ \Gamma\backslash\boldsymbol{x}, \xi & \text{otherwise} \end{cases}$$

We then have the following rule for extending a substitution by a bridge interval term.

$$\frac{\begin{array}{c} \text{I-SUBST} \\ \Gamma' \gg \boldsymbol{r} \in \mathbf{I} \quad \Gamma'\backslash\boldsymbol{r} \gg \gamma \in \Gamma \\ \hline \Gamma' \gg (\gamma, \boldsymbol{r}/\boldsymbol{x}) \in \Gamma \end{array}}{}$$

The restriction in the premises prevents us from deriving, in particular, the following contraction or "diagonal" substitution, which attempts to substitute the same bridge variable $\boldsymbol{x}$ for two distinct variables $\boldsymbol{y}$ and $\boldsymbol{z}$.

$$\boldsymbol{x} : \mathbf{I} \gg (\boldsymbol{x}/\boldsymbol{y}, \boldsymbol{x}/\boldsymbol{z}) \in (\boldsymbol{y} : \mathbf{I}, \boldsymbol{z} : \mathbf{I}) \quad \times$$

When working with a context of the form $(\Gamma, \boldsymbol{x} : \mathbf{I}, \Gamma')$, we therefore think of the variables in $\Gamma$ as being apart from $\boldsymbol{x}$: we are disallowed from substituting a term that mentions $\boldsymbol{x}$ for a variable in $\Gamma$: in a substitution. On the other hand, we can substitute terms that mention $\boldsymbol{x}$ for variables in $\Gamma'$. In accordance with this intuition, we can exchange term variables past bridge variables in one direction but not the other, as witnessed by the following substitution.

$$a : A, \boldsymbol{x} : \mathbf{I} \gg (\boldsymbol{x}/\boldsymbol{x}, a/a) \in (\boldsymbol{x} : \mathbf{I}, a : A)$$

In the domain of this substitution, $a : A$ ranges over fewer terms: only those elements of $A$ that are apart from $\boldsymbol{x}$.

In keeping with the lack of contraction, we allow constraints only to identify bridge variables with constants, not with other variables.

$$\frac{\begin{array}{c} \text{I-CONSTRAINT} \\ \Gamma \gg \boldsymbol{r} \in \mathbf{I} \quad \varepsilon \in \{0, 1\} \\ \hline \Gamma \gg \boldsymbol{r} = \varepsilon \text{ constraint} \end{array}}{}$$

We note that affine variables are also central to nominal sets [Pit13], where they are used to represent variable names in syntax. The BCH model of univalent type theory in

5:18

E. CAVALLO AND R. HARPER

Vol. 17:4

BRIDGE-FORM

\[
\frac {\Gamma , \boldsymbol {x} : \mathbf {I} \gg A \text {type} \quad \Gamma \gg M _ {0} \in A [ \mathbf {0} / \boldsymbol {x} ] \quad \Gamma \gg M _ {1} \in A [ \mathbf {1} / \boldsymbol {x} ]}{\Gamma \gg \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1}) \text {type}}
\]

BRIDGE-INTRO

\[
\frac {\Gamma , \boldsymbol {x} : \mathbf {I} \gg M \in A}{\Gamma \gg \lambda^ {\mathbf {I}} \boldsymbol {x} . M \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M [ \mathbf {0} / \boldsymbol {x} ] , M [ \mathbf {1} / \boldsymbol {x} ])}
\]

BRIDGE-ELIM

\[
\frac {\Gamma \gg \boldsymbol {r} \in \mathbf {I} \quad \Gamma \backslash \boldsymbol {r} \gg P \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})}{\Gamma \gg P @ \boldsymbol {r} \in A [ \boldsymbol {r} / \boldsymbol {x} ]}
\]

BRIDGE-β

\[
\frac {\Gamma \gg \boldsymbol {r} \in \mathbf {I} \quad \Gamma \backslash \boldsymbol {r} , \boldsymbol {x} : \mathbf {I} \gg M \in A}{\Gamma \gg (\lambda^ {\mathbf {I}} \boldsymbol {x} . M) @ \boldsymbol {r} = M [ \boldsymbol {r} / \boldsymbol {x} ] \in A [ \boldsymbol {r} / \boldsymbol {x} ]}
\]

BRIDGE- \( \partial \)

\[
\frac {\Gamma \gg P \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1}) \quad \varepsilon \in \{0 , 1 \}}{\Gamma \gg P @ \varepsilon = M _ {\varepsilon} \in A [ \varepsilon / \boldsymbol {x} ]}
\]

BRIDGE-η

\[
\frac {\Gamma \gg P \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})}{\Gamma \gg P = \lambda^ {\mathbf {I}} \boldsymbol {x} . P @ \boldsymbol {x} \in \operatorname{Bridge} _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})}
\]

Figure 4: Rules for Bridge-types

EXTENT

\[
\begin{array}{l} \Gamma \gg \boldsymbol {r} \in \mathbf {I} \quad \Gamma \backslash \boldsymbol {r}, \boldsymbol {x}: \mathbf {I} \gg A \text {type} \quad \Gamma \backslash \boldsymbol {r}, \boldsymbol {x}: \mathbf {I}, a: A \gg B \text {type} \quad \Gamma \gg M \in A [ \boldsymbol {r} / \boldsymbol {x} ] \\ \Gamma \backslash \boldsymbol {r}, a _ {0}: A [ \mathbf {0} / \boldsymbol {x} ] \gg N _ {0} \in B [ \mathbf {0} / \boldsymbol {x} ] [ a _ {0} / a ] \quad \Gamma \backslash \boldsymbol {r}, a _ {1}: A [ \mathbf {1} / \boldsymbol {x} ] \gg N _ {1} \in B [ \mathbf {1} / \boldsymbol {x} ] [ a _ {1} / a ] \\ \Gamma \backslash \boldsymbol {r}, a _ {0}: A [ \mathbf {0} / \boldsymbol {x} ], a _ {1}: A [ \mathbf {1} / \boldsymbol {x} ], \overline {{a}}: \operatorname{Bridge} _ {\boldsymbol {x}. A} (a _ {0}, a _ {1}) \gg \overline {{N}} \in \operatorname{Bridge} _ {\boldsymbol {x}. B [ \overline {{a}} @ \boldsymbol {x} / a ]} (N _ {0}, N _ {1}) \\ \Gamma \gg \operatorname{extent} _ {\boldsymbol {r}} (M; a _ {0}. N _ {0}, a _ {1}. N _ {1}, a _ {0}. a _ {1}. \overline {{a}}. \overline {{N}}) \in B [ \boldsymbol {r} / \boldsymbol {x} ] [ M / a ] \\ \end{array}
\]

EXTENT- \( \partial \)

\[
\frac {\cdots \quad \varepsilon \in \{0 , 1 \} \quad \Gamma \gg M \in A [ \varepsilon / \boldsymbol {x} ]}{\Gamma \gg \operatorname{extent} _ {\varepsilon} (M ; \cdots) = N _ {\varepsilon} [ M / a _ {\varepsilon} ] \in B [ \varepsilon / \boldsymbol {x} ] [ M / a ]}
\]

EXTENT-β

\[
\frac {\cdots \quad \Gamma \backslash \boldsymbol {r} , \boldsymbol {x} : \mathbf {I} \gg M \in A}{\Gamma \gg \operatorname{extent} _ {\boldsymbol {r}} (M [ \boldsymbol {r} / \boldsymbol {x} ] ; \cdots) = \overline {{N}} [ M [ \mathbf {0} / \boldsymbol {x} ] / a _ {0} ] [ M [ \mathbf {1} / \boldsymbol {x} ] / a _ {1} ] [ \lambda^ {\mathbf {I}} \boldsymbol {x} . M / \overline {{a}} ] @ \boldsymbol {r} \in B [ \boldsymbol {r} / \boldsymbol {x} ] [ M / a ]}
\]

Figure 5: Rules for the extent operator. The elided premises in the second and third rules match those of the first rule.

cubical sets [BCH13, BCH19] is also based on an affine interval (and has been presented in a nominal style by Pitts [Pit14]). We say more about the BCH model in Section 2.5.

2.2. Bridge-types. We define Bridge-types exactly as we define Path-types: elements of  \( \text{Bridge}_{x.A}(M_0, M_1) \)  are elements of A in an abstracted bridge variable x that agree with  \( M_0 \)  and  \( M_1 \)  on their endpoints. We give rules for Bridge-types in Figure 4. The only difference is that a bridge can only be applied to a fresh variable, in keeping with the judgmental structure:  \( P@r \)  makes sense when r is apart from P.

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:19

2.3. The extent operator. As we have mentioned, the first reason for using affine variables is connected to function extensionality. If we follow the standard relational model of type theory—more generally, the standard definition of a logical relation at function type—we expect the following isomorphism, a bridge equivalent of Lemmas 1.1 and 1.2.

$$\mathsf{Bridge}_{\boldsymbol{x},(a:A)\to B}(F_0,F_1)$$

$$\simeq$$

$$(a_0:A[\mathbf{0}/\boldsymbol{x}])(a_1:A[\mathbf{1}/\boldsymbol{x}])(p:\mathsf{Bridge}_{\boldsymbol{x},A}(a_0,a_1))\to\mathsf{Bridge}_{\boldsymbol{x},B[p\otimes\boldsymbol{x}/a]}(F_0a_0,F_1a_1)$$

To go from bottom to top, we can repeat the proof of Lemma 1.1 without issue. On the other hand, the proof of Lemma 1.2 relies on the presence of coe, which has no equivalent in parametric type theory. Instead, we will introduce a new operator to validate this principle, extent, which relies on the substructurality of the bridge interval.

Rules for extent are displayed in Figure 5. The operator is essentially a fully applied version of the principle we are looking for.

Lemma 2.1. Let $x:\mathbb{I}\gg A$ type, $x:\mathbb{I},a:A\gg B$ type, $F_0\in((a:A)\to B)[\mathbf{0}/\boldsymbol{x}]$, and $F_1\in((a:A)\to B)[\mathbf{1}/\boldsymbol{x}]$ be given. Then we have the following.

$$\frac{H\in(a_0:A[\mathbf{0}/\boldsymbol{x}])(a_1:A[\mathbf{1}/\boldsymbol{x}])(p:\mathsf{Bridge}_{\boldsymbol{x},A}(a_0,a_1))\to\mathsf{Bridge}_{\boldsymbol{x},B[p\otimes\boldsymbol{x}/a]}(F_0a_0,F_1a_1)}{\mathsf{bridge-funext}(H)\in\mathsf{Bridge}_{\boldsymbol{x},(a:A)\to B}(F_0,F_1)}$$

Proof. $\mathsf{bridge-funext}(H):=\lambda^{\mathbf{I}}\boldsymbol{x}.\lambda a.\mathsf{extent}_{\boldsymbol{x}}(a;a_0.F_0a_0,a_1.F_1a_1,a_0.a_1.\overline{a}.Ha_0a_1\overline{a})$.

As shown in the rule EXTENT-$\beta$, $\mathsf{extent}_{\boldsymbol{r}}$ evaluates by capturing the occurrences of $\boldsymbol{r}$ in its principal argument $M$. That is, $\mathsf{extent}_{\boldsymbol{x}}(M;a_0.F_0a_0,a_1.F_1a_1,a_0.a_1.\overline{a}.Ha_0a_1\overline{a})$ evaluates by passing $M[\mathbf{0}/\boldsymbol{x}]$, $M[\mathbf{1}/\boldsymbol{x}]$, and $\lambda^{\mathbf{I}}\boldsymbol{x}.M$ to $H$. That this is possible depends on affinity because $\lambda^{\mathbf{I}}\boldsymbol{x}.-$ does not necessarily commute with diagonal substitutions. Specifically, if we have some term $M(\boldsymbol{x},\boldsymbol{y})$ that depends on two variables, we can get different results by abstracting before or after substitution as follows.

$$\begin{array}{ccc} M(\boldsymbol{x},\boldsymbol{y}) & \xrightleftharpoons{[\boldsymbol{y}/\boldsymbol{x}]} & M(\boldsymbol{y},\boldsymbol{y}) \\ \lambda^{\mathbf{I}}\boldsymbol{x}.- & & \Downarrow \lambda^{\mathbf{I}}\boldsymbol{x}.- \\ \lambda^{\mathbf{I}}\boldsymbol{x}.M(\boldsymbol{x},\boldsymbol{y}) & \xrightleftharpoons{[\boldsymbol{y}/\boldsymbol{x}]} & \lambda^{\mathbf{I}}\boldsymbol{x}.M(\boldsymbol{x},\boldsymbol{y}) \neq \lambda^{\mathbf{I}}\boldsymbol{x}.M(\boldsymbol{y},\boldsymbol{y}) \end{array}$$

We call the operator extent because $\mathsf{extent}_{\boldsymbol{r}}(M;\cdots)$ reveals the extent of the term $M$ in the direction $\boldsymbol{r}$: either $\boldsymbol{r}$ is a constant, in which case $M$ is simply a point, or $\boldsymbol{r}$ is a variable $\boldsymbol{x}$, in which case $M$ is a point on a line $\lambda^{\mathbf{I}}\boldsymbol{x}.M$ in that direction.

The conditions under which EXTENT-$\beta$ applies are somewhat subtle. In short, the requirement is that $M$ not depend on any term variables that are not apart from $\boldsymbol{x}$. For example, $\mathsf{extent}_{\boldsymbol{x}}(a;\cdots)$ can be reduced only when $a$ appears prior to $\boldsymbol{x}$ in the context. Once again, this relates to the commutativity of substitutions and capture, in this case the difference between $(\lambda^{\mathbf{I}}\boldsymbol{x}.a)[Q(\boldsymbol{x})/a]$ and $\lambda^{\mathbf{I}}\boldsymbol{x}.(a[Q(\boldsymbol{x})/a])$. Note, however, that an extent term containing no term variables always reduces, so this issue is invisible to the closed operational semantics; it is merely a matter of the degree to which we can extend the closed reduction rule to an equality for open terms.

We can show that bridge-funext is in fact an isomorphism, with inverse given by the bridge equivalent of Lemma 1.1. One inverse condition is EXTENT-$\beta$, while the other is an

5:20

E. CAVALLO AND R. HARPER

Vol. 17:4

“$\eta$-principle for extent” that can be proven up to path equality using extent itself, much as dependent elimination for inductive types gives such weak $\eta$-principles.

**Proposition 2.2.** Let $x : \mathbb{I} \gg A$ type, $x : \mathbb{I}, a : A \gg B$ type, $F_0 \in ((a:A) \to B)[\mathbf{0}/\mathbf{x}]$, and $F_1 \in ((a:A) \to B)[\mathbf{1}/\mathbf{x}]$ be given. Then we have the following.

$$\mathsf{Bridge}_{\mathbf{x},(a:A) \to B}(F_0, F_1)$$

$$\simeq$$

$$(a_0: A[\mathbf{0}/\mathbf{x}]) (a_1: A[\mathbf{1}/\mathbf{x}]) (p: \mathsf{Bridge}_{\mathbf{x},A}(a_0, a_1)) \to \mathsf{Bridge}_{\mathbf{x},B[p \otimes \mathbf{x}/a]}(F_0 a_0, F_1 a_1)$$

We can also show that the function extensionality principle induces a corresponding principle for bridges in isomorphism types. We leave the proof to the reader; one can prove it using extent directly, but it also follows formally from Proposition 2.2 and the correspondence between bridges over path types and paths over bridge types.

**Proposition 2.3.** Let $x : \mathbb{I} \gg A, B$ type, $I_0 \in (A \simeq B)[\mathbf{0}/\mathbf{x}]$, and $I_1 \in (A \simeq B)[\mathbf{1}/\mathbf{x}]$ be given. Then we have the following.

$$\frac{H \in (a_0: A[\mathbf{0}/\mathbf{x}]) (a_1: A[\mathbf{1}/\mathbf{x}]) \to \mathsf{Bridge}_{\mathbf{x},A}(a_0, a_1) \simeq \mathsf{Bridge}_{\mathbf{x},B}(\mathsf{fst}(I_0)(a_0), \mathsf{fst}(I_1)(a_1))}{\mathsf{bridge-isoext}(H) \in \mathsf{Bridge}_{\mathbf{x},A \simeq B}(I_0, I_1)}$$

**2.4. Gel-types and relativity.** Finally, we come to the equivalent of univalence in parametric type theory, which we call *relativity*: the correspondence between bridges of types and relations. One direction of the correspondence is given by **Bridge**-types: given a bridge of types $\mathbf{x} : \mathbf{I} \gg A$ type, we have a relation $\mathsf{Bridge}_{\mathbf{x},A}(-,-)$ on $A[\mathbf{0}/\mathbf{x}]$ and $A[\mathbf{1}/\mathbf{x}]$ (which we henceforth simply write as $\mathsf{Bridge}_{\mathbf{x},A}$). As with V-types for univalence, the inverse will be effected by introducing a new type constructor, which we call the **Gel-type**. These resemble the G-types of the BCH model, but apply to relations rather than isomorphisms, hence the name.

We provide rules for **Gel**-types in Figure 6. Unlike the V-type, the **Gel**-type directly converts relations to bridges of types: for any relation $a_0 : A_0, a_1 : A_1 \gg R \in \mathcal{U}$, we have $\lambda^{\mathbf{I}}\mathbf{x}.\mathsf{Gel}_{\mathbf{x}}(A_0, A_1, a_0.a_1.R) \in \mathsf{Bridge}_{\mathcal{U}}(A_0, A_1)$. The introduction rule turns a witness for the relation $\Gamma \gg P \in R[M_0, M_1/a_0, a_1]$ into a bridge $\lambda^{\mathbf{I}}\mathbf{x}.\mathsf{gel}_{\mathbf{x}}(M_0, M_1, P) \in \mathsf{Bridge}_{\mathbf{x},\mathsf{Gel}_{\mathbf{x}}(A_0, A_1, a_0.a_1.R)}(M_0, M_1)$ over the corresponding **Gel**-type, while the elimination rule conversely turns such a bridge into a witness. When we have a relation in the form $R \in A_0 \times A_1 \to \mathcal{U}$, we will abbreviate $\mathsf{Gel}_{\mathbf{r}}(A_0, A_1, a_0.a_1.R\langle a_0, a_1 \rangle)$ as $\mathsf{Gel}_{\mathbf{r}}(A_0, A_1, R)$.

The problem of shifting dimensions in V-types, described in Section 1.4, is no longer an issue when we have affine interval variables; we can express degeneracy in $\mathbf{r}$ using the context restriction $-\backslash \mathbf{r}$. This is fortunate, as the trick for deriving univalence from V-types would not apply here. For univalence, we rely on the fact that the constant path $\lambda^{\mathbb{I}}_\bullet B$ corresponds to the identity isomorphism on $B$; thus we can transform isomorphisms $A \simeq B$ into paths by composing with $\lambda^{\mathbb{I}}_\bullet B$ in a V-type. On the other hand, the constant bridge $\lambda^{\mathbf{I}}_\bullet A$ does *not* necessarily correspond to the identity relation (i.e., the path relation $\mathsf{Path}_B$); rather, it corresponds to the bridge relation $\mathsf{Bridge}_B$. In particular, $\lambda^{\mathbf{I}}_\bullet \mathcal{U}$ will correspond to $\lambda\langle A, B\rangle.(A \times B \to \mathcal{U})$, not $\lambda\langle A, B\rangle.(A \simeq B)$. Thus, a V-like type would only give us bridges for those relations that factor through the bridge relation on one endpoint—more generally, through some bridge $\mathbf{x}, B$ we already have in hand.

We only mean in the above to give some intuition for the difference between the affine and structural situation, not for example to prove beyond a shadow of a doubt that no

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:21

\[
\begin{array}{c} \text {GEL - FORM} \\ \Gamma \gg \boldsymbol {r} \in \mathbf {I} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {0} \text {type} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {1} \text {type} \qquad \Gamma \backslash \boldsymbol {r}, a _ {0}: A _ {0}, a _ {1}: A _ {1} \gg R \text {type} \\ \hline \Gamma \gg \operatorname{Gel} _ {\boldsymbol {r}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \text {type} \end{array}
\]

\[
\begin{array}{c} \text {GEL - INTRO} \\ \Gamma \backslash \boldsymbol {r} \gg M _ {0} \in A _ {0} \qquad \Gamma \backslash \boldsymbol {r} \gg M _ {1} \in A _ {1} \qquad \Gamma \backslash \boldsymbol {r} \gg P \in R [ M _ {0}, M _ {1} / a _ {0}, a _ {1} ] \\ \hline \Gamma \gg \operatorname{gel} _ {\boldsymbol {r}} (M _ {0}, M _ {1}, P) \in \operatorname{Gel} _ {\boldsymbol {r}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \end{array}
\]

\[
\begin{array}{c c} \text {GEL - FORM - \partial} \\ \varepsilon \in \{0, 1 \} \qquad \Gamma \gg A _ {\varepsilon} \text {type} \\ \hline \Gamma \gg \text {Gel} _ {\varepsilon} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) = A _ {\varepsilon} \text {type} \end{array} \qquad \begin{array}{c c} \text {GEL - INTRO - \partial} \\ \varepsilon \in \{0, 1 \} \qquad \Gamma \gg M _ {\varepsilon} \in A _ {\varepsilon} \\ \hline \Gamma \gg \text {gel} _ {\varepsilon} (M _ {0}, M _ {1}, P) = M _ {\varepsilon} \in A _ {\varepsilon} \end{array}
\]

\[
\begin{array}{c} \text {GEL - ELIM} \\ \Gamma , \boldsymbol {x}: \mathbf {I} \gg Q \in \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, R) \\ \hline \Gamma \gg \operatorname{ungel} (\boldsymbol {x}. Q) \in R [ Q [ \mathbf {0} / \boldsymbol {x} ], Q [ \mathbf {1} / \boldsymbol {x} ] / a _ {0}, a _ {1} ] \end{array}
\]

\[
\begin{array}{c} \text {GEL- } \beta \\ \Gamma \gg P \in R [ M _ {0}, M _ {1} / a _ {0}, a _ {1} ] \\ \hline \Gamma \gg \operatorname{ungel} (\boldsymbol {x}. \operatorname{gel} _ {\boldsymbol {x}} (M _ {0}, M _ {1}, P)) = P \in R [ M _ {0}, M _ {1} / a _ {0}, a _ {1} ] \end{array}
\]

\[
\begin{array}{c} \text {GEL - } \eta \\ \Gamma \gg \boldsymbol {r} \in \mathbf {I} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {0} \text {type} \qquad \Gamma \backslash \boldsymbol {r} \gg A _ {1} \text {type} \\ \Gamma \backslash \boldsymbol {r}, a _ {0}: A _ {0}, a _ {1}: A _ {1} \gg R \text {type} \qquad \Gamma \backslash \boldsymbol {r}, \boldsymbol {x}: \mathbf {I} \gg Q \in \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \\ \hline \Gamma \gg Q [ \boldsymbol {r} / \boldsymbol {x} ] = \operatorname{gel} _ {\boldsymbol {r}} (Q [ \mathbf {0} / \boldsymbol {x} ], Q [ \mathbf {1} / \boldsymbol {x} ], \operatorname{ungel} (\boldsymbol {x}. Q)) \in \operatorname{Gel} _ {\boldsymbol {r}} (A _ {0}, A _ {1}, a _ {0}. a _ {1}. R) \end{array}
\]

Figure 6: Rules for Gel-types.

Gel-like type can exist structurally. However, we note that in the bisimplicial set semantics of Riehl and Shulman's directed type theory [RS17], a similar setting, an issue of dimension shift does indeed prevent the existence of a universe where arrows correspond to relations [Rie18].

We now proceed to prove the relativity principle.

Theorem 2.4. For any \(A_0, A_1 \in \mathcal{U}\), \(\lambda C.\text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}} \in \text{Bridge}_{\mathcal{U}}(A_0, A_1) \to (A_0 \times A_1 \to \mathcal{U})\) is an isomorphism.

Proof. As candidate inverse, we of course take \(\lambda R.\lambda^{\mathbf{I}}\pmb{x}.\mathsf{Gel}_{\pmb{x}}(A_{0},A_{1},R)\).

First we show that this is a left inverse, i.e., that the following holds.

\[
(R: A _ {0} \times A _ {1} \rightarrow \mathcal {U}) \rightarrow \operatorname{Path} _ {A _ {0} \times A _ {1} \rightarrow \mathcal {U}} (\operatorname{Bridge} _ {\boldsymbol {x}. \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, R)}, R)
\]

Let \( R: A_0 \times A_1 \to \mathcal{U} \) be given. We need to construct a path in \( A_0 \times A_1 \to \mathcal{U} \), so we apply function extensionality and univalence. Then for every \( a_0: A_0 \) and \( a_1: A \), we need an isomorphism \( \text{Bridge}_{\boldsymbol{x}, \text{Gel}_x(A_0, A_1, R)}(a_0, a_1) \simeq R \langle a_0, a_1 \rangle \). This isomorphism is implemented exactly by the introduction and elimination forms of the Gel-type, and the inverse conditions hold (up to exact equality) by GEL-\( \beta \) and GEL-\( \eta \).

Now we show it is also a right inverse.

\[
(C: \operatorname{Bridge} _ {\mathcal {U}} (A _ {0}, A _ {1})) \rightarrow \operatorname{Path} _ {\operatorname{Bridge} _ {\mathcal {U}} (A _ {0}, A _ {1})} (\lambda^ {\mathbf {I}} \boldsymbol {x}. \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0}, A _ {1}, \operatorname{Bridge} _ {\boldsymbol {x}. C @ \boldsymbol {x}}), C)
\]

5:22

E. CAVALLO AND R. HARPER

Vol. 17:4

Let $C : \text{Bridge}_{\mathcal{U}}(A_0, A_1)$ be given. We are asked to provide a square with the following boundary.

![img-2.jpeg](img-2.jpeg)

By “flipping” this square—i.e., using the correspondence between bridges of paths and paths of bridges given by exchange of variables—it suffices to show the following.

$$\text{Bridge}_{\boldsymbol{x}, \text{Path}_{\mathcal{U}}(\text{Gel}_{\boldsymbol{x}}(A_0, A_1, \text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}}), C@\boldsymbol{x})}(\lambda^{\mathbb{I}} \_\!\!\!_- A_0, \lambda^{\mathbb{I}} \_\!\!\!_- A_1)$$

Now we apply univalence, converting the path type in the universe to a type of isomorphisms. Here we use the fact that the constant paths $\lambda^{\mathbb{I}} \_\!\!\!_- A_\varepsilon$ correspond to identity isomorphisms $\text{idiso}(A_\varepsilon)$ across univalence. This reduces our goal to the following.

$$\text{Bridge}_{\boldsymbol{x}, \text{Gel}_{\boldsymbol{x}}(A_0, A_1, \text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}}) \simeq C@\boldsymbol{x}}(\text{idiso}(A_0), \text{idiso}(A_1))$$

Finally we apply Proposition 2.3, reducing the goal once more.

$$(a_0: A_0)(a_1: A_1) \to \text{Bridge}_{\text{Gel}_{\boldsymbol{x}}(A_0, A_1, \text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}})}(a_0, a_1) \simeq \text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}}(a_0, a_1)$$

This is a consequence of the left inverse condition we have already proven.

Note that the proof of relativity relies on univalence; not surprising, since it is an isomorphism between types that involve the universe. (It also relies directly on function extensionality, both for paths and bridges.) In [BCM15], which does not include univalence, relativity is instead ensured by imposing stronger equations on Gel-types—precisely the equations $\text{Bridge}_{\boldsymbol{x}, \text{Gel}_{\boldsymbol{x}}(A_0, A_1, R)} = R$ and $C = \lambda^{\mathbb{I}} \boldsymbol{x} \cdot \text{Gel}_{\boldsymbol{x}}(A_0, A_1, \text{Bridge}_{\boldsymbol{x}, C@\boldsymbol{x}})$ required for the proof. (These equations are there named PAIR-PRED and SURJ-TYP.) These equations make it more difficult to construct a presheaf model, as we discuss further in Section 6.

2.5. Using affine variables for paths. Before we dive into using parametric cubical type theory, let us take one more moment to reflect on structural and substructural interval variables. We have seen why affinity is important for parametric type theory, but is structurality important for cubical type theory? The Bezem-Coquand-Huber model gives a partial negative answer: there is a model of univalent type theory in presheaves on the affine cube category [BCH13, BCH19]. While no one has attempted to design a type theory based on this model, it is plausible that it could be done.

Unfortunately, affine interval variables create problems for modeling higher inductive types. Consider, for example, the following extremely simple type, which has a single path constructor with no fixed boundary.

data line where

$$| \text{in}(x : \mathbb{I}) \in \text{line}$$

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:23

This specification generates the following elimination principle and computation rule, which essentially says that maps out of line correspond to terms in a context extended with an interval variable.

$$\frac{\Gamma, a : \text{line} \gg C \text{ type} \quad \Gamma \gg M \in \text{line} \quad \Gamma, x : \mathbb{I} \gg Q_{\text{in}} \in C[\text{in}(x)/a]}{\Gamma \gg \text{interval-elim}_{a.C}(M, x.Q_{\text{in}}) \in C[M/a]}$$

$$\frac{\Gamma, a : \text{line} \gg C \text{ type} \quad \Gamma \gg r \in \mathbb{I} \quad \Gamma, x : \mathbb{I} \gg Q_{\text{in}} \in C[\text{in}(x)/a]}{\Gamma \gg \text{interval-elim}_{a.C}(\text{in}(r), x.Q_{\text{in}}) = Q_{\text{in}}[r/x] \in C[\text{in}(r)/a]}$$

The issue is in the computation rule, which applies the interval substitution $-[r/x]$ to $Q_{\text{in}}$. If our interval is affine, then this substitution will be nonsensical if $Q_{\text{in}}$ already mentions $r$. Moreover, it is not clear how to restrict the premises of interval-elim to ensure the substitution is sensible without ending up with an insufficiently powerful principle. On a more conceptual level, the line type is suspicious in an affine system in that structural maps out of line correspond to affine maps out of the interval.

The problem of higher inductive types is one reason why research in cubical type theory and models has shifted from substructural to structural interval variables. There is also the fact that structural variables are simply easier to work with. Still, the BCH model does have some intriguing advantages; for one, univalence can be implemented in Gel-like rather V-like fashion, and the former admits simpler implementations of coercion and composition.

### 3. APPLYING INTERNAL PARAMETRICITY

Now that we have laid out what we need of parametric cubical type theory, we can get started proving theorems. We will begin with a classic application of parametricity: relating inductive types to their Church encodings, in this case booleans.

3.1. Booleans. The Church booleans are the polymorphic binary operators, the elements of the type $\mathbb{B} := (A:\mathcal{U}) \to A \to A \to A$. Clearly this type has at least two elements, $\lambda A.\lambda t.\lambda_{\dots}t$ and $\lambda A.\lambda_{\dots}\lambda f.f$. It is a classical consequence of parametricity that these are the only two elements of $\mathbb{B}$. Using internal parametricity, we can prove that $\mathbb{B}$ is indeed isomorphic to the standard type of booleans (bool).

Theorem 3.1. bool $\simeq \mathbb{B}$.

Proof. It is easy to define functions $F \in \text{bool} \to \mathbb{B}$ and $G \in \mathbb{B} \to \text{bool}$ in either direction.

$$F := \lambda b.\lambda A.\lambda t.\lambda f.\text{if}_{\_A}(b; t, f) \quad G := \lambda k.k(\text{bool})(\text{tt})(\text{ff})$$

Moreover, it is easy to check by case-analysis that $G(Fb)$ is path-equal to $b$ for any $b : \text{bool}$.

We use parametricity to prove the other inverse condition. Let some $k : \mathbb{B}$ along with $A : \mathcal{U}, t : A, f : A$ be given. We intend to show that $F(Gk)Atf$ is path-equal to $kAtf$. We define a relation $R \in \text{bool} \times A \to \mathcal{U}$ as follows.

$$R\langle b, a \rangle := \text{Path}_A(FbAtf, a)$$

That is, $R$ is the graph of $\lambda b.FbAtf$. Abstracting a bridge interval variable $\boldsymbol{x}$, we can apply $k$ at the Gel-type corresponding to $R$.

$$k(\text{Gel}_\boldsymbol{x}(\text{bool}, A, R)) \in \text{Gel}_\boldsymbol{x}(\text{bool}, A, R) \to \text{Gel}_\boldsymbol{x}(\text{bool}, A, R) \to \text{Gel}_\boldsymbol{x}(\text{bool}, A, R)$$

5:24

E. CAVALLO AND R. HARPER

Vol. 17:4

We see that tt and t are related by R: we have λ$^{\sharp}$...t ∈ R⟨tt, t⟩. Likewise, we have λ$^{\sharp}$...f ∈ R⟨ff, f⟩. We apply k at the two gel terms corresponding to these witnesses of the relation.

$$k(\text{Gel}_x(\text{bool}, A, R))(\text{gel}_x(\text{tt}, t, \lambda^{\sharp}...t))(\text{gel}_x(\text{ff}, f, \lambda^{\sharp}...f)) \in \text{Gel}_x(\text{bool}, A, R)$$

If we substitute 0 for x, each Gel and gel term reduces to its first term argument, leaving k(bool)(tt)(ff), which is Gk. Likewise, if we substitute 1, we get kAtf. When we bind x and project the relation witness from this term, we therefore wind up with the following.

$$\text{ungel}(x.k(\text{Gel}_x(\text{bool}, A, R))(\text{gel}_x(\text{tt}, t, \lambda^{\sharp}...t))(\text{gel}_x(\text{ff}, f, \lambda^{\sharp}...f))) \in R\langle Gk, kAtf \rangle$$

By definition of R, this is exactly our goal: a path from F(Gk)Atf to kAtf. By function extensionality, we get a term in Path$_{\mathbb{B}}$(F(Gk), k).

This argument follows the shape of a classical parametricity proof: we define a relation, apply a function to related arguments (here represented by gel terms), and conclude that the outputs are also related (via ungel). We can apply similar arguments to characterize other Church encodings. For example, we can show that the type (A:U) → A → (A → A) → A is isomorphic to the natural numbers; in that case, we would also use extent to construct a bridge in the function type.

Note that because the system is predicative, it does not appear possible to simply define inductive types using Church encodings. In the absence of a primitive boolean type in U, B can only eliminate into small types (that is, types in the universe U). When there is a primitive boolean type, however, B inherits its properties: we can define functions from B into large type by induction by factoring through the map B → bool.

The picture gets more complex when we consider Church encodings that are parameterized over “external” types, such as the following encoding of the coproduct.

$$A + B \stackrel{?}{\simeq} (C:\mathcal{U}) \to (A \to C) \to (B \to C) \to C$$

A classical proof would rely on the identity extension lemma [Rey83], which implies in particular that the relational interpretation of a closed type (A or B here) is the identity relation. This is not the case in BCM-style internal parametricity. In particular, the principle fails for the universe: the types Bridge$_{\mathcal{U}}$(A, B) and Path$_{\mathcal{U}}$(A, B) are not the same, as one is isomorphic to A × B → U and the other is isomorphic to A ≃ B.

If we focus our attention on small types, we will see that any concrete type A we can think of will satisfy Bridge$_{A}$(a, b) ≃ Path$_{A}$(a, b) for all a, b : A; however, there is no way to prove for an arbitrary A. We say that types that do satisfy this principle are bridge-discrete. We can show that the universe of bridge-discreteness types is well-behaved and closed under most type formers.

3.2. Bridge-discrete types. In any type, we have a canonical map from paths to bridges induced by coercion. A type is bridge-discrete when this map is an isomorphism.

Definition 3.2. For A type and M, N ∈ A, define loosen$_{A}$ ∈ Path$_{A}$(M, N) → Bridge$_{A}$(M, N) by loosen$_{A}$ := λp.coe$^{0→1}_{x.Bridge$_{A}$(p@0,p@x)}$(λ$^{\sharp}$...p@0).

Remark 3.3. For any M ∈ A, loosen$_{A}$ takes the reflexive path on M to the reflexive bridge on A: we have λ$^{\sharp}$y.coe$^{y→1}_{x.Bridge$_{A}$(M,M)}$(λ$^{\sharp}$...M) ∈ Path$_{\text{Bridge}_A(M,M)}$(loosen$_{A}$(λ$^{\sharp}$...M), λ$^{\sharp}$...M).

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:25

**Definition 3.4.** Given $A$ type, define isBDisc($A$) type as follows.

$$\text{isBDisc}(A) := (a:A)(b:A) \to \text{islso}(\text{Path}_A(a,b), \text{Bridge}_A(a,b), \text{loosen}_A)$$

As we mentioned in Section 2.4, the type islso is always a proposition [Uni13, Theorem 4.3.2]; any two proofs of islso are connected by a path. A function type with propositional codomain is again a proposition [Uni13, Example 2.6.2], so isBDisc($A$) is a proposition. We define the universe of bridge-discrete types as $\mathcal{U}_{\text{BDisc}} := (A : \mathcal{U}) \times \text{isBDisc}(A)$.

Before continuing, we recall some standard results from univalent type theory. The proofs we reference are conducted using Martin-Löf identity types, but can be readily adapted to cubical path types by way of Lemma 1.3.

**Proposition 3.5.** Let $A$ type and let $a : A, b : A \gg R$ type be a relation on $A$. Suppose we have a family of maps with right inverses:

$$\begin{array}{l} \triangleright F \in (a:A)(b:A) \to R\langle a,b \rangle \to \text{Path}_A(a,b), \\ \triangleright G \in (a:A)(b:A) \to \text{Rinv}(R\langle a,b \rangle, \text{Path}_A(a,b), Fab). \end{array}$$

The Fab is an isomorphism for all $a, b : A$.

Proof. [Rij18, Corollary 1.2.6].

**Proposition 3.6.** Let $A$ type, $a : A \gg B_0, B_1$ type, and $F \in (a:A) \to B_0 \to B_1$ be given. Then $\lambda\langle a,b \rangle.\langle a,Fab \rangle \in ((a:A) \times B_0) \to (a:A) \times B_1$ is an isomorphism if and only if $Fa$ is an isomorphism for all $a : A$.

Proof. [Uni13, Theorem 4.7.7].

**Definition 3.7.** A type is contractible if it is a proposition and inhabited.

**Proposition 3.8.** Any function between contractible types is an isomorphism.

Proof. This is an elementary consequence of the definition.

**Proposition 3.9.** For any $A$ type and $M \in A$, the type $(a : A) \times \text{Path}_A(M,a)$ is contractible.

Proof. [Uni13, Lemma 3.11.8].

Taken together, these results give us a convenient method for showing that a type is bridge-discrete without reference to $\text{loosen}_A$.

**Lemma 3.10.** Suppose we have a family of maps with right inverses:

$$\begin{array}{l} \triangleright F \in (a:A)(b:A) \to \text{Bridge}_A(a,b) \to \text{Path}_A(a,b), \\ \triangleright G \in (a:A)(b:A) \to \text{Rinv}(\text{Bridge}_A(a,b), \text{Path}_A(a,b), Fab). \end{array}$$

Then $A$ is bridge-discrete. In particular, if $\text{Bridge}_A(a,b)$ and $\text{Path}_A(a,b)$ are isomorphic for all $a, b : A$, then $A$ is bridge-discrete.

Proof. By Proposition 3.5, Fab is an isomorphism for all $a, b : A$. By Proposition 3.6, we conclude that $(b : A) \times \text{Bridge}_A(a,b)$ and $(b : A) \times \text{Path}_A(a,b)$ are isomorphic for all $a : A$. The latter is contractible by Proposition 3.9, so the former is contractible as well. Thus $\lambda\langle b,p \rangle.\langle b,\text{loosen}_A(p) \rangle \in ((b:A) \times \text{Path}_A(a,b)) \to (b:A) \times \text{Bridge}_A(a,b)$ is an isomorphism for all $b : A$, so $A$ is bridge-discrete by Proposition 3.6.

**Lemma 3.11.** Let $A$ type and $a : A \gg B$ type be given. If $B$ is bridge-discrete for all $a : A$, then we have the following isomorphism for all $a_0, a_1 : A$, $t : B[a_0/a]$, $t' : B[a_1/a]$, and $p : \text{Path}_A(a_0, a_1)$.

$$\text{Path}_{x.B[p@x/a]}(t,t') \simeq \text{Bridge}_{x.B[\text{loosen}_A(p)@x/a]}(t,t')$$

5:26

E. CAVALLO AND R. HARPER

Vol. 17:4

Proof. By Lemma 1.3, it suffices to prove the theorem when $a_1$ is $a_0$ and $p$ is $\lambda^\mathbb{I} \dots a_0$. In that case it follows from Remark 3.3 and the assumption that $B$ is bridge-discrete. $\square$

**Theorem 3.12.** Given $A$ type and $a : A \gg B$ type, if $A$ is bridge-discrete and $B$ is bridge-discrete for all $a : A$, then $(a : A) \times B$ is bridge-discrete.

Proof. Given $t, t' : (a : A) \times B$, we can characterize paths between $t$ and $t'$ as pairs of paths between their components.

$$\mathsf{Path}_{(a:A) \times B}(t, t') \simeq (p : \mathsf{Path}_A(\mathsf{fst}(t), \mathsf{fst}(t'))) \times \mathsf{Path}_{x.B[p@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t'))$$

In the forward direction we have $\lambda p. \langle \lambda^\mathbb{I} x.\mathsf{fst}(p@x), \lambda^\mathbb{I} x.\mathsf{snd}(p@x) \rangle$, and in the reverse we have $\lambda \langle q_0, q_1 \rangle. \lambda^\mathbb{I} x. \langle q_0@x, q_1@x \rangle$; these are clearly inverses. We can repeat the proof to obtain an analogous characterization of bridges in $(a : A) \times B$.

$$\mathsf{Bridge}_{(a:A) \times B}(t, t') \simeq (p : \mathsf{Bridge}_A(\mathsf{fst}(t), \mathsf{fst}(t'))) \times \mathsf{Bridge}_{x.B[p@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t'))$$

By assumption, we know that $\mathsf{Path}_A(\mathsf{fst}(t), \mathsf{fst}(t'))$ and $\mathsf{Bridge}_A(\mathsf{fst}(t), \mathsf{fst}(t'))$ are isomorphic via $\mathsf{loosen}_A$. To show that the product types are isomorphic, it then suffices to show the second component types are isomorphic over $\mathsf{loosen}_A$, i.e., that the following holds for all $p : \mathsf{Path}_A(\mathsf{fst}(t), \mathsf{fst}(t'))$.

$$\mathsf{Path}_{x.B[p@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t')) \simeq \mathsf{Bridge}_{x.B[\mathsf{loosen}_A(p)@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t'))$$

This is immediate by Lemma 3.11. $\square$

**Theorem 3.13.** Given $A$ type and $a : A \gg B$ type, if $A$ is bridge-discrete and $B$ is bridge-discrete for all $a : A$, then $(a:A) \to B$ is bridge-discrete.

Proof. Analogous to Theorem 3.12, using Lemmas 1.2 and 2.1. $\square$

**Theorem 3.14.** If $A$ type is bridge-discrete, then $\mathsf{Path}_A(a, b)$ is bridge-discrete for all $a, b : A$.

Proof. Given $p, q : \mathsf{Path}_A(a, b)$, We have the following chain of isomorphisms.

$$\begin{array}{l} \mathsf{Path}_{\mathsf{Path}_A(a,b)}(p, q) \simeq \mathsf{Path}_{x.\mathsf{Path}_A(p@x, q@x)}(\lambda^\mathbb{I} \dots a, \lambda^\mathbb{I} \dots b) \\ \simeq \mathsf{Path}_{x.\mathsf{Bridge}_A(p@x, q@x)}(\mathsf{loosen}_A(\lambda^\mathbb{I} \dots a), \mathsf{loosen}_A(\lambda^\mathbb{I} \dots b)) \\ \simeq \mathsf{Path}_{x.\mathsf{Bridge}_A(p@x, q@x)}(\lambda^\mathbb{I} \dots a, \lambda^\mathbb{I} \dots b) \\ \simeq \mathsf{Bridge}_{\mathsf{Path}_A(a,b)}(p, q) \end{array}$$

The first step is by reordering interval abstractions, the second by Remark 3.3, the third by assumption that $A$ is bridge-discrete, and the fourth by reordering abstractions again. $\square$

**Corollary 3.15.** If $A$ type is bridge-discrete, then $\mathsf{Bridge}_A(a, b)$ is bridge-discrete for all $a, b : A$.

**Theorem 3.16.** bool is bridge-discrete.

Proof. We must define a right inverse to $\mathsf{loosen}_{\mathsf{bool}} \in \mathsf{Path}_{\mathsf{bool}}(b, b') \to \mathsf{Bridge}_{\mathsf{bool}}(b, b')$ for every $b, b' : \mathsf{bool}$. For simplicity, we prove the case where $b = \mathsf{tt}$ and $b' = \mathsf{ff}$; the other cases follow by the same argument. In this case, we first need a function of the following type.

$$\mathsf{tighten} \in \mathsf{Bridge}_{\mathsf{bool}}(\mathsf{tt}, \mathsf{ff}) \to \mathsf{Path}_{\mathsf{bool}}(\mathsf{tt}, \mathsf{ff})$$

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:27

We make use of the type $\text{Gel}_x(\text{bool}, \text{bool}, \text{Path}_{\text{bool}})$, the bridge from bool to bool corresponding to the path relation. This type has two canonical elements given by reflexivity at tt and ff.

$$\text{tt}_x := \text{gel}_x(\text{tt}, \text{tt}, \lambda^{\mathbb{I}}...\text{tt}) \quad \text{ff}_x := \text{gel}_x(\text{ff}, \text{ff}, \lambda^{\mathbb{I}}...\text{ff})$$

Given $x : \mathbf{I}$, we define an auxiliary function $\text{tighten}_x \in \text{bool} \to \text{Gel}_x(\text{bool}, \text{bool}, \text{Path}_{\text{bool}})$ sending each $b : \text{bool}$ to the corresponding such element.

$$\text{tighten}_x := \lambda b. \text{if}_{-\text{Gel}_x(\text{bool}, \text{bool}, \text{Path}_{\text{bool}})}(b; \text{tt}_x, \text{ff}_x)$$

We then define $\text{tighten} := \lambda q. \text{ungel}(x. \text{tighten}_x(q@x))$, applying $\text{tighten}_x$ pointwise to the input bridge.

To equate $\text{loosen}_{\text{bool}}(\text{tighten}(q))$ with $q$, we need a term as follows.

$$\text{inv} \in (q: \text{Bridge}_{\text{bool}}(\text{tt}, \text{ff})) \to \text{Path}_{\text{Bridge}_{\text{bool}}(\text{tt}, \text{ff})}(\text{loosen}_{\text{bool}}(\text{tighten}(q)), q)$$

We again begin by defining an auxiliary function $\text{inv}_x$ of the following type.

$$\text{inv}_x \in (b: \text{bool}) \to \text{Path}_{\text{bool}}((\text{bridge-funext}(\text{loosen}_{\text{bool}} \circ \text{tighten})@x)(b), b)$$

We define $\text{inv}_x(b)$ by induction on $b$. When $b$ is $\text{tt}$, we have the following chain of equalities.

$$\begin{aligned} (\text{bridge-funext}(\text{loosen}_{\text{bool}} \circ \text{tighten})@x)(\text{tt}) &= \text{loosen}_{\text{bool}}(\text{ungel}(x. \text{tighten}_x(\text{tt})))@x \\ &= \text{loosen}_{\text{bool}}(\text{ungel}(x. \text{tt}_x))@x \\ &= \text{loosen}_{\text{bool}}(\lambda^{\mathbb{I}}...\text{tt})@x \end{aligned}$$

The first equation is $\text{EXTENT-}\beta$, the second is by definition of $\text{tighten}_x$, and the third is $\text{GEL-}\beta$. Finally, $\text{loosen}_{\text{bool}}(\lambda^{\mathbb{I}}...\text{tt})@x$ is path-equal to $\text{tt}$ by Remark 3.3. The $\text{ff}$ case follows by the same argument. Note that both $\text{inv}_\varepsilon(\text{tt}) \in \text{Path}_{\text{bool}}(\text{tt}, \text{tt})$ and $\text{inv}_\varepsilon(\text{ff}) \in \text{Path}_{\text{bool}}(\text{ff}, \text{ff})$ are reflexive paths for $\varepsilon \in \{0, 1\}$.

Given $q : \text{Path}_{\text{bool}}(\text{tt}, \text{ff})$, we see that the pointwise application $\text{inv}_x(q@x)@y$ fills the following square.

![img-3.jpeg](img-3.jpeg)

By $\text{EXTENT-}\beta$, the top of this square is equal to $\text{loosen}_{\text{bool}}(\text{tighten}(q))@x$. We may therefore define $\text{inv} := \lambda q. \lambda^{\mathbb{I}} y. \lambda^{\mathbf{I}} x. \text{inv}_x(q@x)@y$.

The pattern of argument we used for bool generalizes to characterize the bridge types of other inductive types, and in particular to show that inductive types preserve bridge-discreteness. (We will see something like it again in Section 3.4.) The fact that relativity is used (via Gel-types) in these proofs is an interesting parallel to the use of univalence to characterize the path types of higher inductive types (e.g., [Uni13, §8.1]).

The bridge-discrete types are even closed under Gel-types, which means that we can also carry out parametricity arguments in $\mathcal{U}_{\text{BDisc}}$. For example, we can show that the Church encoding $(A: \mathcal{U}_{\text{BDisc}}) \to \text{fst}(A) \to \text{fst}(A) \to \text{fst}(A)$ is also isomorphic to bool.

5:28

E. CAVALLO AND R. HARPER

Vol. 17:4

**Theorem 3.17.** Let $A_0, A_1$ type and $a_0: A_0, a_1: A_1 \gg R$ type be given. If $A_0$ and $A_1$ are bridge-discrete and $Ra_0a_1$ is bridge-discrete for all $a_0, a_1$, then $\mathsf{Gel}_x(A_0, A_1, a_0.a_1.R)$ is bridge-discrete for all $\boldsymbol{x}: \mathbf{I}$.

*Proof.* Abbreviate $G_{\boldsymbol{x}} := \mathsf{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$. We show $\mathsf{Path}_{G_{\boldsymbol{x}}}(g, g') \simeq \mathsf{Bridge}_{G_{\boldsymbol{x}}}(g, g')$ for all $\boldsymbol{x}: \mathbf{I}$ and $g, g' \in G_{\boldsymbol{x}}$. Note that when $\boldsymbol{x}$ is an endpoint, this holds by the assumptions that $A_0$ and $A_1$ are bridge-discrete.

We apply extent at $\boldsymbol{x}$, first with $g$ and then with $g'$. It then remains to show that for all $a_0, a_0': A_0, a_1, a_1': A_1$, $q: \mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)$, $q': \mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0', a_1')$, and $\boldsymbol{x}: \mathbf{I}$, we have $\mathsf{Path}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x}) \simeq \mathsf{Bridge}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})$ agreeing with the $\mathsf{loosen}_A$ isomorphism when $\boldsymbol{x} = \mathbf{0}$ and $\mathsf{loosen}_B$ isomorphism when $\boldsymbol{x} = \mathbf{1}$. By Proposition 2.3, it is enough to give an isomorphism

$$\mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Path}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(p_0, p_1) \simeq \mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Bridge}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(\mathsf{loosen}_{A_0}(p_0), \mathsf{loosen}_{A_1}(p_1))$$

for every $p_0: \mathsf{Path}_{A_0}(a_0, a_0')$ and $p_1: \mathsf{Path}_{A_1}(a_1, a_1')$. By identity elimination (Lemma 1.3), we may assume that $p_0$ and $p_1$ are reflexive paths, in which case (with the help of Remark 3.3) we need to show the following for all $q, q': \mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)$.

$$\mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Path}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(\lambda^{\mathbb{I}}...a_0, \lambda^{\mathbb{I}}...a_1) \simeq \mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Bridge}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(\lambda^{\mathbf{I}}...a_0, \lambda^{\mathbf{I}}...a_1)$$

Now we flip the binders on either side, leaving us to prove the following.

$$\mathsf{Path}_{\mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)}(q, q') \simeq \mathsf{Bridge}_{\mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)}(q, q')$$

In other words, we need to show that $\mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)$ is bridge-discrete; this type is isomorphic to $R$ by relativity, so we are finished by assumption.

**3.3. The law of the excluded middle.** As a corollary to the bridge-discreteness of bool, we can refute the law of the excluded middle for propositions. First, let us introduce a few variations on the excluded middle.

$$\begin{array}{l} \mathsf{LEM}_{\infty} := (A:\mathcal{U}) \to (b: \mathsf{bool}) \times \mathsf{if}_{-\mathcal{U}}(b; A, \neg A) \\ \mathsf{LEM}_{-1} := (A:\mathcal{U}) \to \mathsf{isProp}(A) \to (b: \mathsf{bool}) \times \mathsf{if}_{-\mathcal{U}}(b; A, \neg A) \\ \mathsf{WLEM} := (A:\mathcal{U}) \to (b: \mathsf{bool}) \times \mathsf{if}_{-\mathcal{U}}(b; \neg A, \neg\neg A) \end{array}$$

The *unrestricted excluded middle*, $\mathsf{LEM}_{\infty}$, is already refuted by univalence [Uni13, Corollary 4.2.7]. In short, we can obtain a contradiction by examining the action of $\mathsf{LEM}_{\infty}$ on the negation isomorphism not $\in \mathsf{bool} \simeq \mathsf{bool}$ between bool and itself. In univalent type theory, it is therefore customary to restrict the law to propositions (Definition 1.5). The *excluded middle for propositions*, $\mathsf{LEM}_{-1}$, is validated in the simplicial model of univalent type theory [KL20].

In parametric type theory, however, even this law is refuted. In fact, we can contradict the *weak excluded middle*, WLEM, which applies only to negated types. It follows from function extensionality that negated types are always propositions, so we have $\mathsf{LEM}_{-1} \to \mathsf{WLEM}$.

**Lemma 3.18.** If $A$ type is bridge-discrete, then any function $F \in \mathcal{U} \to A$ is constant.

*Proof.* For any pair of types $B_0, B_1$, we can apply $F$ at the empty relation between them.

$$\lambda^{\mathbf{I}}\boldsymbol{x}.F(\mathsf{Gel}_{\boldsymbol{x}}(B_0, B_1, \dots \perp)) \in \mathsf{Bridge}_A(FB_0, FB_1)$$

When $A$ is bridge-discrete, this induces a path between $FB_0$ and $FB_1$.

□

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:29

### Theorem 3.19. $\neg$WLEM.

Proof. Suppose we have $w \in \mathsf{WLEM}$. By Lemma 3.18, we know that $\mathsf{fst} \circ w$ is constant, so $\mathsf{fst}(w \top)$ and $\mathsf{fst}(w \bot)$ are equal. We obtain a contradiction by case analysis; clearly $\mathsf{fst}(w \top)$ must be $\mathsf{ff}$ and $\mathsf{fst}(w \bot)$ must be $\mathsf{tt}$.

For a deeper exploration of the relationship between parametricity and the excluded middle, we refer to Booij, Escardó, Lumsdaine, and Shulman [BELS16].

3.4. The smash product. Now we come to our motivating example: proving coherence laws for the smash product. In this section, we adopt some conventions for dealing with pointed types, elements of $\mathcal{U}_{\mathsf{pt}} := (A : \mathcal{U}) \times A$. We give pointed types names like $A_*, B_*, \ldots$ and write $A, B, \ldots$ and $a_0, b_0, \ldots$ for their first and second components respectively. Given two pointed types $A_*, B_*$, the type of basepoint-preserving functions between them is defined as $A_* \to B_* := (f : A \to B) \times \mathsf{Path}_B(f a_0, b_0)$. The identity function is a basepoint-preserving function $\langle \lambda a.a, \lambda^\parallel ..a_0 \rangle \in A_* \to A_*$, and there is a unique pointed constant function $\langle \lambda ..b_0, \lambda^\parallel ..b_0 \rangle \in A_* \to B_*$ between any pair of pointed types. The type of pointed functions can itself be made a pointed type $A_* \to_* B_*$ by taking the pointed constant function as basepoint, but we will not need this here. As with types, we write $f_*$ for basepoint-preserving functions, $f$ for the underlying function, and $f_0$ for the proof that it preserves the basepoint. Finally, we write $\mathsf{bool}_*$ for the booleans with basepoint $\mathsf{tt}$.

The underlying type of the smash product is given by the following higher inductive type.

data $A_* \land B_*$ where
$\mid \langle\langle a : A, b : B \rangle\rangle \in A_* \land B_*$$
$\mid \circledast^\mathsf{L} \in A_* \land B_*$$
$\mid \circledast^\mathsf{R} \in A_* \land B_*$$
$\mid \mathsf{spoke}^\mathsf{L}(b : B, x : \mathbb{I}) \in A_* \land B_* \ [x = 0 \hookrightarrow \circledast^\mathsf{L} \mid x = 1 \hookrightarrow \langle\langle a_0, b \rangle\rangle]$
$\mid \mathsf{spoke}^\mathsf{R}(a : A, x : \mathbb{I}) \in A_* \land B_* \ [x = 0 \hookrightarrow \circledast^\mathsf{R} \mid x = 1 \hookrightarrow \langle\langle a, b_0 \rangle\rangle]$

In words, $A_* \land B_*$ is the ordinary product $A \times B$ quotiented by the relation collapsing together all elements of the form $\langle a_0, b \rangle$ or $\langle a, b_0 \rangle$. Elements of the former form are identified with a new “hub” point $\circledast^\mathsf{L}$, while elements of the latter are identified with a separate point $\circledast^\mathsf{R}$, producing a shape shown in Figure 7. We write $A_* \land_* B_*$ for the smash product viewed as a pointed type with basepoint $\langle\langle a_0, b_0 \rangle\rangle$.

We will begin by focusing on the following theorem.

Theorem 3.20. Any family of pointed functions $(A_*, B_*: \mathcal{U}_{\mathsf{pt}}) \to (A_* \land_* B_* \to A_* \land_* B_*)$ is either the polymorphic identity or the polymorphic constant pointed function, up to a path.

In an effort to show we have nothing up our sleeves, we will avoid sweeping gory details—that is, coherence proofs—under the rug. However, we encourage the reader to focus on the broad strokes of the argument, and as such we will be less diligent about explaining the gory details.

The relations we use in the following will all be graphs of functions. As such, we introduce the following shorthand notation.

Definition 3.21. Given $f : A \to B$, write $\mathsf{Gr}_r(A, B, f) := \mathsf{Gel}_r(A, B, a.b.\mathsf{Path}_B(f a, b))$. Given $f_* : A_* \to B_*$, define $\mathsf{Gr}_r^*(A_*, B_*, f_*) := \langle \mathsf{Gr}_r(A, B, f), \mathsf{gel}_r(a_0, b_0, f_0) \rangle \in \mathcal{U}_{\mathsf{pt}}$.

5:30

E. CAVALLO AND R. HARPER

Vol. 17:4

![img-4.jpeg](img-4.jpeg)

Figure 7: The smash product of $\langle A, a_0 \rangle$ and $\langle B, b_0 \rangle$

We prove a graph lemma (Lemma 3.25) that relates the smash product of $\mathbf{Gr}^s$-types with the action of the smash product on their underlying functions. First, the following two technical definitions will be handy for concisely filling coherence conditions.

Definition 3.22 (Concatenation by inverse). Let $M \in A$, $r \in \mathbb{I}$, and $x : \mathbb{I} \gg N \in A$ with $r = 1 \gg M = N[1/x] \in A$ be given. For any $s \in \mathbb{I}$, define $\text{conc-inv}_A^{r,s}(M, x.N) \in A$ as follows.

$$\text{conc-inv}_A^{r,s}(M, x.N) := \text{hcom}_A^{1 \rightsquigarrow s}(M; r = 0 \hookrightarrow \_M, r = 1 \hookrightarrow x.N)$$

![img-5.jpeg](img-5.jpeg)

The term $\text{conc-inv}_A^{r,0}(M, x.N)$ is the result of concatenating $M$ (as a path in direction $r$) with the inverse of $x.N$; we need the general form $\text{conc-inv}_A^{r,s}(M, x.N)$ to relate the composite to other terms.

Lemma 3.23 (Join connection). For any $P \in \text{Path}_A(M, N)$, we have a term as follows.

$$\text{connect}_A(P) \in \text{Path}_{x.\text{Path}_A(P@x,N)}(P, \lambda^\mathbb{I} \_N)$$

![img-6.jpeg](img-6.jpeg)

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:31

Proof. By Lemma 1.3, it suffices to construct a term when $P$ is a constant path $\lambda^{\mathbb{I}}_{-}M \in \mathsf{Path}_A(M, M)$, in which case we have $\lambda^{\mathbb{I}}_{-} \lambda^{\mathbb{I}}_{-} M \in \mathsf{Path}_{\mathsf{Path}_A(M, M)}(\lambda^{\mathbb{I}}_{-} M, \lambda^{\mathbb{I}}_{-} M)$. $\square$

The smash product has a functorial action on pointed functions, which we define as follows.

Definition 3.24. Given $f_*: A_* \to C_*$ and $g_*: B_* \to D_*$, we inductively define a map $f_* \wedge g_* \in A_* \wedge B_* \to C_* \wedge D_*$ as follows.

$$
\begin{array}{l}
(f_* \wedge g_*)(\langle\langle a, b \rangle\rangle) \quad := \quad \langle\langle f a, g b \rangle\rangle \\
(f_* \wedge g_*)(\circledast^{\mathsf{L}}) \quad := \quad \circledast^{\mathsf{L}} \\
(f_* \wedge g_*)(\circledast^{\mathsf{R}}) \quad := \quad \circledast^{\mathsf{R}} \\
(f_* \wedge g_*)(\mathsf{spoke}^{\mathsf{L}}(b, y)) \quad := \quad \mathsf{conc-inv}_{C_* \wedge D_*}^{y, 0}(\mathsf{spoke}^{\mathsf{L}}(g b, y), z.\langle\langle f_0 @ z, g b \rangle\rangle) \\
(f_* \wedge g_*)(\mathsf{spoke}^{\mathsf{R}}(a, y)) \quad := \quad \mathsf{conc-inv}_{C_* \wedge D_*}^{y, 0}(\mathsf{spoke}^{\mathsf{R}}(y, f a), z.\langle\langle f a, g_0 @ z \rangle\rangle)
\end{array}
$$

We now prove the graph lemma: that there is a map from the smash product of two $\mathsf{Gr}^*$-types to the $\mathsf{Gr}$-type corresponding to the smash of their underlying functions. We expect that this map is in fact an isomorphism and that a similar principle holds for $\mathsf{Gel}$-types more generally, but such results are not necessary here.

Lemma 3.25 (Graph Lemma for $\wedge$). For any $\boldsymbol{r} \in \mathbf{I}$, there is a map

$$
\wedge\text{-graph}_\boldsymbol{r} \in \mathsf{Gr}_\boldsymbol{r}^*(A_*, C_*, f_*) \wedge \mathsf{Gr}_\boldsymbol{r}^*(B_*, D_*, g_*) \to \mathsf{Gr}_\boldsymbol{r}(A_* \wedge B_*, C_* \wedge D_*, f_* \wedge g_))
$$

equal to the identity function on $A_* \wedge_* B_*$ when $\boldsymbol{r} = \mathbf{0}$ and on $C_* \wedge_* D_*$ when $\boldsymbol{r} = \mathbf{1}$.

Proof. We define the map by induction on the smash product in the domain.

\(\triangleright\) Case \(\langle \langle m,n\rangle \rangle\) : We test whether \(\pmb{r}\) is a constant or variable using extent. In the constant cases, we return \(\langle \langle m,n\rangle \rangle\) . In the case \(\pmb{r}\) is a variable \(\pmb{x}\) , we learn that \(m\) and \(n\) are the instantiation at \(\pmb{x}\) of bridges over their types; by GEL- \(\eta\) , they are of the form \(m = \mathsf{gel}_{\pmb{x}}(a,c,p)\) and \(n = \mathsf{gel}_{\pmb{x}}(b,d,q)\) . We return \(\mathsf{gel}_{\pmb{x}}(\langle \langle a,b\rangle \rangle ,\langle \langle c,d\rangle \rangle ,\lambda^{\mathbb{I}}z.\langle \langle p@\mathcal{Y},q@\mathcal{Y}\rangle \rangle)\)
\(\triangleright\) Case \(\circledast^{\mathsf{L}}\) : We return \(\mathsf{gel}_{\pmb{r}}(\circledast^{\mathsf{L}},\circledast^{\mathsf{L}},\lambda^{\mathbb{I}}_{-}\circledast^{\mathsf{L}})\)
\(\triangleright\) Case \(\circledast^{\mathsf{R}}\) : Symmetric to \(\circledast^{\mathsf{L}}\)
\(\triangleright\) Case \(\mathsf{spoke}^{\mathsf{L}}(n,y)\): We test whether \(\boldsymbol{r}\) is a constant or variable using extent. In the constant cases, we return \(\mathsf{spoke}^{\mathsf{L}}(n,y)\). In the case \(\boldsymbol{r}\) is a variable \(\boldsymbol{x}\), we learn that \(n\) is the instantiation at \(\boldsymbol{x}\) of a bridge; by GEL-\(\eta\), it is of the form \(n = \mathsf{gel}_{\boldsymbol{x}}(b,d,q)\). We return \(\mathsf{gel}_{\boldsymbol{x}}(\mathsf{spoke}^{\mathsf{L}}(b,y),\mathsf{spoke}^{\mathsf{L}}(d,y),\lambda^{\mathbb{I}}z,\dots)\), where \(\dots\) is the following composite.

$$
\mathsf{hcom}_{C_* \wedge D_*}^{1 \rightharpoonup 0} \left( \begin{array}{c c c c} & y = 0 & \hookrightarrow & \_\cdot \circledast^{\mathsf{L}} \\ \mathsf{spoke}^{\mathsf{L}}(q @ z, y); & y = 1 & \hookrightarrow & w.\langle\langle \mathsf{connect}_A(f_0) @ z @ w, q @ z \rangle\rangle \\ & z = 0 & \hookrightarrow & w.\mathsf{conc-inv}_{C_* \wedge D_*}^{y,w}(\mathsf{spoke}^{\mathsf{L}}(g b, y), z.\langle\langle f_0 @ z, g b \rangle\rangle) \\ & z = 1 & \hookrightarrow & \_\cdot \mathsf{spoke}^{\mathsf{L}}(d, y) \end{array} \right)
$$

$\triangleright$ Case $\mathsf{spoke}^{\mathsf{R}}(m, y)$: Symmetric to $\mathsf{spoke}^{\mathsf{L}}(n, y)$.

When $\boldsymbol{r}$ is a constant, the resulting function simplifies to the $\eta$-expansion of the identity function on $A_* \wedge B_*$. By a simple induction on $A_* \wedge B_*$, the $\eta$-expansion is path-equal to the identity function. We may therefore apply an $\mathsf{hcom}$ to adjust the boundary and obtain a function that is exactly the identity when $\boldsymbol{r} = \mathbf{0}$ or $\boldsymbol{r} = \mathbf{1}$. $\square$

Finally, we use the fact that $\mathsf{bool}_* \wedge \mathsf{bool}_*$ is isomorphic to $\mathsf{bool}_*$. This is a consequence of more general facts—that $\mathsf{bool}_*$ is a unit for the smash product, or alternatively that $(1 + X) \wedge (1 + Y) \simeq 1 + (X \times Y)$ when we take 1 for each basepoint—but we prove the

5:32

E. CAVALLO AND R. HARPER

Vol. 17:4

special case directly for simplicity's sake. The importance of bool* arises from the fact that elements of a pointed type X* are in correspondence with pointed maps bool* → X*. As such, we can use naturality conditions with respect to functions bool* → X* to “probe” the behavior of a function polymorphic in pointed types, as we will see in Lemma 3.27.

Lemma 3.26 (Smash of booleans). bool* ∧ bool* is isomorphic to bool*; in particular, any element of bool* ∧ bool* is path-equal to either ⟨tt, tt⟩ or ⟨ff, ff⟩.

Proof. In one direction, we define F ∈ bool → bool* ∧ bool* to send tt to ⟨tt, tt⟩ and ff to ⟨ff, ff⟩. In the other, we define G ∈ bool* ∧ bool* → bool to send ⟨ff, ff⟩ to ff and all other constructors to tt. Clearly G ∘ F is the identity. For the other inverse condition, we show (s:bool* ∧ bool*) → Pathbool*∧bool*(s, F(Gs)) by smash product induction as follows.

▷ Case ⟨tt, tt⟩: Reflexivity.
▷ Case ⟨tt, ff⟩:
λ¹y.hcom₀∼₁bool*∧bool* (spokeᴸ(tt, y); y = 0 ⇔ x.spokeᴸ(ff, x), y = 1 ⇔ ...⟨tt, tt⟩).
▷ Case ⟨ff, ff⟩: Reflexivity.
▷ Case ⊗ᴸ: λ¹y.spokeᴸ(tt, y).
▷ Case spokeᴸ(tt, x): connectbool*∧bool*(λ¹y.spokeᴸ(tt, y))@x.
▷ Case spokeᴸ(ff, x):
λ¹y.hcom₀∼ₓbool*∧bool* (spokeᴸ(tt, y); y = 0 ⇔ x.spokeᴸ(ff, x), y = 1 ⇔ ...⟨tt, tt⟩).

The cases for ⟨tt, ff⟩, ⊗ᴿ, and spokeᴿ are obtained by taking the cases for ⟨ff, tt⟩, ⊗ᴸ, and spokeᴸ respectively and replacing spokeᴸ with spokeᴿ everywhere.

The following result, which characterizes terms F ∈ (A*, B*:Uₚₜ) → A → B → A* ∧ B*, is the linchpin of the argument; all uses of internal parametricity in the final results factor through this lemma. As we only use internal parametricity with relations that are graphs of functions, this result may also be cast as a corollary of the naturality of such terms, a special case of parametricity. In particular, we use the following naturality square for a : A and b : B, where [c]* ∈ bool* → C* is the pointed function sending tt to c₀ and ff to c.

$$\begin{array}{c} \mathsf{bool} \times \mathsf{bool} \xrightarrow{F \mathsf{bool}_* \mathsf{bool}_*} \mathsf{bool}_* \wedge \mathsf{bool}_* \\ [a] \times [b] \Biggl\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A \times B \xrightarrow[FA_* B_*} A_* \wedge B_* \end{array}$$

Lemma 3.27 (Workhorse lemma). Let F ∈ (A*, B*:Uₚₜ) → A → B → A* ∧ B*. Then F is path equal to one of the following.

▷ λ...λ...λa.λb.⟨a, b⟩.
▷ λA*.λB*.λ...λ...⟨a₀, b₀⟩.

Proof. We show that the identity of F is determined by the value of F(bool*)(bool*)(ff)(ff). Let A*: Uₚₜ, B*: Uₚₜ, a : A, and b : B be given.

We have a function [a]* ∈ bool* → A* sending tt to a₀ and ff to a, likewise [b]* ∈ bool* → B* sending tt to b₀ and ff to b. Abstract a bridge variable x : I. We abbreviate G*a := Gr*a(bool*, A*, [a]*) and G*b := Gr*a(bool*, B*, [b]*). Applying F at G*a and G*b, we have the following.

$$FG_*^a G_*^b(\mathsf{gel}_x(\mathsf{ff}, a, \lambda^\mathbb{I}...a))(\mathsf{gel}_x(\mathsf{ff}, b, \lambda^\mathbb{I}...b)) \in G_*^a \wedge G_*^b$$

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:33

At $\boldsymbol{x} = \mathbf{0}$, this term is $F(\mathsf{bool}_{*})(\mathsf{bool}_{*})(\mathsf{ff})(\mathsf{ff})$, and at $\boldsymbol{x} = \mathbf{1}$ it is $FA_{*}B_{*}ab$. Now we apply the Graph Lemma to obtain a term in $\mathsf{Gr}_{x}(\mathsf{bool}_{*} \wedge \mathsf{bool}_{*}, A_{*} \wedge B_{*}, [a]_{*} \wedge [b]_{*})$ with the same boundary. Finally, we apply $\mathsf{ungel}$ to extract a path from $([a]_{*} \wedge [b]_{*})(F(\mathsf{bool}_{*})(\mathsf{bool}_{*})(\mathsf{ff})(\mathsf{ff}))$ to $FA_{*}B_{*}ab$. We therefore see that $F$ is the pairing function if $F(\mathsf{bool}_{*})(\mathsf{bool}_{*})(\mathsf{ff})(\mathsf{ff})$ is $\langle\langle\mathsf{ff}, \mathsf{ff}\rangle\rangle$ and the constant function if it is $\langle\langle\mathsf{tt}, \mathsf{tt}\rangle\rangle$; by Lemma 3.26, we are in one of these two cases.

**Corollary 3.28.** $(A_{*}, B_{*}\mathcal{U}_{\mathsf{pt}}) \to A \to B \to A_{*} \wedge B_{*}$ is a set: any pair of paths between two elements of the type are path-equal.

*Proof.* Lemma 3.27 shows that the type is isomorphic to $\mathsf{bool}$, which is a set.

This is everything we need to prove the final result.

*Proof of Theorem 3.20.* Let $F_{*} \in (A_{*}, B_{*}\mathcal{U}_{\mathsf{pt}}) \to A_{*} \wedge_{*} B_{*} \to A_{*} \wedge_{*} B_{*}$ be given. To characterize $F_{*}$, we need to characterize its behavior on each constructor of $A_{*} \wedge B_{*}$ as well as the proof that it preserves the basepoint of $A_{*} \wedge_{*} B_{*}$.

First, by Lemma 3.27, we know that $\lambda^{\sharp}a.\lambda^{\sharp}b.FA_{*}B_{*}(\langle\langle a,b\rangle\rangle)$ is either pairing or constant. The values of $FA_{*}B_{*}\circledast^{\mathsf{L}}$ and $FA_{*}B_{*}\circledast^{\mathsf{R}}$ must be path-equal to $\circledast^{\mathsf{L}}$ and $\circledast^{\mathsf{R}}$ respectively, as $F$ is basepoint-preserving and $\circledast^{\mathsf{L}}$ ($\circledast^{\mathsf{R}}$) is connected to the basepoint by $\mathsf{spoke}^{\mathsf{L}}(b_{0}, -)$ ($\mathsf{spoke}^{\mathsf{R}}(a_{0}, -)$).

Next, observe that we can capture the behavior of $F$ on $\mathsf{spoke}^{\mathsf{L}}$ by the following term, which is a path in $(A_{*}, B_{*}\mathcal{U}_{\mathsf{pt}}) \to A \to B \to A_{*} \wedge_{*} B_{*}$ between $\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda_{\dots}FA_{*}B_{*}\circledast^{\mathsf{L}}$ and $\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda b.FA_{*}B_{*}(\langle\langle a,b\rangle\rangle)$.

$$\lambda^{\sharp}y.\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda b.FA_{*}B_{*}(\mathsf{spoke}^{\mathsf{L}}(b, y))$$

By Corollary 3.28, this path is path-equal to any other path in this type, in particular path-equal to whatever we need it to be to complete this proof. The same applies to $\circledast^{\mathsf{R}}$. Finally, we can apply the same trick for the basepoint path, writing it as a path in the type from Corollary 3.28 as follows.

$$\lambda^{\sharp}y.\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda_{\dots}f_{0}A_{*}B_{*}\circledast y$$

Now we argue that this strategy can be used to prove the $n$-ary generalization in a uniform way. (The binary version is in fact not very useful on its own; the direct proof of commutativity for the smash product is uncharacteristically straightforward, because the definition of $\wedge$ is completely symmetric.)

**Theorem 3.29.** Any function $(A_{*}^{0}, \dots, A_{*}^{n}\mathcal{U}_{\mathsf{pt}}) \to (A_{*}^{0} \wedge_{*} \dots \wedge_{*} A_{*}^{n}) \to (A_{*}^{0} \wedge_{*} \dots \wedge_{*} A_{*}^{n})$ (associating $\wedge_{*}$ to the right) is either the polymorphic identity or the polymorphic constant pointed function.

*Proof.* We show by induction on $i \leq n + 1$ that any

$$(A_{*}^{0}, \dots, A_{*}^{n}\mathcal{U}_{\mathsf{pt}}) \to A^{0} \to \dots \to A^{n-i} \to (A_{*}^{n-i+1} \wedge_{*} \dots \wedge_{*} A_{*}^{n}) \to (A_{*}^{0} \wedge_{*} \dots \wedge_{*} A_{*}^{n})$$

is either given by iterated pairing or constant. For $i = 0$, it follows from a simple $n$-ary generalization of the workhorse lemma (instantiating each type argument with a graph and applying the binary Graph Lemma repeatedly). For $i > 0$, it follows from the induction hypothesis by the same argument as in the proof of Theorem 3.20.

5:34

E. CAVALLO AND R. HARPER

Vol. 17:4

The key here is that we are never involved in an iterated induction on smash products: for each $i$ in the proof of Theorem 3.29, we have an argument by induction on one occurrence of the smash product, but these arguments do not overlap.

## 4. COMPUTATIONAL INTERPRETATION

We now develop the computational interpretation underlying parametric cubical type theory, building on the work of Allen for Martin-Löf type theory [All87] and Angiuli et al. for cartesian cubical type theory [AFH18]. We closely follow the presentation in Angiuli's thesis [Ang19]; we will give a reasonably complete tour through the definitions, but rely on [Ang19] for many results that are essentially unaffected by the addition of bridge intervals and parametricity primitives.

An interpretation in these frameworks is built from two components: a deterministic operational semantics on closed untyped terms and a value type system. The former explains the evaluation of terms; the latter explains which closed values are names for types and which closed values are elements of said types. Given these two components, we derive an interpretation of the open judgments—$\Gamma \gg A$ type and so on—by extending the value type system first to arbitrary closed terms (roughly, a term is well-typed when it evaluates to a well-typed value) and then to open terms (an open term is well-typed when its closed instances are well-typed).

4.1. Interval contexts and terms. In the above and the following, closed refers to terms that do not contain term variables but that may contain interval variables. It is essential to consider evaluation of terms containing interval variables in order to accommodate the terms $\text{coe}_{x,A}^{r\to s}(M)$ and $\text{ungel}(\boldsymbol{x},N)$, which evaluate terms (here $A$ and $N$) under interval binders. We use $\Psi$ to denote contexts consisting solely of path and bridge interval variables.

$$\Psi ::= \cdot \mid \Psi, x : \mathbb{I} \mid \Psi, \boldsymbol{x} : \mathbf{I}$$

We write $\Psi' \Vdash \psi \in \Psi$ for interval substitutions, which take terms $M$ in context $\Psi$ to terms $M\psi$ in context $\Psi'$. As always, path interval variables are structural and bridge interval variables are affine; $\psi$ cannot identify two bridge variables except by sending both to $\mathbf{0}$ or $\mathbf{1}$.

Definition 4.1. The path interval term judgment $\Psi \Vdash r \in \mathbb{I}$ is defined to hold when either $r \in \{0, 1\}$ or $r = x$ where $(x : \mathbb{I}) \in \Psi$; the bridge interval term judgment $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$ is defined likewise. The interval substitution judgment is then inductively generated by the following rules.

$$\frac{\Psi' \Vdash \cdot \in \cdot}{\Psi' \Vdash \cdot \in \cdot} \qquad \frac{\Psi' \Vdash \psi \in \Psi \qquad \Psi' \Vdash r \in \mathbb{I}}{\Psi' \Vdash (\psi, r/x) \in (\Psi, x : \mathbb{I})} \qquad \frac{\Psi' \Vdash \boldsymbol{r} \in \mathbf{I} \qquad \Psi' \setminus \boldsymbol{r} \Vdash \psi \in \Psi}{\Psi' \Vdash (\psi, \boldsymbol{r}/\boldsymbol{x}) \in (\Psi, \boldsymbol{x} : \mathbf{I})}$$

The judgment $\Psi \Vdash \xi$ constraint is likewise inductively generated by constraints of the form $\Psi \Vdash (r = s)$ constraint and $\Psi \Vdash (\boldsymbol{r} = \varepsilon)$ constraint.

Remark 4.2. We have an operator $\forall \boldsymbol{x}.-$ on constraints defined as follows.

$$\forall \boldsymbol{x}.(r = s) := (r = s)$$

$$\forall \boldsymbol{x}.(\boldsymbol{x} = \varepsilon) := (\mathbf{0} = \mathbf{1})$$

$$\forall \boldsymbol{x}.(\boldsymbol{r} = \varepsilon) := (\boldsymbol{r} = \varepsilon) \quad \text{if } \boldsymbol{r} \neq \boldsymbol{x}$$

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:35

\[
\begin{array}{l} \overline {{\operatorname{Bridge} _ {\boldsymbol {x} . A} \left(M _ {0} , M _ {1}\right) \text {val}}} \quad \overline {{\lambda^ {\mathbf {I}} \boldsymbol {x} . P \text {val}}} \quad \frac {Q \longmapsto Q ^ {\prime}}{Q @ \boldsymbol {r} \longmapsto Q ^ {\prime} @ \boldsymbol {r}} \quad \overline {{\left(\lambda^ {\mathbf {I}} \boldsymbol {x} . P\right) @ \boldsymbol {r} \longmapsto P [ \boldsymbol {r} / \boldsymbol {x} ]}} \\ \overline {{\operatorname{hcom} _ {\text { Bridge } _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})} ^ {r \rightsquigarrow s} (M ; \overline {{\xi_ {i} \hookrightarrow y . N _ {i}}}) \longmapsto}} \\ \lambda^ {\mathbf {I}} \boldsymbol {x}. \operatorname{hcom} _ {A} ^ {r \rightsquigarrow s} (M @ \boldsymbol {x}; \overline {{\xi_ {i} \hookrightarrow y . N _ {i} @ \boldsymbol {x}}}, \boldsymbol {x} = \mathbf {0} \hookrightarrow .. M _ {0}, \boldsymbol {x} = \mathbf {1} \hookrightarrow .. M _ {1}) \\ \overline {{\operatorname{coe} _ {y . \text { Bridge } _ {\boldsymbol {x} . A} (M _ {0} , M _ {1})} ^ {r \rightsquigarrow s} (Q) \longmapsto \lambda^ {\mathbf {I}} \boldsymbol {x} . \operatorname{com} _ {y . A} ^ {r \rightsquigarrow s} (Q @ \boldsymbol {x} ; \boldsymbol {x} = \mathbf {0} \hookrightarrow y . M _ {0} , \boldsymbol {x} = \mathbf {1} \hookrightarrow y . M _ {1})}} \\ \frac {\varepsilon \in \{0 , 1 \}}{\operatorname{extent} _ {\varepsilon} (M ; a _ {0} . N _ {0} , a _ {1} . N _ {1} , a _ {0} . a _ {1} . \bar {a} . \overline {{N}}) \longmapsto N _ {\varepsilon} [ M / a ]} \\ \overline {{\operatorname{extent} _ {\boldsymbol {x}} (M ; a _ {0} . N _ {0} , a _ {1} . N _ {1} , a _ {0} . a _ {1} . \bar {a} . \overline {{N}}) \longmapsto \overline {{N}} [ M [ \mathbf {0} / \boldsymbol {x} ] / a _ {0} ] [ M [ \mathbf {1} / \boldsymbol {x} ] / a _ {1} ] [ \lambda^ {\mathbf {I}} \boldsymbol {x} . M / \bar {a} ] @ x}} \\ \frac {\varepsilon \in \{0 , 1 \}}{\operatorname{Gel} _ {\varepsilon} (A _ {0} , A _ {1} , a _ {0} . a _ {1} . R) \longmapsto A _ {\varepsilon}} \quad \overline {{\operatorname{Gel} _ {\boldsymbol {x}} (A _ {0} , A _ {1} , a _ {0} . a _ {1} . R) \text {val}}} \quad \frac {\varepsilon \in \{0 , 1 \}}{\operatorname{gel} _ {\varepsilon} (M _ {0} , M _ {1} , P) \longmapsto M _ {\varepsilon}} \\ \overline {{\operatorname{gel} _ {\boldsymbol {x}} (M _ {0} , M _ {1} , P) \text {val}}} \quad \frac {Q \longmapsto Q ^ {\prime}}{\operatorname{ungel} (\boldsymbol {x} . Q) \longmapsto \operatorname{ungel} (\boldsymbol {x} . Q ^ {\prime})} \quad \overline {{\operatorname{ungel} (\boldsymbol {x} . \operatorname{gel} _ {\boldsymbol {x}} (M _ {0} , M _ {1} , P)) \longmapsto P}} \\ M _ {\varepsilon , y} := \operatorname{hcom} _ {A _ {\varepsilon}} ^ {r \rightsquigarrow y} (Q [ \varepsilon / \boldsymbol {x} ]; \overline {{\xi_ {i} [ \varepsilon / \boldsymbol {x} ] \hookrightarrow y . Q _ {i} [ \varepsilon / \boldsymbol {x} ])}} \\ P := \operatorname{com} _ {y. R [ M _ {0, y}, M _ {1, y} / a _ {0}, a _ {1} ]} ^ {r \rightsquigarrow s} (\operatorname{ungel} (\boldsymbol {x}. Q); \overline {{\forall \boldsymbol {x} . \xi_ {i} \hookrightarrow y . \operatorname{ungel} (\boldsymbol {x} . Q _ {i})}}) \\ \overline {{\operatorname{hcom} _ {\operatorname{Gel} _ {\boldsymbol {x}} (A _ {0} , A _ {1} , a _ {0} . a _ {1} . R)} ^ {r \rightsquigarrow s} (Q ; \overline {{\xi_ {i} \hookrightarrow y . Q _ {i}}}) \longmapsto \operatorname{gel} _ {\boldsymbol {x}} (M _ {0 , s} , M _ {1 , s} , P)}} \\ M _ {\varepsilon , y} := \operatorname{coe} _ {y. A _ {\varepsilon}} ^ {r \rightsquigarrow y} (Q [ \varepsilon / \boldsymbol {x} ]) \quad P := \operatorname{coe} _ {y. R [ M _ {0, y}, M _ {1, y} / a _ {0}, a _ {1} ]} ^ {r \rightsquigarrow s} (\operatorname{ungel} (\boldsymbol {x}. Q)) \\ \overline {{\operatorname{coe} _ {y . \operatorname{Gel} _ {\boldsymbol {x}} (A _ {0} , A _ {1} , a _ {0} . a _ {1} . R)} ^ {r \rightsquigarrow s} (Q) \longmapsto \operatorname{gel} _ {\boldsymbol {x}} (M _ {0 , s} , M _ {1 , s} , P)}} \\ \end{array}
\]

Figure 8: Operational semantics of parametric cubical type theory

4.2. Operational semantics. An operational semantics, which specifies the evaluation of closed terms, is defined by judgments M val (“M is a value”) and  \( M \longmapsto M' \)  (“M steps to  \( M'' \) ) operating on closed terms. We write  \( M \longmapsto^{*} M' \)  to mean that M steps to  \( M' \)  in zero or more steps and  \( M \Downarrow V \)  to mean that  \( M \longmapsto^{*} V \)  for some V val.

We give the defining rules for our operational semantics in Figure 8. We show only those rules that involve the parametricity primitives; for everything else, we refer to [Ang19, §4.1]. Although we choose a specific operational semantics here, the interpretation goes through for any operational semantics that extends it; we need only the presence of these rules, not the absence of others.

4.3. Judgments from a value type system. A value type system specifies the values that are names for types and the values that each such type classifies. For practical purposes, it

5:36

E. CAVALLO AND R. HARPER

Vol. 17:4

useful to first introduce candidate value type systems and then impose additional conditions under which a candidate is an actual type system.

Definition 4.3. A candidate value type system $\tau$ is a quaternary relation $\tau(\Psi, V, V', \varphi)$ ranging over contexts $\Psi$, values $V, V'$ in context $\Psi$, and binary relations $\varphi$ on values in context $\Psi$.

We read an instance $\tau(\Psi, V, V', \varphi)$ of the relation as specifying that (1) the values $V$ and $V'$ are equal types in context $\Psi$ and that (2) these type names stand for the relation $\varphi$: values $W$ and $W'$ are equal elements of $V$ (likewise $V'$) in context $\Psi$ when $\varphi(W, W')$ holds.

Given a candidate value type system, we derive candidate judgments extending the defining relations to non-value terms. In [All87], a term is a type (resp. well-typed) when it evaluates to a type value (resp. well-typed value). In a setting with interval variables, it becomes necessary to require a stronger “coherent evaluation” condition: to be well-typed, a term must not merely evaluate to a well-typed value, but do so in a way that interacts in a sensible way with interval substitutions. First, we define “incoherent” extensions of value type systems and terms to terms.

Definition 4.4. Given a candidate value type system, we write $\tau^{\Downarrow}(\Psi, A, A', \varphi)$ for (possibly non-value) terms $A, A'$ to mean that $A \Downarrow V$ and $A' \Downarrow V'$ for some $V, V'$ with $\tau(\Psi, V, V', \varphi)$. Given a relation $\varphi$ on values, we define a relation $\varphi^{\Downarrow}$ on terms: $\varphi^{\Downarrow}(M, M')$ holds when $M \Downarrow V$ and $M' \Downarrow V'$ for some $V, V'$ with $\varphi(V, V')$.

To cut down to the coherently well-behaved types and terms, we introduce a notion of $\Psi$-relation, a family of relations indexed by the substitutions into $\Psi$.

Definition 4.5. A $\Psi$-relation $\alpha$ is a family of binary relations $\alpha_{\psi}$, indexed by substitutions $\Psi' \Vdash \psi \in \Psi$ into $\Psi$ and where each $\alpha_{\psi}$ relates terms in context $\Psi'$. Given a $\Psi$-relation $\alpha$ and $\Psi' \Vdash \psi \in \Psi$, we define a $\Psi'$-relation $\alpha\psi$ by $(\alpha\psi)_{\psi'} := \alpha_{\psi\psi'}$.

We now define the coherent candidate judgments: $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$, which asserts that $A$ and $A'$ coherently evaluate to equal type names standing for the $\Psi$-relation $\alpha$, and $\Psi \Vdash M \sim M' \in \alpha$, which asserts that $M$ and $M'$ coherently evaluate to values equal in $\alpha$.

Definition 4.6. We define the candidate judgments as follows.

$\triangleright \Psi \Vdash A \sim A' \downarrow \alpha \in \tau$ holds when for every $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, we have

- (1) $A\psi_1 \Downarrow A_1$ and $A'\psi_1 \Downarrow A_1'$ for some $A_1, A_1'$,
- (2) there is some $\varphi$ such that $\tau^{\Downarrow}(\Psi_2, -, -, \varphi)$ relates $(A_1\psi_2, A\psi_1\psi_2)$ and its reverse, $(A_1'\psi_2, A'\psi_1\psi_2)$ and its reverse, and $(A_1\psi_2, A_1'\psi_2)$,

and $\alpha$ is a $\Psi$-relation on values such that $\tau^{\Downarrow}(\Psi', A\psi, A'\psi, \alpha_{\psi})$ for all $\Psi' \Vdash \psi \in \Psi$.

$\triangleright \Psi \Vdash M \sim M' \in \alpha$ holds when for every $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, we have

- (1) $M\psi_1 \Downarrow M_1$ and $M'\psi_1 \Downarrow M_1'$ for some $M_1, M_1'$,
- (2) $(\alpha_{\psi_1\psi_2})^{\Downarrow}$ relates $(M_1\psi_2, M\psi_1\psi_2)$ and its reverse, and $(M_1'\psi_2, M_1'\psi_2)$.

The conditions in the definition of $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$, for example, ask that we have the square shown below: whether we apply $\psi_2$ to $A\psi_1$ or first evaluate and then apply $\psi_2$, we

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:37

get the same result up to the equality defined by $\tau^{\Downarrow}$.

$$\begin{array}{c c c} A \psi_1 & \Longrightarrow & A_1 \\ -\psi_2 \downarrow & & \downarrow -\psi_2 \\ A \psi_1 \psi_2 & \tau^{\Downarrow} & A_1 \psi_2 \end{array}$$

Note that the candidate judgments are stable under interval substitution by definition: for example, if $\Psi \Vdash M \sim M' \in \alpha$, then $\Psi' \Vdash M\psi \sim M'\psi \in \alpha\psi$ for any $\Psi' \Vdash \psi \in \Psi$.

A candidate is a value type system when the typing relation satisfies several additional conditions, which require that each type names at most one relation, that the type and element relations are partial equivalence relations, and that any value type is *coherently* a type.

**Definition 4.7.** A *value type system* $\tau$ is a candidate value type system satisfying the following.

**Unicity:** If $\tau(\Psi, V, V', \varphi)$ and $\tau(\Psi, V, V', \varphi')$, then $\varphi = \varphi'$.

**PER:** $\tau(\Psi, -, -, \varphi)$ is a partial equivalence relation (PER) for all $\Psi, \varphi$.

**PER-valuation:** If $\tau(\Psi, V, V', \varphi)$, then $\varphi$ is a PER.

**Value-coherence:** If $\tau(\Psi, V, V', \varphi)$, then $\Psi \Vdash V \sim V' \downarrow \alpha \in \tau$ for some $\alpha$.

Likewise, we will require that the values related by the relations associated to types are in fact coherently related.

**Definition 4.8.** We say a $\Psi$-relation $\alpha$ is *value-coherent* and write $\operatorname{Coh}(\alpha)$ if $\alpha_{\psi}(V, V')$ implies $\Psi' \Vdash V\psi \sim V'\psi \in \alpha\psi$ for all $\psi$ and $V, V'$.

Given a value type system, we obtain typing judgments first on closed and then on open terms. For types, we also distinguish between *pretypes* and *types*, the latter of which are required to support Kan operations. For the following series of definitions, we fix an ambient value type system $\tau$.

**Definition 4.9.** We define the closed judgments as follows.

- $\triangleright \Psi \Vdash A = A'$ pretype holds when $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$ for some value-coherent $\alpha$.
- $\triangleright$ Presupposing $\Psi \Vdash A = A$ pretype, $\Psi \Vdash M = M' \in A$ holds when $\Psi \Vdash A \sim A \downarrow \alpha \in \tau$ with $\Psi \Vdash M \sim M' \in \alpha$.

We define $\Psi \Vdash A$ pretype to mean $\Psi \Vdash A = A$ pretype, likewise $\Psi \Vdash M \in A$ to mean $\Psi \Vdash M = M \in A$. We will abbreviate future reflexive judgments in this fashion without comment. When we have $\Psi \Vdash A$ pretype, we write $[[A]]$ for the (necessarily unique) value $\Psi$-relation assigned to $A$ by the value type system.

We now extend the closed judgments to *open judgments*, defined on terms containing arbitrary variables. We do so by means of a *context instantiation judgment* $\Psi \Vdash \gamma = \gamma' \in \Gamma$, which specifies the ways a general context $\Gamma$ may be instantiated by closed terms over $\Psi$.

**Definition 4.10.** We define the context instantiations $\Psi \Vdash \gamma = \gamma' \in \Gamma$ inductively as follows.

- $\triangleright \Psi \Vdash \cdot = \cdot \in \cdot$.
- $\triangleright \Psi \Vdash (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)$ when $\Psi \Vdash \gamma = \gamma' \in \Gamma$ and $\Psi \Vdash M = M' \in A\gamma$.
- $\triangleright \Psi \Vdash (\gamma, r/x) = (\gamma, r/x) \in (\Gamma, x : \mathbb{I})$ when $\Psi \Vdash \gamma = \gamma' \in \Gamma$ and $\Psi \Vdash r \in \mathbb{I}$.
- $\triangleright \Psi \Vdash (\gamma, \boldsymbol{r}/\boldsymbol{x}) = (\gamma, \boldsymbol{r}/\boldsymbol{x}) \in (\Gamma, \boldsymbol{x} : \mathbb{I})$ when $\Psi \Vdash \boldsymbol{r} \in \mathbb{I}$ and $\Psi \setminus \boldsymbol{r} \Vdash \gamma = \gamma' \in \Gamma$.

5:38

E. CAVALLO AND R. HARPER

Vol. 17:4

$\triangleright \Psi \Vdash \gamma = \gamma' \in (\Gamma, \xi)$ when $\Psi \Vdash \gamma = \gamma' \in \Gamma$ and $\xi\gamma$ is true.

The open type and term judgments are then defined to hold when their closed instantiations hold.

**Definition 4.11.** We define the open judgments as follows.

$\triangleright \Gamma \gg A = A'$ pretype holds when $\Psi \Vdash A\gamma = A'\gamma'$ pretype for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

$\triangleright \Gamma \gg M = M' \in A$ holds when $\Psi \Vdash M\gamma = M'\gamma' \in A\gamma$ for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

We note that, in contrast, we define the open *interval* judgments without reference to the terms in the context $\Gamma$. It is therefore not the case that, for example, $v : \perp \gg 0 = 1 \in \mathbb{I}$; interval judgments are prior to term judgments.

**Definition 4.12.** The judgment $\Gamma \gg r \in \mathbb{I}$ is defined to hold when either $r \in \{0, 1\}$ or $(x : \mathbb{I}) \in \Gamma$; an equality $\Gamma \gg r = s \in \mathbb{I}$ is defined to hold when $\Gamma \gg r, s \in \mathbb{I}$ are in the equivalence relation closure of the constraints appearing in $\Gamma$. The judgments $\Gamma \gg r = s \in \mathbf{I}$ and $\Gamma \gg \xi = \xi'$ constraint are defined likewise.

**Definition 4.13.** We define the well-formed contexts inductively.

$\triangleright \cdot = \cdot \text{ctx}$.

$\triangleright (\Gamma, a : A) = (\Gamma', a : A')$ ctx when $\Gamma = \Gamma'$ ctx and $\Gamma \gg A = A'$ pretype.

$\triangleright (\Gamma, x : \mathbb{I}) = (\Gamma', x : \mathbb{I})$ ctx when $\Gamma = \Gamma'$ ctx.

$\triangleright (\Gamma, x : \mathbf{I}) = (\Gamma', x : \mathbf{I})$ ctx when $\Gamma = \Gamma'$ ctx.

$\triangleright (\Gamma, \xi) = (\Gamma', \xi)$ ctx when $\Gamma = \Gamma'$ ctx and $\Gamma \gg \xi = \xi'$ constraint.

A pretype $A$ is a (*Kan*) *type* when it supports the Kan operations, that is, when the operators coe and hcom are well-typed at $A$ and satisfy the necessary equations.

**Definition 4.14** (Kan types). Presupposing $\Psi \Vdash A = A'$ pretype, we say $\Psi \Vdash A = A'$ type when the following conditions hold.

$\triangleright$ For any $(\Psi', x : \mathbb{I}) \Vdash \psi \in \Psi$, if $\Psi' \Vdash r, s \in \mathbb{I}$ and $\Psi' \Vdash M = M' \in A\psi[r/x]$, then

- $\Psi' \Vdash \text{coe}_{x.A\psi}^{r \rightsquigarrow s}(M) = \text{coe}_{x.A'\psi}^{r \rightsquigarrow s}(M') \in A\psi[s/x]$,

- $\Psi' \Vdash \text{coe}_{x.A\psi}^{r \rightsquigarrow r}(M) = M \in A\psi[r/x]$,

$\triangleright$ For any $\Psi' \Vdash \psi \in \Psi$, if $\Psi' \Vdash r, s \in \mathbb{I}, n \in \mathbb{N}$, $\Psi' \Vdash \xi_i$ constraint for all $i < n$, and

- $\Psi' \Vdash M = M' \in A\psi$

- $\Psi', x : \mathbb{I} \Vdash N_i = N'_j \in A\psi$ for all $i, j < n$,

- $\Psi' \Vdash M = N_i[r/x] \in A\psi$ for all $i < n$,

then

- $\Psi' \Vdash \text{hcom}_{A\psi}^{r \rightsquigarrow s}(M; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) = \text{hcom}_{A'\psi}^{r \rightsquigarrow s}(M'; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) \in A\psi$,

- $\Psi' \Vdash \text{hcom}_{A\psi}^{r \rightsquigarrow s}(M; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) = N_i[s/x] \in A\psi$ if $\xi_i$ is true,

- $\Psi' \Vdash \text{hcom}_{A\psi}^{r \rightsquigarrow r}(M; \overrightarrow{\xi_i \hookrightarrow x.N'_i}) = M \in A\psi$.

The extension of the type judgment to open terms is defined as for the pretype judgment: $\Gamma \gg A = A'$ type holds when $\Psi \Vdash A\gamma = A'\gamma'$ type for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

We may also define the open substitution judgment following the pattern of the instantiation judgment.

**Definition 4.15.** We define the substitutions $\Gamma \gg \gamma = \gamma' \in \Gamma$ inductively as follows.

$\triangleright \Gamma \gg \cdot = \cdot \in \cdot$.

$\triangleright \Gamma \gg (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)$ when $\Gamma \gg \gamma = \gamma' \in \Gamma$ and $\Gamma \gg M = M' \in A\gamma$.

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:39

\(\triangleright \Gamma \gg (\gamma, r / x) = (\gamma, r' / x) \in (\Gamma, x : \mathbb{I})\) when \(\Gamma \gg \gamma = \gamma' \in \Gamma\) and \(\Gamma \gg r = r' \in \mathbb{I}\).  
\(\triangleright \Gamma \gg (\gamma, r / x) = (\gamma, r' / x) \in (\Gamma, x : \mathbf{I})\) when \(\Gamma \gg r = r' \in \mathbf{I}\) and \(\Gamma \backslash r \Vdash \gamma = \gamma' \in \Gamma\).  
\(\triangleright \Gamma \gg \gamma = \gamma' \in (\Gamma, \xi)\) when \(\Gamma \gg \gamma = \gamma' \in \Gamma\) and \(\xi \gamma\) is true.

Now that we have laid out the extrapolation of open judgments from a value type system, it remains to construct a particular type system that will validate the inference rules we presented in Sections 1 and 2.

4.4. Constructing a value type system. We obtain a value type system by a fixed-point construction, first defining the least candidate value type system closed under our desired type formers and then showing that it constitutes a value type system. To start, we define the pieces corresponding to each type former. Relative to [Ang19], the novelties here are the Bridge- and Gel-types.

\(\begin{array}{rl} & {\mathrm{BRIDGE}(\tau):=}\\ & {\left\{(\Psi ,\mathrm{Bridge}_{\pmb{x},A}(M_0,M_1),\mathrm{Bridge}_{\pmb{x},A'}(M_0',M_1'),\varphi)\mid \right.}\\ & {\quad \exists \alpha .\Psi ,\pmb {x}:\mathbf{I}\Vdash A\sim A^{\prime}\downarrow \alpha \in \tau \wedge \mathrm{Coh}(\alpha)}\\ & {\quad \wedge (\forall \varepsilon \in \{0,1\} .\Psi \Vdash M_{\varepsilon}\sim M_{\varepsilon}^{\prime}\in \alpha [\pmb {\varepsilon} / \pmb {x}])}\\ & {\quad \wedge \varphi = \left\{(\lambda^{\mathbf{I}}\pmb {x}.M,\lambda^{\mathbf{I}}\pmb {x}.M^{\prime})\mid \Psi ,\pmb {x}:\mathbf{I}\Vdash M\sim M^{\prime}\in \alpha \wedge \forall \varepsilon .\Psi \Vdash M[\pmb {\varepsilon} / \pmb {x}]\sim M_{\varepsilon}\in \alpha [\pmb {\varepsilon} / \pmb {x}]\right\} \right\}}\\ & {\mathrm{GEL}(\tau):=}\\ & {\left\{(\Psi ,\mathrm{Gel}_{\pmb{x}}(A_{0},A_{1},a_{0}.a_{1}.R),\mathrm{Gel}_{\pmb{x}}(A_{0}',A_{1}',a_{0}.a_{1}.R'),\varphi)\mid \right.}\\ & {\quad \exists \alpha^{0},\alpha^{1},\beta^{(-,-,-,-,-)}.}\\ & {(\forall \varepsilon .\Psi \backslash \pmb {x}\Vdash A_{\varepsilon}\sim A_{\varepsilon}^{\prime}\downarrow \alpha \in \tau \wedge \mathrm{Coh}(\alpha^{\varepsilon}))}\\ & {\quad \wedge (\forall \Psi^{\prime}\Vdash \psi \in (\Psi \backslash \pmb {x}).\forall M_{0},M_{1},M_{0}^{\prime},M_{1}^{\prime}.(\forall \varepsilon .\alpha_{\psi}^{\varepsilon}(M_{\varepsilon},M_{\varepsilon}^{\prime}))\implies \\ & {\quad \Psi^{\prime}\Vdash R[M_{0},M_{1}/a_{0},a_{1}]\sim R^{\prime}[M_{0}^{\prime},M_{1}^{\prime}/a_{0},a_{1}]\downarrow \beta^{(\psi ,M_{0},M_{1},M_{0}^{\prime},M_{1}^{\prime})}\in \tau}\\ & {\quad \wedge \mathrm{Coh}(\beta^{(\psi ,M_{0},M_{1},M_{0}^{\prime},M_{1}^{\prime})}))}\\ & {\quad \wedge \varphi = \left\{(\mathrm{gel}_{\pmb{x}}(M_{0},M_{1},P),\mathrm{gel}_{\pmb{x}}(M_{0}^{\prime},M_{1}^{\prime},P^{\prime}))\mid \\ & {\quad \forall \varepsilon .(\Psi \backslash \pmb {x}\Vdash M_{\varepsilon}\sim M_{\varepsilon}^{\prime}\in \alpha^{\varepsilon})\wedge \Psi \backslash \pmb {x}\Vdash P\sim P^{\prime}\in \beta^{(\mathrm{id},M_0,M_1,M_0',M_1')} \right\} \right\}} \end{array}\)

Next, we have an operator on candidate value type systems that applies one level of type formers.

\[
K (\tau) := \operatorname{BRIDGE} (\tau) \cup \operatorname{GEL} (\tau) \cup \dots
\]

Finally, we obtain a least fixed-point  \( \tau_{0} \)  of this operator by the Knaster-Tarski fixed-point theorem [DP02, 2.35]. It is tedious but straightforward to check that this candidate value type system is in fact a value type system [Ang19, Lemma 4.8]. To construct a value type system with a universe, we can repeat the fixed-point construction with the addition of a type U interpreted by the relation  \( \tau_{0} \) , producing a new type system  \( \tau_{1} \)  that is closed under the same type formers as  \( \tau_{0} \)  but also contains  \( \tau_{0} \)  as a universe. This can be repeated further to produce a hierarchy of value type systems  \( \tau_{0} \subseteq \tau_{1} \subseteq \tau_{2} \subseteq \cdots \)  each containing its predecessors as universes; for our purposes, a single universe is sufficient.

As an immediate consequence of the way the typing judgments are defined, we have a canonicity theorem: any closed well-typed term is guaranteed to evaluate to a value of that type. In particular, any closed term of natural number type evaluates to a numeral.

5:40

E. CAVALLO AND R. HARPER

Vol. 17:4

**4.5. Building up inference rules.** With a value type system in hand, it remains to verify that the judgments are closed under the inference rules introduced in Sections 1 and 2. We go through the typing rules for Gel-types in detail. The rules for Bridge-types are simpler to verify, as the reduction rules are all “cubically stable”: they do not depend on the status of any interval term. (In comparison, $\text{gel}_r(M_0, M_1, P)$ may be a value or step depending on whether $r$ is a variable or constant.) The rules for extent do involve unstable transitions, but require no ideas that are not present in the proofs for Gel-types; in particular, the hcom reduction for Gel involves extent-like variable capture. The reader may see [CH19b] for complete proofs of these results.

We rely on the following five lemmas to work with the candidate judgments. These are rephrasings of Lemmas A.2, A.3, and A.5 from [CH18]; each follows straightforwardly by unfolding definitions.

**Lemma 4.16** (Coherent type value). *Suppose $A, A'$ are terms. If for every $\Psi' \Vdash \Psi \in \Psi$, either $\tau(\Psi', A\psi, A'\psi, \alpha_\psi)$ or $\Psi' \Vdash A\psi \sim A'\psi \downarrow \alpha\psi \in \tau$, then $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$.*

**Lemma 4.17** (Coherent term value). *Suppose $\Psi \Vdash A \downarrow \alpha \in \tau$ and $M, M'$ are terms. If for every $\Psi' \Vdash \Psi \in \Psi$, either $\alpha_\psi(M\psi, M'\psi)$ or $\Psi' \Vdash M\psi \sim M'\psi \in \alpha\psi$, then $\Psi \Vdash M \sim M' \in \alpha$.*

**Lemma 4.18** (Coherent type expansion). *Suppose $A$ is a term and $(A_\psi)_{\Psi' \Vdash \psi \in \Psi}$ is a family of terms such that $A\psi \longmapsto^* A_\psi$ and $\Psi' \Vdash A_\psi \sim A_{\text{id}}\psi \downarrow \alpha\psi \in \tau$ for all $\Psi' \Vdash \psi \in \Psi$. Then $\Psi \Vdash A \sim A_{\text{id}} \downarrow \alpha \in \tau$.*

**Lemma 4.19** (Coherent term expansion). *Suppose $\Psi \Vdash A \downarrow \alpha \in \tau$, $M$ is a term, and $(M_\psi)_{\Psi' \Vdash \psi \in \Psi}$ is a family of terms such that $M\psi \longmapsto^* M_\psi$ and $\Psi' \Vdash M_\psi \sim M_{\text{id}}\psi \in \alpha\psi$ for all $\Psi' \Vdash \psi \in \Psi$. Then $\Psi' \Vdash M \sim M_{\text{id}} \in \alpha$.*

**Lemma 4.20** (Evaluation). *Suppose $\Psi \Vdash M = M' \in A$. Then $M \Downarrow V$ and $M' \Downarrow V'$ with $\Psi \Vdash M = V = V' = M' \in A$.*

We now check the rules for Gel-types as presented in Figure 6. We prove that each rule holds when the ambient context is an arbitrary interval context $\Psi$. The open rules—for an arbitrary context $\Gamma$—then follow mechanically, as the open type and term judgments are defined by their closed instantiations.

It is convenient to prove the boundary reduction equations for a type or term former *before* the general introduction rule; for example, we show first $\text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R) = A_\varepsilon$ pretype and then $\text{Gel}_r(A_0, A_1, a_0.a_1.R)$ pretype.

**Rule 4.21** (GEL-FORM-$\partial$). *For any $\varepsilon \in \{0, 1\}$, $\Psi \Vdash A_\varepsilon$ pretype, and terms $A_{1-\varepsilon}$, $R$, we have $\Psi \Vdash \text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R) = A_\varepsilon$ pretype.*

*Proof.* By Lemma 4.18, taking $A_\psi := A_\varepsilon\psi$: we have $\text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R)\psi \longmapsto A_\psi$ and $\Psi' \Vdash A_\varepsilon\psi \sim A_\varepsilon\psi \downarrow [A_\varepsilon]\psi \in \tau$ for all $\psi$. $\square$

As described above, this “closed” principle implies the open rule. Given $\Gamma$ ctx and $\Gamma \gg A_\varepsilon$ pretype, we have by definition that $\Psi \Vdash A_\varepsilon\gamma = A_\varepsilon\gamma'$ pretype for all $\Psi \Vdash \gamma = \gamma' \in \Gamma$. Thus $\Psi \Vdash \text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R)\gamma = A_\varepsilon\gamma'$ pretype for all such instantiations by the rule just proven, which means that $\Gamma \gg \text{Gel}_\varepsilon(A_0, A_1, a_0.a_1.R) = A_\varepsilon$ pretype.

The following lemma gets us part of the way to the formation rule. We also need that the relation for Gel-types is value-coherent and supports the Kan operations; we will return to these later.

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:41

Lemma 4.22 (Gel formation candidate). If we have $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon} = A_{\varepsilon}'$ pretype for $\varepsilon \in \{0,1\}$, and $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ pretype, then $\Psi \Vdash \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R) \sim \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R') \downarrow \gamma \in \tau$ with $\gamma$ defined on $\Psi' \Vdash \psi \in \Psi$ as follows.

$$\gamma_{\psi} := \left\{ \begin{array}{ll} \{(\operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P), \operatorname{gel}_{\boldsymbol{x}}(M_0', M_1', P')) \mid \\ \forall \varepsilon. (\Psi' \backslash \boldsymbol{x} \Vdash M_{\varepsilon} = M_{\varepsilon}' \in A\psi) \\ \wedge \Psi' \backslash \boldsymbol{x} \Vdash P = P' \in R[M_0, M_1/a_0, a_1]\}, & \text{if } \boldsymbol{r}\psi = \boldsymbol{x} \\ \alpha^{\varepsilon}\psi, & \text{if } \boldsymbol{r}\psi = \boldsymbol{\varepsilon} \in \{\mathbf{0}, \mathbf{1}\} \end{array} \right.$$

Proof. By Lemma 4.16. For every $\Psi' \Vdash \psi \in \Psi$, either $\boldsymbol{r}\psi = \boldsymbol{x}$ for some $\boldsymbol{x}$, in which case we have $\tau(\Psi', \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)\psi, \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R')\psi, \gamma_{\psi})$ by definition of the value type system, or $\boldsymbol{r}\psi = \boldsymbol{\varepsilon} \in \{\mathbf{0}, \mathbf{1}\}$, in which case we have $\operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)\psi \sim A_{\varepsilon}\psi \sim A_{\varepsilon}'\psi \sim \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R')\psi$ by way of GEL-FORM-$\partial$.

Rule 4.23 (GEL-INTRO-$\partial$). For any $\varepsilon \in \{0,1\}$, $\Psi \Vdash A_{\varepsilon}$ pretype, and $\Psi \Vdash M_{\varepsilon} \in A_{\varepsilon}$, and terms $M_{1-\varepsilon}$, $P$, we have $\Psi \Vdash \operatorname{gel}_{\boldsymbol{\varepsilon}}(M_0, M_1, P) = M_{\varepsilon} \in A_{\varepsilon}$.

Proof. By Lemma 4.19, taking $M_{\psi} := M_{\varepsilon}\psi$.

Rule 4.24 (GEL-INTRO). If we have $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash M_{\varepsilon} = M_{\varepsilon}' \in A_{\varepsilon}$ for $\varepsilon \in \{0,1\}$, $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ pretype, and $\Psi \backslash \boldsymbol{r} \Vdash P = P' \in R[M_0, M_1/a_0, a_1]$, then $\Psi \Vdash \operatorname{gel}_{\boldsymbol{r}}(M_0, M_1, P) \sim \operatorname{gel}_{\boldsymbol{r}}(M_0', M_1', P') \in \gamma$ for $\gamma$ as in the statement of Lemma 4.22.

Proof. By Lemma 4.17, proceeding as in Lemma 4.22 by cases on $\boldsymbol{r}\psi$ for each $\psi$: we use the definition of $\gamma$ when $\boldsymbol{r}\psi$ is a variable and GEL-INTRO-$\partial$ when $\boldsymbol{r}\psi$ is a constant.

Lemma 4.25 (Gel formation pretype). If we have $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon} = A_{\varepsilon}'$ pretype for $\varepsilon \in \{0,1\}$, and $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ pretype, then $\Psi \Vdash \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R) = \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0, a_1, R')$ pretype.

Proof. A combination of Lemma 4.22 and GEL-INTRO, the latter of which shows that the relation for Gel is value-coherent.

Rule 4.26 (GEL-$\beta$). If $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash P \in R[M_0, M_1/a_0, a_1]$, then

$$\Psi \Vdash \operatorname{ungel}(\boldsymbol{x} \cdot \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P)) = P \in R[M_0, M_1/a_0, a_1].$$

Proof. By Lemma 4.19: we have $\operatorname{ungel}(\boldsymbol{x} \cdot \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P))\psi \longmapsto P\psi$ for all $\psi$.

Rule 4.27 (GEL-ELIM). If $\Psi \Vdash A_{\varepsilon}$ pretype for $\varepsilon \in \{0,1\}$, $\Psi, a_0 : A_0, a_1 : A_1 \gg R$ pretype, and $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q = Q' \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, R)$, then we have the following.

$$\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = \operatorname{ungel}(\boldsymbol{x}, Q') \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$$

Proof. For every $\Psi' \Vdash \psi \in \Psi$, we have by Lemma 4.20 that $Q\psi \Downarrow Q_{\psi}$ and $Q'\psi \Downarrow Q'_{\psi}$ for some $\Psi', \boldsymbol{x} : \mathbf{I} \Vdash Q\psi = Q_{\psi} = Q'_{\psi} = Q'\psi \in \operatorname{Gel}_{\boldsymbol{x}}(A_0\psi, A_1\psi, a_0, a_1, R\psi)$. By definition of the relation for Gel-types, we have $Q_{\psi} = \operatorname{gel}_{\boldsymbol{x}}(M_{0,\psi}, M_{1,\psi}, P_{\psi})$ and $Q'_{\psi} = \operatorname{gel}_{\boldsymbol{x}}(M'_{0,\psi}, M'_{1,\psi}, P'_{\psi})$ for some terms such that $\Psi' \Vdash P_{\psi} = P'_{\psi} \in R\psi[M_{0,\psi}, M_{1,\psi}/a_0, a_1]$. By GEL-INTRO-$\partial$ and functionality of $R$, it follows that also $\Psi' \Vdash P_{\psi} = P'_{\psi} \in R\psi[Q[\mathbf{0}/\boldsymbol{x}]\psi, Q[\mathbf{1}/\boldsymbol{x}]\psi/a_0, a_1]$. We have $\operatorname{ungel}(\boldsymbol{x}, Q)\psi \longmapsto^* P_{\psi}$ for each $\psi$, thus $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = P_{\mathrm{id}} \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$ by Lemma 4.19; likewise, $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q') = P'_{\mathrm{id}} \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$. We conclude by transitivity that $\Psi \Vdash \operatorname{ungel}(\boldsymbol{x}, Q) = P_{\mathrm{id}} = P'_{\mathrm{id}} = \operatorname{ungel}(\boldsymbol{x}, Q') \in R[Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}]/a_0, a_1]$.

Rule 4.28 (GEL-$\eta$). If $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon}$ pretype for $\varepsilon \in \{0,1\}$, $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R$ pretype, and $\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash Q \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0, a_1, R)$, then we have the following.

$$\Psi \Vdash Q[\boldsymbol{r}/\boldsymbol{x}] = \operatorname{gel}_{\boldsymbol{r}}(Q[\mathbf{0}/\boldsymbol{x}], Q[\mathbf{1}/\boldsymbol{x}], \operatorname{ungel}(\boldsymbol{x}, Q)) \in \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0, a_1, R)$$

5:42

E. CAVALLO AND R. HARPER

Vol. 17:4

Proof. By Lemma 4.20, we have $\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash Q = V \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$ for some $Q \Downarrow V$. By definition of the relation for Gel-types, we know $V = \operatorname{gel}_{\boldsymbol{x}}(M_0, M_1, P)$ for some suitably-typed $M_0$, $M_1$, and $P$. By GEL-INTRO-$\partial$, GEL-$\beta$, and GEL-INTRO, we conclude the following.

$$\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I} \Vdash V = \operatorname{gel}_{\boldsymbol{x}}(V[\mathbf{0}/\boldsymbol{x}], V[\mathbf{1}/\boldsymbol{x}], \operatorname{ungel}(\boldsymbol{x}.V)) \in \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$$

We can replace $V$ with $Q$ everywhere in this equation using GEL-INTRO and GEL-ELIM. Substituting $\boldsymbol{r}$ for $\boldsymbol{x}$ then gives the result.

It only remains to show that Gel-types support the Kan operations. We will go through the proof for hcom; the proof for coe has an identical structure. We will begin by proving reduction lemmas for the constant and variable cases.

Lemma 4.29. Let $\Psi \Vdash A_{\varepsilon}$ type for some $\varepsilon \in \{0, 1\}$. If $\Psi \Vdash r, s \in \mathbb{I}, n \in \mathbb{N}$, $\Psi \Vdash \xi_i$ constraint, $\Psi \Vdash Q \in A_{\varepsilon}$, $\Psi, y : \mathbb{I} \Vdash Q_i = Q_j \in A_{\varepsilon}$ for all $i, j < n$, and $\Psi \Vdash Q = Q_i[r/y] \in A_{\varepsilon}$ for all $i < n$, then $\Psi \Vdash \operatorname{hcom}_{\operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) \in A_{\varepsilon}$.

Proof. By Lemma 4.19: every substitution instance of the left-hand side steps to the corresponding instance of the right-hand side, which is well-typed because $A_{\varepsilon}$ is Kan.

Lemma 4.30. Let $\Psi \Vdash A_{\varepsilon}$ type for $\varepsilon \in \{0, 1\}$ and $\Psi, a_0 : A_0, a_1 : A_1 \gg R$ type. Abbreviate $G := \operatorname{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$. For any $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash r, s \in \mathbb{I}, n \in \mathbb{N}$, $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash \xi_i$ constraint, $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q \in G$, $\Psi, \boldsymbol{x} : \mathbf{I}, y : \mathbb{I} \Vdash Q_i = Q_j \in G$ for all $i, j < n$, and $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash Q = Q_i[r/y] \in G$ for all $i < n$, we have $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash \operatorname{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P) \in G$ where $M_{\varepsilon,-}$ and $P$ are defined as follows.

$$\begin{array}{l} M_{\varepsilon,y} := \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow y}(Q[\varepsilon/\boldsymbol{x}]; \overline{\xi_i[\varepsilon/\boldsymbol{x}] \hookrightarrow y.Q_i[\varepsilon/\boldsymbol{x}])} \\ P := \operatorname{com}_{y.R[M_{0,y}, M_{1,y}/a_0,a_1]}^{r \rightsquigarrow s}(\operatorname{ungel}(\boldsymbol{x}.Q); \overline{\forall \boldsymbol{x}.\xi_i \hookrightarrow y.\operatorname{ungel}(\boldsymbol{x}.Q_i)}) \end{array}$$

Proof. By Lemma 4.19. For every $\Psi' \Vdash \psi \in (\Psi, \boldsymbol{x} : \mathbf{I})$, we have two cases.

$\triangleright \boldsymbol{x}\psi = \varepsilon \in \{\mathbf{0}, \mathbf{1}\}$. Then $\operatorname{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi \longmapsto \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi$, and we have $\Psi' \Vdash \operatorname{hcom}_{A_{\varepsilon}}^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi = \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P)\psi \in G\psi$ by GEL-INTRO-$\partial$ and the assumption that $A$ is Kan.

$\triangleright \boldsymbol{x}\psi$ is a variable. Then $\operatorname{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i})\psi \longmapsto \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P)\psi$, and we have $\Psi' \Vdash \operatorname{gel}_{\boldsymbol{x}}(M_{0,s}, M_{1,s}, P)\psi \in G\psi$ by GEL-INTRO-$\partial$, GEL-ELIM, and the assumption that the $A_{\varepsilon}$ and $R$ are Kan. We use here that the capture of $\boldsymbol{x}$ by ungel in the definition of the reduct commutes with $\psi$, which relies on the affinity of bridge interval substitution.

Rule 4.31 (GEL-FORM). If $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$, $\Psi \backslash \boldsymbol{r} \Vdash A_{\varepsilon} = A_{\varepsilon}'$ type for each $\varepsilon \in \{0, 1\}$, and $\Psi \backslash \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R'$ type, then we have the following.

$$\Psi \Vdash \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0.a_1.R) = \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0.a_1.R') \text{ type}$$

Proof. We must check that Gel supports the Kan operations. We give the proof for hcom. Abbreviate $G := \operatorname{Gel}_{\boldsymbol{r}}(A_0, A_1, a_0.a_1.R)$ and $G' := \operatorname{Gel}_{\boldsymbol{r}}(A_0', A_1', a_0.a_1.R')$. Let $\Psi' \Vdash \psi \in \Psi$, $\Psi' \Vdash r, s \in \mathbb{I}$, $n \in \mathbb{N}$, $\Psi' \Vdash \xi_i$ constraint for all $i < n$, $\Psi' \Vdash Q = Q' \in G\psi$, $\Psi', y : \mathbb{I} \Vdash Q_i = Q_j' \in G\psi$ for all $i, j < n$, and $\Psi' \Vdash Q = Q_i[r/y] \in G\psi$ for all $i < n$ be given. If $\boldsymbol{r}\psi$ is a constant, then we simply apply GEL-FORM-$\partial$ and Lemma 4.29 everywhere.

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:43

\(\Gamma \mathrm{ctx}\) \(\Gamma\) is a context  
\(\Gamma \vdash r:\mathbf{I}\) \(r\) is a bridge interval term in context \(\Gamma\)  
\(\Gamma \vdash A\) type \(A\) is a type in context \(\Gamma\)  
\(\Gamma \vdash M:A\) \(M\) is a term of type \(A\) in context \(\Gamma\)  
\(\Gamma \vdash \delta :\Delta\) \(\delta\) is a substitution for context \(\Delta\) in context \(\Gamma\)

Figure 9: Judgments of formal parametric type theory

If \( r\psi \) is a variable \( x \), then \( \Psi' \Vdash \mathsf{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = \mathsf{gel}_x(M_{0,s}, M_{1,s}, P) \in G\psi \) and \( \Psi' \Vdash \mathsf{hcom}_{G'}^{r \rightsquigarrow s}(Q'; \overline{\xi_i \hookrightarrow y.Q_i'}) = \mathsf{gel}_x(M_{0,s}', M_{1,s}', P') \in G'\psi \) as defined in Lemma 4.30. Then we have the following.

\(\triangleright \Psi^{\prime}\Vdash \mathsf{hcom}_{G}^{r\rightsquigarrow s}(Q;\overline{\xi_{i}\hookrightarrow y.Q_{i}}) = \mathsf{hcom}_{G^{\prime}}^{r\rightsquigarrow s}(Q^{\prime};\overline{\xi_{i}\hookrightarrow y.Q_{i}^{\prime}})\in G\psi\) follows from the fact that \(\Psi^{\prime}\Vdash \mathsf{gel}_{\pmb{x}}(M_{0,s},M_{1,s},P) = \mathsf{gel}_{\pmb{x}}(M_{0,s}^{\prime},M_{1,s}^{\prime},P^{\prime})\in G\psi\), which holds by GEL-INTRO-\(\partial\), GEL-ELIM, and the assumption that the \(A_{\varepsilon}\) and \(R\) are Kan.
\(\triangleright \Psi^{\prime}\Vdash \mathsf{hcom}_{G}^{r\rightsquigarrow s}(Q;\overline{\xi_{i}\hookrightarrow y.Q_{i}}) = Q_{i}[s / y]\in G\psi\) if \(\xi_{i}\) is true follows by cases on \(\xi_{i}\). If \(\pmb{x}\) does not occur in \(\xi_{i}\), then \(\forall \pmb {x}.\xi_{i} = \xi_{i}\). It follows by the boundary equations for \(\mathsf{hcom}\) in \(A_{\varepsilon}\) and \(R\) that the composite is equal to \(\mathsf{gel}_{\pmb{x}}(Q_{i}[\mathbf{0} / \pmb {x}],Q_{i}[\mathbf{1} / \pmb {x}],\mathsf{ungel}(\pmb {x}.Q_{i}))[s / y]\), and this term is equal to \(Q_{i}[s / y]\) by GEL- \(\eta\). If \(\pmb{x}\) does occur in \(\xi_{i}\), then the constraint must be either \(\pmb {x} = \mathbf{0}\) or \(\pmb {x} = \mathbf{1}\), in which case it is contradictory that \(\xi_{i}\) is true.
\(\triangleright \Psi^{\prime}\Vdash \mathsf{hcom}_{G}^{r\rightsquigarrow r}(Q;\overline{\xi_{i}\hookrightarrow y.Q_{i}}) = Q\in G\psi\) holds by the corresponding Kan equations for the \(A_{\varepsilon}\) and \(R\) together with GEL-INTRO and GEL-\(\eta\).

## 5. FORMAL PARAMETRIC TYPE THEORY

While we have anchored our type theory in a computational interpretation, we would also like to use parametric cubical type theory as a logic for reasoning about other settings. For this reason, we abstract a formal type theory from the collection of inference rules we have developed in the preceding sections. The proofs of those inference rules, as given for Gel-types in Section 4.5, establish that the computational interpretation is one model of the formalism. In Section 6, we see that the theory can also be interpreted in cartesian-affine bicubical sets.

We focus on parametric type theory here; for the cubical ingredients, we defer to prior work [Ang19, Appendix B]. In the pure parametric case, the theory is defined by the judgments shown in Figure 9 and their equality counterparts. We take care to ensure our definition constitutes a generalized algebraic theory (GAT) [Car86], using for example explicit substitutions. \( ^{2} \)  Ensuring admissibility of substitution—that every term is equal to one containing no explicit substitutions—requires some innovation. In particular, the theory presented in [BCM15] does not satisfy admissibility of substitution, a consequence of the way rules using interval terms (such as bridge elimination) are formulated. Rectifying this issue motivates the introduction of the context restriction operator  \( -\backslash- \)  we have already encountered. We present a formulation of context restriction as an explicit context former characterized as a left adjoint to extension by an interval variable.

\( ^{2} \) We will nevertheless permit ourselves a certain amount of routine syntactic sugar; for one, we will not fully annotate terms.

5:44

E. CAVALLO AND R. HARPER

Vol. 17:4

We defer serious metatheoretic analysis of the formalism we present, such as normalization or decidability of equality, to future work.

5.1. The bridge interval. The main novelty is our treatment of bridge interval restriction. Rather than relying on an operation $-\backslash r$ on raw contexts—which would destroy the algebraic character of the theory—we treat context restriction as a primitive context-forming operation.

$$\begin{array}{c c c c} \text {CTX - NIL} & \text {CTX - TERM} & \text {CTX - I} & \text {CTX - RESTRICT} \\ \hline \cdot \text {ctx} & \frac {\Gamma \vdash A \text {type}}{\Gamma . A \text {ctx}} & \frac {\Gamma \text {ctx}}{\Gamma . I \text {ctx}} & \frac {\Gamma \text {ctx} \quad \Gamma \vdash r : I}{\Gamma . \backslash r \text {ctx}} \end{array}$$

As is usual for ordinary terms, interval terms include variables and are closed under (explicit) substitutions. We defer the matter of the constants 0 and 1 for the moment.

$$\frac {\mathbf {I} \text {-VAR}}{\Gamma . \mathbf {I} \vdash \mathbf {q} _ {\mathbf {I}} : \mathbf {I}} \quad \frac {\Delta \vdash r : \mathbf {I} \quad \Gamma \vdash \delta : \Delta}{\Gamma \vdash r [ \delta ] : \mathbf {I}}$$

Restriction is characterized by its relationship with extension by a bridge interval variable. Given an interval term $\Gamma \vdash r: \mathbf{I}$ and substitution $\Gamma \backslash r \vdash \delta: \Delta$, we may build a substitution $\Gamma \vdash \delta.r: \Delta.\mathbf{I}$. Conversely, given $\Gamma \vdash \delta: \Delta.\mathbf{I}$, we may project a term $\Gamma \vdash \mathbf{q}_{\mathbf{I}}[\delta]: \mathbf{I}$ and substitution $\Gamma \backslash \mathbf{q}_{\mathbf{I}}[\delta] \vdash \delta^{\dagger}: \Delta$. This sets up an adjunction between the category of contexts $\Gamma$ and its slice over the bridge interval, which is to say the category of substitutions $\Gamma \vdash r: \mathbf{I}$, with $-\backslash-$ as the left adjoint and $-\cdot.\mathbf{I}$ as the right.

$$\begin{array}{c c} \text {SUBST - I} & \text {SUBST - RESTRICT} \\ \frac {\Gamma \vdash r : \mathbf {I} \quad \Gamma . \backslash r \vdash \delta : \Delta}{\Gamma \vdash \delta . r : \Delta . \mathbf {I}} & \frac {\Gamma \vdash \delta : \Delta . \mathbf {I}}{\Gamma . \backslash q _ {\mathbf {I}} [ \delta ] \vdash \delta^ {\dagger} : \Delta} \end{array}$$

$$\begin{array}{c c} \text {SUBST - EQ - I} & \text {SUBST - EQ - RESTRICT} \\ \Delta \text {ctx} \quad \Gamma \vdash \delta : \Delta . \mathbf {I} & \frac {\Gamma \vdash r : \mathbf {I} \quad \Gamma . \backslash r \vdash \delta : \Delta}{\Gamma . \backslash r \vdash \delta = (\delta . r) ^ {\dagger} : \Delta} \\ \hline \Gamma \vdash \delta = \delta^ {\dagger}. q _ {\mathbf {I}} [ \delta ]: \Delta . \mathbf {I} & \end{array}$$

These rules induce a functorial action by interval extension, $\Gamma.\mathbf{I}\vdash\delta^{\mathbf{I}}:=(\delta\circ\mathrm{id}^{\dagger}).\mathbf{q}_{\mathbf{I}}:\Delta.\mathbf{I}$, as well as an action by restriction, $\Gamma.\backslash r[\delta]\vdash\delta\backslash r:=(\mathrm{id}.r\circ\delta)^{\dagger}:\Delta.\backslash r$. Using these, we additionally require that the correspondence is natural.

$$\begin{array}{c c} \text {SUBST - I - NATURAL} & \text {SUBST - RESTRICT - NATURAL} \\ \frac {\Gamma \vdash \delta : \Delta \quad \Xi \vdash r : \mathbf {I} \quad \Xi . \backslash r \vdash \gamma : \Gamma}{\Xi \vdash (\delta \circ \gamma) . r = \delta^ {\mathbf {I}} \circ (\gamma . r) : \Delta . \mathbf {I}} & \frac {\Gamma \vdash \delta : \Delta . \mathbf {I} \quad \Xi \vdash \gamma : \Gamma}{\Xi . \backslash q _ {\mathbf {I}} [ \delta \circ \gamma ] \vdash (\delta \circ \gamma) ^ {\dagger} = \delta^ {\dagger} \circ (\gamma \backslash q _ {\mathbf {I}} [ \delta ]) : \Delta} \end{array}$$

The structural laws and constants are then given as generating substitutions (together with the expected equations between them, such as $p_{I} \circ \varepsilon_{I} = id$ and naturality laws).

$$\begin{array}{c c} \text {SUBST - FACE} & \text {SUBST - DEGEN} \\ \varepsilon \in \{0, 1 \} & \frac {\Gamma . \mathbf {I} \vdash p _ {\mathbf {I}} : \Gamma}{\Gamma . \mathbf {I} \vdash p _ {\mathbf {I}} : \Gamma} \end{array} \quad \begin{array}{c c} \text {SUBST - EXCHANGE} \\ \frac {\Gamma \text {ctx}}{\Gamma . \mathbf {I} . \mathbf {I} \vdash \mathrm{ex} _ {\mathbf {I}} : \Gamma . \mathbf {I} . \mathbf {I}} \end{array}$$

Note that the existence of a substitution $\Gamma \vdash \varepsilon_{\mathbf{I}}: \Gamma.\mathbf{I}$ is slightly stronger than the existence of a term $\Gamma \vdash \overline{\varepsilon_{\mathbf{I}}}: \mathbf{I}$; the latter would only give us a substitution $\Gamma \vdash \mathrm{id}.\overline{\varepsilon_{\mathbf{I}}}: \Gamma.\backslash q_{\mathbf{I}}[\overline{\varepsilon_{\mathbf{I}}}].\mathbf{I}$.

We note that the rules for I we have presented so far are consistent with an interpretation by a structural interval, in which case context restriction would be the identity function. It

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:45

is not until we introduce rules for extent and Gel that the structural interval ceases to model the theory.

On the cubical side, we can treat path interval variables in the same way as term variables. However, we also need the principle that bridge and path variables can be exchanged.

$$\begin{array}{c c c} \text {SUBST-}\mathbb {I} & & \text {SUBST-\text {II}} \\ \Gamma \vdash \delta : \Delta & \Delta \vdash r: \mathbb {I} & \text {SUBST-PROJ-}\mathbb {I} \\ \hline \Gamma \vdash \delta . r: \Delta . \mathbb {I} & & \overline {{\Gamma . \mathbb {I} \vdash p _ {\mathbb {I}} : \Gamma}} \\ & & \overline {{\Gamma . \mathbf {I} . \mathbb {I} \vdash \mathrm {ex} _ {\mathbb {I} \mathbf {I}} : \Gamma . \mathbb {I} . \mathbf {I}}} \end{array}$$

The substitution $\mathrm{ex}_{\mathbb{I}}$ serves to invert the substitution $\Gamma.\mathbb{I}.\mathbf{I} \vdash \mathsf{p}_{\mathbb{I}}^{\mathbf{I}}.\mathsf{q}_{\mathbb{I}}[\mathsf{p}_{\mathbb{I}}] : \Gamma.\mathbf{I}.\mathbb{I}$, and expresses that path terms are always apart from bridge terms. Besides this principle, the cubical and parametric sides of the theory only interact via the allowance for bridge constraints in hcom terms and the inclusion of rules for computing Kan operations in Bridge- and Gel-types, which we may formulate following the operational semantics shown in Figure 2.

5.2. Type and term formers. With the judgmental infrastructure in place, it is fairly straightforward to translate the computational type formers introduced in Section 2 to the formal setting. We describe the rules for Bridge-types here; rules for Gel-types and extent may be found in Appendix A. The formation, introduction, and elimination rules for Bridge-types follow exactly the pattern of Figure 4.

$$\frac {\Gamma . \mathbf {I} \vdash A \text {type} \quad \Gamma \vdash M _ {0} : A [ \mathbf {0} _ {\mathbf {I}} ] \quad \Gamma \vdash M _ {1} : A [ \mathbf {1} _ {\mathbf {I}} ]}{\Gamma \vdash \operatorname{Bridge} _ {A} (M _ {0} , M _ {1}) \text {type}} \quad \frac {\Gamma . \mathbf {I} \vdash A \text {type} \quad \Gamma . \mathbf {I} \vdash M : A}{\Gamma \vdash \lambda^ {\mathbf {I}} . M : \operatorname{Bridge} _ {A} (M [ \mathbf {0} _ {\mathbf {I}} ] , M [ \mathbf {1} _ {\mathbf {I}} ])}$$

$$\frac {\Gamma . \backslash \boldsymbol {r} \vdash M _ {0} : A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \begin{array}{c} \Gamma \vdash \boldsymbol {r} : \mathbf {I} \qquad \Gamma . \backslash \boldsymbol {r} . \mathbf {I} \vdash A \text {type} \\ \Gamma . \backslash \boldsymbol {r} \vdash M _ {1} : A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma . \backslash \boldsymbol {r} \vdash P : \operatorname{Bridge} _ {A} (M _ {0} , M _ {1}) \end{array}}{\Gamma \vdash P @ \boldsymbol {r} : A [ \mathrm{id} . \boldsymbol {r} ]}$$

It is the elimination rule—along with the rules for extent and Gel-types—that necessitates the introduction of the interval restriction operator. In [BCM15], bridge elimination is instead described by a rule of the following kind.

$$\frac {\Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0} : A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \Gamma \vdash M _ {1} : A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma \vdash P : \operatorname{Bridge} _ {A} (M _ {0} , M _ {1})}{\Gamma . \mathbf {I} \vdash \operatorname{app} (P) : A}$$

This form of elimination is inter-derivable with our own: one may set $P@\boldsymbol{r} := \mathsf{app}(P)[\mathsf{id}.\boldsymbol{r}]$ or conversely $\mathsf{app}(P) := P[\mathsf{id}^{\dagger}]@\mathsf{q}_{\mathbf{I}}$. However, the [BCM15] rule produces a formalism in which substitution is not admissible, that is, a theory in which not every term is equal to one containing no use of the $-[-]$ operator. Given $P$ as in the rule and a substitution $\Delta \vdash \gamma : \Gamma.\mathbf{I}$, there is no way to reduce the term $\mathsf{app}(P)[\gamma]$ unless it happens that $\Delta = \Delta'.\mathbf{I}$ and $\gamma = \gamma'^{\mathbf{I}}$ for some $\Delta' \vdash \gamma' : \Gamma$, in which case $\mathsf{app}(P)[\gamma] = \mathsf{app}(P[\gamma'])$. By contrast, we may reduce a term $(P@\boldsymbol{r})[\gamma]$ using the functorial action of restriction, as prescribed by the rule below.

5:46

E. CAVALLO AND R. HARPER

Vol. 17:4

$$\begin{array}{c} \Delta \vdash \gamma : \Gamma \qquad \Gamma \vdash \boldsymbol{r} : \mathbf{I} \qquad \Gamma . \backslash \boldsymbol{r}. \mathbf{I} \vdash A \text { type } \\ \Gamma . \backslash \boldsymbol{r} \vdash M_{0} : A[\mathbf{0}_{\mathbf{I}}] \qquad \Gamma . \backslash \boldsymbol{r} \vdash M_{1} : A[\mathbf{1}_{\mathbf{I}}] \qquad \Gamma . \backslash \boldsymbol{r} \vdash P : \operatorname{Bridge}_{A}(M_{0}, M_{1}) \\ \hline \Gamma \vdash (P @ \boldsymbol{r})[\gamma] = P[\gamma \backslash \boldsymbol{r}] @ \boldsymbol{r}[\gamma] : A[\operatorname{id}. \boldsymbol{r}][\gamma] \end{array}$$

Finally, the $\beta$-, $\eta$-, and boundary rules for Bridge-types can be expressed as follows. Note that these rules respectively make use of the unit $\Gamma \vdash \operatorname{id}. \boldsymbol{r} : \Gamma . \backslash \boldsymbol{r}. \mathbf{I}$ and counit $\Gamma . \mathbf{I} . \backslash \mathbf{q}_{\mathbf{I}} \vdash \operatorname{id}^{\dagger} : \Gamma$ of the adjunction between $-\backslash-$ and $-\mathbf{I}$.

$$\begin{array}{c} \frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \qquad \Gamma . \backslash \boldsymbol{r}. \mathbf{I} \vdash A \text { type } \qquad \Gamma . \backslash \boldsymbol{r}. \mathbf{I} \vdash M : A}{\Gamma \vdash \lambda . M @ \boldsymbol{r} = M[\operatorname{id}. \boldsymbol{r}] : A[\operatorname{id}. \boldsymbol{r}]} \\ \frac{\Gamma . \mathbf{I} \vdash A \text { type } \qquad \Gamma \vdash M_{0} : A[\mathbf{0}_{\mathbf{I}}] \qquad \Gamma \vdash M_{1} : A[\mathbf{1}_{\mathbf{I}}] \qquad \Gamma \vdash P : \operatorname{Bridge}_{A}(M_{0}, M_{1})}{\Gamma \vdash P = \lambda^{\mathbf{I}} . P[\operatorname{id}^{\dagger}] @ \mathbf{q}_{\mathbf{I}} : \operatorname{Bridge}_{A}(M_{0}, M_{1})} \\ \frac{\Gamma . \mathbf{I} \vdash A \text { type } \qquad \Gamma \vdash M_{0} : A[\mathbf{0}_{\mathbf{I}}] \qquad \Gamma \vdash M_{1} : A[\mathbf{1}_{\mathbf{I}}] \qquad \Gamma \vdash P : \operatorname{Bridge}_{A}(M_{0}, M_{1})}{\Gamma \vdash P[\varepsilon_{\mathbf{I}}^{\dagger}] @ \mathbf{q}_{\mathbf{I}}[\varepsilon_{\mathbf{I}}] = M_{\varepsilon} : A[\varepsilon_{\mathbf{I}}]} \end{array}$$

## 6. A SEMANTICS IN BICUBICAL SETS

We now describe a second semantics for the formal type theory of Section 5 in a presheaf category of bicubical sets, adapting Angiuli et al.'s presheaf semantics for cubical type theory [ABC$^{+}$19].

**Definition 6.1.** We define the cartesian-affine bicube category $\square_{ca}$ to have as objects interval contexts $\Psi$ and as morphisms interval substitutions $\Psi' \Vdash \psi \in \Psi$, as specified in Definition 4.1.

**Remark 6.2.** The category $\square_{ca}$ is equivalent to a product $\square_{c} \times \square_{a}$ of two cube categories, the cartesian cube category $\square_{c}$ consisting of path interval contexts and the affine cube category $\square_{a}$ consisting of bridge interval contexts.

The presheaf category $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ is the category of contravariant functors from $\square_{ca}$ to $\mathbf{Set}$, meaning that its objects are families of sets indexed by interval contexts with transition maps for each interval substitution. This parallels the situation in the computational interpretation, where types are given meaning by families of relations indexed by such contexts. We use $\mathcal{L}$ (hiragana 'yo') to denote the Yoneda embedding $\square_{ca} \to [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$.

**Remark 6.3.** Bernardy, Coquand, and Moulin instead interpret their type theory in a category of refined presheaves on $\square_{a}$ [BCM15]. Roughly, a refined presheaf is a $\Psi$-indexed family where for each $\Psi \in \square_{a}$, we have not merely a set but a $\Psi$-set, a family of sets indexed by sub-contexts $\Psi' \subseteq \Psi$. This refinement is used to validate the equivalents in their setting of equations $\operatorname{Bridge}_{\boldsymbol{x}. \operatorname{Gel}_{\boldsymbol{x}}(A_{0}, A_{1}, R)} = R$ and $C = \lambda^{\mathbf{I}} \boldsymbol{x}. \operatorname{Gel}_{\boldsymbol{x}}(A_{0}, A_{1}, \operatorname{Bridge}_{\boldsymbol{x}, C @ \boldsymbol{x}})$, as mentioned in Section 2.4. When we build parametric type theory on a cubical base, we no longer need these equations to hold exactly, as we can prove they hold up to a path using univalence (Theorem 2.4).

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:47

6.1. Judgments and cubical type theory. We recall the presheaf interpretation of the judgments of cubical type theory developed in [CCHM15, ABC$^{+}$19], which draw on earlier presheaf interpretations of dependent type theory [Hof97].

Definition 6.4. A semantic context is a presheaf $G \in [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$; a semantic substitution between contexts $G', G$ is a presheaf morphism (i.e., natural transformation) $\alpha : G' \to G$.

Definition 6.5. A semantic pretype over a context $G \in [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ is a presheaf $T \in [(\int G)^{\mathrm{op}}, \mathbf{Set}]$ over the category of elements $\int G$, which is to say the following data:

$\triangleright$ for every $\Psi \in \square_{ca}$ and $g \in G(\Psi)$, a set $T(\Psi, g)$;

$\triangleright$ for every $\Psi' \Vdash \psi \in \Psi$ and $g \in G(\Psi)$, a map $T(\psi) : T(\Psi', G(\psi)(g)) \to T(\Psi, g)$.

Definition 6.6. A semantic element $t$ of a pretype $T$ in context $G$ is a family of elements $t(\Psi, g) \in T(\Psi, g)$ indexed by $\Psi \in \square_{ca}$ and $g \in G(\Psi)$ such that $T(\psi)(t(\Psi, g)) = t(\Psi', G(\psi)(g))$ for every $\Psi' \Vdash \psi \in \Psi$ and $g \in G(\Psi)$.

A semantic type is then a pretype equipped with coercion and homogeneous composition operators implementing the rules shown in Figure 2. We give the definition of coercion operator here and leave it to the reader to infer the corresponding notion of homogeneous composition operator.

Definition 6.7. Given a pretype $T$ over $G$, a coercion operator $c$ for $T$ is a family of elements as follows: for every $\Psi \in \square_{ca}$, interval terms $\Psi \Vdash r, s \in \mathbb{I}$, element $g \in G(\Psi, x : \mathbb{I})$, and $t \in T(\Psi, G(\mathsf{id}_{\Psi}, r/x)(g))$, we require an element $c(\Psi, r, s, g, t) \in T(\Psi, G(\mathsf{id}_{\Psi}, s/x)(g))$. We ask that these satisfy the following properties.

$\triangleright$ $T(\psi)(c(\Psi, r, s, g, t)) = c(\Psi', r\psi, s\psi, G(\psi)(g), T(\psi)(t))$ for every $\Psi' \Vdash \psi \in \Psi$.

$\triangleright$ $c(\Psi, r, r, g, t) = t$.

Definition 6.8. A semantic type $(T, c, h)$ over $G$ is a triple consisting of a semantic pretype $T$ over $G$ with coercion and homogeneous composition operators $c$ and $h$.

Remark 6.9. A semantic substitution $\alpha : G' \to G$ acts on types and terms over $G$ by reindexing; we write $\alpha^*T$ and $\alpha^*t$ for the action on types and terms respectively.

Definition 6.10. A semantic interval term over $G$ is a presheaf morphism $r : G \to \mathcal{K}(x : \mathbb{I})$. A semantic constraint is a morphism $r : G \to \Omega_{dec}$ where $\Omega_{dec}$ is the decidable subobject classifier in $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$, which classifies monomorphisms $m : H' \mapsto H$ in $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ such that $m(\Psi)$ has decidable image for all $\Psi$.

Angiuli et al.'s [ABC$^{+}$19, Theorem 1] shows that cartesian cubical type theory can be interpreted using these semantic judgments in any presheaf category whose base category contains a suitably structured interval object.

Proposition 6.11. $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ interprets cubical type theory with an infinite hierarchy of univalent universes, each closed under dependent function and product types, Path-types, and V-types.

Proof. By Angiuli et al.'s Theorem 1 [ABC$^{+}$19]. The formulation of cartesian cubical type theory given there is slightly different from our own (for example taking com rather than coe and hcom as primitive), but not in any essential way.

We note that the statement of the theorem in [ABC$^{+}$19] requires that the base category is closed under finite products, which is not the case for $\square_{ca}$: the cartesian product of the contexts $(\boldsymbol{x} : \mathbf{I})$ and $(\boldsymbol{y} : \mathbf{I})$ does not exist. However, the proof only actually requires that the product functor $- \times (x : \mathbb{I})$ exists, and this is indeed the case in $\square_{ca}$.

5:48

E. CAVALLO AND R. HARPER

Vol. 17:4

6.2. Bridge interval and restriction. We now turn to the parametric side of the theory. As with the path interval, we interpret bridge interval terms in a context $G$ as morphisms $\boldsymbol{r}: G \to \mathfrak{X}(\boldsymbol{x} : \mathbf{I})$. To interpret bridge interval context extension and restriction, we observe that we have an adjunction between $\square_{ca}$ and its slice category over the affine interval $(\boldsymbol{x} : \mathbf{I})$. Note that elements of this slice category consist of contexts $\Psi$ paired with bridge interval terms $\Psi \Vdash \boldsymbol{r} \in \mathbf{I}$.

![img-7.jpeg](img-7.jpeg)

The right adjoint $Ext$ sends a context $\Psi$ to the extended context $(\Psi, \boldsymbol{x} : \mathbf{I})$ with its canonical projection $\Psi, \boldsymbol{x} : \mathbf{I} \Vdash \boldsymbol{x} \in \mathbf{I}$. The left adjoint is interval restriction: it sends a pair $(\Psi, \boldsymbol{r})$ to the restricted context $\Psi \setminus \boldsymbol{r}$ defined here as in Section 2.1.

$$\Psi \setminus \varepsilon := \Psi \quad \text{if } \varepsilon \in \{\mathbf{0}, \mathbf{1}\}$$

$$(\Psi, y : \mathbb{I}) \setminus \boldsymbol{x} := \Psi \setminus \boldsymbol{x}, y : \mathbb{I}$$

$$(\Psi, \boldsymbol{y} : \mathbf{I}) \setminus \boldsymbol{x} := \begin{cases} \Psi & \text{if } \boldsymbol{x} = \boldsymbol{y} \\ \Psi \setminus \boldsymbol{x}, \boldsymbol{y} : \mathbf{I} & \text{if } \boldsymbol{x} \neq \boldsymbol{y} \end{cases}$$

This adjunction in the base category induces, among other things, the following pair of adjoint functors between the presheaf category and its slice. We implicitly use the equivalence $[(\square_{ca}/\Psi)^{\mathrm{op}}, \mathbf{Set}] \simeq [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]/\mathfrak{X}\Psi$ between presheaves on slice categories and slices over representables.

![img-8.jpeg](img-8.jpeg)

Here $Res^*$ is precomposition with $Res$, while $Res_!$ and $Ext_!$ are each defined by left Kan extension. Both $Ext_!$ and $Res^*$ are left adjoint to $Ext^*$, so are necessarily isomorphic. As for $Res_!$, it may be explicitly calculated as the following coend.

$$Res_!(G, \boldsymbol{r})(\Psi) = \int^{\Psi' \Vdash \boldsymbol{s} : \mathbf{I}} \{g \in G(\Psi') \mid \boldsymbol{r}(\Psi')(g) = \boldsymbol{s}\} \times \{\psi \mid \Psi \Vdash \psi \in \Psi' \setminus \boldsymbol{s}\}$$

For our purposes, however, it is only necessary to know that the extensions $Res_!$ and $Ext_!$ apply the base functors on representables, that is, that $Res_!(\mathfrak{X}\Psi, \boldsymbol{r}) \cong \mathfrak{X}(\Psi \setminus \boldsymbol{r})$ and $Ext_!(\mathfrak{X}\Psi) \cong \mathfrak{X}(\boldsymbol{x}/\boldsymbol{x}) : \mathfrak{X}(\Psi, \boldsymbol{x} : \mathbf{I}) \to \mathfrak{X}(\boldsymbol{x} : \mathbf{I})$; this is a general property of Kan extensions. Henceforth we write $G \otimes \mathbf{I}$ for the object part of $Ext_!G$ and $var(G) : G \otimes \mathbf{I} \to \mathfrak{X}(\boldsymbol{x} : \mathbf{I})$ for the associated projection.

We use $Res_!$ to interpret the type-theoretic restriction of a context by an interval term, likewise $-\otimes \mathbf{I}$ to interpret extension by an interval variable and $var(G)$ for the variable rule. The isomorphism between hom-sets given by the adjunction $Res_! \dashv Ext_!$ implements the substitution constructors SUBST-I and SUBST-RESTRICT. The structural rules for the bridge interval derive from natural transformations in the base category via the action of $(-)_!$; for example, the endpoint transformation $\varepsilon : Id \to \pi \circ Ext$ defined by

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:49

$\Psi \Vdash \varepsilon(\Psi) := (\mathrm{id}_{\Psi}, \varepsilon / \boldsymbol{x}) \in (\Psi, \boldsymbol{x} : \mathbf{I})$ induces a corresponding transformation $\varepsilon_{!} : Id \to (-\otimes \mathbf{I})$ in the presheaf category interpreting the endpoint substitution SUBST-FACE.

6.3. Type and term formers. To interpret the rules for forming types and terms—Bridge-types, Gel-types, and extent—it is useful to observe that the semantic judgments, like the computational ones in Section 4, are determined by their instantiations at interval contexts (i.e., representables). For example, a semantic type $T$ in context $G$ is determined by the types $g^{*}T$ for $g : \not\cong\Psi \to G$: recalling that the Yoneda lemma identifies morphisms $g : \not\cong\Psi \to G$ with elements $g \in G(\Psi)$, we have as we have $T(\Psi, g) = (g^{*}T)(\Psi, \mathrm{id}_{\Psi})$. Conversely, if we have a family of types $T_{g}$ over $\not\cong\Psi$ for every $g : \not\cong\Psi \to G$ such that $(\not\cong\psi)^{*}T_{g} = T_{g \circ \not\cong\psi}$ for all $\Psi' \Vdash \psi \in \Psi$, then this determines a type $T$ over $G$: take $T(\Psi, g) := T_{g}(\Psi, \mathrm{id}_{\Psi})$. A similar principle applies to terms.

The upshot is that we may verify that rules hold in an arbitrary context by showing they hold (naturally) in any interval context, as we did for the computational interpretation in Section 4.5. In the restricted case we may take advantage of the characterizations $Res_{!}(\not\cong\Psi, \boldsymbol{r}) \cong \not\cong(\Psi \backslash \boldsymbol{r})$ and $Ext_{!}(\not\cong\Psi) \cong \not\cong(\boldsymbol{x}/\boldsymbol{x}) : \not\cong(\Psi, \boldsymbol{x} : \mathbf{I}) \to \not\cong(\boldsymbol{x} : \mathbf{I})$, saving us from formal reasoning with the general Kan extension.

**Theorem 6.12.** $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ is closed under Bridge-pretypes.

*Proof.* Per the argument above, we narrow our attention without loss of generality to the cases where the ambient context is representable.

$\triangleright$ *Formation.*

Let a semantic pretype $T$ in context $\not\cong\Psi \otimes \mathbf{I} \cong \not\cong(\Psi, \boldsymbol{x} : \mathbf{I})$ be given together with endpoint elements $t_{0}$ of $\not\cong(\mathbf{0}/\boldsymbol{x})^{*}T$ and $t_{1}$ of $\not\cong(\mathbf{1}/\boldsymbol{x})^{*}T$. We define a semantic pretype $Bridge(T, t_{0}, t_{1})$ over $\not\cong\Psi$ as follows.

$$Bridge(T, t_{0}, t_{1})(\Psi', \psi) := \{a \in T((\Psi', \boldsymbol{x} : \mathbf{I}), (\psi, \boldsymbol{x}/\boldsymbol{x})) \mid \forall \varepsilon. T(\varepsilon/\boldsymbol{x})(a) = t_{\varepsilon}(\Psi', \psi)\}$$

That is, an element of $Bridge(T, t_{0}, t_{1})$ in context $\Psi'$ is an element of $T$ in context $(\Psi', \boldsymbol{x} : \mathbf{I})$ with the requested endpoints. The action of $Bridge(T, t_{0}, t_{1})$ on substitutions is likewise defined from the action of $T$ in the natural way.

$\triangleright$ *Introduction.*

Similarly, given a semantic element $t$ of $T$ such that $\not\cong(\mathbf{1}/\boldsymbol{x})^{*}t = t_{0}$ and $\not\cong(\mathbf{1}/\boldsymbol{x})^{*}t = t_{1}$, we have an abstracted element $lam^{\mathbf{I}}(t)$ of $Bridge(T, t_{0}, t_{1})$ defined as follows.

$$lam^{\mathbf{I}}(t)(\Psi, g) := t((\Psi, \boldsymbol{x} : \mathbf{I}), (\psi, \boldsymbol{x}/\boldsymbol{x}))$$

$\triangleright$ *Elimination.*

To interpret application, we assume now that we have some $\boldsymbol{r} : \not\cong\Psi \to \not\cong(\Psi, \boldsymbol{x} : \mathbf{I})$ and that the pretype $T$ lies in context $Res_{!}(\not\cong\Psi, \boldsymbol{r}) \otimes \mathbf{I} \cong \not\cong(\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I})$. Given an element $u$ of $Bridge(T, t_{0}, t_{1})$,

$$app^{\mathbf{I}}(u)(\Psi', \psi) := T(\boldsymbol{r}\psi/\boldsymbol{x})(u(\Psi' \backslash \boldsymbol{r}\psi, \psi \backslash \boldsymbol{r}))$$

Here $\Psi' \backslash \boldsymbol{r}\psi \Vdash \psi \backslash \boldsymbol{r} \in \Psi \backslash \boldsymbol{r}$ is the functorial action of restriction on $\psi$. By definition of the bridge type, the term $u(\Psi' \backslash \boldsymbol{r}\psi, \psi \backslash \boldsymbol{r})$ is an element of $T((\Psi' \backslash \boldsymbol{r}\psi, \boldsymbol{x} : \mathbf{I}), (\psi \backslash \boldsymbol{r}, \boldsymbol{x}/\boldsymbol{x}))$; applying $T(\boldsymbol{r}\psi/\boldsymbol{x})$ thus gives an element of $T(\Psi', \psi)$.

We leave it to the reader to check that these definitions are natural and that the $\beta$-, $\eta$-, and boundary rules are satisfied. $\square$

5:50

E. CAVALLO AND R. HARPER

Vol. 17:4

We may show that the model interprets Bridge-types—that is, that Bridge-pretypes can be equipped with Kan operations—following the computational definition of coe and hcom in Figure 8; we leave this to the reader. Alternatively, one may follow the definition of composition for Path-types in the BCH model [BCH13, §7.2].

**Theorem 6.13.** $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ *interprets Gel-pretypes*.

*Proof.* We prove the formation rule, following the computational definition in Section 4.4. It is straightforward to see how the introduction and elimination rules follow.

Let a interval term $\boldsymbol{r}: \mathfrak{L}\Psi \to \mathfrak{L}(\boldsymbol{x} : \mathbf{I})$, semantic pretypes $T_0, T_1$ in context $Res!(\mathfrak{L}\Psi, \boldsymbol{r}) \cong \mathfrak{L}(\Psi \backslash \boldsymbol{r})$, and a semantic pretype $R$ in context $\mathfrak{L}(\Psi \backslash \boldsymbol{r}).(T_0 \times T_1)$—here $-.-$ is the semantic equivalent of context extension—be given. We define the Gel-pretype as follows.

$$Gel_{\boldsymbol{r}}(T_0, T_1, R)(\Psi', \psi) := T_{\varepsilon}(\Psi', \psi \backslash \boldsymbol{r}) \quad \text{if } \boldsymbol{r}\psi = \varepsilon$$

$$Gel_{\boldsymbol{r}}(T_0, T_1, R)(\Psi', \psi) := \left\{ (a_0, a_1, t) \left| \begin{array}{l} a_{\varepsilon} \in T_{\varepsilon}(\Psi' \backslash \boldsymbol{r}\psi, \psi \backslash \boldsymbol{r}) \\ t \in (\mathfrak{L}(\psi \backslash \boldsymbol{r}).(a_0 \times a_1))^* R(\Psi' \backslash \boldsymbol{r}\psi, \mathrm{id}) \end{array} \right. \right\} \quad \text{otherwise}$$

As with Bridge-types, the Kan operations may be implemented following the computational definition given in Figure 8. We note that homogeneous composition relies on the closure of the decidable subobject classifier $\Omega_{dec}$ under $\forall \boldsymbol{x}.-$; this parallels the use of $\forall x.-$ for composition in G-, Glue-, or V-types in [BCH13, CCHM15, ABC$^+$19]. As Bridge-types resemble BCH Path-types, so do Gel-types resemble BCH G-types. Coercion for Gel is, however, much simpler than for its cubical equivalents, because the “direction” of a coercion is always a path variable and therefore orthogonal to the direction $\boldsymbol{r}$ of $\mathrm{Gel}_{\boldsymbol{r}}(A, B, R)$: one may coerce “across” a V-type, but not across a Gel-type.

We finish by sketching the interpretation of extent. Suppose we are given dimension term $\boldsymbol{r}: \mathfrak{L}\Psi \to \mathfrak{L}(\boldsymbol{x} : \mathbf{I})$, type $T$ in context $\mathfrak{L}(\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I})$, and element $t$ of $\mathfrak{L}(\boldsymbol{r}/\boldsymbol{x})^* T$, together with clause data for the endpoint and variable cases. For any $\Psi'$ and $\Psi' \Vdash \psi \in \Psi$, we have $t(\Psi', \psi) \in T(\Psi', (\psi, \boldsymbol{r}\psi/\boldsymbol{x}))$; we proceed by inspecting the status of $\boldsymbol{r}\psi$. If $\boldsymbol{r}\psi$ is an endpoint, then we have $t(\Psi', \psi) \in T(\Psi', (\psi, \boldsymbol{r}\psi/\boldsymbol{x})) = (\mathfrak{L}(\varepsilon/\boldsymbol{x})^* T)(\Psi', \psi)$ and may pass this term to the appropriate endpoint clause. If $\boldsymbol{r}\psi$ is a variable, then we employ the substitution $\Psi' \backslash \boldsymbol{r}\psi, \boldsymbol{y} : \mathbf{I} \Vdash \rho \in \Psi'$ that renames $\boldsymbol{r}\psi$ to a fresh variable $\boldsymbol{y}$. We have $T(\rho)(t(\Psi', \psi)) \in T((\Psi' \backslash \boldsymbol{r}\psi, \boldsymbol{y} : \mathbf{I}), (\psi \backslash \boldsymbol{r}, \boldsymbol{y}/\boldsymbol{x}))$, which per the proof of Theorem 6.12 is exactly a bridge at $T$. We may then supply this bridge to the variable clause of extent.

## 7. RELATED AND FUTURE WORK

**7.1. Related work.** Mechanically, our parametric cubical type theory is not much more than the union of Angiuli *et al.*’s cartesian cubical type theory [AFH18, ABC$^+$19, Ang19] and Bernardy, Coquand, and Moulin’s parametric type theory [BCM15]. As mentioned in Sections 2.4 and 6, we do drop some equations required for Gel-types in the BCM type theory which are not necessary in the cubical setting and complicate model constructions. Accordingly, our proof of relativity is novel. The formulation of context restriction in formalism is also novel, though inspired by Cheney’s work on nominal type theory [Che12], and resolves the issue with admissibility of substitution present in the BCM theory. Finally, Bernardy *et al.* present unary rather than binary parametricity, but from a conceptual perspective this is only a cosmetic difference, a matter of how many constants are included in

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:51

|  This paper | [BCM15] | [Mou16]  |
| --- | --- | --- |
|  \( Bridge_{x.A}(a_0, a_1) \) | \( A \ni_x a \) | \( (\forall x.A) \ni a \)  |
|  \( \lambda^I x.a \) | \( a \cdot x \) | \( (\langle x \rangle a)! \)  |
|  \( p@x \) | \( (a, x p) \) | \( (\langle a, x p \rangle) \)  |
|  \( extent_x(-; a_0.t_0, a_1.t_1, a_0.a_1.\overline{a}.u) \) | \( \langle \lambda a.t, x \lambda a.\lambda \overline{a}.u \rangle \) | \( (\langle \lambda a.t, x \lambda a.\lambda \overline{a}.u \rangle) \)  |
|  \( Gel_x(A_0, A_1, a_0.a_1.R) \) | \( (a : A) \times_x R \) | \( A \bowtie_x R \)  |
|  \( gel_x(a_0, a_1, c) \) | \( (a, x c) \) | \( (\langle a, x p \rangle) \)  |
|  \( ungel(x.a) \) | \( a \cdot x \) | \( (\langle x \rangle a)! \)  |

Figure 10: Translation dictionary for internal parametricity

the bridge interval. \( ^{3} \)  As our notation is quite different from that of Bernardy et al., we provide a comparison in Figure 10. Note that the mapping is not one-to-one because of the additional equations imposed in their theory. We also include notations from Moulin's thesis [Mou16]. In that work, the notion of a function  \( (i:\mathbb{I})\to A \)  without a fixed endpoint (called a "ray") is included separately from bridge types, and term formers that are primitive in [BCM15] are often implemented as combinations of terms relating first interval dependency to rays and then rays to bridges. In particular,  \( A\bowtie_{x}R \)  is syntactic sugar for a term  \( (A,\Psi_{A}R)\circledast x \) , while  \( (f,xh) \)  is sugar for  \( (f,\Phi_{f}h)\circledast x \) ; as a result, the equivalents of Gel and extent are sometimes called  \( \Psi- \)  and  \( \Phi \) -operators respectively in the literature.

A second approach to internal parametricity has been proposed by Nuyts, Vezzosi, and Devriese [NVD17]. Their system resembles our own in that it is based on bridges and paths, each of which is represented by a kind of map from an interval. Whereas our bridge and path structures are more-or-less orthogonal to each other, Nuyts et al. use a modality to connect the two. Terms are checked under different modalities depending on whether they are used in type or element positions, capturing the phase separation between type and element-level computation that is often identified as a consequence of parametricity. We see the two approaches of Bernardy et al. and Nuyts et al. as internalizing different perspectives on parametricity: the former internalizes the relational interpretation, while the latter internalizes this phase separation.

Nuyts et al. also distinguish between continuous and parametric function types: the former preserve paths and bridges, while the latter take bridges to paths. By contrast, we consider the former to already be “parametric”—as we have seen, one can prove parametricity theorems in our setting using only this property. However, the stronger condition does obviate the need to identify the class of bridge-discrete types as a replacement for the identity extension lemma. For example, any parametric function  \( U \rightarrow A \)  in their setting is constant, without any assumptions on A (cf. Lemma 3.18), because it takes the bridges in U to paths. Also notable is that their path and bridge intervals both behave structurally, whereas we use an affine interval for bridges. Given the other divergences from Bernardy et al.’s approach, it is difficult to say how the issues we raise with using structural variables for parametricity affect their system, if at all; it seems that they are ameliorated by the stronger condition on parametric functions. One notable limitation is that iterated parametricity is impossible, that is, the results produced by parametricity are not subject to further parametricity theorems.

\( ^{3} \) We conjecture that binary internal parametricity is more powerful than unary parametricity, but that ternary parametricity and so on provide no additional strength, because we can iterate binary parametricity to mimic  \( 2^{n} \) -ary parametricity for any n.

5:52

E. CAVALLO AND R. HARPER

Vol. 17:4

This is addressed in a successor system [ND18], which introduces an infinite hierarchy of bridge-like relationships associated with universe level and is capable of capturing iterated parametricity as well as other modal forms of hypothesis such as irrelevant hypotheses.

Nuyts's thesis [Nuy20] provides a more systematic analysis of the different univalence-like type formers used in cubical and parametric type theories—V, Glue, G, Gel—as derivable from a transpension type former, characterized as the right adjoint to the interval function type former (i : I) → −. This type former corresponds in our setting to the operator Gel_x(T, T, −); Nuyts derives Gel from this special case in combination with quantification over the boundary of x.

Tabareau, Tanter, and Sozeau [TTS18] develop a theory of univalent parametricity in the Calculus of (Inductive) Constructions. This system defines a kind of relation across which results can be transported, much as we transport results across isomorphisms using univalence, but develops a logical relation incorporating ideas from parametricity in order to improve the usability properties of the transport function. Although univalence and parametricity are both involved, therefore, the objectives are largely orthogonal to our own.

Riehl and Shulman's directed type theory [RS17] is a theory in the same mold as our own: it has two layers of higher structure, one which is used to express equality and one which is used for general relations. In their case, the goal is to identify those types whose “bridge” structure has the structure of an (∞, 1)-category, then use the theory as a language for synthetic higher category theory. Where our semantics is based on a product of cube categories, they use a product of simplex categories. Interestingly, their bisimplicial semantics fails to support a universe whose bridges are relations, for reasons that evoke our comparison of V- and Gel-types in Section 2.4 [Rie18]. However, the theory does support a universe of covariant discrete fibrations in which bridges correspond to functions (“directed univalence”). More recently, Weaver and Licata [WL20] have developed a cubical (and constructive) variation on this theory, based on the product of two structural cube categories. Like Riehl and Shulman’s theory, this theory supports a universe satisfying directed univalence, but we suspect it too fails to support a relativistic universe.

Our work fits into traditions of both proof-relevant equality and proof-relevant parametricity. The former is, of course, a primary focus of the field of homotopy type theory. Proof-relevant and higher-dimensional variations on parametricity have been developed by Atkey et al. [AGJ14], Ghani et al. [GJF+15], and Sojakova and Johann [SJ18]. More generally, Benton, Hofmann, and Nigam [BHN14] use a proof-relevant logical relation to study abstract effects, and proof-relevant logical families have recently been deployed as tools for proving metatheorems for dependent type theories [Shu15, Coq18].

7.2. Future work. Our exploration in Section 3 shows that internal parametricity can be effectively employed to prove difficult theorems involving higher inductive types. However, this only means that these results can be obtained in internally parametric type theory; we would also like to know they are true in non-parametric type theory. We believe a fruitful approach would be to combine parametric and non-parametric type theories into a single, modal theory containing a mode for parametric results and a mode for non-pointwise results. In particular, the presheaf categories [□^op_c, Set] and [□^op_{ca}, Set], which interpret cubical and parametric cubical type theory respectively, can be related by axiomatic cohesion, which has been previously been used in the design of modal type theories [SS12, Shu18].

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:53

The formalism we develop in Section 5 must be supported by metatheoretic results such as normalization in order to be truly utile. We have implemented an experimental type-checker for (non-cubical) parametric type theory, **ptt**, based on *normalization by evaluation*; in theory, this implementation implicitly contains a proof of normalization for the Section 5 formalism. However, we have not attempted to extract such a proof, nor have we verified the algorithm's correctness. The current **ptt** theory is also somewhat weaker than that of Section 5: we found it more convenient to give the Gel type a positive eliminator rather than a projection with $\eta$-principle. The $\eta$-expansion rule we have used in this paper applies only to terms that can be put in the form $Q[r/x]$, a condition that is to our knowledge expensive and painful (though we believe possible) to check.

#### ACKNOWLEDGMENTS

We thank Carlo Angiuli, Steve Awodey, Daniel Gratzer, Kuen-Bang Hou (Favonia), Dan Licata, Anders Mörtberg, Emily Riehl, Christian Sattler, Michael Shulman, Jonathan Sterling, and Andrew Swan for many helpful discussions.

5:54

E. CAVALLO AND R. HARPER

Vol. 17:4

## APPENDIX A. FORMAL PARAMETRIC TYPE THEORY

Rules for pushing substitutions through type and term formers are omitted.

### A.1. Contexts.

\[
\begin{array}{c c c c} \text {CTX - NIL} & \text {CTX - TERM} & \text {CTX - I} & \text {CTX - RESTRICT} \\ \hline \cdot \text {ctx} & \frac {\Gamma \vdash A \text {type}}{\Gamma . A \text {ctx}} & \frac {\Gamma \text {ctx}}{\Gamma . I \text {ctx}} & \frac {\Gamma \text {ctx} \quad \Gamma \vdash r : I}{\Gamma . \backslash r \text {ctx}} \end{array}
\]

### A.2. Interval terms.

\[
\frac {\mathbf {I} \text {-VAR}}{\Gamma . \mathbf {I} \vdash \mathbf {q} _ {\mathbf {I}} : \mathbf {I}} \quad \begin{array}{c} \mathbf {I} \text {-SUBST} \\ \Delta \vdash r: \mathbf {I} \qquad \Gamma \vdash \delta : \Delta \\ \hline \Gamma \vdash r [ \delta ]: \mathbf {I} \end{array}
\]

### A.3. Interval term equality.

\[
\begin{array}{c c} \text {I - SUBST - ID} & \text {I - SUBST - CONC} \\ \Gamma \vdash r: \mathbf {I} & \Delta_ {0} \vdash r: \mathbf {I} \quad \Delta_ {1} \vdash \delta_ {0}: \Delta_ {0} \quad \Gamma \vdash \delta_ {1}: \Delta_ {1} \\ \hline \Gamma \vdash r [ \mathrm{id} ] = r: \mathbf {I} & \Gamma \vdash r [ \delta_ {0} \circ \delta_ {1} ] = r [ \delta_ {0} ] [ \delta_ {1} ]: \mathbf {I} \end{array}
\]

\[
\begin{array}{c} \text {I - SUBST - TERM} \\ \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r \vdash \delta : \Delta \\ \hline \Gamma \vdash q _ {\mathbf {I}} [ \delta . r ] = r: \mathbf {I} \end{array}
\]

### A.4. Substitutions.

\[
\begin{array}{c c c} \text {SUBST - NIL} & \text {SUBST - ID} & \text {SUBST - CONC} \\ \hline \Gamma \vdash !: \cdot & \overline {{\Gamma \vdash \mathrm{id} : \Gamma}} & \frac {\Delta_ {1} \vdash \delta_ {0} : \Delta_ {0} \qquad \Gamma \vdash \delta_ {1} : \Delta_ {1}}{\Gamma \vdash \delta_ {0} \circ \delta_ {1} : \Delta_ {0}} \\ \hline \end{array} \qquad \begin{array}{c c c} \text {SUBST - TERM} \\ \frac {\Gamma \vdash \delta : \Delta \qquad \Gamma \vdash M : A [ \delta ]}{\Gamma \vdash \delta . M : \Delta . A} \end{array}
\]

\[
\begin{array}{c c c c} \text {SUBST - PROJ} & \text {SUBST - I} & \text {SUBST - RESTRICT} & \text {SUBST - FACE} \\ \frac {\Gamma \vdash A \text {type}}{\Gamma . A \vdash p : \Gamma} & \frac {\Gamma \vdash r : \mathbf {I} \qquad \Gamma . \backslash r \vdash \delta : \Delta}{\Gamma \vdash \delta . r : \Delta . \mathbf {I}} & \frac {\Gamma \vdash \delta : \Delta . \mathbf {I}}{\Gamma . \backslash q _ {\mathbf {I}} [ \delta ] \vdash \delta^ {\dagger} : \Delta} & \frac {\varepsilon \in \{0 , 1 \}}{\Gamma \vdash \varepsilon_ {\mathbf {I}} : \Gamma . \mathbf {I}} \end{array}
\]

\[
\begin{array}{c c} \text {SUBST - DEGEN} & \text {SUBST - EXCHANGE} \\ \hline \Gamma . \mathbf {I} \vdash p _ {\mathbf {I}}: \Gamma & \frac {\Gamma \text {ctx}}{\Gamma . \mathbf {I} . \mathbf {I} \vdash \mathrm{ex} _ {\mathbf {I}} : \Gamma . \mathbf {I} . \mathbf {I}} \end{array}
\]

We introduce the following abbreviations for the functorial actions of the three forms of context extension.

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta . \mu \vdash A \text {type}}{\Gamma . A [ \delta ] \vdash \delta^ {\times} : = (\delta \circ p) . q : \Delta . A} \qquad \qquad \frac {\Gamma \vdash \delta : \Delta}{\Gamma . I \vdash \delta^ {I} : = (\delta \circ i d ^ {\dagger}) . q _ {I} : \Delta . I}
\]

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta \vdash r : \mathbf {I}}{\Gamma . \backslash r [ \delta ] \vdash \delta \backslash r : = (\mathrm{id} . r \circ \delta) ^ {\dagger} : \Delta . \backslash r}
\]

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:55

### A.5. Substitution equality.

SUBST-NIL-ETA

\[
\frac {\Gamma \vdash \delta : \cdot}{\Gamma \vdash \delta = ! : \cdot}
\]

SUBST-ID-CONC

\[
\overline {{\Gamma \vdash \mathrm{id} \circ \delta = \delta : \Delta}}
\]

SUBST-CONC-ID

\[
\overline {{\Gamma \vdash \delta \circ \mathrm{id} = \delta : \Delta}}
\]

SUBST-CONC-CONC

\[
\frac {\Delta_ {1} \vdash \delta_ {0} : \Delta_ {0} \qquad \Delta_ {2} \vdash \delta_ {1} : \Delta_ {1} \qquad \Gamma \vdash \delta_ {2} : \Delta_ {2}}{\Gamma \vdash (\delta_ {0} \circ \delta_ {1}) \circ \delta_ {2} = \delta_ {0} \circ (\delta_ {1} \circ \delta_ {2}) : \Delta_ {0}}
\]

SUBST-PROJ-TERM

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta \vdash A \text {type} \qquad \Gamma \vdash M : A}{\Gamma \vdash p \circ (\delta . M) = \delta : \Delta}
\]

SUBST-TERM-ETA

\[
\frac {\Delta \vdash A \text {type} \quad \Gamma \vdash \delta : \Delta . A}{\Gamma \vdash \delta = (\mathfrak {p} \circ \delta) . \mathfrak {q} [ \delta ] : \Delta . A}
\]

SUBST-EQ-I

\[
\frac {\Delta \text {ctx} \quad \Gamma \vdash \delta : \Delta . \mathbf {I}}{\Gamma \vdash \delta = \delta^ {\dagger} . \mathbf {q _ {I}} [ \delta ] : \Delta . \mathbf {I}}
\]

SUBST-EQ-RESTRICT

\[
\frac {\Gamma \vdash \boldsymbol {r} : \mathbf {I} \qquad \Gamma . \backslash \boldsymbol {r} \vdash \delta : \Delta}{\Gamma . \backslash \boldsymbol {r} \vdash \delta = (\delta . \boldsymbol {r}) ^ {\dagger} : \Delta}
\]

SUBST-I-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Xi \vdash \boldsymbol {r} : \mathbf {I} \qquad \Xi . \backslash \boldsymbol {r} \vdash \gamma : \Gamma}{\Xi \vdash (\delta \circ \gamma) . \boldsymbol {r} = \delta^ {\mathbf {I}} \circ (\gamma . \boldsymbol {r}) : \Delta . \mathbf {I}}
\]

SUBST-RESTRICT-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta . \mathbf {I} \qquad \Xi \vdash \gamma : \Gamma}{\Xi . \backslash \mathbf {q _ {I}} [ \delta \circ \gamma ] \vdash (\delta \circ \gamma) ^ {\dagger} = \delta^ {\dagger} \circ (\gamma \backslash \mathbf {q _ {I}} [ \delta ]) : \Delta}
\]

SUBST-FACE-NATURAL

\[
\frac {\varepsilon \in \{0 , 1 \} \qquad \Gamma \vdash \delta : \Delta}{\Gamma \vdash \delta^ {\mathbf {I}} \circ \varepsilon_ {\mathbf {I}} = \varepsilon_ {\mathbf {I}} \circ \delta : \Delta . \mathbf {I}}
\]

SUBST-DEGEN-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta}{\Gamma . \mathbf {I} \vdash \delta \circ p _ {\mathbf {I}} = p _ {\mathbf {I}} \circ \delta^ {\mathbf {I}} : \Delta}
\]

SUBST-EXCHANGE-NATURAL

\[
\frac {\Gamma \vdash \delta : \Delta}{\Gamma . \mathbf {I} . \mathbf {I} \vdash \delta^ {\mathbf {I I}} \circ \mathrm{ex} _ {\mathbf {I}} = \mathrm{ex} _ {\mathbf {I}} \circ \delta^ {\mathbf {I I}} : \Delta . \mathbf {I} . \mathbf {I}}
\]

SUBST-PROJ-FACE

\[
\frac {\varepsilon \in \{0 , 1 \}}{\Gamma \vdash p _ {\mathbf {I}} \circ \varepsilon_ {\mathbf {I}} = \mathrm{id} : \Gamma}
\]

SUBST-PROJ-EXCHANGE

\[
\overline {{\Gamma . \mathbf {I} . \mathbf {I} \vdash p _ {\mathbf {I}} \circ e x _ {\mathbf {I}} = p _ {\mathbf {I}} ^ {\mathbf {I}} : \Gamma . \mathbf {I}}}
\]

SUBST-EXCHANGE-EXCHANGE

\[
\overline {{\Gamma . \mathbf {I} . \mathbf {I} \vdash \mathrm{ex} _ {\mathbf {I}} \circ \mathrm{ex} _ {\mathbf {I}} = \mathrm{id} : \Gamma . \mathbf {I} . \mathbf {I}}}
\]

### A.6. Types.

TY-SUBST

\[
\frac {\Delta \vdash A \text {type} \qquad \Gamma \vdash \delta : \Delta}{\Gamma \vdash A [ \delta ] \text {type}}
\]

### A.7. Type equality.

TY-SUBST-ID

\[
\overline {{\Gamma \vdash A [ \mathrm{id} ] = A \text {type}}}
\]

TY-SUBST-CONC

\[
\frac {\Delta_ {0} \vdash A \text {type} \qquad \Delta_ {1} \vdash \delta_ {0} : \Delta_ {0} \qquad \Gamma \vdash \delta_ {1} : \Delta_ {1}}{\Gamma \vdash A [ \delta_ {0} \circ \delta_ {1} ] = A [ \delta_ {0} ] [ \delta_ {1} ] \text {type}}
\]

### A.8. Terms.

TM-VAR

\[
\frac {\Gamma \vdash A \text {type}}{\Gamma . A \vdash \mathfrak {q} : A [ \mathfrak {p} ]}
\]

TM-SUBST

\[
\frac {\Gamma \vdash \delta : \Delta \qquad \Delta \vdash M : A}{\Gamma \vdash M [ \delta ] : A [ \delta ]}
\]

5:56

E. CAVALLO AND R. HARPER

Vol. 17:4

### A.9. Term equality.

\[
\begin{array}{c c} \text {TM - SUBST - ID} & \text {TM - SUBST - CONC} \\ \Gamma \vdash M: A & \Delta_ {0} \vdash M: A \quad \Delta_ {1} \vdash \delta_ {0}: \Delta_ {0} \quad \Gamma \vdash \delta_ {1}: \Delta_ {1} \\ \hline \Gamma \vdash M [ \mathrm{id} ] = M: A & \Gamma \vdash M [ \delta_ {0} \circ \delta_ {1} ] = M [ \delta_ {0} ] [ \delta_ {1} ]: A [ \delta_ {0} ] [ \delta_ {1} ] \end{array}
\]

\[
\begin{array}{c} \text {TM - SUBST - TERM} \\ \Gamma \vdash \delta : \Delta \qquad \Delta \vdash A \text {type} \qquad \Gamma \vdash M: A [ \delta ] \\ \hline \Gamma \vdash \mathfrak {q} [ \delta . M ] = M: A [ \delta ] \end{array}
\]

### A.10. Bridge types.

\[
\begin{array}{c c} \text {TY - BRIDGE} & \text {TM - BLAM} \\ \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \Gamma \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] & \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma . \mathbf {I} \vdash M: A \\ \hline \Gamma \vdash \text {Bridge} _ {A} (M _ {0}, M _ {1}) \text {type} & \overline {{\Gamma \vdash \lambda^ {\mathbf {I}} . M : \text {Bridge} _ {A} (M [ \mathbf {0} _ {\mathbf {I}} ] , M [ \mathbf {1} _ {\mathbf {I}} ])}} \end{array}
\]

\[
\begin{array}{c} \text {TM - BAPP} \\ \Gamma . \backslash r \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \quad \begin{array}{c} \Gamma \vdash r: \mathbf {I} \quad \Gamma . \backslash r. \mathbf {I} \vdash A \text {type} \\ \Gamma . \backslash r \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] \quad \Gamma . \backslash r \vdash P: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \\ \hline \Gamma \vdash P @ r: A [ \mathrm{id}. r ] \end{array} \end{array}
\]

\[
\begin{array}{c} \text {TM - BAPP - BOUNDARY} \\ \hline \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \begin{array}{c} \varepsilon \in \{0, 1 \} \\ \Gamma \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma \vdash P: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \\ \hline \Gamma \vdash P [ \varepsilon_ {\mathbf {I}} ^ {\dagger} ] @ q _ {\mathbf {I}} [ \varepsilon_ {\mathbf {I}} ] = M _ {\varepsilon}: A [ \varepsilon_ {\mathbf {I}} ] \end{array} \end{array}
\]

\[
\begin{array}{c} \text {TM - BLAM - BETA} \\ \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r. \mathbf {I} \vdash A \text {type} \qquad \Gamma . \backslash r. \mathbf {I} \vdash M: A \\ \hline \Gamma \vdash \lambda . M @ r = M [ \mathrm{id}. r ]: A [ \mathrm{id}. r ] \end{array}
\]

\[
\begin{array}{c} \text {TM - BLAM - ETA} \\ \Gamma . \mathbf {I} \vdash A \text {type} \qquad \Gamma \vdash M _ {0}: A [ \mathbf {0} _ {\mathbf {I}} ] \qquad \Gamma \vdash M _ {1}: A [ \mathbf {1} _ {\mathbf {I}} ] \qquad \Gamma \vdash P: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \\ \hline \Gamma \vdash P = \lambda^ {\mathbf {I}}. P [ \mathrm{id} ^ {\dagger} ] @ \mathbf {q} _ {\mathbf {I}}: \operatorname{Bridge} _ {A} (M _ {0}, M _ {1}) \end{array}
\]

### A.11. Gel types.

\[
\begin{array}{c} \text {TY - GEL} \\ \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r \vdash A _ {0} \text {type} \qquad \Gamma . \backslash r \vdash A _ {1} \text {type} \qquad \Gamma . \backslash r. A _ {0}. A _ {1} [ p ] \vdash R \text {type} \\ \hline \Gamma \vdash \operatorname{Gel} _ {r} (A _ {0}, A _ {1}, R) \text {type} \end{array}
\]

\[
\begin{array}{c} \text {TY - GEL - BOUNDARY} \\ \varepsilon \in \{0, 1 \} \qquad \Gamma \vdash A _ {0} \text {type} \qquad \Gamma \vdash A _ {1} \text {type} \qquad \Gamma . A _ {0}. A _ {1} [ p ] \vdash R \text {type} \\ \hline \Gamma \vdash \operatorname{Gel} _ {\varepsilon} (A _ {0} [ \varepsilon_ {\mathbf {I}} ^ {\dagger} ], A _ {1} [ \varepsilon_ {\mathbf {I}} ^ {\dagger} ], R [ \varepsilon_ {\mathbf {I}} ^ {\dagger^ {\times \times}} ]) = A _ {\varepsilon} \text {type} \end{array}
\]

\[
\begin{array}{c} \text {TM - GEL} \\ \Gamma . \backslash r \vdash M _ {1}: A _ {1} \qquad \begin{array}{c} \Gamma \vdash r: \mathbf {I} \qquad \Gamma . \backslash r \vdash M _ {0}: A _ {0} \\ \Gamma . \backslash r. A _ {0}. A _ {1} [ p ] \vdash R \text {type} \qquad \Gamma . \backslash r \vdash P: R [ \mathrm{id}. M _ {0}. M _ {1} ] \\ \hline \Gamma \vdash \operatorname{gel} _ {r} (M _ {0}, M _ {1}, P): \operatorname{Gel} _ {r} (A _ {0}, A _ {1}, R) \end{array} \end{array}
\]

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:57

TM-GEL-BOUNDARY

$$\frac{\Gamma \vdash M_0 : A_0 \quad \Gamma \vdash M_1 : A_1 \quad \Gamma.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma \vdash P : R[\text{id.}M_0.M_1]}{\Gamma \vdash \text{gel}_\varepsilon(M_0[\varepsilon_\mathbf{I}^\dagger], M_1[\varepsilon_\mathbf{I}^\dagger], P[\varepsilon_\mathbf{I}^\dagger]) = M_\varepsilon : A_\varepsilon}$$

TM-UNGEL

$$\frac{\Gamma \vdash A_0 \text{ type}}{\Gamma \vdash A_1 \text{ type} \quad \Gamma.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma.\mathbf{I} \vdash Q : \text{Gel}_{\mathfrak{q}_\mathbf{I}}(A_0[\text{id}^\dagger], A_1[\text{id}^\dagger], R[\text{id}^{\dagger \times \times}])} \quad \Gamma \vdash \text{ungel}(Q) : R[\text{id.}Q[\mathbf{0}_\mathbf{I}].Q[\mathbf{1}_\mathbf{I}]]$$

TM-GEL-BETA

$$\frac{\Gamma \vdash M_0 : A_0 \quad \Gamma \vdash M_1 : A_1 \quad \Gamma.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma \vdash P : R[\text{id.}M_0.M_1]}{\Gamma \vdash \text{ungel}(\text{gel}_{\mathfrak{q}_\mathbf{I}}(M_0[\text{id}^\dagger], M_1[\text{id}^\dagger], P[\text{id}^\dagger])) = P : R[\text{id.}M_0.M_1]}$$

TM-GEL-ETA

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_0 \text{ type} \quad \Gamma.\backslash\boldsymbol{r} \vdash A_1 \text{ type}}{\Gamma.\backslash\boldsymbol{r}.A_0.A_1[\mathfrak{p}] \vdash R \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash Q : \text{Gel}_{\mathfrak{q}_\mathbf{I}}(A_0[\text{id}^\dagger], A_1[\text{id}^\dagger], R[\text{id}^{\dagger \times \times}])} \quad \Gamma \vdash Q[\text{id.}\boldsymbol{r}] = \text{gel}_\boldsymbol{r}(Q[\mathbf{0}_\mathbf{I}], Q[\mathbf{1}_\mathbf{I}], \text{ungel}(Q)) : \text{Gel}_\boldsymbol{r}(A_0, A_1, R)$$

### A.12. Extent.

TM-EXTENT

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash A \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I}.A \vdash B \text{ type}}{\Gamma \vdash M : A[\text{id.}\boldsymbol{r}] \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}] \vdash N_0 : B[\mathbf{0}_\mathbf{I}^\times] \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{1}_\mathbf{I}] \vdash N_1 : B[\mathbf{1}_\mathbf{I}^\times]} \quad \frac{\Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}].A[\mathbf{1}_\mathbf{I} \circ \mathfrak{p}].\text{Bridge}_{A[\mathfrak{p}^2]}(\mathfrak{q}[\mathfrak{p}], \mathfrak{q}) \vdash N : \text{Bridge}_{B[(\mathfrak{p}^3 \circ \text{id}^\dagger).\mathfrak{q}_\mathbf{I}.\mathfrak{q}[\text{id}^\dagger]@\mathfrak{q}_\mathbf{I}]}(N_0[\mathfrak{p}^2], N_1[\mathfrak{p}^\times \circ \mathfrak{p}])}{\Gamma \vdash \text{extent}_\boldsymbol{r}(M; N_0, N_1, N) : B[\text{id.}\boldsymbol{r}.M]}$$

TM-EXTENT-BOUNDARY

$$\frac{\varepsilon \in \{0, 1\} \quad \Gamma.\mathbf{I} \vdash A \text{ type}}{\Gamma.\mathbf{I}.A \vdash B \text{ type} \quad \Gamma \vdash M : A[\varepsilon_\mathbf{I}] \quad \Gamma.A[\mathbf{0}_\mathbf{I}] \vdash N_0 : B[\mathbf{0}_\mathbf{I}^\times] \quad \Gamma.A[\mathbf{1}_\mathbf{I}] \vdash N_1 : B[\mathbf{1}_\mathbf{I}^\times]} \quad \frac{\Gamma.A[\mathbf{0}_\mathbf{I}].A[\mathbf{1}_\mathbf{I} \circ \mathfrak{p}].\text{Bridge}_{A[\mathfrak{p}^2]}(\mathfrak{q}[\mathfrak{p}], \mathfrak{q}) \vdash N : \text{Bridge}_{B[(\mathfrak{p}^3 \circ \text{id}^\dagger).\mathfrak{q}_\mathbf{I}.\mathfrak{q}[\text{id}^\dagger]@\mathfrak{q}_\mathbf{I}]}(N_0[\mathfrak{p}^2], N_1[\mathfrak{p}^\times \circ \mathfrak{p}])}{\Gamma \vdash \text{extent}_{\mathfrak{q}_\mathbf{I}[\varepsilon_\mathbf{I}]}(M; N_0[\varepsilon_\mathbf{I}^{\dagger \times}], N_1[\text{id}^{\dagger \times}], N[\text{id}^{\dagger \times \times \times}]) = N_\varepsilon[\text{id.}M] : B[\varepsilon_\mathbf{I}.M]}$$

TM-EXTENT-BETA

$$\frac{\Gamma \vdash \boldsymbol{r} : \mathbf{I} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash A \text{ type} \quad \Gamma.\backslash\boldsymbol{r}.\mathbf{I}.A \vdash B \text{ type}}{\Gamma.\backslash\boldsymbol{r}.\mathbf{I} \vdash M : A \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}] \vdash N_0 : B[\mathbf{0}_\mathbf{I}^\times] \quad \Gamma.\backslash\boldsymbol{r}.A[\mathbf{1}_\mathbf{I}] \vdash N_1 : B[\mathbf{1}_\mathbf{I}^\times]} \quad \frac{\Gamma.\backslash\boldsymbol{r}.A[\mathbf{0}_\mathbf{I}].A[\mathbf{1}_\mathbf{I} \circ \mathfrak{p}].\text{Bridge}_{A[\mathfrak{p}^2]}(\mathfrak{q}[\mathfrak{p}], \mathfrak{q}) \vdash N : \text{Bridge}_{B[(\mathfrak{p}^3 \circ \text{id}^\dagger).\mathfrak{q}_\mathbf{I}.\mathfrak{q}[\text{id}^\dagger]@\mathfrak{q}_\mathbf{I}]}(N_0[\mathfrak{p}^2], N_1[\mathfrak{p}^\times \circ \mathfrak{p}])}{\Gamma \vdash \text{extent}_\boldsymbol{r}(M[\text{id.}\boldsymbol{r}]; N_0, N_1, N) = N[\text{id.}M[\mathbf{0}_\mathbf{I}].M[\mathbf{1}_\mathbf{I}].\lambda^\mathbf{I}.M]@\boldsymbol{r} : B[\text{id.}\boldsymbol{r}.M]}$$

## REFERENCES

[ABC+19] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Kuen-Bang Hou (Favonia), Robert Harper, and Daniel R. Licata. Syntax and models of cartesian cubical type theory. Unpublished draft, February 2019.

[ACS15] Benedikt Ahrens, Paolo Capriotti, and Régis Spadotti. Non-wellfounded trees in homotopy type theory. In Thorsten Altenkirch, editor, 13th International Conference on Typed Lambda Calculi and Applications, TLCA 2015, July 1-3, 2015, Warsaw, Poland, volume 38 of LIPIcs, pages 17-30. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2015.

5:58

E. CAVALLO AND R. HARPER

Vol. 17:4

[AFH18] Carlo Angiuli, Kuen-Bang Hou (Favonia), and Robert Harper. Cartesian cubical computational type theory: Constructive reasoning with paths and equalities. In *27th EACSL Annual Conference on Computer Science Logic, CSL 2018, September 4-7, 2018, Birmingham, UK*, pages 6:1-6:17, 2018.[AGJ14] Robert Atkey, Neil Ghani, and Patricia Johann. A relationally parametric model of dependent type theory. In *The 41st Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages, POPL '14, San Diego, CA, USA, January 20-21, 2014*, pages 503-516, 2014.[All87] Stuart Allen. A non-type-theoretic definition of Martin-Löf's types. In *Proceedings of the Symposium on Logic in Computer Science (LICS '87), Ithaca, New York, USA, June 22-25, 1987*, pages 215-221, 1987.[Ang19] Carlo Angiuli. *Computational Semantics of Cartesian Cubical Type Theory*. PhD thesis, Carnegie Mellon University, 2019.[AW09] Steve Awodey and Michael A. Warren. Homotopy theoretic models of identity types. *Math. Proc. Cambridge Philos. Soc.*, 146(1):45-55, 2009.[Awo18] Steve Awodey. A cubical model of homotopy type theory. *Ann. Pure Appl. Logic*, 169(12):1270-1294, 2018.[BCH13] Marc Bezem, Thierry Coquand, and Simon Huber. A model of type theory in cubical sets. In *19th International Conference on Types for Proofs and Programs, TYPES 2013, April 22-26, 2013, Toulouse, France*, pages 107-128, 2013.[BCH19] Marc Bezem, Thierry Coquand, and Simon Huber. The univalence axiom in cubical sets. *J. Autom. Reasoning*, 63(2):159-171, 2019.[BCM15] Jean-Philippe Bernardy, Thierry Coquand, and Guilhem Moulin. A presheaf model of parametric type theory. *Electr. Notes Theor. Comput. Sci.*, 319:67-82, 2015.[BELS16] Auke Bart Booij, Martin Hötzel Escardó, Peter LeFanu Lumsdaine, and Michael Shulman. Parametricity, automorphisms of the universe, and excluded middle. In Silvia Ghilezan, Herman Geuvers, and Jelena Ivetic, editors, *22nd International Conference on Types for Proofs and Programs, TYPES 2016, May 23-26, 2016, Novi Sad, Serbia*, volume 97 of *LIPics*, pages 7:1-7:14. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2016.[BHN14] Nick Benton, Martin Hofmann, and Vivek Nigam. Abstract effects and proof-relevant logical relations. In *The 41st Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages, POPL '14, San Diego, CA, USA, January 20-21, 2014*, pages 619-632, 2014.[BJP10] Jean-Philippe Bernardy, Patrik Jansson, and Ross Paterson. Parametricity and dependent types. In *ICFP 2010, Baltimore, Maryland, USA, September 27-29, 2010*, pages 345-356, 2010.[BM12] Jean-Philippe Bernardy and Guilhem Moulin. A computational interpretation of parametricity. In *LICS 2012, Dubrovnik, Croatia, June 25-28, 2012*, pages 135-144, 2012.[BM13] Jean-Philippe Bernardy and Guilhem Moulin. Type-theory in color. In *ICFP 2013, Boston, MA, USA - September 25 - 27, 2013*, pages 61-72, 2013.[Bru18] Guillaume Brunerie. Computer-generated proofs for the monoidal structure of the smash product. *Homotopy Type Theory Electronic Seminar Talks*, November 2018.[Car86] John Cartmell. Generalised algebraic theories and contextual categories. *Ann. Pure Appl. Log.*, 32:209-243, 1986.[CCHM15] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. Cubical type theory: A constructive interpretation of the univalence axiom. In *21st International Conference on Types for Proofs and Programs, TYPES 2015, May 18-21, 2015, Tallinn, Estonia*, pages 5:1-5:34, 2015.[CH18] Evan Cavallo and Robert Harper. Computational higher type theory IV: inductive types. *CoRR*, abs/1801.01568, 2018.[CH19a] Evan Cavallo and Robert Harper. Higher inductive types in cubical computational type theory. *PACMPL*, 3(POPL):1:1-1:27, 2019.[CH19b] Evan Cavallo and Robert Harper. Parametric cubical type theory, 2019.[CH20] Evan Cavallo and Robert Harper. Internal parametricity for cubical type theory. In Maribel Fernández and Anca Muscholl, editors, *28th EACSL Annual Conference on Computer Science Logic, CSL 2020, January 13-16, 2020, Barcelona, Spain*, volume 152 of *LIPics*, pages 13:1-13:17. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2020.[Che12] James Cheney. A dependent nominal type theory. *Logical Methods in Computer Science*, 8(1), 2012.

Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:59

[CHM18] Thierry Coquand, Simon Huber, and Anders Mörtberg. On higher inductive types in cubical type theory. In LICS 2018, Oxford, UK, July 9-12, 2018, 2018.
[CMS20] Evan Cavallo, Anders Mörtberg, and Andrew W. Swan. Unifying cubical models of univalent type theory. In Maribel Fernández and Anca Muscholl, editors, 28th EACSL Annual Conference on Computer Science Logic, CSL 2020, January 13-16, 2020, Barcelona, Spain, volume 152 of LIPIcs, pages 14:1-14:17. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2020.
[Coq18] Thierry Coquand. Canonicity and normalisation for dependent type theory. CoRR, abs/1810.09367, 2018.
[DP02] Brian A. Davey and Hilary A. Priestley. Introduction to Lattices and Order, Second Edition. Cambridge University Press, 2002.
[GJF+15] Neil Ghani, Patricia Johann, Fredrik Nordvall Forsberg, Federico Orsanigo, and Tim Revell. Bifibrational functorial semantics of parametric polymorphism. Electr. Notes Theor. Comput. Sci., 319:165-181, 2015.
[Hof97] Martin Hofmann. Syntax and Semantics of Dependent Types, pages 79-130. Publications of the Newton Institute. Cambridge University Press, 1997.
[HS98] Martin Hofmann and Thomas Streicher. The groupoid interpretation of type theory. In Twenty-five years of constructive type theory (Venice, 1995), volume 36 of Oxford Logic Guides, pages 83-111. Oxford Univ. Press, New York, 1998.
[Kan55] Daniel M. Kan. Abstract homotopy. I. Proceedings of the National Academy of Sciences of the United States of America, 41(12):1092-1096, 1955.
[KD13] Neelakantan R. Krishnaswami and Derek Dreyer. Internalizing relational parametricity in the extensional calculus of constructions. In Computer Science Logic 2013 (CSL 2013), CSL 2013, September 2-5, 2013, Torino, Italy, pages 432-451, 2013.
[KL12] Chris Kapulkin and Peter LeFanu Lumsdaine. The simplicial model of univalent foundations (after Voevodsky), 2012. arXiv:1211.2851.
[KL20] Chris Kapulkin and Peter LeFanu Lumsdaine. The law of excluded middle in the simplicial model of type theory. Unpublished note, 2020.
[KvR19] Nicolai Kraus and Jakob von Raumer. Path spaces of higher inductive types in homotopy type theory. In 34th Annual ACM/IEEE Symposium on Logic in Computer Science, LICS 2019, Vancouver, BC, Canada, June 24-27, 2019, pages 1-13. IEEE, 2019.
[ML75] Per Martin-Löf. An intuitionistic theory of types: predicative part. In H.E. Rose and J.C. Shepherdson, editors, Logic Colloquium '73, volume 80 of Studies in Logic and the Foundations of Mathematics, pages 73-118. North-Holland, 1975.
[ML82] Per Martin-Löf. Constructive mathematics and computer programming. In L.J. Cohen, J. Loš, H. Pfeiffer, and K.-P. Podewski, editors, Logic, Methodology and Philosophy of Science, volume VI, pages 153-175, 1982.
[Mou16] Guilhem Moulin. Internalizing Parametricity. PhD thesis, Chalmers University of Technology, Gothenburg, Sweden, 2016.
[ND18] Andreas Nuyts and Dominique Devriese. Degrees of relatedness: A unified framework for parametricity, irrelevance, ad hoc polymorphism, intersections, unions and algebra in dependent type theory. In Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS 2018, Oxford, UK, July 09-12, 2018, pages 779-788, 2018.
[Nuy20] Andreas Nuyts. Contributions to Multimode and Presheaf Type Theory. PhD thesis, KU Leuven, Leuven, Belgium, 2020.
[NVD17] Andreas Nuyts, Andrea Vezzosi, and Dominique Devriese. Parametric quantifiers for dependent type theory. PACMPL, 1(ICFP):32:1-32:29, 2017.
[OP18] Ian Orton and Andrew M. Pitts. Axioms for modelling cubical type theory in a topos. Logical Methods in Computer Science, 14(4), 2018.
[Pit13] Andrew M. Pitts. Nominal Sets: Names and Symmetry in Computer Science. Cambridge University Press, Cambridge, 2013.
[Pit14] Andrew M. Pitts. Nominal presentation of cubical sets models of type theory. In 20th International Conference on Types for Proofs and Programs, TYPES 2014, May 12-15, 2014, Paris, France, pages 202-220, 2014.
[Rey83] John C. Reynolds. Types, abstraction and parametric polymorphism. In IFIP Congress, pages 513-523, 1983.

5:60

E. CAVALLO AND R. HARPER

Vol. 17:4

[Rie18] Emily Riehl. On the directed univalence axiom. Talk slides, AMS Special Session on Homotopy Type Theory, Joint Mathematics Meetings, January 2018.

[Rij18] Egbert Rijke. Classifying Types: Topics in synthetic homotopy theory. PhD thesis, Carnegie Mellon University, 2018.

[RR94] E. P. Robinson and Giuseppe Rosolini. Reflexive graphs and parametric polymorphism. In Proceedings of the Ninth Annual Symposium on Logic in Computer Science (LICS '94), Paris, France, July 4-7, 1994, pages 364-371. IEEE Computer Society, 1994.

[RS17] Emily Riehl and Michael Shulman. A type theory for synthetic ∞-categories. Higher Structures, 1(1):116-193, 2017.

[Shu15] Michael Shulman. Univalence for inverse diagrams and homotopy canonicity. Math. Struct. Comput. Sci., 25(5):1203-1277, 2015.

[Shu18] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive homotopy type theory. Math. Struct. Comput. Sci., 28(6):856-941, 2018.

[SJ18] Kristina Sojakova and Patricia Johann. A general framework for relational parametricity. In Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS 2018, Oxford, UK, July 09-12, 2018, pages 869-878, 2018.

[SS12] Urs Schreiber and Michael Shulman. Quantum gauge field theory in cohesive homotopy type theory. In Ross Duncan and Prakash Panangaden, editors, Proceedings 9th Workshop on Quantum Physics and Logic, QPL 2012, Brussels, Belgium, 10-12 October 2012, volume 158 of EPTCS, pages 109-126, 2012.

[Tak01] Izumi Takeuti. The theory of parametricity in lambda cube. Technical Report 1217, Kyoto University, 2001.

[TTS18] Nicolas Tabareau, Éric Tanter, and Matthieu Sozeau. Equivalences for free: Univalent parametricity for effective transport. Proceedings of the ACM on Programming Languages, 2(ICFP):92:1-92:29, September 2018.

[Uni13] The Univalent Foundations Program. Homotopy Type Theory: Univalent Foundations of Mathematics. https://homotopytypetheory.org/book, Institute for Advanced Study, 2013.

[VAG⁺] Vladimir Voevodsky, Benedikt Ahrens, Daniel Grayson, et al. UniMath: Univalent Mathematics. Available at https://github.com/UniMath.

[vD18] Floris van Doorn. On the Formalization of Higher Inductive Types and Synthetic Homotopy Theory. PhD thesis, Carnegie Mellon University, 2018.

[vdBG12] Benno van den Berg and Richard Garner. Topological and simplicial models of identity types. ACM Trans. Comput. Log., 13(1):3:1-3:44, 2012.

[Voe15] Vladimir Voevodsky. An experimental library of formalized mathematics based on the univalent foundations. Mathematical Structures in Computer Science, 25:1278-1294, 2015.

[Wad89] Philip Wadler. Theorems for free! In FPCA 1989, London, UK, September 11-13, 1989, pages 347-359, 1989.

[War08] Michael Alton Warren. Homotopy Theoretic Aspects of Constructive Type Theory. PhD thesis, Carnegie Mellon University, 2008.

[WL20] Matthew Z. Weaver and Daniel R. Licata. A constructive model of directed univalence in bicubical sets. In LICS '20: 35th Annual ACM/IEEE Symposium on Logic in Computer Science, Saarbrücken, Germany, July 8-11, 2020, pages 915-928, 2020.

This work is licensed under the Creative Commons Attribution License. To view a copy of this license, visit https://creativecommons.org/licenses/by/4.0/ or send a letter to Creative Commons, 171 Second St, Suite 300, San Francisco, CA 94105, USA, or Eisenacher Strasse 2, 10777 Berlin, Germany.