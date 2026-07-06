arXiv:2311.18781v2 [math.CT] 1 Feb 2024

# Displayed Type Theory and Semi-Simplicial Types

Astra Kolomatskaia\*

Michael Shulman†

## Abstract

We introduce *Displayed Type Theory (dTT)*, a multi-modal homotopy type theory with *discrete* and *simplicial* modes. In the intended semantics, the discrete mode is interpreted by a model for an arbitrary  $\infty$ -topos, while the simplicial mode is interpreted by Reedy fibrant augmented semi-simplicial diagrams in that model. This simplicial structure is represented inside the theory by a primitive notion of *display* or *dependency*, guarded by modalities, yielding a partially-internal form of unary parametricity.

Using the display primitive, we then give a coinductive definition, at the simplicial mode, of a type SST of semi-simplicial types. Roughly speaking, a semi-simplicial type X consists of a type  $X_0$  together with, for each  $x : X_0$ , a displayed semi-simplicial type over X. This mimics how simplices can be generated geometrically through repeated cones, and is made possible by the display primitive at the simplicial mode. The discrete part of SST then yields the usual infinite indexed definition of semi-simplicial types, both semantically and syntactically. Thus, dTT enables working with semi-simplicial types in full semantic generality.

## Contents

|  **1** | **Introduction** | **2**  |
| --- | --- | --- |
|  **2** | **Syntax** | **12**  |
|  2.1 | The mode theory . . . . . | 12  |
|  2.2 | The modal type theory . . . . . | 13  |
|  2.3 | Telescopes and meta-abstractions, I . . . . . | 16  |
|  2.4 | Décalage and displayed types . . . . . | 19  |
|  2.5 | Telescopes and meta-abstractions, II . . . . . | 22  |
|  2.6 | Displayed telescopes . . . . . | 24  |
|  **3** | **Semi-Simplicial and Displayed Coinductive Types** | **29**  |
|  3.1 | Semi-simplicial types . . . . . | 29  |
|  3.2 | Examples of semi-simplicial types . . . . . | 32  |
|  3.3 | Displayed coinductive types . . . . . | 36  |
|  3.4 | Examples of displayed coinductive types . . . . . | 38  |

\*We acknowledge the support of the Natural Sciences and Engineering Research Council of Canada (NSERC). Cette recherche a été financée par le Conseil de recherches en sciences naturelles et en génie du Canada (CRSNG). [funding reference number CGSD3-545891-2020]

This material is based upon work supported by the National Science Foundation under Grant No. DMS-2204304.

†This material is based upon work supported by the Air Force Office of Scientific Research under award number FA9550-21-1-0009.

1

|  4 Semantics | 39  |
| --- | --- |
|  4.1 The semantics of dependent type theory | 40  |
|  4.2 The simplicial model | 51  |
|  4.3 Modalities | 63  |
|  4.4 Semantics of dTT | 74  |
|  4.5 Semantics of semi-simplicial types | 80  |
|  5 Conclusion and Future Work | 97  |
|  A Verifications for the Simplicial Model | 103  |
|  A.1 Variables | 103  |
|  A.2 Π-types | 104  |
|  A.3 Universes | 105  |
|  A.4 ω-limits | 106  |

# 1 Introduction

Semi-simplicial types. Homotopy Type Theory (HoTT) [Uni13] is a perspective on intensional dependent type theory that regards types as homotopical spaces or ∞-groupoids. It has proven remarkably successful as a synthetic context in which to do homotopy theory and algebraic topology, and as an internal language for (∞, 1)-toposes [Shu19]. However, an enduring frustration has been its apparent inability to define general homotopy-coherent structures. Some infinite structures can be defined in HoTT, such as globular types and spectra; but others, such as A∞-spaces or (∞, 1)-categories, have so far resisted all attempts at definition. We know no convincing explanation for why they should be impossible, but the fact that all attempts appear to fail in a similar way suggests the operation of an as-yet-unarticulated principle.

Specifically, stating an 'infinite coherence' property generally seems to require an infinite structure within which to assemble the coherences, while defining such a structure itself seems to require infinite coherence, leading to an infinite regress. This is in contrast to the situation in classical homotopy theory where the infinite structures to describe coherence, such as operads and simplicial diagrams, can themselves be defined using strict point-set-level equalities, which are then automatically fully coherent. It is tempting to try to mimic this in homotopy type theory using definitional equalities in place of point-set ones, but this is difficult because definitional equality is not reified in the theory and we have limited tools for forcing it to hold.

One of the more flexible ways to enforce definitional equalities is to use type dependency, moving from a fibred perspective to an indexed one. In the simplest case, this means replacing a function p : E → B with a type family Ē : B → Type. This has a corresponding projection function π₁ : Σ Ē → B, but we can suppose a point ē : Σ Ē with a definitional equality π₁ ē ≡ b by supposing a point e : Ē b and letting ē = {b, e}.

Thus, it is natural to try to define infinitely coherent structures that can be expressed in a purely indexed way. The example of this sort which has attracted the most attention is that of semi-simplicial types, because they are well-known within homotopy theory and

2

could be used to encode many, if not all, other infinitely coherent structures. In indexed style, a semi-simplicial type consists of type families $A_0$, $A_1$, $A_2$, and so on, having types that start out as follows:

$A_0$: Type

$A_1: (x_0: A_0) (x_0: A_0) \rightarrow \text{Type}$

$A_2: (x_{01}: A_0) (x_{01}: A_0) (\beta_{01}: A_1 x_{01} x_{01}) (x_{01}: A_0) (\beta_{01}: A_1 x_{01} x_{01}) (\beta_{01}: A_1 x_{01} x_{01}) \rightarrow \text{Type}$

$A_3: (x_{001}: A_0) (x_{001}: A_0) (\beta_{001}: A_1 x_{001} x_{001}) (x_{001}: A_0) (\beta_{001}: A_1 x_{001} x_{001}) (\beta_{001}: A_1 x_{001} x_{001})$

$(f_{011}: A_2 x_{001} x_{011} \beta_{011} x_{011} \beta_{011} \beta_{011})$ $(x_{100}: A_0) (\beta_{100}: A_1 x_{001} x_{100})$ $(\beta_{100}: A_1 x_{001} x_{100})$

$(f_{111}: A_2 x_{001} x_{011} \beta_{011} x_{011} \beta_{011} \beta_{011})$ $(\beta_{110}: A_1 x_{010} x_{010})$ $(f_{110}: A_2 x_{001} x_{010} \beta_{010} x_{010} \beta_{010} \beta_{010})$

$(f_{110}: A_2 x_{010} x_{010} \beta_{010} x_{010} \beta_{010} \beta_{010}) \rightarrow \text{Type}$

First, we have a type $A_0$ of points. Second, we have for every two points $x_0, x_0: A_0$, a type $A_1 x_0 x_0$ of lines joining $x_0$ and $x_0$. Third, for every three points $x_{01}, x_{01}, x_{00}: A_0$ and three lines $\beta_{01}: A_0 x_{01} x_{01}$, $\beta_{01}: A_0 x_{01} x_{00}$, and $\beta_{01}: A_0 x_{01} x_{00}$, a type $A_1 x_{01} x_{00} \beta_{01} x_{01} \beta_{01} \beta_{01}$ of triangles with the given boundary. The pattern continues with tetrahedra, which we may also, more technically, call 3-simplices. In general, $A_n$ describes the type of n-simplices indexed by their boundaries.

**Remark 1.1.** The binary subscripts on variables above follow a scheme that we learned from Tim Campion, although related schemas have been rediscovered many times. The $2^{n+1} - 1$ simplices constituting an n-simplex and its boundary are labeled by the numbers from 1 to $2^{n+1} - 1$ written in binary, where the number of 1s in a binary number corresponds to the dimension of the simplex, and the binary numbers corresponding to the boundary of some simplex are obtained by replacing one or more of the 1s in its binary number by 0s. (As we will see later, the binary number 0 can also be regarded as denoting the unique (-1)-simplex in the boundary of an n-simplex in an augmented semi-simplicial set.)

We then list these simplices in the order given by these numbers. This ordering may seem somewhat curious, compared to the more naïve approach of listing all the 0-simplices, then all the 1-simplices, and so on; but it does retain the important property that all the simplices in the boundary of some simplex are listed before it (thus, for instance, it makes the semi-simplex category into an 'ordered direct category'; see section 4.5.5). We will see later that this ordering is what arises most naturally in (co)inductive constructions of semi-simplicial sets (which was also Campion's motivation).

In addition to subscripting simplex variables by binary numbers according to this scheme, in this paper we will use different base letters to indicate the dimension of each variable. Thus for instance $x_{01}$, $x_{01}$, and $x_{00}$ are all 0-simplices, while $\beta_{01}$, $\beta_{01}$, and $\beta_{00}$ are all 1-simplices, and $f_{01}$ is a 2-simplex. We will not have much occasion to denote 3-simplices; for (-1)-simplices we use the Cyrillic letter ʒ (ze). We may also use different letters from the same alphabets for simplices in different semi-simplicial types, e.g. $\gamma_0: B_1 y_0 y_0$ and $\delta_0: C_1 z_0 z_0$.

One may think of the terms $A_0$, $A_1$, $A_2$, and so on as defining the fields of an infinite record type. Terms of this infinite record type SST are known as semi-simplicial types. Thus, the problem is to define a type of semi-simplicial types within homotopy type theory, continuing the above pattern. As a correctness criterion, one would expect that when interpreted in any $(\infty, 1)$-topos the type SST becomes a classifier of semi-simplicial objects. However,

3

even this problem is still unsolved: every attempt to internally encode the combinatorics that generate the type of $A_n$, as a function of $n$, seems to lead once again to an infinite regress.

In light of this situation, an alternative approach is to formulate more expressive type theories that can solve the problem of infinitely coherent objects. One such proposal is Two-Level Type Theory (2LTT) [ACKS23], which introduces an 'outer level' of 'exo-types' that are not homotopy-invariant. The exo-types admit a strict exo-equality type, essentially reifying definitional equality, which can then be used analogously to classical point-set equality to define infinitely coherent structures. And by the results of [Usk23], 2LTT can be interpreted in any $(\infty, 1)$-topos, so its semantics are not significantly less general than ordinary HoTT, and the type SST defined in 2LTT does interpret to the correct classifier. However, although the exo-equality is assumed to satisfy Uniqueness of Identity Proofs, to keep type-checking decidable it cannot satisfy a reflection rule making exo-equalities into definitional equalities. Thus, it can be quite cumbersome to work with in practice.

Another proposal is Simplicial Type Theory (STT) [RS17], which changes perspective to view individual types as simplicial spaces, with additional primitives for manipulating the simplicial structure. One can then simply impose conditions on one of these 'simplicial types' to make it represent (for instance) an $(\infty, 1)$-category. This suggests a 'synthetic' approach to higher category theory analogous to ordinary HoTT's synthetic approach to homotopy theory, which is potentially quite powerful; and the results of [RS17, Wei22] imply that it can be interpreted in the category of simplicial objects in any $(\infty, 1)$-topos. However, the strength of the synthetic approach is also its weakness: because simplicial types are postulated rather than defined, what we can do with them is limited to what is expressed by the axiomatization.

A coinductive definition of semi-simplicial types. In this paper we propose a third enhancement of homotopy type theory, called Displayed Type Theory (dTT), in which it is possible to define and work with semi-simplicial types (and many other things). This type theory is inspired by the following idea for a coinductive definition of a type SST of semi-simplicial types:

Idea 1.2. A semi-simplicial type A consists of

- a type Z A, and
- for each x : Z A, a semi-simplicial type S A x over A.

It may not be at all obvious why this should be a definition of semi-simplicial types, so let us unravel it a few steps:

0. Every semi-simplicial type A has a type Z A, whose points we call 0-simplices of A. Thus we may also write $A_0 = Z A$.
1. Every 0-simplex x : $A_0$ gives rise to a semi-simplicial type S A x over A, called the slice of A over x. Of course, if we don't know what a semi-simplicial type is, we can't be expected to know what one semi-simplicial type over another one is — at least, not completely. But we do know that every semi-simplicial type A has an underlying type Z A, so it stands to reason that a semi-simplicial type B over A should in particular have an underlying type $Z^d B$ over Z A, i.e. a type family $Z^d B : Z A \to \text{Type}$. Thus, in

4

particular for every $x : A_0$ we have $Z^d(S A x) : A_0 \to \text{Type}$, hence for every additional $y : A_0$ we have a type $Z^d(S A x) y$. We call this the type $A_1 x y$ of 1-simplices from $x$ to $y$.

2. Now we know that every semi-simplicial type $A$ has not only an underlying type of 0-simplices $A_0$, but for every $x_0, x_1 : A_0$ a type $A_1 x_0 x_1$ of 1-simplices. Therefore, it stands to reason that any semi-simplicial type $B$ over $A$ should also have, not only a type family $B_0$ over $A_0$, but a type family $B_1$ over $A_1$. Thinking of $A_1$ as an indexed representation of a span $A_0 \leftarrow \int A_1 \to A_0$, we deduce that $B_1$ should be an indexed representation of a span morphism

![img-0.jpeg](img-0.jpeg)

and therefore we should have

$$B_1 : (y_0 : A_0) (z_0 : B_0 y_0) (y_0 : A_0) (z_0 : B_0 y_0) (\gamma_0 : A_1 y_0 y_0) \to \text{Type}.$$

More precisely, since every 0-simplex $y_0$ of $A$ gives rise to a semi-simplicial type $S A y_0$ over $A$, any 0-simplex $z_0$ of $B$ over $y_0$ should give rise to a semi-simplicial type $S^d B y_0 z_0$ over both $B$ and $S A y_0$. But the common dependence on $A$ should be shared, so $S^d B y_0 z_0$ should live over the cospan $B \to A \leftarrow S A y_0$:

![img-1.jpeg](img-1.jpeg)

Passing to 0-simplices, this means that $Z^{dd}(S^d B y_0 z_0)$ should be a type dependent on $y_0 : A_0, z_0 : B_0 y_0$, and $y_{11} : (S A y_0)_0 y_0 \equiv A_1 y_0 y_0$. Thus we can define the 1-simplices of $B$ as $B_1 y_0 z_0 y_0 z_0 \gamma_0 \equiv Z^{dd}(S^d B y_0 z_0) y_0 z_0 \gamma_0$.

In particular, therefore, since for any $x : A_0$ we have a semi-simplicial type $S A x$ over $A$, we have

$$(S A x)_1 : (y_0 : A_0) (z_0 : (S A x)_0 y_0) (y_0 : A_0) (z_0 : (S A x)_0 y_0) (\gamma_0 : A_1 y_0 y_0) \to \text{Type}.$$

Since $(S A x)_0 y_0 \equiv A_1 x y_0$ by definition, this is equivalently

$$(S A x)_1 : (y_0 : A_0) (z_0 : A_1 x y_0) (y_0 : A_0) (z_0 : A_1 x y_0) (\gamma_0 : A_1 y_0 y_0) \to \text{Type}.$$

Renaming the variables as $y_0 \equiv x_{00}$, $\gamma_0 \equiv \beta_{00}$, and $z_0 \equiv \beta_{01}$, and writing $x \equiv x_{01}$, this becomes

$$(S A x_{01})_1 : (x_{01} : A_0) (\beta_{01} : A_1 x_{01} x_{01}) (x_{00} : A_0) (\beta_{01} : A_1 x_{00} x_{00}) (\beta_{00} : A_1 x_{00} x_{00}) \to \text{Type}.$$

Thus, this is precisely correct to be a type of 2-simplices:

$$A_2 x_{01} x_{00} \beta_{01} x_{00} \beta_{01} \beta_{10} \equiv (S A x_{01})_1 x_{00} \beta_{01} x_{00} \beta_{01} \beta_{10}.$$

5

This pattern may be visualised as follows:

Z A

$$Z^d (S A x_{01}) x_{01}$$

$$Z^{dd} (S^d (S A x_{01}) x_{01} \beta_{01}) x_{00} \beta_{01} \beta_{10}$$

![img-2.jpeg](img-2.jpeg)

![img-3.jpeg](img-3.jpeg)

An alternative, and more geometrical, viewpoint, is that the n-simplex is the cone of the (n-1)-simplex. Thus, if we already know that every semi-simplicial type has a suitably indexed type of (n-1)-simplices, we can conclude the same about the n-simplices as follows. For every 0-simplex x, the dependent semi-simplicial type S A x has a type of 'dependent (n-1)-simplices' indexed by the type of (n-1)-simplices of A. Thus, an element of this type depends on x (the cone vertex) as well as an (n-1)-simplex of A (the base face, opposite the cone vertex), and its boundary consisting of dependent k-simplices for k < n-1 that form cones over all the faces of the base (n-1)-simplex sharing the same vertex x. Together, these form the boundary of an n-simplex. (In the ordering of variables induced by the above presentation, the simplices in the base face are interspersed with their dependent versions: thus in the case n ≡ 2 the faces x₁₀, x₁₁, β₁₀ form the base 1-simplex with β₁₁, β₁₂ the dependent 0-simplices (i.e. 1-simplices) forming a cone over the boundary x₁₁, x₁₂.) Hopefully this is sufficiently convincing for now; later we will give a precise justification.

As simple and appealing as this 'definition' is, it is not meaningful in ordinary dependent type theory. The intuitive claim is that it defines a type SST by coinduction, with Z and S as destructors. For Z this is unproblematic (it is not even corecursive). However, the output of S is not an element of the type SST being defined, as would be usual for a corecursive destructor of a coinductive type, but a 'dependent element', or 'displayed element', of SST over the input of S. If we write SSTᵈ for this putative family of 'displayed elements', the types of Z and S are

$$Z : SST \rightarrow Type$$

$$S : (X : SST) \rightarrow Z X \rightarrow SST^d X.$$

(1.3)

We would like to regard this as a sort of 'higher coinductive type'. Just as a higher inductive type can have constructors involving not just elements of the type being defined but also paths therein, here we have a putative coinductive type whose destructors involve not just elements of the type being defined but also 'displayed elements' thereof. Thus, to make sense of this we need a type theory with a primitive operation (-)ᵈ associating to a type its family of 'displayed elements'. As it turns out, the precise notion of (-)ᵈ that we require is a variant of unary internal parametricity.

External and internal parametricity. In general, by 'parametricity' we mean a statement that every type (perhaps subject to contextual restrictions; see below) is equipped with a relation (of some arity), and every function (subject to the same restrictions) preserves those relations. The original form of parametricity, such as in [Wad89], is a meta-theoretic

6

statement about type theory, in which the relations are meta-theoretic, and the contextual restriction is that it applies only to closed types and terms (those defined in the empty context). That is, in this 'external' parametricity, every closed type is given a relation on its closed terms, which is preserved by every closed function. For instance, in the unary case, given a closed function $(\cdot) \vdash f : A \to B$, if the A-relation holds of a closed term $(\cdot) \vdash a : A$, then the B-relation holds of the closed term $(\cdot) \vdash f a : B$. Indeed, the fact that f satisfies this condition is exactly the statement that the $(A \to B)$-relation holds of it, and is thus a special case of the 'fundamental theorem of logical relations' that every closed term satisfies the relation on its type. Semantically, external parametricity is obtained by interpreting type theory in a 'gluing' or 'relational' model.

By contrast, in type theories with fully internal parametricity such as [BM12, BCM15, Mou16], there is no contextual restriction, and the relations are internal (i.e. type families). In the unary case, this means for any type in any context, say $\Gamma \vdash A$ type, there is a type family that we will denote $\Gamma$, $x : A \vdash A^d x$ type, and every function $\Gamma \vdash f : A \to B$ in any context lifts to a function $\Gamma \vdash f^d : (x : A)(x' : A^d x) \to B^d (f x)$ between these type families. As in the external case, there is a formula for the relation of a function-type:

$$((a : A) \to B [ a ])^d f \equiv (a : A) (a' : A^d a) \to B^d [ a , a' ] (f a) \tag{1.4}$$

which says that so-called 'computability witnesses' for f take computability witnesses of a to computability witnesses of f a. Thus the statement that f preserves computability witnesses is equivalent to saying it lifts to an element $f^d$ of this type, and is a special case of a general rule that every term $\Gamma \vdash a : A$ lifts to a computability witness $\Gamma \vdash a^d : A^d a$.¹

Such an internalization of parametricity introduces the new possibility of iterating it, leading to $A^{dd}$, $A^{ddd}$, and so on. Semantically, this means that each type must be interpreted by a cubical type (or set), where the arity of the relations determines the number of 'boundary points' on each side of the cubes, and the dependencies of each iterated relation on the previous ones supplies the faces of a cube. Our primary interest is in unary parametricity, where $A^d$ depends only on one copy of A; in this case the semantics involves 'unary cubes' where each edge has only one vertex.²

The rule lifting any a to $a^d$ then implies that these cubical types must have degeneracies, taking any cube to a higher-dimensional one with some boundaries trivial. More surprisingly, it seems that to have good computational behavior and semantic models, the cubical types must also include symmetries (transpositions): from $d \equiv \lambda x. x^d : (x : X) \to X^d x$, we can either directly obtain the type of $d^d$ as $(x : X) (x' : X^d x) \to X^{dd} x x' x^d$ or first perform the computation $d^d \equiv \lambda x x'. x'^d$ and obtain its type as $(x : X) (x' : X^d x) \to X^{dd} x x^d x'$, and it these must be related by a symmetry operation.

The general advantages of internal parametricity over external are clear: we can reason about computability witnesses while staying within a single type theory, using a single proof assistant. Moreover, internal parametricity allows us to at least try to make sense of a type SST with the destructors (1.3). However, fully internal parametricity is not conservative over ordinary type theory: it is highly nonclassical, incompatible with axioms such as the law of excluded middle; and its semantics is not as general as we would like. We would like our type theory to be interpretable in any $(\infty, 1)$-topos (generalizing [Shu19]), in such

¹The punning of notation is intentional, and indeed consistent, as we will see: the type $(-)^d$ coincides with the term $(-)^d$ applied to elements of the universe.

²Geometrically, these can be thought of as powers of a half-open interval $[0, 1]^n$, or closed octants $[0, \infty)^n$ in n-dimensional Euclidean space.

7

a way that our type SST is interpreted by a category-theoretic 'classifier' of semi-simplicial objects; but as we have just observed, the semantics of internal parametricity seems to live only in a category of cubical objects. Now the category of cubical objects in an $(\infty, 1)$-topos is again an $(\infty, 1)$-topos, so (using [Shu19]) we can expect to interpret an internally parametric type theory in the latter; but the connection of this interpretation to the original $(\infty, 1)$-topos is not clear.

**Displayed Type Theory.** Our solution is to use a *less internally* parametric type theory. We can think of internal parametricity as arising in three stages. The first stage is an *external* parametricity model, where types are interpreted by pairs $(A_0 : \text{Type}, A_1 : A_0 \to \text{Type})$. In this case $(-)^d$ maps one model to a *different* model, interpreting an ordinary type by a pair of types; this yields parametricity results as metatheorems. In the second stage, to make $A^d$ live in the same model as $A$, we iterate this construction infinitely many times; now types are interpreted by *semi-cubical types*, with faces but not degeneracies. Finally, in the third stage we add a 'degeneracy' operation $(x : A) \to A^d x$ making every *term* parametric. This allows proving parametricity theorems *inside* the type theory, and semantically moves us from semi-cubical types to cubical ones.

The solution to our problem is to stop after the *second* stage. This is advantageous semantically because semi-cubical sets are presheaves on a *direct* category (i.e. covariant diagrams on an *inverse* category), and in this case the model construction is much more concrete. Specifically, in [Shu15] it was shown that from any model of univalent dependent type theory inside of a type theoretic fibration category, one may form a derived model of Reedy fibrant presheaves on any direct category, with the type formers in the presheaf model constructed inductively in terms of those in the original model. In particular, in degree 0 all the type-formers act exactly as they do in the original model. Thus, semantically we can be sure that all our constructions, including SST, specialise to something meaningful in an arbitrary $(\infty, 1)$-topos.

dTT is a syntax corresponding to this model, which is likewise intermediate between external parametricity and fully internal parametricity: its parametricity primitive $(-)^d$ has a contextual restriction that is weaker than the 'only closed terms' requirement of external parametricity, but stronger than the 'any context goes' laxity of internal parametricity. We start by observing that in either cubical or semi-cubical sets, the semantically fundamental parametricity operation actually changes the context: given $\Gamma \vdash t : A$, one has $\Gamma^D \vdash t^d : A^d t$, where $\Gamma^D$ augments $\Gamma$ by computability witnesses of all its variables. For cubical sets with degeneracies, we can deduce a version of $(-)^d$ that doesn't change the context by substituting along a degeneracy map $\Gamma \to \Gamma^D$ (e.g. this is the isomorphism between the 'global' and 'local' models of [ACKS24]). But for semi-cubical sets this is impossible, so we have to bite the bullet and deal with context-modifying operations.

The notion of a non-binding operation that changes contexts is familiar from the realm of modal logic, where, to first approximation, a proof of necessity of some proposition, i.e. of $\square A$, may only use necessary assumptions. Modalities in dependent type theory have previously been used to internalise meta-theoretic operations that don't make sense in arbitrary contexts, such as the right adjoint to a $\Pi$-type in [LOPS18], and we use them similarly here. Specifically, in dTT we have a modality $\triangle\square$ that partially internalises the notion of 'closed term' appearing in external parametricity, and which restricts the domain of $(-)^d$. Thus the only analogue of the above $d \equiv \lambda x \cdot x^d : (x : X) \to X^d x$ in dTT is $\overline{d} \equiv \lambda x \cdot x^d : (x : \triangle\square X) \to X^d x$. In particular, modal variables are protected from alteration

8

by $(-)^d$, so that we have $\bar{d}^d \equiv \lambda x \cdot x^{dd} : (x : \triangle \square X) \to X^{dd} \times x^d \times x^d$, thereby avoiding the need for symmetry.

In fact, to emphasise further that dTT retains general semantics over an arbitrary $(\infty, 1)$-topos, we will use a multimodal type theory [GKNB21, GCK$^+$22] with two modes, one for the original topos and the other for the topos of semi-cubical sets. These modes are related by modalities $\triangle$ (the constant semi-cubical type), $\diamond$ (the 0-cubes of a cubical type), and $\square$ (the limit of a cubical type), and $\triangle \square = \triangle \circ \square$ is a composite endo-modality. Only $\triangle \square$ is necessary to formulate display, but the other modalities are also useful to have around: in particular, $\diamond$ internalises the process of passing from the model in semi-cubical types to the original model in $\mathcal{C}$. For instance, $\diamond$ SST is what corresponds semantically to the classifier of semi-simplicial objects in $\mathcal{C}$.

Furthermore, display itself may be thought of as a modality, albeit one that is indexed over the original type. Display falls into into the new and yet underdeveloped framework of indexed modalities, such as the path types of cubical type theory (treated modally in [GCK$^+$22]) and the identity types of the forthcoming Higher Observational Type Theory (HOTT) [AKS22, ACKS24]. Moreover, analogously to those cases, we could formulate display either as an inert type-former defined by abstraction over an 'interval' (like path types in cubical type theory), or as an operation that computes on most other canonical type-formers (like identity types in HOTT). In this paper we make the latter choice, so that rules like eq. (1.4) are actually definitional equalities. Formulating such rules computationally is actually easier for dTT than for HOTT, due mainly to the lack of symmetry (although there is a tradeoff, since the presence of modalities is an extra complicating factor).

Until now we have been talking about semi-cubical types to make the connection with parametricity clear, but in the unary case there is an intriguing coincidence: the unary semi-cube category is isomorphic to the augmented semi-simplex category,$^3$ with a dimension shift: the n-cube corresponds to the $(n-1)$-simplex. For this reason we refer to the two modes in our theory as the discrete mode dm and the simplicial mode sm. Thus, dTT can actually internalise semi-simplicial types in two ways: as the coinductive type SST mentioned above, and as the universe of types at the simplicial mode. The latter suggests that dTT could also be used similarly to simplicial type theory, with types at the simplicial mode treated as synthetic (augmented semi-) simplicial types.

(Note that an augmented semi-simplicial type can be viewed as a family of ordinary semi-simplicial sets indexed by the type of $(-1)$-simplices. Thus, our observation that augmented semi-simplicial types support a better internal language than ordinary ones is analogous to the observation of [RFL21] that parametrised spectra are likewise preferable to unparametrised ones.)

Displayed structures. Our terminology display for the operation $^d$ is inspired by the fact that when applied to record types whose elements are algebraic structures, it produces displayed structures of the corresponding sort. Here a 'displayed structure' over a structure B is a structure A of the same kind with a structure map A $\to$ B, but reformulated in terms of the corresponding family of fibres B $\to$ Type. Working with displayed structures rather than morphisms is a technique for enforcing definitional equalities on images in B.

$^3$To see this geometrically, note that the $(n+1)$-dimensional octant $[0, \infty)^{n+1}$ contains a standard face-preserving embedding of the n-simplex, $\Delta^n = \{(x_0, \dots, x_n) \in [0, \infty)^{n+1} \mid x_0 + \dots + x_n = 1\}$, including the augmentation case $\Delta^{-1} = \emptyset$.

9

The most common displayed structure is a displayed category; here the terminology was introduced by [AL19]. This arises from the record type of categories, defined in the usual dependently typed way (where we omit the axioms for concision):

record Cat : Type where
ob : Type
hom : ob → ob → Type
id : (x : ob) → hom x x
comp : {x y z : ob} → hom y z → hom x y → hom x z
...

We do not discuss record types (including  \( \Sigma \) -types) in this paper, but the extension of  \( ^{d} \)  to them produces another record type whose fields have  \( ^{d} \)  applied to them. For instance, from a  \( \Sigma \) -type:

record \(\Sigma (A:\text{Type})\) \((B:A\to \text{Type})\) : Type where  
fst : A  
snd : B fst

We obtain:

record \(\Sigma^d\) (A : Type) (\(A'\) : Type\(^d\) A) (B : A → Type)
(B' : (A → Type)\(^d\) B) : Type\(^d\) (\(\Sigma\) A B) where
fst\(^d\) : A\(^d\) fst
snd\(^d\) : (B fst)\(^d\) snd

Applying (1.4) and the similar rule Type \( ^{d} \)   \( A \equiv A \rightarrow \)  Type, this becomes:

record \(\Sigma^d\) (A : Type) (\(A'\) : A → Type) (B : A → Type)
(B' : (x : A) → \(A'\) x → B x → Type) (s : \(\Sigma\) A B) : Type where
fst\(^d\) : A' (fst s)
snd\(^d\) : B' (fst s) fst\(^d\) (snd s)

In a similar way, the above definition of the record type of categories yields:

record Cat\( ^{d} \) (C : Cat) : Type where
ob\( ^{d} \) : ob C → Type
hom\( ^{d} \) : (x : ob C) (x' : ob\( ^{d} \) x) (y : ob C) (y' : ob\( ^{d} \) y) → hom C x y → Type
id\( ^{d} \) : (x : ob C) (x' : ob\( ^{d} \) x) → hom\( ^{d} \) x x' x x' (id C x)
comp\( ^{d} \) : {x : ob C} {x' : ob\( ^{d} \) x} {y : ob C} {y' : ob\( ^{d} \) y} {z : ob C}
{z' : ob\( ^{d} \) z} (α : hom C y z) (α' : hom\( ^{d} \) y y' z z' α) (β : hom C x y)
(β' : hom\( ^{d} \) x x' y y' β) → hom\( ^{d} \) x x' z z' (comp C α β)
...

Thus a displayed category over C has a type of objects indexed by those of C, types of morphisms indexed by pairs of objects-over-objects and by a morphism of C, identity and composition operations on displayed objects and morphisms that lie strictly over those in C, and similarly for the axioms.

As observed in [AL19], one use of displayed categories is to state definitions such as Grothendieck fibrations in terms of the existence of cartesian liftings strictly over any morphism in C, without internalizing definitional equality. Another is to construct categories and prove their properties in a modular way out of dependent pieces, just as we do for types using  \( \Sigma \) -types and more general records. It is 'well-known' by now that any sort of

10

algebra-categorical structure has a ‘*displayed version*’ — for instance, displayed bicategories were used in [AFM$^{+}$21] to prove univalence modularly — but to our knowledge this has not previously been formalised. Our *Displayed Type Theory (dTT)* automatically generates the displayed version of any notion definable in type theory; hence the name.

**Outline of the paper.** The rest of this paper has three parts. In section 2 we describe the general syntax of dTT, including the modalities, the operation of display (in various different forms), and how they compute. We do not prove any canonicity or normalization results, but we conjecture that they hold.

In section 3 we extend the syntax of dTT to define a type SST of semi-simplicial types. In fact, we obtain this as a special case of a general notion of ‘*displayed coinductive type*’, which is easier to work with abstractly, and also includes other important examples such as the type of semi-simplicial morphisms between two semi-simplicial types.$^{4}$ Then we explore a few applications, to make the point that this coinductive notion of semi-simplicial type is useful and practical.

Finally, in section 4 we consider the semantics of dTT. In particular, we will show that from any model $\mathcal{C}$ of ordinary dependent type theory with countable inverse limits (roughly as considered in [Kra15]), we can construct a model of dTT whose discrete mode is $\mathcal{C}$ and whose simplicial mode is the category of Reedy fibrant augmented semi-simplicial diagrams in $\mathcal{C}$, and that this model supports displayed coinductive types including a type SST of semi-simplicial types. The underlying ordinary type theory of this model at the simplicial mode is an instance of the inverse diagram models of [Shu15, KL21], but we construct it more explicitly by hand so as to be able to verify the needed formulas for the additional operations of dTT.

Thus, although dTT is (apparently) not conservative over ordinary dependent type theory, we can isolate exactly a kind of extra infinitary structure that yields a well-behaved theory for working with semi-simplicial types, which precisely includes the original model at one mode. In particular, by [Shu19] any $(\infty, 1)$-topos can be presented by a type-theoretic model topos, which is a model of type theory with countable inverse limits, and thus also yields a model of dTT. However, an object with the *internal* universal property of SST expressable in dTT has the potential to exist even in models that lack such infinitary limits, which may have implications for a notion of elementary $(\infty, 1)$-topos.

**Acknowledgements.** Both authors would like to thank Tim Campion for bringing the binary ordering to their attention, via a talk given by Emily Riehl on her joint work with Tim. Astra would also like to thank Emily for many discussions in the course of weekly advising meetings. Further, Astra is grateful to Steve Awodey for hosting her during the months of March and April 2023 at Carnegie Mellon University, and Emily for hosting her during the Fall 2023 semester at Johns Hopkins University. Many of the initial ideas regarding the semantics of dTT were developed during the CMU visit, and our construction of the simplicial model was worked out during the JHU visit. Mike is grateful to Thorsten Altenkirch and Ambrus Kaposi for many useful conversations while developing Higher Observational Type Theory that have also informed this work.

$^{4}$One might hope that it would also include the displayed versions SST$^{d}$, SST$^{dd}$, etc., but this does not seem to be the case unless we add symmetry to our theory.

11

## 2 Syntax

As suggested in the introduction, dTT is based on a modal type theory roughly in the style of [GKNB21, GCK+22], with two modes, one for discrete types and one for (augmented semi-)simplicial types. It then adds a notion of 'display' at the simplicial mode that partially internalises unary parametricity.

In addition, the general form of display, which is needed to state the computation rules for simple display, incorporates dependence on an arbitrary telescope (i.e. context extension). Thus, we also have to include a calculus of telescopes in the theory.5 The fully general calculus of telescopes and display involves a lot of operations, but in syntax and in most models they are all definable from a smaller number of primitives.

This section is organised as follows. In section 2.1 we define the mode theory, which is a 2-category describing the structure of the modal operators. Then in section 2.2 we give the rules for the underlying modal type theory, with modalities but not display.

In section 2.3 we introduce the most basic notions of the telescope calculus: telescopes, partial substitutions (elements of telescopes), and types and terms dependent on a specified telescope (which we call 'meta-abstractions'). These basic notions suffice to give the rules for display, defined mutually with a similar but non-indexed operation on telescopes that we call décalage, in section 2.4.

The remaining two sections introduce further operations that are all essentially 'definable' in terms of the previous ones. This is not strictly true at the level of algebraic syntax, where telescopes are just an additional sort of a generalised algebraic theory. But in a model where telescopes are defined to be finite lists of types — which is an option in any model, both the free syntactic model and in semantic models arising from categories — the laws satisfied by these operations characterise them uniquely. Specifically, in section 2.5 we introduce meta-abstracted telescopes, telescope concatenation, and Π-telescopes, and then in section 2.6 we introduce display for telescopes, and décalage for dependent telescopes. These operations will be used in section 3 to formulate displayed coinductive types, including the type of semi-simplicial types.

### 2.1 THE MODE THEORY

We begin with a modal type theory based on the following 2-category ℳ:

- there are two modes (objects), dm for discrete and sm for simplicial
- there are five nonidentity morphisms, forming hom-posets:

$$\begin{array}{lll} \mathcal{M}(\mathrm{dm}, \mathrm{dm}) = \{1_{\mathrm{dm}}\} & \mathcal{M}(\mathrm{dm}, \mathrm{sm}) = \{\triangle\} \\ \mathcal{M}(\mathrm{sm}, \mathrm{dm}) = \{\square \leqslant \diamond\} & \mathcal{M}(\mathrm{sm}, \mathrm{sm}) = \{\triangle\square \leqslant 1_{\mathrm{sm}} \leqslant \triangle\diamond\} \end{array}$$

5It would probably be possible to collapse this to dependence on a single type, using Σ-types instead of telescope extension, as in [ACKS24], but this would be unaesthetic and less practical for implementation.

12

- composition is defined by the following tables (plus identity laws)

|   | \( \nu \circ \rho \) | \( \triangle \) | \( \triangle \diamondsuit \) | \( \triangle \square \)  |
| --- | --- | --- | --- | --- |
|  \( \nu \) | \( \diamondsuit \) | \( 1_{dm} \) | \( \diamondsuit \) | \( \square \)  |
|   |  \( \square \) | \( 1_{dm} \) | \( \diamondsuit \) | \( \square \)  |
|   |  \( \triangle \diamondsuit \) | \( \triangle \) | \( \triangle \diamondsuit \) | \( \triangle \square \)  |
|   |  \( \triangle \square \) | \( \triangle \) | \( \triangle \diamondsuit \) | \( \triangle \square \)  |

|   | \( \nu \circ \rho \) | \( \rho \)  |
| --- | --- | --- |
|  \( \nu \) | \( \triangle \) | \( \triangle \diamondsuit \) \( \triangle \square \)  |

Intuitively, \(\triangle\) takes a discrete type and forms the constant (augmented semi-)simplicial type, while \(\diamond\) takes the \((-1)\)-simplices of an (augmented semi-)simplicial type and \(\square\) takes the limit of an (augmented semi-)simplicial diagram.

One verifies that the following adjunctions hold in M:

\[
\diamondsuit \dashv \triangle \dashv \square
\]

\[
\Delta \diamondsuit \dashv \Delta \square
\]

\[
1 _ {p} \dashv 1 _ {p}
\]

Thus every morphism in \(\mathcal{M}\), except for \(\diamond\) and \(\triangle\diamond\), has a right adjoint. We refer to the morphisms \(\diamond\) and \(\triangle\diamond\) as hazardous, and the others safe.

### 2.2 THE MODAL TYPE THEORY

The basic syntactic structure of dTT follows MTT [GKNB21]. Following Coquand, we parametrize the type judgment by a universe level; we assume these form a linear hierarchy generated by lzero and lsuc, with a join operation \(\sqcup\), giving the judgement \(\ell\) level. Each mode has its contexts, substitutions, types, and terms, so we have the following judgements where p denotes an arbitrary mode (dm or sm).

\[
\Gamma \operatorname{ctx} _ {p}
\]

\[
\Gamma \vdash_ {p} A \text { type } _ {\ell}
\]

\[
\Gamma \vdash_ {p} t: A
\]

\[
\theta : \Gamma \Rightarrow_ {p} \Theta
\]

Formally speaking, the inference rules we will give below for these judgments should be interpreted as defining a Generalised Algebraic Theory with these four generating sorts. Later, we will also introduce some additional sorts.

#### 2.2.1 Contexts

Contexts are built up from the empty contexts by extending with modally annotated variables and applying locks associated to modalities:

\[
\frac {\text { p   mode }}{\left(\right) _ {p} \text { ctx } _ {p}}
\]

\[
\frac {\mu : p \to q \quad \Gamma \operatorname{ctx} _ {q}}{(\Gamma , \widehat {\mathbf {u}} _ {\mu}) \operatorname{ctx} _ {p}}
\]

\[
\frac {\mu : p \to q \qquad \Gamma \operatorname{ctx} _ {q} \qquad \Gamma , \widehat {\mathbf {u}} _ {\mu} \vdash_ {p} A \text {type} _ {\ell}}{(\Gamma , x : ^ {\mu} A) \operatorname{ctx} _ {q}}
\]

We additionally enforce the functoriality of locking, and the fact that some locks preserve empty contexts.

\[
\left(\Gamma , \widehat {\mathbf {u}} _ {1 _ {p}}\right) \equiv \Gamma
\]

\[
(\Gamma , \widehat {\mathbf {u}} _ {\mu}, \widehat {\mathbf {u}} _ {\nu}) \equiv (\Gamma , \widehat {\mathbf {u}} _ {\mu \circ \nu})
\]

\[
\left(\left(\right) _ {d m}, \widehat {\mathbf {u}} _ {\square}\right) \equiv \left(\right) _ {s m}
\]

\[
\left(\left(\right) _ {s m}, \widehat {\mathbf {u}} _ {\triangle}\right) \equiv \left(\right) _ {d m}
\]

In fact, the last equality follows from the other three, since \((\mathbf{()}_{\mathrm{sm}},\widehat{\mathbf{u}}_{\triangle}) = (\mathbf{()}_{\mathrm{dm}},\widehat{\mathbf{u}}_{\square},\widehat{\mathbf{u}}_{\triangle}) = (\mathbf{()}_{\mathrm{dm}},\widehat{\mathbf{u}}_{\square \circ \triangle}) = (\mathbf{()}_{\mathrm{dm}},\widehat{\mathbf{u}}_{\mathrm{dm}}) = (\mathbf{()}_{\mathrm{dm}}.\) Note that \(\widehat{\mathbf{u}}_{\diamond}\) does not preserve empty contexts.

13

These equalities mean that contexts no longer have a unique presentation using the above rules. However, there are ways to select a canonical presentation for any context. One is to interpret the above equalities as directed rewrites and work with context presentations that are normal for this rewriting system; thus there are no identity locks, no repeated locks, and $\widehat{\bullet}_{\square}$ and $\widehat{\bullet}_{\triangle}$ never occur immediately after an empty context. Another way is to require that exactly one lock appears in between any two variables.

Semantically, each lock is left adjoint to its corresponding modality. Thus, $\widehat{\bullet}_{\square}$ is semantically the same as $\triangle$, while $\widehat{\bullet}_{\triangle}$ is semantically the same as $\diamond$. The other lock, $\widehat{\bullet}_{\diamond}$, is not reified internally by a modality: intuitively, it takes a discrete type and makes it an (augmented semi-)simplicial type that is empty at all dimensions $n > -1$.

In particular, $\widehat{\bullet}_{\square}$ and $\widehat{\bullet}_{\triangle}$ have the further left adjoints $\widehat{\bullet}_{\triangle}$ and $\widehat{\bullet}_{\diamond}$, respectively, so that we will be able to represent their modalities $\square$ and $\triangle$ in Fitch-style as in [GCK$^{+}$22, Shu23].

As far as $\widehat{\bullet}_{\diamond}$ goes, we can say that it is fully faithful and hence an equivalence onto its image, which consists of the simplicial types that are empty in dimensions $n > -1$. Moreover, since the initial object is strict, this subcategory is a sieve: if we have a morphism $\Gamma \to \Delta$ and $\Delta$ lies in this subcategory, then so does $\Gamma$. Therefore, while $\widehat{\bullet}_{\diamond}$ is not a right adjoint, it is a parametric right adjoint, so we can still use the method of of [GCK$^{+}$22] for $\diamond$.

However, rather than postulating an uninterpreted parametric left adjoint of $\widehat{\bullet}_{\diamond}$ as in [GCK$^{+}$22], we can use our knowledge about how this left adjoint is defined semantically to give more specific rules. Specifically, we can identify its domain as the subcategory of contexts in the essential image of $\widehat{\bullet}_{\diamond}$, and on that subcategory the left adjoint actually coincides with $\widehat{\bullet}_{\triangle}$. To represent this semantically, we say that an sm-context is flat if, intuitively, it contains a $\widehat{\bullet}_{\diamond}$ which is not to the left of any $\widehat{\bullet}_{\triangle}$. Formally, flatness is a predicate on contexts (an additional sort of the GAT) characterised by the following rules:

$$\frac{\Gamma \operatorname{ctx}_{\mathrm{dm}}}{(\Gamma, \widehat{\bullet}_{\diamond}) \operatorname{flat}} \qquad \frac{\Gamma \operatorname{ctx}_{\mathrm{sm}} \quad \Gamma \operatorname{flat} \quad \mu : p \to \mathrm{sm} \quad \Gamma, \widehat{\bullet}_{\mu} \vdash_p A \operatorname{type}_\ell}{(\Gamma, x :^\mu A) \operatorname{flat}}$$

Semantically, we think of these as the sm-contexts that are empty above dimension $n > -1$, on which the parametric left adjoint of $\widehat{\bullet}_{\diamond}$ will act as $\widehat{\bullet}_{\triangle}$. (In our actual model we will do something more clever to avoid assuming the existence of strict initial objects.)

### 2.2.2 Substitutions

The judgment $\theta : \Gamma \Rightarrow_p \Theta$ says that $\theta$ is a substitution from context $\Gamma$ to context $\Theta$ at mode $p$. It is generated by the following generating rules, which are the same as those given for MTT in [GKNB21]

$$\frac{\frac{\Gamma \operatorname{ctx}_p}{\Gamma : \Gamma \Rightarrow_p \Gamma} \quad \frac{\Gamma \operatorname{ctx}_p}{[\Gamma]_p : \Gamma \Rightarrow_p \Gamma)_p} \quad \frac{\mu : p \to q \quad \Gamma \operatorname{ctx}_q \quad \Gamma, \widehat{\bullet}_{\mu} \vdash_p A \operatorname{type}_\ell}{\uparrow^{x:^\mu A} : (\Gamma, x :^\mu A) \Rightarrow_q \Gamma}$$
$$\frac{\theta : \Gamma \Rightarrow_p \Theta \quad \nu : \Theta \Rightarrow_p \Upsilon}{\nu \circ \theta : \Gamma \Rightarrow_p \Upsilon} \quad \frac{\theta : \Gamma \Rightarrow_q \Theta \quad \Gamma, \widehat{\bullet}_{\mu} \vdash_p t : A [\theta, \widehat{\bullet}_{\mu}]}{[\theta, t] : \Gamma \Rightarrow_q (\Theta, x :^\mu A)}$$
$$\frac{\theta : \Gamma \Rightarrow_q \Theta}{[\theta, \widehat{\bullet}_{\mu}] : (\Gamma, \widehat{\bullet}_{\mu}) \Rightarrow_p (\Theta, \widehat{\bullet}_{\mu})} \quad \frac{\mu \leqslant \nu}{\widehat{\bullet}_{\bullet}^{\mu \leqslant \nu} : (\Gamma, \widehat{\bullet}_{\nu}) \Rightarrow_p (\Gamma, \widehat{\bullet}_{\mu})}$$

14

With the exceptional rule $\mathcal{Q}^{\triangle\diamond\geqslant 1_{sm}}$, which represents the fact that semantically $\mathcal{Q}_{\triangle\diamond}$ acts as the identity on flat contexts:

$$\frac{\Gamma \text{ flat}}{\mathcal{Q}^{\triangle\diamond\geqslant 1_{sm}} : \Gamma \Rightarrow_{\text{sm}} (\Gamma, \mathcal{Q}_{\triangle\diamond})}$$

In practice, it is useful to iterate the weakening rule and combine it with the lock and key rules to obtain the following rule:

$$\frac{\theta : \Gamma \Rightarrow_q \Theta \quad \mu \leqslant \text{locks}(\Upsilon)}{[\theta, \uparrow_\mu^\Upsilon] : (\Gamma, \Upsilon) \Rightarrow_p (\Theta, \mathcal{Q}_\mu)}$$

In fact, we will generally use named variables and leave weakening implicit.

◁

### 2.2.3 Types

These are defined by several classes of type formers, including, at the most basic level: $\Pi$-types (parametrised by a modality, as in MTT), universes (at each mode), and modal operators.

$$\frac{\Gamma, \mathcal{Q}_\mu \vdash_p A \text{ type}_{\ell_1} \quad \Gamma, x :^\mu A \vdash_q B \text{ type}_{\ell_2}}{\Gamma \vdash_q (x :^\mu A) \to B \text{ type}_{\ell_1 \sqcup \ell_2}}$$

$$\frac{\ell \text{ level}}{\Gamma \vdash_{dm} \text{Disc}_\ell \text{ type}_{\text{lsuc } \ell}}$$

$$\frac{\ell \text{ level}}{\Gamma \vdash_{sm} \text{Type}_\ell \text{ type}_{\text{lsuc } \ell}}$$

$$\frac{\Gamma, \mathcal{Q}_\square \vdash_{sm} A \text{ type}_\ell}{\Gamma \vdash_{dm} \square A \text{ type}_\ell}$$

$$\frac{\Gamma, \mathcal{Q}_\triangle \vdash_{dm} A \text{ type}_\ell}{\Gamma \vdash_{sm} \triangle A \text{ type}_\ell}$$

$$\frac{\Gamma, \mathcal{Q}_\diamond \vdash_{sm} A \text{ type}_\ell}{\Gamma \vdash_{dm} \diamond A \text{ type}_\ell}$$

We don't bother with primitive modal operators $\triangle\diamond$ or $\triangle\square$, since they can be obtained up to isomorphism by composing the others.

We will work with Tarski style universes, and thus require a decoding operation:

$$\frac{\Gamma \vdash_{dm} A : \text{Disc}_\ell}{\Gamma \vdash_{dm} \text{EI } A \text{ type}_\ell}$$

$$\frac{\Gamma \vdash_{sm} A : \text{Type}_\ell}{\Gamma \vdash_{sm} \text{EI } A \text{ type}_\ell}$$

Finally, we also have types that arise from substitution:

$$\frac{\theta : \Gamma \Rightarrow_p \Theta \quad \Theta \vdash_p A \text{ type}_\ell}{\Gamma \vdash_p A [\theta] \text{ type}_\ell}$$

As usual, substitution will be 'eliminable' in that $A [\theta]$ is always equal to something not involving $[\theta]$, but in the GAT presentation it is one of the generating rules like the others. ◁

### 2.2.4 Terms

Terms are defined for each class of type former through introduction and elimination rules. But first, we have variables. There are two rules for variables: the ordinary one from MTT,

15

and an 'exceptional' one arising, like the exceptional key $\mathbf{a}_{\bullet}^{\triangle\diamond\geqslant1_{sm}}$, from the fact that $\mathbf{a}_{\triangle\diamond}$ acts as the identity on flat contexts.

$$\frac{\mu \leqslant \text{locks}(\Theta)}{\Gamma, x:^{\mu}A, \Theta \vdash_q x: A [1_\Gamma, \uparrow_{\mu}^{x:^{\mu}A, \Theta}]}$$

$$\frac{\Gamma \text{ flat } \quad \text{locks}(\Theta) = 1_{sm}}{\Gamma, x:^{\triangle\diamond}A, \Theta \vdash_{sm} x: A [1_\Gamma, \uparrow_{\triangle\diamond}^{x:^{\triangle\diamond}A, \Theta}] [\mathbf{a}_{\bullet}^{\triangle\diamond\geqslant1_{sm}}]}$$

For $\Pi$-types, we have (as in MTT):

$$\frac{\Gamma, x:^{\mu}A \vdash_q t: B}{\Gamma \vdash_q \lambda x.t: (x:^{\mu}A) \to B}$$

$$\frac{\Gamma \vdash_q f: (x:^{\mu}A) \to B \quad \Gamma, \mathbf{a}_{\mu} \vdash_p a: A}{\Gamma \vdash_q f a: B [a/x]}$$

For universes, we have a coding function:

$$\frac{\Gamma \vdash_{dm} A \text{ type}_\ell}{\Gamma \vdash_{dm} \text{Code } A: \text{Disc}_\ell}$$

$$\frac{\Gamma \vdash_{sm} A \text{ type}_\ell}{\Gamma \vdash_{sm} \text{Code } A: \text{Type}_\ell}$$

For the modal operators, we have an introduction rule and negative 'Fitch-style' elimination rules. Following [GCK$^+$22], we formulate these using parametric adjoints in the mode theory. As noted in section 2.1, the safe modalities have actual left adjoints, so their rules simplify as in [Shu23]. And for $\mathbf{a}_{\diamond}$, we have observed that its parametric left adjoint is defined on the flat contexts, and on those it coincides with $\mathbf{a}_{\triangle}$.

$$\frac{\Gamma, \mathbf{a}_{\square} \vdash_{sm} t: A}{\Gamma \vdash_{dm} \square t: \square A}$$

$$\frac{\Gamma, \mathbf{a}_{\triangle} \vdash_{dm} t: A}{\Gamma \vdash_{sm} \triangle t: \triangle A}$$

$$\frac{\Gamma, \mathbf{a}_{\diamond} \vdash_{sm} t: A}{\Gamma \vdash_{dm} \diamond t: \diamond A}$$

$$\frac{\Gamma, \mathbf{a}_{\triangle} \vdash_{dm} t: \square A}{\Gamma \vdash_{sm} \blacksquare^A t: A [\mathbf{a}_{\bullet}^{\triangle\square\leqslant1_{sm}}]}$$

$$\frac{\Gamma, \mathbf{a}_{\diamond} \vdash_{sm} t: \triangle A}{\Gamma \vdash_{dm} \blacktriangle^A t: A}$$

$$\frac{\Gamma \text{ flat } \quad \Gamma, \mathbf{a}_{\triangle} \vdash_{dm} t: \diamond A}{\Gamma \vdash_{sm} \blacklozenge^A t: A [\mathbf{a}_{\bullet}^{\triangle\diamond\geqslant1_{sm}}]}$$

Finally, we have terms that arise from substitution:

$$\frac{\theta: \Gamma \Rightarrow_p \Theta \quad \Theta \vdash_p t: A}{\Gamma \vdash_p t [\theta]: A [\theta]}$$

## 2.3 TELESCOPES AND META-ABSTRACTIONS, I

### 2.3.1 Telescopes

Telescopes are suffixes of contexts, with the restriction that they may not contain locks. The judgement $\Gamma \vdash_p \Theta \text{tel}_\ell$ denotes that $\Theta$ is a telescope in context $\Gamma$ of 'level $\ell$', where the latter means that $\ell$ is greater than or equal to the level of the types occurring in $\Theta$. We allow it to be strictly greater, and in particular allow an empty telescope to exist at all universe levels, for a reason to be explained in section 2.6.3. Formally, telescopes are an additional level-indexed sort of the GAT, with formation rules saying that there is an empty one and they can be built by concatenating types.

$$\frac{\Gamma \text{ctx}_p}{\Gamma \vdash_p ()_p \text{tel}_\ell}$$

$$\frac{\mu: p \to q \quad \Gamma \vdash_q \Theta \text{tel}_\ell \quad \Gamma \mid \Theta, \mathbf{a}_{\mu} \vdash_p A \text{type}_{\ell'} \quad \ell' \leqslant \ell}{\Gamma \vdash_q (\Theta, x:^{\mu}A) \text{tel}_\ell}$$

16

Just as with ordinary contexts, we regard these rules as generating telescopes 'inductively', although this is not formally the case syntactically. We thus regard some other operation on telescopes as 'defined' when we specify rules for how it computes on these forms. This is justified in most models, where we do actually define the judgment of telescopes inductively by the above rules.

For example, the premise of the second rule above requires knowing how to extend a context by a telescope. We write this with a distinctive notation as $\Gamma \mid \Theta$, from which the reader can infer that $\Theta$ is a telescope. Since $\mid$ is an operation on contexts, not a constructor of contexts, it computes on the constructors of telescopes:

$$\frac{\Gamma \vdash_p \Theta \text{tel}_\ell}{(\Gamma \mid \Theta) \text{ctx}} \quad (\Gamma \mid ()_p) \equiv \Gamma \quad (\Gamma \mid (\Theta, x :^\mu A)) \equiv ((\Gamma \mid \Theta), x :^\mu A)$$

We consider the operation $\mid$ to be left-associative with the comma. Thus, for instance, the context $\Gamma \mid \Theta$, $\bullet_\mu$ in the rule for extending a telescope by a type means $(\Gamma \mid \Theta)$, $\bullet_\mu$.

By a strict telescope we mean a telescope without any nontrivially modal variables.

$$\frac{\Gamma \text{ctx}_p}{\Gamma \vdash_p ()_p \text{stel}_\ell} \quad \frac{\Gamma \vdash_p \Theta \text{stel}_\ell \quad \Gamma \mid \Theta \vdash_p A \text{type}_{\ell'} \quad \ell' \leqslant \ell}{\Gamma \vdash_p (\Theta, x :^\mu A) \text{stel}_\ell}$$

As is evident, we do not distinguish syntactically between general telescopes and strict ones. That is, we consider strictness to be a mere property of a telescope, or alternatively we treat the obvious map from strict telescopes to telescopes as an implicit coercion.

Similarly, we can introduce a 'lifting' operation taking a telescope to any higher level.

$$\frac{\Gamma \vdash_p \Theta \text{tel}_\ell \quad \ell \leqslant \ell'}{\Gamma \vdash_p \Theta \text{tel}_{\ell'}}$$

As is evident from the notation, we also treat this as an implicit coercion. Thus, when we define it recursively on the structure of a telescope, the rules look trivial unless we annotate them somehow with levels:

$$()_p \equiv ()_p \quad (\Theta, x :^\mu A) \equiv (\Theta, x :^\mu A) \quad \triangleleft$$

### 2.3.2 Partial substitutions

If $\Gamma \vdash \Upsilon \text{tel}_\ell$ there is a judgment $\Gamma \vdash \sigma : \Upsilon$ for the 'elements' of $\Upsilon$. We call such $\sigma$ a 'partial substitution', thinking of it as a substitution $\Gamma \Rightarrow (\Gamma \mid \Upsilon)$ that is the identity on $\Gamma$. Formally, we specify that they can be built out of terms:

$$\frac{\Gamma \vdash_q \sigma : \Upsilon \quad \Gamma \mid \Upsilon, \bullet_\mu \vdash_p A \text{type}_\ell \quad \Gamma, \bullet_\mu \vdash_p t : A [1_\Gamma \mid \sigma, \bullet_\mu]}{\Gamma \vdash_p [\sigma, t] : (\Upsilon, x :^\mu A)}$$

The second rule involves a notion of extending an ordinary substitution by a partial one.

$$\frac{\theta : \Gamma \Rightarrow_p \Delta \quad \Delta \vdash_p \Upsilon \text{tel}_\ell \quad \Gamma \vdash_p \sigma : \Upsilon [\theta]}{[\theta \mid \sigma] : \Gamma \Rightarrow_p (\Delta \mid \Upsilon)} \quad [\theta \mid []_p] \equiv \theta$$

$$[\theta \mid [\sigma, t]] \equiv [[\theta \mid \sigma], t]$$

17

This gives a simple way to ensure that partial substitutions are uniquely determined by their components: their equality is detected by equality of the induced substitutions.

$$\frac{\Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon \qquad \Gamma \vdash_{\mathrm{p}} \tau : \Upsilon \qquad [1_{\Gamma} \mid \sigma] \equiv [1_{\Gamma} \mid \tau] : \Gamma \Rightarrow_{\mathrm{p}} (\Gamma \mid \Upsilon)}{\Gamma \vdash_{\mathrm{p}} \sigma \equiv \tau : \Upsilon}$$

Note that a partial substitution does, in fact, have 'components': given $\Gamma \vdash_{\mathrm{q}} \sigma : (\Upsilon, x :^{\mu} A)$ we have

$$[1_{\Gamma} \mid \sigma, x, \mathbf{\Omega}_{\mu}] : (\Gamma, \mathbf{\Omega}_{\mu}) \rightarrow (\Gamma \mid \Upsilon, x :^{\mu} A, \mathbf{\Omega}_{\mu})$$

$$\Gamma \mid \Upsilon, x :^{\mu} A, \mathbf{\Omega}_{\mu} \vdash x : A$$

$$\Gamma, \mathbf{\Omega}_{\mu} \vdash x [1_{\Gamma} \mid \sigma, x, \mathbf{\Omega}_{\mu}] : A$$

We also have a notion of weakening for telescopes. As before, we omit the equations that this must satisfy.

$$\frac{\Gamma \vdash \Theta \operatorname{tel}_{\ell}}{\uparrow^{\Theta} : (\Gamma \mid \Theta) \Rightarrow \Gamma} \qquad \uparrow^{(\cdot)_{\mathrm{p}}} \equiv 1_{\Gamma} \qquad \uparrow^{\Theta, x :^{\mu} A} \equiv \uparrow^{\Theta} \circ \uparrow^{x :^{\mu} A} \qquad \triangleleft$$

### 2.3.3 Meta-abstracted types and terms

We now introduce a new judgement form $\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon}$, where $\Gamma \vdash \Upsilon \operatorname{tel}_{\ell_0}$. This should be thought of saying that $A$ is a type depending on the variables $\upsilon$ in $\Upsilon$, i.e. belonging to a 'framework-level $\Pi$-type' $A : (\upsilon : \Upsilon) \rightarrow \operatorname{type}_{\ell_1}$. Accordingly, elements of this judgment are introduced by binding and eliminated by application, with a $\beta$ and $\eta$-rule.

$$\frac{\Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1}}{\Gamma \vdash_{\mathrm{p}} ((A))_{\upsilon : \Upsilon} \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon}} \qquad \frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} A \sigma \operatorname{type}_{\ell_1}}$$

$$\frac{\Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} ((A))_{\upsilon : \Upsilon} \sigma \equiv A [1_{\Gamma} \mid \sigma]}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} B \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} A \upsilon \equiv B \upsilon}{\Gamma \vdash_{\mathrm{p}} A \equiv B}$$

We also regard $A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon}$ as standing in for its own $\Pi$-type '$(\upsilon : \Upsilon) \rightarrow A \upsilon$'. Thus, such an $A$ can have its own terms belonging to it, which are also introduced by binding and eliminated by application, with a $\beta$ and $\eta$-rule.

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} t : A \upsilon}{\Gamma \vdash_{\mathrm{p}} [t]_{\upsilon : \Upsilon} : ((A))_{\upsilon : \Upsilon}}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} t : A \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} t \sigma : A \sigma \operatorname{type}_{\ell_1}}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} t : A \upsilon \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} [t]_{\upsilon : \Upsilon} \sigma \equiv t [1_{\Gamma} \mid \sigma]}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} t : A \qquad \Gamma \vdash_{\mathrm{p}} s : A \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} t \upsilon \equiv s \upsilon}{\Gamma \vdash_{\mathrm{p}} t \equiv s} \qquad \triangleleft$$

18

## 2.4 DÉCALAGE AND DISPLAYED TYPES

Semantically, the fundamental operation is shifting the dimensions of a simplicial type. In classical simplicial homotopy theory, this is called décalage:

$$\left(A^{D}\right)_{n}=A_{n+1}$$

The simplicial structure maps of $A^{D}$ are a subset of those of $A$, while the unused ones assemble into a simplicial map $A^{D} \to A$. When $A$ is a type at mode sm, we will regard $A^{D}$ as the projection from a type $A^{d}$ dependent on $A$; thus we have

$$A^{D}=(x:A, x':A^{d}x)$$

(Semantically, this is validated by the fact that if $A$ is Reedy fibrant, then the map $A^{D} \to A$ is a Reedy fibration.) These dependent types $A^{d}$, which we call display, are our version of the 'logical relations' assigned to every type by an internal parametricity theory.

### 2.4.1 Display for types

In contrast to fully internal parametricity theories, because we don't have degeneracies in our cube category, décalage and display can only be applied in restricted contexts. In external parametricity, the logical relations apply only to types in the empty context; but our modalities allow us to say more generally that they apply to any 'boxed' type. Here by 'box' we mean not $\square$ but the corresponding endofunctor of the simplicial mode, namely $\triangle\square$. Thus, informally display should have the type $d: (A:\triangle\square \text{Type}_{\ell}) \to A \to \text{Type}_{\ell}$, with computability witnesses being assigned by a function $d: (A:\triangle\square \text{Type}_{\ell})(x:\triangle\square A) \to A^{d}x$. If we reformulate these without referring to $\Pi$-types, we obtain the following rules for our basic notion of displayed type:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle\square} \vdash_{sm} A \text{ type}_{\ell} \quad \Gamma \vdash_{sm} t: A \left[ \mathbf{a}_{\ell}^{\triangle\square \leqslant 1_{sm}} \right]}{\Gamma \vdash_{sm} A^{d} \text{ type}_{\ell}} \quad \frac{\Gamma, \widehat{\mathbf{a}}_{\triangle\square} \vdash_{sm} t: A}{\Gamma \vdash t^{d}: A^{d} \left( t \left[ \mathbf{a}_{\ell}^{\triangle\square \leqslant 1_{sm}} \right] \right)}$$

However, in order to compute with this, we need a version of it that incorporates dependence on a telescope to the right of the lock. The corresponding action on that telescope is called décalage.

### 2.4.2 Telescope décalage

As noted above, with display $A^{d}$ defined as dependent on $A$, décalage $A^{D}$ is naturally not a single type but a telescope. It is therefore natural to generalise its input to be a telescope also. This yields an operation that doubles the variables and groups each type with its displayed version, e.g.

$$(x:A, y:B)^{D} \equiv (x:A, x':A^{d}x, y:B, y':B^{d}y).$$

The classical projection from décalage to the identity, composed of the leftover face maps, becomes an 'evens' substitution $\Upsilon^{D} \to \Upsilon$ that throws away the elements of the displayed

19

types (the primed variables in the above example). (The corresponding 'odds' substitution must wait until we introduce telescope display in section 2.6.3.)

$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \Upsilon \text{ tel}_\ell}{\Gamma \vdash_{sm} \Upsilon^D \text{ tel}_\ell} \quad \frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \Upsilon \text{ tel}_\ell \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \sigma : \Upsilon}{\Gamma \vdash_{sm} \sigma^D : \Upsilon^D}$$
$$\frac{\Gamma \vdash_{sm} \sigma^+ : \Upsilon^D}{\Gamma \vdash_{sm} \sigma^{+ev} : \Upsilon [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ]} \quad \sigma^{D \text{ ev}} \equiv \sigma [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ]$$

Notationally, we put a superscript '+' on variables and metavariables belonging to décalaged telescopes, and a prime on variables belonging to displayed types and telescopes. These symbols are part of the variable name, e.g. $\sigma^+$ above is a single variable that just happens to be named mnemonically.

At this point we can assert that décalage preserves empty telescopes.

$$()_{sm}^D \equiv ()_{sm} \quad [ ]_{sm}^D \equiv [ ]_{sm} \quad [ ]_{sm}^{ev} \equiv [ ]_{sm}$$

Décalage will also compute on telescopes extended by a type, but we wait to give these rules in section 2.4.4, since they require more structure.

### 2.4.3 Display for meta-abstractions

The more general version of display alluded to above can informally be thought of as having the following rule:

$$\mathcal{L} \quad \frac{\Gamma, \text{ \textpermil}_{\Delta\square} | \Upsilon \vdash_{sm} A \text{ type}_\ell}{\Gamma | \Upsilon^D, a : A \vdash_{sm} A^d a \text{ type}_\ell} \quad ?$$

However, this is not a well-behaved rule because the context of the conclusion is not fully general. There are multiple ways to solve this problem; we will solve it by saying that general display acts on a meta-abstracted type.

$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon}{\Gamma \vdash_{sm} A^d \text{ type}_{\ell_1} / v^+ : \Upsilon^D, a : A [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ] v^{+ev}}$$
$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} t : A}{\Gamma \vdash_{sm} t^d : \left( \left( A^d v^+ (t v^{+ev}) \right) \right)_{v^+ : \Upsilon^D}}$$

In general, this does not reduce to ordinary display, but it does when applied to a décalaged partial substitution.

$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \sigma : \Upsilon \quad \Gamma \vdash t : (A \sigma) [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ]}{\Gamma \vdash A^d \sigma^D t \equiv (A \sigma)^d t}$$
$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \sigma : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} t : A}{\Gamma \vdash t^d \sigma^D \equiv (t \sigma)^d}$$

In particular, when $\Upsilon \equiv ()_{sm}$ these rules say that display for trivial meta-abstractions is equivalent to ordinary display.

20

### 2.4.4 Computing décalage

Now we can give the rules 'defining' telescope décalage on telescopes extended by a variable. Specifically, when extending by a non-modal variable, we also extend by its displayed version. But that displayed version needs to depend on $\Theta^D$, so we define it in terms of display for meta-abstractions. Note that the well-typedness of $t^d$ in these rules depends on the reduction of meta-abstraction display on displayed partial substitutions.

$$(\theta : \Theta, x : A)^D \equiv (\theta^+ : \Theta^D, x : A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | \theta^{+ev}], x' : ((A))_{\theta : \Theta^d} \theta^+ x)$$

$$[\sigma, t]^D \equiv [\sigma^D, t, t^d]$$

$$[\sigma^+, t, t']^{ev} \equiv [\sigma^{+ev}, t]$$

The case of a nontrivially modal variable is actually simpler. Note that in this case, the modality must be of the form $\triangle \circ \mu$. Recalling that semantically, $\triangle$ constructs a constant simplicial type, we should have informally $(\triangle A)^D = \triangle A$, and therefore $(\triangle A)^d$ is trivial. For an action on types, this would mean that $(\triangle A)^d x$ is the unit type; for our current action on telescopes, it means we can just omit the displayed variables.

$$(\theta : \Theta, x : ^{\triangle\circ\mu} A)^D \equiv (\theta^+ : \Theta^D, x : ^{\triangle\circ\mu} A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | \theta^{+ev}, \mathbf{Q}_{\triangle\circ\mu}])$$

$$[\sigma, t]^D \equiv [\sigma^D, t]$$

$$[\sigma^+, t]^{ev} \equiv [\sigma^{+ev}, t]$$

◁

### 2.4.5 Computing display

Recall from section 1 that we treat display computationally like the identity types of HOTT, so that it computes on the basic type-formers. Note that the abstracting telescope changes as we compute, so these rules could not be stated for ordinary display alone.

#### 2.4.5.1 Non-modal $\Pi$-Types

This rule represents the traditional behavior of parametricity and logical relations on functions: a computability witness for a function says that it preserves computability witnesses.

$$\left( (x : A) \to B \right)_{v : \gamma^d} \equiv \left( \left( x : A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | v^{+ev}] \right) (x' : ((A))_{v : \gamma^d} v^+ x) \to \right.$$

$$\left. \left( (B)_{v : \gamma, x : A}^d v^+ x x' (f x) \right)_{v^+ : \gamma^D, f : (x : A) \to B} \right.$$

$$\llbracket \lambda x . t \rrbracket_{v : \gamma^d} \equiv \llbracket \lambda x x'. \llbracket t \rrbracket_{v : \gamma, x : A}^d v^+ x x' \rrbracket_{v^+ : \gamma^D}$$

$$\llbracket f a \rrbracket_{v : \gamma^d} \equiv \llbracket (\llbracket f \rrbracket_{v : \gamma^d} v^+) a (\llbracket a \rrbracket_{v : \gamma^d} v^+) \rrbracket_{v^+ : \gamma^D}$$

#### 2.4.5.2 Nontrivially modal $\Pi$-Types

As with décalage, here we use the fact that display of $\triangle$ is trivial. Note also that here a modal variable appears in the domain of a meta-abstraction. This is the reason that we cannot restrict to strict telescopes in general.

$$\left( (x : ^{\triangle\circ\mu} A) \to B \right)_{v : \gamma^d} \equiv \left( \left( x : ^{\triangle\circ\mu} A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | v^{+ev}, \mathbf{Q}_{\triangle\circ\mu}] \right) \to \right.$$

$$\left. \left( (B)_{v : \gamma, x : ^{\triangle\circ\mu} A}^d v^+ x (f x) \right)_{v^+ : \gamma^D, f : (x : ^{\triangle\circ\mu} A) \to B} \right.$$

$$\llbracket \lambda x . t \rrbracket_{v : \gamma^d} \equiv \llbracket \lambda x. \llbracket t \rrbracket_{v : \gamma, x : ^{\triangle\circ\mu} A}^d v^+ x \rrbracket_{v^+ : \gamma^D}$$

$$\llbracket f a \rrbracket_{v : \gamma^d} \equiv \llbracket \llbracket f \rrbracket_{v : \gamma^d} v^+ a \rrbracket_{v^+ : \gamma^D}$$

21

2.4.5.3 Universes As with \(\Pi\)-types, this rule represents the traditional behavior of parametricity and logical relations on universes: a computability witness for a type is a relation on that type.

\[
\left(\left(\text { Type } _ {\ell}\right)\right) _ {v: \Upsilon^ {d}} \equiv \left(\left(\text { El   A } \rightarrow \text { Type } _ {\ell}\right)\right) _ {v ^ {+}: \Upsilon^ {0}, A: \text { Type } _ {\ell}}
\]

\[
\llbracket \text {Code} A \rrbracket_ {v: \Upsilon^ {d}} \equiv \llbracket \lambda a. \text {Code} \left(\llbracket A \rrbracket_ {v: \Upsilon^ {d}} v ^ {+} a\right) \rrbracket_ {v ^ {+}: \Upsilon^ {0}}
\]

\[
\left(\left(\text {El} A\right)\right) _ {v: \Upsilon^ {d}} \equiv \left(\left(\text {El} \left(\llbracket A \rrbracket_ {v: \Upsilon^ {d}} v ^ {+} a\right)\right)\right) _ {v ^ {+}: \Upsilon^ {0}, a: \text {El} A}
\]

### 2.5 TELESCOPES AND META-ABSTRACTIONS, II

The rules given so far essentially suffice to characterise the basic theory of dTT. However, in order to formulate our definition of semi-simplicial types, we need a bit more structure. To this end, in this section we introduce some more operations on telescopes that can be 'defined' in terms of those already given.

#### 2.5.1 Meta-abstracted telescopes

We start with another judgement form \(\Gamma \vdash_{\mathfrak{p}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon}\) for a telescope dependent on a telescope, with rules entirely analogous to those for types and terms in section 2.3.3.

\[
\frac {\Gamma \mid (v : \Upsilon) \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}}}{\Gamma \vdash_ {p} ((\Phi)) _ {v : \Upsilon} \operatorname{tel} _ {\ell_ {1} / v : \Upsilon}} \quad \frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1} / v : \Upsilon} \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} \Phi \sigma \operatorname{tel} _ {\ell_ {1}}}
\]

\[
\frac {\Gamma \mid (v : \Upsilon) \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} ((\Phi)) _ {v : \Upsilon} \sigma \equiv \Phi [ 1 _ {\Gamma} | \sigma ]}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma \vdash_ {p} \Psi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma | (v : \Upsilon) \vdash_ {p} \Phi v \equiv \Psi v}{\Gamma \vdash_ {p} \Phi \equiv \Psi}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma | (v : \Upsilon) \vdash_ {p} t : \Phi v}{\Gamma \vdash_ {p} [ [ t ] ] _ {v : \Upsilon} : ((\Phi)) _ {v : \Upsilon}}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma \vdash_ {p} t : \Phi \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} t \sigma : \Phi \sigma \operatorname{tel} _ {\ell_ {1}}}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma | (v : \Upsilon) \vdash_ {p} t : \Phi v \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} [ [ t ] ] _ {v : \Upsilon} \sigma \equiv t [ 1 _ {\Gamma} | \sigma ]}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma \vdash_ {p} t : \Phi \quad \Gamma \vdash_ {p} s : \Phi \quad \Gamma | (v : \Upsilon) \vdash_ {p} t v \equiv s v}{\Gamma \vdash_ {p} t \equiv s}
\]

#### 2.5.2 Telescope concatenation

Telescope concatenation is not necessary for the syntactic definition of SSTs, but seems to be required for a clean description of the semantics. It is essentially a  \( \Sigma \) -type for telescopes, which is definitionally associative with context and telescope extension.

22

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid \Upsilon \vdash \Phi \text{ tel}_{\ell_1}}{\Gamma \vdash (\Upsilon \mid \Phi) \text{ tel}_{\ell_0 \sqcup \ell_1}} \quad \frac{\Gamma \vdash \sigma : \Upsilon \quad \Gamma \vdash \delta : \Phi [1_\Gamma \mid \sigma]}{\Gamma \vdash [\sigma \mid \delta] : (\Upsilon \mid \Phi)} \quad \frac{\Gamma \vdash \theta : (\Upsilon \mid \Phi)}{\Gamma \vdash \theta_0 : \Upsilon}$$

$$\frac{\Gamma \vdash \theta : (\Upsilon \mid \Phi)}{\Gamma \vdash \theta_1 : \Phi \theta_0} \quad [\sigma \mid \delta]_0 \equiv \sigma \quad [\sigma \mid \delta]_1 \equiv \delta \quad [\theta_0 \mid \theta_1] \equiv \theta$$

$$(\Gamma \mid (\Upsilon \mid \Phi)) \equiv ((\Gamma \mid \Upsilon) \mid \Phi) \quad (\Upsilon \mid ()_p) \equiv \Upsilon \quad (\Upsilon \mid (\Phi, x :^\mu A)) \equiv ((\Upsilon \mid \Phi), x :^\mu A)$$

Note that to be at the right universe level, in the rule $(\Upsilon \mid ()_p) \equiv \Upsilon$, the right-hand side '$\Upsilon$' must be implicitly lifted to $\ell_0 \sqcup \ell_1$.

### 2.5.3 $\Pi$-telescopes

To define the copointed endofunctors whose coalgebras are display inductive types, we will need $\Pi$-telescopes. For simplicity, we require that the codomain be a strict telescope; this suffices for our application. The basic rules are just like those for $\Pi$-types.

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid (v : \Upsilon) \vdash \Theta \text{ stel}_{\ell_1}}{\Gamma \vdash (v : \Upsilon) \rightarrow \Theta \text{ stel}_{\ell_0 \sqcup \ell_1}} \quad \frac{\Gamma \mid (v : \Upsilon) \vdash \theta : \Theta}{\Gamma \vdash \lambda v. \theta : (v : \Upsilon) \rightarrow \Theta}$$

$$\frac{\Gamma \vdash \delta : (v : \Upsilon) \rightarrow \Theta \quad \Gamma \vdash \sigma : \Upsilon}{\Gamma \vdash \delta \sigma : \Theta [1_\Gamma \mid \sigma]} \quad \frac{\Gamma \mid (v : \Upsilon) \vdash \theta : \Theta \quad \Gamma \vdash \sigma : \Upsilon}{\Gamma \vdash (\lambda v. \theta) \sigma \equiv \theta [1_\Gamma \mid \sigma]}$$

$$\frac{\Gamma \vdash \delta : (v : \Upsilon) \rightarrow \Theta \quad \Gamma \vdash \delta' : (v : \Upsilon) \rightarrow \Theta \quad \Gamma \mid (v : \Upsilon) \vdash \delta v \equiv \delta' v}{\Gamma \vdash \delta \equiv \delta'}$$

In addition, we assert computation laws for $\Pi$-telescopes when the domain or codomain is an extension.

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_\ell}{((v : \Upsilon) \rightarrow ()_p) \equiv ()_p} \quad \frac{\Gamma \vdash \Theta \text{ stel}_\ell}{((\xi : ()_p) \rightarrow \Theta) \equiv \Theta}$$

$$\lambda v. []_p \equiv []_p \quad \lambda (v : ()_p). \theta \equiv \theta$$

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid (v : \Upsilon) \vdash \Theta \text{ stel}_{\ell_1} \quad \Gamma \mid (v : \Upsilon) \mid (\theta : \Theta) \vdash B \text{ type}_{\ell_2}}{((v : \Upsilon) \rightarrow (\Theta, y : B)) \equiv (\delta : (v : \Upsilon) \rightarrow \Theta, \epsilon : (v : \Upsilon) \rightarrow B [1_\Gamma \mid v \mid \delta v])}$$

$$\lambda v. [\theta, b] \equiv [\lambda v. \theta, \lambda v. b]$$

$$\frac{\Gamma \vdash_q \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid (v : \Upsilon), \text{ }_\mu \vdash_p A \text{ type}_{\ell_1} \quad \Gamma \mid (v : \Upsilon), x :^\mu A \vdash_q \Theta \text{ tel}_{\ell_2}}{((v : \Upsilon, x :^\mu A) \rightarrow \Theta) \equiv ((v : \Upsilon) \rightarrow (x :^\mu A) \rightarrow \Theta)}$$

$$\lambda (v : (\Upsilon \mid A)). \theta \equiv \lambda v. \lambda x. \theta$$

23

$$\frac{\Gamma \vdash \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma \mid (\upsilon : \Upsilon) \vdash \Theta \operatorname{tel}_{\ell_1} \quad \Gamma \mid (\upsilon : \Upsilon) \mid (\theta : \Theta) \vdash \Phi \operatorname{tel}_{\ell_2}}{((\upsilon : \Upsilon) \rightarrow (\Theta \mid \Phi)) \equiv (\delta : (\upsilon : \Upsilon) \rightarrow \Theta \mid \epsilon : (\upsilon : \Upsilon) \rightarrow (\Phi \mid 1_\Gamma \mid \upsilon \mid \delta \upsilon \mid))}$$

$$\lambda \upsilon. [\theta \mid \phi] \equiv [\lambda \upsilon. \theta \mid \lambda \upsilon. \phi]$$

When telescopes are definitionally lists of types, these rules suffice to compute any $\Pi$-telescope in terms of $\Pi$-types. Note that in the rule $((\xi : ()_p) \rightarrow \Theta) \equiv \Theta$, the '$\Theta$' on the right-hand side must be implicitly lifted to the maximum of the levels of $()_p$ and $\Theta$.

## 2.6 DISPLAYED TELESCOPES

The structure in section 2.4, with display acting on types and décalage on telescopes, is sufficient to determine the behavior of display. However, in practice we will also need a notion of dependent décalage and display for telescopes. When telescopes are lists of types, this is determined (like ordinary décalage) by display for types.

### 2.6.1 Meta-abstracted décalage

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon}}{\Gamma \vdash_{\mathrm{sm}} \Phi^D \operatorname{tel}_{\ell_1 / \upsilon^+ : \Upsilon^D}} \quad \frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \tau : \Phi}{\Gamma \vdash_{\mathrm{sm}} \tau^D : \Phi^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma \vdash_{\mathrm{sm}} \tau^+ : \Phi^D}{\Gamma \vdash_{\mathrm{sm}} \tau^{+\mathrm{ev}} : \left( \left( \Phi \mid \widehat{\mathbf{Q}}_{\triangle\square \in 1_{\mathrm{sm}}} \right) \right)_{\upsilon^+ : \Upsilon^D}}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{sm}} \Phi^D \sigma^D \equiv (\Phi \sigma)^D} \tag{2.1}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \tau : \Phi}{\Gamma \vdash_{\mathrm{sm}} \tau^D \sigma^D \equiv (\tau \sigma)^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^+ : \Upsilon^D \quad \Gamma \vdash_{\mathrm{sm}} \tau : \Phi}{\Gamma \vdash_{\mathrm{sm}} \tau^{D \cdot \mathrm{ev}} \sigma^+ \equiv \tau \sigma^{+\mathrm{ev}}}$$

We also require that this operation reduce to ordinary décalage on constant meta-abstractions, and commute appropriately with telescope concatenation, both globally and inside further meta-abstractions.

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^+ : \Upsilon^D}{\Gamma \vdash_{\mathrm{sm}} ((\Phi))_{\upsilon : \Upsilon^D} \sigma^+ \equiv \Phi^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^+ : \Upsilon^D \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi}{\Gamma \vdash_{\mathrm{sm}} [\![ \delta ]\!]_{\upsilon : \Upsilon^D} \sigma^+ \equiv \delta^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1}}{(\Upsilon \mid \Phi)^D \equiv \left( (\upsilon^+ : \Upsilon^D) \mid ((\Phi))_{\upsilon : \Upsilon^D} \upsilon^+ \right)} \tag{2.2}$$

24

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \delta : \Phi \left[ 1_\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \sigma \right]}{\left[ \sigma \mid \delta \right]^D \equiv \left[ \sigma^D \mid \delta^D \right]} \tag{2.3}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_1} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_2}}{\left( \left( (\Upsilon \mid \Phi) \right) \right)_{\theta : \Theta}^D \equiv \left( \left( (\upsilon^+ : (\Upsilon))_{\theta : \Theta}^D \theta^+) \mid (\Phi)_{\theta : \Theta, \upsilon : \Upsilon}^D \theta^+ \upsilon^+ \right) \right)_{\theta^+ : \Theta^D}}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \delta : \Phi \left[ 1_\Gamma, \mathbf{\Omega}_{\triangle\square} \mid 1_\Theta \mid \sigma \right]}{\left[ \left[ \sigma \mid \delta \right] \right]_{\theta : \Theta}^D \equiv \left[ \left[ \left[ \sigma \right] \right]_{\theta : \Theta}^D \theta^+ \mid \left[ \left[ \delta \right] \right]_{\theta : \Theta}^D \theta^+ \right]_{\theta^+ : \Theta^D}}$$

Note that in (2.2) we have to meta-abstract $\Phi$ in order to apply décalage, since $\Phi$ itself is not in a $\triangle\square$-locked context. In (2.3), $\delta^D$ is supposed to inhabit $(\Phi)_{\upsilon : \Upsilon}^D \sigma^D$, but by (2.1) and $\beta$-reduction for meta-abstractions this is equal to $(\Phi \left[ 1_\Gamma \mid \sigma \right])^D$, which is the natural type of $\delta^D$. The last two equations are similar.

**Remark 2.4.** The rules for telescope décalage from section 2.4.2 and this section should be compared with the 'local theory' from [ACKS24], with telescopes and telescope concatenation replacing types and $\Sigma$-types. The $\Upsilon^D$ from section 2.4.2 corresponds to their $\forall A$, while the $(\Phi)_{\Upsilon}^D$ from this section corresponds to their $\forall d(x, B)$. The $\sigma^D$ from section 2.4.2 corresponds to their R (although with an added modal lock), while the $[\delta]_{\upsilon : \Upsilon}^D$ from this section corresponds to their apd (with modal lock). We don't have their ap represented explicitly, but one of their rules says it is equivalent to apd in a constant family. Our $e^v$ is their k (in the unary case, so k = 0), and we do not have their S; as discussed before, the modal guards make symmetry unnecessary. And, of course, we don't have $\Pi$-telescopes or a universe; we have those only for display, which is indexed.

### 2.6.2 Computing meta-abstracted décalage

Like ordinary décalage, meta-abstracted décalage computes on telescopes that are made out of types. For brevity we omit the typing premises of these equalities, but we emphasize that all the meta-variables on the left-hand sides such as $\Theta, A, \sigma, t$ can depend nontrivially on the abstraction variables $\upsilon$ or $\upsilon^+$.

$$\left( \left( \theta : \Theta, x : A \right) \right)_{\upsilon : \Upsilon}^D \equiv \left( \left( \theta^+ : \left( \left( \Theta \right) \right)_{\upsilon : \Upsilon}^D \upsilon^+, x : A \left[ \mathbf{\Omega}_{\mathbf{e}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} \mid \upsilon^{+\mathrm{ev}} \mid \theta^{+\mathrm{ev}} \right. \right. \right. \cup^+,$$

$$x' : \left( \left( A \right) \right)_{\upsilon : \Upsilon \mid \theta : \Theta}^d \upsilon^+ \theta^+ x \right) \right)_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma, t \right] \right]_{\upsilon : \Upsilon}^D \equiv \left[ \left[ \left[ \sigma \right] \right]_{\upsilon : \Upsilon}^D \upsilon^+, \left[ \left[ t \right] \right]_{\upsilon : \Upsilon} \upsilon^{+\mathrm{ev}}, \left[ \left[ t \right] \right]_{\upsilon : \Upsilon}^d \upsilon^+ \right]_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma^+, t, t' \right] \right]_{\upsilon^+ : \Upsilon^D}^{\mathrm{ev}} \equiv \left[ \left[ \sigma^{+\mathrm{ev}}, t \right] \right]_{\upsilon^+ : \Upsilon^D}$$

$$\left( \left( \theta : \Theta, x :^{\triangle\circ\mu} A \right) \right)_{\upsilon : \Upsilon}^D \equiv \left( \left( \theta^+ : \left( \left( \Theta \right) \right)_{\upsilon : \Upsilon}^D \upsilon^+, \right. \right.$$

$$x :^{\triangle\circ\mu} A \left[ \mathbf{\Omega}_{\mathbf{e}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} \mid \upsilon^{+\mathrm{ev}} \mid \theta^{+\mathrm{ev}} \right. \left. \left. \mathbf{\Omega}_{\triangle\circ\mu} \right] \right) \right)_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma, t \right] \right]_{\upsilon : \Upsilon}^D \equiv \left[ \left[ \left[ \sigma \right] \right]_{\upsilon : \Upsilon}^D \upsilon^+, \left[ \left[ t \right] \right]_{\upsilon : \Upsilon} \upsilon^{+\mathrm{ev}} \right]_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma^+, t \right] \right]_{\upsilon^+ : \Upsilon^D}^{\mathrm{ev}} \equiv \left[ \left[ \sigma^{+\mathrm{ev}}, t \right] \right]_{\upsilon^+ : \Upsilon^D}$$

◁

25

### 2.6.3 Telescope display

We also need a notion of indexed display for telescopes. Note that this always gives a strict telescope, even if its input is not.

$$\frac{\Gamma, \widehat{\mathbf{\Omega}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell} \qquad \Gamma \vdash_{\mathrm{sm}} \sigma : \Upsilon [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ]}{\Gamma \vdash_{\mathrm{sm}} (\Upsilon^{\mathrm{d}} \sigma) \operatorname{stel}_{\ell}} \qquad \frac{\Gamma, \widehat{\mathbf{\Omega}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell} \qquad \Gamma, \widehat{\mathbf{\Omega}}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{sm}} \sigma^{\mathrm{d}} : (\Upsilon^{\mathrm{d}} (\sigma [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ]))}$$

Like décalage, telescope display computes on empty telescopes, and on telescopes extended by a type:

$$()_{\mathrm{sm}}^{\mathrm{d}} [ ]_{\mathrm{sm}} \equiv ()_{\mathrm{sm}}$$

$$[ ]_{\mathrm{sm}}^{\mathrm{d}} \equiv [ ]_{\mathrm{sm}}$$

$$(\theta : \Theta, x : A)^{\mathrm{d}} [ \sigma, t ] \equiv (\theta' : \Theta^{\mathrm{d}} \sigma, x' : (( A ))_{\theta : \Theta^{\mathrm{d}}} \langle \sigma, \theta' \rangle t)$$

$$[ \sigma, t ]^{\mathrm{d}} \equiv [ \sigma^{\mathrm{d}}, t^{\mathrm{d}} ] \quad (\text{for a non-modal variable})$$

$$(\theta : \Theta, x : ^{\triangle\circ\mu} A)^{\mathrm{d}} [ \sigma, t ] \equiv \Theta^{\mathrm{d}} \sigma$$

$$[ \sigma, t ]^{\mathrm{d}} \equiv \sigma^{\mathrm{d}} \quad (\text{for a modal variable})$$

As promised, this is the reason that the empty telescope must exist at all levels: if $\Upsilon$ consists only of modal variables, then $\Upsilon^{\mathrm{d}}$ is empty, but it must be at the same level as $\Upsilon$.

Note that compared to décalage, telescope display reorders the variables. For instance, we have

$$(x : A, y : B)^{\mathrm{D}} \equiv (x : A, x' : A^{\mathrm{d}} x, y : B, y' : B^{\mathrm{d}} y)$$

$$(x : A, y : B)^{\mathrm{d}} \equiv (( x' : A^{\mathrm{d}} x, y' : B^{\mathrm{d}} y ))_{x : A, y : B}$$

$$(x : A, y : B) \mid (x : A, y : B)^{\mathrm{d}} \equiv (x : A, y : b, x' : A^{\mathrm{d}} x, y' : B^{\mathrm{d}} y)$$

$$\not\equiv (x : A, y : B)^{\mathrm{D}}.$$

Thus, we instead relate telescope display to décalage by an 'odds' operation that picks out the elements of displayed types, and a 'pairing' operation that interleaves them together, such that evens and odds together form an isomorphism with pairing as inverse.

$$\frac{\Gamma \vdash_{\mathrm{sm}} \sigma^{+} : \Upsilon^{\mathrm{D}}}{\Gamma \vdash_{\mathrm{sm}} \sigma^{+\mathrm{od}} : \Upsilon^{\mathrm{d}} \sigma^{\mathrm{ev}}} \qquad \frac{\Gamma \vdash_{\mathrm{sm}} \sigma : \Upsilon [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ] \qquad \Gamma \vdash_{\mathrm{sm}} \sigma' : \Upsilon^{\mathrm{d}} \sigma}{\Gamma \vdash_{\mathrm{sm}} \langle \sigma, \sigma' \rangle : \Upsilon^{\mathrm{D}}}$$

$$\sigma^{+} \equiv \langle \sigma^{+\mathrm{ev}}, \sigma^{+\mathrm{od}} \rangle \qquad \langle \sigma, \sigma' \rangle^{\mathrm{ev}} \equiv \sigma \qquad \langle \sigma, \sigma' \rangle^{\mathrm{od}} \equiv \sigma'$$

$$\sigma^{\mathrm{D \, od}} \equiv \sigma^{\mathrm{d}} \qquad \langle \sigma [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ], \sigma^{\mathrm{d}} \rangle \equiv \sigma^{\mathrm{D}}$$

These operations also compute on empty telescopes and on telescopes extended by a type:

$$[ ]_{\mathrm{sm}}^{\mathrm{od}} \equiv [ ]_{\mathrm{sm}}$$

$$\langle [ ]_{\mathrm{sm}}, [ ]_{\mathrm{sm}} \rangle \equiv [ ]_{\mathrm{sm}}$$

$$[ \sigma^{+}, t, t' ]^{\mathrm{od}} \equiv [ \sigma^{+\mathrm{od}}, t' ] \quad (\text{for a non-modal variable})$$

$$\langle [ \sigma, t ], [ \sigma', t' ] \rangle \equiv [ \langle \sigma, \sigma' \rangle, t, t' ] \quad (\text{for a non-modal variable})$$

$$[ \sigma^{+}, t ]^{\mathrm{od}} \equiv \sigma^{+\mathrm{od}} \quad (\text{for a modal variable})$$

$$\langle [ \sigma, t ], \sigma' \rangle \equiv [ \langle \sigma, \sigma' \rangle, t ] \quad (\text{for a modal variable})$$

26

# 2.6.4 Meta-abstracted telescope display

Unsurprisingly, we generalise telescope display to apply to meta-abstracted telescopes as well, with rules combining those of sections 2.4.3 and 2.6.3. First we have the basic rules:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon}}{\Gamma \vdash_{\mathrm{sm}} \Phi^{\mathrm{d}} \operatorname{stel}_{\ell_1 / \nu^{+} : \Upsilon^{\mathrm{D}}, \Phi : \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \nu^{+\mathrm{ev}}}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \delta : \Phi}{\Gamma \vdash_{\mathrm{sm}} \delta^{\mathrm{d}} : \left( \left( \Phi^{\mathrm{d}} \nu^{+} (\delta \nu^{+\mathrm{ev}}) \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}}}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma \vdash_{\mathrm{sm}} t : (\Phi \sigma) [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ]}{\Gamma \vdash_{\mathrm{sm}} \Phi^{\mathrm{d}} \sigma^{\mathrm{D}} t \equiv (\Phi \sigma)^{\mathrm{d}} t}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} t : \Phi}{\Gamma \vdash_{\mathrm{sm}} t^{\mathrm{d}} \sigma^{\mathrm{D}} \equiv (t \sigma)^{\mathrm{d}}}$$

Then we have the odds/pairing isomorphism:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma \vdash_{\mathrm{sm}} \delta^{+} : \Phi^{\mathrm{D}}}{\Gamma \vdash_{\mathrm{sm}} \delta^{+\mathrm{od}} : \left( \left( \Phi^{\mathrm{d}} \nu^{+} (\delta^{+\mathrm{ev}} \nu^{+}) \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}}}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon}}{\Gamma \vdash_{\mathrm{sm}} \delta : \left( \left( \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \nu^{+\mathrm{ev}} \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}} \quad \Gamma \vdash_{\mathrm{sm}} \delta' : \left( \left( \Phi^{\mathrm{d}} \nu^{+} (\delta \nu^{+}) \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}}}{\Gamma \vdash_{\mathrm{sm}} \langle \delta, \delta' \rangle : \Phi^{\mathrm{D}}}$$

$$\delta \equiv \langle \delta^{\mathrm{ev}}, \delta^{\mathrm{od}} \rangle \quad \langle \delta, \delta' \rangle^{\mathrm{ev}} \equiv \delta \quad \langle \delta, \delta' \rangle^{\mathrm{od}} \equiv \delta'$$

$$\delta^{\mathrm{D \, od}} \equiv \delta^{\mathrm{d}} \quad \langle \delta [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ], \delta^{\mathrm{d}} \rangle \equiv \delta^{\mathrm{D}}$$

On constant meta-abstractions, this reduces to ordinary telescope display:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^{+} : \Upsilon^{\mathrm{D}} \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \sigma^{+} ]}{\Gamma \vdash_{\mathrm{sm}} \left( (\Phi) \right)_{\nu : \Upsilon^{\mathrm{d}}} \sigma^{+} \delta \equiv \Phi^{\mathrm{d}} \delta}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^{+} : \Upsilon^{\mathrm{D}} \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \sigma^{+} ]}{\Gamma \vdash_{\mathrm{sm}} \left[ \left[ \delta \right] \right]_{\nu : \Upsilon^{\mathrm{d}}} \sigma^{+} \equiv \delta^{\mathrm{d}}}$$

27

And we have computation rules for telescope extensions:

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma : \Upsilon [ \mathbf{a}_{\mathbf{\Phi}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ] \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi [ \mathbf{a}_{\mathbf{\Phi}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} \mid \sigma ]} (\Upsilon \mid \Phi)^d \sigma \delta \equiv ((\upsilon' : \Upsilon^d \sigma) \mid ((\Phi))_{\upsilon : \Upsilon^d} \langle \sigma, \upsilon' \rangle \delta)$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{[ \sigma \mid \delta ]^d \equiv [ \sigma^d \mid \delta^d ]}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1}}{(((\Upsilon \mid \Phi)))_{\theta : \Theta^d} \equiv (((\upsilon' : ((\Upsilon))_{\theta : \Theta^d} \theta^+ \upsilon) \mid ((\Phi))_{\theta : \Theta, \upsilon : \Upsilon^d} \theta^+ \langle \upsilon, \upsilon' \rangle \phi))_{\theta^+ : \Theta^D, \upsilon : \Upsilon, \phi : \Phi}}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \delta : \Phi [ 1_\Gamma, \mathbf{\Omega}_{\triangle\square} \mid 1_\Theta \mid \sigma ]}{[ [ \sigma \mid \delta ]]_{\theta : \Theta^d} \equiv [ [ [ \sigma ]]_{\theta : \Theta^d} \theta^+ \mid [ [ \delta ]]_{\theta : \Theta^d} \theta^+ ]_{\theta^+ : \Theta^D}} \triangleleft$$

### 2.6.5 Computing meta-abstracted telescope display

These computation rules are analogous to the previous ones, first in the non-modal case:

$$((\theta : \Theta, x : A))_{\upsilon : \Upsilon^d} [ \sigma^+ \mid \delta, t ] \equiv (\theta' : ((\Theta))_{\upsilon : \Upsilon^d} \sigma^+ \delta,$$

$$x' : ((\mathcal{A}))_{\upsilon : \Upsilon, \theta : \Theta^d} \sigma \langle \delta, \theta' \rangle t)$$

$$[ [ \delta, t ]]_{\upsilon : \Upsilon^d} \sigma^+ \equiv [ [ [ \delta ]]_{\upsilon : \Upsilon^d} \sigma^+, [ [ t ]]_{\upsilon : \Upsilon^d} \sigma^+ ]$$

$$[ [ \delta^+, t, t']]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+ \equiv [ [ [ \delta^+ ]]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+, [ [ t']]_{\upsilon^+ : \Upsilon^D} \sigma^+ ]$$

$$\langle [ [ \delta, t ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta', t']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+ \equiv [ \langle [ [ \delta ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+,$$

$$[ [ t ]]_{\upsilon^+ : \Upsilon^D} \sigma^+, [ [ t']]_{\upsilon^+ : \Upsilon^D} \sigma^+ ]$$

and then the modal case:

$$((\theta : \Theta, x : \triangle\circ\mu \mathcal{A}))_{\upsilon : \Upsilon^d} [ \sigma^+ \mid \delta, t ] \equiv ((\Theta))_{\upsilon : \Upsilon^d} \sigma^+ \delta$$

$$[ [ \delta, t ]]_{\upsilon : \Upsilon^d} \sigma^+ \equiv [ [ \delta ]]_{\upsilon : \Upsilon^d} \sigma^+$$

$$[ [ \delta, t ]]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+ \equiv [ [ \delta ]]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+$$

$$\langle [ [ \delta, t ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+ \equiv [ \langle [ [ \delta ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+,$$

$$[ [ t ]]_{\upsilon^+ : \Upsilon^D} \sigma^+ ]$$

### 2.6.6 Computing display on $\Pi$-telescopes

Finally, we give the following rules for computing display and meta-abstracted display of a $\Pi$-telescope. These are consistent with the rules for computing display on telescopes extended by a type.

$$((\phi : \Phi) \to \Theta \phi)^d \delta \equiv (\phi^+ : \Phi^D) \to \Theta^d \phi^{+ev} (\delta \phi^{+ev})$$

$$((\phi : \Phi \upsilon) \to \Theta \upsilon \phi))_{\upsilon : \Upsilon^d}$$

$$\equiv ((\phi^+ : \Phi^D \upsilon^+) \to \Theta^d \upsilon^+ \phi^+ (\delta \phi^{+ev}))_{\upsilon^+ : \Upsilon^D, \delta : (\phi : \Phi \upsilon^{+ev}) \to \Theta \upsilon^{+ev} \phi}$$

28

However, it does not seem possible to give rules for computing décalage on a  \( \Pi \) -telescope that are similarly consistent. Fortunately, we will not need such rules. Of course, since décalage and  \( \Pi \) -telescopes both compute independently on telescopes extended by a type, so does their combination.

This concludes our description of the ambient syntax of dTT.

◀

## 3 Semi-Simplicial and Displayed Coinductive Types

Recall from the introduction that our primary goal in formulating dTT (at the moment) is to have a type theory in which we can make precise our coinductive definition of the type SST of semi-simplicial types. In this section we give that definition, making use of the 'display' primitives of dTT that was introduced in section 2. The basic definition is contained in section 3.1, followed by an exploration of some examples in section 3.2. Then in section 3.3 we describe a more general notion of 'displayed coinductive type' that has SST as a special case, and in section 3.4 we explore a few other examples of the general notion.

### 3.1 SEMI-SIMPLICIAL TYPES

In an ideal version of displayed type theory, one could define semi-simplicial types as an instance of a general codata declaration. We would expect to write this in a proof assistant with a syntax like the following, which generalises Agda-like syntax for records by allowing the coinductive input of each destructor to be specified explicitly and referred to in its type:

codata SST : Type where
Z : SST → Type
S : (A : SST) → Z A → SST\( ^{d} \) A

It is beyond the scope of this paper to give a sufficiently broad framework to generally encompass such definitions, but we will describe one general paradigmatic class of them, analogous to W-types as paradigmatic inductive types and M-types as paradigmatic coinductive types. However, we begin by discussing the concrete example of SST in more detail, to help motivate the general case.

#### 3.1.1 SST basics

We begin by giving the type formation law and destructors. Of course, since SST is a sort of 'universe', its elements consisting of types, it must also be parametrized by a level.

\(\Gamma \vdash_{sm} SST_{\ell} type_{lsuc \ell}\)

\(\Gamma \vdash_{sm} Z : ((\text{Type}_{\ell}))_{A : SST_{\ell}}\)

\(\Gamma \vdash_{sm} S : ((\text{SST}_{\ell}^{d} A))_{A : SST_{\ell}, a : EI(Z A)}\)

Note that the destructors are defined as terms belonging to 'meta-abstractions' as introduced in section 2.3.3. We have chosen this over the more common method of supplying the arguments in premises, e.g.

\(\frac{\Gamma \vdash_{sm} A : SST_{\ell}}{\Gamma \vdash_{sm} Z A : Type_{\ell}},\)

29

because it makes it easier to compute  \( ^{d} \)  of them:

\[
\Gamma \vdash_ {s m} S S T _ {\ell} ^ {d} \text { type } _ {\text { l   s   u   c } \ell} / A _ {3}: S S T _ {\ell}
\]

\[
\Gamma \vdash_ {s m} Z ^ {d}: ((\text {   EI   } (Z A _ {3}) \rightarrow \text { Type } _ {\ell})) _ {\{A _ {3}: S S T _ {\ell} \}, A _ {x}: S S T _ {\ell} ^ {d} A _ {3}}
\]

\[
\Gamma \vdash_ {s m} S ^ {d}: \left(\left(S S T _ {\ell} ^ {d d} A _ {3} A _ {x} (S A _ {3} a _ {3})\right)\right) _ {\{A _ {3}: S S T _ {\ell} \}, A _ {x}: S S T _ {\ell} ^ {d} A _ {3}, a _ {3}: E I (Z A _ {3}), a _ {x}: E I (Z ^ {d} A _ {x} a _ {3})}
\]

What this calculation suggests is that the family  \( SST^{d} \)  should behave as though defined by computing  \( ^{d} \)  on all of the destructors in the code block above:

codata  \( SST^{d} \)  ( \( A_{3} \)  : SST) : Type where
 \( Z^{d} \)  :  \( SST^{d} \)   \( A \rightarrow Z \)   \( A \rightarrow Type \) 
 \( S^{d} \)  : ( \( A_{x} \)  :  \( SST^{d} \)   \( A \) ) ( \( a_{3} \)  :  \( Z \)   \( A_{3} \) ) →  \( Z^{d} \)   \( A_{x} \)   \( a_{3} \)  →  \( SST^{dd} \)   \( A_{3} \)   \( A_{x} \)  ( \( S \)   \( A_{3} \)   \( a_{3} \) )

Unfortunately, as we will see this is not actually possible in our theory, but it is a useful intuition. In general, the types obtained by iterating  \( ^{d} \)  n-times on Z and S will begin by taking a n-fold dependent SST in a generic augmented simplicial context of SSTs of lower dependency. This context can be generally inferred from the type of n-fold dependent SST, and we have thus chosen to make those arguments implicit, which aligns with the syntactic presentation in the introduction. In particular, the formula for  \( A_{2} \)  is given by:

\[
Z ^ {d d} \left(S ^ {d} (S A x _ {m}) x _ {m} \beta_ {m}\right) x _ {m} \beta_ {m} \beta_ {m}
\]

as opposed to:

\[
Z ^ {d d} A (S A x _ {m}) (S A x _ {m}) \left(S ^ {d} A (S A x _ {m}) x _ {m} \beta_ {m}\right) x _ {m} \beta_ {m} \beta_ {m}.
\]

#### 3.1.2 The coinduction principle

Suppose that we want to construct a function mapping into SST from a telescope of arbitrary length. We first think purely in terms of code, written in the style of Agda-esque copattern matching, with the goal of writing down something that can conceivably be justified:

f : X → SST
Z (f t) = (?z₀ : Type)
S (f t) a = fᵈ t (?s₀ : Xᵈ t)
g : (t : X) → Y t → SST
Z (g t s) = (?z₁ : Type)
S (g t s) a = gᵈ t (?s₁ : Xᵈ t) s (?s₂ : Yᵈ t ?s₁ s)

Here, suppose that \(\Gamma\), \(\widehat{\mathbf{Q}}_{\Delta \square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell'}\). If we think of \(\Upsilon\) as a state space and \([\sigma : \Upsilon]\) as a state. Then the above definition suggests that we are able to define \(f: (\upsilon : \Upsilon) \to \mathrm{SST}_{\ell}\) provided that we are able to provide two ingredients. First, we need a way of extracting \([\bar{Z} \sigma : \mathrm{Type}_{\ell}]\), a type of 0-simplices, from a state \(\sigma\). Second, we need a way of extracting \([\bar{S} \sigma a : \Upsilon^{d} \sigma]\), a dependent section of \(\Upsilon\) over \(\sigma\), from a state \(\sigma\) and a 0-simplex \([a : \bar{Z} \sigma]\). This suggests that a reasonable coinduction principle for \(\mathrm{SST}_{\ell}\) is the following:

\[
\frac {\Gamma , \widehat {\mathbf {Q}} _ {\Delta \square} \vdash_ {\mathrm{sm}} \Upsilon \operatorname{ctx} _ {\ell^ {\prime}}}{\Gamma , \widehat {\mathbf {Q}} _ {\Delta \square} \vdash_ {\mathrm{sm}} \bar {Z} : ((\text {Type} _ {\ell})) _ {\delta : \Upsilon} \quad \Gamma , \widehat {\mathbf {Q}} _ {\Delta \square} \vdash_ {\mathrm{sm}} \bar {S} : ((\Upsilon^ {d} \delta)) _ {\delta : \Upsilon , a : \operatorname{EI} (\bar {Z} \delta)}}   \frac {}{\Gamma \vdash_ {\mathrm{sm}} R _ {T} \bar {Z} \bar {S} : ((\text {SST} _ {\ell})) _ {\delta : \Upsilon}}
\]

30

and that its computation rules should be:

$$Z \left( R_T \bar{Z} \bar{S} \sigma \right) \equiv \bar{Z} \sigma$$

$$S \left( R_T \bar{Z} \bar{S} \sigma \right) a_3 \equiv \left( R_T \bar{Z} \bar{S} \right)^d \langle \sigma, \bar{S} \sigma a_3 \rangle.$$

Now, the expression $\left( R_T \bar{Z} \bar{S} \right)^d$ defines a meta abstracted-term of meta-abstracted type $\left( \left( SST_f^d \left( R_T \bar{Z} \bar{S} v^{+ev} \right) \right) \right)_{v^+, \gamma^0}$. One reasonable hope is that the display in the above line could be computed in terms of a corecursor for $SST_f^d$. However, this approach runs into issues. Towards this aim, let us more generally try to work out the coinduction principle that would let us define $f : (x : X) \to SST_f^d (A x)$ for $\Gamma$, $\widehat{\mathbf{A}}_{\triangle \square} \vdash_{sm} A : X \to SST_f^d$. We apply the same methodology as before, and start by writing down reasonable looking code:

$$\begin{array}{l} f : (t : X) \to SST^d (A t) \\ Z^d (f t) a = (?_{Z_2} : \text{Type}) \\ S^d (f t) a b = f^d t (?_{S_3} : X^d t) \end{array}$$

However, we then have:

$$\begin{array}{l} \Gamma, \widehat{\mathbf{A}}_{\triangle \square}, t : X, a : \text{EI} (Z (A t)), b : \text{EI} ?_{Z_2} \vdash_{sm} S^d (f t) a b : SST_f^{dd} (A t) (f t) (S (A t) a) \\ \Gamma, \widehat{\mathbf{A}}_{\triangle \square}, t : X, a : \text{EI} (Z (A t)), b : \text{EI} ?_{Z_2} \vdash_{sm} f^d t ?_{S_3} : SST_f^{dd} (A t) (A^d t ?_{S_3}) (f t) \end{array}$$

We see then that there is an index ordering mismatch that seems to prevent us from writing down a coinduction principle for $SST_f^d$ corresponding to a simple class of syntactic tricks as above. If dTT were extended to have symmetries, then we could make progress here by lining up the $f$ $t$ indices and imposing the definitional equality $S (A t) a \equiv A^d t ?_{S_3}$ as a corecursor premise. On the other hand, without the ability to line up the two $f$ $t$ indices, trying to instead impose definitional equalities involving $f$, the very term being defined, creates a vicious cycle, since whether or not a definition of $f$ is well-typed would depend on checking a definitional equality with $f$, which presupposes that $f$ is well-typed. Since, for the present, we have chosen to develop a theory without symmetries, we must abandon this approach.

To salvage this, we will leave $(R_T \bar{Z} \bar{S})^d$ as a stuck form in the theory, but will specify how to compute $Z^d$ and $S^d$ on this normal form. The main idea is that if we define:

$$\begin{array}{l} f : X \to SST \\ Z (f t) = j t \\ S (f t) a = f^d t (s t a) \end{array}$$

then we can compute display on each line of this definition to obtain:

$$\begin{array}{l} f^d : (t : X) \to X^d t \to SST^d (f t) \\ Z^d (f^d t s) = \lambda a \to j^d t s a \\ S^d (f^d t s) a_i a_i = f^{dd} t s (s t a_i) (s^d t s a_i a_i) \end{array}$$

Thus we obtain the computation laws:

$$\begin{array}{l} Z^d \left( (R_T \bar{Z} \bar{S})^d \sigma^+ \right) a \equiv \bar{Z}^d \sigma^+ a \\ S^d \left( (R_T \bar{Z} \bar{S})^d \sigma^+ \right) a_i a_i \equiv (R_T \bar{Z} \bar{S})^{dd} \langle \sigma^+, \bar{S}^D \sigma^+ a_i a_i \rangle \end{array}$$

31

Note that these computation rules were exactly obtained by applying display to both sides of the equation in the initial computation rules. We can iterate this to obtain:

$$Z^{d^n} \left( (R_T \bar{Z} \bar{S})^{d^n} \sigma^n \right) \partial a \equiv \bar{Z}^{d^n} \sigma^n \partial a$$

$$S^{d^n} \left( (R_T \bar{Z} \bar{S})^{d^n} \sigma^n \right) \partial a \, a \equiv (R_T \bar{Z} \bar{S})^{d^{n+1}} \langle \sigma^n, \bar{S}^{D^n} \sigma^n \partial a \, a \rangle$$

The situation on our hands is not unlike that of Agda, where a definition of f made by (co)pattern matching defines a new normal form and does not expand to a first class intro or elim form when normalised⁶; such names only reduce when their defining patterns occur. This specific point does not itself inhibit Nat canonicity (which Cubical Agda otherwise currently lacks due to its treatment of transport in indexed inductives).

We conjecture that dTT, including its treatment of SST, is fully computational in the sense of Nat canonicity, normalization, and decidable typechecking. More precisely, although this may very well not hold verbatim of the theory as written down in this paper, we expect it to hold of a modified presentation fitting within the general framework of ideas. In particular, while we have presented dTT only as a Generalised Algebraic Theory, all the equations have a clear direction and there are no obvious stuck terms.

### 3.2 EXAMPLES OF SEMI-SIMPLICIAL TYPES

Of course, simply defining a type of semi-simplicial types is only the first step: we also want to be able to work with such things conveniently. Developing a full theory of semi-simplicial types is beyond the scope of this paper, but in this section we will give a few examples to suggest that this at least may be possible with our definition of SST and its corecursion principle. We will use Agda-esque copattern-matching, and assume that our type theory has plenty of other structure rather than the bare-bones version of dTT that we have studied formally in this paper.

### 3.2.1 The singular semi-simplicial types

Thus far we have not discussed propositional equality at all, and the reason for this is that the implementation of display is independent from any implementation of equality, whether that be Martin-Löf, cubical, or observational. However, we now want to define a semi-simplicial type that arises from the ∞-groupoid structure of a type in HoTT. For concreteness we will do this using a cubical notion of equality, with notation that aligns with Cubical Agda.

When dTT is combined with cubical type theory, we expect display on cubical path types should work as follows. We have:

$$A : \text{Type}_\ell, x : A, y : A \vdash_{\text{sm}} \text{Path } A \times y \text{ type}_\ell$$

$$A : \text{Type}_\ell, P : A \to \text{Type}_\ell, x : A, x' : P \times,$$

$$y : A, y' : P \times, p : \text{Path } A \times y \vdash_{\text{sm}} \text{PathP } (\lambda \text{ i. } P \text{ (p i)}) \times' y' \text{ type}_\ell,$$

⁶The culprit here is not a lack of first-class forms, since Agda has pattern matching lambdas. Rather, the restriction is made primarily to control such runaway unfolding that would substantially affect the performance of type-checking and normalisation. As a consequence, two structurally identical top-level definitions of functions f and g made by pattern matching are not definitionally equal.

32

so the latter has the right type to be the display of the former. Thus we expect:

\( \left(\left(\text{Path } A \times y\right)\right)_{A : \text{Type}_i, x : A, y : A}^d \equiv \)

\( \left(\left(\text{PathP } (\lambda i. P (p i)) x' y'\right)\right)_{A : \text{Type}_i, P : A \to \text{Type}_i, x : A, x' : P x, y : A, y' : P y, p : \text{Path } A \times y}. \)

With this given, the singular semi-simplicial types are defined by corecursion. Rather than write this explicitly using the corecursor from section 3.1, we use a copattern-matching syntax, including a 'displayed corecursive call' \(\mathrm{Sing}^{\mathrm{d}}\).

Sing : Type → SST
Z (Sing A) = A
S (Sing A) x = Sing \( ^{d} \)  A ( \( \lambda \)  y → Path A x y)

A calculation then yields:

Z (Sing A) = A
 \( Z^{d} \)  (S (Sing A)  \( x_{i1} \) )  \( x_{i1} \)  = Path A  \( x_{i1} \)   \( x_{i1} \) 
 \( Z^{dd} \)  ( \( S^{d} \)  (S (Sing A)  \( x_{i1} \) )  \( x_{i1} \)   \( \beta_{i1} \) )  \( x_{i1} \)   \( \beta_{i1} \)   \( \beta_{i1} \) 
= PathP ( \( \lambda i \rightarrow Path A x_{i1} \beta_{i1} i \) )  \( \beta_{i1} \beta_{i1} \) 
 \( Z^{ddd} \)  ( \( S^{dd} \)  ( \( S^{d} \)  (S (Sing A)  \( x_{i1} \) )  \( x_{i1} \beta_{i1} \) )  \( x_{i1} \beta_{i1} \beta_{i1} \beta_{i1} f_{i1} \) )  \( x_{i1} \beta_{i1} \beta_{i1} \beta_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \)

#### 3.2.2 Nerves of categories

The semi-simplicial nerve of a 1-category can also be defined by corecursion. Let Cat denote the type of 1-categories, defined as a record inside dTT (extended by record types), and recall that in section 1 we computed Cat \( ^{d} \) to consist of ‘displayed categories’ in the usual sense [AL19]. Thus we can define:

Nerve : Cat → SST
Z (Nerve C) = ob C
S (Nerve C) x = Nerve \( ^{d} \)  C (coslice C x)

Here for a category \(\mathcal{C}\) and object \(x: \text{ob } \mathcal{C}\), by coslice \(\mathcal{C} x\) we mean the coslice category \(x / \mathcal{C}\), regarded as a displayed category over \(\mathcal{C}\) via the forgetful functor. Note that a definition of coslice: \((\mathcal{C}: \text{Cat}) \to \text{ob } \mathcal{C} \to \text{Cat}^{\mathrm{d}} \mathcal{C}\) at the global level in dTT automatically induces the definition of the dependent coslice coslice\(^{\mathrm{d}}\). A similar idea works for bicategories, and any other kind of category for which we can define a displayed (co)slice.

#### 3.2.3 Topological singular complexes

In section 3.2.1 we constructed the singular semi-simplicial type associated to the intrinsic \(\infty\)-groupoid structure of any type. But we can also construct a more classical singular semi-simplicial set associated to a topological space. For any type Top of 'topological space' definable inside of dTT as a record, we have a displayed version Top\(^{d}\). In some cases, particularly 'nonalgebraic' ones such as open-set spaces, an element of Top\(^{d}\) X is more general than an Y : Top with a map Y → X; but at least from such a Y we can construct its fibers as a displayed space. Thus, as long as we can construct, for any x : X, a space of 'continuous paths in X starting at x' with an endpoint projection down to X, we can make it a displayed space paths X x over X, and use this to construct the singular semi-simplicial types:

33

Sing : Top → SST
Z (Sing X) = pt X
S (Sing X) x = Sing^d X (paths X x)

#### 3.2.4 Fibers and higher spans

As we will see in section 4, semantically each type at mode sm is already an augmented semi-simplicial type. We expect that if we fix a particular  \( (-1) \) -simplex in an augmented semi-simplicial type, we should obtain an (unaugmented) semi-simplicial type as its 'fibre'. And indeed, we can define this operation:

Fib : (X :  \( \triangle\square \)  Type) ( \( \mathfrak{z} \)  : X) → SST
Z (Fib X  \( \mathfrak{z} \) ) = X \( ^{d} \)   \( \mathfrak{z} \) 
S (Fib X  \( \mathfrak{z} \) ) x = Fib \( ^{d} \)  X  \( \mathfrak{z} \)  x

Note that X is required to be modal so that we can take display of it. Then we have, for instance, if  \( z_{0}: X \)  and  \( x_{0}, x_{0}: X^{d} z_{0} \) ,

\[
\begin{array}{l} (\text { Fib } X _ {\mathfrak {z} _ {0}}) _ {0} \equiv Z (\text { Fib } X _ {\mathfrak {z} _ {0}}) \\ \equiv X ^ {d} \mathfrak {z} _ {0} \\ \left(\operatorname{Fib} X _ {\mathfrak {z} _ {0}}\right) _ {1} x _ {0} x _ {0} \equiv Z ^ {d} \left(S \left(\operatorname{Fib} X _ {\mathfrak {z} _ {0}}\right) x _ {0}\right) x _ {0} \\ \equiv Z ^ {d} \left(\operatorname{Fib} ^ {d} X _ {\mathfrak {z} _ {0}} x _ {0}\right) x _ {0} \\ \equiv X ^ {d d} \mathfrak {z} _ {0} x _ {0} x _ {0} \\ \end{array}
\]

and as a last example

\[
\begin{array}{l} \left(\text { Fib } X _ {\mathfrak {z} _ {0}}\right) _ {2} x _ {0 1} x _ {0 1} \beta_ {0 1} x _ {0 0} \beta_ {0 1} \beta_ {0 1} \equiv Z ^ {d d} \left(S ^ {d} \left(S \left(\text { Fib } X _ {\mathfrak {z} _ {0}}\right) x _ {0 1}\right) x _ {0 1} \beta_ {0 1}\right) x _ {0 0} \beta_ {0 1} \beta_ {0 1} \\ \equiv Z ^ {d d} \left(S ^ {d} \left(\operatorname{Fib} ^ {d} X _ {\mathfrak {z} _ {0 0}} x _ {0 1}\right) x _ {0 0} \beta_ {0 1}\right) x _ {0 0} \beta_ {0 1} \beta_ {0 1} \\ \equiv Z ^ {d d} \left(\operatorname{Fib} ^ {d d} X _ {\mathfrak {z} _ {0 0}} x _ {0 1} x _ {0 0} \beta_ {0 1}\right) x _ {0 0} \beta_ {0 1} \beta_ {0 1} \\ \equiv \operatorname{Fib} ^ {d d} X _ {\mathfrak {z} _ {0 0}} x _ {0 1} x _ {0 0} \beta_ {0 1} x _ {0 0} \beta_ {0 1} \beta_ {0 1}. \\ \end{array}
\]

In particular, if we let \( X = \text{Type}_\ell \) be a universe and \( \mathfrak{z} = \top \) be a unit type, we have

\[
\begin{array}{l} (\text { Fib   Type } _ {\ell} \top) _ {0} \equiv \text { Type } _ {\ell} ^ {d} \top \\ \equiv \top \rightarrow \text { Type } _ {\ell} \\ \cong \text { Type } _ {\ell} \\ \end{array}
\]

\[
\left(\text { Fib   Type } _ {\ell} \top\right) _ {1} X _ {0} X _ {0} \equiv \text { Type } _ {\ell} ^ {\mathrm{dd}} \top X _ {0} X _ {0}
\]

\[
\cong X _ {0} \rightarrow X _ {0} \rightarrow \text { Type } _ {\ell}
\]

\[
\left(\text { Fib   Type } _ {\ell} \top\right) _ {2} X _ {0 1} X _ {0 0} B _ {0 1} X _ {0 0} B _ {0 1} B _ {0 1} \equiv \text { Type } _ {\ell} ^ {\text { ddd }} \top X _ {0 1} X _ {0 0} B _ {0 1} X _ {0 0} B _ {0 1} B _ {0 1}
\]

\[
\cong \left(\mathrm{x} _ {0 1}: \mathrm{X} _ {0 1}\right) \left(\mathrm{x} _ {0 2}: \mathrm{X} _ {0 2}\right) \left(\beta_ {0 1}: \mathrm{B} _ {0 1} \mathrm{x} _ {0 1} \mathrm{x} _ {0 2}\right)
\]

\[
\left(\mathrm{x} _ {0 0}: \mathrm{X} _ {0 0}\right)\left(\beta_ {0 1}: \mathrm{B} _ {0 1} \mathrm{x} _ {0 1} \mathrm{x} _ {0 2}\right)\left(\beta_ {0 2}: \mathrm{B} _ {0 2} \mathrm{x} _ {0 2} \mathrm{x} _ {0 3}\right)\rightarrow \text {Type} _ {\ell}
\]

Thus \(\text{Fib Type}_\ell \top\) is the semi-simplicial type of types, spans, and a sort of simplicial 'higher spans' that could also be called 'heterogeneous simplices'. More generally, \(\text{Fib Type}_\ell A\) for any type \(A\) consists of types, spans, and simplicial higher spans indexed by \(A\).

34

### 3.2.5 Operations on semi-simplicial types

We can also use corecursion to define operations on semi-simplicial types that are essentially levelwise. For instance, any two semi-simplicial types have a product:

_×_ : SST → SST → SST
Z (X × Y) = Z X × Z Y
S (X × Y) ⟨ x , y ⟩ = (S X x) ×^d (S Y y)

Here in the S case, we have treated the non-displayed arguments of ×^d as implicit: its full type is

$$\_\times^d : \{X : SST\} \{X' : SST^d X\} \{Y : SST\} \{Y' : SST^d Y\} \to SST^d \{X \times Y\}$$

There is a similar dependently-typed version, i.e. a Σ-semi-simplicial-type:

Σ : (X : SST) → SST^d X → SST
Z (Σ X Y) = Σ (Z X) (Z^d Y)
S (Σ X Y) ⟨ x , y ⟩ = Σ^d (S X x) (S Y y)

There is an empty semi-simplicial type. Note that the S case can be omitted, since one of its arguments would belong to the empty type ⊥.

∅ : SST
Z ∅ = ⊥

Similarly, there is a trivial one:

T : SST
Z T = T
S T u = T^d

We can also take the product of any family of semi-simplicial types indexed by a discrete type. Note that the discreteness of A means that it doesn't need a displayed version when we apply ×^d in the S case.

X : (A :^Δ Disc) → ((a :^Δ A)) → SST) → SST
Z (X A X) = ((a :^Δ A) → Z (X a))
S (X A X) p = X^d A X (λ a → S (X a) (p a))

However, there are some things we would naturally expect to be able to define that do not seem possible with our current theory. For example, the disjoint union of semi-simplicial types should certainly have the disjoint union of 0-simplices, but the slice over a 0-simplex should come only from one of the two sides. That is, S (X + Y) (inl x) should be morally just S X x. However, S X x belongs to SST^d X, whereas S (X + Y) (inl x) must belong to SST^d (X + Y); thus we need to take its disjoint union with an empty semi-simplicial type displayed over Y.

We defined a 'global' empty semi-simplicial type above, and it seems intuitively that we should be able to define a 'constant' version of this displayed over Y. But as noted in section 3.1, without symmetry it does not seem possible to formulate a useful corecursor for SST^d, and without such a thing it is unclear how to define 'constantly displayed' semi-simplicial types. This suggests that further work in this direction might require the addition of symmetries.

35

### 3.3 DISPLAYED COINDUCTIVE TYPES

Generalizing the discussion of SST, we now formulate a fairly general notion of 'indexed displayed coinductive type'. It depends on a telescope \(\Phi\) of 'non-uniform parameters', and every element of it has a 'head' belonging to some specified type family \(A\) and a 'tail', depending on a telescope of parameters \(\mathcal{B}\), and belonging to the displayed version of the coinductive type itself. The parameters of this displayed version of the very type being defined are \(\Phi^{\mathrm{D}}\), which we can assemble provided that the data of the old parameters \(\varphi : \Phi\), the head \(x: A \varphi\), and the new dependencies \(b: \mathcal{B} \varphi a\), are sufficient to extract a section \(\sigma \varphi x b: \Phi^{\mathrm{d}} \varphi\). The idea is analogous to an 'indexed M-type', but with the output of the tail being displayed, and with \(\mathcal{B}\) being a telescope rather than a simple type. The pseudo-Agda corresponding to this would be:

module = (Φ : △□ Tel) (A : △□ Φ → Type) (B : △□ (φ : Φ) (a : A φ) → Tel)
(σ : △□ (φ : Φ) (a : A φ) (b : B φ a) → Φ\( ^{d} \) φ) where
codata dCoind (φ : Φ) : Type where
head : dCoind φ → A φ
tail : (x : dCoind φ) (b : B φ (head x)) → dCoind\( ^{d} \) ⟨φ , σ φ (head x) b⟩ x

We can thus write down the formation and introduction rules for dCoind as follows:

\(\begin{array}{c}\Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\Phi \operatorname {tel}_{\ell_0}\qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\Lambda \operatorname {type}_{\ell_1} / \varphi :\Phi \\ \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\mathcal{B}\operatorname {tel}_{\ell_2} / \varphi :\Phi ,a:A\varphi \qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\sigma :\left(\left(\Phi^{\mathrm{d}}\varphi\right)\right)_{\varphi :\Phi ,a:A\varphi ,b:\mathcal{B}\varphi x}\\ \hline \Gamma \vdash_{\mathrm{sm}}\mathrm{dCoind}_{[\Phi ,A,\mathcal{B},\sigma ]}\operatorname {type}_{\ell_1\sqcup \ell_2} / \varphi :\Phi [\mathbf{a}_{\mathbf{a}}\triangle \square \leqslant 1_{\mathrm{sm}}]\\ \Gamma \vdash_{\mathrm{sm}}\operatorname {head}_{[\Phi ,A,\mathcal{B},\sigma ]}:(A[\mathbf{a}_{\mathbf{a}}\triangle \square \leqslant 1_{\mathrm{sm}}]\varphi))_{\varphi ,x:\mathrm{dCoind}_{[\Phi ,A,\mathcal{B},\sigma ]}}\varphi \\ \Gamma \vdash_{\mathrm{sm}}\operatorname {tail}_{[\Phi ,A,\mathcal{B},\sigma ]}:(dCoind_{[\Phi ,A,\mathcal{B},\sigma ]}^{\mathrm{d}}\langle \varphi ,\sigma \varphi (\operatorname {head}x)b\rangle x))_{\varphi ,x,b:\mathcal{B}[\mathbf{a}_{\mathbf{a}}\triangle \square \leqslant 1_{\mathrm{sm}}]\varphi (\operatorname {head}\varphi x)} \end{array}\)

Note that the universe level of dCoind is governed by those of A and B, but does not depend on the level of the telescope of non-uniform parameters  \( \Phi \) .

Following the example of SST, we will begin by attempting to write down a reasonable template for a coinduction principle. In the same module context, we can attempt to map into a dCoind type from a length two context as follows:

f : (t : X) (s : Y t) → dCoind (φ t s)
head (f t s) = (?h₁ : A (φ t s))
tail (f t s) b = fᵈ t (?t₁ : Xᵈ t) s (?t₂ : Yᵈ t ?t₁ s)

The types that we have are then:

\[
\text { tail } (f t s) b: d \text { Coind } ^ {d} \langle \phi t s, \sigma (\phi t s)? _ {h _ {1}} b \rangle (f t s)
\]

\[
f ^ {d} t? _ {t _ {1}} s? _ {t _ {2}}: d \text { Coind } ^ {d} \langle \phi t s, \phi^ {d} t? _ {t _ {1}} s? _ {t _ {2}} \rangle (f t s)
\]

Thus there is a non-trivial condition that needs to be imposed for this definition template to be well typed. Fortunately, unlike in the case of  \( SST^{d} \) , we generally have terms lining up in the sense that the terminal (f t s) terms align, which avoids the vicious cycle from before. We get the following rule:

\(\begin{array}{c}\Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\Upsilon \operatorname {tel}_{\ell^{\prime}}\qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\phi :\left((\Phi)\right)_{v:\Upsilon}\\ \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\overline{h}:(A(\phi v))_{v:\Upsilon}\qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\overline{\tau}:((\Upsilon^{d}v))_{v:\Upsilon ,b:\mathcal{B}(\phi v)(\overline{h} v)}\\ \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}|v:\Upsilon ,b:\mathcal{B}(\phi v)(\overline{h} v)\vdash \phi^{d}\langle v,\overline{\tau} v b\rangle \equiv \sigma (\phi v)(\overline{h} v)b\\ \hline \Gamma \vdash_{\mathrm{sm}}\operatorname {corec}_{[\Phi ,A,\mathcal{B},\sigma ]}[\Upsilon ,\phi ,\overline{h},\overline{\tau} ]:(dCoind_{[\Phi ,A,\mathcal{B},\sigma ]}(\phi v))_{v:\Upsilon} \end{array}\)

36

This comes with the following computation rules:

$$\text{head } (\phi \upsilon) \left( \text{corec}_{[\Phi, A, \mathcal{B}, \sigma]} [\Upsilon, \phi, \bar{h}, \bar{\tau}] \upsilon \right) \equiv \bar{h} \upsilon$$

$$\text{tail } (\phi \upsilon) \left( \text{corec}_{[\Phi, A, \mathcal{B}, \sigma]} [\Upsilon, \phi, \bar{h}, \bar{\tau}] \upsilon \right) \mathfrak{b} \equiv \left( \text{corec}_{[\Phi, A, \mathcal{B}, \sigma]} [\Upsilon, \phi, \bar{h}, \bar{\tau}] \right)^d \langle \upsilon, \bar{\tau} \upsilon \mathfrak{b} \rangle$$

Now we can define SST as a particular instance of an indexed displayed coinductive type (which happens to have trivial indexing). In fact, it is in some sense the universal such instance, where the family $\mathcal{B}$ indexed by $A$ is the universal family $\mathcal{EI}$ indexed by $\text{Type}_\ell$. This may be compared with the fact that the $W$-type of $\mathcal{EI}$ is the type of 'presentations of well-founded sets' [Acz78], while its $M$-type is the type of 'presentations of ill-founded sets' [Lin89].

$$\text{SST}_\ell \equiv \text{dCoind} \left[ ()_{\text{sm}}, ((\text{Type}_\ell))_{\varphi:()_{\text{sm}}}, ((\text{EI X}))_{X:\text{Type}_\ell}, [\![\!]_{\text{sm}}]\!]_{X:\text{Type}_\ell, x:\text{EI X}} \right]$$

This is the end of all the primitive rules and definitions we have to give. From here, we can deduce the rules for $\text{SST}_\ell$, defining $Z \equiv \text{head}$ and $S \equiv \text{tail}$ and $R \equiv \text{corec}$:

$$\overline{\Gamma \vdash_{\text{sm}} Z : ((\text{Type}_\ell))_{X:\text{SST}_\ell}} \quad \overline{\Gamma \vdash_{\text{sm}} S : ((\text{SST}_\ell^d X))_{X:\text{SST}_\ell, x:\text{EI}(Z X)}}$$

$$\frac{\Gamma, \widehat{\bullet}_{\Delta\square} \vdash_{\text{sm}} \Upsilon \text{tel}_{\ell'}}{\Gamma, \widehat{\bullet}_{\Delta\square} \vdash_{\text{sm}} \bar{Z} : ((\text{Type}_\ell))_{\upsilon:\Upsilon} \quad \Gamma, \widehat{\bullet}_{\Delta\square} \vdash_{\text{sm}} \bar{S} : ((\Upsilon^d \upsilon))_{\upsilon:\Upsilon, x:\text{EI}(\bar{Z}\upsilon)}}{\Gamma \vdash_{\text{sm}} R_\Upsilon \bar{Z} \bar{S} : ((\text{SST}_\ell))_{\upsilon:\Upsilon}}$$

The problem of giving a corecursion rule for $\text{SST}^d$ carries over to the general case in the following way. Just as $^d$ of a $\Pi$-type is another $\Pi$-type and so on for records and ordinary coinductive types, We'd like to compute $^d$ of a dCoind to be another dCoind, with something like the following:

$$\begin{array}{l} \text{dCoind}_{[\Phi, A, \mathcal{B}, \sigma]^d} \equiv \text{dCoind} \left[ (\varphi^+: \Phi^D, c: \text{dCoind}_{[\Phi, A, \mathcal{B}, \sigma]} \varphi^{+\text{ev}}), \right. \\ \left. \left( (A^d \varphi^+ (\text{head } c))_{\varphi^+, c}, ((\mathcal{B}^D \varphi^+ (\text{head } c) a'))_{\varphi^+, x, a'}, \right. \right. \\ \left. \left[ \sigma^D \varphi^+ [\text{head } c, a'] \mathfrak{b}^+, \text{tail } c \mathfrak{b}^{+\text{ev}} \right]_{\varphi^+, c, a', \mathfrak{b}^+} \right] \end{array}$$

To see whether this is well-typed, observe that we have

$$\begin{array}{l} \varphi: \Phi, a: A \varphi, \mathfrak{b}: \mathcal{B} \varphi a \vdash_{\text{sm}} \sigma \varphi a \mathfrak{b}: \Phi^d \varphi \\ \varphi^+: \Phi^D, a: A, a': A^d a, \mathfrak{b}^+: \mathcal{B}^D \varphi^+ [a, a'] \vdash_{\text{sm}} \sigma^D \varphi^+ [a, a'] \mathfrak{b}^+: \Phi^{dD} \varphi^+ \end{array}$$

whereas the $\sigma$ of the resulting dCoind must lie in $(\varphi^+: \Phi^D, c: \text{dCoind}_{[\Phi, A, \mathcal{B}, \sigma]} \varphi^{+\text{ev}})^d$. Thus, in particular, we need to compare $\Phi^{dD} \varphi^+$ to $\Phi^{Dd} \varphi^+$, where $\varphi^+: \Phi^D$. In the case of a one-type telescope $\Phi = (a: A)$, this becomes

$$\begin{array}{l} \Phi^D \equiv (a: A, a': A^d a) \\ \Phi^d a \equiv (a': A^d a) \\ \Phi^{dD} [a, a'] \equiv (a'': A^d a, a''': A^{dd} a a' a'') \\ \Phi^{Dd} [a, a'] \equiv (a'': A^d a, a''': A^{dd} a a'' a') \end{array}$$

37

Unfortunately the last two are not the same! This is not just about ordering the variables in a telescope; although the second and third arguments of $A^{dd}$ both lie in $A^d$ $a$, it need not be symmetrical with respect to those arguments. So again we see that without adding symmetry to the theory, it seems we can't give a general corecursor for $d\text{Coind}^d$, and hence we can't compute $\text{corec}^d$ to something more primitive.

### 3.4 EXAMPLES OF DISPLAYED COINDUCTIVE TYPES

We now continue our exploration of the theory of semi-simplicial types from section 3.2, now using the general notion of displayed coinductive type. As in section 3.2, we will use Agda-esque codata and copattern-matching definitions, and assume that our type theory has plenty of other structure.

We have already noted that SST is in some sense the 'universal' (unparametrised) displayed coinductive type, whose determining family $x : A \vdash \mathcal{B} \times \text{type}_{\ell_2}$ is the universal one $X : \text{Type}_\ell \vdash \text{El} \times \text{type}_\ell$. Moreover, it seems likely that in order for an unparametrised displayed coinductive type to be interesting, the types $A$ and $\mathcal{B}$ must have nontrivial display structure, i.e. they must not be discrete. But the simplicial universe $\text{Type}_\ell$ is the primary source of types with nontrivial display, just as the universe in homotopy type theory is a primary source of types with higher homotopy structure. (In section 5.0.0.9 we will speculate about a notion of 'display inductive type' analogous to higher inductive types, which are the other source of higher homotopy structure in homotopy type theory.) For these reasons, we do not have a lot of interesting examples of other unparametrised displayed coinductive types, but there is at least one: augmented semi-simplicial types.

#### 3.4.1 Augmented semi-simplicial types

If we simply omit the Z input of S in the definition of SST, we obtain a definition of augmented semi-simplicial types. (Recall from section 1 that these are equivalently unary semicubical types.)

codata ASST : Type where
Z+ : ASST → Type
S+ : (A : ASST) → ASSTd A

We can convince ourselves of this by extracting types of low-dimensional simplices from an X : ASST:

$$\vdash X_{-1} \equiv Z^+ X$$

$$\mathfrak{z}_i : X_{-1} \vdash X_0 \mathfrak{z}_i \equiv Z^{+d} (S^+ X)$$

$$\mathfrak{z}_i : X_{-1}, x_0 : X_0 \mathfrak{z}_i, x_0 : X_0 \mathfrak{z}_i \vdash X_1 \mathfrak{z}_i x_0 x_0 \equiv Z^{+dd} (S^{+d} (S^+ X)) \mathfrak{z}_i x_0 x_0$$

and so on. Now we can observe that the construction Fib of section 3.2.4 factors through ASST via a pair of maps, both defined by copattern-matching:

Int : (X : Type) → ASST
Z+ (Int X) = X
S+ (Int X) = Intd X

38

Fib' : (X : ASST) (x : Z⁺ X) → SST
Z (Fib' X x) = Z⁺ᵈ (S⁺ X) x
S (Fib' X x) y = Fib'ᵈ X (S⁺ X) x y

#### 3.4.2 Pointed semi-simplicial types

More interesting examples of displayed coinductive types have nontrivial parametrizations, often involving more semi-simplicial types. For instance, we can define the structure of a pointing on a semi-simplicial type displayed-coinductively:

codata Pt (X : SST) : Type where
zp : Pt X → Z X
sp : (p : Pt X) → Pt^d X (S X (zp p)) p

We then have, for p : Pt X,

zp p : Z X ≡ X₀
zpᵈ (sp p) : Zᵈ (S X (zp p)) (zp p) ≡ X₁ (zp p) (zp p)
zpᵈᵈ (spᵈ (sp p)) : X₂ (zp p) (zp p) (zpᵈ (sp p)) (zp p) (zpᵈ (sp p)) (zpᵈ (sp p))

and so on. That is, an element of Pt X equips X with a 'fat point', i.e. a chosen 0-simplex zp that comes with all of the higher 'degenerate simplices' that one would expect to be associated to zp if it were in a simplicial set rather than a semi-simplicial one.

#### 3.4.3 Morphisms of semi-simplicial types

With a double parametrization, we can define a type of morphisms of semi-simplicial types.

codata Hom (X Y : SST) : Type where
zhom : Hom X Y → Z X → Z Y
shom : (f : Hom X Y) (x : Z X) → Hom^d X (S X x) Y (S Y (zhom f x)) f

As usual, we can unravel this a few steps to see what it looks like. zhom f is a function between types of 0-simplices, which we may denote \( f_0 \). At the next dimension we have:

\( zhom^{d} \)  (shom f  \( x_{0} \) )  \( x_{0} \)   \( \beta_{0} \) :  \( Z^{d} \)  (S Y (zhom f  \( x_{0} \) )) (zhom f  \( x_{0} \) )

which is to say

\( zhom^{d} \)  (shom f  \( x_{0} \) )  \( x_{0} \) :  \( X_{1} \)   \( x_{0} \)   \( x_{0} \)  →  \( Y_{1} \)  ( \( f_{0} \)   \( x_{0} \) ) ( \( f_{0} \)   \( x_{0} \) ).

We may denote this function by  \( f_{1} \) , and go on to extract a function  \( f_{2} \)  between types of 2-simplices and so on. We expect other basic operations on semi-simplicial types to be internalizable in a similar way.

## 4 Semantics

We now discuss the semantics of dTT. Specifically, we will show that from any model of ordinary dependent type theory with infinite limits, we can construct a model of dTT in which the original model sits as the discrete mode.

39

**Remark 4.1.** Actually we will not quite model all of dTT as presented in section 2: we omit the type-former $\triangle$ and its associated introduction and elimination rule. This is purely for reasons of simplicity and space. It should be possible to model $\triangle$ as well as long as the starting discrete model has a unit type, but we leave the details for the future. We will, however, still model $\triangle$-annotated variables and function types such as $(x : \triangle A) \to B x$.

In section 4.1 we review the semantics of ordinary dependent type theory, introduce some notation, extend this to our calculus of telescopes and meta-abstractions, and define what it means for such a model to have countable infinite limits. Then in section 4.2 we construct a model of augmented semi-simplicial Reedy diagrams, starting with any model of dependent type theory having countable infinite limits. This is essentially an instance of the general inverse diagram models constructed in [Shu15, KL21], but we give an explicit inductive construction that avoids category-theoretic machinery and builds display and décalage in from the beginning. In section 4.3 we add modalities to this model, and then in section 4.4 we discuss the *general* notion of model of dTT and show that the simplicial model is in fact such. Finally, in section 4.5 we construct displayed coinductive types in these models, including the type SST of semi-simplicial types.

## 4.1 THE SEMANTICS OF DEPENDENT TYPE THEORY

We approach semantics from the perspective of *Categories with Families* (CwF) [CCD21]. Here we will recount the relevant categorical concepts while providing a translation into language reminiscent of a type theoretic logical framework.

At the most basic level, a category with families is just a category with a terminal object and distinguished substructure of objects and morphisms that behave like *types* and *terms* in a dependent type theory. In the absence of any other structure, the only way in which this behaviour is manifested is through the presence of *substitution*, which categorically corresponds to a choice of definitionally functorial distinguished pullbacks. Here, instead of giving the substructure as a proposition on objects and morphisms, we first give it as presheaves, and then use representability to overlay this structure into the category.

### 4.1.1 Categories with Families

A 'CwF with levels' consists of a category $\mathcal{C}$, along with a chosen terminal object $\mathbb{I}$, and equipped with the data of two families of presheaves, indexed by $\ell$ level:

$$\text{Ty}_\ell : \mathcal{C}^{\text{op}} \to \text{Set} \quad \quad \quad \quad \quad \quad \quad \text{Tm}_\ell : \left( \int^{\mathcal{C}} \text{Ty}_\ell \right)^{\text{op}} \to \text{Set},$$

such that for every $\Gamma : \text{ob}_\mathcal{C}$ and $A : \text{Ty}_\ell \Gamma$, there is a chosen representation of the presheaf:

$$\Delta \mapsto \{\sigma : \text{mor}_\mathcal{C}(\Delta, \Gamma)\} \times \text{Tm}_\ell(\Delta, A^\sigma).$$

### 4.1.2 Notation

The objects of the category $\mathcal{C}$ are called *contexts* and denoted by $\Gamma, \Delta$. For $\Gamma : \text{ob}_\mathcal{C}$ we write:

$\Gamma$ ob

40

The empty context is the chosen terminal object $\mathbb{1}$, and is denoted by:

$$\text{() ob}$$

The morphisms of $\mathcal{C}$ are called substitutions and denoted by $\sigma$, $\tau$. For $\sigma : \text{mor}_{\mathcal{C}}(\Delta, \Gamma)$ we write:

$$\sigma : \Delta \to \Gamma$$

The unique substitution into the empty context is denoted by:

$$\text{[] : } \Gamma \to \text{()}$$

The notations $\Gamma$ ob and $\sigma : \Delta \to \Gamma$ are examples of 'absolute' or 'context-less' judgments. In the notation of this section, each absolute judgment asserts that some element belongs to some set, such as the set of objects or a hom-set of $\mathcal{C}$. Note that a set can be 'dependent' on elements of another set, such as the hom-set $\text{mor}_{\mathcal{C}}(\Delta, \Gamma)$ depending on $\Delta$, $\Gamma : \text{ob}_{\mathcal{C}}$; and thus elements of one absolute judgment can appear in another absolute judgment, such as $\sigma : \Delta \to \Gamma$ where $\Delta$ ob and $\Gamma$ ob. Operations on sets can be written as rules, such as composition of morphisms:

$$\frac{\sigma : \Delta \to \Gamma \qquad \tau : \Gamma \to \Theta}{\tau \circ \sigma : \Delta \to \Theta}.$$

Equations between these operations can likewise be written as rules, where we use $\equiv$ for equality since it corresponds to definitional equality in syntax:

$$\frac{\sigma : \Delta \to \Gamma \qquad \tau : \Gamma \to \Theta \qquad \upsilon : \Theta \to \Upsilon}{\upsilon \circ (\tau \circ \sigma) \equiv (\upsilon \circ \tau) \circ \sigma}.$$

The elements of $\text{Ty}_{\ell}$ are called types of level $\ell$ and denoted by $A, B$. For $A : \text{Ty}_{\ell} \Gamma$ we write:

$$\gamma : \Gamma \vdash A \ \gamma \ \text{type}_{\ell}$$

Similarly, the elements of $\text{Tm}_{\ell}$ are called terms and denoted by $t$, $s$. For $t : \text{Tm}_{\ell}(\Gamma, A)$ we write:

$$\gamma : \Gamma \vdash t \ \gamma : A \ \gamma$$

These notations are examples of 'hypothetical' or 'contextual' judgments. In the notation of this section, each hypothetical judgment asserts that some element belongs to a value of some presheaf, such as $\text{Tm}_{\ell}$ or $\text{Ty}_{\ell}$. The object of $\mathcal{C}$ at which the presheaf is evaluated (in these examples, $\Gamma$) is written on the left-hand side of the turnstile $\vdash$. We annotate it with a formal 'variable' such as $\gamma$, and 'apply' all the elements appearing on the right-hand side to that element; at the moment this is just a convention of notation. As with absolute judgments, one presheaf can be dependent on another, such as $\text{Tm}_{\ell}(\Gamma, A)$ depending on $A : \text{Ty}_{\ell} \Gamma$; and thus the elements of one hypothetical judgment can appear in another hypothetical judgment, such as $\gamma : \Gamma \vdash t \ \gamma : A \ \gamma$ where $\gamma : \Gamma \vdash A \ \gamma \ \text{type}_{\ell}$.

For a morphism $\sigma : \Delta \to \Gamma$, we denote its functorial action on types $A$ and terms $t$ by $A^{\sigma}$ and $t^{\sigma}$; thus the presheaf actions of $\text{Ty}_{\ell}$ and $\text{Tm}_{\ell}$ can be expressed by rules

$$\frac{\sigma : \Delta \to \Gamma \qquad \gamma : \Gamma \vdash A \ \gamma \ \text{type}_{\ell}}{\delta : \Delta \vdash A^{\sigma} \ \delta \ \text{type}_{\ell}}$$

$$\frac{\sigma : \Delta \to \Gamma \qquad \gamma : \Gamma \vdash t : A}{\delta : \Delta \vdash t^{\sigma} \ \delta : A^{\sigma} \ \delta}$$

41

We allow ourselves to write this alternatively by taking the formal variables $\gamma, \delta$ more seriously and 'applying' $\sigma$ to them:

$$\delta : \Delta \vdash A \ (\sigma \ \delta) \ \text{type}_\ell \qquad \delta : \Delta \vdash t \ (\sigma \ \delta) : A \ (\sigma \ \delta)$$

Formally, this is justified by interpretation in the internal type theory of the presheaf category $\text{Set}^{\text{CW}}$. By virtue of functoriality, for $\sigma : \Delta \to \Gamma$ and $\tau : \Omega \to \Delta$ we have that

$$A \ (\sigma \ (\tau \ \omega)) \equiv A \ ((\sigma \circ \tau) \ \omega) \qquad t \ (\sigma \ (\tau \ \omega)) \equiv t \ ((\sigma \circ \tau) \ \omega)$$

Now let us consider the representation hypothesis. In categorical notation, for $\Gamma : \text{ob}_\mathcal{C}$ and $A : \text{Ty}_\ell$ we have a representing object $\Gamma \cdot A : \text{ob}_\mathcal{C}$ called the context extension. In type-theoretic notation, we denote the context extension by

$$\frac{\Gamma \text{ ob} \qquad \gamma : \Gamma \vdash A \ \gamma \ \text{type}_\ell}{(\gamma : \Gamma, \ a : A \ \gamma) \ \text{ob}}$$

Note that this is an operation that takes an element of one set (the absolute judgment $\Gamma$ ob) and an element of one presheaf (the hypothetical judgment $\gamma : \Gamma \vdash A \ \gamma \ \text{type}_\ell$) and produces an element of a set (the absolute judgment $(\gamma : \Gamma, \ a : A \ \gamma)$ ob). As before, at the moment the 'variables' $\gamma$ and $a$ are just a convention of notation.

We then have a family of bijections, natural in $\Delta$:

$$(\Delta \to (\gamma : \Gamma, \ a : A \ \gamma)) \simeq ((\sigma : \Delta \to \Gamma) \times (\delta : \Delta \vdash t \ \delta : A \ (\sigma \ \delta)))$$

Note that this says that a substitution into an extended context $(\gamma : \Gamma, \ a : A \ \gamma)$ is precisely a substitution $\sigma$ into $\Gamma$, along with some term $t$ of type $A^\sigma$. By the Yoneda lemma, the left-to-right part of this bijection is determined by setting $\Delta$ to $(\gamma : \Gamma, \ a : A \ \gamma)$ and evaluating at the identity $1_{(\gamma : \Gamma, \ a : A \ \gamma)}$. The first component gives us a substitution $\text{pt}^A : (\gamma : \Gamma, \ a : A \ \gamma) \to \Gamma$, which we call a fundamental context projection or parent map$^7$ and denote by:

$$\text{pt}^A : (\gamma : \Gamma, \ a : A \ \gamma) \to \Gamma$$

The second component then gives us a term that we call the zero variable and denote by $\text{zv}^A : \text{Tm}((\gamma : \Gamma, \ a : A \ \gamma), A^{\text{pt}^A})$, or:

$$\delta : (\gamma : \Gamma, \ a : A \ \gamma) \vdash \text{zv}^A \ \delta : A \ (\text{pt}^A \ \delta)$$

Note that the forward direction of the bijection sends a substitution $\tau : \Delta \to (\gamma : \Gamma, \ a : A \ \gamma)$ to the pair $(\text{pt}^A \circ \tau, \ (\text{zv}^A)^\top)$. That this map is a bijection is witnessed by the existence of a substitution extension operation:

$$\frac{\sigma : \Delta \to \Gamma \qquad \delta : \Delta \vdash t \ \delta : A \ (\sigma \ \delta)}{[\sigma, \ t] : \Delta \to (\gamma : \Gamma, \ a : A \ \gamma)}$$

such that for $\sigma : \Delta \to \Gamma$ and $\delta : \Delta \vdash t \ \delta : A \ (\sigma \ \delta)$, we have:

$$\text{pt}^A \circ [\sigma, \ t] \equiv \sigma \tag{4.2}$$

$$(\text{zv}^A)^{[\sigma, \ t]} \equiv t \tag{4.3}$$

$^7$From the perspective of type theoretic fibration categories, an alternative approach to semantics from that of CwFs, the role of fundamental context projections is instead played by fibrations.

42

and, conversely, for $\tau : \Delta \to (\gamma : \Gamma, a : A \gamma)$, we have:

$$[ \mathrm{pt}^A \circ \tau, (\mathrm{zv}^A)^\tau ] \equiv \tau. \tag{4.4}$$

As a corollary of this we have that the following diagram is a pullback:

$$\begin{array}{c} (\delta : \Delta, a : A (\sigma \delta)) \xrightarrow{[\sigma \circ \mathrm{pt}^{A^\sigma}, \mathrm{zv}^{A^\sigma}]} (\gamma : \Gamma, a : A \gamma) \\ \mathrm{pt}^{A^\sigma} \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Delta \xrightarrow{\sigma} \Gamma \end{array}$$

So, in particular, in a CwF we have a distinguished pullback of any parent map along an arbitrary morphism, as another parent map, and this choice of pullbacks is definitionally functorial. We will often omit the superscripts from pt and zv.

The map constructed from $\sigma$ in the top row of the diagram above will occur frequently in the exposition that follows, and we shall refer to it as the weakening two of $\sigma$ by $A$. Formally, given $\sigma : \Delta \to \Gamma$, and $\gamma : \Gamma \vdash A \gamma \text{ type}_\ell$, we have:

$$W_2^A \sigma : (\theta : \Theta, a : A (\sigma \theta)) \to (\gamma : \Gamma, a : A \gamma)$$

$$W_2^A \sigma = [\sigma \circ \mathrm{pt}, \mathrm{zv}]$$

Finally, when working with hypothetical judgments in an extended context, we can also treat the variables more traditionally. Instead of $\delta : (\gamma : \Gamma, a : A \gamma) \vdash B \delta \text{ type}_{\ell_1}$, we write $\gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}$, and so on. In particular, the zero variable zv can be written more simply as

$$\gamma : \Gamma, a : A \gamma \vdash a : A \gamma$$

As before, this can be justified formally as an interpretation in the internal type theory of $\mathsf{Set}^{\mathrm{true}}$.

### 4.1.3 $\Pi$-Types

All the basic type-forming operations in syntax translate into structure on a CwF. For instance, a $\Pi$-structure on a CwF with levels consists of the following structure and properties:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_{\ell_0} \qquad \gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash (\Pi A B) \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma, a : A \gamma \vdash t \gamma a : B \gamma a}{\gamma : \Gamma \vdash (\lambda t) \gamma : (\Pi A B) \gamma}$$

$$\frac{\gamma : \Gamma \vdash f \gamma : (\Pi A B) \gamma \qquad \gamma : \Gamma \vdash s \gamma : A \gamma}{\gamma : \Gamma \vdash (\mathrm{app} f s) \gamma : B^{[1_r, s]} \gamma}$$

The above notation lets us talk about types in point-free notation, e.g. $\Pi A B : \mathsf{Ty}_\ell \Gamma$. When the explicit dependence on $\gamma$ is written, we can propagate the notation as follows:

$$(\Pi A B) \gamma \equiv (a : A \gamma) \to B \gamma a$$

$$(\lambda t) \gamma \equiv \lambda a . t \gamma a$$

$$(\mathrm{app} f s) \gamma \equiv \mathrm{app} \gamma (f \gamma) (s \gamma)$$

43

Such that the $\beta$ and $\eta$ laws hold:

$$\frac{\gamma : \Gamma, a : A \gamma \vdash t \gamma a : B \gamma a \quad \gamma : \Gamma \vdash s \gamma : A \gamma}{\gamma : \Gamma \vdash (\text{app } (\lambda t) s) \gamma \equiv t^{[1_r, s]} \gamma : B^{[1_r, s]} \gamma}$$

$$\frac{\gamma : \Gamma \vdash f \gamma : (a : A \gamma) \rightarrow B \gamma a}{\gamma : \Gamma \vdash (\lambda (\text{app } f^{\text{pt}} z v)) \gamma \equiv f \gamma : (\Pi A B) \gamma}$$

Or, in indexed notation:

$$\gamma : \Gamma \vdash \text{app } \gamma (\lambda a . t \gamma a) (s \gamma) \equiv t \gamma (s \gamma) : B \gamma (s \gamma)$$

$$\gamma : \Gamma \vdash \lambda a . \text{app } [\gamma, a] (f \gamma) a \equiv f \gamma : (a : A \gamma) \rightarrow B \gamma a$$

And such that the above constructs are stable under substitution, i.e. for $\sigma : \Delta \rightarrow \Gamma$:

$$(\Pi A B)^\sigma \equiv \Pi A^\sigma B^{W_2^\Delta \sigma}$$

$$(\lambda t)^\sigma \equiv \lambda t^{W_2^\Delta \sigma}$$

$$(\text{app } f s)^\sigma \equiv \text{app } f^\sigma s^\sigma$$

### 4.1.4 Universes

A $\mathcal{U}$-structure on a CwF with levels consists of the following structure and properties:

$$\frac{\ell \text{ level}}{\gamma : \Gamma \vdash \text{Type}_\ell \gamma \text{ type}_{\text{lsuc } \ell}}$$

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_\ell}{\gamma : \Gamma \vdash \text{Code } A \gamma : \text{Type}_\ell \gamma}$$

$$\frac{\gamma : \Gamma \vdash A \gamma : \text{Type}_\ell \gamma}{\gamma : \Gamma \vdash \text{EI } A \gamma \text{ type}_\ell}$$

Such that Code and EI are mutual inverses:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_\ell}{\gamma : \Gamma \vdash \text{EI } (\text{Code } A) \gamma \equiv A \gamma}$$

$$\frac{\gamma : \Gamma \vdash A \gamma : \text{Type}_\ell \gamma}{\gamma : \Gamma \vdash \text{Code } (\text{EI } A) \gamma \equiv A \gamma : \text{Type}_\ell \gamma}$$

And such that the above constructs are stable under substitution, i.e. for $\sigma : \Delta \rightarrow \Gamma$:

$$\text{Type}_\ell^\sigma \equiv \text{Type}_\ell$$

$$(\text{Code } A)^\sigma \equiv \text{Code } A^\sigma$$

$$(\text{EI } A)^\sigma \equiv \text{EI } A^\sigma$$

### 4.1.5 Natural models

We recall from [Awo18] that a CwF can equivalently be described as a natural model: a category $\mathcal{C}$ together with an (algebraically) representable natural transformation $\text{pr} : \text{Tm} \rightarrow \text{Ty}$ of presheaves on $\mathcal{C}$. This amounts to representing the dependency of terms on types in 'fibered' rather than 'indexed' style, which is different from the usual type-theoretic notation, but it has the advantage that various operations can cleanly be described in terms of pr. Similarly, of course, a CwF with levels can be described by a family of representable transformations $\text{pr}_\ell : \text{Tm}_\ell \rightarrow \text{Ty}_\ell$.

In particular, like any morphism in a locally cartesian closed category, any such pr induces a polynomial endofunctor $P_{\text{pr}}$ of the presheaf category, where for any presheaf

44

(i.e. judgment) X, morphisms $\mathcal{X} \to P_{\mathrm{pr}}(X)$ (i.e. elements of the presheaf $P_{\mathrm{pr}}(X)$) are bijectively related to pairs consisting of a type $A \in \mathrm{Ty}(\Gamma)$ in context $\Gamma$ and a morphism $\mathcal{X}(\gamma : \Gamma, a : A\gamma) \to X$ (i.e. an element of $X(\gamma : \Gamma, a : A\gamma)$). In syntax, this is a bidirectional rule, indicating a bijection between the data above and below the lines:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type } \quad \gamma : \Gamma, a : A \gamma \vdash \xi \gamma a : X}{\gamma : \Gamma \vdash \bar{\xi} \gamma : P_{\mathrm{pr}}(X)}$$

Thus, for instance, $P_{\mathrm{pr}_{\ell_0}}(\mathrm{Ty}_{\ell_1})$ represents families of types of level $\ell_1$ indexed by a type of level $\ell_0$. Therefore, formation rules such as those for $\Pi$-types and $\Sigma$-types:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash (\Pi A B) \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a : A \gamma \vdash B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash (\Sigma A B) \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

are represented by morphisms $\Pi, \Sigma : P_{\mathrm{pr}_{\ell_0}}(\mathrm{Ty}_{\ell_1}) \to \mathrm{Ty}_{\ell_0 \sqcup \ell_1}$.

The rules for terms can also be represented in this language. For instance, a natural model has $\Pi$-types if and only if there is a pullback square

$$\begin{array}{ccc} P_{\mathrm{pr}_{\ell_0}}(\mathrm{Tm}_{\ell_1}) & \longrightarrow & \mathrm{Tm}_{\ell_0 \sqcup \ell_1} \\ P_{\mathrm{pr}_{\ell_0}}(\mathrm{pr}_{\ell_1}) \downarrow & \downarrow & \downarrow \mathrm{pr}_{\ell_0 \sqcup \ell_1} \\ P_{\mathrm{pr}_{\ell_0}}(\mathrm{Ty}_{\ell_1}) & \xrightarrow[\Pi]{} & \mathrm{Ty}_{\ell_0 \sqcup \ell_1}, \end{array}$$

meaning that there is a bijection

$$\frac{\gamma : \Gamma, a : A \gamma \vdash t \gamma a : B \gamma a}{\gamma : \Gamma \vdash (\lambda t) \gamma : (\Pi A B) \gamma}$$

Polynomial functors can also be composed, yielding another polynomial functor. For instance, in a CwF without levels, $P_{\mathrm{pr}} \circ P_{\mathrm{pr}}$ is the functor such that $(P_{\mathrm{pr}} \circ P_{\mathrm{pr}})(X)$ represents elements of $X$ in a doubly-extended context ($\gamma : \Gamma, a : A\gamma, b : B\gamma a$), which means that it is the polynomial functor associated to the map $\mathrm{pr}^2 : \mathrm{Tm}^2 \to P_{\mathrm{pr}}(\mathrm{Ty})$ where the fiber of $\mathrm{Tm}^2(\Gamma)$ over $(A, B)$ consists of a pair of terms $\gamma : \Gamma \vdash a : A\gamma$ and $\gamma : \Gamma \vdash b : B\gamma a$. In particular, a CwF $\mathcal{C}$ has $\Sigma$-types if and only if $\Sigma : P_{\mathrm{pr}}(\mathrm{Ty}) \to \mathrm{Ty}$ represents any such pair by a single term, i.e. there is a pullback square

$$\begin{array}{ccc} \mathrm{Tm}^2 & \longrightarrow & \mathrm{Tm} \\ \mathrm{pr}^2 \downarrow & \downarrow & \downarrow \mathrm{pr} \\ P_{\mathrm{pr}}(\mathrm{Ty}) & \xrightarrow[\Sigma]{} & \mathrm{Ty}, \end{array}$$

This is equivalent to a (cartesian) morphism of polynomial functors $P_{\mathrm{pr}} \circ P_{\mathrm{pr}} \to P_{\mathrm{pr}}$. Of course, there is an analogous version for a CwF with levels.

45

#### 4.1.6 Telescopes

We will often have finite towers of types:

\[
\begin{array}{l} \gamma : \Gamma \vdash A \gamma \text { type } _ {\ell_ {0}} \\ \gamma : \Gamma , a: A \vdash B \gamma a t y p e _ {\ell_ {1}} \\ \gamma : \Gamma , a: A, b: B \gamma a b \vdash C \gamma a b t y p e _ {\ell_ {2}} \\ \end{array}
\]

We represent these with a single judgement, defining a telescope:

\[
\gamma : \Gamma \vdash (a: A \gamma , b: B \gamma a, c: C \gamma a b) \gamma t e l _ {\ell}.
\]

Formally speaking, telescopes and their elements (which we call partial substitutions) are another CwF structure on the same category of contexts, which are related to the original one by specified operations. In natural model style, the definition is:

Definition 4.5. A natural model with levels C has telescopes if it is equipped with:

- Another family of (algebraically) representable natural transformations \(\mathrm{tpr}_{\ell}:\mathrm{PSub}_{\ell}\to\) \(\mathrm{Tel}_{\ell}\). This yields two families of judgments for telescopes and partial substitutions:

\[
\gamma : \Gamma \vdash \Upsilon \gamma \operatorname{tel} _ {\ell} \quad \Gamma : \Gamma \vdash \upsilon : \Upsilon
\]

Their representability yields the extension of a context by a telescope:

\[
\frac {\Gamma \text {   ob   } \quad \gamma : \Gamma \vdash \Upsilon \gamma \text {   tel } _ {\ell}}{(\gamma : \Gamma | \nu : \Upsilon \gamma) \text {   ob.   }}
\]

- Morphisms of polynomial functors \(1_{\mathcal{C}} \to P_{\mathrm{tpr}_{\ell}}\), i.e. pullback squares

\[
\begin{array}{c} 1 \longrightarrow \text { PSub } _ {\ell} \\ \Big \downarrow \quad \text {   } \quad \Big \downarrow \text { tpr } _ {\ell} \\ 1 \xrightarrow {\quad (\quad)} \text { Tel } _ {\ell}. \end{array}
\]

This gives 'empty telescopes' \(\gamma : \Gamma \vdash ()\) tel\(_{\ell}\) containing exactly one partial substitution \(\gamma : \Gamma \vdash [] : ()\).

- Morphisms of polynomial functors \( \mathrm{P}_{\mathrm{tpr}_{\ell}} \circ \mathrm{P}_{\mathrm{pr}_{\ell'}} \to \mathrm{P}_{\mathrm{tpr}_{\ell}} \) whenever \( \ell' \leqslant \ell \). This says how to extend a telescope by a type:\( ^8 \)

\[
\frac {\gamma : \Gamma \vdash \Upsilon   \gamma   \text { tel } _ {\ell} \qquad \gamma : \Gamma   |   \upsilon : \Upsilon   \gamma \vdash A   \gamma   \upsilon   \text { type } _ {\ell^ {\prime}} \qquad \ell^ {\prime} \leqslant \ell}{\gamma : \Gamma \vdash (\upsilon : \Upsilon   \gamma ,   a : A   \gamma   \upsilon)   \text { tel } _ {\ell_ {0} \sqcup \ell}}
\]

such that the partial substitutions in  \( (\upsilon:\Upsilon\gamma,\;a:A\gamma\nu) \)  are exactly pairs of a partial substitution in  \( \Upsilon \)  and a term in A, just as for  \( \Sigma \) -types. Thus we get the rules from section 2.3.2.

\( ^{8} \) Note that  \( P_{tpr} \circ P_{pr} \)  is the polynomial functor associated to a map whose codomain is  \( P_{tpr}(Ty) \) , which is the presheaf of types in a context extended by a telescope.

46

- The rules \((\Gamma \mid (\cdot)_{\mathbb{P}}) \equiv \Gamma\) and \((\Gamma \mid (\Theta, x: A)) \equiv ((\Gamma \mid \Theta), x: A)\) from section 2.3.1 hold. Note that these are equalities of objects of \(\mathcal{C}\), and in particular only make sense if \(\mathbb{P}\) and \(\mathbb{P}\) are algebraically representable.
- A morphism of polynomial functors \(\mathrm{P_{tpr}_{i_0}}\circ \mathrm{P_{tpr}_{i_1}}\to \mathrm{P_{tpr}_{i_0 + i_1}}\), giving the extension of telescopes by telescopes \((\upsilon :\Upsilon |\phi :\Phi \upsilon)\) from section 2.5.2, such that the rules from that section hold:

$$
(\Gamma \mid (\Upsilon \mid \Phi)) \equiv ((\Gamma \mid \Upsilon) \mid \Phi) \qquad (\Upsilon \mid ()) \equiv \Upsilon \qquad (\Upsilon \mid (\Phi, x: A)) \equiv ((\Upsilon \mid \Phi), x: A)
$$

Syntactically, this definition represents the rules from sections 2.3.1, 2.3.2 and 2.5.2, in the non-modal case. Because it is phrased in terms of presheaves and operations on them, it implicitly includes substitution into telescopes that commute with the other operations. Some of these commutation properties refer to weakening-two, which can be characterised in terms of them as well, for instance:

$$
\frac{\gamma : \Gamma \vdash \Upsilon \gamma \operatorname{tel}_{\ell} \qquad \sigma : \Delta \to \Gamma}{\delta : \Delta \vdash \Upsilon (\sigma \delta) \operatorname{tel}_{\ell}} \qquad \frac{\sigma : \Delta \to \Gamma \qquad \gamma : \Gamma \vdash \Upsilon \gamma \operatorname{tel}_{\ell}}{W_2^\Upsilon \sigma : (\delta : \Delta, \upsilon : \Upsilon (\sigma \delta)) \to (\gamma : \Gamma, \upsilon : \Upsilon \gamma)}
$$

$$
()^\sigma \equiv () \qquad (\upsilon : \Upsilon \gamma, a: A \gamma \upsilon)^\sigma \delta \equiv (\delta : \Upsilon (\sigma \delta), a: A ((W_2^\Upsilon \sigma) [\delta, \upsilon])) \quad
$$

$$
W_2^{(1)} \sigma \equiv \sigma \qquad W_2^{(\Upsilon, A)} \sigma \equiv W_2^A (W_2^\Upsilon \sigma)
$$

For example, we have:

$$
(a: A \gamma, b: B \gamma a)^\sigma \delta \equiv (a: A (\sigma \delta), b: B (\sigma (\operatorname{pt} [\delta, a])) (\operatorname{zv} [\delta, a]))
$$

When we allow ourselves to use variables in the usual way, justified by the internal type theory of presheaves, we can write this as:

$$
(a: A \gamma, b: B \gamma a)^\sigma \delta \equiv (a: A (\sigma \delta), b: B (\sigma \delta) a)
$$

Note that the meaning of this construction is simply iterating the canonical construction of pullbacks over a tower:

• There is a pullback square

$$\begin{array}{c} \mathrm{P}_{\mathrm{tpr}_{\ell_0}}(\mathrm{PSub}_{\ell_1}) \longrightarrow \mathrm{PSub}_{\ell_0 \sqcup \ell_1} \\ \mathrm{P}_{\mathrm{tpr}_{\ell_0}}(\mathrm{tpr}_{\ell_1}) \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \\ \mathrm{P}_{\mathrm{tpr}_{\ell_0}}(\mathrm{Tel}_{\ell_1}) \xrightarrow{\Pi} \mathrm{Tel}_{\ell_0 \sqcup \ell_1}, \end{array}$$

• The computation rules from section 2.5.3 hold.

Now the above rules allow us to build telescopes up from the empty telescope by adding types, just as the rules of a CwF allow us to build contexts from the empty context by adding types. However, just as in the case of contexts, the rules do not stipulate that every telescope is obtained in that way. Indeed, there is no way to assert such a thing in a Generalised Algebraic Theory. However, it holds 'admissibly' in the initial syntactic model, and any CwF can be extended with telescopes in this way:

**Theorem 4.7.** *Any CwF with levels can be equipped with telescopes. If it has Π-types, it also has Π-telescopes.*

*Proof.* We define $\mathrm{tpr}_{\ell}$ to be the map such that

$$\mathrm{P}_{\mathrm{tpr}_{\ell}} = \sum_{\substack{n \leqslant n \\ \forall i \leqslant n, \ell_i \leqslant \ell}} \mathrm{P}_{\mathrm{pr}_{\ell_0}} \circ \dots \circ \mathrm{P}_{\mathrm{pr}_{\ell_n}}.$$

Thus an element of $\mathrm{Tel}_{\ell}(\Gamma)$ is a tower of $n$ types over $\Gamma$ of level $\leqslant \ell$, and similarly for terms. The two morphisms of polynomial functors are then immediate. We define context extension in the obvious way by iterating context extension by types, and the equations hold. (This is the *initial* structure of telescopes on $\mathcal{C}$ in a straightforward sense.) Similarly, we define Π-telescopes by using the rules for computing them on extended telescopes. $\square \triangleleft$

### 4.1.7 Meta-abstractions

Because meta-abstractions are not 'reified' in the theory as types, they do not require assuming any structure beyond that which is already present in the presheaf category. Specifically, the rules for the judgment $\Gamma \vdash A \text{ type}_{\ell: \Upsilon}$ simply say that it should be (up to isomorphism) the object $\mathrm{P}_{\mathrm{tpr}}(\mathrm{Ty})$ that classifies types indexed by a telescope. Similarly, the rules for the elements of a meta-abstraction simply say that these are the object $\mathrm{P}_{\mathrm{tpr}}(\mathrm{Tm})$ that classifies terms indexed by a telescope. In other words, meta-abstractions of types and their terms are classified by a map (isomorphic to) $\mathrm{P}_{\mathrm{tpr}}(\mathrm{pr})$. Likewise, meta-abstractions of telescopes (the judgment $\Gamma \vdash \Theta \text{ tel}_{\ell: \Upsilon}$) are classified by a map isomorphic to $\mathrm{P}_{\mathrm{tpr}}(\mathrm{tpr})$. This gives all the rules from sections 2.3.3 and 2.5.1; thus any natural model with telescopes also has meta-abstractions of types and telescopes.

Semantically, we don't ever need to discuss meta-abstractions explicitly, since to judge $\Gamma \vdash A \text{ type}_{\ell/\delta: \Upsilon}$ is equivalent to judging $\Gamma \mid \Upsilon \vdash A \text{ type}_{\ell}$, and so on. Thus we will generally talk only about types and telescopes in contexts. $\triangleleft$

48

#### 4.1.8 Infinite Telescopes

We now define a new judgement \(\gamma : \Gamma \vdash \bar{\Upsilon} \gamma \operatorname{stel}_{\ell}^{\infty}\) whose elements are 'infinite telescopes'. As with meta-abstractions, this is not (yet) introducing new structure on a CwF, rather it is a definition that can be made in the presheaf category of any CwF. The idea is that an infinite telescope consists of an infinite sequence of types each dependent on all the previous ones:

\[
\gamma : \Gamma \vdash \bar {\Upsilon} ^ {0} \gamma \text { type } _ {\ell_ {0}}
\]

\[
\gamma : \Gamma , v ^ {0}: \bar {\Upsilon} ^ {0} \gamma \vdash \bar {\Upsilon} ^ {1} \gamma v ^ {0} \text {type} _ {\ell_ {1}}
\]

\[
\gamma : \Gamma , v ^ {0}: \bar {\Upsilon} ^ {0} \gamma , v ^ {1}: \bar {\Upsilon} ^ {1} \gamma v ^ {0} \vdash \bar {\Upsilon} ^ {1} \gamma v ^ {0} v ^ {1} \text {type} _ {\ell_ {2}}
\]

•
•
•

where \(\ell_n \leqslant \ell\) for all \(n\). Formally, we define this along with its approximating finite telescopes:

\[
\bar {\Upsilon} ^ {\partial 0} \gamma \equiv ()
\]

\[
\bar {\Upsilon} ^ {\partial 1} \gamma \equiv (v ^ {0}: \bar {\Upsilon} ^ {0} \gamma)
\]

\[
\bar {\Upsilon} ^ {\partial 2} \gamma \equiv \left(v ^ {0}: \bar {\Upsilon} ^ {0} \gamma , v ^ {1}: \bar {\Upsilon} ^ {1} \gamma v ^ {0}\right)
\]

•
•
•

so that we can say that in general \(\bar{\Upsilon}^n\) is a type in context (\(\gamma : \Gamma \mid \upsilon : \bar{\Upsilon}^{\partial n}\)). In syntax, this means we give the following bidirectional rule with infinitely many premises:

\[
\begin{array}{l} \left(\gamma : \Gamma \vdash \bar {\Upsilon} ^ {\partial n} \gamma \operatorname{tel} _ {\ell}\right) _ {n \in \mathbb {N}} \quad \left(\gamma : \Gamma \mid \partial v: \bar {\Upsilon} ^ {\partial n} \gamma \vdash \bar {\Upsilon} ^ {n} \gamma \partial v \operatorname{type} _ {\ell_ {n}}\right) _ {n \in \mathbb {N}} \quad (\ell_ {n} \leqslant \ell) _ {n \in \mathbb {N}} \\ \bar {\Upsilon} ^ {\partial 0} \gamma \equiv () \quad (\gamma : \Gamma \vdash \bar {\Upsilon} ^ {\partial (n + 1)} \gamma \equiv (\partial v: \bar {\Upsilon} ^ {\partial n} \gamma , v: \bar {\Upsilon} ^ {n} \gamma \partial v)) _ {n \in \mathbb {N}} \\ \hline \gamma : \Gamma \vdash \bar {\Upsilon} \gamma \operatorname{stel} _ {\ell} ^ {\infty} \\ \end{array}
\]

(It would also be possible to define infinite contexts coinductively, but for our purposes this concrete definition is easier to work with.)

We have already defined substitution on finite telescopes, and that definition extends level-wise to infinite telescopes. Given \(\sigma : \Delta \to \Gamma\) and \(\gamma : \Gamma \vdash \bar{\Upsilon} \gamma \operatorname{stel}_{\ell}^{\infty}\), we define \(\delta : \Delta \vdash \bar{\Upsilon} (\sigma \delta) \operatorname{stel}_{\ell}^{\infty}\) to consist of the data:

\[
\delta : \Delta , \partial v: \bar {\Upsilon} ^ {n} (\sigma \delta) \vdash \bar {\Upsilon} ^ {n} (\sigma \delta) \partial v \text { type } _ {\ell_ {n}}
\]

Similarly, we would like to define infinite partial substitutions as infinite lists of terms sectioning an infinite telescope. This is encapsulated by the judgement  \( \gamma : \Gamma \vdash \bar{\upsilon} \gamma : \bar{\Upsilon} \gamma \) , which is characterised by a similar bidirectional rule:

\[
\begin{array}{l} (\gamma : \Gamma \vdash \bar {v} ^ {\partial n} \gamma : \bar {\Upsilon} ^ {\partial n} \gamma) _ {n \in \mathbb {N}} \quad (\gamma : \Gamma \vdash \bar {v} ^ {n} \gamma : \bar {\Upsilon} ^ {n} \gamma (\bar {v} ^ {\partial n} \gamma)) _ {n \in \mathbb {N}} \\ \bar {v} ^ {\partial 0} \gamma \equiv [ ] \quad (\gamma : \Gamma \vdash \bar {v} ^ {\partial (n + 1)} \gamma \equiv [ \bar {v} ^ {\partial n} \gamma , \bar {v} ^ {n} \gamma ]) _ {n \in \mathbb {N}} \\ \hline \gamma : \Gamma \vdash \bar {v}   \gamma : \bar {\Upsilon}   \gamma \\ \end{array}
\]

Pullback of infinite partial substitutions is defined, as before, to consist of the data:

\[
\delta : \Delta \vdash \bar {v} ^ {n} (\sigma \delta): \bar {\Upsilon} ^ {n} (\sigma \delta) (\bar {v} ^ {\partial n} (\sigma \delta))
\]

49

Categorically, these rules mean we define the map $\mathsf{pr}^{\infty}_{\ell}: \mathsf{PSub}^{\infty}_{\ell} \to \mathsf{Tel}^{\infty}_{\ell}$ to be the limit of the sequence:

$$\cdots \to \mathsf{pr}_{\ell}^{n} \to \cdots \to \mathsf{pr}_{\ell}^{3} \to \mathsf{pr}_{\ell}^{2} \to \mathsf{pr}_{\ell} \to \mathbb{1}$$

where $\mathsf{pr}_{\ell}^{n}$ is the map such that

$$\mathsf{P}_{\mathsf{pr}_{\ell}^{n}} = \sum_{\forall i \leqslant n, \ell_{i} \leqslant \ell} \mathsf{P}_{\mathsf{pr}_{\ell_{0}}} \circ \cdots \circ \mathsf{P}_{\mathsf{pr}_{\ell_{n}}}.$$

In particular, $\mathsf{P}_{\mathbb{1}}$ is the identity functor and $\mathbb{1}$ is the identity map of the terminal object. There is only one natural map $\mathsf{pr}_{\ell}^{n+1} \to \mathsf{pr}_{\ell}^{n}$, which discards the last type in a telescope of length $n+1$; it is not possible to discard any of the other types and get a telescope of length $n$.

### 4.1.9 $\omega$-Limits

Finally, we define the structure of infinite (sequential, Reedy) limits on a CwF. These are an 'infinitary rule' (i.e. a non-elementary structure) that is not part of dTT or any implementable type theory, but we will use them to build our intended models of dTT. Syntactically, they are essentially just a kind of $\Sigma$-type of an infinite telescope.

**Definition 4.8.** A CwF with levels has $\omega$-limits if it is equipped with pullback squares

$$\begin{array}{ccc} \mathsf{PSub}_{\ell}^{\infty} & \xrightarrow{\lim} & \mathsf{Tm}_{\ell} \\ \mathsf{pr}^{\infty}_{\ell} \downarrow & \downarrow & \downarrow \mathsf{pr}_{\ell} \\ \mathsf{Tel}_{\ell}^{\infty} & \xrightarrow{\lim} & \mathsf{Ty}_{\ell}, \end{array}$$

In syntax, this means we have the following structure and properties. Firstly, having a merely commutative square as above gives the following rules:

$$\frac{\gamma : \Gamma \vdash \widetilde{\Upsilon} \gamma \mathsf{stel}_{\ell}^{\infty}}{\gamma : \Gamma \vdash \lim \left( \widetilde{\Upsilon} \gamma \right) \mathsf{type}_{\ell}}$$

$$\frac{\gamma : \Gamma \vdash \widetilde{\upsilon} \gamma : \widetilde{\Upsilon} \gamma}{\gamma : \Gamma \vdash \lim \left( \widetilde{\upsilon} \gamma \right) : \lim \left( \widetilde{\Upsilon} \gamma \right)}$$

Secondly,

$$\frac{\gamma : \Gamma \vdash u : \lim \left( \widetilde{\Upsilon} \gamma \right)}{\gamma : \Gamma \vdash \mathsf{res}^{\partial n} \gamma u : \widetilde{\Upsilon}^{\partial n} \gamma}$$

$$\frac{\gamma : \Gamma \vdash u : \lim \left( \widetilde{\Upsilon} \gamma \right)}{\gamma : \Gamma \vdash \mathsf{res}^{n} \gamma u : \widetilde{\Upsilon}^{n} \gamma \left( \mathsf{res}^{\partial n} \gamma u \right)}$$

We require that $\mathsf{res}^{\partial n}$ is derived from $\mathsf{res}^{n}$ via:

$$\begin{array}{l} \mathsf{res}^{\partial 0} \gamma u \equiv [ ] \\ \mathsf{res}^{\partial (n+1)} \gamma u \equiv [ \mathsf{res}^{\partial n} \gamma u, \mathsf{res}^{n} \gamma u ] \end{array}$$

and that the following computation and uniqueness rules hold:

$$\begin{array}{l} \mathsf{res}^{\partial n} \gamma \left( \lim \left( \widetilde{a} \gamma \right) \right) \equiv \widetilde{a}^{\partial n} \gamma \\ \mathsf{res}^{n} \gamma \left( \lim \left( \widetilde{a} \gamma \right) \right) \equiv \widetilde{a}^{n} \gamma \\ u \equiv \lim \left( \mathsf{res}^{n} \gamma u \right)_{n} \end{array}$$

50

Of course, all these constructions must also be stable under substitution:

$$\left( \lim \left( \widetilde{\Upsilon} \ \gamma \right) \right)^{\sigma} \equiv \lim \left( \widetilde{\Upsilon} \ (\sigma \ \theta) \right)$$

$$\left( \lim \left( \bar{\alpha} \ \gamma \right) \right)^{\sigma} \equiv \lim \left( \bar{\alpha} \ (\sigma \ \theta) \right)$$

$$\left( \operatorname{res}^{\partial n} \ \gamma \ (\alpha \ \gamma) \right)^{\sigma} \equiv \operatorname{res}^{\partial n} \ \theta \ (\alpha \ (\sigma \ \theta) \right)$$

$$\left( \operatorname{res}^{n} \ \gamma \ (\alpha \ \gamma) \right)^{\sigma} \equiv \operatorname{res}^{n} \ \theta \ (\alpha \ (\sigma \ \theta) \right)$$

◁

## 4.2 THE SIMPLICIAL MODEL

In this section we fix a model of dependent type theory with all of the structure described above, which we call the discrete model (dm). From it, we will construct a derived model called the simplicial model (sm). We will do this, first, by way of constructing the truncated simplicial models (smⁿ) for n ≥ -2.

### 4.2.1 The Augmented Semi-Simplex Category

Let B be the type of binary digits, which are 0, 1 : B. For n ≥ m ≥ -1, let B⁽ⁿ⁾,⁽ᵐ⁾ be the type of length n + 1 binary sequences such that exactly m + 1 of the digits have value 1. When b₁ : B⁽ⁿ⁾,⁽ᵐ⁾ and b₀ : B⁽ᵐ⁾,⁽ᵏ⁾, we have a composition b₁ ∘ b₀ : B⁽ⁿ⁾,⁽ᵏ⁾ obtained by replacing the 1 digits in b₁ with the digits of b₀. For example 1010011 ∘ 0110 = 0010010. The category whose objects are ⟨n⟩ and whose morphisms ⟨m⟩ → ⟨n⟩ are B⁽ⁿ⁾,⁽ᵐ⁾ is the augmented semi-simplex category Δ⁺. Note that each of the representables B⁽ⁿ⁾,⁻ only has finitely many elements. We write ∅ for the length-zero sequence, which is the unique element of B⁽⁻¹⁾,⁽⁻¹⁾.

The identities 1⁽ⁿ⁾ are given by length n + 1 sequences of the digit 1. Further, for any b : B⁽ⁿ⁾,⁽ᵏ⁾, we obtain 0b : B⁽ⁿ⁺¹⁾,⁽ᵏ⁾ and 1b : B⁽ⁿ⁺¹⁾,⁽ᵏ⁺¹⁾ by left appending the indicated digit. The following identities hold:

$$0b_1 \circ b_0 \equiv 0 \ (b_1 \circ b_0)$$

$$1b_1 \circ 1b_0 \equiv 1 \ (b_1 \circ b_0)$$

$$1b_1 \circ 0b_0 \equiv 0 \ (b_1 \circ b_0)$$

Note that by the second rule, along with the fact that 11⁽ⁿ⁾ ≡ 1⁽ⁿ⁺¹⁾, the assignments ⟨n⟩ ↦ ⟨n + 1⟩ and b ↦ 1b define an endofunctor of Δ⁺.

Additionally, for every n ≥ -2, we have the full subcategory Δₙ⁺ of Δ⁺ on those objects ⟨k⟩ with k ≤ n. Thus Δ₋₂⁺ is the empty category, while Δ₋₁⁺ is the terminal category.

### 4.2.2 Truncated Simplicial Objects

The objects of the n-truncated simplicial model smⁿ are C-valued presheaves on Δₙ⁺, denoted:

$$\Gamma \operatorname{ob}_{\operatorname{sm}^n}$$

Thus the underlying category of smⁿ is CΔₙ⁺. For each such presheaf and n ≥ m ≥ -2, we have Γₘ ob_dm, where Γ₋₂ ≡ ()_dm is the distinguished terminal object of C.

51

Further, if we have $b : \mathbb{B}^{(n),\langle m\rangle}$, then $\Gamma^b : \Gamma_n \to \Gamma_m$, and this assignment is contravariantly functorial on the nose. We also sometimes write $\gamma^b$ for $\Gamma^b \gamma$. Morphisms of simplicial objects are natural transformations. The data of $\sigma : \Delta \to \Gamma$ thus consists of a morphism $\sigma_n : \Delta_n \to \Gamma_n$ for each $n$, such that for any $b : \mathbb{B}^{(n),\langle m\rangle}$, we have:

$$\Delta^b \circ \sigma_n \equiv \sigma_m \circ \Gamma^b$$

There are two additional functors of relevance relating the truncated simplicial models at different dimensions: truncation and décalage.

$$\begin{array}{ll} \pi : \mathcal{C}^{\Delta_{n+1}^+} \to \mathcal{C}^{\Delta_n^+} & (-)^D : \mathcal{C}^{\Delta_{n+1}^+} \to \mathcal{C}^{\Delta_n^+} \\ (\pi\Gamma)_{m+1} \equiv \Gamma_{m+1} & (\Gamma^D)_{m+1} \equiv \Gamma_{m+2} \\ (\pi\Gamma)^b \equiv \Gamma^b & (\Gamma^D)^b \equiv \Gamma^{\sharp b} \\ (\pi\sigma)_{m+1} \equiv \sigma_{m+1} & (\sigma^D)_{m+1} \equiv \sigma_{m+2} \end{array}$$

There is a natural transformation between them:

$$\begin{array}{l} \rho : (-)^D \Rightarrow \pi \\ (\rho_\Gamma)_{m+1} \equiv \Gamma^{\wp 1_{(m+1)}} \end{array}$$

Note that $\rho_\Gamma : \Gamma^D \to \pi\Gamma$ is a morphism of presheaves since for $b : \mathbb{B}^{(n+1),\langle m+1\rangle}$, we have:

$$\begin{array}{l} (\pi\Gamma)^b \circ (\rho_\Gamma)_{n+1} \equiv \Gamma^b \circ \Gamma^{\wp 1_{(n+1)}} \equiv \Gamma^{\wp 1_{(n+1)}\circ b} \equiv \Gamma^{\wp(1_{(n+1)}\circ b)} \equiv \Gamma^{\wp b} \\ \equiv \Gamma^{\wp(b\circ 1_{(m+1)})} \equiv \Gamma^{\sharp b\circ \wp 1_{(m+1)}} \equiv \Gamma^{\wp 1_{(m+1)}} \circ \Gamma^{\sharp b} \equiv (\rho_\Gamma)_{m+1} \circ (\Gamma^D)^b \end{array}$$

A similar proof shows that $\rho$ is natural, as its components arise from morphisms in $\Delta_n^+$, and any morphism of presheaves must respect these.

### 4.2.3 Intuition

We will now construct the type-theoretical/fibrant structure of the truncated simplicial model. This will be done concretely through a series of mutually inductive definitions that will require substantially strengthening the inductive hypothesis for the sake of making everything well-typed.

However, before we launch into that, it would be useful to keep in mind where we are headed. At the most basic level, we would like to define the judgement

$$\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{ type}_\ell$$

A simplicial type consists entirely of the data of its discrete $m$-simplex types for $m \leqslant n + 1$, all of which live at the same level $\ell$:

$$\begin{array}{c} \gamma_{-1} : \Gamma_{-1} \vdash_{dm} A_{-1} \gamma_{-1} \text{ type}_\ell \\ \gamma_0 : \Gamma_0, \mathfrak{z}: A_{-1} \gamma_0^\wp \vdash_{dm} A_0 \gamma_0 \mathfrak{z} \text{ type}_\ell \\ \gamma_1 : \Gamma_1, \mathfrak{z}: A_{-1} \gamma_1^{\wp 0}, x_0 : A_0 \gamma_1^{\wp 1} \mathfrak{z}, x_0 : A_0 \gamma_1^{\sharp 0} \mathfrak{z} \vdash_{dm} A_1 \gamma_1 \mathfrak{z} x_0 x_0 \text{ type}_\ell \\ \vdots \end{array}$$

52

Note that $\Gamma_0$ (for example) denotes the 0-component of the presheaf $\Gamma$, which is an object at dm, while $\gamma_0$ is an atomic variable name belonging to this object. As another example, the type annotation on the variable $x_0$ is well-typed because the outer square of the following diagram is a distinguished pullback:

![img-4.jpeg](img-4.jpeg)

We will write the type declarations of $A_n$ generically as:

$$\gamma_{n+1} : \Gamma_{n+1}, \ \partial a : \pi A_{\partial(n+1)} \ \gamma_{n+1} \vdash_{dm} A_{n+1} \ \gamma_{n+1} \ \partial a \text{ type}_{\ell_{n+1}}.$$

Here $\pi A_{\partial(n+1)}$ is a telescope consisting of the 'boundary' of an $(n+1)$-simplex, also known as the Reedy 'matching object' of an augmented semi-simplicial type. For example, we will have:

$$\begin{array}{l} A_{\partial(-1)} \ \gamma_{-1} \equiv () \\ A_{\partial 0} \ \gamma_0 \equiv (\mathfrak{z}_0 : A_{-1} \ \gamma_0^0) \\ A_{\partial 1} \ \gamma_1 \equiv (\mathfrak{z}_0 : A_{-1} \ \gamma_1^{00}, x_0 : A_0 \ \gamma_1^{01} \mathfrak{z}_0, x_0 : A_0 \ \gamma_1^{10} \mathfrak{z}_0). \end{array}$$

Similarly, we would like to define simplicial terms to consist of the data of their discrete m-simplex terms for $m \leqslant n + 1$. The judgement

$$\gamma : \Gamma \vdash_{sm^{n+1}} t \ \gamma : A \ \gamma$$

will be defined to consist of the data:

$$\begin{array}{l} \gamma_{-1} : \Gamma_{-1} \vdash_{dm} t_{-1} \ \gamma_{-1} : A_{-1} \ \gamma_{-1} \\ \gamma_0 : \Gamma_0 \vdash_{dm} t_0 \ \gamma_0 : A_0 \ \gamma_0 \ (t_{-1} \ \gamma_0^0) \\ \gamma_1 : \Gamma_1 \vdash_{dm} t_1 \ \gamma_1 : A_1 \ \gamma_1 \ (t_{-1} \ \gamma_0^{00}) \ (t_0 \ \gamma_1^{01}) \ (t_0 \ \gamma_1^{10}) \\ \vdots \end{array}$$

Similarly to before, we will write this generically as

$$\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} t_{n+1} \ \gamma_{n+1} : A_{n+1} \ \gamma_{n+1} \ (\pi t_{\partial(n+1)} \ \gamma_{n+1})$$

where $\pi t_{\partial(n+1)} \ \gamma_{n+1}$ denotes the action of the lower-dimensional parts of t on the boundary of $\gamma_{n+1}$.

### 4.2.4 Fibrant Structure

As suggested above, the basic structure of the fibrant theory of the models $sm^n$ will be defined by mutual induction. In this section our goal is to define the presheaves of types and terms in $sm^n$, along with the context extension operation (but not yet its universal property). This requires defining several other notions mutually, including a type-theoretic version of Reedy 'matching objects' and a truncated version of display that decreases dimension.

53

4.2.4.1 Declarations and Simple Cases We start by declaring the type of all these structures and operations, and giving those definitions that are direct. First, we will have matching telescopes and matching substitutions:

$$\frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} A \gamma^{-} \text{type}_\ell}{\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} A_{\partial(n+1)} \gamma_{n+1} \text{tel}_\ell} \quad \frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} t \gamma^{-} : A \gamma^{-}}{\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} t_{\partial(n+1)} \gamma_{n+1} : A_{\partial(n+1)} \gamma_{n+1}}$$

The inductive definitions of these telescopes and substitutions will be given in section 4.2.4.2. However, in terms of them, we are able to define the types and terms of $sm^{n+1}$, as pairs of a type or term in $sm^n$ with a discrete type or term over its matching object. We can formulate these definitions type-theoretically as bidirectional rules.

$$\frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} \pi A \gamma^{-} \text{type}_\ell}{\gamma_{n+1} : \Gamma_{n+1}, \partial a : \pi A_{\partial(n+1)} \gamma_{n+1} \vdash_{dm} A_{n+1} \gamma_{n+1} \partial a \text{type}_\ell} \quad \frac{\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell}{\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell}$$

$$\frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} \pi t \gamma^{-} : \pi A \gamma^{-}}{\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} t_{n+1} \gamma_{n+1} : A_{n+1} \gamma_{n+1} (\pi t_{\partial(n+1)} \gamma_{n+1})} \quad \frac{\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma}$$

Extension of contexts by a type $\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell$, and of a substitution by a term $\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma$, are then obtained as follows:

$$\begin{array}{l} (\gamma : \Gamma, a : A \gamma)_{m+1} \equiv (\gamma^{-} : \pi\Gamma, a^{-} : \pi A \gamma^{-})_{m+1} \quad \text{for} \quad m < n \\ (\gamma : \Gamma, a : A \gamma)_{n+1} \equiv (\gamma_{n+1} : \Gamma_{n+1}, \partial a : \pi A_{\partial(n+1)} \gamma_{n+1}, a : A_{n+1} \gamma_{n+1} \partial a) \\ [\sigma, t]_{m+1} \equiv [\pi\sigma, \pi t]_{m+1} \quad \text{for} \quad m < n \\ [\sigma, t]_{n+1} \equiv [\sigma_{n+1}, \pi t_{\partial(n+1)}, t_{n+1}]. \end{array}$$

So far this is just a definition of the family of discrete objects underlying $(\gamma : \Gamma, a : A \gamma)$; we will enhance it to a diagram in (4.15) below.

We will also prove that matching telescopes and substitutions are stable under substitution, such that for $\sigma : \Delta \to \Gamma$ in $\mathcal{C}^{\Delta_{n+1}}$, we have:

$$(A^{\pi\sigma})_{\partial(n+1)} \equiv (A_{\partial(n+1)})^{\sigma_{n+1}} \qquad (t^{\pi\sigma})_{\partial(n+1)} \equiv (t_{\partial(n+1)})^{\sigma_{n+1}}$$

Substitution on types $\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell$ and terms $\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma$ can then be defined as:

$$\begin{array}{l} \pi(A^\sigma) \equiv \pi A^{\pi\sigma} \qquad (A^\sigma)_{n+1} \equiv A_{n+1}^{W_\sigma^{\pi A_{\partial(n+1)}}\sigma_{n+1}} \\ \pi(t^\sigma) \equiv \pi t^{\pi\sigma} \qquad (t^\sigma)_{n+1} \equiv t_{n+1}^{\sigma_{n+1}}. \end{array}$$

Functoriality of substitutions in $sm^{n+1}$ then follows from that of $sm^n$ and $dm$.

In order to define the matching telescopes and substitutions, we will require the definition of display to be part of the mutual induction. As noted above, when working with truncated diagrams, display takes an $(n+1)$-truncated semi-simplicial diagram $A$ to an $n$-truncated one that's dependent on $\pi A$. Since we have no modal locks available yet, we are

54

also forced to take this version of display to be in a totally décalaged context; recall that décalage makes sense for arbitrary (non-fibrant) contexts.

$$\frac {\gamma : \Gamma \vdash_ {\mathrm{sm} ^ {n + 1}} A \gamma \text {type} _ {\ell}}{\gamma^ {+} : \Gamma^ {D} , a : \pi A ^ {\rho_ {\Gamma}} \gamma^ {+} \vdash_ {\mathrm{sm} ^ {n}} A ^ {d} \gamma^ {+} a \text {type} _ {\ell}} \quad \frac {\gamma : \Gamma \vdash_ {\mathrm{sm} ^ {n + 1}} t \gamma : A \gamma}{\gamma^ {+} : \Gamma^ {D} \vdash_ {\mathrm{sm} ^ {n}} t ^ {d} \gamma^ {+} : A ^ {d} \gamma^ {+} \pi t ^ {\rho_ {\Gamma}}}$$

We will prove that display is stable under substitution by $\sigma : \Delta \to \Gamma$ in $\mathcal{C}^{\Delta_{n+1}^+}$, and satisfies the expected formulas relating it to décalage:

$$(A ^ {\sigma}) ^ {d} \equiv (A ^ {d}) ^ {W _ {2} ^ {\pi A ^ {\rho_ {\Gamma}}} \sigma^ {D}}$$

$$(t ^ {\sigma}) ^ {d} \equiv (t ^ {d}) ^ {\sigma^ {D}}$$

$$(\gamma : \Gamma , a : A \gamma) ^ {D} \equiv (\gamma^ {+} : \Gamma^ {D}, a : \pi A ^ {\rho_ {\Gamma}} \gamma^ {+}, a ^ {\prime} : A ^ {d} \gamma^ {+} a) \tag {4.9}$$

$$[ \sigma , t ] ^ {D} \equiv [ \sigma^ {D}, \pi t ^ {\rho_ {\Delta}}, t ^ {d} ]. \tag {4.10}$$

Finally, we will also define substitutions that give an the actions of morphisms in $\Delta_{n+1}^+$ on matching telescopes and on types:

$$\frac {\gamma^ {-} : \pi \Gamma \vdash_ {\mathrm{sm} ^ {n}} A \gamma^ {-} \text {type} _ {\ell} \quad b : \mathbb {B} ^ {(n + 1) , (m + 1)}}{\gamma_ {n + 1} : \Gamma_ {n + 1} , \partial a : A _ {\partial (n + 1)} \gamma_ {n + 1} \vdash_ {d m} \operatorname{act} _ {\partial b} ^ {A} \gamma_ {n + 1} \partial a : \pi^ {n - m} A _ {\partial (m + 1)} (\Gamma^ {b} \gamma_ {n + 1})}$$

$$\frac {\gamma : \Gamma \vdash_ {\mathrm{sm} ^ {n + 1}} A \gamma \text {type} _ {\ell} \quad b : \mathbb {B} ^ {(n + 1) , (m + 1)}}{\gamma_ {n + 1} : \Gamma_ {n + 1} , \partial a : \pi A _ {\partial (n + 1)} \gamma_ {n + 1} , a : A _ {n + 1} \gamma_ {n + 1} \partial a}$$

$$\vdash_ {d m} \operatorname{act} _ {b} ^ {A} \gamma_ {n + 1} \partial a a : \pi^ {n - m} A _ {m + 1} (\Gamma^ {b} \gamma_ {n + 1}) (\operatorname{act} _ {\partial b} \gamma_ {n + 1} \partial a)$$

We will show that these compute to the identities (i.e. weakening) when $b = 1_{(n+1)}$, are functorial such that for $b_1 : \mathbb{B}^{(n+1), (m+1)}$ and $b_0 : \mathbb{B}^{(m+1), (k+1)}$:

$$\operatorname{act} _ {\partial b _ {0}} ^ {\pi^ {n - m} A} \left(\Gamma^ {b _ {1}} \gamma_ {n + 1}\right) \left(\operatorname{act} _ {\partial b _ {1}} ^ {A} \gamma_ {n + 1} \partial a\right) \equiv \operatorname{act} _ {\partial (b _ {1} \circ b _ {0})} ^ {A} \gamma_ {n + 1} \partial a \tag {4.11}$$

$$\operatorname{act} _ {b _ {0}} ^ {\pi^ {n - m} A} \left(\Gamma^ {b _ {1}} \gamma_ {n + 1}\right) \left(\operatorname{act} _ {\partial b _ {1}} ^ {\pi A} \gamma_ {n + 1} \partial a\right) \left(\operatorname{act} _ {b _ {1}} ^ {A} \gamma_ {n + 1} \partial a a\right) \equiv \operatorname{act} _ {b _ {1} \circ b _ {0}} ^ {A} \gamma_ {n + 1} \partial a a \tag {4.12}$$

and are also stable under substitution in the sense that for $\sigma : \Delta \to \Gamma$ in $\mathcal{C}^{\Delta_{n+1}^+}$:

$$\operatorname{act} _ {\partial b} ^ {A ^ {\pi \sigma}} \equiv \left(\operatorname{act} _ {\partial b} ^ {A}\right) ^ {W _ {2} ^ {A _ {\partial (n + 1)} \sigma_ {n + 1}}} \tag {4.13}$$

$$\operatorname{act} _ {b} ^ {A ^ {\sigma}} \equiv \left(\operatorname{act} _ {b} ^ {A}\right) ^ {W _ {2} ^ {A _ {n + 1}} W _ {2} ^ {\pi A _ {\partial (n + 1)} \sigma_ {n + 1}}}. \tag {4.14}$$

Given these, we can then define the functorial structure of the putative object $(\gamma : \Gamma, a : A \gamma)$: a morphism $b_1 : \mathbb{B}^{(n+1), (m+1)}$ acts on it by:

$$(\gamma : \Gamma , a : A \gamma) ^ {b} \gamma_ {n + 1} \partial a a \equiv [ \Gamma^ {b} \gamma_ {n + 1}, \operatorname{act} _ {\partial b} ^ {\pi A} \gamma_ {n + 1} \partial a, \operatorname{act} _ {b} ^ {A} \gamma_ {n + 1} \partial a a ] \tag {4.15}$$

Equations (4.11) and (4.12) tell us that the assignment $(\gamma : \Gamma, a : A \gamma)^b$ is functorial, while eqs. (4.13) and (4.14) tell us that the extension $[\sigma, t]$ is a morphism of presheaves.

The above is the complete list of constructions and theorems that we need in order to inductively define the type and term presheaves in the models $\mathbf{sm}^n$ and their context extension function.

55

4.2.4.2 The Inductive Cases Now we give the inductive definitions and proofs of the objects and theorems declared previously. The model \(\mathfrak{sm}^{-2}\) is the terminal CwF on the terminal category. For \(\mathfrak{sm}^{-1}\), we have that:

\[
A _ {\partial (- 1)} \equiv () _ {d m} \quad t _ {\partial (- 1)} \equiv [ ] _ {d m}
\]

from which the rest of the definitions and theorems evidently follow.

Suppose now that the model \(\mathfrak{sm}^{n + 1}\) has been defined with all of the above structure and properties. We first define matching telescopes and substitutions as follows:

\[
A _ {\partial (n + 2)} \gamma_ {n + 2} \equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \gamma_ {n + 2}, a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} \gamma_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} [ \gamma_ {n + 2}, \partial a, a ]\right)
\]

\[
\mathsf {t} _ {\partial (n + 2)} \gamma_ {n + 2} \equiv [ (\pi \mathsf {t} ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)}, (\mathsf {t} ^ {\rho_ {\Gamma}}) _ {n + 1}, (\mathsf {t} ^ {d}) _ {\partial (n + 1)} ].
\]

The stability of these under substitution follows from that of the constituent constructions in the previous dimension; for \(\sigma : \Delta \to \Gamma\) in \(\mathcal{C}^{\Delta_{n+2}^{\tau}}\):

\[
\left(A ^ {\pi \sigma}\right) _ {\partial (n + 2)} \delta_ {n + 2}
\]

\[
\equiv \left(\partial a: (\pi A ^ {\pi \pi \sigma \circ \rho_ {\pi \Delta}}) _ {\partial (n + 1)} \delta_ {n + 2}, a: (A ^ {\pi \sigma \circ \rho_ {\Delta}}) _ {n + 1} \delta_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(\left(A ^ {\pi \sigma}\right) ^ {d}\right) _ {\partial (n + 1)} [ \delta_ {n + 2}, \partial a, a ]\right)
\]

\[
\equiv \left(\partial a: \left(\pi A ^ {\rho_ {\pi \Gamma} \circ \pi \sigma^ {0}}\right) _ {\partial (n + 1)} \delta_ {n + 2}, a: \left(A ^ {\rho_ {\Gamma} \circ \sigma^ {0}}\right) _ {n + 1} \delta_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(\left(A ^ {d}\right) ^ {\pi W _ {2} ^ {A ^ {\rho_ {\Gamma}}} \sigma^ {0}}\right) _ {\partial (n + 1)} [ \delta_ {n + 2}, \partial a, a ]\right)
\]

\[
\equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \left(\sigma_ {n + 1} ^ {D} \delta_ {n + 2}\right), a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} \left(\sigma_ {n + 1} ^ {D} \delta_ {n + 2}\right) \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} \left[ \left(\sigma_ {n + 1} ^ {D} \delta_ {n + 2}\right), \partial a, a \right]\right)
\]

\[
\equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} (\sigma_ {n + 2} \delta_ {n + 2}), a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} (\sigma_ {n + 2} \delta_ {n + 2}) \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} \left[ \left(\sigma_ {n + 2} \delta_ {n + 2}\right), \partial a, a \right]\right)
\]

\[
\equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \gamma_ {n + 2}, a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} \gamma_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} \left[ \gamma_ {n + 2}, \partial a, a \right]\right) ^ {\sigma_ {n + 2}}
\]

\[
\equiv A _ {\partial (n + 2)} \left(\sigma_ {n + 2} \delta_ {n + 2}\right).
\]

For display, we define:

\[
\pi (A ^ {d}) \equiv \pi A ^ {d} \quad (A ^ {d}) _ {n + 1} \equiv A _ {n + 2}
\]

\[
\pi (t ^ {d}) \equiv \pi t ^ {d} \qquad \qquad (t ^ {d}) _ {n + 1} \equiv t _ {n + 2}.
\]

This definition is well typed because the expected typing judgement for  \( (A^{d})_{n+1} \)  is:

\[
\gamma_ {n + 2}: \Gamma_ {n + 2}, \partial a: (\pi \pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \gamma_ {n + 2}, a: (\pi A ^ {\rho_ {\Gamma}}) _ {n + 1} \gamma_ {n + 2} \partial a,
\]

\[
\partial a ^ {\prime}: \left(\pi A ^ {d}\right) _ {\partial (n + 1)} \gamma_ {n + 2} \partial a a \vdash_ {d m} \left(A ^ {d}\right) _ {n + 1} [ \gamma_ {n + 2}, \partial a, a ] \partial a ^ {\prime} \text {type} _ {\mathrm{f}}
\]

56

and the context in which $A_{n+2}$ lives expands to this by the definition of matching telescopes:

$$\gamma_{n+2} : \Gamma_{n+2}, \ \partial a : \pi A_{\partial(n+2)} \ \gamma_{n+2} \vdash_{dm} A_{n+2} \ \gamma_{n+2} \ \partial a \ \text{type}_\ell.$$

We can now check (4.9) at the level of $n + 1$ simplices:

$$\begin{aligned} & \left( (\gamma : \Gamma, \ a : A \ \gamma)^D \right)_{n+1} \\ & \quad \equiv (\gamma : \Gamma, \ a : A \ \gamma)_{n+2} \\ & \quad \equiv (\gamma_{n+2} : \Gamma_{n+2}, \ \partial a : \pi A_{\partial(n+2)} \ \gamma_{n+2}, \ a : A_{n+2} \ \gamma_{n+2} \ \partial a) \\ & \quad \equiv (\gamma_{n+2} : \Gamma_{n+2}, \ \partial a : (\pi \pi A^{p_{\pi\Gamma}})_{\partial(n+1)} \ \gamma_{n+2}, \ a : (\pi A^{p_\Gamma})_{n+1} \ \gamma_{n+2} \ \partial a, \\ & \qquad \qquad \partial a' : (\pi A^d)_{\partial(n+1)} \ [ \gamma_{n+2}, \ \partial a, \ a \ ], \ a' : (A^d)_{n+1} \ [ \gamma_{n+2}, \ \partial a, \ a \ ] \ \partial a') \\ & \quad \equiv (\gamma^+ : \Gamma^D, \ a : \pi A^{p_\Gamma} \ \gamma^+, \ a' : A^d \ \gamma^+ \ a)_{n+1}, \end{aligned}$$

where (4.10) follows similarly. Stability under substitutions follows inductively:

$$\begin{aligned} \pi \Big( (A^\sigma)^d \Big)_{n+1} & \equiv (\pi A^{\pi\sigma})^d \\ & \equiv (\pi A^d)^{W_2^{\pi A^p \pi \Gamma} \pi \sigma^D} \\ & \equiv (\pi A^d)^{\pi W_2^{\pi A^p \Gamma} \sigma^D} \\ & \equiv \pi \Big( (A^d)^{W_2^{\pi A^p \Gamma} \sigma^D} \Big) \\ \Big( (A^\sigma)^d \Big)_{n+1} & \equiv (A^\sigma)_{n+2} \\ & \equiv A_{n+2}^{W_2^{\pi A_{\partial(n+2)}} \sigma_{n+2}} \\ & \equiv A_{n+2}^{W_2^{(\pi A^d)_{\partial(n+1)}} W_2^{(\pi A^p \Gamma)_{n+1}} W_2^{(\pi \pi A^p \pi \Gamma)_{\partial(n+1)}} \sigma_{n+2}} \\ & \equiv \Big( (A^d)_{n+1} \Big)^{W_2^{(\pi A^d)_{\partial(n+1)}} \left( W_2^{\pi A^p \Gamma} \sigma^D \right)_{n+1}} \\ & \equiv \Big( (A^d)^{W_2^{\pi A^p \Gamma} \sigma^D} \Big)_{n+1}. \end{aligned}$$

Lastly, we define the components of the functorial action on presheaves as follows:

$$\text{act}_{\partial(\mathbb{0}b)}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \equiv \text{act}_{\partial b}^{\pi A^{p_{\pi\Gamma}}} \ \gamma_{n+2} \ \partial a$$

$$\text{act}_{\mathbb{0}b}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \ a' \equiv \text{act}_b^{\pi A^{p_\Gamma}} \ \gamma_{n+2} \ \partial a \ a$$

$$\text{act}_{\partial(\mathbb{1}b)}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \equiv$$

$$[ \text{act}_{\partial b}^{\pi A^{p_{\pi\Gamma}}} \ \gamma_{n+2} \ \partial a, \ \text{act}_b^{A^{p_\Gamma}} \ \gamma_{n+2} \ \partial a \ a, \ \text{act}_{\partial b}^{A^d} \ [ \gamma_{n+2}, \ \partial a, \ a \ ] \ \partial a' ]$$

$$\text{act}_{\mathbb{1}b}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \ a' \equiv \text{act}_b^{A^d} \ [ \gamma_{n+2}, \ \partial a, \ a \ ] \ \partial a' \ a',$$

57

where the last definition is well typed because $\left(A^{d}\right)_{n+1} \equiv A_{n+2}$. We check functoriality:

$$\begin{array}{l} \operatorname{act}_{\partial b_{0}}^{\pi^{(n+1)-m}A}\left(\Gamma^{\otimes b_{1}} \gamma_{n+2}\right)\left(\operatorname{act}_{\partial\left(\emptyset b_{1}\right)}^{A} \gamma_{n+2}\left[\partial a, a, \partial a^{\prime}\right]\right) \\ \quad \equiv \operatorname{act}_{\partial b_{0}}^{\pi^{n-m} \pi A}\left(\left(\rho_{\Gamma}\right)_{m+1}\left(\left(\Gamma^{D}\right)^{b_{1}} \gamma_{n+2}\right)\right)\left(\operatorname{act}_{\partial\left(\emptyset b_{1}\right)}^{A} \gamma_{n+2} \partial a\right) \\ \quad \equiv \operatorname{act}_{\partial b_{0}}^{\pi^{n-m} \pi A^{\rho_{\pi \Gamma}}}\left(\left(\Gamma^{D}\right)^{b_{1}} \gamma_{n+2}\right)\left(\operatorname{act}_{\partial b_{1}}^{\pi A^{\rho_{\pi \Gamma}}} \gamma_{n+2} \partial a\right) \\ \quad \equiv \operatorname{act}_{\partial\left(b_{1} \circ b_{0}\right)}^{\pi A^{\rho_{\pi \Gamma}}} \gamma_{n+2} \partial a \\ \quad \equiv \operatorname{act}_{\partial\left(\emptyset b_{1} \circ b_{0}\right)}^{A} \gamma_{n+2}\left[\partial a, a, \partial a^{\prime}\right] \end{array}$$

and stability under substitutions:

$$\begin{array}{l} \operatorname{act}_{\partial\left(\emptyset b\right)}^{A^{\pi \sigma}} \delta_{n+2}\left[\partial a, a, \partial a^{\prime}\right] \equiv \operatorname{act}_{\partial b}^{\pi A^{\pi \pi \sigma \circ \rho_{\pi A}}} \delta_{n+2} \partial a \\ \quad \equiv \operatorname{act}_{\partial b}^{\pi A^{\rho_{\pi \Gamma} \circ \pi \sigma^{D}}} \delta_{n+2} \partial a \\ \quad \equiv \operatorname{act}_{\partial b}^{\pi A^{\rho_{\pi \Gamma}}}\left(\sigma_{n+1}^{D} \delta_{n+2}\right) \partial a \\ \quad \equiv \operatorname{act}_{\partial\left(\emptyset b\right)}^{A}\left(\sigma_{n+2} \delta_{n+2}\right)\left[\partial a, a, \partial a^{\prime}\right]. \end{array}$$

All omitted verifications are similar to the cases presented. This completes the construction of the type and term presheaves and their context extension function, plus display, for the truncated simplicial models $\mathbf{sm}^{n}$.

### 4.2.5 Variables

To make the models $\mathbf{sm}^{n}$ into CwFs, what is missing from the above construction are the fundamental context projections and variables. In this section we will now define these:

$$\frac{\gamma : \Gamma \vdash_{\mathbf{sm}^{n}} A \gamma \operatorname{type}_{\ell}}{\operatorname{pt}_{\mathbf{sm}^{n}}^{A} : (\gamma : \Gamma, a : A \gamma) \rightarrow \Gamma} \quad \frac{\gamma : \Gamma \vdash_{\mathbf{sm}^{n}} A \gamma \operatorname{type}_{\ell}}{\gamma : \Gamma, a : A \gamma \vdash_{\mathbf{sm}^{n}} z v_{\mathbf{sm}^{n}}^{A} \gamma a : A^{\operatorname{pt}} \gamma a}.$$

We now construct variables and parent maps in $\mathbf{sm}^{n}$ inductively, with all of the hypothesise eqs. (4.2) to (4.4) outlined before assumed at all prior levels. This construction will be performed such that the following theorems hold inductively:

$$\left(\operatorname{pt}_{\mathbf{sm}^{n+1}}^{A}\right)^{D} \equiv \operatorname{pt}_{\mathbf{sm}^{n}}^{\pi A^{\rho_{\Gamma}}} \circ \operatorname{pt}_{\mathbf{sm}^{n}}^{A^{d}} \tag{4.16}$$

$$\left(z v_{\mathbf{sm}^{n+1}}^{A}\right)^{d} \equiv z v_{\mathbf{sm}^{n}}^{A^{d}} \tag{4.17}$$

$$\left(z v_{\mathbf{sm}^{n}}^{\pi A}\right)^{\rho_{\left(\Gamma, A\right)}} \equiv \left(z v_{\mathbf{sm}^{n}}^{\pi A^{\rho_{\Gamma}}}\right)^{\operatorname{pt}_{\mathbf{sm}^{n}}^{A^{d}}}. \tag{4.18}$$

Note that the above equations are well typed by way of the formulas for décalage given in the fibrant construction above. Now for $\mathbf{sm}^{-1}$, we define:

$$\left(\operatorname{pt}_{\mathbf{sm}^{-1}}^{A}\right)_{-1} \equiv \operatorname{pt}_{\mathbf{dm}}^{A-1}$$

$$\left(z v_{\mathbf{sm}^{-1}}^{A}\right)_{-1} \equiv z v_{\mathbf{dm}}^{A-1}.$$

58

Then we inductively define:

$$\left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+1}}^{\mathrm{A}} \right)_{\mathrm{m}+1} \equiv \left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n}}^{\pi \mathrm{A}} \right)_{\mathrm{m}+1} \quad \text { for } \quad \mathrm{m}<\mathrm{n}$$

$$\left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+2}}^{\mathrm{A}} \right)_{\mathrm{n}+2} \equiv \left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+1}}^{\pi \mathrm{A}^{\mathrm{p} \mathrm{r}}} \right)_{\mathrm{n}+1} \circ \left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+1}}^{\mathrm{A}^{\mathrm{d}}} \right)_{\mathrm{n}+1}$$

$$\pi\left( \mathrm{zv}_{\mathrm{sm}^{n+2}}^{\mathrm{A}} \right) \equiv \mathrm{zv}_{\mathrm{sm}^{n}}^{\pi \mathrm{A}}$$

$$\left( \mathrm{zv}_{\mathrm{sm}^{n+2}}^{\mathrm{A}} \right)_{\mathrm{n}+2} \equiv \left( \mathrm{zv}_{\mathrm{sm}^{n+1}}^{\mathrm{A}^{\mathrm{d}}} \right)_{\mathrm{n}+1} .$$

This says that the constructions are performed level-wise. From this, theorems eqs. (4.16) and (4.17) then follow inductively, since the hypothesised décalage and display formulas were used to define each successive level.

Are these definitions correct? We gave well typed definitions, but to show that they give a notion of parent maps and zero variables, we have to verify that equations eqs. (4.2) to (4.4) hold. These verification appear in appendix A.1.

### 4.2.6 $\Pi$-Types

We construct $\Pi$-types inductively, with all of the assumptions of a $\Pi$-type structure outlined before assumed at all prior levels. Now note that we have the following two types in the same context:

$$\gamma^{+}: \Gamma^{\mathrm{D}}, f: \left( \Pi^{\mathrm{sm}^{n}} \pi \mathrm{A} \pi \mathrm{B} \right)^{\mathrm{p} \mathrm{r}} \gamma^{+} \vdash_{\mathrm{sm}^{n}} \left( \Pi^{\mathrm{sm}^{n+1}} \mathrm{A} \mathrm{B} \right)^{\mathrm{d}} \gamma^{+} \mathrm{f} \text { type }_{\ell}$$

$$\gamma^{+}: \Gamma^{\mathrm{D}}, f: \left( \Pi^{\mathrm{sm}^{n}} \pi \mathrm{A} \pi \mathrm{B} \right)^{\mathrm{p} \mathrm{r}} \gamma^{+} \vdash_{\mathrm{sm}^{n}}$$

$$\left( a: \pi \mathrm{A}^{\mathrm{p} \mathrm{r}} \gamma^{+} \right)\left( a^{\prime}: \mathrm{A}^{\mathrm{d}} \gamma^{+} a \right) \rightarrow \mathrm{B}^{\mathrm{d}}\left[\gamma^{+}, a, a^{\prime}\right]\left( \operatorname{app}\left[\gamma^{+}, f, a, a^{\prime}\right] f a \right) \text { type }_{\ell} .$$

We will prove inductively along with our definition that these two types are equal. In point-free notation, this means we will have:

$$\left( \Pi^{\mathrm{sm}^{n+1}} \mathrm{A} \mathrm{B} \right)^{\mathrm{d}} \equiv \Pi^{\mathrm{sm}^{n}}\left( \pi \mathrm{A}^{\mathrm{p} \mathrm{r}} \right)^{\mathrm{p} \mathrm{t}} \Pi^{\mathrm{sm}^{n}}\left(\mathrm{A}^{\mathrm{d}}\right)^{\mathrm{W}_{2}^{\pi \mathrm{A}^{\mathrm{p} \mathrm{r}}} \mathrm{p} \mathrm{t}}\left(\mathrm{B}^{\mathrm{d}}\right)^{\left[\mathrm{W}_{2}^{\mathrm{A}^{\mathrm{d}}} \mathrm{W}_{2}^{\pi \mathrm{A}^{\mathrm{p} \mathrm{r}}} \mathrm{p} \mathrm{t}, \operatorname{app} \mathrm{zv}^{\mathrm{p} \mathrm{t} \mathrm{p} \mathrm{t}} \mathrm{zv}^{\mathrm{p} \mathrm{t}}\right]}$$

$$\left( \lambda^{\mathrm{sm}^{n+1}} \mathrm{t} \right)^{\mathrm{d}} \equiv \lambda^{\mathrm{sm}^{n}}\left( \lambda^{\mathrm{sm}^{n}} \mathrm{t}^{\mathrm{d}} \right)$$

$$\left( \operatorname{app}^{\mathrm{sm}^{n+1}} \mathrm{f} \mathrm{s} \right)^{\mathrm{d}} \equiv \operatorname{app}^{\mathrm{sm}^{n}}\left( \operatorname{app}^{\mathrm{sm}^{n}} \mathrm{f}^{\mathrm{d}} \pi \mathrm{s}^{\mathrm{p} \mathrm{r}} \right) \mathrm{s}^{\mathrm{d}} .$$

Now to start on the induction, for $\mathrm{sm}^{-1}$ we define:

$$\left( \Pi^{\mathrm{sm}^{-1}} \mathrm{A} \mathrm{B} \right)_{-1} \equiv \Pi^{\mathrm{dm}} \mathrm{A}_{-1} \mathrm{B}_{-1}$$

$$\left( \lambda^{\mathrm{sm}^{-1}} \mathrm{t} \right)_{-1} \equiv \lambda^{\mathrm{dm}} \mathrm{t}_{-1}$$

$$\left( \operatorname{app}^{\mathrm{sm}^{-1}} \mathrm{f} \mathrm{s} \right)_{-1} \equiv \operatorname{app}^{\mathrm{dm}} \mathrm{f}_{-1} \mathrm{s}_{-1} .$$

59

Then we inductively define:

$$\pi(\Pi^{\text{sm}^{n+2}} \text{ A B}) \equiv \Pi^{\text{sm}^{n+1}} \pi \text{A} \pi \text{B}$$

$$(\Pi^{\text{sm}^{n+2}} \text{ A B})_{n+2} \equiv \left( \Pi^{\text{sm}^{n+1}} (\pi \text{A}^{\rho_{\Gamma}})^{\text{pt}} \Pi^{\text{sm}^{n+1}} (\text{A}^{\text{d}})^{\text{W}_2^{\pi \text{A}^{\rho_{\Gamma}} \text{pt}}} (\text{B}^{\text{d}})^{\left| \text{W}_2^{\text{A}^{\text{d}} \text{W}_2^{\pi \text{A}^{\rho_{\Gamma}} \text{pt}}, \text{app} \text{zv}^{\text{pt} \circ \text{pt}} \text{zv}^{\text{pt}} \right|} \right)_{n+1}$$

$$\pi(\lambda^{\text{sm}^{n+2}} \text{ t}) \equiv \lambda^{\text{sm}^{n+1}} \pi \text{t}$$

$$(\lambda^{\text{sm}^{n+2}} \text{ t})_{n+2} \equiv \left( \lambda^{\text{sm}^{n+1}} \left( \lambda^{\text{sm}^{n+1}} \text{ t}^{\text{d}} \right) \right)_{n+1}$$

$$\pi(\text{app}^{\text{sm}^{n+2}} \text{ f s}) \equiv \text{app}^{\text{sm}^{n+1}} \pi \text{f} \pi \text{s}$$

$$(\text{app}^{\text{sm}^{n+2}} \text{ f s})_{n+2} \equiv \left( \text{app}^{\text{sm}^{n+1}} \left( \text{app}^{\text{sm}^{n+1}} \text{ f}^{\text{d}} \pi \text{s}^{\rho_{\Gamma}} \right) \text{ s}^{\text{d}} \right)_{n+1}.$$

As before, this says that the constructions are performed level-wise. From this, theorems eqs. (4.19) to (4.21) then follow inductively, since the hypothesised display formulas were used to define each successive level. The correctness of these definitions will follow from verifying the $\beta$ and $\eta$ laws in appendix A.2.

### 4.2.7 Universes

The universes of the discrete model are denoted $\text{Disc}_{\ell}$. We construct universes in $\text{sm}^n$ inductively, with all of the assumptions of a $\mathcal{U}$-type structure outlined before assumed at all prior levels. We will inductively have that:

$$(\text{Type}_{\ell}^{\text{sm}^{n+1}})^{\text{d}} \equiv \Pi^{\text{sm}^n} (\text{EI zv}) \text{ Type}_{\ell}^{\text{sm}^n} \tag{4.22}$$

$$(\text{Code}^{\text{sm}^{n+1}} \text{ A})^{\text{d}} \equiv \lambda^{\text{sm}^n} (\text{Code}^{\text{sm}^n} \text{ A}^{\text{d}}) \tag{4.23}$$

$$(\text{EI}^{\text{sm}^{n+1}} \text{ A})^{\text{d}} \equiv \text{EI}^{\text{sm}^n} (\text{app}^{\text{sm}^n} (\text{A}^{\text{d}})^{\text{pt}} \text{ zv}). \tag{4.24}$$

For $\text{sm}^{-1}$, we define:

$$(\text{Type}_{\ell}^{\text{sm}^{-1}})_{-1} \equiv \text{Disc}_{\ell}$$

$$(\text{Code}^{\text{sm}^{-1}} \text{ A})_{-1} \equiv \text{Code}^{\text{dm}} \text{ A}_{-1}$$

$$(\text{EI}^{\text{sm}^{-1}} \text{ A})_{-1} \equiv \text{EI}^{\text{dm}} \text{ A}_{-1}.$$

Then we inductively define:

$$\pi(\text{Type}_{\ell}^{\text{sm}^{n+2}}) \equiv \text{Type}_{\ell}^{\text{sm}^{n+1}}$$

$$(\text{Type}_{\ell}^{\text{sm}^{n+2}})_{n+2} \equiv \left( \Pi^{\text{sm}^{n+1}} (\text{EI zv}) \text{ Type}_{\ell}^{\text{sm}^{n+1}} \right)_{n+1}$$

$$\pi(\text{Code}^{\text{sm}^{n+2}} \text{ A}) \equiv \text{Code}^{\text{sm}^{n+1}} \pi \text{A}$$

$$(\text{Code}^{\text{sm}^{n+2}} \text{ A})_{n+2} \equiv \left( \lambda^{\text{sm}^{n+1}} (\text{Code}^{\text{sm}^{n+1}} \text{ A}^{\text{d}}) \right)_{n+1}$$

$$\pi(\text{EI}^{\text{sm}^{n+2}} \text{ A}) \equiv \text{EI}^{\text{sm}^{n+1}} \pi \text{A}$$

$$(\text{EI}^{\text{sm}^{n+2}} \text{ A})_{n+2} \equiv \left( \text{EI}^{\text{sm}^{n+1}} (\text{app}^{\text{sm}^{n+1}} (\text{A}^{\text{d}})^{\text{pt}} \text{ zv}) \right)_{n+1}.$$

Again, this says that the constructions are performed level-wise. From this, theorems eqs. (4.22) to (4.24) then follow inductively, since the hypothesised display formulas were

60

used to define each successive level. The correctness of these definitions will follow from verifying that Code and El are mutual inverses in appendix A.3.

### 4.2.8 ω-Limits

If ω-limits are defined in smⁿ, then given an infinite telescope γ : Γ ⊢ₛₘⁿ⁺¹ Ϡ γ stelℓ∞ or infinite partial substitution γ : Γ ⊢ₛₘⁿ⁺¹ ϋ γ : Ϡ γ in smⁿ, we can meaningfully give a type declaration of its display through use of limits:

$$\frac{\gamma : \Gamma \vdash_{\text{sm}^{n+1}} \bar{\Upsilon} \gamma \text{stel}_{\ell}^{\infty}}{\gamma^{+} : \Gamma^{\text{D}}, u : \lim_{\text{sm}^{n}} \pi \bar{\Upsilon}^{\text{pr}} \gamma^{+} \vdash_{\text{sm}^{n}} \bar{\Upsilon}^{\text{d}} \gamma^{+} u \text{stel}_{\ell}^{\infty}}$$

$$\frac{\gamma : \Gamma \vdash_{\text{sm}^{n+1}} \bar{\upsilon} \gamma : \bar{\Upsilon} \gamma \text{stel}_{\ell}^{\infty}}{\gamma^{+} : \Gamma^{\text{D}} \vdash_{\text{sm}^{n}} \bar{\upsilon}^{\text{d}} \gamma^{+} : \bar{\Upsilon}^{\text{d}} \gamma^{+} \left( \lim_{\text{sm}^{n}} \pi \bar{\upsilon}^{\text{pr}} \right)}$$

We then define these by:

$$\begin{array}{l} \left(\bar{\Upsilon}^{\text{d}} \gamma^{+} u\right)^{\partial m} \equiv \left(\bar{\Upsilon}^{\partial m}\right)^{\text{d}} \gamma^{+} \left(\text{res}_{\text{sm}^{n}}^{\partial m} \gamma^{+} u\right) \\ \left(\bar{\Upsilon}^{\text{d}} \gamma^{+} u\right)^{m} \equiv \left(\bar{\Upsilon}^{m}\right)^{\text{d}} \gamma^{+} \left(\text{res}_{\text{sm}^{n}}^{m} \gamma^{+} u\right) \\ \left(\bar{\upsilon}^{\text{d}}\right)^{\partial m} \equiv \left(\bar{\upsilon}^{\partial m}\right)^{\text{d}} \\ \left(\bar{\upsilon}^{\text{d}}\right)^{m} \equiv \left(\bar{\upsilon}^{m}\right)^{\text{d}}. \end{array}$$

The third declaration, for example, is well typed because its expected type is:

$$\begin{array}{l} \left(\bar{\Upsilon}^{\text{d}} \gamma^{+} \left(\lim_{\text{sm}^{n}} \pi \bar{\upsilon}^{\text{pr}}\right)\right)^{\partial m} \\ \equiv \left(\bar{\Upsilon}^{\partial m}\right)^{\text{d}} \gamma^{+} \left(\text{res}_{\text{sm}^{n}}^{\partial m} \gamma^{+} \left(\lim_{\text{sm}^{n}} \pi \bar{\upsilon}^{\text{pr}}\right)\right) \\ \equiv \left(\bar{\Upsilon}^{\partial m}\right)^{\text{d}} \gamma^{+} \left(\pi \left(\bar{\upsilon}^{\partial m}\right)^{\text{pr}}\right). \end{array}$$

We now construct ω-limits in smⁿ inductively, with all of the assumptions of a ω-structure outlined before assumed at all prior levels. This construction will be performed such that the following theorems hold inductively:

$$\begin{array}{l} \left(\lim_{\text{sm}^{n+1}} \bar{\Upsilon}\right)^{\text{d}} \equiv \lim_{\text{sm}^{n}} \bar{\Upsilon}^{\text{d}} \quad (4.25) \\ \left(\lim_{\text{sm}^{n+1}} \bar{\upsilon}\right)^{\text{d}} \equiv \lim_{\text{sm}^{n}} \bar{\upsilon}^{\text{d}} \quad (4.26) \\ \left(\text{res}_{\text{sm}^{n+1}}^{\partial m} u\right)^{\text{d}} \equiv \text{res}_{\text{sm}^{n}}^{\partial m} u^{\text{d}} \quad (4.27) \\ \left(\text{res}_{\text{sm}^{n+1}}^{m} u\right)^{\text{d}} \equiv \text{res}_{\text{sm}^{n}}^{m} u^{\text{d}}. \quad (4.28) \end{array}$$

For sm⁻¹, we define:

$$\begin{array}{l} \left(\lim_{\text{sm}^{-1}} \bar{\Upsilon}\right)_{-1} \equiv \lim_{\text{dm}} \bar{\Upsilon}_{-1} \\ \left(\lim_{\text{sm}^{-1}} \bar{\upsilon}\right)_{-1} \equiv \lim_{\text{dm}} \bar{\upsilon}_{-1} \\ \left(\text{res}_{\text{sm}^{-1}}^{\partial m} u\right)_{-1} \equiv \text{res}_{\text{dm}}^{\partial m} u_{-1} \\ \left(\text{res}_{\text{sm}^{-1}}^{m} u\right)_{-1} \equiv \text{res}_{\text{dm}}^{m} u_{-1}. \end{array}$$

61

We then inductively define:

$$\pi(\lim_{\mathfrak{m}^{n+2}} \bar{Y}) \equiv \lim_{\mathfrak{m}^{n+1}} \pi \bar{Y}$$

$$(\lim_{\mathfrak{m}^{n+2}} \bar{Y})_{n+2} \equiv (\lim_{\mathfrak{m}^{n}} \bar{Y}^d)_{n+1}$$

$$\pi(\lim_{\mathfrak{m}^{n+2}} \bar{v}) \equiv \lim_{\mathfrak{m}^{n+1}} \pi \bar{v}$$

$$(\lim_{\mathfrak{m}^{n+2}} \bar{v})_{n+2} \equiv (\lim_{\mathfrak{m}^{n}} \bar{v}^d)_{n+1}$$

$$\pi(\text{res}_{\mathfrak{m}^{n+2}}^{\partial m} u) \equiv \text{res}_{\mathfrak{m}^{n+1}}^{\partial m} \pi u$$

$$(\text{res}_{\mathfrak{m}^{n+2}}^{\partial m} u)_{n+2} \equiv (\text{res}_{\mathfrak{m}^{n}}^d u^d)_{n+1}$$

$$\pi(\text{res}_{\mathfrak{m}^{n+2}}^m u) \equiv \text{res}_{\mathfrak{m}^{n+1}}^m \pi u$$

$$(\text{res}_{\mathfrak{m}^{n+2}}^m u)_{n+2} \equiv (\text{res}_{\mathfrak{m}^{n}}^m u^d)_{n+1}.$$

As always, this says that the constructions are performed level-wise. From this, theorems eqs. (4.25) to (4.28) then follow inductively, since the hypothesised display formulas were used to define each successive level. The correctness of these definitions will follow from verifying laws in appendix A.4.

### 4.2.9 The Simplicial Model

Having constructed the truncated simplicial models $\mathfrak{sm}^n$, we obtain the *simplicial model* fairly directly by taking a limit. In order to state this, we first define a *tail-cutting truncation functor* and extend *décalage* to an endofunctor:

$$\pi_n : \mathcal{C}^{\Delta^+} \to \mathcal{C}^{\Delta_n^+} \quad (-)^D : \mathcal{C}^{\Delta^+} \to \mathcal{C}^{\Delta^+}$$

$$(\pi_n \Gamma)_{m+1} \equiv \Gamma_{m+1} \quad (\Gamma^D)_{m+1} \equiv \Gamma_{m+2}$$

$$(\pi_n \Gamma)^b \equiv \Gamma^b \quad (\Gamma^D)^b \equiv \Gamma^{\ddagger b}$$

$$(\pi_n \sigma)_{m+1} \equiv \sigma_{m+1} \quad (\sigma^D)_{m+1} \equiv \sigma_{m+2}$$

Since décalage is now an endofunctor, $\rho$ no longer involves truncation:

$$\rho : (-)^D \Rightarrow 1_{\mathcal{C}^{\Delta^+}}$$

$$(\rho_\Gamma)_{m+1} \equiv \Gamma^{\Theta_1(m+1)}$$

Now we define the types and terms in $\mathfrak{sm}$ to be compatible towers of types and terms in the truncated models $\mathfrak{sm}^n$. In syntax this can be expressed by the following infinitary bidirectional rules:

$$\frac{(\gamma : \pi_n \Gamma \vdash_{\mathfrak{sm}_n} \pi_n A \gamma \text{ type}_\ell)_{n \geqslant -2} \quad (\pi(\pi_{n+1} A) \equiv \pi_n A)_{n \geqslant -2}}{\gamma : \Gamma \vdash_{\mathfrak{sm}} A \gamma \text{ type}_\ell}$$

$$\frac{(\gamma : \pi_n \Gamma \vdash_{\mathfrak{sm}_n} \pi_n t \gamma : \pi_n A \gamma)_{n \geqslant -2} \quad (\pi(\pi_{n+1} t) \equiv \pi_n t)_{n \geqslant -2}}{\gamma : \Gamma \vdash_{\mathfrak{sm}} t \gamma : A \gamma}$$

We also define:

$$\frac{\gamma : \Gamma \vdash_{\mathfrak{sm}} A \gamma \text{ type}_\ell}{A_{n+1} \equiv (\pi_{n+1} A)_{n+1}} \quad \frac{\gamma : \Gamma \vdash_{\mathfrak{sm}} t \gamma : A \gamma}{t_{n+1} \equiv (\pi_{n+1} t)_{n+1}}.$$

62

The the above introduction rules equivalently then say that A and t in sm are defined by the data of each of the simplex levels $A_{n+1}$ and $t_{n+1}$. At this point, every single construction in $\text{sm}^n$ performed above extends to sm levelwise, since it is preserved strictly by all the finite truncation functors. In lieu of listing all of them, we will only give the case of display, which is slightly modified in the absence of truncation:

$$\frac{\gamma : \Gamma \vdash_{\text{sm}} A \gamma \text{ type}_\ell}{\gamma^+ : \Gamma^D, a : A^{pr} \gamma^+ \vdash_{\text{sm}} A^d \gamma^+ a \text{ type}_\ell}$$

$$\frac{\gamma : \Gamma \vdash_{\text{sm}} t \gamma : A \gamma}{\gamma^+ : \Gamma^D \vdash_{\text{sm}} t^d \gamma^+ : A^d \gamma^+ t^{pr}}$$

The computation rules for display on variables, $\Pi$-types, universes, and $\omega$-limits similarly hold in sm when modified to exclude $\pi$.

### 4.3 MODALITIES

We now relate the discrete (dm) and simplicial (sm) models by way of modalities, and introduce modal variants of the structural operations of a CwF.

The interesting facet of our approach is our treatment of $(\Gamma, \bullet_\Delta)$ and $(\gamma : \Gamma, a :^\Delta A \gamma)$. These examples concern the passage from dm to sm. Both examples construct a context in sm, but where (part of) the starting data is discrete — $\Gamma$ in the first example and A in the second example. One naive approach to this construction would be to convert the discrete data to simplicial data (fibrantly so in the second case) — in the first example we would set values of the presheaf at $m + 2$ to be zeros, and in the second example we would set the simplex types at levels $m + 2$ to be units. However, this would require us to assume that the starting CwF has, respectively, an initial object and unit types. The approach that we take avoids these assumptions, and also ensures that all computation laws have definitionally strict interpretations.

#### 4.3.1 Pieces of the triangle modality

We begin by dealing with $\triangle$. The modality $\triangle$ is supposed to construct a constant (augmented semi-)simplicial diagram, while its left adjoint $\bullet_\triangle$ picks out the object of (-1)-simplices. Both of these operations are determined levelwise by their behavior on truncated diagrams, which is where most of the work is. Recalling that we will not be modeling the modality $\triangle$ on types itself, since it would require assuming the existence of unit types in dm, in this section we describe the other aspects of $\triangle$ in the models $\text{sm}^{n+1}$ and how they fit together on sm.

We begin by defining a functor $\left(-, \bullet_{\triangle_{n+1}}\right) : \mathcal{C}^{\triangle_{n+1}^+} \to \mathcal{C}$ via:

$$\begin{array}{l} \left(\gamma : \Gamma, \bullet_{\triangle_{n+1}}\right) \equiv \Gamma_{-1} \\ \left[\sigma, \bullet_{\triangle_{n+1}}\right] \equiv \sigma_{-1} \end{array}$$

Then we construct modal extension for $\triangle_{n+1}$ in $\text{sm}^{n+1}$:

$$\frac{\begin{array}{c} \Gamma \text{ ob}_{\text{sm}^{n+1}} \quad \gamma : \Gamma, \bullet_{\triangle_{n+1}} \vdash_{\text{dm}} A \gamma \text{ type}_\ell \\ \hline \left(\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma\right) \text{ ob}_{\text{sm}^{n+1}} \end{array}}{\frac{\sigma : \Delta \to_{\text{sm}^{n+1}} \Gamma \quad \gamma : \Gamma, \bullet_{\triangle_{n+1}} \vdash_{\text{dm}} t \gamma : A \gamma}{\left[\sigma, t\right]_{\triangle_{n+1}} : \Delta \to_{\text{sm}^{n+1}} \left(\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma\right)}}$$

63

These are defined such that:

$$\left( \gamma : \Gamma, a :^{\triangle_{n+2}} A \gamma \right)^D \equiv \left( \gamma^+ : \Gamma^D, a :^{\triangle_{n+1}} A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]} \gamma^+ \right)$$

$$\left( [\sigma, t]_{\triangle_{n+2}} \right)^D \equiv [\sigma^D, t^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}]_{\triangle_{n+1}}$$

For dimension $-1$, we define:

$$\left( \gamma : \Gamma, a :^{\triangle_{-1}} A \gamma \right)_{-1} \equiv \left( \gamma_{-1} : \Gamma_{-1}, a : A \gamma_{-1} \right)$$

$$\left( [\sigma, t]_{\triangle_{-1}} \right)_{-1} \equiv [\sigma_{-1}, t]$$

Then we inductively define:

$$\left( \gamma : \Gamma, a :^{\triangle_{n+2}} A \gamma \right)_{m+1} \equiv \left( \gamma^- : \pi \Gamma, a :^{\triangle_{n+1}} A \gamma^- \right)_{m+1} \quad \text{for} \quad m \leqslant n$$

$$\left( \gamma : \Gamma, a :^{\triangle_{n+2}} A \gamma \right)_{n+2} \equiv \left( \gamma^+ : \Gamma^D, a :^{\triangle_{n+1}} A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]} \gamma^+ \right)_{n+1}$$

$$\left( [\sigma, t]_{\triangle_{n+2}} \right)_{m+1} \equiv \left( [\pi \sigma, t]_{\triangle_{n+1}} \right)_{m+1} \quad \text{for} \quad m \leqslant n$$

$$\left( [\sigma, t]_{\triangle_{n+2}} \right)_{n+2} \equiv \left( [\sigma^D, t^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}]_{\triangle_{n+1}} \right)_{n+1}$$

We next have fundamental context projections and zero variables:

$$\frac{\gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}} \vdash_{dm} A \gamma \text{ type}_\ell}{\text{pt}_{\triangle_{n+1}}^A : \left( \gamma : \Gamma, a :^{\triangle_{n+1}} A \right) \rightarrow_{sm^{n+1}} \Gamma}$$

$$\frac{\gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}} \vdash_{dm} A \gamma \text{ type}_\ell}{\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}} \vdash_{dm} zv_{\triangle_{n+1}}^A \gamma a : A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]} \gamma a}$$

These are defined such that:

$$\left( \text{pt}_{\triangle_{n+2}}^A \right)^D \equiv \text{pt}_{\triangle_{n+1}}^{A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}}$$

For dimension $-1$, we define:

$$\left( \text{pt}_{\triangle_{-1}}^A \right)_{-1} \equiv \text{pt}_{dm}^A$$

$$zv_{\triangle_{-1}}^A \equiv zv_{dm}^A$$

Then we inductively define:

$$\pi \left( \text{pt}_{\triangle_{n+2}}^A \right) \equiv \text{pt}_{\triangle_{n+1}}^A$$

$$\left( \text{pt}_{\triangle_{n+2}}^A \right)_{n+2} \equiv \left( \text{pt}_{\triangle_{n+1}}^{A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}} \right)_{n+1}$$

$$zv_{\triangle_{n+2}}^A \equiv zv_{\triangle_{n+1}}^A$$

Finally, we construct modal $\Pi$-types:

$$\frac{\gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle} \vdash_{dm} A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma \vdash_{sm^{n+1}} B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash_{sm^{n+1}} \Pi_{\triangle}^{sm^{n+1}} A B \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma \vdash_{sm^n} t \gamma a : B \gamma a}{\gamma : \Gamma \vdash_{sm} \lambda_{\triangle}^{sm^{n+1}} t \gamma : \Pi_{\triangle}^{sm^{n+1}} A B \gamma}$$

$$\frac{\gamma : \Gamma \vdash_{sm^n} f \gamma : \Pi_{\triangle}^{sm^n} A B \gamma \quad \gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle} \vdash_{dm} s \gamma : A \gamma}{\gamma : \Gamma \vdash_{sm} \text{app}_{\triangle}^{sm^n} f s \gamma : B^{[1_\Gamma, s]_{\triangle}} \gamma}$$

64

This construction follows the pattern of the non-modal truncated case and is performed level-wise. We will inductively assert the following formulas for display:

$$\left( \Pi_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{A} \mathrm{B} \right)^{\mathrm{d}} \equiv \Pi_{\triangle}^{\mathrm{sm}^{n+1}} \left( \mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]} \right)^{\mathrm{pt}} \left( \mathrm{B}^{\mathrm{d}} \right)^{\left[ \mathrm{W}_{2}^{\mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]}} \mathrm{pt}, \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{zv}^{\mathrm{stop}} \mathrm{zv}_{\triangle}^{\mathrm{pt}} \right]}$$

$$\left( \lambda_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{t} \right)^{\mathrm{d}} \equiv \lambda_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{t}^{\mathrm{d}}$$

$$\left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{f} \mathrm{s} \right)^{\mathrm{d}} \equiv \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{f}^{\mathrm{d}} \mathrm{s}.$$

In dimension -1 we set:

$$\left( \Pi_{\triangle}^{\mathrm{sm}^{-1}} \mathrm{A} \mathrm{B} \right)_{-1} \equiv \Pi^{\mathrm{dm}} \mathrm{A} \mathrm{B}_{-1}$$

$$\left( \lambda_{\triangle}^{\mathrm{sm}^{-1}} \mathrm{t} \right)_{-1} \equiv \lambda^{\mathrm{dm}} \mathrm{t}_{-1}$$

$$\left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{-1}} \mathrm{f} \mathrm{s} \right)_{-1} \equiv \mathrm{app}^{\mathrm{dm}} \mathrm{f}_{-1} \mathrm{s}.$$

Then we inductively define:

$$\pi \left( \Pi_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{A} \mathrm{B} \right) \equiv \Pi_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{A} \pi \mathrm{B}$$

$$\left( \Pi_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{A} \mathrm{B} \right)_{n+2} \equiv \left( \Pi_{\triangle}^{\mathrm{sm}^{n+1}} \left( \mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]} \right)^{\mathrm{pt}} \left( \mathrm{B}^{\mathrm{d}} \right)^{\left[ \mathrm{W}_{2}^{\mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]}} \mathrm{pt}, \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{zv}^{\mathrm{stop}} \mathrm{zv}_{\triangle}^{\mathrm{pt}} \right]} \right)_{n+1}$$

$$\pi \left( \lambda_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{t} \right) \equiv \lambda_{\triangle}^{\mathrm{sm}^{n+1}} \pi \mathrm{t}$$

$$\left( \lambda_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{t} \right)_{n+2} \equiv \lambda_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{t}^{\mathrm{d}}$$

$$\pi \left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{f} \mathrm{s} \right) \equiv \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \pi \mathrm{f} \mathrm{s}$$

$$\left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{f} \mathrm{s} \right)_{n+2} \equiv \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{f}^{\mathrm{d}} \mathrm{s}.$$

The verification of many identities has been omitted.

Finally, we check that $\pi$ preserves all the operations defined above. Therefore, we can define the untruncated operations $\triangle$ and $\mathbf{\Theta}_{\triangle}$ on sm, with modal context extension $x :^{\triangle} \mathrm{A}$ and modal $\Pi$-types, simply by acting levelwise on each $\mathrm{sm}^{n+1}$.

### 4.3.2 Pieces of the Box Modality

The box modality is more subtle because it is not determined levelwise by operations on truncated diagrams. However, we can still construct it in terms of truncated data. We start with a truncated lock functor $\{-, \mathbf{\Theta}_{\square_n}\} : \mathcal{C} \to \mathcal{C}^{\Delta_n^*$ that constructs a constant simplicial diagram:

$$\left( \gamma : \Gamma, \mathbf{\Theta}_{\square_{n+1}} \right)_{m+1} \equiv \Gamma$$

$$\left( \gamma : \Gamma, \mathbf{\Theta}_{\square_{n+1}} \right)^{\mathrm{b}} \equiv 1_{\Gamma}$$

$$[\sigma, \mathbf{\Theta}_{\square_{n+1}}]_{m+1} \equiv \sigma.$$

We define the following four new pieces of syntax. The operation $\mathrm{A}_{\square(n+1)}$ is like a truncated version of $\square$, in that it takes the limit of a truncated diagram, but yielding a finite

65

telescope rather than a type.

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\gamma : \Gamma \vdash_{\text{dm}} A_{\square(n+1)} \gamma \text{ tel}_\ell} \quad \frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\text{dm}} t_{\square(n+1)} : A_{\square(n+1)} \gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\text{pt}_{\square_n}^A : (\gamma : \Gamma, \square a : A_{\square(n+1)} \gamma) \to \Gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\gamma : \Gamma, \square a : A_{\square(n+1)} \gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} z v_{\square_n}^A \gamma \square a : A^{[\text{pt}_{\square_n}^A, \mathbf{\Omega}_{\square_n}]} \gamma \square a}$$

These will satisfy the inductively proven property that for $\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} t \gamma : A \gamma$:

$$\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} z v_{\square_n}^A \gamma (t_{\square(n+1)} \gamma) \equiv t \gamma.$$

For $\text{sm}^{-2}$, the term $z v_{\square_{-2}}^A$ is trivial, since it lives in the terminal CwF structure. We also set:

$$A_{\square(-1)} \gamma \equiv ()_{\text{dm}}$$

$$t_{\square(-1)} \gamma \equiv []_{\text{dm}}$$

$$\text{pt}_{\square_{-2}}^A \equiv 1_\Gamma.$$

Note that, in general, since $z v_{\square_n}^A$ is a simplicial term, we may form its matching substitution:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\gamma : \Gamma, \square a : A_{\square(n+1)} \gamma \vdash_{\text{dm}} (z v_{\square_n}^A)_{\partial(n+1)} \gamma \square a : A_{\partial(n+1)} \gamma}$$

For $\text{sm}^{n+1}$ we then inductively set:

$$A_{\square(n+2)} \equiv (a : \pi A_{\square(n+1)} \gamma, a' : A_{n+1} \gamma ((z v_{\square_n}^{\pi A})_{\partial(n+1)} \gamma a)$$

$$t_{\square(n+2)} \equiv [t_{\square(n+1)}, t_{n+1}]$$

$$\text{pt}_{\square_{n+1}}^A \equiv \text{pt}_{\square_n}^{\pi A} \circ \text{pt}_{\text{dm}}^{A_{n+1}}$$

$$z v_{\square_{n+1}}^A \equiv \langle (z v_{\square_n}^{\pi A})^{[\text{pt}_{\text{dm}}^{A_{n+1}}, \mathbf{\Omega}_{\square}]}, (z v_{\square_{n+1}}^A)_{n+1} \rangle$$

$$(z v_{\square_{n+1}}^A)_{n+1} \gamma [a, a'] \equiv a'.$$

The second line is well typed by the inductive hypothesis and makes the next case of the hypothesis clear. Also, note the pt substitution in the fourth line. The basic idea is that, at the top dimension, the $(n+1)$-st simplicial value of a boxed variables access the last component of the modal context extension, whereas lower dimensional simplicial values search further back in the linear context.

We now move on to the untruncated model. The functor $\mathbf{\Omega}_{\square}$ in sm similarly constructs a constant presheaf. Note that $(\Gamma, \mathbf{\Omega}_{\square})^D \equiv (\Gamma, \mathbf{\Omega}_{\square})$, and $\rho_{\Gamma, \mathbf{\Omega}_{\square}}$ is an identity; we will omit writing these whenever the previous rules say that a $^D$ or $\rho$ is necessary. We now define a key natural transformation:

$$\mathbf{\Omega}_{\square}^{\triangle \square \leqslant 1_{\text{sm}}} : 1_{\text{sm}} \Rightarrow (-, \mathbf{\Omega}_{\triangle \square})$$

$$\left( \mathbf{\Omega}_{\square}^{\triangle \square \leqslant 1_{\text{sm}}} \right)_{m+1} \equiv \Gamma^{D^{m+1}}.$$

66

We then use the constructions above to construct a modal type former:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} A \gamma \text{ type}_t}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square_{\mathrm{sm}} A \gamma \text{ type}_t}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square_{\mathrm{sm}} t \gamma : \square_{\mathrm{sm}} A \gamma}$$

$$\frac{\gamma_{-1} : \mathbf{\Omega}_{\triangle} \Gamma \vdash_{\mathrm{dm}} t \gamma_{-1} : \square A \gamma_{-1}}{\gamma : \Gamma \vdash_{\mathrm{sm}} \mathbf{\Sigma}_{\mathrm{sm}}^A t \gamma : A \left( \mathbf{\Omega}_{\mathbf{t}}^\triangle \square \leqslant 1_{\mathrm{sm}} \gamma \right)}$$

(Recall from section 4.3.1 that $\mathbf{\Omega}_{\triangle} \Gamma \equiv \Gamma_{-1}$.) In order to form these, we will take an $\omega$-limit of sequences $A_{\square}$ or $t_{\square}$ obtained from the $m$-simplex levels of $A$ or $t$:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} A \gamma \text{ type}_t}{\gamma : \Gamma \vdash_{\mathrm{dm}} A_{\square} \text{ stel}_t^{\infty}}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} t \gamma : A \gamma \text{ type}_t}{\gamma : \Gamma \vdash_{\mathrm{dm}} t_{\square} \gamma : A_{\square} \gamma}$$

These are defined as follows:

$$A_{\square}^{\partial(m+1)} \gamma \equiv (\pi_m A)_{\square(m+1)} \gamma$$

$$A_{\square}^{m+1} \gamma \square a \equiv A_{m+1} \gamma \left( \left( zv_{\square_m}^{\pi_m A} \right)_{\partial(m+1)} \gamma \square a \right)$$

$$t_{\square}^{\partial(m+1)} \gamma \equiv (\pi_m t)_{\square(m+1)} \gamma$$

$$t_{\square}^{m+1} \gamma \equiv t_{m+1} \gamma.$$

We then define:

$$\square_{\mathrm{sm}} A \equiv \lim A_{\square}$$

$$\square_{\mathrm{sm}} t \equiv \lim t_{\square}.$$

We define the eliminator by:

$$\pi_{n+1} \left( \mathbf{\Sigma}_{\mathrm{sm}}^A a \right) \gamma_{n+1} \equiv zv_{\square_{n+1}}^{\pi_{n+1} A} \gamma_{n+1}^{\partial^{n+1}} \left[ \text{res}^{\partial(n+1)} \gamma_{n+1}^{\partial^{n+1}} a, \text{res}^{n+1} \gamma_{n+1}^{\partial^{n+1}} a \right].$$

One then checks the computation laws.

◁

### 4.3.3 The Extended Simplicial Model

So far, we have equipped the simplicial model sm with the locks $\mathbf{\Omega}_{\triangle}$ and $\mathbf{\Omega}_{\square}$, modal extension and modal $\Pi$-types for $\triangle$, and a modality $\square_{\mathrm{sm}}$ with Fitch-style introduction and elimination rules. (Because $\square_{\mathrm{sm}}$ satisfies an $\eta$-rule, we could then derive modal extension and modal $\Pi$-types for $\square_{\mathrm{sm}}$ by simply extending and mapping out of $\square_{\mathrm{sm}} A$, as we will do in sections 4.3.6 and 4.3.7 for our eventual model.)

The modality $\diamond$ presents a different problem: in syntax, for $\Gamma \text{ ob}_{\mathrm{dm}}$, the context $(\Gamma, \mathbf{\Omega}_{\diamond})$ is flat. This creates an issue of how we store such contexts semantically. Our solution is to extend the simplicial model constructed in section 4.2 to what we call the extended simplicial model, $\text{sm}_+$, built out of a copy of dm (representing the flat contexts) and the original sm (representing the non-flat contexts). We start with the non-modal aspects of this model.

67

#### 4.3.3.1 Contexts and substitutions. We have the following introduction rules:

\[
\frac {\Gamma \mathrm{ob} _ {\mathrm{dm}}}{\mathrm{in} _ {\mathrm{dm}} \Gamma \mathrm{ob} _ {\mathrm{sm} _ {+}}}
\]

\[
\frac {\Gamma \mathrm{ob} _ {\mathrm{sm}}}{\mathrm{in} _ {\mathrm{sm}} \Gamma \mathrm{ob} _ {\mathrm{sm} _ {+}}}
\]

\[
\frac {\sigma : \Delta \rightarrow_ {\mathrm{sm}} \Gamma}{\mathrm{in} _ {\mathrm{sm}} \sigma : \mathrm{in} _ {\mathrm{sm}} \Delta \rightarrow_ {\mathrm{sm} _ {+}} \mathrm{in} _ {\mathrm{sm}} \Gamma}
\]

\[
\frac {\sigma : \Delta \rightarrow_ {\mathrm{dm}} \Gamma}{\mathrm{in} _ {\mathrm{dm}} \sigma : \mathrm{in} _ {\mathrm{dm}} \Delta \rightarrow_ {\mathrm{sm} _ {+}} \mathrm{in} _ {\mathrm{dm}} \Gamma}
\]

\[
\frac {\sigma : \Delta \rightarrow_ {\mathrm{dm}} \Gamma_ {- 1}}{\mathrm{in} _ {\mathrm{fl}} \sigma : \mathrm{in} _ {\mathrm{dm}} \Delta \rightarrow_ {\mathrm{sm} _ {+}} \mathrm{in} _ {\mathrm{sm}} \Gamma}
\]

Equivalently, we can say that the underlying category of \(\mathfrak{sm}_{+}\), which we denote \(\mathcal{C}_{+}^{\Delta +}\), is defined as follows:

\[
\mathrm{ob} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \cong \mathrm{ob} _ {\mathcal {C}} \sqcup \mathrm{ob} _ {\mathcal {C} ^ {\Delta^ {+}}}
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{dm}} \Delta , \operatorname{in} _ {\mathrm{dm}} \Gamma\right) \cong \operatorname{mor} _ {\mathcal {C}} (\Delta , \Gamma)
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{sm}} \Delta , \operatorname{in} _ {\mathrm{sm}} \Gamma\right) \cong \operatorname{mor} _ {\mathcal {C} ^ {\Delta^ {+}}} (\Delta , \Gamma)
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{dm}} \Delta , \operatorname{in} _ {\mathrm{sm}} \Gamma\right) \cong \operatorname{mor} _ {\mathcal {C}} \left(\Delta , \Gamma_ {- 1}\right)
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{sm}} \Delta , \operatorname{in} _ {\mathrm{dm}} \Gamma\right) \cong \emptyset .
\]

This makes sense, because we intuitively think of  \( in_{dm} \Delta \)  as having been extended by zeroes, thus it is easy to map out of. A substitution of the form  \( in_{fl} \sigma \)  is known as flat.

#### 4.3.3.2 Types and Terms. We have the following introduction forms for types and terms in \(\mathfrak{sm}_{+}\):

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{dm}} A \gamma \text {type} _ {\ell}}{\gamma : \text {in} _ {\mathrm{dm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{dm}} A \gamma \text {type} _ {\ell}}
\]

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{sm}} A \gamma \text {type} _ {\ell}}{\gamma : \text {in} _ {\mathrm{sm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{sm}} A \gamma \text {type} _ {\ell}}
\]

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{dm}} t \gamma : A \gamma}{\gamma : \text {in} _ {\mathrm{dm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{dm}} t \gamma : \text {in} _ {\mathrm{dm}} A \gamma}
\]

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{sm}} t \gamma : A \gamma}{\gamma : \text {in} _ {\mathrm{sm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{sm}} t \gamma : \text {in} _ {\mathrm{sm}} A \gamma}.
\]

Formally, we set the following, depending on whether on not  \( \Gamma \)  is flat:

\[
\mathrm{Ty} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{dm}} \Gamma\right) \cong \mathrm{Ty} _ {\mathrm{dm}} \Gamma
\]

\[
\mathrm{Tm} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{dm}} \Gamma\right) \left(\mathrm{in} _ {\mathrm{dm}} A\right) \cong \mathrm{Tm} _ {\mathrm{dm}} \Gamma A
\]

\[
\mathrm{Ty} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{sm}} \Gamma\right) \cong \mathrm{Ty} _ {\mathrm{sm}} \Gamma
\]

\[
\mathrm{Tm} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{sm}} \Gamma\right) \left(\mathrm{in} _ {\mathrm{sm}} A\right) \cong \mathrm{Tm} _ {\mathrm{sm}} \Gamma A.
\]

Note that, in the following definition of the functorial action of substitutions, the flat case discards higher data:

\[
\left(\operatorname{in} _ {\mathrm{dm}} A\right) ^ {\operatorname{in} _ {\mathrm{dm}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{dm}} t\right) ^ {\operatorname{in} _ {\mathrm{dm}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} A\right) ^ {\operatorname{in} _ {\mathrm{sm}} \sigma} \equiv \operatorname{in} _ {\mathrm{sm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} t\right) ^ {\operatorname{in} _ {\mathrm{sm}} \sigma} \equiv \operatorname{in} _ {\mathrm{sm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} A\right) ^ {\operatorname{in} _ {\mathrm{fl}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} \left(A _ {- 1}\right) ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} t\right) ^ {\operatorname{in} _ {\mathrm{fl}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} \left(A _ {- 1}\right) ^ {\sigma}.
\]

Extension of contexts operates by passing under the inclusion:

\[
\left(\operatorname{in} _ {\mathrm{dm}} \Gamma , \operatorname{in} _ {\mathrm{dm}} A\right) \equiv \operatorname{in} _ {\mathrm{dm}} (\Gamma , A)
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} \Gamma , \operatorname{in} _ {\mathrm{sm}} A\right) \equiv \operatorname{in} _ {\mathrm{sm}} (\Gamma , A)
\]

\[
\left[ \begin{array}{c c} \text {in} _ {\mathrm{dm}} & \sigma , \text {in} _ {\mathrm{dm}} t \end{array} \right] \equiv \text {in} _ {\mathrm{dm}} [ \sigma , t ]
\]

\[
\left[ \begin{array}{c c} \text {in} _ {\mathrm{sm}} & \sigma , \text {in} _ {\mathrm{sm}} t \end{array} \right] \equiv \text {in} _ {\mathrm{sm}} [ \sigma , t ]
\]

\[
\left[ \begin{array}{c c} \text {in} _ {\mathrm{fl}} & \sigma , \text {in} _ {\mathrm{dm}} t \end{array} \right] \equiv \text {in} _ {\mathrm{fl}} [ \sigma , t ].
\]

68

Note that in the last case, if we have $\text{in}_{\text{fl}} \sigma : \text{in}_{\text{dm}} \Delta \to \text{in}_{\text{sm}} \Gamma$ then $\sigma : \Delta \to \Gamma_{-1}$. In order to form the extension $[\text{in}_{\text{fl}} \sigma, s] : \text{in}_{\text{dm}} \Delta \to \text{in}_{\text{sm}} (\gamma : \Gamma, a : A \gamma)$, we must give $\delta : \text{in}_{\text{dm}} \Delta \vdash_{\text{sm}_+} s \delta : (\text{in}_{\text{sm}} A)^{\text{in}_{\text{fl}} \sigma} \delta$. We see then that such an $s$ has type $\text{in}_{\text{dm}} (A_{-1})^\sigma$ and must be of the form $\text{in}_{\text{dm}} t$.

4.3.3.3 $\Pi$-Types and Universes. We define (non-modal) $\Pi$-types and universes in $\text{sm}_+$ by reducing to the respective constructs in $\text{dm}$ and $\text{sm}$, depending on whether or not the context is flat:

$$\begin{array}{l} \Pi^{\text{sm}_+} (\text{in}_{\text{dm}} A) (\text{in}_{\text{dm}} B) \equiv \text{in}_{\text{dm}} (\Pi^{\text{dm}} A B) \\ \Pi^{\text{sm}_+} (\text{in}_{\text{sm}} A) (\text{in}_{\text{sm}} B) \equiv \text{in}_{\text{sm}} (\Pi^{\text{sm}} A B) \\ \text{Type}_{\ell}^{\text{sm}_+} \equiv \begin{cases} \text{in}_{\text{dm}} \text{Disc}_{\ell} & \text{for} \quad \text{in}_{\text{dm}} \Gamma \\ \text{in}_{\text{sm}} \text{Type}_{\ell}^{\text{sm}} & \text{for} \quad \text{in}_{\text{sm}} \Gamma. \end{cases} \end{array}$$

The definitions of $\lambda^{\text{sm}_+}$, $\text{app}^{\text{sm}_+}$, $\text{Code}^{\text{sm}_+}$, and $\text{EI}^{\text{sm}_+}$ are similar.

Note that stability under substitution is a more general property in $\text{sm}_+$ since we have to additionally consider flat substitutions; if $\text{in}_{\text{fl}} \sigma : \text{in}_{\text{dm}} \Delta \to \text{in}_{\text{sm}} \Gamma$, then we have:

$$\begin{array}{l} \left(\Pi^{\text{sm}_+} (\text{in}_{\text{sm}} A) (\text{in}_{\text{sm}} B)\right)^{\text{in}_{\text{fl}} \sigma} \\ \equiv \left(\text{in}_{\text{sm}} (\Pi^{\text{sm}} A B)\right)^{\text{in}_{\text{fl}} \sigma} \\ \equiv \text{in}_{\text{dm}} \left((\Pi^{\text{sm}} A B)_{-1}\right)^\sigma \\ \equiv \text{in}_{\text{dm}} \left(\Pi^{\text{dm}} A_{-1} B_{-1}\right)^\sigma \\ \equiv \text{in}_{\text{dm}} \left(\Pi^{\text{dm}} (A_{-1})^\sigma (B_{-1})^{W_2^{A_{-1}} \sigma}\right) \\ \equiv \Pi^{\text{sm}_+} (\text{in}_{\text{dm}} (A_{-1})^\sigma) (\text{in}_{\text{dm}} (B_{-1})^{W_2^{A_{-1}} \sigma}) \\ \equiv \Pi^{\text{sm}_+} (\text{in}_{\text{sm}} A)^{\text{in}_{\text{fl}} \sigma} (\text{in}_{\text{sm}} B)^{W_2^A (\text{in}_{\text{fl}} \sigma)} \end{array}$$

Similarly for universes:

$$\begin{array}{l} \left(\text{Type}_{\ell}^{\text{sm}_+}\right)^{\text{in}_{\text{fl}} \sigma} \equiv \left(\text{in}_{\text{sm}} \text{Type}_{\ell}^{\text{sm}}\right)^{\text{in}_{\text{fl}} \sigma} \\ \equiv \text{in}_{\text{dm}} \left((\text{Type}_{\ell}^{\text{sm}})_{-1}\right)^\sigma \\ \equiv \text{in}_{\text{dm}} \text{Disc}_{\ell}^\sigma \\ \equiv \text{in}_{\text{dm}} \text{Disc}_{\ell} \\ \equiv \text{Type}_{\ell}^{\text{sm}_+} \end{array}$$

What makes these calculations work is the relevant constructs have been defined to agree with their discrete counterparts in dimension -1. In the rest of this section, we show how $\text{dm}$ and $\text{sm}^+$ can be made into a model of all of dTT (except for the type-former $\triangle$).

69

#### 4.3.4 Locks and Keys

The definition of \(\mathfrak{sm}^+\) is tailored to allow us to define \(\widehat{\mathbf{a}}_{\diamond}\). Putting this together with the \(\widehat{\mathbf{a}}_{\triangle}\) and \(\widehat{\mathbf{a}}_{\square}\) defined on \(\mathfrak{sm}\) in sections 4.3.1 and 4.3.2, we now define a 2-functor \([[-]]: \mathcal{M}^{\mathrm{coop}} \to \mathcal{C}at\), where \(\mathcal{M}^{\mathrm{coop}}\) denotes the 2-category obtained by reversing both 1 and 2 cells. On modes, we have:

\[
[ [ \mathrm{dm} ] ] \equiv \mathcal {C}
\]

\[
[ [ \mathrm{sm} ] ] \equiv \mathcal {C} _ {+} ^ {\Delta^ {+}}.
\]

To define this 2-functor on modalities, we extend the prior definitions of locks to \(\mathfrak{sm}_{+}\):

\[
\left(-, \widehat {\mathbf {a}} _ {\triangle} ^ {+}\right): \mathcal {C} _ {+} ^ {\Delta^ {+}} \rightarrow \mathcal {C}
\]

\[
\left(-, \widehat {\mathbf {a}} _ {\square} ^ {+}\right): \mathcal {C} \rightarrow \mathcal {C} _ {+} ^ {\Delta^ {+}}
\]

\[
\left(-, \widehat {\mathbf {a}} _ {\diamond} ^ {+}\right): \mathcal {C} \rightarrow \mathcal {C} _ {+} ^ {\Delta^ {+}}
\]

\[
\left(\operatorname{in} _ {\mathfrak {s m}} \Gamma , \widehat {\mathbf {a}} _ {\triangle} ^ {+}\right) \equiv (\Gamma , \widehat {\mathbf {a}} _ {\triangle})
\]

\[
\left(\Gamma , \widehat {\mathbf {a}} _ {\square} ^ {+}\right) \equiv \operatorname{in} _ {\mathrm{sm}} \left(\Gamma , \widehat {\mathbf {a}} _ {\square}\right)
\]

\[
\left(\Gamma , \widehat {\mathbf {a}} _ {\diamond} ^ {+}\right) \equiv \operatorname{in} _ {\mathrm{dm}} \Gamma
\]

\[
\left(\operatorname{in} _ {\mathrm{dm}} \Gamma , \widehat {\mathbf {a}} _ {\triangle} ^ {+}\right) \equiv \Gamma
\]

\[
[ \mathrm{in} _ {\mathrm{sm}} \sigma , \widehat {\mathbf {a}} _ {\triangle} ^ {+} ] \equiv \sigma_ {- 1}
\]

\[
[ \sigma , \widehat {\mathbf {a}} _ {\square} ^ {+} ] _ {m + 1} \equiv \operatorname{in} _ {\mathrm{sm}} [ \sigma , \widehat {\mathbf {a}} _ {\square} ]
\]

\[
[ \sigma , \widehat {\mathbf {a}} _ {\diamond} ^ {+} ] \equiv \operatorname{in} _ {\mathrm{dm}} \sigma .
\]

\[
[ \mathrm{in} _ {\mathrm{dm}} \sigma , \widehat {\mathbf {a}} _ {\triangle} ^ {+} ] \equiv \sigma
\]

\[
[ \mathrm{in} _ {\mathrm{fl}} \sigma , \widehat {\mathbf {a}} _ {\triangle} ^ {+} ] \equiv \sigma
\]

We then define the evident composites:

\[
\left(-, \widehat {\mathbf {a}} _ {\triangle \square} ^ {+}\right) \equiv \left(-, \widehat {\mathbf {a}} _ {\triangle} ^ {+}, \widehat {\mathbf {a}} _ {\square} ^ {+}\right)
\]

\[
\left(-, \widehat {\mathbf {a}} _ {\triangle \diamond} ^ {+}\right) \equiv \left(-, \widehat {\mathbf {a}} _ {\triangle} ^ {+}, \widehat {\mathbf {a}} _ {\diamond} ^ {+}\right).
\]

Finally, it is easy to check that \(\left(-,\widehat{\mathbf{a}}_{\square}^{+},\widehat{\mathbf{a}}_{\triangle}^{+}\right)\) and \(\left(-,\widehat{\mathbf{a}}_{\diamond}^{+},\widehat{\mathbf{a}}_{\triangle}^{+}\right)\) define identity functors. It follows that we have a contravariantly functorial assignment:

\[
\frac {\mu : p \to q}{[ [ \mu ] ] \equiv (- , \widehat {\mathbf {a}} _ {\mu} ^ {+}) : [ [ q ] ] \to [ [ p ] ]}
\]

Next, to define this 2-functor on 2-cells, we define the key natural transformations. We have \(\square \leqslant \diamond\), \(\triangle \square \leqslant 1_{\mathrm{sm}_+}\), and \(1_{\mathrm{sm}_+} \leqslant \triangle \diamond\), which corresponds to the following natural transformations:

\[
\mathbf {a} _ {\bullet} ^ {\square \leqslant \diamond}: (-, \widehat {\mathbf {a}} _ {\diamond} ^ {+}) \Rightarrow (-, \widehat {\mathbf {a}} _ {\square} ^ {+})
\]

\[
\mathbf {a} _ {\bullet} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm} +}}: 1 _ {\mathrm{sm} +} \Rightarrow (-, \widehat {\mathbf {a}} _ {\triangle \square} ^ {+})
\]

\[
\mathbf {a} _ {\bullet} ^ {1 _ {\mathrm{sm} +} \leqslant \triangle \diamond}: (-, \widehat {\mathbf {a}} _ {\triangle \diamond} ^ {+}) \Rightarrow 1 _ {\mathrm{sm} +}
\]

\[
\mathbf {a} _ {\Gamma} ^ {\square \leqslant \diamond} \equiv \operatorname{in} _ {\mathrm{fl}} 1 _ {\Gamma}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{sm}} \Gamma} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm} +}} \equiv \operatorname{in} _ {\mathrm{sm}} \mathbf {a} _ {\Gamma} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm}}}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{sm}} \Gamma} ^ {1 _ {\mathrm{sm}} \leqslant \triangle \diamond} \equiv \operatorname{in} _ {\mathrm{fl}} 1 _ {\Gamma - 1}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{dm}} \Gamma} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm}}} \equiv \operatorname{in} _ {\mathrm{fl}} 1 _ {\Gamma}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{dm}} \Gamma} ^ {1 _ {\mathrm{sm}} \leqslant \triangle \diamond} \equiv \operatorname{in} _ {\mathrm{dm}} 1 _ {\Gamma}.
\]

We also have \(\mathbf{a}_{\bullet}^{\triangle \square \leqslant \triangle \diamond} \equiv \mathbf{a}_{\bullet}^{\triangle \square \leqslant 1_{\mathrm{sm}_{+}}} \circ \mathbf{a}_{\bullet}^{1_{\mathrm{sm}_{+}} \leqslant \triangle \diamond}\). The keys assemble into a contravariantly functorial assignment:

\[
\frac {\alpha : \mu \leqslant \nu}{[ [ \alpha ] ] \equiv \mathbf {a} _ {\bullet} ^ {\alpha} : [ [ \nu ] ] \Rightarrow [ [ \mu ] ]}.
\]

One checks whiskering identities to verify that  \( [[-] \)  defines a 2-functor  \( M^{coop} \to Cat \) .

◀

70

### 4.3.5 Modal Types

Displayed Type Theory has two modal type formers that we need to model (recall that we omit $\triangle$ at present):

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\diamond}^{+} \vdash_{\mathrm{sm}_{+}} A \gamma \text{ type}_{\ell}}{\gamma : \Gamma \vdash_{\mathrm{dm}} \diamond A \gamma \text{ type}_{\ell}}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square}^{+} \vdash_{\mathrm{sm}_{+}} A \gamma \text{ type}_{\ell}}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square A \gamma \text{ type}_{\ell}}$$

These come with the following intro and elimination forms:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\diamond}^{+} \vdash_{\mathrm{sm}_{+}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \diamond t \gamma : \diamond A \gamma}$$

$$\frac{\gamma : \Gamma \vdash_{\mathrm{dm}} t \gamma : \diamond A \gamma}{\gamma : \text{in}_{\mathrm{dm}} \Gamma \vdash_{\mathrm{sm}_{+}} \blacklozenge^{A} t \gamma : A \gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square}^{+} \vdash_{\mathrm{sm}_{+}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square t \gamma : \square A \gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\triangle}^{+} \vdash_{\mathrm{dm}} t \gamma : \square A \gamma}{\gamma : \Gamma \vdash_{\mathrm{sm}_{+}} \blacksquare^{A} t \gamma : A [\mathbf{\alpha}_{\Gamma}^{\triangle\square\leqslant 1_{\mathrm{sm}_{+}}} \gamma]}$$

Note that there is an asymmetry between the statements of laws for $\blacklozenge$ and $\blacksquare$. To clear up this confusion, we could have instead written:

$$\frac{\Gamma \text{ flat } \quad \gamma : \Gamma, \mathbf{\Omega}_{\triangle}^{+} \vdash_{\mathrm{dm}} t \gamma : \diamond A \gamma}{\gamma : \Gamma \vdash_{\mathrm{sm}_{+}} \blacklozenge^{A} t \gamma : A [\mathbf{\alpha}_{\Gamma}^{\triangle\diamond\diamond 1_{\mathrm{sm}_{+}}} \gamma]}$$

But this is entirely equivalent, because the semantic-side definition of the predicate $\Gamma$ flat is that $\Gamma$ is of the form $\text{in}_{\mathrm{dm}} \Delta$, in which case we have $((\text{in}_{\mathrm{dm}} \Delta), \mathbf{\Omega}_{\triangle}^{+}) \equiv \Delta$ by definition. Note that the key $\mathbf{\alpha}_{\Gamma}^{\triangle\diamond\diamond 1_{\mathrm{sm}_{+}}}$ does not arise from a natural transformation and is only defined when $\Gamma \equiv \text{in}_{\mathrm{dm}} \Delta$, in which case we simply have $\mathbf{\alpha}_{\text{in}_{\mathrm{dm}} \Delta}^{\triangle\diamond\diamond 1_{\mathrm{sm}_{+}}} \equiv \text{in}_{\mathrm{dm}} 1_{\Delta}$. The first definition can thus be seen as a proof-relevant pattern match along the flat predicate.

The definition of $\diamond$ and its introduction and elimination rules are done by shuffling around discrete information and inclusions:

$$\begin{array}{l} \diamond (\text{in}_{\mathrm{dm}} A) \equiv A \\ \diamond (\text{in}_{\mathrm{dm}} t) \equiv t \\ \blacklozenge^{A} t \equiv \text{in}_{\mathrm{dm}} t. \end{array}$$

For $\square$, we fall back to our prior construction for the type former and intro rule:

$$\begin{array}{l} \square (\text{in}_{\mathrm{sm}} A) \equiv \square_{\mathrm{sm}} A \\ \square (\text{in}_{\mathrm{sm}} t) \equiv \square_{\mathrm{sm}} t \end{array}$$

For the eliminator, we split on whether or not $\Gamma$ is flat:

$$\blacksquare^{\text{in}_{\mathrm{sm}} A} t \equiv \begin{cases} \text{in}_{\mathrm{dm}} (\blacksquare_{\mathrm{dm}}^{A} t) & \text{for } \text{in}_{\mathrm{dm}} \Gamma \\ \text{in}_{\mathrm{sm}} (\blacksquare_{\mathrm{dm}}^{A} t) & \text{for } \text{in}_{\mathrm{sm}} \Gamma \end{cases}$$

where the discrete case above is as follows:

$$\frac{\Gamma \text{ ob}_{\mathrm{dm}} \quad \gamma : \Gamma \vdash_{\mathrm{dm}} t \gamma : \lim A_{\square} \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \blacksquare_{\mathrm{dm}}^{A} t \gamma : A_{-1} \gamma}$$

It is defined by:

$$\blacksquare^{\text{in}_{\mathrm{sm}} A} t \equiv \text{res}^{-1} \gamma a$$

$\triangle$

71

### 4.3.6 Modal Variables

We have the following rules for extending a context and substitution modally:

$$\frac{\mu : p \to q \quad \Gamma \text{ ob}_{[\![q]\!]} \quad \gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} A \gamma \text{ type}_{\ell}}{(\gamma : \Gamma, a :^{\mu+} A \gamma) \text{ ob}_{[\![q]\!]}}$$

$$\frac{\sigma : \Delta \to_{[\![q]\!]} \Gamma \quad \gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} t \gamma : A \gamma}{[\sigma, t]_{\mu+} : \Delta \to_{[\![q]\!]} (\gamma : \Gamma, a :^{\mu+} A \gamma)}$$

The case of $\triangle_+$ is defined as follows, splitting on whether or not $\Gamma$ is flat:

$$(\gamma : \text{in}_{\text{dm}} \Gamma, a :^{\triangle_+} A \gamma) \equiv \text{in}_{\text{dm}} (\gamma : \Gamma, a : A \gamma)$$

$$[\text{in}_{\text{dm}} \sigma, t]_{\triangle_+} \equiv \text{in}_{\text{dm}} [\sigma, t]$$

$$(\gamma : \text{in}_{\text{sm}} \Gamma, a :^{\triangle_+} A \gamma) \equiv \text{in}_{\text{sm}} (\gamma : \Gamma, a :^{\triangle} A \gamma)$$

$$[\text{in}_{\text{sm}} \sigma, t]_{\triangle_+} \equiv \text{in}_{\text{sm}} [\sigma, t]_{\triangle}.$$

Following this, the rest of the definitions say that the case of modal extension reduces to extension by a variable or term of modal type:

$$(\gamma : \Gamma, a :^{\diamond_+} A \gamma) \equiv (\gamma : \Gamma, a : \diamond A \gamma)$$

$$[\sigma, t]_{\diamond_+} \equiv [\sigma, t]$$

$$(\gamma : \Gamma, a :^{\triangle\diamond_+} A \gamma) \equiv (\gamma : \Gamma, a :^{\triangle_+} \diamond A \gamma)$$

$$[\sigma, t]_{\triangle\diamond_+} \equiv [\sigma, t]_{\triangle_+}$$

$$(\gamma : \Gamma, a :^{\square_+} A \gamma) \equiv (\gamma : \Gamma, a : \square A \gamma)$$

$$[\sigma, t]_{\square_+} \equiv [\sigma, t]$$

$$(\gamma : \Gamma, a :^{\triangle\square_+} A \gamma) \equiv (\gamma : \Gamma, a :^{\triangle_+} \square A \gamma)$$

$$[\sigma, t]_{\triangle\square_+} \equiv [\sigma, t]_{\triangle_+}.$$

Each of the context extension operations comes with a notion of parent maps and variables:

$$\frac{\gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} A \gamma \text{ type}_{\ell}}{\text{pt}_{\mu_+}^A : (\gamma : \Gamma, a :^{\mu_+} A \gamma) \to \Gamma} \quad \frac{\gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} A \gamma \text{ type}_{\ell}}{\gamma : \Gamma, a :^{\mu_+} A \gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} zv_{\mu_+}^A \gamma a : A^{[\text{pt}_{\mu_+}^A, \mathbf{\Theta}_{\mu}^{+}]} \gamma a}$$

For the parent maps $\text{pt}_{\triangle_+}^A$, we make a definition by cases on whether or not $\Gamma$ is flat:

$$\text{pt}_{\triangle_+}^A \equiv \begin{cases} \text{in}_{\text{dm}} \text{ pt}_{\text{dm}}^A & \text{for} \quad \text{in}_{\text{dm}} \Gamma \\ \text{in}_{\text{sm}} \text{ pt}_{\triangle}^A & \text{for} \quad \text{in}_{\text{sm}} \Gamma. \end{cases}$$

The parent maps for $\diamond_+$ and $\square_+$ reduce to discrete parent maps of variables of modal type:

$$\text{pt}_{\diamond_+}^A \equiv \text{pt}_{\text{dm}}^{\diamond A} \quad \text{pt}_{\square_+}^A \equiv \text{pt}_{\text{dm}}^{\square A}.$$

Then, for $\triangle\diamond_+$ and $\triangle\square_+$, we combine this with the substitution above:

$$\text{pt}_{\triangle\diamond_+}^A \equiv \text{pt}_{\triangle_+}^{\diamond A} \quad \text{pt}_{\triangle\square_+}^A \equiv \text{pt}_{\triangle_+}^{\square A}.$$

72

For the zero variables for $\diamondsuit_{+}$ and $\square_{+}$, one checks that the following are well-typed:

$$z v_{\diamondsuit_{+}}^{A} \equiv \diamondsuit^{A} z v_{d m}^{\diamondsuit A}$$

$$z v_{\square_{+}}^{A} \equiv \blacksquare^{A} z v_{d m}^{\square A}.$$

For the zero variables $z v_{\triangle_{+}}^{A}$, we once again case split:

$$z v_{\triangle_{+}}^{A} \equiv \begin{cases} z v_{d m}^{A} & \text{for } \text{in}_{d m} \Gamma \\ z v_{\triangle}^{A} & \text{for } \text{in}_{s m} \Gamma. \end{cases}$$

Then, for $\diamondsuit_{+}$ and $\triangle \square_{+}$, we use $z v_{\triangle_{+}}$:

$$z v_{\diamondsuit \diamondsuit_{+}}^{A} \equiv \diamondsuit^{A} z v_{\triangle_{+}}^{\diamondsuit A}$$

$$z v_{\triangle \square_{+}}^{A} \equiv \blacksquare^{A} z v_{\triangle_{+}}^{\square A}.$$

### 4.3.7 Modal $\Pi$-Types

The last remaining modal construct that we must address is modal $\Pi$-types. These behave according to the following rules:

$$\frac{\mu : p \to q \quad \gamma : \Gamma, \widehat{\blacksquare}_{\mu}^{+} \vdash_{[p]} A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a :^{\mu_{+}} A \gamma \vdash_{[q]} B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash_{[q]} \Pi_{\mu}^{s m_{+}} A B \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma, a :^{\mu_{+}} A \gamma \vdash_{[q]} t \gamma a : B \gamma a}{\gamma : \Gamma \vdash_{[q]} \lambda_{\mu}^{s m_{+}} t \gamma : \Pi_{\mu}^{s m_{+}} A B \gamma}$$

$$\frac{\gamma : \Gamma \vdash_{[q]} f \gamma : \Pi_{\mu}^{s m_{+}} A B \gamma \quad \gamma : \Gamma, \widehat{\blacksquare}_{\mu}^{+} \vdash_{[p]} s \gamma : A \gamma}{\gamma : \Gamma \vdash_{[q]} \text{app}_{\mu}^{s m_{+}} f s \gamma : B^{\lceil \lceil \Gamma, s \rceil_{\mu}} \gamma}$$

For $\triangle_{+}$ we define:

$$\Pi_{\triangle}^{s m_{+}} A \text{ (in}_{s m} B) \equiv \text{in}_{s m} \left( \Pi_{\triangle}^{s m} A B \right)$$

$$\Pi_{\triangle}^{s m_{+}} A \text{ (in}_{d m} B) \equiv \text{in}_{d m} \left( \Pi^{d m} A B \right)$$

$$\lambda_{\triangle}^{s m_{+}} \text{ (in}_{s m} t) \equiv \text{in}_{s m} \left( \lambda_{\triangle}^{s m} t \right)$$

$$\lambda_{\triangle}^{s m_{+}} \text{ (in}_{d m} t) \equiv \text{in}_{d m} \left( \lambda^{d m} t \right)$$

$$\text{app}_{\triangle}^{s m_{+}} \text{ (in}_{s m} f) s \equiv \text{in}_{s m} \left( \text{app}_{\triangle}^{s m} f s \right)$$

$$\text{app}_{\triangle}^{s m_{+}} \text{ (in}_{d m} f) s \equiv \text{in}_{d m} \left( \text{app}^{d m} f s \right).$$

The other cases reduce to functions of a modal variable:

$$\Pi_{\diamondsuit}^{s m_{+}} A B \equiv \Pi^{s m_{+}} (\diamondsuit A) B$$

$$\Pi_{\triangle \diamondsuit}^{s m_{+}} A B \equiv \Pi_{\triangle}^{s m_{+}} (\diamondsuit A) B$$

$$\Pi_{\square}^{s m_{+}} A B \equiv \Pi^{s m_{+}} (\square A) B$$

$$\Pi_{\triangle \square}^{s m_{+}} A B \equiv \Pi_{\triangle}^{s m_{+}} (\square A) B$$

The cases of $\lambda$ and app are similar.

◁

73

## 4.4 SEMANTICS OF DTT

Having reviewed the general notion of model for dependent type theory in section 4.1, and constructed our intended model of dTT in sections 4.2 and 4.3, we now describe the general notion of model for dTT. Of course, since our syntax was presented as a Generalised Algebraic Theory, there is an immediate notion of model, namely an algebra for that theory (with algebraic syntax being the initial model). The point is to reformulate this in more familiar category-theoretic terms.

### 4.4.1 Modal structure

The general multimodal type theory MTT was presented algebraically in [GKNB21]. We therefore start from this as a baseline and add structure corresponding to our particular theory.

For a general mode 2-category $\mathcal{M}$, the starting point is a modal context structure, which is a 2-functor $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$, where $\mathcal{M}^{\text{coop}}$ denotes reversal of both 1-cells and 2-cells. The image of a mode $p$ is the category $\mathcal{C}_p$ of contexts and substitutions at that mode, and the image of a morphism $\mu: p \to q$ is the lock functor $\bullet_\mu: \mathcal{C}_q \to \mathcal{C}_p$, which we write postfix, $\Gamma \mapsto \Gamma \cdot \bullet_\mu$. It is a modal natural model if each $\mathcal{C}_p$ is equipped with a morphism $\text{pr}_p: \text{Tm}_p \to \text{Ty}_p$ in its presheaf category such that for any $\mu: p \to q$ the morphism $(\bullet_\mu)^*(\text{pr}_p)$ is representable. (In particular, taking $\mu = 1_p$, we see that each $\mathcal{C}_p$ is an ordinary natural model, hence a CwF.) This notion encapsulates all the rules for building contexts and substitutions from section 2.2 except for those that refer to flatness of contexts.

Now, specializing to our mode 2-category from section 2.1, the rules of section 2.2 say that the flat contexts form a full subcategory of $\mathcal{C}_{sm}$ that contains the image of $\bullet_\circ$. In our algebraic theory we take as primitive the derived rules that a context is flat if and only if it admits a substitution to $(1, \bullet_\circ)$, and in that case the latter substitution is unique. Thus, semantically, $1, \bullet_\circ$ is subterminal and the flat contexts are the slice category $\mathcal{C}_{sm}/1, \bullet_\circ$. Since the unit of the adjunction $\bullet_\circ \dashv \bullet_\circ$ is an identity, $\bullet_\circ$ is fully faithful, and on its image it has $\bullet_\circ$ as an inverse and therefore also a left adjoint. In addition, since flat contexts are fixed points (up to isomorphism) of $\bullet_{\circ\circ}$, when $\Gamma$ is flat there is a bijection $\text{Ty}(\Gamma) \cong \text{Ty}(\Gamma \cdot \bullet_{\circ\circ})$, and so the modal comprehension $(\Gamma, x: \circ\circ A)$ is isomorphic to an ordinary one $(\Gamma, x: A')$. This justifies the special variable rule and key substitution. Thus, the following definition encapsulates the judgmental structure of our modal type theory.

Definition 4.29. A dTT context structure is a modal context structure $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ in the sense of [GKNB21], where $\mathcal{M}$ is as in section 2.1, such that $1, \bullet_\circ$ is subterminal and the slice category $\mathcal{C}_{sm}/1, \bullet_\circ$ is the replete image of the fully faithful functor $\bullet_\circ: \mathcal{C}_{dm} \to \mathcal{C}_{sm}$. A dTT natural model is a dTT context structure that is also a modal natural model.

Next, since our modalities are Fitch-style, their semantics follows [GCK$^+$22]. This requires each functor $\bullet_\mu$ to be a parametric right adjoint and have a dependent right adjoint. However, since each safe $\mu$ is already a right adjoint in $\mathcal{M}$, such $\bullet_\mu$ are also ordinary (hence parametric) right adjoints. And since $\bullet_\circ$ is an equivalence onto a slice category, the inverse of that equivalence is a parametric left adjoint of it. Thus, to justify our Fitch-style rules for modalities, it suffices to assume the following.

Definition 4.30. A dTT modal model is a dTT natural model such that the functors $\bullet_\circ$ and $\bullet_\square$ have dependent right adjoints.

74

Our primary example is, of course, the following.

**Theorem 4.31.** *The simplicial model of sections 4.2 and 4.3 is a dTT natural model.*

*Proof.* Of course, we use the extended simplicial model along with the discrete model. We showed explicitly in section 4.3 that this yields a modal context structure for our $\mathcal{M}$. In the notation of that section, the object $1 \cdot \bullet$ referred to above is $((), \bullet) \equiv \text{in}_{\text{dm}}()$. The definition of the category $\text{sm}_+$ implies immediately that this object is subterminal and its slice category is the replete image (and even the literal image) of $\bullet$. Finally, in section 4.3.5 we verified the rules of $[\text{GCK}^+ 22]$ for $\diamond$ and $\square$, which as shown in *loc. cit.* are equivalent to their being dependent right adjoints of $\bullet$ and $\bullet$.

### 4.4.2 Telescopes

Modal telescopes generalise ordinary telescopes to modal natural models in a straightforward way. Let $\mathcal{M}$ be a 2-category.

**Definition 4.32.** A modal natural model $\mathcal{C} : \mathcal{M}^{\text{coop}} \to \mathcal{Cat}$ has telescopes if it is equipped with:

- For each $p \in \mathcal{M}$, a representable natural transformation $\text{tpr}_p : \text{PSub}_p \to \text{Tel}_p$, whose comprehensions we write as $(\gamma : \Gamma \mid \theta : \Theta \gamma)$.
- For each $p$, a morphism of polynomial functors $()_p : 1_{\mathcal{C}_p} \to \text{P}_{\text{tpr}_p}$.
- For any $\mu : p \to q$, a morphism of polynomial functors $\text{P}_{\text{tpr}_q} \circ \text{P}_{\bullet_{p} \circ \text{P}_{\text{p}}} \to \text{P}_{\text{tpr}_q}$ that we write as $(\theta : \Theta, x :^\mu A \theta)$.
- The rules $(\gamma : \Gamma \mid ()) = \Gamma$ and $(\gamma : \Gamma \mid (\upsilon : \Upsilon \gamma, x :^\mu A \gamma \upsilon)) = ((\gamma : \Gamma \mid \upsilon : \Upsilon), x :^\mu A \gamma \upsilon)$ from section 2.3.1 hold.
- A morphism of polynomial functors $\text{P}_{\text{tpr}} \circ \text{P}_{\text{tpr}} \to \text{P}_{\text{tpr}}$, which we write as $\Upsilon \mid \Phi$. (This says how to concatenate telescopes.)
- The rules $(\gamma : \Gamma \mid (\upsilon : \Upsilon \gamma \mid \phi : \Phi \gamma \upsilon)) = ((\gamma : \Gamma \mid \upsilon : \Upsilon \gamma) \mid \phi : \Phi \gamma \upsilon)$ and $(\upsilon : \Upsilon \mid ()) = \Upsilon$ and $(\upsilon : \Upsilon \mid (\phi : \Phi \upsilon, x :^\mu A \upsilon \phi)) = ((\upsilon : \Upsilon \mid \phi : \Phi \upsilon), x :^\mu A \upsilon \phi)$ from section 2.5.2 hold.

In addition, we say $\mathcal{C}$ has $\Pi$-telescopes if for each $p$ there is a pullback square

$$\begin{array}{ccc} \text{P}_{\text{tpr}_p}(\text{PSub}_p) & \longrightarrow & \text{PSub}_p \\ \downarrow_{\text{P}_{\text{tpr}_p}(\text{tpr}_p)} & \downarrow_{\Pi} & \downarrow_{\text{tpr}_p} \\ \text{P}_{\text{tpr}_p}(\text{Tel}_p) & \xrightarrow[\Pi]{} & \text{Tel}_p, \end{array}$$

such that the computation rules from section 2.5.3 hold.

As in sections 4.1.6 and 4.1.7, we can equip any modal natural model with telescopes and $\Pi$-telescopes, and interpret meta-abstracted types and telescopes automatically, without needing to discuss them explicitly.

75

### 4.4.3 Display and décalage

If $\mathcal{C}$ is a CwF with telescopes and $\Gamma \in \mathcal{C}$, we write $\text{Tel} \parallel \Gamma$ for the category whose objects are telescopes $\Theta \in \text{Tel}(\Gamma)$ and whose morphisms are morphisms $(\Gamma \mid \Theta_1) \to (\Gamma \mid \Theta_2)$ in $\mathcal{C}/\Gamma$. Thus, it is equivalent to the full subcategory of $\mathcal{C}/\Gamma$ on objects of the form $\Gamma \mid \Theta$. We call this the category of telescopes of $\Gamma$. Note that by substitution, it is strictly functorial in $\Gamma$, i.e. we have a functor $\text{Tel} \parallel -: \mathcal{C}^{\text{op}} \to \mathcal{C}at$. Equivalently, therefore, we can regard this as an internal category in the presheaf category $\text{Set}^{\mathcal{C}^{\text{op}}}$.

In fact the category $\text{Tel} \parallel \Gamma$ is actually itself a CwF. Its 'types' in 'context' $\Upsilon \in \text{Tel} \parallel \Gamma$ are meta-abstracted telescopes $\Gamma \vdash \Phi \text{ tel}_{\Gamma/\upsilon: \Upsilon}$. These are equivalent (but not equal) to telescopes in an extended context, i.e. the elements of $\text{Tel}(\Gamma \mid \Upsilon)$. Similarly, meta-abstracted partial substitutions $\Gamma \vdash \phi: \Phi$ are equivalent to terms $\Gamma \mid (\upsilon: \Upsilon) \vdash \phi: \Phi \upsilon$, and semantically to sections of such a projection, $(\Gamma \mid \Upsilon) \to (\Gamma \mid \Upsilon \mid \Phi)$ over $(\Gamma \mid \Upsilon)$. Comprehension is by telescope concatenation. Because $\Gamma \mid () \equiv \Gamma$, the CwF $\text{Tel} \parallel \Gamma$ has the following special property.

**Definition 4.33.** A CwF $\mathcal{C}$ is **strongly democratic** if every context is the comprehension of a unique type in the empty context.

Since all of the structure of $\text{Tel} \parallel \Gamma$ is strictly stable under substitution in $\Gamma$, these categories form an internal CwF in the presheaf category $\text{Set}^{\mathcal{C}^{\text{op}}}$. We call this the *internal telescope model* of $\mathcal{C}$ and denote it $\text{Tel}$. Recalling remark 2.4 and comparing to the discussion of the local theory in [ACKS24], we find that the syntactic structure of décalage from sections 2.4.2 and 2.6.1 can be described precisely as an internal CwF morphism.

**Definition 4.34.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescopes. We say it **has décalage** if it is equipped with a strict morphism of internal strongly democratic CwFs

$$(-)^D: (\widehat{\bullet}_{\triangle\square})^* \text{Tel}_{sm} \to \text{Tel}_{sm}$$

in the category of presheaves over $\mathcal{C}_{sm}$, together with an internal natural transformation evens from $(-)^D$ to $(-)[\widehat{\bullet}_{\triangle\square \leqslant 1_{sm}}]: (\widehat{\bullet}_{\triangle\square})^* \text{Tel}_{sm} \to \text{Tel}_{sm}$.

In particular, therefore, this structure ordinary includes functors $(-)^D: \text{Tel} \parallel (\Gamma \cdot \widehat{\bullet}_{\triangle\square}) \to \text{Tel} \parallel \Gamma$ and natural transformations evens consisting of maps $(\Gamma \mid \Upsilon^D) \to (\Gamma \cdot \widehat{\bullet}_{\triangle\square} \mid \Upsilon)$, all strictly stable under pullback. This, together with the strict preservation of empty contexts by the functor $(-)^D$, is what the rules of section 2.4.2 say. The corresponding action on 'types' (meta-abstracted telescopes) and 'terms' (meta-abstracted partial substitutions) assembles into the rules of section 2.6.1.

We can phrase display in a similar way by defining an auxiliary internal CwF. We start with telescope display (section 2.6). Recall from [Shu15, KL21] that from any CwF $\mathcal{C}$ we can construct a 'Sierpinski' model $\mathcal{C}^2$. Its objects (contexts) are arbitrary morphisms $\gamma_{01}: \Gamma_1 \to \Gamma_0$ in $\mathcal{C}$, but its types are pairs of $A_0 \in \text{Ty}(\Gamma_0)$ and $A_1 \in \text{Ty}(\Gamma_1 \cdot A_0[\gamma_{01}])$. Moreover, there is a strict CwF morphism $(-)_0: \mathcal{C}^2 \to \mathcal{C}$, which preserves all the type-formers, in particular $\Sigma$-types if $\mathcal{C}$ has them. If $\mathcal{C}$ has $\Sigma$-types there is also a functor $(-)_1: \mathcal{C}^2 \to \mathcal{C}$ that sends a type $(A_0, A_1)$ to $\Sigma(A_0[\gamma_{01}], A_1) \in \text{Ty}(\Gamma_1)$, but this only preserves comprehension and $\Sigma$-types up to isomorphism. Thus it is a pseudo CwF morphism in the sense of [CD11, Definition 10], although it preserves substitution and the empty context strictly.

Now let $\mathcal{C}$ be a CwF, and apply this construction internally in the category of presheaves on $\mathcal{C}$ to the internal telescope model $\text{Tel}$. We thus obtain another CwF $\text{Tel}^2$ internal to

76

presheaves, in which the 'contexts' over $\Gamma$ are morphisms of telescopes $\theta_{01}: \Theta_1 \to \Theta_0$ over $\Gamma$, and the 'types' in such a 'context' over $\Gamma$ are pairs of two telescopes $\Upsilon_0 \in \text{Tel}(\Gamma \mid \Theta_0)$ and $\Upsilon_1 \in \text{Tel}(\Gamma \mid \Theta_1 \mid \Upsilon_0[\theta_{01}])$. This is no longer strongly democratic, but as always we have the strict CwF morphism $(-)_0: \text{Tel}^2 \to \text{Tel}$ that preserves $\Sigma$-types (i.e. telescope concatenation), and the pseudo CwF-morphism $(-)_1: \text{Tel}^2 \to \text{Tel}$. Moreover, in this case the latter is actually a strict CwF-morphism, because telescope concatenation is strictly associative.

**Definition 4.35.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{Cat}$ be a dTT natural model with telescopes. We say $\mathcal{C}$ has telescope display if it is equipped with

1. An internal pseudo CwF morphism that preserves substitution, the empty context, and $\Sigma$-types strictly:

$$(-)^d: (\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}^2$$

2. An equality between the composite $(\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \xrightarrow{(-)^d} \text{Tel}_{sm}^2 \xrightarrow{(-)_0} \text{Tel}_{sm}$ and the key transformation $(-)[\mathcal{Q}_{\widehat{\bullet}}^{\Delta\square\in\mathbb{1}_{sm}}]: (\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}$. Since the latter is a strict morphism, that means that so is the former.

3. A strict internal CwF morphism

$$(-)^D: (\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}$$

and an isomorphism of pseudo CwF morphisms between $(-)^D$ and the composite morphism $(\widehat{\bullet}_{\Delta\square})^*\text{Tel}_{sm} \xrightarrow{(-)^d} \text{Tel}_{sm}^2 \xrightarrow{(-)_1} \text{Tel}$, that is the identity on underlying functors.

We have not assumed *a priori* in definition 4.35 that $\mathcal{C}$ has décalage, but it is actually included: the morphism $(-)^D$ is of course the same as in definition 4.34, and the transformation $\text{evens}: \Theta^D \to \Theta$ from definition 4.34 arises in definition 4.35 as the image of $\Theta$ under the underlying functor of $(-)^d$. The additional data in definition 4.35 beyond this is the 1-part of the action of $(-)^d$ (the 0-part is determined by the composition with $(-)_0$ equaling $(-)[\mathcal{Q}_{\widehat{\bullet}}^{\Delta\square\in\mathbb{1}_{sm}}]$) making it a pseudo CwF morphism preserving substitution and $\Sigma$-types strictly, and the isomorphism on 'types' (dependent telescopes) between $(-)^D$ and the composite of $(-)^d$ with $(-)_1$. But since the latter is to be a pseudo CwF transformation (see [CCD17, Appendix B]), and since $(-)^D$ is strict and the underlying functor is the identity this just means that this isomorphism must coincide with the 1-part of the comprehension coherence isomorphism of $(-)^d$ (the 0-part being the identity).

So all that remains is the 1-part of the action of $(-)^d$ on meta-abstracted telescopes, preserving substitution and telescope concatenation, and coherence isomorphisms relating it to comprehension. This gives the rules of section 2.6.4, which have section 2.6.3 as a special case. In particular, since the 1-part of the comprehension of $(\Upsilon, \Upsilon^d)$ in $\text{Tel}^2$ is $(\Upsilon \mid \Upsilon^d)$, the comprehension isomorphisms are the pairing $\langle -, - \rangle$ together with $^{\text{ev}}$ and $^{\text{od}}$.

Finally, we consider display of types, as in section 2.4.3, and its relation to décalage as in sections 2.4.4 and 2.6.2. In some ways this is simpler, since we don't have to worry about rearranging between display and décalage; but in other ways it is more complicated, since we have to take account of extending dependent telescopes by types.

To start with, note that the internal telescope model $\text{Tel}$ of any CwF has a 'sub-model' $\text{Tel}_1$ whose internal category of 'contexts' is the same (telescopes), but whose internal presheaf of 'types' consists of the *length-1 telescopes*, i.e. single types annotated by a modality. Note that unlike $\text{Tel}$, it does not automatically have $\Sigma$-types.

77

**Definition 4.36.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescopes. We say $\mathcal{C}$ has type display if it is equipped with

1. An internal strict CwF morphism:

$$(-)^d: (\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm,1} \to \text{Tel}^2_{sm}$$

2. An equality between the composite $(\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm} \xrightarrow{(-)^d} \text{Tel}^2_{sm} \xrightarrow{(-)_o} \text{Tel}_{sm}$ and the key transformation $(-)[\widehat{\mathbf{\Theta}}_{\triangle\square} \leqslant 1_{sm}]: (\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}$.
3. If a length-1 telescope $A$ is non-modal, then the telescope $A^d$ is a single non-modal type.
4. If a length-1 telescope $A$ is nontrivially modal, then the telescope $A^d$ is empty.

Note that, like definition 4.35, this definition includes décalage. It represents the rules for display from sections 2.4.1 and 2.4.3, and the rules for computing décalage on a telescope extended by a type from section 2.4.4. Of course, with both telescope display and type display we want them to be compatible.

**Definition 4.37.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescope display. We say it has complete display if the restriction of $(-)^d: (\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm} \to \text{Tel}^2_{sm}$ to $(\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm,1}$ is an internal strict CwF morphism such that

- Items 3 and 4 of definition 4.36 hold.
- The rules in section 2.6.2 for computing meta-abstracted décalage in terms of type display hold.
- The rules in section 2.6.5 for computing meta-abstracted telescope display in terms of type display hold.

Finally, we add the compatibility conditions with type-formers:

**Definition 4.38.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescopes, décalage, telescope display, and type display. We say that display respects $\Pi$-types (respectively universes) if the rules in section 2.4.5 hold.

This completes the description of the abstract categorical semantics of the theory of section 2: it is a dTT natural model with telescopes and complete display that respects $\Pi$-types and universes. However, as noted in section 2, when telescopes are lists of types, as they almost always are, much of this structure can be deduced from the rest.

**Theorem 4.39.** Let $\mathcal{C}$ be a dTT natural model, with telescopes defined from types as in theorem 4.7, and with type display defined relative to these telescopes. Then there is a unique way to extend this type display on $\mathcal{C}$ to complete display.

*Proof.* The rules in section 2.6 for computing telescope display and décalage in terms of type display uniquely determine those operations when telescopes are defined as lists of types. $\square$

78

Using this, we can verify that our intended model is indeed a model.

**Theorem 4.40.** *The simplicial model of sections 4.2 and 4.3 has type display, and hence complete display, which respects $\Pi$-types and universes.*

*Proof.* We constructed a display operation for the simplicial model in section 4.2, but it does not yet have exactly the needed form. What we have so far is a 'global' operation that décalages the whole context:

$$\frac{\gamma : \Gamma \vdash_{\text{sm}} A \gamma \text{ type}}{\gamma^+ : \Gamma^D, a : A^{\rho_\Gamma} \gamma^+ \vdash_{\text{sm}} A^d \gamma^+ a \text{ type}}.$$

(Note that this is only defined on the original simplicial model sm, not the extended one sm$_{+}$: indeed, décalage is not even defined on flat contexts.) But the (meta-abstracted version of the) operation we specified in the syntax of section 2 is a 'local' one that only décalages part of the context, keeping the rest of it modally locked away:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon \vdash_{\text{sm}} A \gamma \nu \text{ type}}{\gamma : \Gamma, \nu^+ : \Upsilon^D, a : A^{\mathbf{a}_{\mathbf{s}} \triangleq \mathbb{I}_{\text{sm}}} \gamma (\nu^+)^{\text{ev}} \vdash_{\text{sm}} A^d \gamma \nu^+ a \text{ type}}$$

However, it is straightforward to obtain the latter from the former. In sm$_{+}$, a context of the form $(\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon)$ is not flat, hence lies essentially in sm so that décalage is defined on it. Furthermore, we already observed that $(\Gamma, \mathbf{\Omega}_{\square})^D \equiv (\Gamma, \mathbf{\Omega}_{\square})$ since $\mathbf{\Omega}_{\square}$ lands in constant presheaves. Thus, when $\Upsilon$ is a telescope built out of types, we have

$$(\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon)^D \equiv (\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu^+ : \Upsilon^D)$$

and so the global operation yields as a special case

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon \vdash_{\text{sm}_+} A \gamma \nu \text{ type}}{\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu^+ : \Upsilon^D, a : A^\rho \gamma \nu^+ \vdash_{\text{sm}_+} A^d \gamma \nu^+ a \text{ type}}.$$

Now we simply substitute along $\mathbf{a}_{\mathbf{s}} \triangleq \mathbb{I}_{\text{sm}}$ to obtain the desired local rule. The necessary computation rules for décalage, $\Pi$-types, and universes follow immediately from the rules we proved for the global operation in section 4.2. $\square \triangleleft$

### 4.4.4 Display of $\omega$-limits

Finally, when we have both display and also $\omega$-limits, it is reasonable to require the former to compute on the latter, in the following way. Suppose that $\Gamma, \mathbf{\Omega}_{\Delta\square} \mid \phi : \Phi \vdash_{\text{sm}} \tilde{\Upsilon} \phi \text{ stel}^\infty$, and we want to compute $\Gamma, \phi : \Phi^D, u : \lim \tilde{\Upsilon} \vdash \lim \tilde{\Upsilon}^d \phi u$. Then by definition, we have

$$\begin{array}{l} \Gamma, \mathbf{\Omega}_{\Delta\square} \vdash_{\text{sm}} \Upsilon^{\partial n} \text{ tel} / \phi : \Phi \\ \Gamma, \mathbf{\Omega}_{\Delta\square} \vdash_{\text{sm}} \Upsilon^n \text{ type} / \phi : \Phi, \partial \nu : \Upsilon^{\partial n} \phi \end{array}$$

and therefore

$$\begin{array}{l} \Gamma \vdash_{\text{sm}} (\Upsilon^{\partial n})^d \text{ tel}_\ell / \phi : \Phi^D, \partial \nu : \Upsilon^{\partial n} \phi^{\text{ev}} \\ \Gamma \vdash_{\text{sm}} (\Upsilon^n)^d \text{ type}_\ell / \phi : \Phi^D, \partial \nu : (\Upsilon^{\partial n})^D \phi, \nu : \Upsilon^n \phi^{\text{ev}} \partial \nu^{\text{ev}} \end{array}$$

79

Weakening and substituting to the needed context $\Gamma$, $\phi : \Phi^D$, $u : \lim \bar{Y}$, we have

$$\Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} (Y^{\partial n})^d \phi (\text{res}^{\partial n} u) \text{ tel}$$

$$\Gamma, \phi : \Phi^D, u : \lim \bar{Y}, \partial v : (Y^{\partial n})^d \phi (\text{res}^{\partial n} u) \vdash_{sm} (Y^n)^d \phi \langle \text{res}^{\partial n} u, \partial v \rangle (\text{res}^n u) \text{ type}$$

such that

$$\begin{aligned} (Y^{\partial(n+1)})^d \phi (\text{res}^{\partial(n+1)} u) &\equiv \left( \partial v : \bar{Y}^{\partial n}, v : \bar{Y}^n \partial v \right)^d \phi [\text{res}^{\partial n} u, \text{res}^n u] \\ &\equiv \left( \partial v : (\bar{Y}^{\partial n})^d \phi (\text{res}^{\partial n} u), v : (\bar{Y}^n)^d \phi \langle \text{res}^{\partial n} u, \partial v \rangle (\text{res}^n u) \right). \end{aligned}$$

Thus, these data form another infinite telescope, which we denote

$$\begin{aligned} \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} \bar{Y}^d \phi u \text{ stel}^\infty \\ (Y^d)^{\partial n} \phi u &\equiv (Y^{\partial n})^d \phi (\text{res}^{\partial n} u) \\ (Y^d)^n \phi u \partial v &\equiv (Y^n)^d \phi \langle \text{res}^{\partial n} u, \partial v \rangle (\text{res}^n u) \end{aligned}$$

We say that display respects $\omega$-limits if

$$\begin{aligned} \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} \lim \bar{Y}^d \phi u &\equiv \lim(\bar{Y}^d \phi u) \\ \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} (\text{res}^{\partial n})^d \phi u &\equiv \text{res}^{\partial n} \phi u \\ \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} (\text{res}^n)^d \phi u &\equiv \text{res}^n \phi u. \end{aligned}$$

where in the last two equations, the left-hand side is a restriction relative to $\bar{Y}$, and on the right-hand side it is relative to $\bar{Y}^d$.

**Theorem 4.41.** *Display respects $\omega$-limits in the simplicial model.*

*Proof.* This holds essentially by construction of $\omega$-limits therein, plus passing across the translation between different forms of display from theorem 4.40. $\square \triangleleft$

### 4.5 SEMANTICS OF SEMI-SIMPLICIAL TYPES

Finally, we construct semantics for the displayed coinductive types of section 3.3, in particular including SST. As with most kinds of coinductive definitions, they are terminal coalgebras of some sort, but in this case they are terminal coalgebras for a *copointed* endofunctor. We will construct such a terminal coalgebra by a sequential limit construction, assuming that the base (discrete) model admits such limits.

#### 4.5.1 Terminal coalgebras for copointed endofunctors

**Definition 4.42.** A **copointed endofunctor** of a category $\mathcal{C}$ is a functor $F : \mathcal{C} \to \mathcal{C}$ together with a natural transformation $\epsilon : F \to 1_{\mathcal{C}}$. A **coalgebra** for a copointed endofunctor is an object $X$ with a morphism $x : X \to FX$ such that the composite $X \xrightarrow{x} FX \xrightarrow{\epsilon_x} X$ is the identity. A **terminal coalgebra** is a terminal object of the category of coalgebras.

80

Note that a coalgebra for a copointed endofunctor is not just a coalgebra for its underlying ordinary endofunctor, but satisfies the equation $\epsilon_X \circ x = 1_X$.

As usual, we can obtain terminal coalgebras by a sequential limit construction, when such limits exist. However, in the copointed case it does not suffice to simply consider the limit of the tower $\cdots \to F^1\mathbb{1} \to F^2\mathbb{1} \to F\mathbb{1} \to \mathbb{1}$; we have to incorporate the transformation $\epsilon$ in some way. The classical way to do this (e.g. the dual of [Kel80]) is to take equalisers at each step. However, equalisers are difficult to understand homotopy-theoretically, so we replace them by a pullback. The following definition is a partial dual of [Shu19, Definition 8.6].

Definition 4.43. Given a natural transformation $\epsilon : F \to G$ and a morphism $f : X \to Y$ in the domain of $F$ and $G$, we write $\widehat{\hom}(\epsilon, f)$ for the gap map in the following pullback, assuming that the pullback exists.

![img-5.jpeg](img-5.jpeg)

If the domain and codomain of $F$ and $G$ have a notion of 'fibration', we say that $\epsilon$ is a Quillen pre-fibration if whenever $f$ is a fibration, so is $\widehat{\hom}(\epsilon, f)$.

For example, we have:

Lemma 4.44. In a category of telescopes, consider the fibrations to be the morphisms isomorphic to a dependent projection of some telescope. Then the transformation evens : $(-)^D \to (-)[\mathcal{Q}^{\Delta\square\leqslant 1_{\text{sim}}}]$ from definition 4.34 is a Quillen pre-fibration.

Proof. Given a dependent projection $(\Theta \mid \Upsilon) \to \Theta$ in $\text{Tel} / (\Gamma \widehat{\mathbf{Q}}_{\Delta\square})$, the gap map is isomorphic to the dependent projection of $\Upsilon^d$:

$$(\Theta^D \mid \Upsilon[\mathcal{Q}^{\Delta\square\leqslant 1}] \mid \Upsilon^d) \to (\Theta^D \mid \Upsilon[\mathcal{Q}^{\Delta\square\leqslant 1}]).$$

Theorem 4.45. Suppose $\mathcal{C}$ is a category with a terminal object and a notion of fibration that is stable under pullback, and that $F$ is a copointed endofunctor of $\mathcal{C}$ such that $\epsilon : F \to 1_{\mathcal{C}}$ is a Quillen pre-fibration. Suppose also that $\mathcal{C}$ has limits of inverse $\omega$-sequences of fibrations, and that $F$ preserves these limits. Then there is a terminal $F$-coalgebra.

Proof. We define inductively a sequence of objects $X_n$ with morphisms $g_{n+1} : X_{n+1} \to X_n$, of which the terminal $F$-coalgebra will be the limit $X_\infty$. We can think of each $X_n$ as an approximation to the terminal coalgebra, with $X_{n+1}$ extending $X_n$ with additional data making it a better approximation; thus each $g_n$ should be a fibration. Since $X_{n+1}$ will be constructed inductively from $X_n$, we can expect it to contain all the data that $X_\infty$ should contain that relates to $X_n$, and thus we can expect to have a map $x_{n+1} : X_{n+1} \to FX_n$ (but not yet to $FX_{n+1}$). To achieve the copointedness condition in the limit for these data, we

81

should demand $\epsilon_{X_n} \circ x_{n+1} = g_{n+1}$. And to ensure that the successive approximations are consistent with each other, we should ask that $Fg_n \circ x_{n+1} = x_n \circ g_{n+1}$.

In sum, therefore, we will inductively construct a sequence of objects $X_n$, with fibrations $g_{n+1}: X_{n+1} \to X_n$ and morphisms $x_{n+1}: X_{n+1} \to FX_n$, such that $\epsilon_{X_n} \circ x_{n+1} = g_{n+1}$ and $Fg_n \circ x_{n+1} = x_n \circ g_{n+1}$.

To start with, let $X_0 = \mathbb{1}$, the terminal object, and let $X_1 = FX_0 = F\mathbb{1}$, with $x_1$ the identity. Now, assume the data constructed up to level $n > 0$. The idea is to define $X_{n+1}$ to be the *universal* object equipped with $g_{n+1}$ and $x_{n+1}$ satisfying the desired equations. This means it is a limit of some diagram. The usual way to write that diagram is as the equalizer of the two maps

![img-6.jpeg](img-6.jpeg)

but this does not make it evident that $g_{n+1}$ is a fibration. Instead, we can express this same limit as the following pullback:

$$
\begin{array}{c}
X_{n+1} \xrightarrow{x_{n+1}} FX_n \\
g_{n+1} \downarrow \quad \downarrow \quad \downarrow \\
X_n \xrightarrow{(1,x_n)} X_n \times_{X_{n-1}} FX_{n-1}.
\end{array}
\tag{4.46}
$$

The commutativity of this square says that $Fg_n \circ x_{n+1} = x_n \circ g_{n+1}$ and $\epsilon_{X_n} \circ x_{n+1} = g_{n+1}$. And by assumption, $\widehat{\hom}(\epsilon, g_n)$ is a fibration, hence so is its pullback $g_{n+1}$.

Now let $X_\infty$ be the limit of the $\omega$-sequence of fibrations

$$
X_\infty \cdots \xrightarrow{g_{n+1}} X_n \xrightarrow{g_n} \cdots \xrightarrow{g_2} X_1 \xrightarrow{g_1} X_0 = \mathbb{1}.
$$

Since $F$ preserves limits of inverse $\omega$-sequences, $FX_\infty$ is the limit of the corresponding sequence

$$
FX_\infty \cdots \xrightarrow{Fg_{n+1}} FX_n \xrightarrow{Fg_n} \cdots \xrightarrow{Fg_2} FX_1 \xrightarrow{Fg_1} FX_0 = \mathbb{1}.
$$

The morphisms $x_n$ and $\epsilon_{X_n}$ form fence diagrams:

![img-7.jpeg](img-7.jpeg)

composed of the parallelograms $Fg_n \circ x_{n+1} = x_n \circ g_{n+1}$ from our construction, and naturality squares $\epsilon_{X_n} \circ Fg_{n+1} = g_{n+1} \circ \epsilon_{X_{n+1}}$. The former induces a map of limits $x_\infty: X_\infty \to FX_\infty$, while by naturality the latter induces $\epsilon_{X_\infty}$. The universal property of limits implies that

82

$\epsilon_{X_{\infty}} \circ x_{\infty}$ is induced by the composite fence, and since $g_{n+1} = \epsilon_{X_n} \circ x_{n+1}$ this is

$$\begin{array}{c} X_{\infty} \longrightarrow \cdots \longrightarrow X_3 \xrightarrow{g_3} X_2 \xrightarrow{g_2} X_1 \xrightarrow{g_1} X_0 \\ 1_{X_{\infty}} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad X_{\infty} \longrightarrow \cdots \longrightarrow X_3 \xrightarrow{g_3} X_2 \xrightarrow{g_2} X_1 \xrightarrow{g_1} X_0 \end{array}$$

which induces the identity $1_{X_{\infty}}$. Thus, $X_{\infty}$ is an F-coalgebra.

Now suppose $y : Y \rightarrow FY$ is another F-coalgebra. We construct inductively maps $h_n : Y \rightarrow X_n$ such that $x_{n+1} \circ h_{n+1} = Fh_n \circ y$ and $g_{n+1} \circ h_{n+1} = h_n$. We start with $h_0 : Y \rightarrow X_0 = \mathbb{1}$ the unique morphism, and $h_1 : Y \rightarrow X_1 = FX_0$ the composite $Y \xrightarrow{y} FY \xrightarrow{Fh_0} FX_0$. Then we induce $h_{n+1}$ by the universal property of the pullback defining $X_{n+1}$:

$$\begin{array}{c} Y \xrightarrow{h_{n+1}} X_{n+1} \xrightarrow{x_{n+1}} FX_n \\ h_n \downarrow g_{n+1} \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \downarrow \end{array}$$

This is valid because using the inductive assumptions about $h_n$ and $h_{n-1}$, we have

$$\begin{aligned} \epsilon_{X_n} \circ Fh_n \circ y &= h_n \circ \epsilon_Y \circ y \\ &= h_n \end{aligned}$$

and

$$\begin{aligned} Fg_n \circ Fh_n \circ y &= F(g_n \circ h_n) \circ y \\ &= Fh_{n-1} \circ y \\ &= x_n \circ h_n, \end{aligned}$$

and the two triangles relating to $h_{n+1}$ show that it has the necessary properties.

Now, the equations $g_{n+1} \circ h_{n+1} = h_n$ imply there is an induced map $h_{\infty} : Y \rightarrow X_{\infty}$, such that $x_{\infty} \circ h_{\infty}$ is induced by the composites $x_{n+1} \circ h_{n+1}$. But $x_{n+1} \circ h_{n+1} = Fh_n \circ y$, and the morphisms $Fh_n$ induce the limit map $Fh_{\infty}$. Thus, $h_{\infty}$ is an F-coalgebra morphism.

Finally, suppose $k : Y \rightarrow X_{\infty}$ is any F-coalgebra morphism, so we have $x_{\infty} \circ k = Fk \circ y$. Then $k$ is uniquely determined by the maps $k_n : Y \rightarrow X_n$, and we have $x_{n+1} \circ k_{n+1} = Fk_n \circ y$. But this equation implies by induction that $k_n = h_n$ for all $n$, hence $k = h_{\infty}$. $\square \triangleleft$

### 4.5.2 Displayed coinductive types

Let $\mathcal{C}$ be a dTT natural model with levels, telescopes, décalage, telescope display, type display respecting $\Pi$-types and universes, and $\Pi$-telescopes. We will apply theorem 4.45 in $\text{Tel} \parallel (\Gamma \cdot \widehat{\bullet}_{\Delta \square} \mid \Phi)$, in which the fibrations are the morphisms isomorphic to the dependent projection from some telescope,

$$(\Gamma \cdot \widehat{\bullet}_{\Delta \square} \mid \Phi \mid \Theta \mid Y) \rightarrow (\Gamma \cdot \widehat{\bullet}_{\Delta \square} \mid \Phi \mid \Theta).$$

83

In the presence of levels, the objects of $\mathsf{Tel} \mathbin{//} (\Gamma \cdot \widehat{\mathbf{B}}_{\triangle \square} \mid \Phi)$ are telescopes at any level.

Suppose given the input data for a displayed coinductive type, consisting of

$$\Gamma \in \mathcal {C} \quad \Phi \in \operatorname {T e l} _ {\ell_ {0}} (\Gamma . \widehat {\mathbf {B}} _ {\triangle \square}) \quad A \in \operatorname {T y} _ {\ell_ {1}} (\Gamma . \widehat {\mathbf {B}} _ {\triangle \square} | \Phi) \quad \mathcal {B} \in \operatorname {T e l} _ {\ell_ {2}} (\Gamma . \widehat {\mathbf {B}} _ {\triangle \square} | \Phi . A)$$

$$\sigma \in \mathsf {P S u b} _ {\ell_ {0}} \left(\left(\Gamma . \widehat {\mathbf {B}} _ {\triangle \square} \mid \Phi . A \mid \mathcal {B}\right), \Phi^ {d}\right).$$

Categorically, this yields the data of a sort of 'display polynomial', where we indicate fibrations with $\rightarrow$:

![img-8.jpeg](img-8.jpeg)

The left vertical map is a fibration because it is isomorphic to the dependent projection

$$(\Gamma . \widehat {\mathbf {B}} _ {\triangle \square} | \Phi | \Phi^ {d}) \rightarrow (\Gamma . \widehat {\mathbf {B}} _ {\triangle \square} | \Phi).$$

Since everything is in the category of telescopes over $\Gamma \cdot \widehat{\mathbf{B}}_{\triangle \square}$, we will omit it from the notation for conciseness, so that the above display polynomial becomes

![img-9.jpeg](img-9.jpeg)

This display polynomial then defines a copointed endofunctor of $\mathsf{Tel} \mathbin{//} (\Gamma . \widehat{\mathbf{B}}_{\triangle \square} \mid \Phi)$ as follows:

$$\frac {\Gamma , \widehat {\mathbf {B}} _ {\triangle \square} \vdash_ {\mathrm {s m}} X \operatorname {t e l} _ {\ell / \phi : \Phi}}{\Gamma , \widehat {\mathbf {B}} _ {\triangle \square} \vdash_ {\mathrm {s m}} F X \operatorname {t e l} _ {\ell \sqcup \ell_ {1} \sqcup \ell_ {2} / \phi : \Phi , x : X \phi}}$$

$$\mathsf {F X} \equiv \left(\left(a: A \phi , x ^ {\prime}: (b: \mathcal {B} \phi a) \rightarrow X ^ {d} (\phi , \sigma a b) x\right)\right) _ {\phi : \Phi , x: X \phi}$$

Here the $\rightarrow$ denotes a $\Pi$-telescope (section 2.5.3), and $X^d$ denotes meta-abstracted telescope display (section 2.6.4); this is why we wanted those in the syntax. Note that FX is meta-abstracted over $\Phi$ extended by $X$, so it lies in $\mathsf{Tel} \mathbin{//} (\Gamma . \widehat{\mathbf{B}}_{\triangle \square} \mid \Phi \mid X)$ rather than $\mathsf{Tel} \mathbin{//} (\Gamma . \widehat{\mathbf{B}}_{\triangle \square} \mid \Phi)$. The actual endofunctor of $\mathsf{Tel} \mathbin{//} (\Gamma . \widehat{\mathbf{B}}_{\triangle \square} \mid \Phi)$ is thus

$$\overline {{\mathsf {F}}} (X) \equiv (X \mid \mathsf {F X}).$$

The weakening projection $(X \mid \mathsf{FX}) \to X$ is then a copointing $\epsilon : \overline{\mathsf{F}} \to 1$ of this endofunctor, which is evidently a fibration. More than this, we have:

Lemma 4.47. The copointing $\epsilon : \overline{\mathsf{F}} \to 1$ is a Quillen pre-fibration.

Proof. Suppose given a fibration over $X \in \mathsf{Tel}_{\ell_0}(\Gamma, \widehat{\mathbf{B}}_{\triangle \square})$, meaning a dependent telescope

$$\Gamma , \widehat {\mathbf {B}} _ {\triangle \square} \vdash_ {\mathrm {s m}} Y \operatorname {t e l} _ {\ell_ {1}} / _ {\phi : \Phi , x: X \phi}.$$

84

Then we have

$$\Gamma, \mathbf{\Theta}_{\triangle\square} \vdash_{sm} \left( \left( x : X \phi \mid y : Y \phi x \right) \right)_{\phi : \Phi} \text{tel}_{\ell_0 \sqcup \ell_1} / \phi : \Phi$$

which we write as XY for conciseness. Then by definition, we have

$$F(XY) \equiv \left( \left( a : A \phi, z' : (b : \mathcal{B} \phi a) \rightarrow (XY)^d \langle \phi, \sigma a b \rangle [x \mid y] \right) \right)_{\phi : \Phi, x : X \phi, y : Y \phi x}.$$

To simplify this, note that by the rules in section 2.6.4

$$(XY)^d \langle \phi, \sigma a b \rangle [x \mid y] \equiv \left( x' : X^d \langle \phi, \sigma a b \rangle x \mid Y^d \langle \phi, \sigma a b \rangle \langle x, x' \rangle y \right)$$

and therefore by the rules in section 2.5.3

$$\begin{array}{l} (b : \mathcal{B} \phi a) \rightarrow (XY)^d \langle \phi, \sigma a b \rangle [x \mid y] \\ \equiv \left( \delta : (b : \mathcal{B} \phi a) \rightarrow X^d \langle \phi, \sigma a b \rangle x \mid \epsilon : (b : \mathcal{B} \phi a) \rightarrow Y^d \langle \phi, \sigma a b \rangle \langle x, \delta b \rangle y \right). \end{array}$$

Now when $\delta$ is paired with $a : A \phi$, it yields FX. Thus, the relevant gap map

![img-10.jpeg](img-10.jpeg)

is the dependent projection from the telescope

$$\begin{array}{l} \left( \left( (b : \mathcal{B} \phi a) \rightarrow Y^d \langle \phi, \sigma a b \rangle \langle x, \delta b \rangle y \right) \right)_{\phi : \Phi, x : X \phi, y : Y \phi x, a : A \phi,} \\ \delta : (b : \mathcal{B} \phi a) \rightarrow X^d \langle \phi, \sigma a b \rangle x \tag{4.48} \end{array}$$

and thus a fibration.

Lemma 4.49. The endofunctor $\overline{F}$ preserves inverse limits of $\omega$-sequences of fibrations.

Sketch of proof. This follows from the $\eta$-rules for inverse limits, together with the fact that display also preserves inverse limits.

Therefore, by theorem 4.45, there exists a terminal $\overline{F}$-coalgebra. Moreover, since we have assumed that inverse limits are representable by single types, this coalgebra is a type and not just a telescope. This type is our candidate for the displayed coinductive type; we can unpack its definition as follows. The construction produces a tower of fibrations $g_n$, which is to say a sequence of finite telescopes dependent on the previous ones:

$$\begin{array}{l} \phi : \Phi \vdash_{sm} X^{\partial n} \phi \text{tel}_\ell \\ \phi : \Phi, \partial x : X^{\partial n} \phi \vdash_{sm} X^n \phi \partial x \text{tel}_\ell \\ \phi : \Phi \vdash_{sm} X^{\partial 0} \phi \equiv () \\ \phi : \Phi \vdash_{sm} X^{\partial (n+1)} \phi \equiv (\partial x : X^{\partial n} \phi, x : X^n \phi \partial x) \end{array}$$

85

We choose the level of the empty telescope $X^{\partial 0}$ to be $\ell \equiv \ell_0 \sqcup \ell_1$; the explicit description given below then implies that all the other telescopes $X^{\partial n}$ and $X^n$ are also at level $\ell$.

The object $X_{n+1}$ in section 4.5.1 corresponds to the telescope

$$(\phi : \Phi, \partial x : X^{\partial(n+1)} \phi) = (\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x).$$

Each morphism $x_{n+1} : X_{n+1} \to \overline{F}X_n$ such that $\epsilon \circ x_{n+1} = g_{n+1}$ then corresponds to a term

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x \vdash_{sm} \xi_n : F(X^{\partial n}) \phi \partial x.$$

By definition of $F$, $\xi_n$ is equivalent to two terms

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x \vdash_{sm} h_n \phi \partial x \, x : A \phi$$

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, b : \mathcal{B} \phi (h_n \phi \partial x) \vdash_{sm} t_n \phi \partial x \, x \, b :$$

$$(X^{\partial n})^d \langle \phi, \sigma (h_n \phi \partial x) b \rangle \partial x.$$

The equation $Fg_{n+1} \circ x_{n+2} = x_{n+1} \circ g_{n+2}$ means that

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, x' : X^{n+1} \phi [\partial x, x] \vdash_{sm} h_{n+1} \phi [\partial x, x] x' \equiv h_n \phi \partial x \, x$$

and

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, x' : X^{n+1} \phi [\partial x, x], b : \mathcal{B} \phi (h_n \phi \partial x)$$

$$\vdash_{sm} t_{n+1} \phi [\partial x, x] x' \, b \equiv [t_n \phi \partial x \, x \, b, s_n \phi \partial x \, x \, x' \, b]$$

for some term

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, x' : X^{n+1} \phi [\partial x, x], b : \mathcal{B} \phi (h_n \phi \partial x)$$

$$\vdash_{sm} s_n \phi \partial x \, x \, x' \, b : (X^n)^d \langle \phi, \sigma (h_n \phi \partial x) b \rangle \langle \partial x, t_n \phi \partial x \, x \, b \rangle x$$

$$\equiv (X^n)^d \langle \phi, \sigma (h_{n-1} \phi \partial x) b \rangle \langle \partial x, t_n \phi \partial x \, x \, b \rangle x$$

Now inspecting the actual construction, we start with $X_0 = X^{\partial 0} = \langle \rangle$, the empty telescope, and $X^0 = F(X^{\partial 0}) = F(\cdot) = A$. It is easy to see by induction that the functions $h_n$ then all just project to $X^0$. For the rest, combining eqs. (4.46) and (4.48), we find that $X^{n+1}$ is defined by

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x \vdash_{sm}$$

$$X^{n+1} \phi [\partial x, x] \equiv$$

$$(b : \mathcal{B} \phi (h_{n-1} \phi \partial x)) \to (X^n)^d \langle \phi, \sigma (h_{n-1} \phi \partial x) b \rangle \langle \partial x, t_n \phi \partial x \, x \, b \rangle x$$

and we have tautologically

$$s_n \phi \partial x \, x \, x' \, b \equiv x' \, b.$$

In particular, by induction we find that in fact each $X^n$, though by construction a telescope, is actually just a single type for all $n \geqslant 0$. Therefore, the tower $(X^{\partial n}, X^n)$ is precisely an infinite telescope as defined in section 4.1.8, which we denote

$$\bar{X} = (X^{\partial n}, X^n).$$

Our displayed coinductive type is therefore precisely the limit of this infinite telescope as in section 4.1.9:

$$\text{dCoind} [\Phi, A, \mathcal{B}, \sigma] \phi \equiv \lim \left( \bar{X} \phi \right).$$

86

Example 4.50. Recall that for semi-simplicial types SST, we have $\Phi \equiv ()$, with $A \equiv \text{Type}$ and $\mathcal{B} a \equiv \{x : \text{El } a\}$. Therefore, in this case we have

$$X^0 \equiv \text{Type}$$

$$X^0 A_0 \equiv \text{El } A_0 \to \text{Type}^d A_0$$

$$\equiv \text{El } A_0 \to \text{El } A_0 \to \text{Type}$$

$$X^2 A_0 A_1 \equiv (a_1 : A_0) \to \{(A \to A \to \text{Type})\}_{A : \text{Type}^d} A_0 (A_1 a_1) A_1$$

$$\equiv (a_1 : A_0) \to \{((x : A)(x' : A' x)(y : A)(y' : A' y) \to \text{Type}^d (A'' x y))\}$$

$$A : \text{Type}, A' : \text{Type}^d A, A'' : A \to A \to \text{Type} A_0 (A_1 a_1) A_1$$

$$\equiv (a_{01} : A_0)(a_{10} : A_0)(a_{01} : A_1 a_{01} a_{10})$$

$$(a_{10} : A_0)(a_{01} : A_1 a_{01} a_{10})(a_{10} : A_1 a_{10} a_{10}) \to \text{Type}$$

This suggests that in general, $X^{\partial n}$ will be the type of $(n-1)$-truncated semi-simplicial types, while $X^n A$ will be the type of ways to extend such an $A$ to an $n$-truncated one, i.e. the types of indexed families of $n$-simplices. We will prove this formally in section 4.5.5.

It remains to show that this construction of dCoind has the structure stipulated in section 3.3. To this end, we first unpack what it means for a type $C \in \text{Ty}(\Gamma \bullet_{\triangle\square} | \Phi)$ to be an $\overline{\text{F}}$-coalgebra. This means it is equipped with a section of the projection $\overline{\text{F}}(C) = (C | \text{F}(C)) \to C$, which syntactically is to say a partial substitution

$$\Gamma, \bullet_{\triangle\square} | (\phi : \Phi), x : C \vdash_{sm} c : (a : A \phi, x' : (b : \mathcal{B} \phi a) \to X^d \langle \phi, \sigma a b \rangle x).$$

But this is equivalent to giving its components, which we abstract over $x$ to emphasise their dependence on it:

$$\Gamma, \bullet_{\triangle\square} | (\phi : \Phi) \vdash_{sm} h : C \to A \phi$$

$$\Gamma, \bullet_{\triangle\square} | (\phi : \Phi) \vdash_{sm} t : (x : C)(b : \mathcal{B} \phi (h x)) \to X^d \langle \phi, \sigma (h x) b \rangle x$$

This is evidently precisely the structure of head and tail from section 3.3. Thus, our terminal $\overline{\text{F}}$-coalgebra admits these destructors.

Furthermore, to give some other telescope $\Theta \in \text{Tel}(\Gamma \bullet_{\triangle\square} | \Phi)$ an $\overline{\text{F}}$-coalgebra structure is equivalent to equipping $\Upsilon \equiv (\Phi | \Theta)$ with the premises of the corecursor, where the indices-assigning map $\zeta : (\Phi | \Theta) \to \Phi$ is the dependent projection. Thus, terminality of our terminal $\overline{\text{F}}$-coalgebra implies that it admits the corecursor for telescopes $\Upsilon$ of this form.

In the models arising from type-theoretic model toposes, the underlying category is actually locally cartesian closed, and thus the functor $\overline{\text{F}}$ can be extended from $\text{Tel} \not\parallel (\Gamma \bullet_{\triangle\square} \Phi)$ to the larger slice category $(\text{Tel} \not\parallel (\Gamma \bullet_{\triangle\square})) / \Phi$, with the same terminal coalgebra in this larger category. This directly implies the full corecursion principle, since $\zeta$ in that rule equips $\Upsilon$ with the structure of an object of this slice.

In fact, the same is true for arbitrary models: the premises of the corecursor equip $\Upsilon$ with 'enough of an $\overline{\text{F}}$-coalgebra structure' to deduce the existence of a unique compatible map to the terminal coalgebra. In the next section we prove this in a more general abstract context.

### 4.5.3 Terminal generalised coalgebras

Let $\text{F}$ be a copointed endofunctor of a category $\mathcal{C}$ as in section 4.5.1, where $\mathcal{C}$ is a full subcategory of some larger category $\text{E}$.

87

**Definition 4.51.** An object $Y \in E$ is a **generalised F-coalgebra** if it is equipped with:

- For any $X \in \mathcal{C}$ and morphism $h: Y \to X$, a specified morphism $\overline{h}: Y \to FX$, such that
- $\epsilon_X \circ \overline{h} = h$.
- For any $g: X \to Z$ in $\mathcal{C}$, we have $Fg \circ \overline{h} = \overline{g \circ h}$.

In more abstract language, we can say that $F$ induces a copointed endofunctor $F^*$ of the functor category $\mathsf{Set}^{\mathcal{C}}$ by precomposition, and $Y$ is a generalised F-coalgebra if the functor $E(Y, -): \mathcal{C} \to \mathsf{Set}$ is an $F^*$-coalgebra. The following observation is then a consequence of the Yoneda lemma, but we write it out explicitly.

**Lemma 4.52.** If $Y \in \mathcal{C}$, then generalised F-coalgebra structures on $Y$ are bijective to ordinary F-coalgebra structures.

*Proof.* In one direction, if $y: Y \to FY$ is an F-coalgebra structure, then given $h: Y \to X$ define $\overline{h} = Fh \circ y$. Then we have

$$\epsilon_X \circ \overline{h} = \epsilon_X \circ Fh \circ y = h \circ \epsilon_Y \circ y = h$$

and

$$Fg \circ \overline{h} = Fg \circ Fh \circ y = F(g \circ h) \circ y = \overline{g \circ h}.$$

In the other direction, given a generalised F-coalgebra structure, let $y = \overline{1_Y}: Y \to FY$. Then $\epsilon_Y \circ y = 1_Y$ by assumption, so $y$ is an F-coalgebra structure. Moreover, the other axiom implies that for any $g: Y \to Z$ we have $\overline{g} = \overline{g \circ 1_Y} = Fg \circ \overline{1_Y} = Fg \circ y$. Thus one round-trip composite is the identity. The other round-trip composite simply sends $y: Y \to FY$ to $\overline{1_Y} = F(1_Y) \circ y = 1_{FY} \circ y = y$.

Of course, a **morphism of generalised F-coalgebras** is a morphism $f: Y \to Z$ such that for any $h: Z \to X \in \mathcal{C}$ we have $\overline{h} \circ f = \overline{h \circ f}$.

**Lemma 4.53.** If $Y \in E$ is a generalised F-coalgebra and $x: X \to FX$ is an F-coalgebra in $\mathcal{C}$, then a morphism $f: Y \to X$ is a generalised F-coalgebra morphism if and only if $\overline{f} = x \circ f$.

*Proof.* If it is a generalised F-coalgebra map, then taking $h = 1_X$ in $\overline{h} \circ f = \overline{h \circ f}$ we get $x \circ f = \overline{f}$. On the other hand, if $x \circ f = \overline{f}$ then for any $h: X \to X'$ in $\mathcal{C}$ we have $\overline{h} \circ f = x' \circ h \circ f = Fh \circ x \circ f = Fh \circ \overline{f} = \overline{h \circ f}$, as desired.

**Theorem 4.54.** *Let $\mathcal{C}$ and $F$ be as in theorem 4.45, and let $\mathcal{C}$ be a full subcategory of $E$ such that the embedding preserves the terminal object and the inverse limits of $\omega$-sequences of fibrations. Then the terminal F-coalgebra constructed in theorem 4.45 is also a terminal generalised F-coalgebra.*

*Proof.* Indeed, the proof of terminality in theorem 4.45 really only uses the generalised F-coalgebra structure, which we can see clearly by repeating it in that language. Let $Y \in E$ be a generalised F-coalgebra. We construct inductively maps $h_n: Y \to X_n$ such that $x_{n+1} \circ h_{n+1} = \overline{h_n}$ and $g_{n+1} \circ h_{n+1} = h_n$. We start with $h_0: Y \to X_0 = \mathbb{1}$ the unique

88

morphism (since $1 \in \mathcal{C}$ is also terminal in E), and $h_1 = \overline{h_0} : Y \to X_1 = FX_0$. Then we induce $h_{n+1}$ by the universal property of the pullback defining $X_{n+1}$:

![img-11.jpeg](img-11.jpeg)

This is valid because using the inductive assumptions about $h_n$ and $h_{n-1}$ and the properties of generalised coalgebras, we have

$$\epsilon_{X_n} \circ \overline{h_n} = h_n$$

and

$$\begin{array}{l} Fg_n \circ \overline{h_n} = \overline{g_n \circ h_n} \\ = \overline{h_{n-1}} \\ = x_n \circ h_n, \end{array}$$

and the two triangles relating to $h_{n+1}$ show that it has the necessary properties.

Now, the equations $g_{n+1} \circ h_{n+1} = h_n$ imply there is an induced map $h_\infty : Y \to X_\infty$, such that $x_\infty \circ h_\infty$ is induced by the composites $x_{n+1} \circ h_{n+1}$. But $x_{n+1} \circ h_{n+1} = \overline{h_n}$, and the morphisms $Fh_n$ induce the limit map $Fh_\infty$, so $x_\infty \circ h_\infty = \overline{h_\infty}$. Thus, by lemma 4.53, $h_\infty$ is an F-coalgebra morphism.

Finally, suppose $k : Y \to X_\infty$ is any F-coalgebra morphism, so we have $x_\infty \circ k = \overline{k}$. Then $k$ is uniquely determined by the maps $k_n : Y \to X_n$, and we have $x_{n+1} \circ k_{n+1} = \overline{k_n}$. But this equation implies by induction that $k_n = h_n$ for all $n$, hence $k = h_\infty$. $\square \triangleleft$

### 4.5.4 The general corecursor

Suppose $Y \in \text{Tel}(\Gamma, \widehat{\bullet}_{\triangle\square})$ has the structure of the premises of the corecursor from section 3.3:

$$\begin{array}{l} \Gamma, \widehat{\bullet}_{\triangle\square} \mid v : Y \vdash_{sm} \zeta v : \Phi \\ \Gamma, \widehat{\bullet}_{\triangle\square} \mid v : Y \vdash_{sm} h v : A (\zeta v) \\ \Gamma, \widehat{\bullet}_{\triangle\square} \mid v : Y \mid y : \mathcal{B}(\zeta v, h) \vdash_{sm} \tau v y : Y^d v \\ \Gamma, \widehat{\bullet}_{\triangle\square} \mid v : Y \mid y : \mathcal{B}(\zeta v, h) \vdash_{sm} \zeta^d \langle v, \tau v y \rangle = \sigma (\zeta v) (h v) y \end{array}$$

Then $\zeta$ makes it an object of the slice category $(\text{Tel} // (\Gamma, \widehat{\bullet}_{\triangle\square})) / \Phi$. We will apply theorem 4.54 to the full subcategory $\text{Tel} // (\Gamma, \widehat{\bullet}_{\triangle\square} \mid \Phi) \subseteq (\text{Tel} // (\Gamma, \widehat{\bullet}_{\triangle\square})) / \Phi$. To that end, we give $Y$ the structure of a generalised $\overline{F}$-coalgebra as follows.

Suppose $X \in \text{Tel}(\Gamma, \widehat{\bullet}_{\triangle\square} \mid \Phi)$, and suppose we have a map $g : Y \to X$ in $(\text{Tel} // (\Gamma, \widehat{\bullet}_{\triangle\square})) / \Phi$, which is to say

$$\Gamma, \widehat{\bullet}_{\triangle\square} \mid v : Y \vdash_{sm} g v : X (\zeta v).$$

89

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

Example 4.56. Let $\Delta_n$ be the subcategory of the category $\Delta^+$ from section 4.2.1 containing the objects $\langle k \rangle$ with $0 \leqslant k \leqslant n$. Thus $\Delta_n(\langle k \rangle, \langle l \rangle)$ is the set of length $l+1$ binary sequences containing exactly $k+1$ 1s. For fixed $l$ we give these morphisms Campion's ordering, namely the usual ordering of binary numbers. Then $\Delta_n$ is an ordered direct category.

For $x \in I$ we write $\partial_{\mathcal{K}_x}$ for the sub-presheaf of the representable $\mathcal{K}_x$ consisting of nonidentity morphisms, i.e. $\partial_{\mathcal{K}_x}(y) = \{f \in I(y, x) \mid f \neq 1_x\} = \{f \in I(y, x) \mid y \prec x\}$.

If $I$ is a finite direct category and $H$ is a finite presheaf on it, there is a new finite direct category $I \oplus H$, called the **collage** of $H$, which contains $I$ as a full subcategory, together with one new object $*$ such that $I(x, *) = H(x)$ for all $x \in I$. Note that $\partial_{\mathcal{K}_x}$ restricted to $I$ coincides with $H$. Moreover, $I$ and $H$ are ordered if and only if $I \oplus H$ is. Moreover, if $I$ is an ordered direct category of finite height with $x$ its object of greatest rank, then $I \cong (I \setminus \{x\}) \oplus \partial_{\mathcal{K}_x}$. Thus, we can treat this as an induction principle for ordered direct categories.

### 4.5.5.2 Classifying contexts.

As our first use of this sort of induction, we construct for each ordered direct category $I$ a 'classifying context' for Reedy fibrant $I$-presheaves. Specifically, we construct by simultaneous induction:

1. For each ordered direct category I, a context \(\Gamma^1\). This will be the classifying context of Reedy fibrant I-types at level \(\ell\).
2. For each ordered presheaf H on I, a telescope \(\Gamma^1 \vdash_{\mathrm{sm}} \Theta^H \operatorname{tel}_{\ell}\).
3. For each map of ordered presheaves \(\alpha: \mathsf{H} \to \mathsf{H}'\) (not necessarily order-preserving) on I, a partial substitution \(\Gamma^1 \vdash_{\mathrm{sm}} \theta^\alpha: \Theta^{\mathsf{H}'} \to \Theta^{\mathsf{H}}\), varying functorially.
4. For each object \( x \in I \), a type \( \Gamma^1 \mid \Theta^{\partial_{\mathcal{K}_x}} \vdash_{\mathrm{sm}} B^x \text{ type}_\ell \).
5. For each \( h \in H(x) \), inducing by the Yoneda lemma a map \( \beta_h: \partial_{\mathcal{K}_x} \subseteq_{\mathcal{K}_x} \to H \), a term \( \Gamma^1 \mid \Theta^H \vdash_{sm} b^h: B^x[\theta^{\beta_h}] \), such that \( b^h[\theta^\alpha] = b^{\alpha(h)} \) for any \( \alpha: H \to H' \).
6. For each sieve \( J \subseteq I \), a telescope \( \Gamma^J \vdash_{\mathrm{sm}} \Gamma^{J,1} \operatorname{tel}_{\mathrm{isuc} \ell} \) and an isomorphism \( \Gamma^I \cong (\Gamma^J \mid \Gamma^{J,1}) \). Moreover, for all the structure in 2-5, the action of the weakening substitution \( \Gamma^I \cong (\Gamma^J \mid \Gamma^{J,1}) \to \Gamma^J \) corresponds to left Kan extension along the inclusion \( J \hookrightarrow I \).

For 1, we inductively use 2 and set

$$
\begin{array}{l}
\Gamma^\emptyset \equiv () \\
\Gamma^{I \oplus H} \equiv \left( \Gamma^I, A_*: \Theta^H \to \mathsf{Type}_\ell \right).
\end{array}
$$

For 2, we argue inductively on the linear ordering of $H$. If $H$ is empty, we set

$$
\Theta^\emptyset \equiv ().
$$

Otherwise, $H = (H \setminus \{h\}) \cup \{h\}$ where $h \in H(x)$ is the last element in the ordering; the condition on the ordering ensures that $H \setminus \{h\}$ is still an (ordered) presheaf. By the Yoneda lemma, $h$ induces a map $\beta_h: \partial_{\mathcal{K}_x} \subseteq_{\mathcal{K}_x} \to H \setminus \{h\}$, hence by 3 a substitution $\Gamma^I \vdash_{\mathrm{sm}} \theta^{\beta_h}: \Theta^{H \setminus \{h\}} \to \Theta^{\partial_{\mathcal{K}_x}}$. Thus, inductively using 4 as well, we can define

$$
\Theta^H = \left( \Theta^{H \setminus \{h\}}, a_h: B^x[\theta^{\beta_h}] \right).
$$

91

We similarly construct 3 by induction on H (the domain of α). The case when H is empty is trivial. Otherwise, we inductively have θ^α\{h\} : Θ^H' → Θ^H\{h\}, and to extend the codomain to Θ^H it suffices to give a term in context Γ^I | Θ^H' of type

$$\begin{array}{l} \mathrm{B}^{\mathrm{x}}[\theta^{\beta_{\mathrm{h}}}][\theta^{\alpha\backslash\{h\}}] \equiv \mathrm{B}^{\mathrm{x}}[\theta^{\beta_{\mathrm{h}}} \circ \theta^{\alpha\backslash\{h\}}] \\ \equiv \mathrm{B}^{\mathrm{x}}[\theta^{\beta_{\alpha\{h\}}}]. \end{array}$$

For this we can pick b^α{h}, using 5 inductively. Functoriality follows from the inductive assumption of functoriality in 5.

For 4, note that the slice category I/x is a sieve in I containing x. Then it suffices to define B^x in the case of I/x, since it can then be weakened to I using 6. In this case we have I/x = (I/x \ {x}) ⊕ ∂_x, so the last variable in Γ^I/x is A_x : Θ^∂_x → Type_ℓ. Thus, we can define Γ^I/x | y : Θ^∂_x ⊢_sm B^x to be Γ^I/x\{x}, A_x : Θ^∂_x → Type_ℓ | y : Θ^∂_x ⊢_sm A_x y.

For 5, it suffices to deal with the case when h is the last element in the ordering of H, since otherwise we can weaken from the sub-presheaf of all elements ≤ h to all of H, using 3 for the inclusion of this sub-presheaf. But in this case, the last variable in Θ^H is a_h : B^x[θ^h], so we can take b^h ≡ a_h. Functoriality follows immediately, as does stability under weakening from initial segments for all the data.

Finally, for 6 we induct on I. For a sieve in I ⊕ H there are two possibilities: it could be J or J ⊕ H for some sieve J in I, depending on whether it contains the new object *. (Of course, if it contains *, it must also contain all objects y such that H(y) ≠ ∅, which is to say that H must be left Kan extended from J.) In these two cases, we define

$$\begin{array}{l} \Gamma^{\mathrm{J}, \mathrm{I} \oplus \mathrm{H}} \equiv (\Gamma^{\mathrm{J}, \mathrm{I}}, A_{\star} : \Theta^{\mathrm{H}} \rightarrow \text{Type}_{\ell}) \\ \Gamma^{\mathrm{J} \oplus \mathrm{H}, \mathrm{I} \oplus \mathrm{H}} \equiv \Gamma^{\mathrm{J}, \mathrm{I}} \quad \text{weakened to } \Gamma^{\mathrm{J} \oplus \mathrm{H}}. \end{array}$$

This completes the construction of the classifying context. Note in particular that a consequence of 3 is that re-ordering the elements of a presheaf H modifies Θ^H only up to isomorphism.

4.5.5.3 The classifying context is classifying. To show this, we first construct a 'universal' diagram over Γ^I. Specifically, in any category with families, we construct simultaneously:

1. For each ordered direct category I, a Reedy type B of shape I and level ℓ over Γ^I in the sense of [KL21, Definition 3.22].
2. For each ordered presheaf H on I, the object Θ^H is the canonical H-weighted limit of B constructed by the 'master lemma' of [KL21, Lemma 3.11]. (In particular, therefore, Θ^∂_x is the matching object of B at x.)
3. The maps θ^α are the functorial action of these limits.
4. The type Γ^I | Θ^χ_ν ⊢_sm B^x is the object B(x) with its fibration to the matching object M_x B = Θ^∂_x.
5. The elements b^x are the projections from the weighted limit Θ^H.

92

The interesting case is 1, where we weaken the Reedy I-type B over $\Gamma^I$ to $\Gamma^{I \oplus H}$ and then must extend it to a Reedy $(I \oplus H)$-type by giving a type over the matching object $\Theta^{\partial \mathcal{L}_*}$. But $\mathcal{L}_* = H$ (weakened to $I \oplus H$), and so we can use $\operatorname{EI} A^H$ where $A^H$ is the newly added variable in $\Gamma^{I \oplus H}$. The other parts follow essentially tautologically.

Lastly, suppose C is a Reedy I-type over any context $\Delta$, and suppose that it is 'ℓ-small' in the sense that each type $C(x)$ over the matching object $M_x C$ is classified by a specified map into the universe $M_x C \to \text{Type}_\ell$. We show by induction on I that it is classified by a unique map $c: \Delta \to \Gamma^I$ such that $B[c] \equiv C$. This is trivial when I is empty. Assuming it to be true for I, if C is a Reedy $(I \oplus H)$-type over $\Delta$, and its restriction to an I-type is classified by a map $c: \Delta \to \Gamma^I$, then to extend this to a map into $\Gamma^{I \oplus H}$ we must give a term in context $\Delta$ of type $\Theta^H[c] \to \text{Type}_\ell$. But matching objects are preserved by substitution, so $\Theta^H[c]$ is the matching object $M_x C$, and thus this is exactly the data extending C to a Reedy $(I \oplus H)$-type.

4.5.5.4 Display and décalage of classifying contexts. Since the data $\Gamma^I$, $\Theta^H$, $B^x$, and so on are concrete finite syntactic objects (for any fixed I, H, x and so on), the rules in sections 2.4.4, 2.4.5, 2.6.2 and 2.6.5 suffice to completely compute display and décalage on them. We can characterize the results as follows.

Let 2 denote the interval category $(0 \xrightarrow{\mathcal{L}} 1)$, with two objects and one nonidentity morphism $\xi$ between them. Then if I is a direct category, so is $2 \times I$ with the product well-ordering where $x \prec y$ yields $(0, x) \prec (1, x) \prec (0, y) \prec (1, y)$. If I is ordered, we make $2 \times I$ ordered as follows. The morphisms in $2 \times I$ with codomain $(0, x)$ are bijective to those in I with codomain x, so we inherit that ordering. And the morphisms in $2 \times I$ with codomain $(1, x)$ are two copies of those in I with codomain x, one copy indexed by $1_1$ and one by $\xi$, so we give them the product well-ordering where $\xi \prec 1_1$: thus from $g \prec f$ we have $(\xi, g) \prec (1_1, g) \prec (\xi, f) \prec (1_1, f)$.

There is an evident projection $p: 2 \times I \to I$, inducing by precomposition from any presheaf H on I a presheaf $p^*H$ on $2 \times I$. Each element of H, say $h \in H(x)$, then induces two elements $p^*H$ in $H((0, x))$ and $H((1, x))$; we denote these $(0, h)$ and $(1, h)$ respectively for clarity. If H is ordered, we induce an ordering on $p^*H$ by ordering each element of $H((0, x))$ before the corresponding element of $H((1, x))$ (which is necessary, since $\xi$ maps the latter to the former).

We also have an inclusion $i_0: I \to 2 \times I$ defined by $i_0(x) = (0, x)$, which is a sieve. Left Kan extending along this inclusion takes a presheaf H on I to a presheaf $(i_0)_! H$ on $2 \times I$ that is supported only on the objects of the form $(0, x)$ and has exactly the same elements, hence inherits an ordering as well.

Now we prove by simultaneous induction:

1. For any I, we have $(\Gamma^I)^D \equiv \Gamma^{2 \times I}$.
2. For any presheaf H on I, we have $(\Theta^H)^D \equiv \Theta^{p^*H}$ and $\gamma': \Gamma^{2 \times I} \vdash_{sm} \Theta^{(i_0)_! H} \gamma' \equiv \Theta^H \gamma'^{ev}$.
3. This identification is functorial in maps $\alpha: H \to H'$.

93

4. For each $x \in I$, we have:

$$\gamma' : \Gamma^{2 \times I} \vdash_{\text{sm}} \Theta^{\partial \mathcal{K}_{(0,x)}} \gamma' \equiv \Theta^{\partial \mathcal{K}_x} \gamma'^{\text{ev}}$$

$$\gamma' : \Gamma^{2 \times I}, y : \Theta^{\partial \mathcal{K}_{(0,x)}} \gamma' \vdash_{\text{sm}} B^{(0,x)} \gamma' y \equiv B^x \gamma'^{\text{ev}} y$$

$$\partial \mathcal{K}_{(1,x)} = p^* \partial \mathcal{K}_x \cup \{(\xi, 1_x)\}$$

$$\gamma' : \Gamma^{2 \times I} \vdash_{\text{sm}} \Theta^{\partial \mathcal{K}_{(1,x)}} \gamma' \equiv \left( y' : (\Theta^{\partial \mathcal{K}_x})^D \gamma', a_{(0,x)} : B^x \gamma'^{\text{ev}} y'^{\text{ev}} \right)$$

$$\gamma' : \Gamma^{2 \times I}, y' : \Theta^{\partial \mathcal{K}_{(1,x)}} \gamma' \vdash_{\text{sm}} B^{(1,x)} \gamma' y' \equiv (B^x)^d \gamma' y'$$

5. For each $h \in H(x)$, we have:

$$\gamma' : \Gamma^{2 \times I}, y' : \Theta^{p^*H} \vdash_{\text{sm}} b^{(0,h)} \gamma' y' \equiv b^h \gamma'^{\text{ev}} y'^{\text{ev}}$$

$$\gamma' : \Gamma^{2 \times I}, y' : \Theta^{p^*H} \vdash_{\text{sm}} b^{(1,h)} \gamma' y' \equiv (b^h)^d \gamma' y'$$

For the inductive step of 1, we have

$$2 \times (I \oplus H) = (2 \times I) \oplus (i_0)_! H \oplus (p^*H \cup \{(\xi, 1_\star)\}).$$

Thus, using 2, we have

$$\Gamma^{2 \times (I \oplus H)}$$

$$\equiv \left( \gamma' : \Gamma^{(2 \times I)}, A_{(0,\star)} : \Theta^{(i_0)_!} H \to \text{Type}_\ell, A_{(1,\star)} : \Theta^{(p^*H \cup \{(\xi, 1_\star)\})} \to \text{Type}_\ell \right)$$

$$\equiv \left( \gamma' : (\Gamma^I)^D, A_{(0,\star)} : \Theta^H \gamma'^{\text{ev}} \to \text{Type}_\ell, A_{(1,\star)} : (y' : (\Theta^H)^D \gamma') \to A_{(0,\star)} y'^{\text{ev}} \to \text{Type}_\ell \right)$$

$$\equiv \left( \gamma : \Gamma^I, A_\star : \Theta^H \gamma \to \text{Type}_\ell \right)^D.$$

The other cases are similar. We can likewise show that

$$\Gamma^{I, 2 \times I} \equiv (\Gamma^I)^d,$$

with the isomorphism $\Gamma^{2 \times I} \cong (\Gamma^I \mid \Gamma^{I, 2 \times I})$ coinciding with the evens/odds pairing isomorphism $(\Gamma^I)^D \cong (\Gamma^I \mid (\Gamma^I)^d)$.

**4.5.5.5 Discrete fibrations.** The isomorphism $\Gamma^I \cong (\Gamma^I \mid \Gamma^{J,I})$ ensures that if $J \subseteq I$ is a sieve, we have a weakening substitution $\Gamma^I \to \Gamma^J$. But more generally, we can expect to induce a context substitution from any discrete fibration. Even more generally, we can get a *partial* substitution from a 'dependent' discrete fibration, in the following sense.

**Definition 4.57.** If $i : J \hookrightarrow I$ is the inclusion of a sieve in a direct category, a **co-section** of it is a discrete fibration $p : I \to J$ such that $p \circ i = 1_J$. In this case, if $H$ is a presheaf on $I$ and $K$ a presheaf on $J$, a morphism $H \to K$ over $p$ is a **relative isomorphism** if it induces a bijection $\sum_{y \in I} H(y) \to \sum_{y \in J} K(y)$.

Note that the projection $p : 2 \times I \to I$ above is *not* a co-section of the sieve $i_0 : I \hookrightarrow 2 \times I$, since it is not a discrete fibration. The prototypical example of a relative isomorphism is $\partial \mathcal{K}_x \to \partial \mathcal{K}_{p(x)}$ for any $x \in I$ (this is essentially the definition of a discrete fibration).

Now we define and prove inductively:

94

1. For any co-section $p : I \to J$ of a sieve $i : J \hookrightarrow I$ in an ordered direct category, a partial substitution $\Gamma^J \vdash_{sm} \gamma^p : \Gamma^{J,I}$.
2. In addition, for any order-preserving relative isomorphism $H \to K$ between ordered presheaves, we have $\Theta^H[\gamma^p] \equiv \Theta^K$.
3. For $x \in I$, we have $B^x[\gamma^p] \equiv B^{p(x)}$.
4. For $\alpha : H \to K$ an order-preserving relative isomorphism and $h \in H(x)$, we have $b^x[\gamma^p] \equiv b^{\alpha(x)}$.

To construct 1, note that as before there are two possibilities for a sieve in $I \oplus H$: it can be $J$ or $J \oplus H$ for a sieve $J$ in $I$. In the latter case, we have $\Gamma^{J \oplus H, I \oplus H} = \Gamma^{J,I}$ weakened to $\Gamma^{J \oplus H}$, and a co-section of $J \oplus H \hookrightarrow I \oplus H$ is determined by a co-section $p$ of $J \subseteq I$; thus we can similarly weaken $\gamma^p$.

In the former case, a co-section $I \oplus H \to J$ is determined by a co-section $p : I \to J$ together with an object $x \in J$ and a relative isomorphism $H \to \partial_{\mathcal{K}_x}$. Since $\Gamma^{J, I \oplus H} = (\Gamma^{J,I}, A_x : \Theta^H \to \text{Type}_\ell)$ in this case, to extend $\gamma^p$ as desired it suffices to give a term of type $\Gamma^J \vdash_{sm} \Theta^H[\gamma^p] \to \text{Type}_\ell$. But using 2 inductively, this is equal to $\Gamma^J \vdash_{sm} \Theta^{\partial_{\mathcal{K}_x}} \to \text{Type}_\ell$, so we can use the variable $A_x$ in $\Gamma^J$.

Now to prove 2, we induct on the ordering of $H$ and $K$, inductively using 3. The inductive arguments for 3–4 are similar.

4.5.5.6 Categorical coning. Our last generic construction is a category-theoretic notion of 'coning' a direct category. Let $J \subseteq I$ be a sieve in a direct category that contains the bottom object, which we presciently denote $\langle 0 \rangle$. Let $I^+$ denote the direct category $I$ augmented by an additional morphism $\zeta_x : \langle 0 \rangle \to x$ for all objects $x \in I \setminus J$. We define $f \circ \zeta_x = \zeta_y$ for all $f : x \to y$; note that $x \in I \setminus J$ implies $y \in I \setminus J$ since $J$ is a sieve. If $I$ is ordered, we order $I^+$ by placing $\zeta_x$ before all other morphisms with codomain $x$; this is actually the only possibility given our definition of composition. Note that $J$ is still a sieve in $I^+$.

Similarly, for a presheaf $H$ on $I$, let $H^+$ denote the presheaf on $I^+$ consisting of $H$ augmented by a new element $\zeta_H \in H(\langle 0 \rangle)$, such that $H^+(\zeta_x)(h) = \zeta_H$ for all $h \in H(x)$. If $H$ is ordered, we order $H^+$ by putting $\zeta_H$ first.

We now inductively prove:

1. For any sieve \( J \subseteq I \) in an ordered direct category, we have \( \Gamma^{J,I^+} \equiv (z : B^{\langle 0 \rangle}) \to \Gamma^{J,I} \) (meaning a \( \Pi \)-telescope).
2. In addition, for any \( H \) on \( I \), if we transfer \( \Theta^H \) and \( \Theta^{H^+} \) across the isomorphisms

$$\Gamma^I \cong (\gamma : \Gamma^J \mid \delta : \Gamma^{J,I} \gamma)$$

$$\Gamma^{I^+} \cong (\gamma : \Gamma^J \mid \delta : \Gamma^{J,I^+} \gamma) \equiv (\gamma : \Gamma^J \mid \delta : (z : B^{\langle 0 \rangle} \gamma) \to \Gamma^{J,I} \gamma)$$

to get $\tilde{\Theta}^H$ and $\tilde{\Theta}^{H^+}$, then we have

$$\tilde{\Theta}^{H^+} \gamma \delta \equiv (z : B^{\langle 0 \rangle} \gamma, \tilde{\Theta}^H \gamma (\delta z))$$

Both proofs are entirely straightforward, using the inductive definition of $\Pi$-telescopes as well as $\Gamma^I$ and $\Theta^H$.

The notation is somewhat abusive, since the construction depends on $J$ as well as $I$.

95

4.5.5.7 Correctness of semi-simplicial types. Recall that our definition of semi-simplicial types $\mathsf{SST}_{\ell}$ is as a displayed coinductive type with $\Phi \equiv ()$, $A \equiv \mathsf{Type}_{\ell}$, and $\mathcal{B} \ a \equiv \{x : \mathsf{El} \ a\}$. Therefore, the construction in section 4.5.2 simplifies as follows:

$$\vdash_{sm} X^{\partial n} \text{ tel} \quad \partial x : X^{\partial n} \vdash_{sm} X^n \partial x \text{ tel} \quad \vdash_{sm} X^{\partial 0} \equiv ()$$

$$\vdash_{sm} X^{\partial (n+1)} \equiv (\partial x : X^{\partial n}, x : X^n \partial x) \quad \vdash_{sm} X^0 \equiv \mathsf{Type}_{\ell}$$

$$\partial x : X^{\partial n}, x : X^n \partial x \vdash_{sm} h_n \partial x \ x : \mathsf{Type}_{\ell} \quad x : X^0 \vdash_{sm} h_0 \ x \equiv x$$

$$\partial x : X^{\partial n}, x : X^n \partial x, x' : X^{n+1} [ \partial x, x ] \vdash_{sm} h_{n+1} [ \partial x, x ] x' \equiv h_n \partial x \ x$$

$$\partial x : X^{\partial n}, x : X^n \partial x, b : \mathsf{El} (h_n \partial x \ x) \vdash_{sm} t_n \partial x \ x \ b : (X^{\partial n})^d \partial x$$

$$x : X^0, b : \mathsf{El} (h_0 \ x) \vdash_{sm} t_0 \ x \ b \equiv [ ]$$

$$\partial x : X^{\partial n}, x : X^n \partial x, x' : X^{n+1} [ \partial x, x ], b : \mathsf{El} (h_n \partial x \ x) \vdash_{sm} t_{n+1} [ \partial x, x ] x' \ b \equiv [ t_n \partial x \ x \ b, x' \ b ]$$

$$\partial x : X^{\partial n}, x : X^n \partial x \vdash_{sm} X^{n+1} [ \partial x, x ] \equiv (b : \mathsf{El} (h_{n-1} \partial x)) \to (X^n)^d \langle \partial x, t_n \partial x \ x \ b \rangle \ x$$

We will prove inductively that

$$X^{\partial n} \equiv \Gamma^{\Delta_{n-1}} \quad \text{and} \quad X^n \equiv \Theta^{\partial \mathcal{L}(n)} \to \mathsf{Type}_{\ell}.$$

This will imply that $\mathsf{SST} = \lim_n X^{\partial n}$ is a classifying context for all of $\Delta$. The claim about $X^n$ clearly inductively implies the claim about $X^{\partial n}$. Also it is easy to show inductively that $h_n \equiv B^{(0)}$. So it remains to say something useful about $t_n$.

Let $I_n$ be the subcategory of $2 \times \Delta_n$ containing all the objects except $(1, \langle n \rangle)$, and let $J_n = \{0\} \times \Delta_n$ regarded as a sieve in $I_n$. The central fact is the following.

Lemma 4.58. For any $n$, there is a co-section $q_n : I_n^+ \to J_n$.

Proof. On objects, let $q_n((1, \langle k \rangle)) = (0, \langle k+1 \rangle)$ for $0 \leqslant k < n$. A morphism $(1, \langle k \rangle) \to (1, \langle l \rangle)$ is a length $l+1$ sequence with $k+1$ 1s, and we augment it by another 1 on the right to get a length $l+2$ sequence with $k+2$ 1s, hence a morphism $(0, \langle k+1 \rangle) \to (0, \langle l+1 \rangle)$. A morphism $(0, \langle k \rangle) \to (1, \langle l \rangle)$ is also a length $l+1$ sequence with $k+1$ 1s, but this time we augment it by a 0 on the right to get a length $l+2$ sequence with $k+1$ 1s, hence a morphism $(0, \langle k \rangle) \to (0, \langle l+1 \rangle)$. Finally, we send the new morphism $\mathcal{L}_{(1, \langle l \rangle)}$ to the sequence of $l+1$ 0s followed by one 1. Functoriality is easy to check. And to see that it is a discrete fibration, we observe that any binary sequence of length $l+2$ with a positive number of 1s must be of exactly one of these three forms: a positive number of 1s followed by a 1, a positive number of 1s followed by a 0, or a sequence of 0s followed by a 1.

Evidently $q_{n+1}$ restricts to $q_n$ as we shrink the categories. Thus, we also get a relative isomorphism $\partial \mathcal{L}_{(1, \langle n \rangle)}^+ \to \partial \mathcal{L}_{(0, \langle n+1 \rangle)}$ over $q_n$.

Now note that if we abstract over $b$, the type of $t_n$ matches that of $\gamma^{q_n}$. Thus, we can now prove by simultaneous induction that:

1. $X^{\partial n} \equiv \Gamma^{\Delta_{n-1}}$.

96

2. $X^n \equiv \Theta^{\partial \lambda_{\langle n \rangle}} \to \text{Type}_\ell$.
3. $h_n \equiv B^{(0)}$.
4. $t_n \equiv \gamma^{q_n}$.

We have already remarked that 1 and 3 are easy, and the base cases of 2 and 4 are likewise trivial. For the induction step of 2, we have

$$\begin{aligned} X^{n+1}[\partial x, x] &\equiv \{b : \text{EI}(h_{n-1} \partial x)\} \to (X^n)^d \langle \partial x, t_n \partial x \times b \rangle x \\ &\equiv \{b : B^{(0)} \partial x\} \to \Theta^{\partial \lambda_{\langle 1, \langle n \rangle \rangle}} \langle \partial x, t_n \partial x \times b \rangle x \to \text{Type}_\ell \\ &\equiv \Theta^{\partial \lambda_{\langle 1, \langle n \rangle \rangle}} [\gamma^{q_n}] \to \text{Type}_\ell \\ &\equiv \Theta^{\partial \lambda_{\langle 1, \langle n+1 \rangle \rangle}} [\partial x, x] \to \text{Type}_\ell. \end{aligned}$$

Finally, the induction step of 4 follows immediately from the definition of $\gamma^p$ and the inductive hypothesis of 2. This completes the proof of the correctness of our construction of semi-simplicial types.

## 5 Conclusion and Future Work

In this paper we have made two main contributions. First, we have described *Displayed Type Theory (dTT)*, a new kind of type theory that incorporates (unary) internal parametricity but guarded by a modality, and showed that any model of dependent type theory with countable Reedy limits can be lifted to a model of dTT using augmented semi-simplicial diagrams. Because the latter are diagrams on an *inverse* category, their type theory is more closely related to that of the original model, and indeed the original model sits inside our model of dTT at the discrete mode. In particular, unlike other internally parametric type theories, dTT is compatible with classical axioms such as excluded middle and choice, as long as they are formulated at the discrete mode (or under the modality $\diamond$), and can be used as an internal logic to reason about arbitrary $(\infty, 1)$-toposes.

Secondly, inside dTT we have introduced a notion of *displayed coinductive type*, where the output of a destructor can be a parametricity 'computability witness' of the input, and showed that as a particular case of this notion we can define a type of *semi-simplicial types*. This yields a new approach to the long-standing open problem of representing infinitely coherent higher structures in type theory. Relative to other approaches, ours has the advantage that semi-simplicial types are defined (not postulated) as a simple instance of a type-former with natural introduction and elimination rules, i.e. a categorical universal property. While it remains to be seen how much can actually be done in practice with our definition, early indications of its utility are promising.

There are a number of directions for future work suggested by our results; here we survey a few of them briefly.

**5.0.0.1 Computation and implementation.** We conjecture that dTT satisfies canonicity and normalization, and should therefore be possible to implement in a proof assistant.

97

**5.0.0.2 Modal internal parametricity.** We expect that most applications of ordinary internal parametricity have modal versions that can be proven in dTT (or a higher-ary version of it, as discussed below). In addition to the traditional 'free theorems' such as those mentioned in the introduction, it would be especially interesting to investigate this for the proof of the pentagon identity for the smash product in [Cav21], since such a proof would then apply internally to any $(\infty, 1)$-topos.

**5.0.0.3 Computing diamond.** Our intended semantic model strictly validates computation rules for diamond, such as $\diamond (A \to B) \equiv \diamond A \to \diamond B$, because type formers in the simplicial model extend type formers in the discrete model at the level of $(-1)$-simplices. The syntax of dTT may thus be augmented with computation rules for diamond. Formally, this would be accomplished in a manner similar to display, by extending the definition of diamond to meta-abstractions, such as to handle open terms under binders. One would introduce an operation, *troncature* (meaning '*truncation*' in French), to model the action of diamond on telescopes. One then has:

$$\frac{\Gamma, \widehat{\bullet}_{\diamond} \vdash_{sm} \Upsilon \operatorname{tel}_{\ell}}{\Gamma \vdash_{dm} \diamond \Upsilon \operatorname{tel}_{\ell}}$$

$$\frac{\Gamma, \widehat{\bullet}_{\diamond} \vdash_{sm} \mathcal{A} \operatorname{type}_{\ell_1 / \nu : \Upsilon}}{\Gamma \vdash_{dm} \diamond \mathcal{A} \operatorname{type}_{\ell_1 / \nu^*: \diamond \Upsilon}}$$

**5.0.0.4 Higher category theory.** We have *defined* a type of semi-simplicial types in dTT, but such a definition is not an end in itself; it is intended as a tool for developing a theory of higher categories and other higher structures. We hope that our corecursion principle of SST, and the availability of other displayed coinductive types for predicates and structures on them, should make the development of such a theory feasible in dTT. We sketched some initial ideas in sections 3.2 and 3.4, but much remains to be done.

**5.0.0.5 Elementary models.** In section 4 we showed that any model of type theory with $\omega$-limits can be enhanced to a model of dTT including SST, but this is probably not the only way to construct models of dTT. In particular, we conjecture that there are 'realizability' models of dTT in which SST is a classifier for 'uniform' semi-simplicial types. This suggests that perhaps displayed coinductive types might be useful to include in a definition of elementary $(\infty, 1)$-topos.

**5.0.0.6 Higher-ary dTT.** The parametricity of dTT is *unary*, meaning that $A^d$ depends on one copy of $A$; but parametricity in general can be $n$-ary for any natural number $n$, and some applications require higher arities. We expect that higher-ary versions of dTT can be defined and modeled by a straightforward modification of the constructions in this paper, using higher-ary semi-cubical types in place of augmented semi-simplicial types (recall that augmented semi-simplicial types are the same as unary semi-cubical types). In this case the binary numbers described in section 4.2.1 become base-$(n + 1)$ numbers.

**5.0.0.7 Symmetries.** In theories with non-modal internal parametricity, and also in Higher Observational Type Theory, it appears to be necessary to include a '*symmetry*' operation on higher-dimensional types. For instance, in our notation a symmetry operation would have the type $A^{dd} a_{\equiv} a_{\equiv} a_{\equiv} \to A^{dd} a_{\equiv} a_{\equiv} a_{\equiv}$. The absence of symmetry in dTT is a significant simplification; for instance, it means that $\Delta^{+op}$ is a strict inverse category, making possible the explicit syntactic model construction in section 4.2. However, we have also seen that it

98

leads to certain limitations, e.g. without symmetry it is unclear how to give a corecursion principle for SST$^{d}$.

It should be possible to formulate a version of dTT (unary or higher-ary) with symmetry, but in the presence of symmetry it is unclear whether it is possible for display to compute definitionally on type-formers. However, it should work to use either the interval-based style of [BM12, BCM15, Mou16] or the 'observational' style of [ACKS24].

5.0.0.8 Unimode dTT. We have formulated dTT with two modes, but intuitively the discrete mode is unnecessary, as the dm-types are embedded in the sm-types by the modality $\triangle$. Thus, it should be possible to formulate a version of dTT in which there is only one mode. This is similar to other situations such as spatial/cohesive type theory [Shu18] and synthetic guarded domain theory [GKNB21] that have both unimodal and bimodal versions.

5.0.0.9 Conjectural syntax. In addition to displayed coinductive types, one may consider other kinds of generalized inductive and coinductive types. These are especially useful when taking a more 'synthetic' approach to higher structures in dTT, using the sm-types as augmented semi-simplicial objects rather than working with the internally defined type SST of semi-simplicial types.

Firstly, regarding display as analogous to paths in homotopy type theory suggests displayed inductive types as analogues of higher inductive types. Here the constructors generate displayed elements rather than ordinary ones. As an example, we can construct the simplicial cone of any type:

data C (A : $\square$ Type) : Type where
  $\iota$ : A $\to$ C A
  $\sigma$ : (x : A) $\to$ (C A)$^{d}$ ( $\iota$ x)

f : C A $\to$ B
f ( $\iota$ x) = ?$_{\iota}$ : B
f$^{d}$ ( $\iota$ x) ( $\sigma$ x) = ?$_{\sigma}$ : B$^{d}$ ?$_{\iota}$

Secondly, regarding both display and paths as a kind of modality suggests considering more general modal inductive types, whose constructors can land in modal versions of the type. For instance, since $\diamond A$ is the (-1)-simplices of A, a $\diamond$-modal constructor adds a (-1)-simplex without any higher simplices above it. In this way we can construct the free-living (-1)-simplex, and then all the higher simplices by coning:

data $\Delta^{-1}$ : Type where
  $\star$ : $\diamond$ $\Delta^{-1}$

f : $\Delta^{-1}$ $\to$ A
$\diamond$ f $\star$ = ?$_{\star}$ : $\diamond$ A

$\Delta$ : N $\to$ Type
$\Delta$ zero = C $\Delta^{-1}$
$\Delta$ (suc n) = C ($\Delta$ n)

Note that in both cases, we rely on the computation behaviour of $^{d}$ and $\diamond$ in order to directly give induction principles.$^{10}$ For example, the pattern match $\diamond$ f $\alpha$ requires that $\diamond$

$^{10}$The case splits for defining a function f valued out of an inductive type in this hypothetical extension of Agda,

99

of a function type compute to a function type. This is an improvement on the treatment of higher inductive types in [Uni13], since their natural elimination principle use ap, which is not there a primitive constant but a compound expression defined by path induction. In particular, we conjecture that in dTT, these displayed and modal inductive types can be made fully computational.

## References

[ACKS23] Danil Annenkov, Paolo Capriotti, Nicolai Kraus, and Christian Sattler. Two-level type theory and applications. Mathematical Structures in Computer Science, page 1–56, 2023. arXiv:1705.03307. (Cited on p. 4)

[ACKS24] Thorsten Altenkirch, Yorgo Chamoun, Ambrus Kaposi, and Michael Shulman. Internal parametricity, without an interval. To appear in POPL'24. arXiv:2307.06448, 2024. (Cited on pp. 8, 9, 12, 25, 76, and 99)

[Acz78] Peter Aczel. The type theoretic interpretation of constructive set theory. In Angus Macintyre, Leszek Pacholski, and Jeff Paris, editors, Logic Colloquium '77, volume 96 of Studies in Logic and the Foundations of Mathematics, pages 55–66. Elsevier, 1978. (Cited on p. 37)

[AFM+21] Benedikt Ahrens, Dan Frumin, Marco Maggesi, Niccolò Veltri, and Niels van der Weide. Bicategories in univalent foundations. Mathematical Structures in Computer Science, 31(10):1232–1269, 2021. (Cited on p. 11)

[AKS22] Thorsten Altenkirch, Ambrus Kaposi, and Michael Shulman. Towards a third-generation HOTT. URL: https://ncatlab.org/nlab/show/higher+observational+type+theory, 2022. (Cited on p. 9)

[AL19] Benedikt Ahrens and Peter LeFanu Lumsdaine. Displayed categories. Logical Methods in Computer Science, 15(1), March 2019. (Cited on pp. 10 and 33)

[Awo18] Steve Awodey. Natural models of homotopy type theory. Math. Structures Comput. Sci., 28(2):241–286, 2018. arXiv:1406.3219. (Cited on p. 44)

[BCM15] Jean-Philippe Bernardy, Thierry Coquand, and Guilhem Moulin. A presheaf model of parametric type theory. Electronic Notes in Theoretical Computer Science, 319:67 – 82, 2015. The 31st Conference on the Mathematical Foundations of Programming Semantics (MFPS XXXI). (Cited on pp. 7 and 99)

[BM12] Jean-Philippe Bernardy and Guilhem Moulin. A computational interpretation of parametricity. In Proceedings of the 2012 27th Annual IEEE/ACM Symposium on Logic in Computer Science, LICS '12, page 135–144, USA, 2012. IEEE Computer Society. (Cited on pp. 7 and 99)

[Cav21] Evan Cavallo. Higher Inductive Types and Internal Parametricity for Cubical Type Theory. PhD thesis, Carnegie Mellon University, February 2021. (Cited on p. 98)

as above, would result automatically by writing f x = ? and pressing C-c C-c in the context of the hole.

100

[CCD17] Simon Castellan, Pierre Clairambault, and Peter Dybjer. Undecidability of equality in the free locally cartesian closed category (extended version). *Logical Methods in Computer Science*, 13(4), November 2017. (Cited on p. 77)[CCD21] Simon Castellan, Pierre Clairambault, and Peter Dybjer. Categories with families: Unityped, simply typed, and dependently typed. In Claudia Casadio and Philip J. Scott, editors, *Joachim Lambek: The Interplay of Mathematics, Logic, and Linguistics*, pages 135–180. Springer Verlag, 2021. (Cited on p. 40)[CD11] Pierre Clairambault and Peter Dybjer. The biequivalence of locally cartesian closed categories and Martin-Löf type theories. In *Proceedings of the 10th international conference on Typed lambda calculi and applications*, TLCA'11, pages 91–106, Berlin, Heidelberg, 2011. Springer-Verlag. (Cited on p. 76)[GCK$^{+}$22] Daniel Gratzer, Evan Cavallo, G. A. Kavvos, Adrien Guatto, and Lars Birkedal. Modalities and parametric adjoints. *ACM Trans. Comput. Logic*, 23(3), apr 2022. (Cited on pp. 9, 12, 14, 16, 74, and 75)[GKNB21] Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. Multimodal dependent type theory. *Logical Methods in Computer Science*, 17(3), July 2021. (Cited on pp. 9, 12, 13, 14, 74, and 99)[Kel80] G. M. Kelly. A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on. *Bull. Austral. Math. Soc.*, 22(1):1–83, 1980. (Cited on p. 81)[KL21] Krzysztof Kapulkin and Peter LeFanu Lumsdaine. Homotopical inverse diagrams in categories with attributes. *Journal of Pure and Applied Algebra*, 225(4):106563, 2021. arXiv:1808.01816. (Cited on pp. 11, 40, 76, 90, and 92)[Kra15] Nicolai Kraus. The general universal property of the propositional truncation. In Hugo Herbelin, Pierre Letouzey, and Matthieu Sozeau, editors, *20th International Conference on Types for Proofs and Programs (TYPES 2014)*, volume 39 of *Leibniz International Proceedings in Informatics (LIPics)*, pages 111–145, Dagstuhl, Germany, 2015. Schloss Dagstuhl–Leibniz-Zentrum fuer Informatik. arXiv:1411.2682. (Cited on p. 11)[Lin89] Ingrid Lindström. A construction of non-well-founded sets within Martin-Löf's type theory. *The Journal of Symbolic Logic*, 54(1):57–64, 1989. (Cited on p. 37)[LOPS18] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. Internal universes in models of homotopy type theory. *Leibniz International Proceedings in Informatics (LIPics)*, 108(22):1–17, 2018. arXiv:1801.07664. (Cited on p. 8)[Mou16] Guilhem Moulin. *Internalizing parametricity*. PhD thesis, Chalmers University, 2016. (Cited on pp. 7 and 99)[RFL21] Mitchell Riley, Eric Finster, and Daniel R. Licata. Synthetic spectra via a monadic and comonadic modality. arXiv:2102.04099, 2021. (Cited on p. 9)[RS17] Emily Riehl and Michael Shulman. A type theory for synthetic ∞-categories. *Higher structures*, 1(1), 2017. arXiv:1705.07442. (Cited on p. 4)

101

[Shu15] Michael Shulman. Univalence for inverse diagrams and homotopy canonicity. *Mathematical Structures in Computer Science*, 25(5):1203–1277, June 2015. (Cited on pp. 8, 11, 40, and 76)

[Shu18] Michael Shulman. Brouwer’s fixed-point theorem in real-cohesive homotopy type theory. *Mathematical Structures in Computer Science*, 28(6):856–941, 2018. arXiv:1509.07584. (Cited on p. 99)

[Shu19] Michael Shulman. All $(\infty, 1)$-toposes have strict univalent universes. arXiv:1904.07004, 2019. (Cited on pp. 2, 7, 8, 11, and 81)

[Shu23] Michael Shulman. Semantics of multimodal adjoint type theory. *Electronic Notes in Theoretical Informatics and Computer Science*, 3 (Proceedings of MFPS XXXIX), November 2023. arXiv:2303.02572. (Cited on pp. 14 and 16)

[Uni13] Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. http://homotopytypetheory.org/book/, first edition, 2013. (Cited on pp. 2 and 100)

[Usk23] Elif Uskuplu. *Formalizing two-level type theory with cofibrant exo-nat*. PhD thesis, University of Southern California, 2023. (Cited on p. 4)

[Wad89] Philip Wadler. Theorems for free! In *Functional Programming Languages and Computer Architecture*, pages 347–359. ACM Press, 1989. (Cited on p. 6)

[Wei22] Jonathan Weinberger. Strict stability of extension types. arXiv:2203.07194, 2022. (Cited on p. 4)

102

# A Verifications for the Simplicial Model

## A.1 VARIABLES

We first check that pt is a morphism of presheaves:

$$\begin{array}{l} \left(\Gamma^{\mathrm{b}} \circ \left(p t_{\mathrm{sm}^{n+1}}^{A}\right)_{n+1}\right) \gamma_{n+1} \partial a a \\ \equiv \Gamma^{\mathrm{b}} \gamma_{n+1} \\ \equiv \left(p t_{\mathrm{sm}^{n+1}}^{A}\right)_{m+1} \left(\Gamma^{\mathrm{b}} \gamma_{n+1}\right) \left(\operatorname{act}_{\partial b}^{\pi A} \gamma_{n+1} \partial a\right) \left(\operatorname{act}_{b}^{A} \gamma_{n+1} \partial a a\right) \\ \equiv \left(\left(p t_{\mathrm{sm}^{n+1}}^{A}\right)_{m+1} \circ (\gamma : \Gamma, a : A \gamma)^{\mathrm{b}}\right) \gamma_{n+1} \partial a a. \end{array}$$

We now verify eq. (4.18) at the level of $(n+1)$-simplices:

$$\begin{array}{l} \left(\left(z v_{\mathrm{sm}^{n+1}}^{\pi A}\right)^{\rho_{(\Gamma, A)}} \gamma^{+} a a^{\prime}\right)_{n+1} \\ \equiv \left(z v_{\mathrm{sm}^{n+1}}^{\pi A}\right)_{n+1}^{(\Gamma, A)^{01(n+1)}} \gamma_{n+2} a_{\partial(n+1)} a_{n+1} a^{\prime}_{\partial(n+1)} a^{\prime}_{n+1} \\ \equiv \left(z v_{\mathrm{sm}^{n+1}}^{\pi A}\right)_{n+1} \left(\Gamma^{01(n+1)} \gamma_{n+2}\right) \left(\operatorname{act}_{\partial(01(n+1))}^{\pi A} \gamma_{n+2} a_{\partial(n+1)} a_{n+1} a^{\prime}_{\partial(n+1)}\right) \\ \left(\operatorname{act}_{01(n+1)}^{A} \gamma_{n+2} a_{\partial(n+1)} a_{n+1} a^{\prime}_{\partial(n+1)} a^{\prime}_{n+1}\right) \\ \equiv \left(z v_{\mathrm{sm}^{n+1}}^{\pi A}\right)_{n+1} \left(\left(\rho_{\Gamma}\right)_{n+1} \gamma_{n+2}\right) a_{\partial(n+1)} a_{n+1} \\ \equiv \left(z v_{\mathrm{sm}^{n+1}}^{\pi A^{\rho_{\Gamma}}}\right)_{n+1} \gamma_{n+2} a_{\partial(n+1)} a_{n+1} \\ \equiv \left(z v_{\mathrm{sm}^{n+1}}^{\pi A^{\rho_{\Gamma}}}\right)_{n+1} \left(\left(p t_{\mathrm{sm}^{n+1}}^{A^{\mathrm{d}}}\right)_{n+1} \gamma_{n+2} a_{\partial(n+1)} a_{n+1}, a^{\prime}_{\partial(n+1)} a^{\prime}_{n+1}\right) \\ \equiv \left(\left(z v_{\mathrm{sm}^{n+1}}^{\pi A^{\rho_{\Gamma}}}\right)^{\mathrm{p}_{\mathrm{sm}^{n+1}}^{A^{\mathrm{d}}}}\right)_{n+1} \gamma_{n+2} a_{\partial(n+1)} a_{n+1} a^{\prime}_{\partial(n+1)} a^{\prime}_{n+1} \\ \equiv \left(\left(z v_{\mathrm{sm}^{n+1}}^{\pi A^{\rho_{\Gamma}}}\right)^{\mathrm{p}_{\mathrm{sm}^{n+1}}^{A^{\mathrm{d}}}} \gamma^{+} a a^{\prime}\right)_{n+1}. \end{array}$$

We now need to verify eqs. (4.2) to (4.4) at the level of $(n+2)$-simplices. For the first two of these, for $\sigma : \Delta \to \Gamma$ and $\delta : \Delta \vdash_{\mathrm{sm}^{n+2}} t \delta : A (\sigma \delta)$, we have that:

$$\begin{array}{l} \left(p t_{\mathrm{sm}^{n+2}}^{A} \circ [\sigma, t]\right)_{n+2} \equiv \left(\left(p t_{\mathrm{sm}^{n+2}}^{A} \circ [\sigma, t]\right)^{\mathrm{D}}\right)_{n+1} \\ \equiv \left(\left(p t_{\mathrm{sm}^{n+2}}^{A}\right)^{\mathrm{D}} \circ [\sigma, t]^{\mathrm{D}}\right)_{n+1} \\ \equiv \left(p t_{\mathrm{sm}^{n+1}}^{\pi A^{\rho_{\Gamma}}} \circ p t_{\mathrm{sm}^{n+1}}^{A^{\mathrm{d}}} \circ [\sigma^{\mathrm{D}}, \pi t^{\rho_{\Delta}}, t^{\mathrm{d}}]\right)_{n+1} \\ \equiv \left(p t_{\mathrm{sm}^{n+1}}^{\pi A^{\rho_{\Gamma}}} \circ [\sigma^{\mathrm{D}}, \pi t^{\rho_{\Delta}}]\right)_{n+1} \\ \equiv \left(\sigma^{\mathrm{D}}\right)_{n+1} \\ \equiv \sigma_{n+2}. \end{array}$$

103

For the second:

$$\begin{aligned} \left( \left( z v_{s m^{n+2}}^{A} \right)^{\left[ \sigma, t \right]} \right)_{n+2} & \equiv \left( \left( \left( z v_{s m^{n+2}}^{A} \right)^{\left[ \sigma, t \right]} \right)^{d} \right)_{n+1} \\ & \equiv \left( \left( \left( z v_{s m^{n+2}}^{A} \right)^{d} \right)^{\left[ \sigma, t \right]^{D}} \right)_{n+1} \\ & \equiv \left( \left( z v_{s m^{n+1}}^{A^{d}} \right)^{\left[ \sigma^{D}, \pi t^{\rho_{A}}, t^{d} \right]} \right)_{n+1} \\ & \equiv \left( t^{d} \right)_{n+1} \\ & \equiv t_{n+2}. \end{aligned}$$

For the third, we will use eq. (4.18). For $\tau : \Delta \rightarrow (\gamma : \Gamma, a : A \gamma)$ in $s m^{n+2}$ we have:

$$\begin{aligned} & \left[ p t_{s m^{n+2}}^{A} \circ \tau, \left( z v_{s m^{n+2}}^{A} \right)^{\tau} \right]_{n+2} \\ & \equiv \left( \left[ p t_{s m^{n+2}}^{A} \circ \tau, \left( z v_{s m^{n+2}}^{A} \right)^{\tau} \right]^{D} \right)_{n+1} \\ & \equiv \left[ \left( p t_{s m^{n+2}}^{A} \right)^{D} \circ \tau^{D}, \left( z v_{s m^{n+1}}^{\pi A} \right)^{\pi \tau \circ \rho_{A}}, \left( \left( z v_{s m^{n+2}}^{A} \right)^{\tau} \right)^{d} \right]_{n+1} \\ & \equiv \left[ p t_{s m^{n+1}}^{\pi A^{\rho_{\Gamma}}} \circ p t_{s m^{n+1}}^{A^{d}} \circ \tau^{D}, \left( z v_{s m^{n+1}}^{\pi A} \right)^{\rho_{\left[ \Gamma, A \right] \circ \tau^{D}}}, \left( \left( z v_{s m^{n+2}}^{A} \right)^{d} \right)^{\tau^{D}} \right]_{n+1} \\ & \equiv \left[ p t_{s m^{n+1}}^{\pi A^{\rho_{\Gamma}}} \circ p t_{s m^{n+1}}^{A^{d}} \circ \tau^{D}, \left( z v_{s m^{n+1}}^{\pi A^{\rho_{\Gamma}}} \right)^{\rho t_{s m^{n+1}}^{A^{d}} \circ \tau^{D}}, \left( z v_{s m^{n+1}}^{A^{d}} \right)^{\tau^{D}} \right]_{n+1} \\ & \equiv \left[ p t_{s m^{n+1}}^{A^{d}} \circ \tau^{D}, \left( z v_{s m^{n+1}}^{A^{d}} \right)^{\tau^{D}} \right]_{n+1} \\ & \equiv \left[ \tau^{D} \right]_{n+1} \\ & \equiv \tau_{n+2}. \end{aligned}$$

◀

## A.2 $\Pi$-TYPES

We verify the $\beta$-law at the level of $(n + 2)$-simplices:

$$\begin{aligned} & \left( a p p^{s m^{n+2}} \left( \lambda^{s m^{n+2}} t \right) s \right)_{n+2} \\ & \equiv \left( \left( a p p^{s m^{n+2}} \left( \lambda^{s m^{n+2}} t \right) s \right)^{d} \right)_{n+1} \\ & \equiv \left( a p p^{s m^{n+1}} \left( a p p^{s m^{n+1}} \left( \lambda^{s m^{n+2}} t \right)^{d} \pi s^{\rho_{\Gamma}} \right) s^{d} \right)_{n+1} \\ & \equiv \left( a p p^{s m^{n+1}} \left( a p p^{s m^{n+1}} \left( \lambda^{s m^{n+1}} \left( \lambda^{s m^{n+1}} t^{d} \right) \right) \pi s^{\rho_{\Gamma}} \right) s^{d} \right)_{n+1} \\ & \equiv \left( a p p^{s m^{n+1}} \left( \lambda^{s m^{n+1}} t^{d} \right)^{\left[ 1_{\Gamma D}, \pi s^{\rho_{\Gamma}} \right]} s^{d} \right)_{n+1} \\ & \equiv \left( a p p^{s m^{n+1}} \left( \lambda^{s m^{n+1}} \left( t^{d} \right)^{W_{2}^{A^{d}} \left[ 1_{\Gamma D}, \pi s^{\rho_{\Gamma}} \right]} \right) s^{d} \right)_{n+1} \\ & \equiv \left( \left( t^{d} \right)^{\left[ 1_{\Gamma}^{D}, \pi s^{\rho_{\Gamma}}, s^{d} \right]} \right)_{n+1} \\ & \equiv \left( \left( t^{\left[ 1_{\Gamma}, s \right]} \right)^{d} \right)_{n+1} \\ & \equiv \left( t^{\left[ 1_{\Gamma}, s \right]} \right)_{n+2}. \end{aligned}$$

104

We also verify the η-law:

$$\begin{aligned} & \left(\lambda^{\mathrm{sm}^{n+2}}\left(\mathrm{app}^{\mathrm{sm}^{n+2}} \mathrm{f}^{\mathrm{pt}} \mathrm{zv}\right)\right)_{n+2} \\ & \quad \equiv\left(\left(\lambda^{\mathrm{sm}^{n+2}}\left(\mathrm{app}^{\mathrm{sm}^{n+2}} \mathrm{f}^{\mathrm{pt}} \mathrm{zv}\right)\right)^{\mathrm{d}}\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+2}} \mathrm{f}^{\mathrm{pt}} \mathrm{zv}\right)^{\mathrm{d}}\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{f}^{\mathrm{pt}}\right)^{\mathrm{d}} \pi \mathrm{zv}^{\mathrm{P}(\mathrm{f}, \mathrm{A})}\right) \mathrm{zv}^{\mathrm{d}}\right)\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{f}^{\mathrm{d}}\right)^{\mathrm{pt}^{\mathrm{D}}} \mathrm{zv}^{\mathrm{pt}}\right) \mathrm{zv}\right)\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{f}^{\mathrm{d}}\right)^{\mathrm{ptopt}} \mathrm{zv}^{\mathrm{pt}}\right) \mathrm{zv}\right)\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{f}^{\mathrm{d}}\right)^{\mathrm{pt}} \mathrm{zv}\right)^{\mathrm{pt}} \mathrm{zv}\right)\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\mathrm{f}^{\mathrm{d}}\right)^{\mathrm{pt}} \mathrm{zv}\right)\right)_{n+1} \\ & \quad \equiv\left(\mathrm{f}^{\mathrm{d}}\right)_{n+1} \\ & \quad \equiv \mathrm{f}_{n+2}. \end{aligned}$$

◁

### A.3 UNIVERSES

We verify that Code and EI are mutually inverse at the level of (n + 2)-simplices:

$$\begin{aligned} & \left(\mathrm{EI}^{\mathrm{sm}^{n+2}}\left(\mathrm{Code}^{\mathrm{sm}^{n+2}} \mathrm{A}\right)\right)_{n+2} \\ & \quad \equiv\left(\left(\mathrm{EI}^{\mathrm{sm}^{n+2}}\left(\mathrm{Code}^{\mathrm{sm}^{n+2}} \mathrm{A}\right)\right)^{\mathrm{d}}\right)_{n+1} \\ & \quad \equiv\left(\mathrm{EI}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\left(\mathrm{Code}^{\mathrm{sm}^{n+2}} \mathrm{A}\right)^{\mathrm{d}}\right)^{\mathrm{pt}} \mathrm{zv}\right)\right)_{n+1} \\ & \quad \equiv\left(\mathrm{EI}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{Code}^{\mathrm{sm}^{n+1}} \mathrm{A}^{\mathrm{d}}\right)\right)^{\mathrm{pt}} \mathrm{zv}\right)\right)_{n+1} \\ & \quad \equiv\left(\mathrm{EI}^{\mathrm{sm}^{n+1}}\left(\mathrm{app}^{\mathrm{sm}^{n+1}}\left(\lambda^{\mathrm{sm}^{n+1}}\left(\mathrm{Code}^{\mathrm{sm}^{n+1}} \mathrm{A}^{\mathrm{d}}\right)^{\mathrm{W}_{2}^{\mathrm{nA}^{\mathrm{dP}} \mathrm{pt}}}\right) \mathrm{zv}\right)\right)_{n+1} \\ & \quad \equiv\left(\mathrm{EI}^{\mathrm{sm}^{n+1}}\left(\mathrm{Code}^{\mathrm{sm}^{n+1}} \mathrm{A}^{\mathrm{d}}\right)^{\left[\mathrm{pt}, \mathrm{zv}\right]}\right)_{n+1} \\ & \quad \equiv\left(\mathrm{EI}^{\mathrm{sm}^{n+1}}\left(\mathrm{Code}^{\mathrm{sm}^{n+1}} \mathrm{A}^{\mathrm{d}}\right)\right)_{n+1} \\ & \quad \equiv\left(\mathrm{A}^{\mathrm{d}}\right)_{n+1} \\ & \quad \equiv \mathrm{A}_{n+2}. \end{aligned}$$

105

In the other direction:

$$\begin{aligned} & \left(\operatorname{Code}^{\mathfrak{sm}^{n+2}}\left(\operatorname{EI}^{\mathfrak{sm}^{n+2}} A\right)\right)_{n+2} \\ & \quad \equiv\left(\left(\operatorname{Code}^{\mathfrak{sm}^{n+2}}\left(\operatorname{EI}^{\mathfrak{sm}^{n+2}} A\right)\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathfrak{sm}^{n+1}}\left(\operatorname{Code}^{\mathfrak{sm}^{n+1}}\left(\operatorname{EI}^{\mathfrak{sm}^{n+2}} A\right)^{d}\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathfrak{sm}^{n+1}}\left(\operatorname{Code}^{\mathfrak{sm}^{n+1}}\left(\operatorname{EI}^{\mathfrak{sm}^{n+1}}\left(\operatorname{app}^{\mathfrak{sm}^{n+1}}\left(A^{d}\right)^{\mathrm{pt}} z v\right)\right)\right)\right)_{n+1} \\ & \quad \equiv\left(\lambda^{\mathfrak{sm}^{n+1}}\left(\operatorname{app}^{\mathfrak{sm}^{n+1}}\left(A^{d}\right)^{\mathrm{pt}} z v\right)\right)_{n+1} \\ & \quad \equiv\left(A^{d}\right)_{n+1} \\ & \quad \equiv A_{n+2} . \end{aligned}$$

### A.4 ω-LIMITS

We mutually verify the identity between res and lim at the m-th stage and on the boundary:

$$\begin{aligned} & \left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\partial \mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+2}} \bar{a}\right)\right)_{n+2} \\ & \quad \equiv\left(\left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\partial \mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+2}} \bar{a}\right)\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\operatorname{res}_{\mathfrak{sm}^{n+1}}^{\partial \mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+2}} \bar{a}\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\operatorname{res}_{\mathfrak{sm}^{n+1}}^{\partial \mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+1}} \bar{a}^{d}\right)\right)_{n+1} \\ & \quad \equiv\left(\left(\bar{a}^{d}\right)^{\partial \mathfrak{m}}\right)_{n+1} \\ & \quad \equiv\left(\left(\bar{a}^{\partial \mathfrak{m}}\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\bar{a}^{\partial \mathfrak{m}}\right)_{n+2} \\ & \quad \left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+2}} \bar{a}\right)\right)_{n+2} \\ & \quad \equiv\left(\left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+2}} \bar{a}\right)\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\operatorname{res}_{\mathfrak{sm}^{n+1}}^{\mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+2}} \bar{a}\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\operatorname{res}_{\mathfrak{sm}^{n+1}}^{\mathfrak{m}}\left(\lim _{\mathfrak{sm}^{n+1}} \bar{a}^{d}\right)\right)_{n+1} \\ & \quad \equiv\left(\left(\bar{a}^{d}\right)^{\mathfrak{m}}\right)_{n+1} \\ & \quad \equiv\left(\left(\bar{a}^{\mathfrak{m}}\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\bar{a}^{\mathfrak{m}}\right)_{n+2} . \end{aligned}$$

We also verify the η-law:

$$\begin{aligned} & \left(\lim _{\mathfrak{sm}^{n+2}}\left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\mathfrak{m}} \bar{u}\right)_{\mathfrak{m}}\right)_{n+2} \\ & \quad \equiv\left(\left(\lim _{\mathfrak{sm}^{n+2}}\left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\mathfrak{m}} \bar{u}\right)_{\mathfrak{m}}\right)^{d}\right)_{n+1} \\ & \quad \equiv\left(\lim _{\mathfrak{sm}^{n+1}}\left(\operatorname{res}_{\mathfrak{sm}^{n+2}}^{\mathfrak{m}} \bar{u}\right)_{\mathfrak{m}}^{d}\right)_{n+1} \\ & \quad \equiv\left(\lim _{\mathfrak{sm}^{n+1}}\left(\operatorname{res}_{\mathfrak{sm}^{n+1}}^{\mathfrak{m}} \bar{u}^{d}\right)_{\mathfrak{m}}\right)_{n+1} \\ & \quad \equiv\left(\bar{u}^{d}\right)_{n+1} \\ & \quad \equiv\left(\bar{u}\right)_{n+2} . \end{aligned}$$

◁

106