arXiv:1411.0898v2 [math.CT] 10 Apr 2023

# Localic metric spaces and the localic Gelfand duality

Simon Henry

April 12, 2023

## Abstract

In this paper we prove, as conjectured by B.Banachewski and C.J.Mulvey, that the constructive Gelfand duality can be extended into a duality between compact regular locales and unital abelian localic $C^*$-algebras. In order to do so we develop a constructive theory of localic metric spaces and localic Banach spaces, we study the notion of localic completion of such objects and the behaviour of these constructions with respect to pull-back along geometric morphisms.

## Contents

|  **1 Introduction** | **2**  |
| --- | --- |
|  **2 Notations and Preliminaries** | **3**  |
|  2.1 General remarks | 3  |
|  2.2 The category of locales | 4  |
|  2.3 Positivity and fiberwise density | 6  |
|  2.4 Descent theory | 12  |
|  2.5 Spaces of numbers | 13  |
|  2.6 $[X, \mathbb{R}]$ is locally positive | 14  |
|  **3 Constructive theory of metric locales** | **18**  |
|  3.1 Pre-metric locale | 18  |
|  3.2 Metric locales | 29  |
|  3.3 Completion of a metric locale | 32  |
|  3.4 Product of metric locales | 42  |
|  3.5 The locale $[X, Y]_1$ of metric maps | 43  |
|  3.6 Case of metric sets | 48  |
|  **4 Banach locales and $C^*$ locales** | **50**  |
|  4.1 Banach locales and completeness | 50  |
|  4.2 The Localic Gelfand duality | 54  |

Keywords. Locales, Metric locales, Banach locales, Gelfand duality.
2010 Mathematics Subject Classification. 18B25, 03G30, 06D22, 46L05, 47S30.
email: shenry2@uottawa.ca

1

# 1 Introduction

In [1], C.J.Mulvey and B.Banaschewski showed$^{1}$ that the usual Gelfand duality between abelian $C^*$ algebras and compact (Hausdorff) topological spaces can be extended into a “constructive” Gelfand duality between $C^*$ algebras and compact completely regular locales. A locale (see 2.2) is almost the same as a topological space, but may fail to have points. A locale which has enough points is called a spatial locale and is the same thing as a (sober) topological space. Assuming the axiom of choice, any locally compact locale has enough points; hence the result of Banaschewski and Mulvey gives back the usual Gelfand duality when assuming the axiom of choice. But the constructive version can be applied to a broader context: for example an internal application to the topos of sheaves over a topological space $X$ relates continuous fields of abelian $C^*$ algebras over $X$ and proper maps to $X$, and this can also be applied to more general toposes.

At the end of their proof of the constructive Gelfand duality, Banachewski and Mulvey suggested that “compact completely regular” is not the most natural condition one would have expected. It would be nicer to weaken this condition into “compact regular” (which is the same as compact separated, see [12] C3.2.10). Unfortunately, when a locale is not completely regular it might fail to have $\mathbb{C}$-valued continuous functions, and hence the associated $C^*$ algebra has no reason to keep track of enough informations about $X$. They suggested that their result should be extended into a duality between compact regular locales and a notion of localic $C^*$ algebras yet to be defined. This is a natural idea because when $X$ is a compact regular locale, one can still define a locale $[X, \mathbb{C}]$ of functions from $X$ to $\mathbb{C}$ and complete regularity only concerns the existence of points for this locale. The main goal of this article is to define this notion of localic $C^*$ algebras (which we will call $C^*$ locales) and to prove this conjectured duality.

Two other reasons for developing a theory of localic $C^*$ algebras and more generally of localic Banach spaces (called Banach locales) are the following. In [14] I.Moerdijk showed (using the result of A.Joyal and M.Tierney in [13]) that Grothendieck toposes can be identified with a full subcategory of the 2-category of localic groupoids (that is groupoids in the category of locale, morphisms between them being the localic principal bi-bundles, see [4] for more details). A Banach space in the logic of the topos which corresponds to a localic groupoid $G_1 \Rightarrow G_0$ is essentially a continuous field of Banach spaces $\mathcal{B}$ over $G_0$ endowed with a continuous action of $G_1$ such that there are enough local sections of $\mathcal{B}$ which have an open stabilizer. This hypothesis of open stabilizers is, from the point of view of analysis and geometry, a little too restrictive and is related to the requirement of existence of points. Hence one could expect that a good notion of Banach locale could remove it. Also for the purpose of non-commutative geometry one would like to be able to study equivariant bundle on general localic (topological) groupoids and not just those which correspond to toposes.

$^{1}$To be more accurate, they only showed this result internally in Grothendieck toposes, using at some points an external argument relying on the axiom of choice (the Barr covering theorem). A completely internal and constructive proof has been given later by T.Coquand and B.Spitters in [7].

2

For example the groupoid defined by $G_0$ being a point and $G_1$ being a connected locally compact topological group does not correspond to a topos but is an important groupoid for non-commutative geometry. In order to define the notion of Banach space over an arbitrary localic groupoid, an important point is that this notion should descend along open surjections (see 2.4). Unfortunately, there is no such descent property for Banach spaces and $C^*$ algebras. However, as locales descend along open (or proper) surjections and as the pull-back of Banach spaces is a pull-back of the localic completion, we will be able to prove that Banach locales and $C^*$ locales have this descent property, and form in fact the “stackification” of the notion of Banach spaces and $C^*$ algebras, i.e. the smallest generalization of the notion which have this descent property.

Section 2 reviews some well known facts and definitions, mostly about the theory of locales, in order to fix the notation and prove some basic but important results for the rest of the paper. In section 3 we will develop the theory of metric locales in a constructive context (the classical theory is already known and can be found for example in [17]). We also show how to construct a classifying locale $[X, Y]_1$ for metric maps between two complete metric locales, which was apparently not known even in the classical case. In section 4 we apply the theory of section 3 in order to define Banach locales and $C^*$ locales and prove the announced result, although most of the technical difficulties lie in section 3.

An extended version of this article can be found in the author’s thesis [9]. This extended version also contains an additional section where we prove (assuming the axiom of dependant choice) that when we work internally in a topos $\mathcal{T}$ satisfying some technical condition related to paracompactness then the category of localic banach spaces of $\mathcal{T}$ is equivalent to the category of usual Banach spaces of $\mathcal{T}$. This result is a topos theoretic adaptation of a theorem$^2$ of A.Douady and L.Dal Soglio-Herault asserting that over a paracompact topological spaces every Banach bundle has enough continuous sections. We decided not to include this last result in the present paper because we think that it still needs to be improved, in particular, more recent results we obtained suggest that it should be a consequence of a fully constructive result with more natural hypothesis.

## 2 Notations and Preliminaries

### 2.1 General remarks

In all the article we are implicitly working internally in an elementary topos $\mathcal{S}$ with a natural number object $\mathbb{N}$. This means that we will never use neither the law of excluded middle nor the axiom of choice. Objects of $\mathcal{S}$ will simply be called “sets”. All other toposes mentioned are bounded $\mathcal{S}$-toposes, i.e. Grothendieck toposes over $\mathcal{S}$ (although the hypothesis bounded can probably be removed most of the time).

A proposition (internal to a topos) is said to be *decidable* if it is complemented (i.e. such that $P \vee \neg P$ holds). An object is said to have decidable equality, or

$^2$published as an appendix of [8]

3

to be *decidable*, if its diagonal embedding $X \rightarrow X \times X$ is complemented. A set $X$ (or an object of a topos) is said to be *inhabited* if it satisfies (internally) $\exists x \in X$. It is said to be *finite* if it is Kuratowski finite (see [12, D5.4]), i.e. if $\exists n \in \mathbb{N}, x_1, \dots, x_n \in X$ such that $\forall x \in X, \exists i, x = x_i$. Note that in particular (as $\mathbb{N}$ is decidable) a finite set is either empty or inhabited.

When considering product $E_1 \times \dots \times E_n$ of objects of any kind (generally locales) we will denote by $\pi_i$ the projection onto $E_i$, by $\pi_{i,j}$ the projection onto $E_i \times E_j$, etc... We generally do not specify the domain of definition and we hope that it will be clear from the context. For example one has: $\pi_1 \circ \pi_{i,j} = \pi_i$ and $\pi_2 \circ \pi_{i,j} = \pi_j$ because in these formulas $\pi_1$ and $\pi_2$ denote the two projections from $E_i \times E_j$ to $E_i$ and $E_j$ respectively.

## 2.2 The category of locales

We will start by briefly introducing the notion of locale, essentially in order to fix the notation and the vocabulary. A short introduction to this subject can be found in the first two sections of [2], a more complete one in part $C$ (especially in $C1$) of [12] and an extremely complete (but non constructive) one in [17].

2.2.1. A *frame* is an ordered set which admit arbitrary supremums and such that binary infimums distribute over arbitrary supremums. A morphism of frame is a non-decreasing map which preserve both arbitrary supremum and finite infimum.

2.2.2. The category of *locales* is defined as the opposite category of the category of frames. But we will adopt “topological” notations for them:

- If $X$ is a locale, the corresponding frame is denoted by $\mathcal{O}(X)$.
- If $f: X \rightarrow Y$ is a morphism of locales, we denote by $f^*$ the corresponding frame homomorphism from $\mathcal{O}(Y)$ to $\mathcal{O}(X)$.
- An element $U \in \mathcal{O}(X)$ is called an open sublocale of $X$, the top element of $\mathcal{O}(X)$ is denoted $X$.
- As $f^*$ commutes to arbitrary supremums, it has a right adjoint denoted $f^*$.

Also we will tend to call unions and intersections the supremums and infimums in $\mathcal{O}(X)$.

4

2.2.3. A *sublocale* of a locale $X$ is (an equivalence class of) a locale $Y$ endowed with a morphism $f: Y \rightarrow X$ such that $f^*$ is a surjective frame homomorphism (such a morphism is called an *inclusion*). A morphism of locale $f$ is said to be *surjective* if the corresponding frame homomorphism is injective. In particular, the injection/surjection factorisation of frame homomorphisms induces a unique (up to unique isomorphism) factorisation of every morphism of locale $f: X \rightarrow Y$ in a surjection followed by an inclusion:

$$X \rightarrow f_!(X) \hookrightarrow Y.$$

The sublocale $f_!(X)$ is called the image$^{3}$ of $f$. More generally if $S$ is any sublocale of $X$ we denote by $f_!(S)$ the image of the restriction of $f$ to $S$ and this is called the image of $S$ by $f$.

2.2.4. If $f: X \rightarrow Y$ is a morphism of locales and $S$ is a sublocale of $Y$ then the categorical pull-back $f^{-1}(S)$ is a sublocale of $X$ and one has an adjunction formula:

$$A \subset f^{-1}(B) \Leftrightarrow f_!(A) \subset B$$

for any sublocale $A$ of $X$ and $B$ of $Y$.

2.2.5. If $U$ is an element of the frame $\mathcal{O}(X)$ then it corresponds to a sublocale (also denoted $U$) of $X$ which is defined by the frame $\mathcal{O}(U) = \{v \in \mathcal{O}(X) | v \leq U\}$ and which is sent into $X$ by the morphism corresponding to $i^*(V) = V \wedge U$ for any $V \in \mathcal{O}(X)$. Hence, the elements of $\mathcal{O}(X)$ correspond to particular sublocales of $X$, which justifies the term “open sublocales” for elements of $\mathcal{O}(X)$. Also, through this identification, one has $f^*(U) = f^{-1}(U)$.

2.2.6. To any locale $X$ one can associate the topos of sheaves on $X$, denoted $\mathsf{Sh}(X)$. If $X$ and $Y$ are two locales, the category of geometric morphisms from $\mathsf{Sh}(X)$ to $\mathsf{Sh}(Y)$ is (equivalent to) the ordered set of locale morphisms from $X$ to $Y$ ordered by the pointwise ordering of the corresponding frame homomorphism (this is called the specialisation order). For this reasons locales will be seen as a specific kind of toposes.

2.2.7. An extremely important result of the theory of locales, that we will use constantly, is that there is an equivalence of category between $X$-locales, that is locales in the logic of $\mathsf{Sh}(X)$ and locales $Y$ endowed with a morphism to $X$. This allows one to turn any reasonable property of locales into a property of geometric morphisms, corresponding to the relative notion, for example one says that a map $Y \rightarrow X$ is proper if the $X$-locale corresponding to $Y$ is compact in the logic of $\mathsf{Sh}(X)$.

$^{3}$From a purely categorical point of view, we should call it the regular image of $X$.

5

2.2.8. At several points of this article we will deal (in simple situations) with locales as if they had points in order to define a map between two locales or to give constraints on some map. This kind of expression should of course not be interpreted in terms of points of a locale $X$ but in terms of “generalized points”, that is morphisms from $T$ to $X$ for an arbitrary locale $T$, and all the constructions done on these points should be interpreted in the logic of $\mathfrak{Sh}(T)$. If all the constructions on these generalized elements are “geometric” (that is compatible with the pull-back from $\mathfrak{Sh}(T)$ to $\mathfrak{Sh}(T')$ for any locale $T'$ over $T$) then these constructions yield a morphism of functor, or relation between such morphisms and hence by the Yoneda lemma this indeed gives a morphism of locales or conditions between such morphisms.

2.2.9. One says that a locale $\mathcal{L}$ classifies some theory $T$ if the topos $\mathfrak{Sh}(\mathcal{L})$ classifies the theory $T$. (see the part $D$ of [12] for the general theory of classifying toposes) Locales are the classifying spaces of what is called propositional geometric theory. That is geometric theory over a signature (see [12]D1.1.1) which contains no sorts. In particular it contains no function symbol and all the relations symbol it contains have no free variable and are called propositions. A propositional geometric theory classified by a locale $\mathcal{L}$ is essentially the same thing as a presentation of the frame $\mathcal{O}(\mathcal{L})$: indeed basic proposition of the theory are generator and the geometric (in the sense of [12, D1.1.3(f)]) axioms of the theory are relations of the form $T \leqslant T'$ where $T$ and $T'$ are formed from the basic proposition using finite intersection and arbitrary union.

2.2.10. If $\mathcal{L}$ is a locale in the logic of some topos $\mathcal{T}$ and if $f: \mathcal{E} \to \mathcal{T}$ is a geometric morphism then, $f^*\mathcal{O}(\mathcal{L})$ is in general not a frame in $\mathcal{E}$, but it can be completed in a frame, giving rise to locale called $f^\#(\mathcal{L})$ in $\mathcal{E}$. More precisely, if one takes a presentation of $\mathcal{L}$, then one can pull-back the presentation through $f$ and construct a locale $\mathcal{L}'$ in $\mathcal{E}$. One can then check from the universal property that one has the following pull-back diagram of toposes:

$$\begin{array}{c} \mathfrak{Sh}_{\mathcal{E}}(\mathcal{L}') \longrightarrow \mathcal{E} \\ \downarrow \qquad \qquad \qquad \downarrow \\ \mathfrak{Sh}_{\mathcal{T}}(\mathcal{L}) \longrightarrow \mathcal{T} \end{array}$$

which shows that $\mathcal{L}'$ does not depend on any choice of the presentation, and hence can be denoted $f^\#(\mathcal{L})$.

## 2.3 Positivity and fiberwise density

### 2.3.1. Definition :

6

- A locale $\mathcal{L}$ is said to be positive, if whenever we can write $\mathcal{L}$ as a union of open sublocales:

$$\mathcal{L} = \bigvee_{i \in I} u_i$$

the set of indices $I$ has to be inhabited. In this case, we write $\mathcal{L} > \emptyset$.

- A locale $\mathcal{L}$ is said to be locally positive if every open sublocale can be written as a union of positive open sublocales.

If one assumes the law of excluded middle, then an open sublocale is positive if and and only if it is non-zero and every locale is locally positive (any non-zero element is the union of just itself, and the zero element is the empty union). But without the law of excluded middle this becomes a non trivial property.

2.3.2. If $X$ is a locale (preferably locally positive) we will denote by $\mathcal{O}(X)^+$ the subset of positive open sublocales of $X$.

2.3.3. Local positivity is closely related to the notion of open map:

Proposition : Let $f : \mathcal{L} \to \mathcal{M}$ be a morphism of locale, then the following conditions are equivalent:

- For any \(U\) open sublocale of \(\mathcal{L}\), its image \(f_{1}(U)\) is an open sublocale of \(\mathcal{M}\); i.e. \(f\) is an open map.
- The frame morphism \( f^{*} : \mathcal{O}(\mathcal{M}) \to \mathcal{O}(\mathcal{L}) \) has a left adjoint \( f_{\circ} \) (i.e. \( f_{\circ}(U) \leqslant V \) if and only if \( U \leqslant f^{*}(V) \)) which satisfies the additional identity:

$$f_{\circ}(U \wedge f^{*}(V)) = (f_{\circ}U) \wedge V;$$

- $\mathcal{L}$ is locally positive as a $\mathcal{M}$-locale.

Moreover in this situation, $f_{\circ}$ is the same as $f_1$ (restricted to open sublocales) and it corresponds to the internal map which associates to every $U \in \mathcal{O}(\mathcal{L})$ the $\mathcal{M}$-proposition " $U$ is positive ".

For a proof, see [2]1.6.1 and 1.6.2 for the equivalence of the first two points, and see [12] C3.1.17 for the last point.

Because of this proposition, locally positive locales are generally called "open locales". We cannot use this terminology here because we will have to speak a lot about locally positive sublocales, and "open sublocales" would have two possible meaning in this case. The name "overt" has also been proposed to avoid this confusion.

7

2.3.4. The following lemma will often be useful to prove that some locales are locally positive:

**Lemma :** *Let $X$ be a locale, and $p$ the morphism from $X$ to the point $\{*\}$. Assume that there is a basis $(b_i)_{i \in I}$ of $X$ and a collection of propositions $(w_i)_{i \in I}$ such that:*

$$w_i \Rightarrow (b_i) > \emptyset$$

$$b_i \leqslant p^* w_i$$

*Then $X$ is positive, $w_i$ is equivalent to “$b_i > \emptyset$” and an arbitrary open sublocale of $X$ is positive if and only if it contains one of the $b_i$ such that $b_i > \emptyset$.*

**Proof :**

As the $b_i$ form a basis, any $U \in \mathcal{O}(X)$ can be written as:

$$U = \bigvee_{\substack{i \in I \\ b_i \leqslant U}} b_i$$

but as $b_i \leqslant p^*(w_i) = \bigvee_{w_i} \top$ one has:

$$U = \bigvee_{\substack{i \in I \\ b_i \leqslant U}} p^*(w_i) \wedge b_i = \bigvee_{\substack{i \in I \\ b_i \leqslant U \text{ and } w_i}} b_i$$

as $w_i$ implies that $b_i$ is positive, this is an expression of $U$ as a supremum of positive open sublocales, proving that $X$ is locally positive. Now $w_i \Rightarrow b_i > \emptyset$ and as $b_i = \bigvee_{w_i} b_i$ one also has $b_i > \emptyset \Rightarrow w_i$, which proves the equivalence between $w_i$ and “$b_i$ is positive”. Finally if $U$ is positive, then from the previous expression of $U$ as a union, there exists an $i$ such that $b_i \leqslant U$ and $w_i$ hence $b_i$ is positive, and conversely if $U$ contains a positive $b_i$ then $U$ is itself positive. $\square$

**2.3.5. Proposition :** *A locale $\mathcal{L}$ is locally positive if and only if it can be defined by a Grothendieck site where each covering is inhabited. In this situation, an open $U$ of $\mathcal{L}$ is positive if and only if it contains one of the representable.*

This is essentially the localic version of [12, C3.1.19]. It can be applied to site as defined in [12, C2.1.1], that is where the cover are only assumed to satisfies the base change axiom.

8

2.3.6. **Proposition :** *Let $X$ be a locally positive locale in a topos $\mathcal{T}$ and $f : \mathcal{E} \to \mathcal{T}$ a geometric morphism. Then $f^\#(X)$ is also locally positive, and (internally in $\mathcal{E}$) an open $f^*(U) \in f^*(\mathcal{O}(X))$ is positive if and only if $f^*(U > \emptyset)$.*

# **Proof :**

If one has a site of definition $(C, J)$ for $\mathcal{L}$ in which each covering relation is inhabited then $f^*(C, J)$ also has this property and it is a site of definition for $f^\#(\mathcal{L})$. Hence this is an immediate corollary of the previous proposition. $\square$

2.3.7. Once we replace the idea of “having points” by “being positive and locally positive” to state that a locale is inhabited one can obtain a constructive version of “the axiom of choice” in the form of:

**Proposition :** *Let $I$ be a set with decidable equality and let $(X_i)_{i \in I}$ be a family of positive and locally positive locales. Then $\prod_{i \in I} X_i$ is positive and locally positive.*

Note that the hypothesis that $I$ is decidable cannot be removed, and in fact cannot be weakened at least if we want to keep a first order property. See [9, Chapter 3, 2.3.8] for more details. We are grateful to Graham Manuell for pointing out a mistake in the original proof of this proposition.

# **Proof :**

For a finite product this follows from the fact that open surjections are stable under composition and pull-back ([12, C3.1.11]). If $I$ is decidable, then as a frame $\mathcal{O}(\prod_{i \in I} X_i)$ is the directed colimits of the $\mathcal{O}(\prod_{i \in P} X_i)$ for $P \subset I$ a finite subset, and all the transition map between the $\mathcal{O}(\prod_{i \in P} X_i)$ are open surjections. We can then essentially copy the proof of [12, C3.1.22]: For each finite $P \subset I$ we have a site of definition for $\prod_{i \in P} X_i$ given by all the locally positive open sublocales and all covering relation between them. Then, because for $P \subset P' \subset I$ the transition map $\pi : \prod_{i \in P'} X_i \to \prod_{i \in P} X_i$ is an open surjection, the $\pi^*$ preserves locally positive elements and hence one can obtain a site of definition for $\mathcal{O}(\prod_{i \in P} X_i)$ by taking the direct colimits of all these sites. Similarly to what happen in the proof of [12, C3.1.22], the actual Grothendieck topology on this site is complicated to describe concretely: it is the smallest topology generated by union of the topologies on the sites for $\prod_{i \in P} X_i$. But the set of covers coming from all the $\prod_{i \in P} X_i$ already satisfies the base change axiom, that is, it is a site in the sense of Definition [12, C2.1.1], so we can apply proposition 2.3.5 to it and conclude that the product is indeed open.

$\square$

2.3.8. We also have a constructive version of the axiom of dependent choice:

**Proposition :** *Let $X$ be an inhabited set equipped with a relation $R$ such that for each $x \in X$ there exists $y \in X$ with $xRy$. Then the sublocale of $X^N$ which*

9

classifies the sequences $(x_n)$ such that for each $n$ one has $x_n R x_{n+1}$ is positive and locally positive.

This is proved in [15] as lemma $C$.

2.3.9. A geometric morphism $f : \mathcal{M} \to \mathcal{L}$ is said to be *fiberwise dense* (or to have a fiberwise dense image) if for any proposition $U$, one has the relation:

$$p^*(U) = f_* f^* p^*(U)$$

where $p$ denotes the canonical map $\mathcal{L} \to \{*\}$ and $U$ is identified with an open sublocale of $\{*\}$.

A sublocale $S \subset \mathcal{L}$ is said to be *fiberwise closed* if it is fiberwise dense in no other sublocale of $\mathcal{L}$.

2.3.10. In the presence of the law of excluded middle these are equivalent to the more classical notions of density and closeness, but in general fiberwise density only implies density, and closeness only implies fiberwise closeness. For this reason they have also been called “strongly dense” and “weakly closed”, but we prefer the terminology “fiberwise” which is more uniform, more specific and allows less confusions. This name “fiberwise” comes from the fact that, when interpreted internally in $\mathsf{Sh}(X)$ for a (nice enough) topological space $X$, it indeed corresponds to a notion of fiberwise density (and fiberwise closeness) of morphisms of locales over $X$ whereas the usual notion of density would correspond to simple density, without taking the basis into account.

Aside from this difference of terminology, these definitions and the proof of all the results stated here can be found in [12] after C1.1.22 and after C1.2.14.

Of course every sublocale $S$ admits a fiberwise closure $\overline{S}$ which is the smallest fiberwise closed sublocale containing $S$, or equivalently, the unique fiberwise closed sublocale in which $S$ is fiberwise dense.

2.3.11. In the case of locally positive locales, the fiberwise density takes the following simpler form.

**Proposition :** Let $f : X \to Y$ be a map with $X$ locally positive. Then the following conditions are equivalent:

(a) \(f\) is fiberwise dense.
(b) \(Y\) is locally positive, and for any positive open sublocale \(U\) of \(Y\), \(f^{*}(U)\) is positive.

In presence of the law of excluded middle, every locale is locally positive and a positive open sublocale is just a non-zero open sublocale. Hence the previous proposition asserts (in presence of the law of excluded middle) that $f$ is fiberwise dense if for every non zero open sublocale $f^*(U)$ is also non zero, which is a classical characterisation of a dense map.

10

2.3.12. Corollary : Let $f : X \to Y$ be a surjection with $X$ locally positive, then $Y$ is locally positive.

Proof :

A surjection is in particular a fiberwise dense map. $\square$

2.3.13. Proposition : A fiberwise dense sublocale of a locally positive sublocale is also locally positive.

2.3.14. Proposition : If $g : X \to Y$ is a fiberwise dense map between two locally positive locales, then any pull-back of $g$ by a geometric morphism is also fiberwise dense.

A counterexample to this proposition without the local positivity assumption can be found in [12] right after corollary C.1.2.16.

2.3.15. Definition : A locale $\mathcal{L}$ is said to be weakly spatial if there exists a fiberwise dense map $P \to \mathcal{L}$ with $P$ a spatial locale (or simply, with $P$ a set).

By 2.3.11, a weakly spatial locale is automatically locally positive, and a locally positive locale is weakly spatial if and only if every positive open sublocale has a point.

2.3.16. Lemma : Let $X$ be any object of the base topos, then there exists a positive locally positive locale $\mathcal{L}$, with $p$ the canonical geometric morphism from $\mathfrak{Sh}(\mathcal{L})$ to the base topos, such that $p^*X$ is the quotient of an object $I$ of $\mathfrak{Sh}(\mathcal{L})$ which has decidable equality.

Proof :

One can take $\mathcal{L}$ to be the classifying space for partial surjective maps from $\mathbb{N}$ to $X$. It is always a positive locally positive locale (see [13]V.3 just after proposition 2), and in $\mathfrak{Sh}(\mathcal{L})$ the object $p^*X$ is naturally a quotient of a subobject of $\mathbb{N}$, which is decidable. $\square$

11

**2.3.17. Proposition :** *Let $X$ be a locally positive locale (of the base topos), then there exists a topos $\mathcal{T}$ (even a locale) such that the canonical geometric morphism $p : \mathcal{T} \rightarrow \ast$ is an open surjection and such that $p^\#(X)$ is weakly spatial in $\mathcal{T}$.*

This result will be extremely important in the rest of this paper: indeed weak spatiality will play the same role as spatiality for complete metric spaces (see 3.6), and as locales descend along open surjections this result will roughly allow us to assume whenever needed that all the metric locales involved come from metric sets.

**Proof :**

Thanks to the previous lemma, one can construct a locale $\mathcal{L}$ in which one has a basis $(U_i)_{i \in I}$ of positive open sublocales of $p^\#(X)$ indexed by a set with decidable equality. By 2.3.7:

$$Y = \prod_{i \in I} U_i$$

is a positive locally positive locale, and corresponds to an open surjection (also denoted $p$) $p : \mathsf{Sh}_{\mathcal{L}}(Y) \rightarrow \mathcal{L} \rightarrow \ast$. We will now prove that $p^\#(X)$ is weakly spatial.

Internally in $\mathcal{L}$, there is a canonical map $s_i : Y \rightarrow X \times Y$ defined as the composition of the i-th projection and the inclusion of $U_i$ into $X$ on the first component and the identity of $Y$ on the second component. This defines a map of locale over $Y$:

$$s : \prod_{i \in I} Y \rightarrow X \times Y = p^\#(X)$$

which internally in $\mathsf{Sh}_{\mathcal{L}}(Y)$ gives a map $s$ from $f^*(I)$ to $p^\#(X)$ such that for each $i$, $s(i)$ is a point of $U_i$. As any positive open sublocale of $p^\#(X)$ contains one of the $U_i$, it shows that $p^\#(X)$ is weakly spatial. $\square$

## 2.4 Descent theory

Let $\mathcal{C}$ be a functor from the 2-category of toposes to the 2-category of categories, like for example the functor which sends every topos $\mathcal{T}$ to the category of internal locales of $\mathcal{T}$, and any geometric morphism $f$ to the functor $f^\sharp$. We will denote by $f^*$ the action of a geometric morphism $f$ on $\mathcal{C}$.

Let $f : \mathcal{E} \rightarrow \mathcal{T}$ be a geometric morphism, and let $c \in |\mathcal{C}(\mathcal{E})|$. A descent data on $c$ is the data of an isomorphism $\epsilon : \pi_1^*(c) \rightarrow \pi_2^*(c) \in \mathcal{C}(\mathcal{E} \times_{\mathcal{T}} \mathcal{E})$, such that if $\Delta$ denotes the diagonal map $\Delta : \mathcal{E} \rightarrow \mathcal{E} \times_{\mathcal{T}} \mathcal{E}$ then $\Delta^*(\epsilon)$ identifies with the identity map of $c$, and if $\pi_{1,2}, \pi_{1,3}$ and $\pi_{2,3}$ denote the three projections $\mathcal{E} \times_{\mathcal{T}} \mathcal{E} \times_{\mathcal{T}} \mathcal{E} \rightarrow \mathcal{E} \times_{\mathcal{T}} \mathcal{E}$ and $\pi_1, \pi_2$ and $\pi_3$ the three projections from $\mathcal{E} \times_{\mathcal{T}} \mathcal{E} \times_{\mathcal{T}} \mathcal{E}$ to $\mathcal{E}$ then one has a commutative diagram:

12

$$\begin{array}{c} \pi_1^*(c) \xrightarrow{\pi_{12}^* \epsilon} \pi_2^*(c) \\ \searrow \pi_{13}^* \downarrow \pi_{23}^* \epsilon \\ \pi_3^*(c) \end{array}$$

We define $Des(f, \mathcal{C})$ to be the category of objects of $\mathcal{C}(\mathcal{E})$ endowed with a descent data (and morphisms being the morphisms in $\mathcal{C}(\mathcal{E})$ whose pull-back along $\pi_1$ and $\pi_2$ commute to the $\epsilon$). If $c_0 \in \mathcal{C}(\mathcal{T})$ then $f^*c$ is naturally endowed with a descent data and this defines a functor from $\mathcal{C}(\mathcal{T})$ to $Des(f, \mathcal{C})$. One says that objects of $\mathcal{C}$ descend along $f$, or that $f$ is a descent morphism$^4$ for $\mathcal{C}$ if this functor induces an equivalence between $\mathcal{C}(\mathcal{T})$ and $Des(f, \mathcal{C})$.

It is for example proved in [13] that both objects and locales descend along open surjections. That is, for $\mathcal{C}(\mathcal{T}) = \mathcal{T}$ and $\mathcal{C}(\mathcal{T})$ being the category of internal locales of $\mathcal{T}$ the geometric morphisms which are open and surjective are descent morphisms.

In another language, the fact that objects of $\mathcal{C}$ descend along all open surjections, or more generally along all geometric morphisms belonging to some Grothendieck topology one the 2-category of topos exactly means that $\mathcal{C}$ is a stack for this topology.

## 2.5 Spaces of numbers

2.5.1. As mentioned in the introduction we are assuming that the base topos has a natural number object denoted by $\mathbb{N}$ (see [12, A2.5 and D5.1]). And from this natural number object one defines as usual the set $\mathbb{Z}$ of relative integers and $\mathbb{Q}$ of rational numbers with all their usual operations and properties.

2.5.2. $\mathbb{R}$ will denote the formal locale of real numbers, i.e., classifying locale of the geometric propositional theory of Dedekind real numbers (continuous real number). When it is spatial (for example in presence of the law of excluded middle) it is the set of real numbers endowed with its classical topology. In any case, it agrees with the localic completion (as we define in 3.3.12) of $\mathbb{Q}$ for the Archimedean distance. $\mathbb{C}$ denote the formal locale of complex numbers, i.e. $\mathbb{R} \times \mathbb{R}$ endowed with its usual multiplication and addition.

2.5.3. Similarly will define a locale $\overline{\mathbb{R}_+^\infty}$ in which the distance function will take value. As earlier work of C.J.Mulvey showed we only care about knowing when a distance is smaller than some rational number, hence $\overline{\mathbb{R}_+^\infty}$ will be defined as the classifying locale of the theory of $P \subset \mathbb{Q}_+^*$ such that if $q \in P$ and $q < q'$ then $q' \in P$ and if $q \in P$ then there exists $q' < q$ such that $q' \in P$.

$^4$We follow the terminology of [12], it is in fact more common to say that $f$ is an effective descent morphism.

13

As $P$ is defined as a subset of positive rational numbers, $\overleftarrow{\mathbb{R}}_+^\infty$ corresponds only to non-negative numbers, and as we do not ask $P$ to be inhabited, $\overleftarrow{\mathbb{R}}_+^\infty$ contains a point $+\infty$ (corresponding to $P = \emptyset$). The topology on $\overleftarrow{\mathbb{R}}_+^\infty$ is the topology of upper semi-continuity i.e. the basic open sublocales are the $[0, q]$ for $q$ a rational (or real) number.

2.5.4. On a topological space (or more generally in a Grothendieck topos) Dedekind real numbers correspond to continuous functions to $\mathbb{R}$, whereas points of $\overleftarrow{\mathbb{R}}_+^\infty$ correspond to non negative upper semi-continuous (possibly infinite) functions. This explains why Dedekind reals are called “continuous” real numbers, and why points of $\overleftarrow{\mathbb{R}}_+^\infty$ can be called upper semi-continuous real numbers.

## 2.6 $[X, \mathbb{R}]$ is locally positive

The goal of this subsection is to show that, when $X$ is a compact regular locale, the locale $[X, \mathbb{R}]$ is locally positive (and hence also $[X, \mathbb{C}] \simeq [X, \mathbb{R}]^2$).

If $U$ and $V$ are two open sublocales of $X$ we write $U \ll V$ if $U$ is way below $V$, i.e. if when $V \leqslant \bigvee_{i \in I} U_i$ then there exists a finite subset $J \subset I$ such that $U \leqslant \bigvee_{j \in J} U_j$. We write $U \prec V$ when $U$ is rather below $V$, i.e. when $V \vee \neg U = X$, where $\neg U$ is the biggest open sublocale disjoint from $U$. A locale $X$ is regular when $\forall V \in \mathcal{O}(X)$, $V = \bigvee_{U \prec V} U$. In a compact regular locale the two relations $\prec$ and $\ll$ are equivalent.

In [10] one can find a description of the geometric theory classified by $[X, \mathbb{R}]$. This description shows that the open sublocales of the form $(U, q, q') = \{f | U \ll f^*([q, q'])\}^5$ for $U$ an open sublocale of $X$ and $q, q'$ two rational numbers form a pre-basis of the topology of $[X, \mathbb{R}]$.

As:

$$U \ll f^*([q, q']) \Leftrightarrow (U \ll f^*([q, +\infty])) \wedge (U \ll f^*([-\infty, q'])),$$

$[X, \mathbb{R}]$ has a basis of open sublocales of the form

$$B = \left( \bigwedge_{i=1}^n (U_i, u_i, -) \right) \wedge \left( \bigwedge_{j=1}^m (V_j, v_j, +) \right), \quad (1)$$

where $U_i$ and $V_i$ are open sublocales of $X$, $u_i$ and $v_i$ are rational numbers, $(U_i, u_i, -)$ denotes $\{f | U \ll f^*([-\infty, u_i])\}$ and $(V_j, v_j, +)$ denotes $\{f | V_j \ll f^*([v_j, +\infty])\}$.

$^5$Of course, we do not mean the set of points $f$ of $[X, \mathbb{R}]$ satisfying this properties, but the open sublocale classifying such functions $f$.

14

2.6.1. **Definition :** *An open sublocale of the form given in (1) will be called a basic sublocale. A basic sublocale will be said to be admissible if it satisfies the following condition:*

$$\forall i \in 1, \dots, n, j \in 1, \dots, m, (u_i \leq v_j) \Rightarrow (\neg U_i) \vee (\neg V_j) = X.$$

We will show in 2.6.5 that a basic open is admissible if and only if it is positive, hence the property of being admissible is indeed a property of the open sublocale $B$, and not of its representation. But, while we have not proven this, we will assume that each time we consider a basic open $B$, it is given with a representation in the form of (1) and say that it is admissible if and only if its representation is.

2.6.2. The following lemma is in some sense a constructive form of Urysohn's lemma, asserting that compact regular locales are in fact completely regular.

**Lemma :** *Let $X$ be a compact regular locale, and let $U, V$ be two open sublocales of $X$ such that $U \ll V$. Then there exists a positive locally positive locale $\mathcal{L}$, such that in the logic of $\mathcal{L}$ there exists a continuous function from $X$ to $[0, 1]^6$ such that $f$ restricted to $U$ is zero and $f$ is constant equal to one on $\neg V$.*

# **Proof :**

The classical proof of the Urysohn lemma for locale (see for example [17, Chap. XIV]) goes as follows: In a compact regular locale the relation $U \prec V$ is equivalent to the relation $U \ll V$. The relation $\prec$ in general does not interpolate, but in a locally compact locale the relation $\ll$ always does, ie if $a \ll b$ then there exists $c$ such that $a \ll c \ll b$. In particular in a compact regular space the relation $\prec$ interpolates and (using the axiom of choice) one can construct a $\mathbb{Q}$-indexed family of open subspaces $U_q$ such that $U_0 = U$, $U_1 = V$ and if $q < q'$ then $U_q \prec V_{q'}$, and we define $U_q = \emptyset$ when $q < 0$ and $U_q = X$ when $q > 1$. This defines a 'scale' (see [17] XIV.5.2) which in turns defines a function from $X$ to $[0, 1]$ with the required property (see [17]XIV.5.2.2).

The only part of the previous proof which is not constructive is the application of the axiom of dependent choice to construct the sequence $U_q$. By applying 2.3.8 one can construct a locale $\mathcal{L}$ in which there exists such a sequence and then finish the proof in the logic of $\mathcal{L}$ by constructing the function we are looking for. The only thing we need to check is that if $x \prec y$ then their pull-back to $\mathcal{L}$ also satisfy this identity, but as it can equivalently be defined by ' $\exists c$ such that $x \wedge c = \emptyset$ and $c \vee y = \top$ ' this is immediate.

□

$^{6}$That is externally a function from $\mathcal{L} \times X$ to $[0, 1]$.

15

**2.6.3. Proposition :** If $X$ is compact completely regular and $B$ is an admissible basic sublocale of $[X, \mathbb{R}]$, then $B$ has a point. If $X$ is just compact regular and $B$ is admissible then $B$ is positive.

**Proof :**

Assume that $X$ is completely regular, and let us first remark that when $X$ is a compact completely regular locale, if $U$ and $V$ are two open sublocales of $X$ such that $(\neg U) \vee (\neg V) = X$, then, as $U \ll (\neg V)$, it is possible to construct a continuous function $f : X \rightarrow [0, 1]$ such that $f$ restricted to $U$ is constant equal to 0 and $f$ restricted to $V \subseteq \neg \neg V$ is constant equal to 1.

Now let

$$B = \left( \bigwedge_{i=1}^n (U_i, u_i, -) \right) \wedge \left( \bigwedge_{j=1}^m (V_j, v_j, +) \right)$$

be an admissible basic sublocale of $[X, \mathbb{R}]$.

Let $\epsilon$ be a positive rational number smaller than all the positive differences between two numbers of the form $u_i$ or $v_i$. For each couple $(i, j)$ we choose a continuous function $f_{i,j} : X \rightarrow \mathbb{R}$ such that:

- If $v_j < u_i$ then $f_{i,j}$ is the constant function equal to $\frac{v_j \leq u_i}{2}$
- If $u_i \leq v_j$ then $(\neg U_i) \vee (\neg V_j) = X$ and $f_{i,j}$ is a continuous function such that $f$ is constant equal to $u_i - \epsilon$ on $U_i$, $f$ is constant equal to $v_j + \epsilon$ on $V_j$ and $f$ takes value in $[u_i - \epsilon, v_j + \epsilon]$. (such a function exists by the previous remark).

Then,

$$f = \max_{1 \leq j \leq m} \min_{1 \leq i \leq n} f_{i,j},$$

is a point of $B$. Indeed:

- Let $i \in \{1, \dots, n\}$, then (on $U_i$), since for each $j$, $f_{i,j}$ is smaller than $u_i - \frac{\epsilon}{2}$, the infimum $\inf_{i'=1}^n f_{i',j}$ is smaller than $u_i - \frac{\epsilon}{2}$ and $f$ smaller than $u_i - \frac{\epsilon}{2}$ on $U_i$ as a (finite) supremum of a quantities smaller than $u_i - \frac{\epsilon}{2}$.
- Let $j \in \{1, \dots, m\}$, then (on $V_j$), as for each $i$, $f_{i,j}$ is greater than $v_j + \frac{\epsilon}{2}$, the infimum $\inf_{i=1}^n f_{i,j}$ is greater than $v_j + \frac{\epsilon}{2}$. And $f$ is greater than $v_j + \frac{\epsilon}{2}$ on $V_j$.

This concludes the proof when $X$ is completely regular. We now assume that $X$ is only regular. Then all the functions $f_{i,j}$ we used in the first part can be instead constructed in the logic of positive locally positive locales $\mathcal{L}_{i,j}$ using 2.6.2. The product $\mathcal{L}$ of all these $\mathcal{L}_{i,j}$ is also positive and locally positive by 2.3.7, and in the logic of $\mathcal{L}$, all the functions $f_{i,j}$ we used in the first part exist and hence one can construct the function $f$ which is going to be a point of $B$ in the logic of $\mathcal{L}$ exactly as we did above. This defines a map $\mathcal{L} \rightarrow B$ and, as $\mathcal{L}$ is positive, this proves that $B$ is positive and concludes the proof. $\square$

16

2.6.4. **Lemma :** Let $p$ denote the canonical map from $[X, \mathbb{R}]$ to the point. Let $B$ be a basic sublocale then one has:

$$B \leqslant p^*(\text{“}B \text{ is admissible ”})$$

where we identify the proposition “$B$ is admissible” with a subset of $\{*\}$ and hence with an open sublocale of the point.

# **Proof :**

We will prove that in the theory classified by $[X, \mathbb{R}]$ (describe in [10]) the proposition asserting that $B$ is admissible can be deduced from the proposition corresponding to $B$.

Indeed, let $B$ be as in (1) and let $i$ and $j$ such that $u_i \leqslant v_j$. one has:

$$\begin{aligned} & B \vdash (U_i \ll f^*(\lceil -\infty, u_i[\rceil)) \wedge (V_j \ll f^*(\lceil v_j, +\infty[\rceil)), \\ & (U_i \ll f^*(\lceil -\infty, u_i[\rceil)) \vdash \bigvee_{U_i \ll U} (U \ll f^*(\lceil -\infty, u_i[\rceil)) \end{aligned}$$

and

$$(U \ll f^*(\lceil -\infty, u_i[\rceil)) \wedge (V \ll f^*(\lceil v_j, +\infty[\rceil)) \vdash (U \wedge V) = \emptyset.$$

Hence

$$B \vdash \bigvee_{\substack{U_i \ll U \\ V_j \ll V}} (V \wedge U = \emptyset)$$

but for any $U_i \ll U$ and $V_j \ll V$ if $(V \wedge U = \emptyset)$ then $\neg U \vee \neg V = X$ because

$$\begin{aligned} X &= (\neg U_i \vee U) \wedge (\neg V_j \vee V) \\ &= (\neg U_i \wedge \neg V_j) \vee (\neg U_i \wedge V) \vee (U \wedge \neg V_j) \vee (U \wedge V) \end{aligned}$$

The last term of the union can be removed by assumption, and we can duplicate the first, obtaining

$$\begin{aligned} X &= [(\neg U_i \wedge \neg V_j) \vee (\neg U_i \wedge V)] \vee [(U \wedge \neg V_j) \vee (\neg U_i \wedge \neg V_j)] \\ &= [(\neg U_i) \wedge (\neg V_j \vee V)] \vee [(\neg V_j) \wedge (\neg U_i \vee U)] \\ &= \neg U_i \vee \neg V_j \end{aligned}$$

Hence $B \vdash \neg U_i \vee \neg V_j$. As this is true for any $(i, j)$ such that $u_i \leqslant v_j$ we get the desired result.

$\square$

17

2.6.5. Combining all these results we obtain:

**Theorem :** If $X$ is a compact regular locale, then a basic sublocale $B$ of $[X, \mathbb{R}]$, is admissible if and only it is positive. In particular, $[X, \mathbb{R}]$ is locally positive and the admissible basic sublocales form a basis of positive open sublocales.

# **Proof :**

It suffices to apply Lemma 2.3.4 with $b_i$ the basic open sublocales and $w_i$ the propositions “$b_i$ is admissible”. Proposition 2.6.3 shows that $w_i$ implies $b_i > \emptyset$ and 2.6.4 is exactly the second condition. $\square$

2.6.6. We also obtain the following

**Proposition :** Let $X$ be a compact regular locale, $X$ is completely regular if and only if $[X, \mathbb{R}]$ is weakly spatial.

# **Proof :**

If $X$ is completely regular, then 2.6.3 shows that each admissible has a point. But by 2.6.5 they form a basis of positive open, hence this proves that points of $[X, \mathbb{R}]$ are dense. Conversely, if $[X, \mathbb{R}]$ is weakly spatial and $U, V$ are two open sublocales of $X$ such that $U \prec V$, then there exists $W$ such that $U \prec W \prec V$ and the basic open:

$$
B = (U, 0, -) \wedge (\neg W, 1, +)
$$

is admissible because $\neg U \vee \neg\neg W \geqslant \neg U \vee W = X$. Hence it is positive and hence it has a point. But a point of $B$ is a function from $X$ to $\mathbb{R}$ such that $f$ is negative on $U$ and greater than one on $\neg W$. As $\neg W \vee V = X$ the function $f$ shows that $U$ is “completely below $V$”, and this proves that $X$ is completely regular. $\square$

## 3 Constructive theory of metric locales

### 3.1 Pre-metric locale

As our major concern is the study of localic Banach spaces, we will only consider metrics on a locale which are defined by a distance function. However, it should be noted that the point 9 of the series of propositions given in 3.1.4 shows that one can specify a distance by giving the diameter $\delta(U)$ of each open sublocale $U$, and the classical theory$^7$ which can be found for example in the chapter XI of [17] suggests that a definition by diameters should also be possible.

7Which has not been done constructively yet as far the author knows.

18

# 3.1.1. **Definition :** *A pre-distance $d$ on a locale $X$ is a function*

$$d : X \times X \rightarrow \overleftarrow{\mathbb{R}_+^\infty}$$

*which is symmetric ($d(x, y) = d(y, x)$), satisfies the triangular inequality $d(x, y) \leqslant d(x, z) + d(z, y)$ and such that $d(x, x) = 0$*

*A pre-metric locale is a locally positive locale $X$ endowed with a pre-distance.*

We insist on the fact that our pre-metric locale are always assumed to be locally positive. We do not know exactly which parts of the theory of metric locales it is possible to develop without this hypothesis (without it, one should at least avoid everything which uses the construction $B_q \mathcal{L}$ of 3.1.2 but it seems that what is left is relatively well behaved without it). In any case, the theory is at least easier, and probably nicer with this local positivity assumption. Theorem 2.6.5 shows that this case is enough for the Gelfand duality, and as locale positivity descend along open surjections and is automatic for metric sets it is also enough to obtain good descent properties.

Of course, the formulas $d(x, y) = d(y, x)$ and $d(x, y) \leqslant d(x, z) + d(z, y)$ have to be interpreted in a diagrammatic way or in terms of generalized points. In particular, if we define

$$\Delta_q := \{(x, y) | d(x, y) < q\} = d^* \left( \overleftarrow{[0, q]} \right)$$

then the symmetry means that $\Delta_q$ is invariant by exchange of the two factors, $d(x, x) = 0$ means that for all $q$, $\Delta_q$ contains the diagonal embeddings of $X$, and finally the triangular inequality means that:

$$\pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) \leqslant \pi_{1,3}^*(\Delta_{q+q'})$$

Where $\pi_{i,j}$ denote the various projections from $X^3$ to $X^2$.

# 3.1.2. **Definition :** *Let $X$ be a pre-metric locale, and $\mathcal{L}$ and $\mathcal{M}$ be two sublocales of $X$. then*

- *We say that $\delta(\mathcal{L}) < q$ if $\mathcal{L} \times \mathcal{L} \subseteq \Delta_{q'}$ for some positive rational number $q' < q$. One easily sees that $\delta(\mathcal{L})$ is indeed an element of $\overleftarrow{\mathbb{R}_+^\infty}$;*
- *We say that $\mathcal{L} \triangleleft_q \mathcal{M}$ if $\pi_1^*(\mathcal{L}) \wedge \Delta_q \leqslant \pi_2^*(\mathcal{M})$. We say that $\mathcal{L} \triangleleft \mathcal{M}$ if $\mathcal{L} \triangleleft_q \mathcal{M}$ for some positive rational $q$;*
- *if $q$ is a positive rational number then $B_q \mathcal{L} = (\pi_2)! (\pi_1^*(\mathcal{L}) \wedge \Delta_q)$.*

These should be interpreted as: $\delta$ is the diameter of a sublocale, $B_q$ is the $q$ neighborhood of a sublocale and $\mathcal{L} \triangleleft_q \mathcal{M}$ means that the $q$ neighborhood of $\mathcal{L}$ is included in $\mathcal{M}$.

19

3.1.3. We will denote by $\mathcal{O}(X)^{<q}$ the set of open sublocales $U$ of $X$ such that $\delta(U) < q$, and $\mathcal{O}(X)^{+,<q}$ will be simply the subset $\mathcal{O}(X)^+ \cap \mathcal{O}(X)^{<q}$ of positive elements of $\mathcal{O}(X)^{<q}$.

# 3.1.4. Proposition :

1. $B_q \mathcal{L} \subseteq \mathcal{M}$ if and only if $\mathcal{L} \triangleleft_q \mathcal{M}$.

2. If $\mathcal{L} \subseteq \mathcal{M}$ then $\delta(\mathcal{L}) \leqslant \delta(\mathcal{M})$.

3. If $\mathcal{L} \triangleleft \mathcal{M}$ then $\mathcal{L} \subseteq \mathcal{M}$. In particular for all positive rational numbers $q$ one has $\mathcal{L} \subseteq B_q \mathcal{L}$.

4. If $\mathcal{L} \triangleleft_q \mathcal{M}$ and $\mathcal{L}' \triangleleft_q \mathcal{M}'$ then $\mathcal{L} \wedge \mathcal{L}' \triangleleft_q \mathcal{M} \wedge \mathcal{M}'$ and $\mathcal{L} \vee \mathcal{L}' \triangleleft_q \mathcal{M} \vee \mathcal{M}'$.

5. $\delta\left(\bigvee_{i \in I} \mathcal{L}_i\right) = \sup_{i,j \in I} \delta(\mathcal{L}_i \vee \mathcal{L}_j)$

6. If $\mathcal{L} \wedge \mathcal{M}$ contains a positive and locally positive sublocale then $\delta(\mathcal{L} \vee \mathcal{M}) \leqslant \delta(\mathcal{L}) + \delta(\mathcal{M})$.

7. Let $(\mathcal{L}_i)_{i=0 \dots n}$ be a finite sequence of sublocales such that for all $i$, $\mathcal{L}_{i-1} \wedge \mathcal{L}_i$ contains a positive and locally positive sublocale then:

$$\delta\left(\bigvee_{i=0}^n \mathcal{L}_i\right) \leqslant \sum_{i=0}^n \delta(\mathcal{L}_i)$$

8. For any $q > 0$, $\mathcal{O}(X)^{<q}$ is a basis of the topology of $X$.

9. $\Delta_q = \bigvee_{U \in \mathcal{O}(X)^{<q}} U \times U$

10. If $\mathcal{L}$ is locally positive, then

$$B_q \mathcal{L} = \bigvee_{\substack{U \in \mathcal{O}(X)^{<q} \\ U \wedge \mathcal{L} > \emptyset}} U.$$

In particular, if $\mathcal{L}$ is locally positive, $B_q \mathcal{L}$ is open.

11. If $\mathcal{L}$ is locally positive then

$$B_{q'}(B_q(\mathcal{L})) \subseteq B_{q+q'}(\mathcal{L}).$$

12. If $\mathcal{L}$ is locally positive then $\delta(B_q \mathcal{L}) \leqslant 2q + \delta(\mathcal{L})$.

# Proof :

1. This is simply the adjunction between $(\pi_2)_!$ and $(\pi_2)^*$.

20

2. If $\mathcal{L} \subseteq \mathcal{M}$ and if $\delta(\mathcal{M}) < q$ then there exists a positive rational $q' < q$ such that $\mathcal{L} \times \mathcal{L} \subseteq \mathcal{M} \times \mathcal{M} \subseteq \Delta_{q'}$ hence $\delta(\mathcal{L}) < q$.

3. Assume that $\pi_1^*(\mathcal{L}) \wedge \Delta_q \subseteq \pi_2^*(\mathcal{M})$ for some positive rational number $q$, and let $i: X \to X \times X$ be the diagonal embedding, then:

$$i^*(\pi_1^*(\mathcal{L}) \wedge \Delta_q) \subseteq i^*\pi_2^*(\mathcal{M}) = \mathcal{M}$$

And:

$$i^*(\pi_1^*(\mathcal{L}) \wedge \Delta_q) = i^*\pi_1^*(\mathcal{L}) \wedge i^*\Delta_q = \mathcal{L} \wedge X = \mathcal{L}$$

hence $\mathcal{L} \subseteq \mathcal{M}$. The second part of the result then follows from the fact that as $B_q\mathcal{L} \subseteq B_q\mathcal{L}$, one has $\mathcal{L} \triangleleft_q B_q\mathcal{L}$.

4. Assume that $\pi_1^*\mathcal{L} \wedge \Delta_q \subseteq \pi_2^*\mathcal{M}$ and that $\pi_1^*\mathcal{L}' \wedge \Delta_q \subseteq \pi_2^*\mathcal{M}'$, then:

$$\pi_1^*(\mathcal{L} \wedge \mathcal{L}') \wedge \Delta_q = \pi_1^*(\mathcal{L}) \wedge \Delta_q \wedge \pi_1^*(\mathcal{L}') \wedge \Delta_q \subseteq \pi_2^*(\mathcal{M}) \wedge \pi_2^*(\mathcal{M}')$$

hence $\mathcal{L} \wedge \mathcal{L} \triangleleft_q \mathcal{M} \wedge \mathcal{M}$.

And for the union:

$$\begin{array}{rcl} \pi_1^*(\mathcal{L} \vee \mathcal{L}') \wedge \Delta_q & = & (\pi_1^*(\mathcal{L}) \vee \pi_1^*(\mathcal{L}')) \wedge \Delta_q \\ & = & (\pi_1^*\mathcal{L} \wedge \Delta_q) \vee (\pi_1^*\mathcal{L}' \wedge \Delta_q) \\ & \subseteq & \pi_2^*(\mathcal{M}) \vee \pi_2^*(\mathcal{M}'), \end{array}$$

which gives the result.

The fact that intersections distribute over finite unions of sublocales and that pull-backs preserve finite unions of sublocales can be found in [12] C1.1.15 and C.1.19, but formulated in terms of frames instead of locales (i.e. union of sublocales correspond to intersection of nuclei, and pull-back of a sublocale to a pushout).

5. Clearly, $\sup_{i,j \in I} \delta(\mathcal{L}_i \vee \mathcal{L}_j) \leqslant \delta(\bigvee_i \mathcal{L}_i)$ because $\mathcal{L}_i \vee \mathcal{L}_j \subseteq \bigvee_i \mathcal{L}_i$. Let $q$ such that $\sup_{i,j \in I} \delta(\mathcal{L}_i \vee \mathcal{L}_j) < q$ i.e. there exists $q' < q$ such that for all $i, j$, $\delta(\mathcal{L}_i \vee \mathcal{L}_j) < q'$. But as

$$\left( \bigvee_{i \in I} \mathcal{L}_i \right) \times \left( \bigvee_{j \in I} \mathcal{L}_j \right) = \bigvee_{i,j} \mathcal{L}_i \times \mathcal{L}_j$$

and for all $i, j$, $\mathcal{L}_i \times \mathcal{L}_j \subseteq \Delta_{q'}$, one obtains

$$\left( \bigvee_{i \in I} \mathcal{L}_i \right) \times \left( \bigvee_{j \in I} \mathcal{L}_j \right) \subseteq \Delta_{q'},$$

which concludes the proof.

21

6. Assume that $\mathcal{L} \times \mathcal{L} \subseteq \Delta_q$ and $\mathcal{M} \times \mathcal{M} \subseteq \Delta_{q'}$, we will prove that, under the assumption of the proposition, $(\mathcal{L} \vee \mathcal{M}) \times (\mathcal{L} \vee \mathcal{M}) \subseteq \Delta_{q+q'}$.

As $(\mathcal{L} \vee \mathcal{M}) \times (\mathcal{L} \vee \mathcal{M}) = (\mathcal{L} \times \mathcal{L}) \vee (\mathcal{L} \times \mathcal{M}) \vee (\mathcal{L} \times \mathcal{M}) \vee (\mathcal{M} \times \mathcal{M})$ and $(\mathcal{L} \times \mathcal{L})$ and $(\mathcal{M} \times \mathcal{M})$ are already known to be subsets of $\Delta_{q+q'}$, we only have to prove it for $(\mathcal{L} \times \mathcal{M})$ and $(\mathcal{M} \times \mathcal{L})$. In $X^3$ one has:

$$\begin{array}{rcl} \mathcal{M} \times (\mathcal{L} \wedge \mathcal{M}) \times \mathcal{L} & \subseteq & \pi_{1,2}^*(\mathcal{M} \times \mathcal{M}) \wedge \pi_{2,3}^*(\mathcal{L} \times \mathcal{L}) \quad \subseteq \quad \pi_{1,2}^*(\Delta_q') \wedge \pi_{2,3}^*(\Delta_q) \\ & & \subseteq \pi_{1,3}^*(\Delta_{q'+q}) \end{array}$$

Applying $(\pi_{1,3})_!$ yields the result because as $(\mathcal{L} \times \mathcal{M})$ contains some positive and locally positive sublocale, the projection $\pi_{1,3}$ from $\mathcal{L} \times (\mathcal{L} \wedge \mathcal{M}) \times \mathcal{M}$ to $\mathcal{L} \times \mathcal{M}$ is a surjection.

7. It is immediate by induction on $n$ using the previous point.

8. Thanks to the point 2, it is enough to check that $\mathcal{O}(X)^{<q}$ covers $X$. Take a covering of $\Delta_{q/2}$ by open sublocales of the form $U_i \times V_i$, then pulling back along the diagonal embeddings of $X$ into $\Delta_{q/2}$ one has:

$$X = \bigvee_i U_i \wedge V_i$$

but $(U_i \wedge V_i)^2 \leqslant U_i \times V_i \leqslant \Delta_{q/2}$ hence $\delta(U_i \wedge V_i) < q$ which concludes the proof.

9. Thanks to the previous point, for any $q' < q$, $\Delta_{q'}$ can be written as a union of $U_i \times V_i$ with $\delta(U_i) < q'$ and $\delta(V_i) < q'$. If $U_i \times V_i \subseteq \Delta_{q'}$, then so does $V_i \times U_i$, and hence, in our situation:

$$(U_i \cup V_i)^2 = (U_i \times U_i) \cup (V_i \times U_i) \cup (U_i \times V_i) \cup (V_i \times V_i) \subseteq \Delta_{q'}$$

Hence $\delta(U_i \cup V_i) < q$ and the $(U_i \cup V_i)^2$ cover $\Delta_{q'}$. This being done for an arbitrary $q' < q$, these open sublocales also cover $\Delta_q$, because as the $\Delta_q$ are defined by a function from $X \times X$ to $\overleftarrow{\mathbb{R}}^\infty$ one has

$$\Delta_q = \bigvee_{q' < q} \Delta_{q'}$$

10. Applying the definition of $B_q V$ using that $\pi_1^*(\mathcal{L}) = \mathcal{L} \times X$ and the previous point gives directly

$$B_q \mathcal{L} = (\pi_2)_! \left( \bigvee_{\delta(U) < q} (\mathcal{L} \wedge U) \times U \right) = \bigvee_{\substack{\delta(U) < q \\ \mathcal{L} \wedge U > \emptyset}} U.$$

11. From the previous point

$$B_q(B_{q'} \mathcal{L}) = \bigvee_{\substack{v \in \mathcal{O}(X) < q \\ v \wedge B_{q'} \mathcal{L} > \emptyset}} v$$

22

But, still by the previous point, an open sublocale $v$ of $X$ satisfies $v \wedge B_{q'}\mathcal{L} > \emptyset$ if and only if there exists $v' \in \mathcal{O}(X)^{<q'}$ such that $v' \wedge \mathcal{L} > \emptyset$ and $v \wedge v' > \emptyset$. For any open sublocale of this sort, one has $\delta(v \vee v') < q + q'$ by point 6. Hence $v \vee v'$ is a positive open sublocale such that $\delta(v \vee v') < q + q'$ and $(v \vee v') \wedge \mathcal{L} > \emptyset$. In particular $v \leqslant v \vee v' \leqslant B_{q+q'}\mathcal{L}$.

This proves that $B_q(B_{q'}\mathcal{L}) \leqslant B_{q+q'}\mathcal{L}$.

12. From point 10 one has

$$B_q\mathcal{L} = \bigvee_{\substack{v \in \mathcal{O}(X) < q \\ v \wedge \mathcal{L} > \emptyset}} v.$$

Hence from point 5 one has

$$\delta(B_q\mathcal{L}) = \sup_{\substack{v, v' \in \mathcal{O}(X) < q \\ v \wedge \mathcal{L}, v' \wedge \mathcal{L} > \emptyset}} \delta(v \vee v').$$

But for any two such $v, v'$ one has by point 7: $\delta(v \vee v') \leqslant \delta(v \vee v' \vee \mathcal{L}) \leqslant \delta(\mathcal{L}) + \delta(v) + \delta(v') \leqslant \delta(\mathcal{L}) + 2q$. One obtains the result by taking the supremum.

3.1.5. Usually, the distance function $d: X \times X \to \overleftarrow{\mathbb{R}_+^\infty}$ is expected to be in fact a continuous map from $X \times X$ to $\mathbb{R}$, and not only a semi-continuous map as our definition of distance suggest it. The reason for our choice is that we know (see for example [5]) that the norm on a Banach space has to take value in $\overleftarrow{\mathbb{R}_+^\infty}$, even if we want to think of it as a function which is continuous$^8$. Classically, the continuity is a consequence of the triangular inequality, and the following proposition gives a constructive interpretation of this result, restoring a form of "fiberwise continuity" of $d$.

Proposition: Let $\overline{\Delta_q}$ be the fiberwise closure of $\Delta_q$ in $X \times X$. Then for all $q < q'$ one has $\overline{\Delta_q} \subseteq \Delta_{q'}$.

Proof:

Let $q'$ be a rational such that $q < q'$ and let $\epsilon = \frac{q' - q}{2}$. As $\Delta_q$ is by definition fiberwise dense in $\overline{\Delta_q}$, Proposition 2.3.11 implies that $\overline{\Delta_q}$ is locally positive, and in particular one can write that

$$\overline{\Delta_q} \leqslant \bigvee_{\substack{v, v' \in \mathcal{O}(X) < \epsilon \\ v \times v' \wedge \overline{\Delta_q} > \emptyset}} v \times v'.$$

But, still by 2.3.11 and by fiberwise density of $\Delta_q$ in $\overline{\Delta_q}$, for any two such $v, v'$ one has $v \times v' \wedge \Delta_q > \emptyset$ and hence there exists $U$ such that $\delta(U) < q$ and $(v \times v') \wedge (U \times U)$ is positive. This implies that $v \wedge U$ and $v' \wedge U$ are positive and hence, by point 7 of 3.1.4, that $\delta(v \vee v') \leqslant \delta(v) + \delta(v') + \Delta(U) < q + 2\epsilon = q'$.

$^8$as opposed to semi-continuous.

23

Therefore,

$$v \times v' \subseteq (v \vee v') \times (v \vee v') \subseteq \Delta_{q'},$$

and this concludes the proof.

☐

3.1.6. Definition : Let $X$ be a pre-metric locale, we will say that $X$ has a continuous distance if the pre-distance function $d : X \times X \to \overleftarrow{\mathbb{R}_+^\infty}$ internally corresponds to a continuous real number, i.e. if the pre-distance function factors into $X \times X \to \overline{\mathbb{R}_+^\infty} \to \overleftarrow{\mathbb{R}_+^\infty}$. In this situation we define $\Theta_q$ to be the open sublocale of $X \times X$ corresponding to $\{(x, y) | d(x, y) > q\}$.

3.1.7. Assuming the law of excluded middle, we indeed obtain continuity:

Proposition : Assuming the law of excluded middle in the base topos, any pre-metric locale has a continuous distance.

Proof :

If one assumes the law of excluded middle in the base topos then any fiberwise closed sublocale is in fact a closed sublocale. In particular, there exists open sublocales $\Theta'_q$ of $X \times X$, which are the complementary open sublocales of the (closed) sublocales $\overline{\Delta_q}$. From the fact, proved in 3.1.5 that for any $q < q'$ one has the relation

$$\Delta_q \leqslant \overline{\Delta_q} \leqslant \Delta_{q'}$$

and we deduce

$$\Delta_q \wedge \Theta'_q = \emptyset$$

$$\Delta_{q'} \vee \Theta'_q = X \times X$$

and $\overline{\Delta_q} \leqslant \overline{\Delta_{q'}}$ gives $\Theta'_q \geqslant \Theta'_{q'}$.

If we define, $\Theta_q = \bigvee_{q < q'} \Theta'_{q'}$, then $\Delta_q$ and $\Theta_q$ define a map from $X \times X$ to $\overline{\mathbb{R}_+^\infty}$ which yields the desired factorisation. ☐

24

3.1.8. Proposition : Let $f : X \to Y$ be a map between two pre-metric locales. Then the following conditions are equivalent:

- (a) For any positive rational $q$, $\Delta_q \subseteq (f \times f)^*(\Delta_q)$
- (b) For any locally positive sublocale $\mathcal{L}$ of $X$, $\delta(f_!\mathcal{L}) \leqslant \delta(\mathcal{L})$.
- (c) For any $U \in \mathcal{O}(X)^{<q_1}$, $v_1 \in \mathcal{O}(Y)^{<q_2}$, $v_2 \in \mathcal{O}(Y)^{<q_3}$ such that $f^*(v_1) \wedge U$ and $f^*(v_2) \wedge U$ are positive, one has $\delta(v_1 \vee v_2) < q_1 + q_2 + q_3$.
- (d) For any $U \in \mathcal{O}(X)$ and any positive rational $q$:

$$\delta(B_q f_! U) \leqslant \delta(U) + 2q.$$

- (e) For any open sublocale $U$ of $X$ such that $\delta(U) < q$ there exists an open sublocale $V$ of $Y$ such that $\delta(V) < q$ and $U \subseteq f^*(V)$.

A map satisfying these conditions is called a metric map.

Of course, condition (a) is the point free formulation of the usual $d(f(x), f(y)) \leqslant d(x, y)$.

Proof :

- (a) $\Rightarrow$ (b) Let $q$ such that $\delta(\mathcal{L}) < q$, i.e. there exists $q' < q$ such that $\mathcal{L} \times \mathcal{L} \subseteq \Delta_{q'}$. Hence,

$$\mathcal{L} \times \mathcal{L} \subseteq (f \times f)^*(\Delta_{q'})$$

This proves that the image $(f \times f)_!(\mathcal{L} \times \mathcal{L})$ in $X \times X$ is included in $\Delta_{q'}$. Unfortunately, as a product of surjections may fail to be a surjection, it is not enough to conclude directly that $f_!(\mathcal{L}) \times f_!(\mathcal{L}) \subseteq \Delta_{q'}$. But we can still conclude using the fact that as $\mathcal{L}$ and $f_!(\mathcal{L})$ are both locally positive, then by 2.3.14 (applied twice) the map $f : \mathcal{L} \times \mathcal{L} \to f_!(\mathcal{L}) \times f_!(\mathcal{L})$ is always fiberwise dense. This implies that $\Delta_{q'}$ is fiberwise dense in $f_!(\mathcal{L}) \times f_!(\mathcal{L})$, and by 3.1.5 that:

$$f_!(\mathcal{L}) \times f_!(\mathcal{L}) \subseteq \overline{\Delta_{q'}} \subseteq \Delta_q$$

which concludes the proof.

- (b) $\Rightarrow$ (c) by 2.3.12 $\mathcal{L} = f_!(U)$ is locally positive because $U$ is and $f : U \to f_!(U)$ is a surjection. Also, $\delta(f_!(U)) < q_1$ by (b). Hence one obtains (c) by applying point 7 of 3.1.4 (with n=2), together with the fact that $f^*v \wedge U > \emptyset$ is equivalent to $v \wedge f_!U > \emptyset$ because $f : U \to f_!U$ is a surjection and hence in particular a fiberwise dense map.

- (c) $\Rightarrow$ (d) One has

$$B_q f_! U = \bigvee_{\substack{v \in \mathcal{O}(Y)^{<q} \\ f^*(v) \wedge U > \emptyset}} v$$

The same argument as given for point 12 of 3.1.4 allow one to conclude.

25

$(d) \Rightarrow (e)$ If $\delta(U) < q$ then there exists a positive $\epsilon$ such that $\delta(U) < q - 2\epsilon$. Take $V = B_\epsilon f_U$ yields the result as $U \leqslant f^* f_U \leqslant f^* B_\epsilon f_U = f^* V$.

$(e) \Rightarrow (a)$ Using $(e)$ one gets immediately the inclusion

$$\Delta_q = \bigvee_{U \in \mathcal{O}(X) < q} U \times U \subseteq \bigvee_{V \in \mathcal{O}(Y) < q} f^*(V) \times f^*(V) = (f \times f)^*(\Delta_q)$$

$\square$

3.1.9. Proposition : Let $f : X \to Y$ be a map between two pre-metric locales, let $\epsilon$ and $\eta$ be two positive rational numbers, then the following conditions are equivalent:

(a) \(\Delta_{\eta}\leqslant (f\times f)^{*}\Delta_{\epsilon}\)
(b) If \(U\in \mathcal{O}(X)\) and \(\delta (U) <   \eta\) then \(\delta (f_1(U)) <   \epsilon\)
(c) If \(U \in \mathcal{O}(X)\) and \(\delta(U) < \eta\) then there exists \(V \in \mathcal{O}(Y)\) such that \(\delta(V) < \epsilon\) and \(U \leqslant f^{*}(V)\).

The point of this proposition is to define a uniform map:

Definition : One says that a map $f$ is a uniform map if for all $\epsilon$ there exists $\eta$ satisfying the conditions of the previous proposition.

Proof :

The proof essentially follows the same lines as the proof of 3.1.8:

\((a)\Rightarrow (b)\) The argument for \((a)\Rightarrow (b)\) in 3.1.8 applies in exactly the same way here.
\((b)\Rightarrow (c)\) If \(\delta (f_1(U) <   \epsilon\) , then there exists \(q\) such that \(\delta (B_qf_1(U)) <   \epsilon\) hence one can take \(V = B_qf_1(U)\)
\((c)\Rightarrow (a)\) One has

$$\Delta_\eta = \bigvee_{\delta(U) < \eta} U \times U$$

but for each $U$ such that $\delta(U) < \eta$, there exists $V$ such that $\delta(V) < \epsilon$ and $U \leqslant f^*(V)$, hence

$$\Delta_\eta \leqslant \bigvee_{\delta(V) < \epsilon} f^* V \times f^* V = (f \times f)^* (V \times V)$$

$\square$

26

3.1.10. **Definition :** A map between two pre-metric locales is said to be “compatible with $\triangleleft$” if $U \triangleleft V$ implies $f^*U \triangleleft f^*V$.

Metric maps and uniform maps are in particular compatible with $\triangleleft$ because if $f$ is uniform and if $\pi_1^*U \wedge \Delta_\epsilon \leqslant \pi_2^*(V)$ then, letting $\eta$ such that

$$\Delta_\eta \leqslant (f \times f)^* \Delta_\epsilon$$

as we have

$$(f \times f)^*(\pi_1^*(U) \wedge \Delta_\epsilon) \leqslant (f \times f)^* \pi_2^* V$$

we obtain

$$\pi_1^*(f^*U) \wedge \Delta_\eta \leqslant \pi_1^*(f^*U)) \wedge (f \times f)^* \Delta_\epsilon \leqslant \pi_2^* f^*V$$

i.e. $f^*U \triangleleft_\eta f^*V$

3.1.11. **Definition :** A map $f : X \to Y$ between two pre-metric locales is called an isometric map if $d(f(x), f(y)) = d(x, y)$, i.e. if $\Delta_q = (f \times f)^*(\Delta_q)$.

We can easily see (by the same kind of argument that 3.1.8) that this is equivalent to the fact that $\delta(\mathcal{L}) = \delta(f_!\mathcal{L})$ for all sublocales of $X$.

**Lemma :** If $f$ is an isometric map $X \to Y$ then for any locally positive sublocale $\mathcal{L}$ of $X$

$$\mathcal{L} \leqslant f^*(B_q f_! \mathcal{L}) \leqslant B_q \mathcal{L}$$

**Proof :**

The first inequality immediately follows from the fact that $f_!\mathcal{L} \leqslant B_q f_!\mathcal{L}$. For the second, as $f_!(\mathcal{L})$ is locally positive (because of 2.3.12) one can write that

$$B_q f_! \mathcal{L} = \bigvee_{\substack{v \in \mathcal{O}(Y) < q \\ v \wedge f_!(\mathcal{L}) > \emptyset}} v.$$

By 2.3.11, $v \wedge f_!(\mathcal{L})$ is positive if and only if $f^*(v) \wedge \mathcal{L}$ is. Also, as $f$ is isometric, for any $v \in \mathcal{O}(Y)^{<q}$, one has $f^*(v) \in \mathcal{O}(X)^{<q}$. Finally

$$f^*(B_q f_! \mathcal{L}) = \bigvee_{\substack{v \in \mathcal{O}(Y) < q \\ f^*(v) \wedge \mathcal{L} > \emptyset}} f^*(v) \leqslant \bigvee_{\substack{w \in \mathcal{O}(X) < q \\ w \wedge \mathcal{L} > \emptyset}} w = B_q \mathcal{L}.$$

$\square$

27

3.1.12. We now consider two toposes $\mathcal{E}$ and $\mathcal{T}$, a geometric morphism $f: \mathcal{E} \to \mathcal{T}$ and $X$ a pre-metric locale in $\mathcal{T}$. As $f^\#$ is a functor from locale in $\mathcal{T}$ to locale in $\mathcal{E}$ commuting to projective limit and $f^\#(\widehat{\mathbb{R}_+^\infty}_\mathcal{T}) \simeq \widehat{\mathbb{R}_+^\infty}_\mathcal{E}$, we obtain a map $f^\#(d): f^\#(X) \times f^\#(X) \to \widehat{\mathbb{R}_+^\infty}$. Moreover all the axioms asserting that $d$ is a pre-distance can be pulled back turning $f^\#(X)$ into a pre-metric locale.

**Proposition :** Let $\mathcal{L}, \mathcal{M}$ be a sublocales of $X$, then (as sublocales of the pre-metric locale $f^\#(X)$) one has:

- If $\delta(\mathcal{L}) < q$ then $\delta(f^\#(\mathcal{L})) < q$.
- If $\mathcal{L} \triangleleft_q \mathcal{M}$ then $f^\#(\mathcal{L}) \triangleleft_q f^\#(\mathcal{M})$.
- If $\mathcal{L}$ is locally positive then $B_q f^\#(\mathcal{L}) = f^\#(B_q \mathcal{L})$.

**Proof :**

$f^\#$ is a functor commuting to all projective limits, in particular pull-backs, products and intersections, and by definition of the metric $f^\#(\Delta_q) = \Delta_q$ hence

$$\mathcal{L} \times \mathcal{L} \subseteq \Delta_{q'}$$

implies

$$f^\#(\mathcal{L}) \times f^\#(\mathcal{L}) \subseteq \Delta_{q'}$$

and

$$\pi_1^*(\mathcal{L}) \wedge \Delta_q \subseteq \pi_2^*(\mathcal{M})$$

implies

$$\pi_1^*(f^\#(\mathcal{L})) \wedge \Delta_q \subseteq \pi_2^*(f^\#(\mathcal{M}))$$

which proves the first two points.

The third point is harder because in general the pull-back $f^\#$ does not commute with the direct image functor $(\pi_2)_!$. But if we assume that $\mathcal{L}$ is locally positive, then the map

$$\pi_1^*(\mathcal{L}) \wedge \Delta_q \to B_q \mathcal{L}$$

is the restriction of the projection from $\mathcal{L} \times X$ to $X$ and hence is an open map. In particular (as we know that it is a surjection by definition) it is an open surjection and hence its pull-back by $f^\#$ is again an open surjection. In particular, the maps

$$\pi_1^*(f^\#(\mathcal{L})) \wedge \Delta_q \to f^\#(B_q \mathcal{L}) \to f^\#(X)$$

form a factorisation surjection/inclusion and, by uniqueness of such a factorisation, we obtain the third point. $\square$

28

3.1.13. We also note that if we define $\mathcal{C}(\mathcal{T})$ to be the category of pre-metric locales and metric maps internal to $\mathcal{T}$, then open surjections are descent morphisms for $\mathcal{C}$ (see 2.4): If $f: \mathcal{E} \to \mathcal{T}$ is an open surjection and $(X, d)$ is a pre-metric locale in $\mathcal{E}$ endowed with a descent data then it is in particular a descent data on $X$ as a locale, so as locale descend along open surjections, $X$ comes from a locale $X'$ in $\mathcal{T}$. As the $\epsilon: \pi_1^* X \to \pi_2^* X$ is an isomorphism in the category of metric maps it is an isometric map and hence the distance is a morphism in $Des(f, \mathcal{C})$ and hence also descends into a function $d': X' \times X' \to \overbrace{\mathbb{R}_+^\infty}^\infty$. All the axioms defining a pre-distance are equality relations (and inequality for the specialisation order), hence as they are satisfied by the pull-back of $(X', d')$ along an open surjection they are also satisfied by $(X', d')$. Hence $(X, d)$ is the pull-back of the pre-metric locale $(X', d')$. This proves that the functor $\mathcal{T} \to Des(f, \mathcal{C})$ is essentially surjective, but it is also fully faithful for similar reasons: a metric map commuting to descent data is in particular a map of locales commuting to descent data, and as $f$ is an open surjection a map $h$ is metric if and only if $f^*(h)$ is metric.

## 3.2 Metric locales

3.2.1. If $(X, d)$ is a pre-metric locale, then the various properties given in 3.1.4 show that, essentially, the "topology defined by $d$" (whatever the precise meaning of this is) is coarser than the topology of $X$, but nothing forces them to agree. For example, a metric set in the usual sense (with a distance function taking value in $\overbrace{\mathbb{R}_+^\infty}^\infty$), gives a pre-distance on a discrete locale, and the topology defined by $d$ can disagree with the discrete topology. That is why we require the following additional property:

Definition: A Metric locale is a pre-metric locale $X$ such that for all $U \in \mathcal{O}(X)$,

$$U = \bigvee_{\substack{V \in \mathcal{O}(X) \\ V \triangleleft U}} V.$$

This definition is equivalent to the fact that the family $(B_q V)_{V \in \mathcal{O}(X), q \in \mathbb{Q}_+^\infty}$ forms a basis of the topology. Indeed $V \triangleleft_q U$ is equivalent to $B_q V \leqslant U$ and $B_q V = \bigvee B_{q'} V$ for $q' < q$, hence this asserts that the open balls form a basis of the topology.

Also if $X$ is metric and $f$ is a geometric morphism then $f^\#(X)$ is also metric because the $B_q V$ for $V \in f^*(\mathcal{O}(X))$ form a basis of $f^\#(X)$.

Proposition: A Metric locale satisfies the following separation axiom: the diagonal embedding

$$X \to \bigwedge_q \Delta_q$$

is an isomorphism (where the intersection is an intersection of sublocale).

The intuitive reason for this is that if we consider two points $(x, y)$ in $\bigwedge_q \Delta_q$ then by definition $d(x, y) = 0$. If the open balls form a basis of the topology

29

then for any open $U$, $x \in U$ if and only if $y \in U$, but for points of a locale this implies that $x = y$. The following proof is just the translation of this argument in terms of generalized points.

# **Proof :**

Consider $f : Y \rightarrow \bigwedge_q \Delta_q$ a map, and let $f_1$ and $f_2$ be the two components $Y \rightarrow X$ of $f$. Let $U, V$ be two open sublocales of $X$ such that $U \triangleleft_q V$. Then

$$\pi_1^*(U) \wedge \Delta_q \leqslant \pi_2^*(V).$$

Applying $f^*$ to each side gives

$$f_1^*(U) \wedge f^*(\Delta_q) \leqslant f_2^*(V),$$

and as $f^*(\Delta_q) = Y$ by hypothesis, one has $f_1^*(U) \leqslant f_2^*(V)$.

Finally, writing $V = \bigvee_{U \in V} U$ one has:

$$f_1^*(V) = \bigvee_{U \in V} f_1^*(U) \leqslant f_2^*(V).$$

The converse inequality follows by symmetry and hence $f_1 = f_2$ i.e. $f$ factors into the diagonal embedding, and this concludes the proof. $\square$

In particular, as by 3.1.5,

$$\bigwedge \Delta_q = \bigwedge \overline{\Delta_q}$$

The diagonal embedding of a metric locale is fiberwise closed, one says that metric locales are *fiberwise separated*.

**3.2.2. Proposition :** Let $X$ be a metric locale, and $Y$ a pre-metric locale. Let $f : X \rightarrow Y$ be an isometric map. Then $X$ is a sublocale of $Y$ i.e. $f^*$ is onto. More generally, if we only assume that $X$ is pre-metric then we obtain the inequalities

$$\forall U \in \mathcal{O}(X), \bigvee_{V \in U} V \leqslant f^* f^*(U) \leqslant U$$

The proposition follows from Lemma 3.1.11:

# **Proof :**

Let $U$ be any open sublocale of $X$, such that

$$U = \bigvee_{V \in U} V$$

For any $V \triangleleft_q U$ one has by Lemma 3.1.11

$$V \leqslant f^*(B_q f, V) \leqslant U$$

30

hence

$$U = \bigvee_{q, V \leqslant q U} f^*(B_q f_l V) = f^* \left( \bigvee_{q, V \leqslant q U} B_q f_l V \right)$$

In particular, if $X$ is metric, then this works for an arbitrary $U$ and $f^*$ is surjective.

If $X$ is no longer metric, then let $U' = \bigvee_{V \in U} V$, then $U'$ satisfy $U' = \bigvee_{V \in U'} V$ and hence the first part can be applied to $U'$ and there exists $V$ such that $U' = f^*(V)$. In particular, as $f^*(V) \leqslant U$ we obtain that $V \leqslant f_*(U)$ and hence

$$U' = f^*(V) \leqslant f^*(f_*(U)).$$

The inequality $f^*(f_*(U)) \leqslant U$ being always true this concludes the proof. $\square$

3.2.3. The following proposition allows one to extend by density relations between continuous functions with values in metric locale.

Proposition : Let $f, g : X \rightrightarrows Y$ be two maps of locales with $Y$ a metric locale (or more generally a fiberwise separated locale). Assume that $f$ and $g$ coincide on some fiberwise dense sublocale $T \subset X$. Then $f = g$.

Proof :

Let $V$ be the pull-back of the diagonal of $Y$ by the map $(f, g) : X \to Y \times Y$. As fiberwise closeness is stable under pull-back (see [12] C1.2.14(v)), $V$ is a fiberwise closed sublocale of $X$, containing the fiberwise dense sublocale $T$, hence $V = X$, and this concludes the proof. $\square$

3.2.4. We will also sometimes need to extend by continuity "metric relations" between functions, which will generally be about comparing functions with value in $\overleftarrow{\mathbb{R}}_+^\infty$. As $\overleftarrow{\mathbb{R}}_+^\infty$ is not fiberwise separated, it is not possible to apply directly the previous result. However, one has the following statement:

We will say that a function from $m : X \to \overleftarrow{\mathbb{R}}_+^\infty$ is admissible if there exist two families of functions $f_1, \dots f_n$ and $g_1, \dots, g_n$ from $X$ to pre-metric locales $X_1, \dots X_n$ and a commutative diagram:

![img-0.jpeg](img-0.jpeg)

(where the vertical arrows are the canonical maps) such that:

$$m(x) = \lambda(d(f_1(x), g_1(x)), \dots, d(f_n(x), g_n(x))).$$

31

It is probably possible to use a more general definition of “admissible” map, but this one will be enough for all the applications appearing here.

Proposition : Assume that one has two admissible maps  \( m_{1}, m_{2}: X \Rightarrow \overleftarrow{R_{+}^{\infty}} \)  such that one has an inequality  \( m_{1} \leqslant m_{2} \)  on some fiberwise dense sublocale S of X a locally positive locale, then the inequality holds one the whole X.

#### Proof :

The idea is to pull-back everything to some boolean locale \(\mathcal{B}\). In the logic of \(\mathcal{B}\), thanks to 3.1.7 the admissible functions \(m_1\) and \(m_2\) will factor as functions \(X \Rightarrow \overline{\mathbb{R}}\) still satisfying an inequality over \(S\). The pull-back of \(S\) is still fiberwise dense in the pull-back of \(X\) because of 2.3.14, but, contrary to \(\overleftarrow{\mathbb{R}_+^\infty}\), \(\mathbb{R}\) is (fiberwise) separated and hence one can conclude that in the category of sheaves over \(\mathcal{B}\) the pull-backs of \(m_1\) and \(m_2\) agree on the pull-back of \(X\) by 3.2.3. This implies that (in the base topos) one has a diagram:

![img-1.jpeg](img-1.jpeg)

In order to conclude that  \( m_{1} \leqslant m_{2} \)  it is enough to choose B such that  \( \pi_{2}: B \times X \to X \)  is surjective. It is possible, indeed, if one chooses a boolean locale B which covers X, i.e. with a surjective map  \( s: B \to X \)  then:

![img-2.jpeg](img-2.jpeg)

The projection  \( \pi_{2}:B\times B\to B \)  is a surjection because it has a section, the map  \( s:B\to X \)  is surjective by hypothesis, hence the diagonal map is surjective. This implies that the map  \( \pi_{2}:B\times X\to X \)  is surjective and hence it concludes the proof. ☐

Of course the same result where the inequality is replaced by an equality also holds by two applications of this result.

### 3.3 Completion of a metric locale

In this subsection we will define the completion of pre-metric locale as the space of minimal Cauchy filters. The same idea has been previously used by S.Vickers in [18].

32

**3.3.1. Definition :** *Let $X$ be a pre-metric locale. A basis $B$ of $X$ is said to be a metric basis if and only if $B$ contains only positive elements, and if $V \in B$ implies $B_q V \in B$.*

This definition can easily be changed without altering the main result of this article, we have chosen it only because it is the simplest notion we have found which is strong enough to assert that the basis will be well behaved and weak enough so that the natural examples we will encounter in practice satisfy this definition, like for example the basis of all open balls on a normed space.

Of course if $B$ is an arbitrary basis of $X$ (composed of positive elements) one can consider the metric basis generated by $B$ by adding to $B$ all the elements of the form $B_{q_1} \dots B_{q_n} V$ for $V \in B$ and $(q_i)$ a finite sequence of positive rational numbers. Also, if $B$ is a metric basis on $X$ in a topos, then the pull-back of $B$ by any geometric morphism $f : \mathcal{E} \to \mathcal{T}$ is a metric basis of the pull-back of $X$.

**3.3.2. Definition :** *Let $X$ be a pre-metric locale endowed with a metric basis $B$, a $B$-Cauchy filter on $X$ is a subset $\mathcal{F} \subseteq B$ such that:*

*(CF1) For all $V \in \mathcal{F}$ and $U \in B$ such that $V \leqslant U$ one has $U \in \mathcal{F}$.*

*(CF2) If $U, V \in \mathcal{F}$ then there exists $W \in B$ such that $W \leqslant U$ and $W \leqslant V$ and $W \in \mathcal{F}$.*

*(CF3) For all positive rational numbers $q$, there exists $U \in \mathcal{F}$ such that $\delta(U) < q$.*

*A $B$-Cauchy filter is said to be regular if it satisfies additionally:*

*(CF4) For all $U \in \mathcal{F}$ there exists $V \in \mathcal{F}$ such that $V \triangleleft U$.*

*A Cauchy filter on $X$ (without specifying the basis) is a $B$-Cauchy filter on $X$, for $B = \mathcal{O}(X)^+$.*

We insist on the fact that $B$ (as a metric basis) is always assumed to be a subset of $\mathcal{O}(X)^+$. This is why there is no axiom asserting that $\emptyset$ is not an element of $\mathcal{F}$, or that all the elements of $\mathcal{F}$ are positive.

**3.3.3. Proposition :** *Any $B$-Cauchy filter $\mathcal{F}$ contains a unique regular Cauchy filter which is $\mathcal{F}^r = \{V \in B | \exists u \in \mathcal{F}, u \triangleleft V\}$.*

# **Proof :**

One easily checks that $\mathcal{F}^r$ is a regular $B$-Cauchy filter. Conversely, let $\mathcal{F}'$ be a regular $B$-Cauchy filter included in $\mathcal{F}$, then for any $U \in \mathcal{F}'$ there exists by (CF4) an element $V \in \mathcal{F}$ such that $V \leqslant B_q V \leqslant U$, hence $U \in \mathcal{F}'$, which proves that $\mathcal{F}' \subset \mathcal{F}^r$. Let now $U \in \mathcal{F}^r$, by definition there exists $V \in \mathcal{F}$ such that $V \leqslant B_q V \leqslant U$, by (CF3) there exists $W \in \mathcal{F}'$ such that $\delta(W) < q$ and by (CF2) there must be an element $\tau$ of $\mathcal{F}$ such that $\tau \leqslant W$ and $\tau \leqslant V$. In particular, $W \wedge V > \emptyset$ and hence (by the point 10 of 3.1.4) $W \leqslant B_q V \leqslant U$ and $U \in \mathcal{F}'$ which concludes the proof. $\square$

33

Hence regular Cauchy filters correspond to the notion of minimal Cauchy filter, this explains why we will later construct the completion of a locale as the classifying space of regular Cauchy filters, by analogy with the classical construction of the completion of a uniform space as a uniform structure on the set of minimal Cauchy filters (see [3, Chap. II.7]).

**3.3.4. Lemma :** *Let $X$ be a pre-metric locale endowed with a metric basis $B$, and let $\mathcal{F}$ be a regular Cauchy filter on $X$. Then for any $U \in \mathcal{F}$, there exists $V \in B \wedge \mathcal{F}$ such that $V \leqslant U$.*

**Proof :**

Let $U \in \mathcal{F}$, by (CF4) there exists $U' \triangleleft_q U$ such that $U' \in \mathcal{F}$. Also by (CF3) there exists an element $W \in \mathcal{F}$ such that $\delta(W) < (q/3)$ and as $B$ is a basis and $W$ is positive there exists $b \leqslant W$ with $b \in B$. Let $V = B_{q/3}b$, then, by the point 12 of 3.1.4, one has $\delta(V) < q$, also $V \in B$ because $B$ is metric, $W \leqslant V$ because $b \wedge W = b$ is positive and $\delta(W) < q/3$ and hence $V \in \mathcal{F}$. Also by (CF2) there exists $V' \in \mathcal{F}$ such that $V' \leqslant V \wedge U'$, as $V'$ is positive this implies that $V \leqslant B_q U' \leqslant U$. As $V \in B \wedge \mathcal{F}$, this concludes the proof. $\square$

**3.3.5. Corollary :** *The map $\mathcal{F} \to B \wedge \mathcal{F}$ induces a bijection between the set of regular Cauchy filters on $X$ and the set of regular $B$-Cauchy filters on $X$.*

We also mention that, as the following proof will show, this proposition holds for any family $B$ satisfying the conclusion of the previous lemma (3.3.4) even if it is not a metric basis or even if it is not a basis at all.

**Proof :**

Let $\mathcal{F}$ be a regular Cauchy filter on $X$. We will first prove that $\mathcal{F}' = \mathcal{F} \wedge B$ is a regular $B$-Cauchy filter, this is essentially immediate by Lemma 3.3.4:

- If $U \leqslant V$ with $V \in \mathcal{F}'$ and $U \in B$ then $U \in \mathcal{F}$ and hence $U \in \mathcal{F}'$ because $\mathcal{F}$ satisfy (CF1).
- If $U, V \in \mathcal{F}'$ then there exists $W \in \mathcal{F}$ such that $W \leqslant U \wedge V$ and by the lemma there exists $W' \in \mathcal{F}'$ such that $W' \leqslant W \leqslant U, V$.
- There exists $U \in \mathcal{F}$ such that $\delta(U) < q$ and (by the lemma) a $U' \leqslant U$ such that $U' \in \mathcal{F}'$, hence $\delta(U') < q$.
- Let $U \in \mathcal{F}'$, there exists $V \in \mathcal{F}$ such that $V \triangleleft U$, then any $V' \leqslant V$ with $V' \in \mathcal{F}'$ (again given by the lemma) works.

Now $\mathcal{F}$ can be reconstructed from $\mathcal{F}'$ by the lemma together with (CF1) :

$$\mathcal{F} = \{U | \exists U' \in \mathcal{F}', U' \leqslant U\}.$$

And if you take $\mathcal{F}'$ to be any regular $B$-Cauchy filter, then the previous formula defines a $\mathcal{F} \subseteq \mathcal{O}(X)^+$ which is easily checked to be a regular Cauchy filter as well, and by (CF1) $\mathcal{F}' = \mathcal{F} \wedge B$. This concludes the proof. $\square$

34

3.3.6. Let $X$ be a pre-metric locale, and $B$ be a metric basis on $X$, the theory of regular $B$-Cauchy filters as defined in 3.3.2 is clearly a propositional geometric theory with basic propositions indexed by $B$. Hence it has a classifying space $\tilde{X}_B$.

If $X$ is a pre-metric locale in a topos $\mathcal{T}$ and if $f : \mathcal{E} \rightarrow \mathcal{T}$ is a geometric morphism, then $f^\#(\tilde{X}_B) \simeq f^\#(\tilde{X})_{f^*(B)}$ because the pull-back of a classifying locale classifies the pull-back of the theory and the pull-back of the theory of regular $B$-Cauchy filter is exactly the theory of regular $f^*(B)$-Cauchy filter on $f^\#(X)$. But by 3.3.5 the points of $\tilde{X}_B$ do not depend on $B$, and hence by the observations we just made, their points on any topos over the base topos do not depend on $B$, and all the $\tilde{X}_B$ are isomorphic.

**Definition :** *The completion $\tilde{X}$ of $X$ is defined as the classifying locale $\tilde{X}_B$ of the theory of regular $B$-Cauchy filters on $X$ for any metric basis $B$ of $X$.*

Also if $U$ is any positive open sublocale of $X$ we denote by $U^\sim$ the open sublocale of $\tilde{X}$ corresponding to the proposition “$U \in \mathcal{F}$”. It is a general fact about classifying spaces that the $U^\sim$ form a pre-basis of the topology of $X$, but the axiom (CF2) show that for any metric basis $B$ of $X$, the $U^\sim$ with $U \in B$ form a basis of $\tilde{X}$. If $U$ is not necessarily positive, one can still defined $U^\sim$ by

$$U^\sim = \bigvee_{\substack{V \leqslant U \\ V > \emptyset}} V^\sim.$$

When $U > \emptyset$, the two possible definitions of $U^\sim$ are compatible because

$$\bigvee_{\substack{V \leqslant U \\ V > \emptyset}} V^\sim = U^\sim$$

3.3.7. **Proposition :** *Let $Y$ be a locale, a morphism $f$ from $Y$ to $\tilde{X}$ corresponds to a map $\tau : B \rightarrow \mathcal{O}(Y)$ such that:*

1. $\tau$ is non-decreasing.
2. $\tau(U) \wedge \tau(V) \leqslant \bigvee_{\substack{W \in B \\ W \leqslant U \wedge V}} \tau(W)$
3. $\bigvee_{\substack{U \in B \\ \delta(U) < \eta}} (\tau(U)) = Y$
4. $\tau(U) \leqslant \bigvee_{\substack{V \in B \\ V \leqslant U}} \tau(V)$

*Moreover this correspondence is characterized by the relation $\tau(U) = f^*(U^\sim)$. Also if $\tau$ only satisfies the first three properties, then there exists a unique $\tau^r$ such that $\tau^r$ satisfy the four properties and $\tau^r \leqslant \tau$ for the pointwise ordering and one has*

35

$$\tau^r(U) = \bigvee_{\substack{V \in B \\ V \triangleleft U}} \tau(V)$$

# **Proof :**

A morphism from $Y$ to $\tilde{X}$ is the data of a regular Cauchy filter on $X$ in the internal logic of $Y$. i.e. for each $U \in B$ one should have a proposition $\tau(U) := \text{“}U \in \mathcal{F}$” satisfying (internally) the axiom $(CF1 - 5)$. The four properties given for $\tau$ corresponds exactly to the externalisation of the four axioms $(CF1 - 4)$ (in the right order).

If $\tau$ only satisfies the first three properties then it is just a $B$-Cauchy filter on $X$ and in this case one can apply 3.3.3 and there is a unique regular $B$-Cauchy filter $\tau^r \leqslant \tau$ and it is indeed given by

$$\tau^r(U) = \bigvee_{\substack{V \in B \\ V \triangleleft U}} \tau(V)$$

which is the direct translation of $U \in \tau^r$ if there exists $V \triangleleft U$ with $V \in \tau$.  
□

Of course, the inequalities in the axioms 2. and 4. are in fact equalities because the axiom 1. implies the reverse inequalities.

# **3.3.8. Proposition :** *There is a map $i$ from $X$ to $\tilde{X}$ defined by*

$$i^*(U^\sim) = \bigvee_{V \triangleleft U} V.$$

*Moreover, for any $U \in \mathcal{O}(X)$,*

$$i^*(U) = U^\sim$$

# **Proof :**

The inclusion map $e : \mathcal{O}(X)^+ \rightarrow \mathcal{O}(X)$ clearly satisfies the first three points of 3.3.7. Hence the map

$$e^r(U) = \bigvee_{V \triangleleft U} V$$

satisfies the four points of 3.3.7 and hence there is a map $i : X \rightarrow \tilde{X}$ such that for any $U \in \mathcal{O}(X)^+$ one has $i^*(U^\sim) = e^r(U)$. But as $U^\sim$ is defined as $\bigvee_{\substack{V \leqslant U \\ V > 0}} V^\sim$ this formula immediately extends to an arbitrary $U$.

We still have to prove that $i^*(U) = U^\sim$. As $i^*(U^\sim) \leqslant U$, one has $U^\sim \leqslant i^*(U)$. Let $V$ an arbitrary open sublocale of $X$ such that $V^\sim \leqslant i^*U$ hence,

$$\bigvee_{V' \triangleleft V} V' \leqslant U$$

36

Consider an arbitrary Cauchy filter $F$ on $X$ such that $V \in F$. Then there exists $V' \triangleleft V$ such that $V' \in F$ and hence $U \in F$. This proves that $V^{\sim} \leqslant U^{\sim}$ and hence, as $V^{\sim} \leqslant U^{\sim}$ imply $V^{\sim} \leqslant i_{\star}(U)$ one has $V^{\sim} \leqslant i_{\star}U$ if and only if $V^{\sim} \leqslant U^{\sim}$ hence as the $V^{\sim}$ form a basis of $\widetilde{X}$ this proves that $i_{\star}(U) = U^{\sim}$.

**3.3.9. Proposition :** *The canonical map $i: X \rightarrow \widetilde{X}$ is fiberwise dense and $\widetilde{X}$ is locally positive.*

**Proof :**

The $(B_q V)^{\sim}$ for $q$ a positive rational number and $V$ a positive element of $\mathcal{O}(X)$ form a basis of $\widetilde{X}$. Indeed, the $U^{\sim}$ for $U \in \mathcal{O}(X)^+$ form a basis, and for any $U \in \mathcal{O}(X)$ by (CF4),

$$U^{\sim} = \bigvee_{\substack{V \triangleleft U \\ V > \delta}} V^{\sim} = \bigvee_{B_q V \leqslant U} (B_q V)^{\sim}.$$

Moreover,

$$i^*((B_q V)^{\sim}) = \bigvee_{U \triangleleft B_q V} U \geqslant \bigvee_{q' < q} B_{q'} V = B_q V.$$

Hence one has a basis of elements of $\widetilde{X}$ whose pre-image by $i$ are positive. This implies that $\widetilde{X}$ has a basis of positive elements and that for each positive element of $\widetilde{X}$ its pre-image along $i$ is positive, which concludes the proof. $\square$

**3.3.10. Proposition :** *There is a distance function $d$ on $\widetilde{X}$ such that*

$$\Delta_q = \bigvee_{U \in \mathcal{O}(X)^{<q}} U^{\sim} \times U^{\sim}.$$

One might note that this definition of the distance on $\widetilde{X}$ is the point-free formulation of the more usual definition:

$$d(\mathcal{F}, \mathcal{F}') < q \text{ if and only if } \exists u \in \mathcal{F} \wedge \mathcal{F}' \text{ with } \delta(u) < q$$

which is equivalent if interpreted in terms of generalized points.

**Proof :**

Let $U \in \mathcal{O}(X)$ such that $\delta(U) < q$. Then there exists $q'$ such that $\delta(U) < q'$ and $U^{\sim} \times U^{\sim} \leqslant \Delta_{q'}$. Hence

$$\Delta_q = \bigvee_{q' < q} \Delta_{q'},$$

37

which proves that this formula defines a function $d : \widetilde{X} \times \widetilde{X} \to \overleftarrow{\mathbb{R}_+^\infty}$. This function is clearly symmetric, and the diagonal embeddings factor into $\Delta_q$ because the $U^\sim$ with $\delta(U) < q$ cover $\widetilde{X}$ by axiom (CF3). The last point to check is the triangular inequality, but:

$$\pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) = \bigvee_{\substack{\delta(U) < q \\ \delta(U') < q'}} U^\sim \times (U^\sim \wedge U'^\sim) \times U'^\sim$$
$$(\pi_{1,3})! \left( \pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) \right) = \bigvee_{\substack{\delta(U) < q \\ \delta(U') < q' \\ U \wedge U' > \emptyset}} U^\sim \times U'^\sim.$$

Since $U^\sim \times U'^\sim \leqslant (U \vee U')^\sim \times (U \vee U')^\sim$ and as we are restricted to the case $U \wedge U' > \emptyset$, one has $\delta(U \vee U') < q + q'$ by point 6 of 3.1.4, hence $U^\sim \times U'^\sim \subset \Delta_{q+q'}$ and

$$(\pi_{1,3})! \left( \pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) \right) \leqslant \Delta_{q+q'},$$

which is the triangular inequality. The last point to prove is that this pre-distance is a distance. This a consequence of the following lemma. $\square$

**Lemma :** For any $U \in \mathcal{O}(X)$ one has $B_q(U^\sim) \leqslant (B_q U)^\sim$. In particular, if $U \triangleleft_q V$ then $U^\sim \triangleleft_q V^\sim$.

**Proof :**

Indeed, for any $W \in \mathcal{O}(X)$ such that $\delta(W) < q$ and $U^\sim \wedge W^\sim$ is positive, (CF2) proves that $U \wedge W$ is positive, hence, from the definition of $\Delta_q$:

$$B_q(U^\sim) = (\pi_2)! (\pi_1^*(U^\sim)\Delta_q) = \left( \bigvee_{\substack{\delta(W) < q \\ U^\sim \wedge W^\sim > \emptyset}} W^\sim \right) \leqslant (B_q U)^\sim$$

which concludes the proof of the lemma. $\square$

This lemma allows to finish the proof of the proposition, indeed, by (CF4), $V^\sim = \bigvee_{U \triangleleft V} U^\sim$, hence any $V \in \mathcal{O}(\widetilde{X})$ can be written as

$$V = \bigvee_{U^\sim \leqslant V} U^\sim = \bigvee_{A^\sim \triangleleft U^\sim \leqslant V} A^\sim.$$

**3.3.11. Proposition :** Let $S \to Y$ be a fiberwise dense isometric map between two pre-metric locales, let $X$ be any pre-metric locale and $f : S \to \widetilde{X}$ be a uniform map. Then there exists a unique extension $\widetilde{f} : Y \to \widetilde{X}$.

**Proof :**

38

The uniqueness of the extension follows from the fact that $\tilde{X}$ is metric (3.3.10) and the result of 3.2.3, so we only have to prove the existence. We will use 3.3.7 for this. Let $\tau : \mathcal{O}(X)^+ \rightarrow \mathcal{O}(Y)$ defined by:

$$\tau(U) = i_* f^*(U^\sim)$$

where $i$ denote the embeddings of $S$ into $Y$.

We will first check that $\tau$ satisfies the first three properties of 3.3.7:

1. $i_*, f^*$ and $U \mapsto U^\sim$ are all order preserving. Hence $\tau$ is order preserving.
2. One has $U^\sim \wedge V^\sim = (U \wedge V)^\sim$ (essentially by (CF2)) hence as $i_*$ and $f^*$ also commute to binary intersection one has: $\tau(U) \wedge \tau(V) = \tau(U \wedge V)$. This is not enough to conclude immediately the proof of this point because $U \wedge V$ might fail to be positive. Fortunately, if one assumes that $\tau(W) = i_* f^*(W^\sim)$ is positive, then $i^* i_* f^*(W^\sim)$ is also positive because $i$ is fiberwise dense, which implies that $f^*(W^\sim)$ is positive (because it is bigger than $i^* i_* f^*(W^\sim)$) and hence that $W^\sim$ is positive, which finally implies that $W$ is positive (by 3.3.9 and 3.3.8). Hence one can write that

$$\tau(U) \wedge \tau(V) = \tau(U \wedge V) = \bigvee_{\tau(U \wedge V) > \emptyset} \tau(U \wedge V) \leqslant \bigvee_{U \wedge V > \emptyset} \tau(U \wedge V),$$

which proves points 2.

3. We fix $q$ a positive rational number, and (as $f$ is uniform) $\eta$ such that $\Delta_\eta \leqslant (f \times f)^* \Delta_{q/3}$ (see 3.1.9).

Let $U \in \mathcal{O}(S)^{+, <\eta}$ then (by 3.1.9) there exists $W \in \mathcal{O}(\tilde{X})^{<q/3}$ such that $U \leqslant f^*(W)$.

In particular $W$ is also positive and hence, by (CF3) and the fact that the $V^\sim$ form a basis of $\tilde{X}$, there exists $V_0 \in \mathcal{O}(X)^{+, <q/3}$ such that $V_0^\sim \leqslant W$. We define $V = B_{q/3} V_0$. One has $\delta(V) < q$ (by 3.1.4.12) and $W \leqslant V^\sim$ (by the lemma proved in 3.3.10), in particular $U \leqslant f^*(V^\sim)$. This proves that

$$\bigvee_{U \in \mathcal{O}(S)^{+, <\eta}} i_* U \leqslant \bigvee_{V \in \mathcal{O}(X)^{+, <\eta}} i_* f^*(V^\sim) = \bigvee_{V \in \mathcal{O}(X)^{+, <\eta}} \tau(V), \quad (2)$$

Finally

$$Y = \bigvee_{V \in \mathcal{O}(Y)^{+, <\eta}} V \leqslant \bigvee_{V \in \mathcal{O}(Y)^{+, <\eta}} i_* i^* V = Y.$$

As $i$ is an isometric map, for any $V \in \mathcal{O}(Y)^{<\eta}$ one has $i^* V \in \mathcal{O}(S)^{<\eta}$. Hence

$$Y = \bigvee_{V \in \mathcal{O}(Y)^{+, <\eta}} i_* i^* V \leqslant \bigvee_{U \in \mathcal{O}(S)^{+, <\eta}} i_* U. \quad (3)$$

The inequalities (2) and (3) together conclude the proof of the third point.

39

Hence from 3.3.7 there is a map $\tilde{f}: Y \to \tilde{X}$ such that $\tilde{f}^*(U^\sim) = \tau^*(U) = \bigvee_{V \triangleleft U} i_* f^* V^\sim$. It remains to be proved that $\tilde{f}$ is indeed an extension of $f$, i.e. that $\tilde{f} \circ i = f$.

$$i^* \tilde{f}^*(U^\sim) = \bigvee_{V \triangleleft U} i^* i_* f^*(V^\sim) \leqslant \bigvee_{V \triangleleft U} f^*(V^\sim) = f^*(U^\sim)$$

Because $\bigvee_{V \triangleleft U} V^\sim = U^\sim$ by (CF4). One the other hand, from the non-metric part of 3.2.2

$$i^* \tilde{f}^*(U^\sim) = \bigvee_{V \triangleleft U} i^* i_* f^*(V^\sim) \geqslant \bigvee_{\substack{V \triangleleft U \\ V' \triangleleft f^*(V^\sim)}} V'.$$

As $f^*$ is uniform it is compatible with $\triangleleft$, hence the set of $V'$ appearing in the last union contains all the $f^*(W^\sim)$ for $W \triangleleft V$ hence

$$i^* \tilde{f}^*(U^\sim) \geqslant \bigvee_{\substack{V \triangleleft U \\ W \triangleleft V}} f^*(W^\sim) = f^*(U^\sim),$$

which proves $i^* \tilde{f}^*(U^\sim) = f^*(U^\sim)$ and concludes the proof. $\square$

We also note that if the map $f$ is metric (resp. isometric), the extension $\tilde{f}$ will also be metric (resp. isometric) by an application of 3.2.4.

3.3.12. **Theorem**: Let $X$ be a pre-metric locale, then the following conditions are equivalent:

1. The map \( X \to \tilde{X} \) is an isomorphism;
2. \(X\simeq \tilde{Y}\) for some \(Y\)
3. For any \( S \to Y \) a strongly dense isometric map between pre-metric locales, and any map from \( S \) to \( X \) there exists a map from \( Y \) to \( X \) making the triangle commute;
4. Any strongly dense isometric map from \( X \) to a metric locale \( Y \) is an isomorphism.

A locale satisfying these conditions is called a complete metric locale.

**Proof**:

1. \(\Rightarrow 2\) is clear.
2. \(\Rightarrow 3\) is a direct consequence of 3.3.11.
4. \(\Rightarrow 1\) is also clear because the map from \(X\) to \(\tilde{X}\) is a dense isometric map.
3. \(\Rightarrow 4\) remains to be proved. Let \(f:X\to Y\) be a strongly dense isometric map. The identity map from \(X\) to \(X\) can be extended into a map \(g\) from \(Y\) to \(X\) by 3., such that \(g\circ f = Id_X\). As, \(f\circ g\) restricted to \(X\) is the inclusion from \(X\) to \(Y\), \(f\circ g\) is the identity of \(Y\) by fiberwise density of \(X\) into \(Y\) and fiberwise separation of \(Y\) (3.2.3) hence \(g\) is an inverse for \(f\), and they are isomorphisms.

40

It is immediate from point 3. that a locally positive fiberwise closed sublocale of a complete locale is also complete.

**3.3.13. Proposition :** *If $X$ is a pre-metric locale in a topos $\mathcal{T}$ and $f : \mathcal{E} \to \mathcal{T}$ is an open (or proper) surjection such that $f^\#(X)$ is complete then $X$ is complete.*

**Proof :**

The pull-back along $f$ of the canonical map $X \to \tilde{X}$ is the canonical map $f^\#(X) \to f^\#(\tilde{X})$. Hence as $f^\#$ is a descent functor for the categories of locales, it is in particular conservative and if the pull-back map is an isomorphism, the map $X \to \tilde{X}$ is also an isomorphism. $\square$

An immediate corollary of this result is that if $\mathcal{C}(\mathcal{T})$ is the category of complete metric locales and metric maps between them then objects of $\mathcal{C}$ descend along open surjections. Indeed, it is a full subcategory of the category of pre-metric locales, for which open surjections are descent morphisms as observed in 3.1.13, and this just states that $(X', d')$ is complete if it descends from a complete locale $(X, d)$.

**3.3.14. Proposition :** *Let $X$ be a pre-metric locale and let $X_d$ be the regular image of $X$ into $\tilde{X}$ then $\mathcal{O}(X_d)$ identifies with the set of $U \in \mathcal{O}(X)$ such that*

$$U = \bigvee_{V \triangleleft U} V$$

*and any map compatible with $\triangleleft$ from $X$ to a metric locale $Y$ factors into $X_d$.*

**Proof :**

The regular image of $i : X \to \tilde{X}$ is identified as a frame with the image of $i^* : \mathcal{O}(\tilde{X}) \to \mathcal{O}(X)$ which is clearly (by 3.3.8) the set of open sublocales defined in the proposition. If one has any map $f$ from $X$ to a metric locale $Y$ compatible with $\triangleleft$ then for any $U \in \mathcal{O}(Y)$,

$$U = \bigvee_{V \triangleleft U} V$$

Hence,

$$f^*(U) = \bigvee_{V \triangleleft U} f(V)^*$$

as $f^*(V) \leqslant f^*(U)$ this proves that $f^*(U) \in \mathcal{O}(X_d)$. Hence $f$ factors into $X_d$. $\square$

41

### 3.4 Product of metric locales

3.4.1. Let $\mathcal{L}$ and $\mathcal{M}$ be two pre-metric locales, one defines a pre-distance on $\mathcal{L} \times \mathcal{M}$ in the following way: $\Delta_q^{\mathcal{L} \times \mathcal{M}} \subset (\mathcal{L} \times \mathcal{M}) \times (\mathcal{L} \times \mathcal{M})$ is the intersection of the pull-back $\pi_{1,3}^*(\Delta_q^{\mathcal{L}})$ and $\pi_{2,4}^*(\Delta_q^{\mathcal{M}})$ (where the exponent on $\Delta$ indicate to which locale it is related). This corresponds to taking $d((l, m), (l', m')) = \max(d(l, l'), d(m, m'))$, and the classical argument can be adapted (in terms of generalised points) to prove that this is indeed a pre-distance on $\mathcal{L} \times \mathcal{M}$.

**Proposition :** $\mathcal{M} \times \mathcal{L}$ endowed with the previously constructed distance function is the categorical product of $\mathcal{M}$ and $\mathcal{L}$ in the category of pre-metric locales and metric maps.

**Proof :**

The projection $\pi_1 : \mathcal{L} \times \mathcal{M} \to \mathcal{L}$ satisfies $\Delta_q \subset \pi_1^*(\Delta_q)$ by construction of the distance function on $\mathcal{L} \times \mathcal{M}$, hence it is a metric map. In particular if $f : X \to \mathcal{M} \times \mathcal{L}$ is a metric map then the two component $f_1$ and $f_2$ are metric maps. Conversely, assume that $f_1$ and $f_2$ are metric maps. Then

$$(f \times f)^*(\Delta_q^{\mathcal{L} \times \mathcal{M}}) = (f \times f)^*(\pi_{1,3}^*(\Delta_q^{\mathcal{L}}) \wedge \pi_{2,4}^*(\Delta_q^{\mathcal{M}})).$$

But $\pi_{1,3}(f \times f) = f_1 \times f_1$ and $\pi_{2,4}(f \times f) = f_2 \times f_2$, hence,

$$(f \times f)^*(\Delta_q^{\mathcal{L} \times \mathcal{M}}) = (f_1 \times f_1)^*(\Delta_q^{\mathcal{L}}) \wedge (f_2 \times f_2)^*(\Delta_q^{\mathcal{M}})$$

As we assume that both $f_1$ and $f_2$ are metric,

$$\Delta_q^X \subset (f_1 \times f_1)^*(\Delta_q^{\mathcal{L}}) \wedge (f_2 \times f_2)^*(\Delta_q^{\mathcal{M}}).$$

This proves that $f$ is also metric and concludes the proof of the proposition. $\square$

3.4.2. **Proposition :** *The product of two complete metric locales is a complete metric locale. More generally the completion of $\mathcal{L} \times \mathcal{M}$ is canonically isomorphic to $\widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$.*

**Proof :**

Assume that $\mathcal{L}$ and $\mathcal{M}$ are complete. Let $S \to Y$ be a strongly dense map, and let $f : S \to \mathcal{L} \times \mathcal{M}$ be an isometric map. Then by the previous result and Proposition 3.3.11 there is a map $\widetilde{f} : Y \to \mathcal{L} \times \mathcal{M}$ extending $f$. Hence $\mathcal{L} \times \mathcal{M}$ is complete.

For the second part, $\mathcal{L} \times \mathcal{M} \to \widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$ is a fiberwise dense isometric map with $\widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$ complete, hence $\widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$ is the completion of $\mathcal{L} \times \mathcal{M}$. $\square$

42

### 3.5 The locale $[X, Y]_1$ of metric maps

In this subsection we show that it is possible to construct a classifying space $[X, Y]_1$ of metric maps between two metric locales $X$ and $Y$, at least when $Y$ is complete. The key observation underlying this construction is that (in a classical settings) on the set of metric functions the topology of point-wise convergence on any dense subsets is equivalent to the compact-open topology, and that when we endow this set of metric functions with this topology the composition law is bi-continuous. This suggests that this topology classifies metric functions. The general idea of this section is to give a point-free formulation of this topology, by replacing the basic open “$f(x) \in V$” by “$U \wedge f^{-1}(V) > \emptyset$” for $U$ a small neighborhood of $x$.

#### 3.5.1. Definition :

Let $X$ and $Y$ be two pre-metric locales. Let $A$ be a basis$^9$ of positive open of $X$ and $B$ be a metric basis of $Y$. We define $[X_A, Y_B]_1$ as the classifying space of the propositional geometric theory on propositions $(U, V)$ for $U \in A$ and $V \in B$ with the axioms:

(MM1) For all $U' \leqslant U$ and $V' \leqslant V$

$$(U', V') \vdash (U, V)$$

(MM2) For all $V \in B, U \in A$ and any positive rational number $q$ one has

$$(U, V) \vdash \bigvee_{\substack{u \leqslant U \\ \delta(u) < q}} (u, V);$$

(MM3) For all $U \in A$ and all $q$ positive:

$$\vdash \bigvee_{\substack{V \in B \\ \delta(V) < q}} (U, V);$$

(MM4) For all $U \in A, V \in B$

$$(U, V) \vdash \bigvee_{\substack{V' \in B \\ V' < V}} (U, V');$$

(MM5) Let $W_1, W_2, \tau \in A, q_1, q_2 \in \mathbb{Q}, V_1, V_2, V_1', V_2' \in B$ such that

$$\begin{array}{l} \delta(W_1) < q_1 \quad \delta(W_2) < q_2 \\ V_1' \triangleleft_{q_1} V_1 \quad V_2' \triangleleft_{q_2} V_2 \\ \tau \leqslant W_1 \quad \tau \leqslant W_2 \end{array}$$

then

$$(W_1, V_1') \wedge (W_2, V_2') \vdash \bigvee_{\substack{V \in B \\ V \leqslant V_1 \wedge V_2}} (\tau, V)$$

$^9$One can actually see that we do not even need $A$ to be a basis. All we need is that for all positive rational $q$ the set of $a \in A$ such that $\delta(a) < q$ cover $X$.

43

(MM6)

$$(U, V) \wedge (U, V') \vdash \delta(V \vee V') \leqslant \delta(U) + \delta(V) + \delta(V').$$

### 3.5.2. The main result of this section is

**Theorem :** *The locale $[X_A, Y_B]_1$ we just constructed does not depend on $A$ and $B$ and classifies metric maps between $X$ and $\tilde{Y}$. With the propositions $(U, V)$ corresponding to $U \wedge f^*(V^\sim) > \emptyset$. This locale will be denoted $[X, Y]_1$*

Its proof will occupy us for the rest of this subsection.

3.5.3. If $f$ is a geometric morphism from $\mathcal{E}$ to $\mathcal{T}$, then, by the same argument as in 3.3.6:

$$f^\#([X_A, Y_B]_1) \simeq [f^\#(X)_{f^*(A)}, f^\#(Y)_{f^*(B')}]_1$$

So it suffices to show that the points of $[X_A, Y_B]_1$ correspond to metric functions from $X$ to $\tilde{Y}$ to obtain the announced result.

3.5.4. **Proposition :** *Let $f : X \rightarrow \tilde{Y}$ be a metric map and let:*

$$(U, V)_f := \text{“}U \wedge f^*(V^\sim) > \emptyset\text{”}$$

*For $U \in A$ and $V \in B$. Then this defines a point of $[X_A, Y_B]_1$.*

#### Proof :

Axiom (MM1) is immediate. (MM2) holds because for any $V \in B, U \in A$, if $f^*(V^\sim) \wedge U$ is positive then one can write $U$ as a union of $u \in A$ such that $u \leqslant U$ and $\delta(u) < q$ and the locale positivity of $X$ allows one to conclude. Axiom (MM3) and (MM4) hold because the corresponding unions holds in $\tilde{Y}$.

We now prove axiom (MM5). Let $W_1, W_2, \tau, q_1, q_2, V_1, V_1', 2_2, V_2'$ satisfying the hypothesis of (MM5). We also assume that $(W_1, V_1')_f$ and $(W_2, V_2')_f$ holds. Then as $f$ is metric and $V_i' \triangleleft_{q_i} V_i$ then $V_i'^\sim \triangleleft_{q_i} V_i^\sim$ one has

$$f^*(V_i'^\sim) \triangleleft_{q_i} f^*(V_i^\sim).$$

As $\delta(W_i) < q_i$ and $W_i \wedge f^*(V_i) > \emptyset$ this implies that

$$W_i \subseteq f^*(V_i^\sim),$$

and hence, as $\tau \leqslant W_1 \wedge W_2$, that

$$\tau \subseteq f^*(V_1^\sim \wedge V_2^\sim).$$

44

As $\tau$ is positive (the presentation of $X$ is assumed to be locally positive) and $V_1 \sim \wedge V_2$ is covered by the $V^\sim$ for $V \subseteq V_1 \wedge V_2$ this concludes the proof of (MM5).

We now prove (MM6). Let $U, V$ and $V'$ such that $U \wedge f^*(V^\sim) > \emptyset$ and $U \wedge f^*(V'^\sim) > \emptyset$. Let $q$ and $q'$ such that $\delta(V) < q$ and $\delta(V') < q'$. Let also $\epsilon$ be a positive rational number such that $\delta(V) < q - 2\epsilon$ and $\delta(V') < q' - 2\epsilon$. Let $W = B_\epsilon V$ and $W' = B_\epsilon V'$, in particular $\delta(W) < q$ and $\delta(W') < q'$.

One has, by the assumption on $V$ and $V'$ and the fact that $f$ is metric (see 3.1.8 proposition (c)):

$$\delta(W^\sim \vee W'^\sim) \subseteq \delta(W^\sim) + \delta(W'^\sim) + \delta(U)$$

Let $i$ be the isometric map $Y \rightarrow \tilde{Y}$ of 3.3.8, i.e.

$$i^*(V^\sim) = \bigvee_{U \in V} U.$$

In particular, as $W$ and $W'$ are open balls, one has $i^*(W^\sim) = W$ and $i^*(W'^\sim) = W'$, and $i^*(W^\sim \vee W'^\sim) = W \vee W'$, and as $i$ is isometric, this implies that $\delta(W \vee W') \leqslant \delta(W^\sim \vee W'^\sim)$.

Moreover since $\delta(W) < q$ then by definition of the distance on $\tilde{Y}$, $W^\sim \times W^\sim \subseteq \Delta_q$, and hence $\delta(W^\sim) \leqslant q$. One deduces from this that

$$\delta(V \vee V') \leqslant \delta(W \vee W') \leqslant \delta(W^\sim \vee W'^\sim) \leqslant \delta(W^\sim) + \delta(W'^\sim) + \delta(U) \leqslant q + q' + \delta(U),$$

which concludes the proof as it has been done for arbitrary $q$ and $q'$ bigger than $\delta(V)$ and $\delta(V')$.

3.5.5. **Definition :** *To any point $p$ of $[X_A, Y_B]_1$ we associate the function $\tau_p : B \rightarrow \mathcal{O}(X)$ defined by:*

$$\tau_p(V) := \bigvee_{\substack{\delta(W) < q \\ V' \in \mathbb{N}^p \\ p \in (W, V')}} W$$

where $V'$ runs through elements of $B$, $W$ through elements of $A$, and $q$ through positive rational numbers.

**Proposition :** *If $f$ is a metric map from $X$ to $\tilde{Y}$ and $p$ is the point of $[X_A, Y_B]$ associated to $f$ in 3.5.4 then*

$$\tau_p(V) = f^*(V^\sim).$$

**Proof :**

45

One has by definition:

$$\tau_{p}(V) = \bigvee_{\substack{\delta(W) < q \\ V' \triangleleft_{q} V \\ f^{*}(V'^{\sim}) \wedge W > \emptyset}} W.$$

Hence, as for any $W$ appearing in the supremum one has $W \leqslant f^{*}(V^{\sim})$, we obtain that $\tau_{p}(V) \leqslant f^{*}(V^{\sim})$.

Conversely,

$$f^{*}(V^{\sim}) = \bigvee_{V' \triangleleft_{q} V} f^{*}(V'^{\sim}) = \left( \bigvee_{\substack{V' \triangleleft_{q} V \\ \emptyset < W \leqslant f^{*}(V'^{\sim}) \\ \delta(W) < q}} W \right) \leqslant \tau_{p}(V'^{\sim}).$$

3.5.6. Lemma : Let $p$ be any point of $[X_A, Y_B]_1$, then:

$$p \in (U, V) \Leftrightarrow U \wedge \tau_{p}(V) > \emptyset$$

Proof :

Assume first that $\tau_{p}(V) \wedge U > \emptyset$. Then there exists $W$ and $V'$ such that $\delta(W) < q$, $V' \triangleleft_{q} V$, $(W, V')$ and $W \wedge U > \emptyset$. Applying (MM5), one obtains that there exists $V'' \leqslant V$ such that $p \in (W \wedge U, V'')$ and hence $p \in (U, V)$.

Conversely assume that $p \in (U, V)$, then (by (MM4)) there exists $V' \in B$ and a positive $q$ such that $V' \triangleleft_{q} V$ and $p \in (U, V')$. Also by (MM2) there exists $W \in A$ such that $\delta(W) < q$ and $p \in (W, V')$. But this implies that $W \leqslant \tau_{p}(V)$ and as $W \leqslant U$ and $W > \emptyset$ one concludes that $U \wedge \tau_{p}(V) > \emptyset$. $\square$

3.5.7. At this point, all that remains to be checked in order to prove 3.5.2 is that for any point $p$, $\tau_{p}$ extends into a map from $X \to \widetilde{Y}$ and that this map is indeed metric.

Proposition : The map $\tau_{p}: B \to \mathcal{O}(X)$ satisfies the four conditions of 3.3.7 and in particular there is a (unique) map $f: X \to \widetilde{Y}$ such that $f^{*}(V^{\sim}) = \tau_{p}(V)$.

Proof :

We recall that

$$\tau_{p}(V) := \bigvee_{\substack{\delta(W) < q \\ V' \triangleleft_{q} V \\ p \in (W, V')}} W$$

Also the point $p$ being fixed, we will write $\tau$ instead of $\tau_{p}$ and $(U, V)$ instead of $p \in (U, V)$.

46

1. if $U \leqslant V$ then any $W$ appearing in the supremum defining $\tau(U)$ also appears in the one defining $\tau(V)$ with the same $V'$ and $q$. Hence $\tau$ is order preserving.

2.

$$\tau(V_1) \wedge \tau(V_2) = \bigvee W_1 \wedge W_2$$

where the union runs over all $W_1, W_2 \in A$ such that there exist $q'_1, q'_2$ positive rational numbers, and $V'_1, V'_2 \in B$ such that

$$\delta(W_i) < q'_i;$$

$$V'_i \triangleleft_{q'_i} V_i;$$

$$(W_i, V'_i).$$

For any such $W_1$ and $W_2$ there exists a positive rational number $\epsilon$ such that $\delta(W_i) < q'_i - \epsilon$. Let $q_i = q'_i - \epsilon$. One has in particular $\delta(W_i) < q_i$ and

$$V'_i \triangleleft_{q_i} B_{q_i} V'_i \triangleleft_\epsilon V_i.$$

Moreover $W_1 \wedge W_2$ can be written as the union of $\tau \in A$ such that $\tau \leqslant W_1 \wedge W_2$ and $\delta(\tau) < \epsilon$. Finally, one can apply (MM5) (taking $B_{q_i} V'_i$ instead of $V_i$) to obtain that there exists $V$ such that

$$V \leqslant (B_{q_1} V'_1 \wedge B_{q_2} V'_2) \triangleleft_\epsilon V_1 \wedge V_2$$

and

$$(\tau, V).$$

This proves that $\tau \leqslant \tau(B_\epsilon V)$ with $B_\epsilon B \leqslant V_1 \wedge V_2$ and $B_\epsilon V \in B$ because $B$ is metric, and hence concludes the proof that.

$$\tau(V_1) \wedge \tau(V_2) \leqslant \bigvee_{\substack{V \in B \\ V \leqslant V_1 \wedge V_2}} \tau(V).$$

3. Let $q$ be any positive rational number. Let $W \in A$ such that $\delta(W) < q/3$. Then by (MM3) there exists $V' \in B$ such that $\delta(V') < q/3$ and $(W, V')$. Let $V = B_{q/3} V' \in B$, one has: $\delta(W) < q/3$, $V' \triangleleft_{q/3} V$, $(W, V')$, hence $W \leqslant \tau(V)$ with $\delta(V) < q$ this proves that

$$W \leqslant \bigvee_{\substack{V \in B \\ \delta(V) < q}} \tau(V)$$

As we have done this for an arbitrary $W$ with $\delta(W) < q/3$ this concludes the proof.

47

4. Let $V \in B$, let $W$ appearing in the union defining $\tau(V)$, i.e. there exists a positive rational $q$, and a $V' \in B$ such that $\delta(W) < q$ and $V' \triangleleft_q V$.

But, there exists a positive rational number $\epsilon$ such that $\delta(W) < q - \epsilon$, and $V' \triangleleft_{q-\epsilon} B_{q-\epsilon} V' \triangleleft_\epsilon V$. Hence

$$W \leqslant \tau(B_{q-\epsilon} V' \leqslant \bigvee_{\substack{U \in B \\ U \triangleleft V}} \tau(U).$$

Finally, we obtain

$$\tau(V) \leqslant \bigvee_{\substack{U \in B \\ U \triangleleft V}} \tau(U).$$

The fact that the map $f$ induced by $\tau_p$ is metric follows from axiom (MM6) using the characterization (c) of metric maps given in 3.1.8, hence this concludes the proof of theorem 3.5.2.

### 3.6 Case of metric sets

3.6.1. We define a (pre)metric set as set $X$ endowed with a distance function $d: X \times X \to \overleftarrow{\mathbb{R}_+^\infty}$ satisfying the usual axioms for a (pre)distance:

- $d(x, x) = 0$
- $d(x, y) = d(y, x)$
- $d(x, z) \leqslant d(x, y) + d(y, z)$

With additionally, $d(x, y) = 0 \Rightarrow x = y$ for a metric set.

A (pre)metric set can be seen as a pre-metric locale by seeing its underlying set as a discrete locale. It is in general not a metric locale even if we start with a metric set.

3.6.2. We will say that a metric set $(X, d)$ is complete if the natural map $i: X \to \widetilde{X}$ identifies $X$ with the points of $\widetilde{X}$. As points of $\widetilde{X}$ identify with regular Cauchy filters one easily checks that this is equivalent to the usual (Cauchy filter based) definition of completeness.

48

3.6.3. **Theorem :** *There is an equivalence of categories between the category of weakly spatial complete metric locales (with metric maps) and complete metric sets (with metric maps).*

# **Proof :**

The functors are given by the following construction: to a complete metric set $X$ one associates its localic completion $\tilde{X}$, which is weakly spatial, because $X$ is fiberwise dense in it, and to a weakly spatial complete metric locale one associates its set of points endowed with the induced distance. These two constructions are functorial on metric maps.

By definition of a complete metric set it identifies with the set of points of its localic completion, and conversely, if $\mathcal{L}$ is a weakly spatial complete metric locale and $X$ is its set of points endowed with the induced distance, then $X \rightarrow \mathcal{L}$ is a fiberwise dense isometric map from $X$ to a complete locale, hence $\mathcal{L}$ is isomorphic to the completion of $X$. This proves that the two functors are inverse from each other on objects. They are also inverse of each other on morphisms, tautologically on one side and by 3.2.3 on the other side. $\square$

3.6.4. The internal application of the fact that the set of points of a complete metric locale is complete in the classical sense can prove directly a result of completeness of the space of functions with values in a complete locale for the uniform distance. This cannot be stated directly in terms of completeness of some metric locale because in general (if the initial space is not locally compact) the space of functions is not a locale, but one has:

**Proposition :** *Let $(f_i)_{i \in I}$ be a Cauchy net of functions between two locales $X$ and $Y$, with $Y$ a complete metric locale. This means that $I$ is a directed (filtering) ordered set and that for all positive rational number $\epsilon$ there exists $i_0 \in I$ such that $\forall i, j \geq i_0$, the map $(f_i, f_j)$ factors into $\Delta_\epsilon \subset Y \times Y$.*

*Then the net $f_i$ converges to some (uniquely defined) function $f : X \rightarrow Y$. This mean that there is a unique function $f : X \rightarrow Y$ such that for all positive rational number $\epsilon$ there exists $i_0 \in I$ such that $\forall i \geq i_0$, the map $(f, f_i)$ factors into $\Delta_\epsilon$.*

# **Proof :**

The net of functions $f_i : X \rightarrow Y$ can be interpreted as a net of points of $p^\#Y$ in the logic of $X$ (where $p$ is the map $X \rightarrow *$). And the fact that it is externally a Cauchy net immediately gives that it is internally a Cauchy net. The usual proof that completeness by filter imply completeness by net is completely constructive$^{10}$ and hence the fact that $p^\#Y$ is complete implies the convergence of the net $f_i$. Uniqueness of the limit implies that the limit is a global point of $p^\#Y$ in $X$, and hence a map from $X$ to $Y$. One then easily check that the internal convergence together with the external Cauchy condition imply the external convergence. $\square$

$^{10}$On the contrary, the converse relies on the axiom of choice.

49

3.6.5. In particular the category of complete metric sets identifies with the full subcategory of the category of complete metric locales composed of weakly spatial locales, and by 2.3.17 any complete metric locale becomes weakly spatial (hence identifies with a complete metric set) after a pull-back to some open locale. We already mentioned that if one defines $\mathcal{C}(\mathcal{T})$ as the category of complete metric locales over $\mathcal{T}$, then, it is a stack for the topology whose covering are open surjections.

From these observations one can deduce that the stack of internal complete metric locales is the stackification (the analogue of sheafication for stack and pre-stack) of the pre-stack of complete metric sets, that is the universal extension of the notion of complete metrics sets for the descent properties along open surjection.

At this point one could obtain the localic Gelfand duality of 4.2.5 directly by observing that the notion of compact regular locale is obtained as the stackification of the notion of compact completely regular locale, and apply the constructive Gelfand duality between compact regular locale and $C^*$ algebra to show that the two pre-stacks are equivalent. This will also avoid the use any of the material of section 3.5, but it will give an extremely uncomfortable definition of the spectrum of a localic $C^*$ algebra. This is why we prefer explicitly constructing the spectrum (in 4.2.3, using the construction of 3.5) before applying the descent argument to show the Gelfand duality.

## 4 Banach locales and $C^*$ locales

### 4.1 Banach locales and completeness

4.1.1. **Definition :** *A pre-Banach locale is a locally positive locale $\mathcal{H}$ endowed with:*

- *A commutative group law: $+ : \mathcal{H} \times \mathcal{H} \rightarrow \mathcal{H}$, with neutral element $0 : * \rightarrow \mathcal{H}$ and an inversion: $x \mapsto -x : \mathcal{H} \rightarrow \mathcal{H}$.*
- *An action of $\mathbb{Q}[i]$ (endowed with the discrete topology), $\mathbb{Q}[i] \times \mathcal{H} \rightarrow \mathcal{H}$, satisfying the usual axioms of a (unital) module.*
- *A norm function $\|\cdot\| : \mathcal{H} \rightarrow \overleftarrow{\mathbb{R}}_+^\infty$*

*where the norm function is expected to satisfy the following conditions:*

- $\forall x, y \in \mathcal{H} \|x + y\| \leqslant \|x\| + \|y\|$
- $\forall \lambda \in \mathbb{Q}[i], \forall x \in \mathcal{H}, \|\lambda x\| = |\lambda|\|x\|$
- $\|0\| = 0$
- $\mathcal{H} = \bigvee_{n \in \mathbb{N}} \{x \|x\| < n\}$

Of course, all the conditions stated in this definition have to be interpreted either in diagrammatic terms or in terms of generalized elements.

50

4.1.2. Proposition : Let $(\mathcal{H}, \|.\|)$ be a pre-Banach locale. Let $s$ and $p$ denote the maps $\mathcal{H} \times \mathcal{H} \to \mathcal{H}$ defined by:

$$s(x, y) = x - y$$

$$p(x, y) = x + y$$

Let $m$ denote the map $x \mapsto -x$ and $n$ be the norm map, $n : \mathcal{H} \to \overleftarrow{\mathbb{R}}^\infty$.

Finally we will denote $B_q 0 = n^*([0, q])$ (point 5 ensures that there is no possible confusion).

Then, one has the following facts:

1. The map \( n \circ s \) is a pre-distance on \( \mathcal{H} \).
2. The maps \(s\) and \(p\) are open maps.
3. The open sublocales \(\Delta_q\) coincide with \(s^*(B_q0)\).
4. If \(\mathcal{L}\) is any sublocale of \(\mathcal{H}\) then \(B_q\mathcal{L}\) coincide with both \(p_{!}(\mathcal{L}\times B_{q}0)\) and \(s_{!}(\mathcal{L}\times B_{q}0)\).
5. \(B_{q}0\) is the same things as \(B_{q}\{0\}\).

# Proof :

1. A proof by generalized points will be exactly the same as the usual proof that \( d(x,y) = \| x - y\| \) is a distance on a normed space.
2. We will consider two maps \(\mathcal{H} \times \mathcal{H} \to \mathcal{H} \times \mathcal{H}\) given by

$$\tau_p = (p, m \circ \pi_1);$$

$$\tau_s = (\pi_1, s).$$

These maps correspond in term of generalized points to the maps $\tau_p(x, y) = -x + y, -y)$ and $\tau_s(x, y) = (x, x - y)$, and they are both involutive and hence bijective. The maps $s$ and $p$ are then obtained as $\pi_2 \circ \tau_s$ and $\pi_1 \circ \tau_p$, but as $\mathcal{H}$ is locally positive, both $\pi_1$ and $\pi_2$ are open maps. Hence by composition $s$ and $p$ are open maps.

3. \(\Delta_q\) is by definition \(d^* ([0,q])\), but as \(d = n\circ s\), one has \(\Delta_q = s^* n^* ([0,q]) = s^* (B_q0)\).
4. The involutive map \(\tau_s\) introduced in the proof of point 2 exchange \(\pi^*(\mathcal{L}) \wedge \Delta_q\) with \(\mathcal{L} \times B_q0\), indeed:

$$\tau_s^*(\mathcal{L} \times B_q 0) = p i_1^*(\mathcal{L}) \wedge s^*(B_q 0) = \pi_1^*(\mathcal{L}) \wedge \Delta_q.$$

Hence $\pi_2!(\pi_1^*(\mathcal{L}) \wedge \Delta_q) = (\pi_2 \circ \tau_s)!(\mathcal{L} \times B_q 0)$ and $\pi \circ \tau_s = s$, which shows that $B_q \mathcal{L} = s!(\mathcal{L} \times B_q 0)$.

It also coincides with $p!(\mathcal{L} \times B_q 0)$ because as $n \circ m = n$ one has $m^*(B_q 0) = B_q 0$, and as $s = p \circ (Id, m)$ this concludes the proof.

51

5. From the previous result, $B_q\{0\}$ identifies with $p_!(\{0\} \times B_q0)$ but $p$ acts on $\{0\} \times B_q0$ as the inclusion of $B_q0$ in $\mathcal{H}$ (this is the definition of 0 being the neutral element), hence $p_!(\{0\} \times B_q0) = B_q0$ and this concludes the proof.

□

4.1.3. **Proposition :** *Let $\mathcal{H}$ be a pre-Banach locale, the following conditions are equivalent:*

*(LB1) The open sublocales $B_q0$ form a basis of neighborhoods of 0.*

*(LB2) $\mathcal{H}$ is metric for the distance induced by $\|.\|$.*

A pre-Banach locale satisfying either *(LB1)* or *(LB2)* is called a Banach locale, we will soon see that there is no need for a completeness assumption: it will be automatic.

**Proof :**

We will use the same notation $s, p$ as in proposition 4.1.2. Assume *(LB1)*, and let $U$ be any open of $\mathcal{H}$. Consider the open sublocale $p^*U \subset \mathcal{H} \times \mathcal{H}$, and decompose it as a union of basic open sublocales

$$p^*U = \bigvee_{i \in I} A_i \times B_i$$

where $A_i$ and $B_i$ are open sublocales of $\mathcal{H}$. Let $i$ such that $(A_i \times B_i) \wedge U \times \{0\}$ is positive. Then $B_i \wedge \{0\}$ is also positive, hence $0 \in B_i$, and from the hypothesis, there exists $q$ such that $B_q0 \leqslant B_i$. This implies that for each $i$ such that $0 \in B_i$, as $A_i \times B_q0 \leqslant p^*U$ one has $B_qA_i = p_!(A_i \times B_q0) \leqslant U$ hence $A_i \triangleleft_q U$.

Now as $U \times \{0\}$ is locally positive and a subset of $p^*(U)$:

$$U \times \{0\} \leqslant \bigvee_{\substack{i \in I \\ (A_i \times B_i) \wedge (U \times \{0\}) > \emptyset}} \leqslant \bigvee_{\substack{i \in I \\ 0 \in B_i}} A_i \times B_i$$

Applying $\pi_1$ one gets (as any $B_i$ having a point is positive) that

$$U \leqslant \bigvee_{\substack{i \in I \\ 0 \in B_i}} A_i \leqslant \bigvee_{\substack{i \in I \\ A_i \triangleleft U}} A_i,$$

which concludes the proof of the first implication.

Assume now *(LB2)*, let $U$ be an arbitrary neighborhood of 0, then as $\mathcal{H}$ is metric, there exists an open sublocale $V$ such that $0 \in V$ and $V \triangleleft U$. In particular, there exists $q$ such that $B_qV \leqslant U$, and as $0 \in V$ one has:

$$B_q0 \subset B_qV \subset U$$

which proves *(LB1)* and concludes the proof of the proposition.

□

52

4.1.4. **Proposition :** *Let $\mathcal{H}$ be a pre-Banach locale, then its completion $\widetilde{\mathcal{H}}$ is naturally endowed with a structure of Banach locale such that the map $\mathcal{H} \rightarrow \widetilde{\mathcal{H}}$ is a linear isometric map.*

# **Proof :**

Everything comes more or less immediately from 3.3.11 for the construction of operations and from 3.2.3 and 3.2.4 for the verification of the axioms:

Indeed, as $\mathcal{H} \times \mathcal{H}$ has a fiberwise dense image in $\widetilde{\mathcal{H}} \times \widetilde{\mathcal{H}}$, the canonical (uniform) map $p : \mathcal{H} \times \mathcal{H} \rightarrow \mathcal{H} \rightarrow \widetilde{\mathcal{H}}$ extends into a map $\widetilde{\mathcal{H}} \times \widetilde{\mathcal{H}} \rightarrow \widetilde{\mathcal{H}}$. Similarly, the opposite map $m : \mathcal{H} \rightarrow \mathcal{H}$ is isometric and hence extends into a map $m : \widetilde{\mathcal{H}} \rightarrow \widetilde{\mathcal{H}}$ and one checks all the group axioms on $\widetilde{\mathcal{H}}$ because they hold in $\mathcal{H}$, that $\widetilde{\mathcal{H}}$ is metric and that $\mathcal{H}^n$ has a fiberwise dense image in $\widetilde{\mathcal{H}}^n$.

The action of the locale of complex numbers on $\widetilde{\mathcal{H}}$ is obtained in the same way: for each $\lambda \in \mathcal{Q}[i]$ the multiplication by $\lambda$ is a uniform map $\mathcal{H} \rightarrow \mathcal{H}$ and hence extends into a map $\widetilde{\mathcal{H}} \rightarrow \mathcal{H}$, giving a map $\mathcal{Q}[i] \times \widetilde{\mathcal{H}} \rightarrow \widetilde{\mathcal{H}}$ and all the axioms of compatibility with the group law are also satisfied by a density argument.

Finally, we already know that there is a distance function on $\widetilde{\mathcal{H}}$ we only have to check that $\|x\| = d(0, x)$ is a norm and that $d(x, y) = \|x - y\|$. But this also immediately comes from a density argument by 3.2.4. $\square$

4.1.5. **Corollary :** *Banach locale are complete metric locales.*

# **Proof :**

Let $\mathcal{H}$ be a Banach locale, in particular $\mathcal{H}$ is a metric locale and hence by 3.2.2 it identifies with a sublocale of $\widetilde{\mathcal{H}}$. More precisely, as the inclusion is a linear map, $\mathcal{H}$ identifies with a localic subgroup of a locally positive localic group $\widetilde{\mathcal{H}}$, hence thanks to the constructive version of the closed subgroups theorem proved by P.T. Johnstone in [11], one concludes that $\mathcal{H}$ is fiberwise closed (weakly closed in the terminology of [11]) in $\widetilde{\mathcal{H}}$ and hence is also complete (see the remark at the end of 3.3.12). $\square$

4.1.6. In particular, the action of $\mathcal{Q}[i]$ on a Banach locale extends to an action of its completion $\mathbb{C}$. Indeed (assuming that $\mathcal{H}$ is complete), the map $B_n 0 \times \mathcal{Q}[i] \rightarrow \mathcal{H}$ is uniform (it is $n$-Lipschitz) and hence it extends into $\overline{B_n 0} \times \mathbb{C} \rightarrow \mathcal{H}$. One has a family of compatible maps $B_n 0 \times \mathbb{C} \rightarrow \mathcal{H}$ which gives rise to a map $\mathcal{H} \times \mathbb{C} \rightarrow \mathcal{H}$.

4.1.7. Similarly to what is done in section 3.6, a pre-Banach space in the usual (constructive) sense is exactly the same as a pre-Banach locale whose underlying locale is a discrete topological space. To such a Banach space one can associate its completion which is going to be a Banach locale. Conversely to any Banach locale one can associate its space of points which is a Banach space, and these

53

two constructions induce an equivalence between the category of weakly spatial Banach locales (and linear map) and the category of Banach spaces (with bounded linear map).

## 4.2 The Localic Gelfand duality

4.2.1. **Definition :** A $C^*$ locale (or localic $C^*$ algebra) is a Banach locale $\mathcal{C}$, endowed with an involution $* : \mathcal{C} \to \mathcal{C}$ and a product $\mathcal{C} \times \mathcal{C} \to \mathcal{C}$ which satisfy the usual axioms for a $C^*$ algebra:

- $\mathcal{C}$ is a $\mathbb{C}$ algebra (i.e. the product is associative, distributes over the addition and is compatible with the action of $\mathbb{C}$).
- The $*$ involution is $\mathbb{C}$ anti-linear and satisfies $(ab)^* = b^*a^*$.
- One has: $\|ab\| \leqslant \|a\|\|b\|$.
- One has: $\|a^*a\| = \|a\|^2$.

All the axioms are equalities (or inequalities with respect to the specialization order), hence are clearly preserved by pull-back and therefore if $\mathcal{C}$ is a $C^*$ algebra and $f$ is a geometric morphism to the base topos then $f^\#(\mathcal{C})$ is also a $C^*$ locale. And if $\mathcal{C}$ is a (pre)-Banach locale endowed with an $*$ map and a map $\mathcal{C} \times \mathcal{C} \to \mathcal{C}$ such that for some open surjection $f$, $f^\#(\mathcal{C})$ is a $C^*$ algebra for those structure then $\mathcal{C}$ is a $C^*$ algebra.

The main result of this section will be an anti-equivalence of categories between the categories of abelian unital $C^*$ locales and compact regular locales. The “difficult” part lies in the construction of the two functors, and the proof that they are compatible with pull-back along geometric morphisms. Indeed once it is done, one can apply 2.3.17 to reduce the proof of the equivalence to the case of spatial $C^*$ algebras and completely regular compact locales which is already known ([1] [7]). Actually, even the construction of the two functors could be avoided since we know that the notion of $C^*$ locale is the “stackification” of the notion of $C^*$ algebra (it is a direct consequence of the observations made in 3.6.5), and one can prove (applying 2.6.6) a similar result for compact regular locales and compact completely regular locales. Hence the already known equivalence between unital abelian $C^*$ algebras and compact completely regular locales immediately yields the equivalence between the “stackified” notions, but we think that it is important to have an explicit construction of these functors without having to use descent theory.

4.2.2. **Proposition :** Let $X$ be a compact regular locale, then $[X, \mathbb{C}]$ is a $C^*$ algebra, for the addition, product and involution given by the addition, the product and the complex conjugation of $\mathbb{C}$, and the norm given by:

$$B_q 0 = [X \ll f^* D_q]$$

54

where $D_q$ denotes the open disc of radius $q$ in $\mathbb{C}$, and $[X \ll f^*D_q]$ denotes the basic open which classifies the $f$ such that $X \ll f^*D_q$.

# **Proof :**

$[X, \mathbb{C}]$ is indeed locally positive by 2.6.5. For the rest, we recall that Hyland gave in [10] a description of the theory classified by $[X, Y]$ in terms of the basic propositions $[U \ll f^*V]$ for $U \in \mathcal{O}(X)$ and $V \in \mathcal{O}(Y)$. From this description, we immediately obtain that:

$$\bigvee_{q' < q} B_{q'} 0 = B_q 0;$$ $$\bigvee_n B_n 0 = [X, \mathbb{C}].$$

Also, as 0 is the point corresponding to the function constant equal to 0, one has indeed $0 \in B_q 0$.

Hence the $B_q 0$ indeed define a function $\|\cdot\| : [X, \mathbb{C}] \to \overleftarrow{\mathbb{R}_+^\infty}$ such that $\|0\| = 0$, and such that $\bigvee_n B_n 0 = [X, \mathbb{C}]$.

All the algebraic axioms (including the triangular inequality) are checked on generalized point exactly as one does for classical points in the usual (constructive) case.

A basic open $[U \ll f^*V]$ (for $U$ positive) contains 0 if $U \ll \bigvee_{0 \in V} X$, but this implies that there exists a finite set $F$ included in $\{0 \in V\}$ such that $U \leqslant \bigvee_{f \in F} X$. A finite set is inhabited or empty, hence either $F$ is empty and $U = \emptyset$ or $F$ is inhabited and $0 \in V$. In the first case $[U \ll f^*V] = [X, \mathbb{C}]$ contains all the $B_q 0$. In the second case one has a $q$ such that $D_q \ll V$ and hence $0 \in B_q 0 = [X \ll f^*(D_q)] \leqslant [U \ll f^*(V)]$ which proves that the $B_q 0$ form a basis of neighborhood of 0, and hence $[X, \mathbb{C}]$ is a Banach locale.

□

4.2.3. We now want to construct the spectrum of a $C^*$ locale. We will start by defining the locale $\text{Fn } \mathcal{H}$ of linear forms of norm smaller than 1 on a Banach locale $\mathcal{H}$ (the spectrum being the space of characters, it will be a sublocale of this locale). It generalizes the locale $\text{Fn } E$ constructed in [16] and [6].

**Proposition :** *Let $\mathcal{H}$ be a Banach locale. There exists a sublocale $\text{Fn } \mathcal{H} \subset [\mathcal{H}, \mathbb{C}]_1$ which classifies the linear forms of norm smaller or equal to one on $\mathcal{H}$. If $\mathcal{C}$ is a unital commutative $C^*$ locale, then there exists a sublocale $\text{Spec } \mathcal{C} \subset [\mathcal{C}, \mathbb{C}]_1$ which classifies characters of $\mathcal{C}$.*

# **Proof :**

One can for example define the locale $\text{Fn } \mathcal{H}$ as the intersection of the equalizer of the following two diagrams:

$$[\mathcal{H}, \mathbb{C}]_1 \Rightarrow [D_1 \times \mathcal{H}, \mathbb{C}]_1$$

where $D_1$ denotes the open unit ball in $\mathbb{C}$ and the two maps are the maps defined on generalized elements by: $f \mapsto ((\lambda, x) \mapsto \lambda f(x))$ and $f \mapsto ((\lambda, x) \mapsto f(\lambda x))$, and where the distance on $D_1 \times \mathcal{H}$ is the max distance.

55

And,

$$[\mathcal{H}, \mathbb{C}]_1 \Rightarrow [\mathcal{H} \times \mathcal{H}, \mathbb{C}]_1$$

where $\mathcal{H} \times \mathcal{H}$ is endowed with the norm $\|x_1\| + \|x_2\|$ and the two maps are given by: $f \mapsto ((x, y) \mapsto f(x + y))$ and $f \mapsto ((x, y) \mapsto f(x) + f(y))$.

A map $X \rightarrow \text{Fn } \mathcal{H}$ is then exactly the data (internally to $X$) of a metric map from $\mathcal{H} \rightarrow \mathbb{C}$ which is additive and linear with respect to complex numbers smaller than 1. As it is also linear with respect to integers, it is linear on $nD_1$ for all $n$ and this forms an open cover of $\mathbb{C}$ so it concludes the proof.

If now $\mathcal{C}$ is a unital $C^*$ locale, then one defines $\text{Spec } \mathcal{C}$ as the intersection of the two previous equalizers with the pull-back of $\{1\} \subset \mathbb{C}$ by the map of evaluation on the unit on $[\mathcal{C}, \mathbb{C}]_1$ and with the equalizer of the following diagram:

$$[\mathcal{C}, \mathbb{C}]_1 \Rightarrow [B_1 0 \times B_1 0, \mathbb{C}]$$

where $B_1 0$ is the open unit ball of $\mathcal{C}$, and the distance $B_1 0 \times B_1 0$ is given by the max distance. The two maps are given by $f \mapsto ((x, y) \mapsto f(x)f(y))$ and $f \mapsto ((x, y) \mapsto f(xy))$.

A map factoring into $\text{Spec } \mathcal{C}$ exactly corresponds to an internal character of $\mathcal{C}$.

#### 4.2.4. The following result is a localic version of the Banach-Alaoglu theorem.

**Proposition :** *Let $\mathcal{H}$ be a Banach locale, $\mathcal{C}$ a unital commutative $C^*$ locale, then the locales $\text{Fn } \mathcal{H}$ and $\text{Spec } \mathcal{C}$ are compact regular locales.*

##### **Proof :**

Compact regular locales descend along open surjections: for example because for a locale being compact and regular is the same thing as having a map to the point which is both proper and separated (see [12] C.3.2.10) and because both proper maps and separated maps descend along open morphisms, (see [12]C5.1.7). Hence it is enough to prove that some pull-back of $\text{Fn } \mathcal{H}$ and $\text{Spec } \mathcal{C}$ by an open surjection is compact and regular to conclude. In particular, by 2.3.17 one can freely assume that $\mathcal{H}$ and $\mathcal{C}$ are weakly spatial and hence that it is the completion of some Banach space $H$ or $C^*$ algebra $C$. But in this situation, a linear form or a character on the Banach locale is exactly the same as a linear form or a character on the set of points (by extension to the completion) and hence (the pull-back of) $\text{Fn } \mathcal{H}$ and $\text{Spec } \mathcal{C}$ classify the same theory as the locale $\text{Fn } H$ and $\text{Spec } C$ (also called $\text{MFn } C$) studied in [16] and [1] for the case of Grothendieck toposes, and in [6] and [7] for general elementary toposes. These references prove that these locales are indeed compact (completely) regular. $\square$

56

4.2.5. **Theorem :** *The previous two constructions $X \rightarrow [X, \mathbb{C}]$ and $\mathcal{C} \rightarrow \text{Spec } \mathcal{C}$ induce an anti-equivalence of categories between unital abelian $C^*$ locales and compact regular locales.*

**Proof :**

These two constructions are defined in terms of the theory they classified and hence we can easily check that they are preserved by pull-back along geometric morphisms. They correspond to the well known notion of (completion of the) space of continuous functions on $X$ and spectrum of a $C^*$ algebra when $X$ is completely regular and when $\mathcal{C}$ is weakly spatial. Moreover the two canonical maps “evaluation at $x \in X$” from $X$ to $\text{Spec } [X, \mathbb{C}]$ and “evaluation at $c \in \mathcal{C}$” from $\mathcal{C}$ to $[\text{Spec } \mathcal{C}, \mathbb{C}]$ are preserved by pull-back (a proof by generalized points shows it immediately).

Hence, applying 2.3.17 one can pull-back (along an open surjection) those two maps to a similar situation but with $\mathcal{C}$ and $[X, \mathbb{C}]$ weakly spatial (hence with $X$ completely regular by 2.6.6). We can then conclude that the pull-back (along an open surjection) of the two canonical maps are isomorphisms from the usual constructive Gelfand duality (proved in [1] for Grothendieck toposes, and generalized in [7] to arbitrary elementary toposes). And hence, as pull-back by an open surjection is conservative, these two canonical maps are isomorphisms. This proves that the two constructions are inverse from each other, the fact that they form an equivalence of categories follows immediately from the same argument. $\square$

## References

## References

- [1] Banaschewski, Bernhard and Mulvey, Christopher J. A globalisation of the Gelfand duality theorem. *Annals of Pure and Applied Logic*, 137(1):62–103, 2006.
- [2] Borceux, F. *Handbook of Categorical Algebra: Volume 3, Sheaf Theory*, volume 3. Cambridge University Press, 1994.
- [3] Bourbaki, Nicolas. *Elements of Mathematics: General Topology*. Hermann, 1966.
- [4] Bunge, Marta. An application of descent to a classification theorem for toposes. In *Mathematical Proceedings of the Cambridge Philosophical Society*, volume 107, pages 59–79. Cambridge Univ Press, 1990.
- [5] Burden, CW and Mulvey, CJ. Banach spaces in categories of sheaves. In *Applications of sheaves*, pages 169–196. Springer, 1979.
- [6] Coquand, Thierry. A Direct Proof of the Localic Hahn-Banach Theorem. *to appear*, 1999.

57

[7] Coquand, Thierry and Spitters, Bas and others. Constructive Gelfand duality for C\*-algebras. In *Mathematical Proceedings of the Cambridge Philosophical Society*, volume 147, pages 323–337. Cambridge Univ Press, 2009.[8] Fell, James Michael Gardner and Douady, Adrien and Dal Soglio-Hérault, Letizia. *Induced representations and Banach \*-algebraic bundles*. Springer-Verlag Berlin, 1977.[9] Simon Henry. *Des topos à la géométrie non commutative par l'étude des espaces de Hilbert internes*. PhD thesis, Université Paris 7, 2014.[10] Hyland, JME. Function spaces in the category of locales. In *Continuous lattices*, pages 264–281. Springer, 1981.[11] Johnstone, Peter T. A constructive “closed subgroup theorem” for localic groups and groupoids. *Cahiers de Topologie et Géométrie Différentielle Catégoriques*, 30(1):3–23, 1989.[12] Johnstone, P.T. *Sketches of an elephant: a topos theory compendium*. Clarendon Press, 2002.[13] Joyal, A. and Tierney, M. *An extension of the Galois theory of Grothendieck*. American Mathematical Society, 1984.[14] Ieke Moerdijk. The classifying topos of a continuous groupoid. II. *Cahiers de Topologie et Géométrie Différentielle Catégoriques*, 31(2):137–168, 1990.[15] Moerdijk, Izak and Wraith, GC. Connected locally connected toposes are path-connected. *Transactions of the American Mathematical Society*, 295(2):849–859, 1986.[16] Mulvey, Christopher J and Pelletier, Joan Wick. A globalization of the Hahn-Banach theorem. *Advances in Mathematics*, 89(1):1–59, 1991.[17] Picado, Jorge and Pultr, Aleés. *Frames and Locales: topology without points*. Springer, 2012.[18] Vickers, Steven. Localic completion of generalized metric spaces I. *Theory and Applications of Categories*, 14(15):328–356, 2005.

58