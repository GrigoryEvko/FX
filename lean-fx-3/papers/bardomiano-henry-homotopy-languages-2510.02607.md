arXiv:2510.02607v1 [math.CT] 2 Oct 2025

# Homotopy Languages

César Bardomiano Martínez and Simon Henry

October 6, 2025

## Abstract

We attach to each weak model category $\mathcal{M}$ a class of first order formulas about the fibrant objects of $\mathcal{M}$ whose validity is invariant under homotopies and weak equivalences. This is a generalization of the classical Blanc-Freyd Language of categories—which involves formula avoiding equality on objects and which are invariant under isomorphism and equivalences of categories. In particular, we obtain similar homotopy invariant languages for 2-categories, bicategories, chain complexes, Kan complexes, quasi-categories, Segal spaces, and so on...

## Contents

|  **1 Introduction** | **2**  |
| --- | --- |
|  **2 The homotopy invariant language** | **8**  |
|  2.1 Syntactic approach: The first-order language of a generalized algebraic theory . . . . . | 8  |
|  2.2 Categories of models and their weak factorization systems . . . . . | 14  |
|  2.3 The Category theoretic approach: The first-order language of a $\kappa$-clans . . . . . | 18  |
|  2.4 The language of a weak model category and two invariance theorems . . . . . | 25  |
|  **3 Examples of languages of model categories** | **29**  |
|  3.1 Categories . . . . . | 33  |
|  3.2 2-categories and Bicategories . . . . . | 36  |

2020 Mathematics Subject Classification. 18A15,18C10,18N40,18N45,55U35.
Keywords. Dependent type, Model categories, Generalized algebraic theory.
emails: cbard035@uottawa.ca, shenry2@uottawa.ca

1

3.3 Bounded below chain complexes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 38
3.4 Unbounded chain complexes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 41
3.5 Topological spaces . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 42
3.6 Kan complexes and quasi-categories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 43
3.7 Reedy languages . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 47
3.8 Segal spaces . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 49
3.9 Functors and Isofibrations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 52
4 Language invariance under Quillen equivalences . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 56
4.1 The third and fourth invariance theorem . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 56
4.2 Invariance along Barton trivial fibrations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 62
4.3 Path objects for weak model categories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 67
4.4 Proof of main theorem . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 88
A Infinitary Cartmell theories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 89
A.1 Generalized algebraic theories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 90
A.2 Substitution property . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 96
A.3 Equivalence relation on judgments . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 98
A.4 The category of generalized $\kappa$-algebraic theories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 102
A.5 Construction and properties of the syntactic category $\mathbb{C}_T$ . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 105
B Contextual categories and Cartmell theories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 110
B.1 $\kappa$-contextual categories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 111
B.2 Interlude: categorical facts . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 114
B.3 The equivalence between $\kappa$-GAT and $\kappa$-CON . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 116
B.4 Models of a generalized Cartmell theory . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 133
B.5 Coclans and contextual categories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 136
C Weak model categories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 143
C.1 Review . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 144
C.2 Weak Reedy model structure . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 148
1 Introduction

It is a well-known result in category theory (see for example [Fre76], [Bla78]) that any property of a category, or of objects and morphisms of this category, that does not use equality between objects is automatically invariant both under equivalence of categories, and under substitution of all the objects and morphisms involved by isomorphic ones consistently.

2

For example, because the notion of limit in a category is naturally formulated without using equality between objects we automatically know that equivalences of categories preserve limits, or that if two diagrams are naturally isomorphic then a limit for one is also a limit for the other.

To be a little more precise, the above-mentioned results are about first-order formulas in which we can have quantifiers over all objects of the category, or over all morphisms in a given hom-set “hom($X, Y$)”. We can use equality between two terms taken from the same hom($X, Y$), but not between two terms of type “objects”, or two terms that are in different hom-sets.

For example, the property of an object $X$ to be a terminal object, which can be written as

$$\text{isTerminal}(X) := \forall Y \in \text{Ob}, (\exists v \in \text{Hom}(Y, X) \text{ and } \forall u, w \in \text{Hom}(Y, X), u = w)$$

is an instance of such a formula, but the following formula

$$\begin{aligned} \forall X, Y \in \text{Ob}, \forall f \in \text{Hom}(X, Y), \forall g \in \text{Hom}(Y, X), \\ (f \circ g = \text{id}_Y \text{ and } g \circ f = \text{id}_X \Rightarrow X = Y) \end{aligned}$$

which states that the category we are working with is skeletal, or the formula

$$\begin{aligned} \forall X, Y \in \text{Ob}, \forall f \in \text{Hom}(X, Y), \forall g \in \text{Hom}(Y, X), \\ (f \circ g = \text{id}_Y \text{ and } g \circ f = \text{id}_X \Rightarrow f = \text{id}_X) \end{aligned}$$

which expresses that identities are the only isomorphisms, are not of this form: the first one involves the equality $X = Y$, and the second one involves an equality $f = \text{id}_X$ that is not correctly typed as $f \in \text{Hom}(X, Y)$. And these two formulas are indeed not invariant under equivalence of categories$^1$.

Note that in order for this to make sense, it is key to use a notion of “dependent types”. Indeed, we need to be able to formulate the idea that a morphism $f$ is in $\text{Hom}(X, Y)$, without being able to say that $s(f) = X$ and $t(f) = Y$ as this would involve using equality between objects. So, given two objects $X$ and $Y$, we need to be able to consider the type of arrows from $X$ to $Y$ as a primitive notion.

Now, it is natural to expect that similar results can be generalized to higher categories. For example, we expect (and it can be shown) that a

$^1$As they are formulas with no free parameters, invariance under substitution by isomorphic objects does not really make sense.

3

property of 2-categories or bicategories that does not use equality between objects or between 1-arrows will also be invariant under biequivalences. One can also expect it can be generalized to other sorts of higher structures, for example a result about multicategories not using equality between objects should also have similar invariance properties.

The main goal of this paper is, informally, to establish a version of this result for essentially any kind of higher structure independently of the type of structure or the “categoricity level”. The only requirement is that the sort of higher structure we are considering must be organized as the fibrant objects of a model category (or semi-model category, or weak model category).

That is, we will attach to every (semi/weak) model category a “first-order language”, whose formulas are statements about objects of the category (possibly with parameters) such that

- Replacing the value of the parameters by homotopically equivalent parameters does not change the validity of a formula.
- Two weakly equivalent fibrant objects satisfy the same formulas.

We call these two results respectively the 1st and 2nd invariance theorem, and their precise statement is given as theorem 2.38. We will now go into a little more detail about how this language is defined, and explain the role of the different sections of the paper.

As mentioned above, our language is based first on dependent types. More precisely, we use the formalism of “Generalised algebraic theory” in the sense of Cartmell ([Car78]) as our basis, which are algebraic theories with dependent types. If we compare our approach to traditional model theory, our choice of a generalized algebraic theory T plays a role similar to the choice of a signature. However, contrary to traditional model theory, it is crucial for us that the theory T (i.e., our signature) can be any generalized algebraic theory, in particular the theory T can include equality axioms. This is in part because the first-order logic we will introduce on top of it will not have equality, so algebraic equations cannot be treated as axioms like any other.

## Overview

Starting from a generalized algebraic theory T, we build in section 2.1 the first-order language L^T, as well as its quotient L^T where “provably equivalent formulas” (for a relatively weak notion of proof) are identified.

4

The idea is that for each formula, the (free) variables are taken from a context of the theory $T$, and there can be no equality at all. In particular, the theory $T$ itself can have axioms that are not part of this first order language $\mathcal{L}^T$. We will see through examples how in some cases, some notion of equality, for example the case of equality between morphisms in the same $\operatorname{Hom}(X, Y)$ in the example of categories we started from, can be recovered indirectly using certain equality axioms in the theory $T$ itself.

Since we want to be able to do infinitary logic, we use everywhere an infinitary generalization of the notion of generalized algebraic theory that is introduced in section A. However, a reader familiar with generalized algebraic theories can probably guess how it works. The logic $\mathcal{L}^T$ we introduce can include arbitrary disjunction and conjunction, as well as quantifiers ranging on infinitely many variables. We will denote by $\mathcal{L}_{\lambda,\kappa}^T$ the language where the formulas only include disjunction and conjunction on less than $\lambda$ subformulas and where a quantifier quantifies on less than $\kappa$ many variables at the same time. The $\kappa$ is very often omitted from the notation for technical reasons, but see theorem 2.12.

In section 2.2 we review quickly some important properties of the category of models of a generalized algebraic theory, most notably their canonical weak factorization system. In section 2.3 we explain how the language defined in section 2.1 can be given an alternative categorical definition that can be applied to any “clan” — clans are a notion of a categories with a class of fibrations — for any generalized algebraic theory $T$, the syntactic, or contextual, category $\mathbb{C}_T$ is a clan. And we show that the category-theoretic definition of the language of the clan is equivalent to the syntactic definition of the language of any such generalized algebraic theory. Note that every clan can be shown to be the syntactic category of a generalized algebraic theory (and we prove more generally that in our infinitary setting any “$\kappa$-clan” is the syntactic category of a generalized $\kappa$-algebraic theory, this is in section B) so that the language can still be seen syntactically as the “first-order language” of some generalized algebraic theory, but we now also have the option of working “categorically” with it without relying on a choice of a syntax.

This reinterpretation in terms of clans is the key to associate a language to any model category: Given a (weak) model category $\mathcal{M}$ we take the category $\mathcal{M}^{\mathrm{COF}}$ of cofibrant objects and cofibration between them. This category constitutes a co-clan (the opposite of a clan) and we can take the language associated to it. This is what we call the language of the model category $\mathcal{M}$. We review briefly the general theory of weak model categories

5

in section C.1 and in section 2.4 we explain in detail how this language of $\mathcal{M}$ actually talks about the objects of $\mathcal{M}$ and prove the first two invariance theorems mentioned above.

To give a general picture of how this language works, if $\mathcal{M}$ is our model category, each formula in the language has a “context” $C$, which informally can be thought of as the list of free variables that can appear in the formula as well as their types. This “context” $C$ is concretely just a cofibrant object of $\mathcal{M}$. An interpretation of the context $C$ into an object $X \in \mathcal{M}$ is just a map $v : C \rightarrow X$. And given $\phi$ a formula in context $C$ and $v : C \rightarrow X$ a map, $\phi(v)$ can be either true or false. We write

$$M \vdash \phi(v)$$

if $\phi(v)$ is true.

Section 2 ends with our first two invariance theorems, stated as theorem 2.38:

**$1^{st}$ Invariance Theorem.** *If $X$ is fibrant and $v : C \rightarrow X$ is homotopic to $v' : C \rightarrow X$ then $M \vdash \phi(v) \Leftrightarrow M \vdash \phi(v')$.*

**$2^{nd}$ Invariance Theorem.** *If $F : X \rightarrow Y$ is a weak equivalence between fibrant objects, then $X \vdash \phi(v) \Leftrightarrow Y \vdash \phi(f(v))$.*

To give a more concrete example of all this, when $\mathcal{M}$ is the canonical or folk model structure on categories, our construction recovers the language of categories as in [Fre76] or [Bla78]. Now, the formula

$$\forall Z \in \text{Ob}, \forall g, h \in \text{Hom}(Y, Z), g \circ f = h \circ f \Rightarrow g = h$$

is a formula in context $X, Y \in \text{Ob}, f \in \text{Hom}(X, Y)$ which corresponds to the (cofibrant) category $\mathcal{C}$ which has two objects $X$ and $Y$ and a unique non-identity arrow $f : X \rightarrow Y$. A map from $\mathcal{C}$ to another category $\mathcal{D}$ is the choice of an arrow $f$ in $\mathcal{D}$ and $\phi(f)$ is true if and only if $f$ is an epimorphism. The second invariance theorem says (in this special case) that equivalence of categories preserves epimorphisms, and the first invariance theorem that if $f$ is isomorphic to another arrow then one is an epimorphism if and only if the other is.

In section 3 we show how our notion of language specializes to many classical model structures. We also discuss briefly some general (but informal) tools to construct this language explicitly for any model structure.

6

Finally, in section 4 we prove two more invariance theorems (theorem 4.2), that are this time about the expressive power of the language and can be stated informally as:

3$^{rd}$ **Invariance Theorem.** *If $A$ and $B$ are two cofibrant objects of $\mathcal{M}$, then each formula in context $A$ can be translated into a formula in context $B$ that is “equivalent” in the sense that its interpretation in any fibrant object is the same.*

4$^{th}$ **Invariance Theorem.** *If $\mathcal{M}$ and $\mathcal{N}$ are two Quillen equivalent weak model categories, then any formula in the language of $\mathcal{M}$ can be similarly translated into an equivalent formula in the language of $\mathcal{N}$.*

More details on these will be given in the introduction to section 4.

One should also mention that, despite the paper being stated in the language of “weak” model categories, all our examples are actual Quillen model categories, and the reader can replace weak model categories by Quillen model categories almost everywhere. The only reason for which we consider weak model categories is because the extra generality doesn’t affect any of our results, and also because at some point in the proof of the second half of theorem 4.2 we need to use our construction of a language to something that in general will not be a full Quillen model category (even if we only try to prove theorem 4.2 for Quillen model categories). The main difference between weak model categories and Quillen model categories is that many results (and axioms) of a Quillen model category can only be applied to arrows from cofibrant to fibrant objects in a weak model category. A review of the notion of weak model category is in section C.1.

Notably, we will use the terminology “*core cofibration*” to mean cofibration between cofibrant objects and “*core fibration*” to mean fibration between fibrant objects.

The paper has three appendices that serve to review or introduce basic material. They can either be read first, or skipped entirely: Section A reviews Cartmell’s notion of generalized algebraic theory, and generalizes it to the infinitary case. The goal of section B is to establish the link between generalized $\kappa$-algebraic theory and a notion of $\kappa$-clan, with a notion of $\kappa$-contextual category as an intermediate. This result is absolutely crucial for the paper, but is a very expected generalization of what happens in the finitary case. Finally, section C reviews some material on weak model categories and introduces a notion of Reedy model categories in that context, which is only used in section 4.

7

## Further remarks

We finish by mentioning that this work is closely related to Makkai's notion of 'First-order logic with dependent sorts' or FOLDS from [Mak95]. In a sense, Makkai's FOLDS corresponds to the special case where $T$ is the theory of presheaves on a direct category $I$, encoded using dependent type axioms only, with an additional equality predicate for the types corresponding to maximal objects of $I$. Because Makkai does not make assumptions about the existence of a model structure he only establishes an invariance theorem for what he calls 'very surjective maps' (our 'anodyne fibrations'), that is the analogous to our theorem 2.32, more general notions of equivalence and homotopy are not clearly available in his setting.

In conclusion, the present work is at the same time considering a more general algebraic setting (by allowing terms and type in $T$), but also is restricting the setting by assuming the presence of a model structure that gives a good homotopy theory to be invariant under, and allows obtaining much more interesting results. This seems to make our approach considerably more usable in practice, given the richness of examples it potentially covers.

It should be noted however that there are some results in [Mak95] that we have not yet been able to generalize to this new setting: Makkai established several results that essentially say that any formula that has the desired invariance properties is equivalent to one in the language introduced. Similar results are also given in [Fre76] and [Bla78], and this paper contains no analogue to these results.

## Acknowledgment

This work was supported by the Natural Sciences and Engineering Research Council of Canada (NSERC), funding reference number RGPIN-2020-067 awarded to Simon Henry.

## 2 The homotopy invariant language

### 2.1 Syntactic approach: The first-order language of a generalized algebraic theory

In this section, we give a very classic syntactical approach to the language we consider in this paper. We start from a generalized algebraic theory, and we build its first-order language on top of it.

8

Since we aim to do infinitary logic, we enhance Cartmell's notion of generalized algebraic theory to what we call *generalized $\kappa$-algebraic theory* for $\kappa$ a regular cardinal, which we develop in detail in section A. Nevertheless, this generalization is straightforward and a reader familiar with Cartmell's formalism should be able to guess how it works and read this section directly. The main difference to keep in mind is that our contexts are sequences of typed variables indexed by ordinals less than $\kappa$ instead of finite sequences. A consequence of this is that we need to use more heavily the "generalized display maps" that correspond to "projections" from a context $(x_i : X_i)_{i<\gamma}$ to $(x_i : X_i)_{i<\beta}$ for arbitrary $\beta < \gamma < \kappa$, where the classical theory uses the display maps that corresponds to projections that only forget the last variable.

In what follows, we fix $\kappa$, $\lambda$ two regular cardinals and $T$ a generalized $\kappa$-algebraic theory. We will define the first-order language of $T$ with $\lambda$-small conjunction and disjunction, denoted $\mathcal{L}_\lambda^T$ or $\mathcal{L}_{\lambda,\kappa}^T$.

More precisely, for each context $\Gamma$ of $T$, we will define a set $\mathcal{L}_\lambda^T(\Gamma)$ of "$T$-formulas in context $\Gamma$". Essentially, these are first-order formulas with $\lambda$-small conjunctions and disjunctions whose free variables are the variables of the context $\Gamma$, in particular, they have less than $\kappa$-variables.

**Definition 2.1.** The sets $\mathcal{L}_\lambda^T(\Gamma)$ of $T$-formulas in context $\Gamma$ are defined inductively using the following rules:

1. For each context $\Gamma$, the true formula $\top$ and false formula $\bot$ are in $\mathcal{L}_\lambda^T(\Gamma)$.
2. If $\Phi \in \mathcal{L}_\lambda^T(\Gamma)$ then $\neg\Phi \in \mathcal{L}_\lambda^T(\Gamma)$.
3. For each collection of formulas $\Phi_i \in \mathcal{L}_\lambda^T(\Gamma)$, indexed by a $\lambda$-small set $I$, the conjunction and disjunction

$$\bigvee_{i \in I} \Phi_i \qquad \bigwedge_{i \in I} \Phi_i$$

are in $\mathcal{L}_\lambda^T(\Gamma)$.

4. Given two ordinals $\gamma < \alpha < \kappa$: If $\Gamma' \equiv \{x_\beta : \Gamma_\beta\}_{\beta<\alpha}$ is a context of length $\alpha$, and $\Gamma \equiv \{x_\beta : \Gamma_\beta\}_{\beta<\gamma}$ is the subcontext of length $\gamma$, then for any formula $\Phi \in \mathcal{L}_\lambda^T(\Gamma')$ we have formulas

$$\exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha} \Phi \qquad \forall\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha} \Phi$$

in $\mathcal{L}_\lambda^T(\Gamma)$.

9

The collection of all formulas $\{\mathcal{L}_{\lambda}^{T}(\Gamma)\}_{\Gamma \in T}$ is what we call *the language of $T$*. Often, we will simply refer to it by $\mathcal{L}_{\lambda}^{T}$.

*Remark 2.2.* The key point in theorem 2.1 is that we are not including atomic formulas other than $\top$ and $\bot$. In particular, the language *does not include any equality*. At this point it might be unclear how we get non-trivial formulae in this language as it seems that applying quantifiers, conjunction or disjunction to formulas that are either $\bot$ or $\top$ will never produce any formulas that are not immediately interpreted as $\bot$ or $\top$. Or even, on how we might obtain formulas with free variables. The central idea is that free variables appear thanks to the fact we quantify over dependent types, that is, types in which free variables can appear. The following examples will demonstrate these phenomena.

**Example 2.3.** Let $Cat$ be the generalized $\omega$-algebraic theory of categories as introduced in theorem A.7. Then, in the context $(x : \mathsf{Ob})$ we can write the formula

$$\phi(x) := (\forall y : \mathsf{Ob}, \exists f : \mathsf{Hom}(x, y), \top)$$

which expresses that for any object $y$ there is an arrow from $x$ to $y$. This simply means that $x$ is a weakly initial object. Indeed, $\top$ is a formula in context $(x : \mathsf{Ob}, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y))$, so that $\exists f : \mathsf{Hom}(x, y), \top$ is a formula in context $(x : \mathsf{Ob}, y : \mathsf{Ob})$, and $\forall y : \mathsf{Ob}, \exists f : \mathsf{Hom}(x, y), \top$ is a formula in context $(x : \mathsf{Ob})$.

The logic is still not strong enough to express many of the interesting category theoretic notions. For example, without any kind of equality predicate on morphisms there is no way to write down a formula for an initial object, or a limit. In the next example, we show how modifying the theory $Cat$ allows the recovery of equality on morphisms:

**Example 2.4.** We consider the theory $Cat_{\equiv}$ obtained by adding to the theory $Cat$ the following:

$$\begin{aligned} &x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y) \vdash \mathsf{Eq}(f, g) \text{Type} \\ &x, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash r_f : \mathsf{Eq}(f, f) \\ &x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash f \equiv g \\ &x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash a \equiv r_f \end{aligned}$$

One can easily see that a model of $Cat_{\equiv}$ is just a category, with the type $\mathsf{Eq}(f, g)$ being empty if $f \neq g$ and $\{r_f\}$ if $f = g$. In this new theory, we can

10

now form a formula “ $f = g$ ” in context $(x, y : \text{Ob}, f, g : \text{Hom}(x, y))$ which is defined as

$$(f = g) := (\exists v : \text{Eq}(f, g), \top).$$

Therefore, in the language $\mathcal{L}_\omega^{\text{Cat}_\omega}$ we can form formulas involving equality between parallel morphisms. Then, we recover the “language of categories” as studied in [Bla78] and [Fre76]. For example, we can form the formula “ $x$ is initial” in context $(x : \text{Ob})$ as

$$\text{isInitial}(x) := \forall y : \text{Ob}, (\exists f : \text{Hom}(x, y)) \wedge (\forall f, g : \text{Hom}(x, y), f = g).$$

**Construction 2.5.** If $f : \Delta \rightarrow \Gamma$ is a context morphism and $\phi \in \mathcal{L}_\lambda^T(\Gamma)$, then we can define its pullback $f^*\phi$. This pullback is obtained by substituting the free variables of $\phi$ by the components of $f$. Formally, this is defined inductively as:

1. $f^*\top := \top$ and $f^*\bot := \bot$.
2. $f^*(\neg\Phi) := \neg f^*\Phi$.
3. $f^*(\bigvee_{i \in I} \Phi_i) := \bigvee_{i \in I} f^*\Phi_i$ and $f^*(\bigwedge_{i \in I} \Phi_i) := \bigwedge_{i \in I} f^*\Phi_i$.
4. If $\Gamma' \equiv (\Gamma, x_1 \in X_1, \dots, x_\alpha \in X_\alpha)$ then

$$f^*(\exists(x_1 \in X_1, \dots, x_\alpha \in X_\alpha)\Phi) := \exists(x_1 \in f^*X_1, \dots, x_\alpha \in f^*X_\alpha)f^*\Phi,$$

$$f^*(\forall(x_1 \in X_1, \dots, x_\alpha \in X_\alpha)\Phi) := \forall(x_1 \in f^*X_1, \dots, x_\alpha \in f^*X_\alpha)f^*\Phi,$$

where $f^*X_i$ denotes the pullback of types, obtained by substitution, that is, the types appearing in the canonical pullback of the generalized display map:

$$(\Delta, f^*X_1, \dots, f^*X_\alpha) \longrightarrow (\Gamma, X_1, \dots, X_\alpha)$$
$$\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \longrightarrow \Gamma.$$

**Definition 2.6.** For each context $\Gamma$ in $T$ we define the relation $\vdash_\Gamma$ on $\mathcal{L}_\lambda^T(\Gamma)$ as the smallest family of relations such that:

1. $\vdash_\Gamma$ is a transitive and reflexive relation on $\mathcal{L}_\lambda^T(\Gamma)$.
2. $\forall \Phi \in \mathcal{L}_\lambda^T(\Gamma)$, $\Phi \vdash_\Gamma \top$ and $\bot \vdash_\Gamma \Phi$.

11

3. $\forall \Phi \in \mathcal{L}_{\lambda}^{T}(\Gamma), \Phi \wedge \neg \Phi \vdash \bot$ and $\top \vdash \Phi \vee \neg \Phi$.
4. For any $\lambda$-small family $(\Phi_i)_{i \in I} \in \mathcal{L}_{\lambda}^{T}(\Gamma)$ we have

$$\bigvee_{i \in I} \Phi_i \vdash_{\Gamma} \Psi \Leftrightarrow \forall i, (\Phi_i \vdash_{\Gamma} \Psi)$$

$$\Psi \vdash \bigwedge_{i \in I} \Phi_i \Leftrightarrow \forall i, (\Psi \vdash_{\Gamma} \Phi_i)$$

5. For $\Gamma' \equiv \left( \Gamma, \left\{ x_{\beta} : \Gamma'_{\beta} \right\}_{\gamma \in \beta < \alpha} \right)$ a context extension, with $p : \Gamma' \rightarrow \Gamma$ the corresponding generalized display map, $\Psi \in \mathcal{L}_{\lambda}^{T}(\Gamma')$ and $\Phi \in \mathcal{L}_{\lambda}^{T}(\Gamma)$ we have

$$\exists \{ x_{\beta} : \Gamma_{\beta} \}_{\gamma \in \beta < \alpha} \Psi \vdash_{\Gamma} \Phi \Leftrightarrow \Psi \vdash_{\Gamma'} p^* \Phi,$$

$$\Phi \vdash_{\Gamma} \forall \{ x_{\beta} : \Gamma_{\beta} \}_{\gamma \in \beta < \alpha} \Psi \Leftrightarrow p^* \Phi \vdash_{\Gamma'} \Psi.$$

While we have not included the following in the definition, we can show that:

**Proposition 2.7.** *If $f : \Delta \rightarrow \Gamma$ is a context morphism in $T$, and $\Phi \vdash_{\Gamma} \Psi$ then $f^* \Phi \vdash_{\Delta} f^* \Psi$.*

*Proof.* We can show that if we define the relation $\Phi \vdash_{\Gamma}' \Delta$ to be “For all $f : \Delta \rightarrow \Gamma$, we have $f^* \Phi \vdash_{\Delta} f^* \Psi$” then it satisfies all the conditions from theorem 2.6. Which shows that $\vdash \Rightarrow \vdash'$ and hence concludes the proof. $\square$

In section B.4 we define a model for a generalized $\kappa$-algebraic theory $T$ is as a morphism of contextual categories $X : \mathbb{C}_T \rightarrow \mathbf{Fam}_{\kappa}$ where $\mathbf{Fam}_{\kappa}$ is a contextual categories of “families of sets”. By theorem B.50 this turns out to be equivalent to the naive definition of models where for each dependent type we have a family of sets, for each term a function, and equation axioms give us equations. Importantly for us, for each model $X$ and context $\Gamma$, there is a set $X(\Gamma)$, an element of which is a choice of an interpretation of each variable of $\Gamma$ as an element of the corresponding set in $X$. These $X(\Gamma)$ forms a functor on the category of contexts of $T$.

In what follows, we will use notation as explained in theorem B.51.

**Construction 2.8.** Given a model $X$ of our theory $T$, $\Gamma$ a context, $x \in X(\Gamma)$ and $\Phi \in \mathcal{L}_{\lambda}^{T}(\Gamma)$, we can interpret $\Phi(x)$ as a proposition *i.e.*, true or false in the obvious way by substituting the components of $x$ into $\phi$ and interpreting all the logic symbols in the usual way. Formally we have:

12

1. If $\Phi = \top$, then $\Phi(x)$ is true and if $\Phi = \bot$ then $\Phi(x)$ is false,
2. If $\Phi = \neg\Psi$, then $\Phi(x)$ is true if and only if $\Psi(x)$ is false,
3. If $\Phi = \bigvee \Phi_i$, then $\Phi(x)$ is true if and only if $\Phi_i(x)$ is true for some $i$,
4. If $\Phi = \bigwedge \Phi_i$, then $\Phi(x)$ is true if and only $\Phi_i(x)$ is true for all $i$,
5. If $\Phi = \exists\{x_\beta : \Gamma_\beta\}_{\gamma \in \beta < \alpha} \Psi$ for $\Gamma' = \left( \Gamma, \{x_\beta : \Gamma'_\beta\}_{\gamma \in \beta < \alpha} \right)$ a context extension, with $p : \Gamma' \to \Gamma$ the corresponding generalized display map, then $\Phi(x)$ is true if there exists a $y \in X(\Gamma')$ such that $p(y) = x$ and $\Psi(y)$,
6. If $\Phi = \forall\{x_\beta : \Gamma_\beta\}_{\gamma \in \beta < \alpha} \Psi$ in the same situation as above, then $\Phi(x)$ is true if for any $y \in X(\Gamma')$ such that $p(y) = x$ we have $\Psi(y)$.

The following lemma is immediate by induction, the proof is left to the reader.

**Lemma 2.9.** *Let $X$ be a model of a generalized $\kappa$-algebraic theory $T$.*

1. *For $\Phi, \Psi \in \mathcal{L}^T_\lambda(\Gamma)$ and $x \in X(\Gamma)$, then if $\Psi \vdash_\Gamma \Phi$ and $\Psi(x)$ then $\Phi(x)$.*
2. *If $f : \Gamma \to \Delta$ is any context morphism and $\Phi = f^*\Psi$ and $x \in X(\Gamma)$ then $\Phi(x) \Leftrightarrow \Psi(f(x))$.*

**Definition 2.10.** We write $\Psi \dashv_\Gamma \Phi$ to mean both $\Psi \vdash_\Gamma \Phi$ and $\Phi \vdash_\Gamma \Psi$. We denote by

$$\mathbb{L}^T_\lambda(\Gamma) := \mathcal{L}^T_\lambda(\Gamma) / (\dashv_\Gamma)$$

the quotient.

Note that $(\dashv_\Gamma)$ is indeed an equivalence relation, as $\vdash_\Gamma$ is transitive and reflexive.

*Remark 2.11.* It follows from theorem 2.7 that for a context morphism $f : \Delta \to \Gamma$ the $f^*$ operation from $\mathcal{L}^T_\lambda(\Gamma) \to \mathcal{L}^T_\lambda(\Delta)$ is compatible with the relation $\dashv$, and hence it descends to an operation

$$f^* : \mathbb{L}^T_\lambda(\Gamma) \to \mathbb{L}^T_\lambda(\Delta).$$

It is also easy to see from theorem 2.6 that the relation $\vdash$ is compatible with all the logical operations on $\mathcal{L}^T_\lambda$, that is $\neg, \bigvee, \bigwedge, \exists, \forall$ in the sense that for example, if $\Phi_i \vdash \Psi_i$ for all $i \in I$ then $\bigvee_{i \in I} \Phi_i \vdash \bigvee_{i \in I} \Psi_i$ and hence they all descend into operations on $\mathbb{L}^T_\lambda$.

13

**Construction 2.12.** At the beginning of the section, we have briefly called the language $\mathcal{L}_{\lambda,\kappa}^{T}$ before dropping the $\kappa$ from the notation, as it can be read from the fact that $T$ is a generalized $\kappa$-algebraic theory. However, we can consider $\mathcal{L}_{\lambda,\kappa'}^{T}$ for any $\kappa' \geqslant \kappa$. Indeed, given $T$ a generalized $\kappa$-algebraic theory, we can define a generalized $\kappa'$-algebraic theory $T_{\kappa'}$ by taking a set of axioms for $T$ and seeing them as axioms for a generalized $\kappa'$-algebraic theory. A model of $T_{\kappa'}$ is the same as a model of $T$. We then define

$$\mathcal{L}_{\lambda,\kappa'}^{T} := \mathcal{L}_{\lambda,\kappa'}^{T_{\kappa'}} = \mathcal{L}_{\lambda}^{T_{\kappa'}},$$

as well as its quotient

$$\mathbb{L}_{\lambda,\kappa'}^{T} := \mathbb{L}_{\lambda,\kappa'}^{T_{\kappa'}} = \mathbb{L}_{\lambda}^{T_{\kappa'}}.$$

**Example 2.13.** Let $\Sigma$ be a signature in the sense of traditional model theory, that is a set of formal symbols for types, functions and relations. Then we can consider the generalized algebraic theory $T_{\Sigma,=}$, which has one type in the empty context of each sort symbol $X$ in the signature. Each of these types have an equality predicate as the one constructed in theorem 2.4, a term for each function symbol, and for each relation symbol $R \subset X_1, \ldots, X_n$ a type axiom

$$x_1 : X_1, \ldots, x_n : X_n \vdash R(x_1, \ldots, x_n) \text{Type}$$

with the additional axiom

$$x_1 : X_1, \ldots, x_n : X_n, t_1, t_2 : R(x_1, \ldots, x_n) \vdash t_1 = t_2.$$

Models of this theory are exactly $\Sigma$-structures, and elements of $\mathbb{L}_{\omega,\omega}^{T_{\Sigma,=}}$ are essentially the same as usual first-order formulas in this signature. Elements of $\mathbb{L}_{\lambda,\kappa}^{T_{\Sigma,=}}$ correspond to infinitary first-order formulas using $\lambda$-small conjunction and disjunction and where $\exists$ and $\forall$ quantifiers can quantify over $\kappa$-small set of variables.

## 2.2 Categories of models and their weak factorization systems

In this section and the next we will abstract the notion of the first-order language of a generalized algebraic theory in terms of its category of models, this will allow us to generalize this notion of language to an arbitrary category. To be more precise, we will abstract it terms in terms of the category of models together with a certain weak factorization system we will introduce in this section, and in the next section we will generalize this to an arbitrary category equipped with a weak factorization system.

14

Recall (see section B.4), that given a generalized $\kappa$-algebraic theory $T$, the category of models of $T$ is defined as the category of morphisms of contextual categories from the syntactic category of $T$ to a certain contextual category $\mathbf{Fam}_{\kappa}$ of families of sets. Though, see theorem B.50, this is exactly equivalent to the naive definition of a model where for each type axiom we have a family of sets, for each term axiom we have an operation and for each equation axiom, the corresponding equality is satisfied. Note however, that in the presence of type equality axioms this means that certain equalities between sets need to be satisfied.

We also recall from theorem B.53 that for any context $\Gamma$, there is a “representable” model $\Gamma^*$ such that for any other model $M$,

$$\operatorname{Hom}(\Gamma^*, M) = M(\Gamma).$$

This forms a functor $\mathbb{C}_T^{\mathrm{op}} \to \operatorname{Mod}(T)$, which sends pullbacks along display maps to pushouts and limit of $\kappa$-small towers of display maps to colimits.

Now, it can be shown that any locally $\kappa$-presentable category is the category of models of a generalized $\kappa$-algebraic theory, but crucially, the category of models of $T$ comes with additional structure:

**Definition 2.14.** Given a generalized $\kappa$-algebraic theory $T$, we consider the weak factorization system on the category $\operatorname{Mod}(T)$ which is cofibrantly generated by the maps

$$\Gamma^* \hookrightarrow \Gamma'^*$$

where $\Gamma' \to \Gamma$ is a (generalized) display map in $\mathbb{C}_T$. The elements of the left class will be called *cofibrations* and the elements of right class *anodyne fibrations*.

*Remark 2.15.* In most of the paper, we will assume that the category $\operatorname{Mod}(T)$ of models of $T$ is equipped with a model structure (or at least weak model category.) whose trivial fibrations are these anodyne fibrations. However, we want to reserve the use of “trivial fibration” to the case where there is indeed a (weak) model category involved.

We also recall the closely related notion of models of clans: A $\kappa$-clan is

**Definition 2.16.** A *clan*, or $\omega$-*clan*, is a category $\mathcal{C}$ endowed with a class of maps called *fibrations* such that:

1. $\mathcal{C}$ has a terminal object 1, and for every $X \in \mathcal{C}$ the unique map $X \to 1$ is a fibration,

15

2. Isomorphisms are fibrations, the composite of two fibrations is a fibration,
3. Pullback of fibrations exist and are fibrations.

For $\kappa$ a regular cardinal, a $\kappa$-clan is a clan which further satisfies:

4 For any ordinal $\lambda < \kappa$, if $A_{\bullet} : \lambda^{\text{op}} \rightarrow \mathcal{C}$ is a diagram in which all the transition maps $A_{\beta} \rightarrow A_{\alpha}$ for $\alpha < \beta$ are fibrations, then the limits

$$\text{Lim}_{\alpha < \lambda} A_{\alpha}$$

exist, and all the projection maps $\pi_{\beta} : \text{Lim}_{\alpha < \lambda} A_{\alpha} \rightarrow A_{\beta}$ are fibrations. We refer to these as *limits of $\kappa$-small chains of fibrations*.

A *morphism of clans* is a functor that sends fibrations to fibrations, preserves the terminal object and pullbacks of fibrations. A *morphism of $\kappa$-clans* is in addition required to preserve the limits of $\kappa$-small chains of fibrations.

A *model* of a $\kappa$-clan $\mathcal{C}$ is a morphism of $\kappa$-clans $\mathcal{C} \rightarrow \mathbf{Set}$, where $\mathbf{Set}$ has the $\kappa$-clan structure where every map is a fibration.

*Remark 2.17.* For a generalized $\kappa$-algebraic theory $T$, the syntactic category $\mathbb{C}_T$ is an example of a $\kappa$-clan, and we show in section B that every $\kappa$-clan is equivalent to such a syntactic category $\mathbb{C}_T$. As discussed in theorem B.52 and theorem B.54, models of a generalized algebraic theory $T$ are closely related to models of the $\kappa$-clan $\mathbb{C}_T$, but they are not the same thing in general. It can be shown they agree, in the case of theories without type equality axioms, but not in general. Replacing the notion of model of a theory by that of models of a clan everywhere in the paper has no consequences anywhere and the reader should feel free to do so. The cofibration/anodyne fibrations weak factorization on $\text{Mod}(T)$ can be defined in the exact same way (using the Yoneda embedding) on the category $\text{Mod}(\mathcal{C})$ of models of a clan.

*Remark 2.18.* In the special case $\kappa = \omega$, this weak factorization was defined in [Hen16, Definition 2.4.2] and extensively studied in [Fre25] in the context of models of clans. In particular, Jonas Frey gave in [Fre25] a complete characterization of which pairs of a category and a weak factorization system can be obtained in this way from an $\omega$-clan – or equivalently from a generalized algebraic theory with no type equality axioms (see the discussion in theorem B.52 and theorem B.54). The methods used by Frey can be extended to the $\kappa$-case to obtain a similar characterization. Frey also shows

16

that (in the $\kappa = \omega$ case) the $\omega$-presentable cofibrant object in $\text{Mod}(\mathcal{C})$ are exactly the retracts of representable models. The same proof generalizes to the $\kappa$-case to show that if $\mathcal{C}$ is a $\kappa$-clan, then $\kappa$-presentable cofibrant objects are exactly the retracts of representables. We only mention these results for context, we will not directly use them.

**Lemma 2.19.** *Given a generalized $\kappa$-algebraic theory $T$, a morphism $f : M \to N$ of $T$-models is an anodyne fibration if and only if for every generalized display map $p : X \twoheadrightarrow Y$ in $\mathbb{C}_T$, the naturality square:*

$$\begin{array}{ccc} M(X) & \longrightarrow & M(Y) \\ \downarrow & & \downarrow \\ N(X) & \longrightarrow & N(Y) \end{array}$$

*is a weak pullback square, that is, if the induced map $M(X) \to N(X) \times_{N(Y)} M(Y)$ is a surjection.*

*Proof.* By the Yoneda lemma, there is a one-to-one correspondence between elements of $M(X)$ and morphisms of models $X^* \to M$. The map $M(X) \to M(Y)$ is obtained as the composite $Y^* \to X^* \to M$, and the map $M(X) \to N(X)$ as the composite $X^* \to M \to N$. An element of $N(X) \times_{N(Y)} M(Y)$ is hence the data of maps $X^* \to N$ and $Y^* \to M$ such that the composite $Y^* \to M \to N$ and $Y^* \to X^* \to N$ coincide. This is exactly a commutative square:

$$\begin{array}{ccc} Y^* & \longrightarrow & M \\ p^* \downarrow & & \downarrow f \\ X^* & \longrightarrow & N. \end{array}$$

An element of $M(X)$ whose image in $N(X) \times_{N(Y)} M(Y)$ is then exactly a dotted diagonal filling in the square above:

$$\begin{array}{ccc} Y^* & \longrightarrow & M \\ p^* \downarrow & & \downarrow f \\ X^* & \longrightarrow & N. \end{array}$$

Hence the surjectivity of this map is equivalent to the fact that $f$ has the right lifting property against $Y^* \to X^*$ for all fibrations $X \twoheadrightarrow Y$, which concludes the proof. $\square$

17

## 2.3 The Category theoretic approach: The first-order language of a $\kappa$-clans

In this section we present another equivalent approach to the definition of the language, which is more categorical in spirit, and strongly inspired from Lawvere's theory of hyperdoctrines ([Law69], [Law70]). This approach, while much more abstract, has several advantages over the syntactic one. Mainly, it allows working directly with the category $\text{Mod}(T)$ of models equipped with the weak factorization system on the category of models constructed in the previous subsection, without referring to the theory $T$ at all, and to generalize it to an arbitrary category with a weak factorization system. This will be useful later on to define the language of a model category without having to build explicitly a syntax for it.

As before, we fix $\lambda$ a regular cardinal. A $\lambda$-boolean algebra is a boolean algebra which admits joins (and hence intersections) of $\lambda$-small families. We denote by $\mathbf{Bool}_{\lambda}$ the category whose objects are $\lambda$-boolean algebras and whose morphisms are boolean algebra morphisms preserving $\lambda$-small joins (and hence intersections).

We introduce the notion of $\lambda$-boolean algebra over a clan $\mathcal{C}$, which we can think of as an axiomatization of the structure that the $\mathbb{L}_{\lambda}^{T}$ from section 2.1 have over the contextual category of $T$.

**Definition 2.20.** Given $\mathcal{C}$ a clan and $\lambda$ a regular cardinal, a $\lambda$-boolean algebra over $\mathcal{C}$ is a functor

$$\mathcal{B} : \mathcal{C}^{op} \to \mathbf{Bool}_{\lambda}$$

such that:

1. For each fibration $\pi : Z \to X$ in $\mathcal{C}$, $\pi^* : \mathcal{B}(X) \to \mathcal{B}(Z)$ has a left adjoint:

$$\exists_{\pi} : \mathcal{B}(Z) \leftrightarrows \mathcal{B}(X) : \pi^*.$$

2. The Beck-Chevalley condition holds for each pullback square along a fibration. That is, given any pullback square:

$$\begin{array}{ccc} Z' & \xrightarrow{f'} & Z \\ \pi' \downarrow & \downarrow^{\perp} & \downarrow^{\pi} \\ X' & \xrightarrow{f} & X \end{array}$$

with $\pi$ a fibration, we have $f^* \exists_{\pi} = \exists_{\pi'} f'^*$.

18

Morphisms of $\lambda$-boolean algebras over $\mathcal{C}$ are natural transformations that commute with the $\exists_\pi$. We call weak morphisms the natural transformations with no additional conditions.

*Remark 2.21.* If $\mathcal{B}$ is a $\lambda$-boolean algebra over $\mathcal{C}$, then for each $X \in \mathcal{C}$, the negation $\neg : \mathcal{B}(X) \rightarrow \mathcal{B}(X)^{op}$ is a contravariant equivalence. Therefore, if $\pi : Z \rightarrow X$ is a fibration, then the map $\pi^* : \mathcal{B}(X) \rightarrow \mathcal{B}(Z)$ also has a right adjoint defined by:

$$\forall_\pi(\phi) := \neg(\exists_\pi \neg \phi).$$

From this definition, we immediately have the other Beck-Chevalley condition $f^*(\forall_\pi) = \forall_\pi f^*$ and the fact that morphisms of boolean algebras over $\mathcal{C}$ are also compatible with $\forall_\pi$, simply because $f^*$ is compatible with both $\exists_\pi$ and the negation.

*Remark 2.22.* Theorem 2.20 will in practice be applied to $\mathcal{C}$ a $\kappa$-clan (and not just a clan). The only reason it is stated like that is because the definition actually does not explicitly involve $\kappa$. This is related to the fact that the dependencies in $\kappa$ of the language defined in the previous subsection are only through the choice of which context can our variables (including bound variables) be taken from: taking a larger $\kappa$ means we can quantify over more variables at the same time. Similarly, the dependency on $\kappa$ is hidden in the dependency on $\mathcal{C}$, as $\mathcal{C}$ is playing the role of the category of $\kappa$-contexts.

Let us start with our main example of such a boolean algebra over a clan, which is the motivating example for the notion:

**Theorem 2.23.** *Let $T$ be a generalized $\kappa$-algebraic theory and $\mathcal{C}_T$ the corresponding $\kappa$-contextual category, seen as a clan. Then the construction $X \mapsto \mathbb{L}_\lambda^T(X)$ from theorem 2.10 (see also theorem 2.1 and 2.6) is a $\lambda$-boolean algebra over $\mathcal{C}_T$. In fact, it is an initial object in the category of $\lambda$-boolean algebras over $\mathcal{C}_T$.*

*Proof.* We first check that $\mathcal{L}_\lambda^T$ is a $\lambda$-boolean algebra over $\mathcal{C}_T$. We have mentioned in theorem 2.11 that all the logical operations $\vee, \wedge, \neg, \exists$ and so on are compatible with the equivalence relation $\dashv$. Therefore, they all induce operations on the quotient $\mathbb{L}_\lambda^T$. The first four points of theorem 2.6 immediately show that each $\mathbb{L}_\lambda^T(X)$ is a boolean algebra whose order relation is given by $\vdash$, and with $\lambda$-small unions. By theorem 2.5, the map $f^* : \mathcal{L}_\lambda^T(X) \rightarrow \mathcal{L}_\lambda^T(Y)$ is compatible with all the logical operations, so it gives rise to a morphism of boolean algebras $\mathbb{L}_\lambda^T(X) \rightarrow \mathbb{L}_\lambda^T(Y)$. We get a functor $\mathcal{C}_T \rightarrow \mathbf{Bool}_\lambda$, the conditions $(g \circ f)^*(\phi) = f^*g^*(\phi)$ and $id^*(\phi) = \phi$ follow immediately by induction. Next, the last two conditions of theorem 2.6

19

show that $\exists$ and $\forall$ define left and right adjoints to $\pi^*$. Finally, the Beck-Chevalley condition follows from how $f^*$ is defined on formulas starting with a $\exists$ quantifier:

$$f^*(\exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}\Phi) = \exists\{x_\beta : f^*\Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}f^*\Phi,$$

which (after passing to the quotient $\mathcal{L} \rightarrow \mathbb{L}$) exactly says that $f^*\exists_\pi = \exists\pi f^*$ where $\pi$ is the generalized display map corresponding to forgetting the variables $\{x_\beta\}_{\gamma \leqslant \beta < \alpha} \in X_\alpha$.

We now check that it is an initial object in the category of $\lambda$-boolean algebras over $\mathcal{C}_T$. Let $\mathcal{B}$ be any $\lambda$-boolean algebra over $\mathcal{C}$. Any morphism $v : \mathbb{L}_\lambda^T \rightarrow \mathcal{B}$ has to satisfy:

1. $v(\perp) = \perp_\mathcal{B}$ and $v(\top) = \top_\mathcal{B}$.
2. $v(\neg\Phi) = \neg v(\Phi)$.
3. $v(\bigvee_{i \in I} \Phi_i) = \bigvee_{i \in I} v(\Phi_i)$ and $v(\bigwedge_{i \in I} \Phi_i) = \bigwedge_{i \in I} v(\Phi_i)$.

4.

$$v(\exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}\Phi) = \exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}v(\Phi)$$

and

$$v(\forall\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}\Phi) = \forall\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}v(\Phi).$$

These form an inductive definition for a function $\mathcal{L}_\lambda^T \rightarrow \mathcal{B}$. So there is a unique such function $v : \mathcal{L}_\lambda^T \rightarrow \mathcal{B}$. To conclude, we only need to check that this function $v$ descends to a function $\mathbb{L}_\lambda^T \rightarrow \mathcal{B}$ and is a morphism of $\lambda$-boolean algebras over $\mathcal{C}$. But this is rather immediate: We first observe, by induction over theorem 2.6, that if $\Phi \vdash \Psi$ then $v(\Phi) \leqslant v(\Psi)$. This implies that if $\Phi \dashv \Psi$ then $v(\Phi) = v(\Psi)$, so $v$ does define a function $\mathbb{L}_\lambda^T \rightarrow \mathcal{B}$. The naturality condition

$$v(f^*(\Phi)) = f^*(v(\Phi))$$

can be proved by induction on the formula $\Phi$, and the compatibility of $v$ with all the boolean algebra operations and the quantifiers follows immediately from the definition of $v$. $\square$

**Proposition 2.24.** *Given any (small) clan $\mathcal{C}$ and $\lambda$ a regular cardinal, there is an initial $\lambda$-boolean algebra over $\mathcal{C}$, which we denote by $\mathbb{L}_\lambda^\mathcal{C}$.*

20

Note that by theorem 2.23, if $T$ is a generalized $\kappa$-algebraic theory, with $\mathcal{C}_T$ its $\kappa$-contextual category, then

$$\mathbb{L}_{\lambda}^{\mathcal{C}_T} = \mathbb{L}_{\lambda}^T.$$

This provides a way to define (or at least to characterize) the first-order language of any clan without having to explicitly give a syntactic description of the clan.

Proof. We can either remark that the $\lambda$-boolean algebras over $\mathcal{C}$ are (by their definition) the models of a multi-sorted $\lambda$-algebraic theory (with one sort for each object $c \in \mathcal{C}$) and hence there is an initial object by usual results on algebraic theories. Alternatively, we can use (see section C) that every clan is equivalent to the contextual category of a generalized algebraic theory and use theorem 2.23 to conclude. □

Next, we mention a few more examples:

### Example 2.25.

1. Let **Set** be the category of sets, considered as a clan where every arrow is a fibration. The contravariant power-set functor $\mathcal{P}: \mathbf{Set}^{op} \to \mathbf{Bool}_{\lambda}$ is a $\lambda$-Boolean algebra over **Set**. The Beck-Chevalley condition follows from theorem 2.26 below.
2. Given $F: \mathcal{C} \to \mathcal{D}$ a morphism of clans, if $\mathcal{B}$ is a $\lambda$-boolean algebra over $\mathcal{D}$, then $F^*\mathcal{B}$ defined by $F^*\mathcal{B}(\Gamma) = \mathcal{B}(F(\Gamma))$ is a $\lambda$-boolean algebra over $\mathcal{C}$.
3. Combining the two observations above, given any model $M$ of a clan $\mathcal{C}$, that is, a morphism of clans $M: \mathcal{C} \to \mathbf{Set}$, one has a boolean algebra $\mathcal{P}(M)$ over $\mathcal{C}$ given by pulling back example 1 along the morphism $M: \mathcal{C} \to \mathbf{Set}$. More explicitly:

$$\begin{array}{rcl} \mathcal{P}(M): & \mathcal{C}^{op} & \to \quad \mathbf{Set} \\ & \Gamma & \mapsto \quad \mathcal{P}(M(\Gamma)). \end{array}$$

Lemma 2.26. Given a square of sets,

$$\begin{array}{c} W \xrightarrow{f} X \\ \downarrow g \qquad \qquad \downarrow h \\ Y \xrightarrow{k} Z, \end{array}$$

21

*then the power set functor satisfies the Beck-Chevalley condition on this square, i.e., $k^*\exists_h = \exists_g f^*$ as maps $\mathcal{P}(X) \rightarrow \mathcal{P}(Y)$ if and only if the square is a weak pullback square i.e., if and only if the cartesian gap map $W \rightarrow Y \times_Z X$ is surjective.*

*Proof.* Given a subset $P \subset X$ one has:

$$k^*h!P = \{y \in Y | k(y) = h(p) \text{ for some } p \in P\},$$

$$g!f^*P = \{g(w) | f(w) \in P\}.$$

Surjectivity of the map $W \rightarrow Y \times_Z X$ gives a canonical way to make any element of $k^*h!P$ into an element of $g!f^*P$, and conversely, applying the equality to $P = \{p\}$ produces the surjectivity of $W \rightarrow Y \times_Z X$. $\square$

In this new setting with just a clan $\mathcal{C}$, one can still define the set of formulas $\mathbb{L}_\lambda^\mathcal{C}$ as the initial $\lambda$-boolean algebra over $\mathcal{C}$. We now explain what it means for formulas defined in this way to be “true” or “false” given a model and an interpretation of its variables in the model.

**Construction 2.27.** Given a clan $\mathcal{C}$ and a model of $M : \mathcal{C} \rightarrow \mathbf{Set}$ we have, as explained in theorem 2.25, a $\lambda$-boolean algebra over $\mathcal{C}$ defined by $c \mapsto \mathcal{P}(M(c))$. By initiality of the $\lambda$-boolean algebra $\mathbb{L}_\lambda^\mathcal{C}$, there exists a unique morphism of $\lambda$-boolean algebras over $\mathcal{C}$:

$$|-|_M : \mathbb{L}_\lambda^\mathcal{C} \rightarrow \mathcal{P}(M).$$

This morphism associates each formula $\phi$ in context $\Gamma$ to a subset $|\phi|_M \subseteq M(\Gamma)$. An element $x \in M(\Gamma)$ is said to *satisfy* $\phi$ if $x \in |\phi|_M$. With some abuse of notation, we say that “$\phi(x)$ is true” in this case. We also write

$$M \vdash \phi(x)$$

when we want to insist on which model we are talking about. When $\Gamma$ is the terminal object of $\mathcal{C}$ *i.e.,* $\phi$ is a closed formula, then $M(\Gamma) = \{*\}$. Therefore, $\mathcal{P}(M(\Gamma)) = \{\bot, \top\}$ so that $|\phi|_M$ is simply a proposition. One then says that $M$ satisfies $\phi$, and we write $M \vdash \phi$.

**Lemma 2.28.** *When $\mathcal{C} = \mathcal{C}_T$ is the $\kappa$-contextual category of a $\kappa$-generalized algebraic theory, then through the identification $\mathbb{L}_\lambda^T = \mathbb{L}_\lambda^\mathcal{C}$, the two definitions of validity of a formula on elements of a model given by theorem 2.8 and theorem 2.27 are equivalent.*

22

Proof. Defining the validity of formulas as in theorem 2.27 it is immediate to verify all the explicit conditions of the inductive definition given in theorem 2.8 simply because the map $\mathbb{L}_{\lambda}^{\mathcal{C}} \to \mathcal{P}(M)$ is a morphism of $\lambda$-boolean algebras. Hence, it immediately follows by induction on formulas that the two definitions are equivalent. $\square$

Construction 2.29. Let $F : \mathcal{C} \to \mathcal{D}$ be a morphism of clans. And let $\mathbb{L}_{\lambda}^{\mathcal{C}}$ and $\mathbb{L}_{\lambda}^{\mathcal{D}}$ be their respective initial $\lambda$-boolean algebras. From the fact that $\mathbb{L}_{\lambda}^{\mathcal{C}}$ is initial, there is a morphism of $\lambda$-boolean algebras

$$\alpha^F : \mathbb{L}_{\lambda}^{\mathcal{C}} \to F^* \left( \mathbb{L}_{\lambda}^{\mathcal{D}} \right).$$

For any $\Gamma \in \mathcal{C}$ and any formula $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{C}}(\Gamma)$ we denote $F(\Phi) := \alpha_{\Gamma}^F(\Phi)$ which is a formula in context $F(\Gamma)$ i.e., an element of $\mathbb{L}_{\lambda}^{\mathcal{D}}(F(\Gamma))$. The following is immediate from the definition above:

Proposition 2.30. Let $M : \mathcal{D} \to \mathbf{Set}$ a model of the clan $\mathcal{D}$, $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{C}}(\Gamma)$ a formula in context $\Gamma$ and $x \in M(F(\Gamma))$. Then, $M \vdash \alpha_F(\Phi)(x)$ if and only if $F^*M \vdash \Phi(x)$.

Of course this also applies to models of a generalized $\kappa$-algebraic theory.

Finally, we finish this section by showing the key property of invariance of formulas along anodyne fibrations. An invariance property will be established in the next section assuming we are working with a model category, but this first invariance property is purely algebraic. This is also the key observation in Makkai FOLDS [Mak95] and it is directly inspired from it.

We start with the following observation: let $\mathcal{C}$ be a clan and $f : M \to N$ a morphism of two $\mathcal{C}$-models, then we have an obvious map $f^* : \mathcal{P}(N) \to \mathcal{P}(M)$ which sends a subset $A \subset N(c)$ for $c \in \mathcal{C}$ to

$$f_c^{-1}(A) \subset M(c)$$

this map is easily seen to be a weak morphism of boolean algebras over $\mathcal{C}$. It is compatible with the boolean algebra operations and the ordinary contravariant functoriality, but it does not have to be compatible with the covariant functoriality $\exists_\pi$ along fibrations. However, one has:

Lemma 2.31. Let $\mathcal{C}$ be a clan and let $f : M \to N$ be a morphism between two $\mathcal{C}$-models. Then $f$ is an anodyne fibration if and only if $f^* : \mathcal{P}(N) \to \mathcal{P}(M)$ is a morphism of $\lambda$-boolean algebras.

23

Proof. We only need to show that for every fibration $p: X \to Y$ the following square

$$\begin{array}{c} \mathcal{P}(N(X)) \xrightarrow{f_X^*} \mathcal{P}(M(X)) \\ \downarrow \exists \qquad \qquad \qquad \qquad \downarrow \exists \\ \mathcal{P}(N(Y)) \xrightarrow{f_Y^*} \mathcal{P}(M(Y)). \end{array}$$

commutes. From theorem 2.26 this is equivalent to saying that the dotted map in

![img-0.jpeg](img-0.jpeg)

is surjective. But this is exactly the characterization of anodyne fibrations given in theorem 2.19. □

This allows us to deduce the key result of invariance of formulas along anodyne fibrations of models. Basically, the validity of formulas is preserved by anodyne fibrations of models:

**Corollary 2.32.** Let $\mathcal{C}$ be a clan and let $f: M \twoheadrightarrow N$ be an anodyne fibration between two $\mathcal{C}$-models. For $c \in \mathcal{C}$, let $x \in M(c)$ and $\phi \in \mathbb{L}_{\lambda}^{\mathcal{C}}$ be any formula. Then

$$M \vdash \phi(x) \Leftrightarrow N \vdash \phi(f(x))$$

Proof. As $f: M \to N$ is an anodyne fibration, it follows from theorem 2.31 that the map $f^*: \mathcal{P}(N) \to \mathcal{P}(M)$ is a morphism of boolean algebra over $\mathcal{C}$. Hence, by initiality of $\mathbb{L}_{\lambda}^{\mathcal{C}}$, the unique morphism $|\cdot|_M: \mathbb{L}_{\lambda}^{\mathcal{C}} \to \mathcal{P}(M)$ is obtained as a composite

$$\mathbb{L}_{\lambda}^{\mathcal{C}} \xrightarrow{|\cdot|_N} \mathcal{P}(N) \xrightarrow{f^*} \mathcal{P}(M).$$

By definition, $M \vdash \phi(x)$ means that $x \in |\phi|_M$ while $N \vdash \phi(f(x))$ means that $x \in f^*|\phi|_N$, hence the result immediately follows. □

24

## 2.4 The language of a weak model category and two invariance theorems

Construction 2.33. Given $\mathcal{M}$ a weak model category, the category $\mathcal{M}^{\mathrm{COF}}$ of cofibrant objects with cofibrations between them forms a coclan. We define the language of $\mathcal{M}$ to be the language of the coclan $\mathcal{M}^{\mathrm{COF}}$. For any regular cardinal $\lambda$, we denote by $\mathbb{L}_{\lambda}^{\mathcal{M}}$ the $\lambda$-boolean algebra $\mathbb{L}_{\lambda}^{\mathcal{M}^{\mathrm{COF}}}$ over $\mathcal{M}^{\mathrm{COF}}$.

Note that for each cofibrant object $X \in \mathcal{M}$, we have a set (or possibly a class if $\mathcal{M}$ is large) of formulas $\mathbb{L}_{\lambda}^{\mathcal{M}}(X)$.

Remark 2.34. There is a size issue to be mentioned here. In most practical examples, $\mathcal{M}^{\mathrm{COF}}$ is a large category while the construction of $\mathbb{L}_{\lambda}^{\mathcal{M}^{\mathrm{COF}}}$ developed in section 2.3 assumes it is a small category. We can deal with this by invoking a larger Grothendieck universe, but this has a practical consequence: The set of formulas $\mathbb{L}_{\lambda}^{\mathcal{M}}(X)$ might not be a small set. Indeed, it lives in the same Grothendieck universe as the one in which $\mathcal{M}^{\mathrm{COF}}$ is small.

Construction 2.35. If $X \in \mathcal{M}$ then we can define a model of the coclan $\mathcal{M}^{\mathrm{COF}}$ using the restricted Yoneda embedding:

$$\begin{array}{c c c c} \updownarrow_{X}: & (\mathcal{M}^{\mathrm{COF}})^{\mathrm{op}} & \to & \mathbf{Set} \\ & c & \mapsto & \mathrm{Hom}(c, X), \end{array}$$

which defines a functor $\updownarrow : \mathcal{M} \to \mathrm{Mod}(\mathcal{M}^{\mathrm{COF}})$.

Definition 2.36. Let $\mathcal{M}$ be a weak model category. For $c \in \mathcal{M}$ a cofibrant object, and $X \in \mathcal{M}$ any object, $v : c \to X$ and $\phi \in \mathbb{L}_{\lambda}^{\mathcal{M}}(c)$ we write

$$X \vdash \phi(v)$$

to mean

$$\updownarrow_{X} \vdash \phi(v)$$

where $v$ is seen as an element of $\updownarrow_{X}(c) = \mathrm{Hom}(c, X)$.

Remark 2.37. In the special case where $\mathcal{M} = \mathrm{Mod}(T)$ is the category of models of a generalized $\kappa$-algebraic theory (or more generally of a $\kappa$-coclan), then $\mathbb{L}_{\lambda}^{\mathcal{M}}$ is the initial $\lambda$-boolean algebra over the coclan of all cofibrant objects of $\mathcal{M}$, while the syntactic category of $T$ is equivalent to a full sub-$\kappa$-coclan of that. In particular, there is a morphism of $\lambda$-boolean algebras over the syntactic category $\mathcal{C}_T$

$$\mathbb{L}_{\lambda}^{T}(X) \to \mathbb{L}_{\lambda}^{\mathcal{M}}(X) \qquad (\mathrm{For}\ X \in \mathcal{C}_T).$$

25

If we denote this map by $i$ then for $X$ any model of $T$ we can easily check that

$$X \vdash \phi(v) \Leftrightarrow X \vdash i(\phi)(v)$$

for any $c \in \mathcal{C}_T$ and $\phi \in \mathbb{L}_\lambda^T(c)$, where the left-hand side is interpreted in the sense of theorem 2.1 while the right-hand side is in terms of theorem 2.36.

Note that we do expect these to be the same. Informally, $\mathbb{L}_\lambda^T$ corresponds to an $\mathcal{L}_{\kappa,\lambda}$ logic, in the sense that quantifiers can only be applied to formulas in $\kappa$-small contexts — applied to less than $\kappa$-many variables at the same time—while $\mathbb{L}_\lambda^\mathcal{M}$ corresponds to an $\mathcal{L}_{\infty,\lambda}$ logic, where quantifiers can be applied to arbitrarily many formulas at the same time.

**Theorem 2.38.** *Let $\mathcal{M}$ be a weak model category, $c \in \mathcal{M}$ a cofibrant object and $\phi \in \mathbb{L}_\lambda^\mathcal{M}(c)$.*

- • $1^{st}$ **invariance theorem:** *Let $v_1, v_2 : c \to X$ be two homotopically equivalent maps with $X$ fibrant. Then*

$$X \vdash \phi(v_1) \quad \Leftrightarrow \quad X \vdash \phi(v_2).$$

- • $2^{nd}$ **invariance theorem:** *Let $f : X \to Y$ be a weak equivalence between two fibrant objects and $v : c \to X$ any map. Then*

$$X \vdash \phi(v) \quad \Leftrightarrow \quad Y \vdash \phi(fv).$$

*Proof.* We start by first observing that the second invariance theorem in the special case where $f$ is a trivial fibration immediately follows from theorem 2.32 as a trivial fibration $f$ has the right lifting property against all core cofibrations and hence is sent to an anodyne fibration in $\text{Mod}(\mathcal{M}^{\text{COF}})$ by the functor from theorem 2.35.

We use this to prove the $1^{st}$ invariance theorem: If $v_1, v_2 : c \to X$ are homotopic then there exists a map $h$:

![img-1.jpeg](img-1.jpeg)

26

The two maps $p_1, p_2 : PX \to X$ are trivial fibrations (they are both fibrations and weak equivalences), $v_1 = p_1 \circ h$ and $v_2 = p_2 \circ h$. By the observation above, we have:

$$\begin{array}{rcl} & X & \vdash & \phi(v_1) \\ \Leftrightarrow & X & \vdash & \phi(p_1 h) \\ \Leftrightarrow & PX & \vdash & \phi(h) \\ \Leftrightarrow & X & \vdash & \phi(p_2 h) \\ \Leftrightarrow & X & \vdash & \phi(v_2) \end{array}$$

This concludes the proof of the $1^{st}$ invariance theorem.

Next, we observe it is enough to prove the second invariance theorem when $X$ and $Y$ are both bifibrant. Indeed, starting from $f : X \to Y$ a weak equivalence between fibrant objects, $v : c \to X$ and $\phi \in \mathbb{L}_\lambda^M(c)$ as in the theorem. We can replace both $X$ and $Y$ by bifibrant objects

$$\begin{array}{ccc} X^{\text{COF}} & \xrightarrow[f]{\sim} & Y^{\text{COF}} \\ \downarrow\searrow & & \downarrow\searrow \\ X & \xrightarrow[f]{} & Y. \end{array}$$

First replacing $X$ by a cofibrant object $X^{\text{COF}}$ and then factoring the map $X^{\text{COF}} \to Y$, which is a weak equivalence, as a trivial cofibration followed by a trivial fibration. The map $v : c \to X$, can be lifted to a map $v' : c \to X^{\text{COF}}$. As we can already apply the $2^{nd}$ invariance theorem to trivial fibrations, we have that:

$$\begin{array}{l} X \vdash \phi(v) \Leftrightarrow X^{\text{COF}} \vdash \phi(v') \\ Y \vdash \phi(fv) \Leftrightarrow Y^{\text{COF}} \vdash \phi(f'v'). \end{array}$$

Therefore, it is enough to show the $2^{nd}$ invariance theorem for bifibrant objects.

This last step is achieved essentially using a “Brown factorization”: any weak equivalence between bifibrant objects can be factored as a section of a trivial fibration followed by a trivial fibration. Indeed, if $f : X \to Y$ is a

27

map between bifibrant objects we can form the pullbacks:

![img-2.jpeg](img-2.jpeg)

Note that because the fibrations $PY \to Y$ are trivial fibrations, the map $X \times_Y PY \to X$ in the diagram above is also a trivial fibration. The total vertical maps are both the identity. Which gives us a diagram:

![img-3.jpeg](img-3.jpeg)

Where $p$ is the map $X \times_Y PY \twoheadrightarrow X \times Y \xrightarrow{\pi_2} Y$. Note that all maps in this diagram are weak equivalences due to the 2-out-of-3 condition. We can now prove the theorem, we have

$$X \vdash \phi(v) \Leftrightarrow X \times_Y PY \vdash \phi(e'v)$$

because $v = qe'v$ and $q$ is a trivial fibration, and

$$X \times_Y PY \vdash \phi(e'v) \Leftrightarrow Y \vdash \phi(fv)$$

because $p$ is a trivial fibration and $fv = pe'v$. Hence, combining the two

$$X \vdash \phi(v) \Leftrightarrow Y \vdash \phi(fv)$$

Finally, we explain how Quillen adjunctions act on formulas. A *Quillen adjunction* between two weak model categories is an adjunction

$$L : \mathcal{C} \leftrightarrows \mathcal{D} : R$$

where the left adjoint $L$ sends cofibrations to cofibrations and the right adjoint $R$ sends fibrations to fibrations.

28

*Remark 2.39.* There is also a more general notion called “weak Quillen functors” introduced in [Hen20] which is sometimes more convenient. The functor $L$ is only defined on cofibrant objects and $R$ on fibrant objects, and they are only required to preserve core (co)fibrations – all results in this section below, as well as the $4^{th}$ invariance theorem from section 4 apply to weak Quillen adjunctions too. We restrict ourselves to Quillen adjunctions in the paper, unless otherwise stated, for simplicity, and because this already cover most of the applications.

**Construction 2.40.** Given a Quillen adjunction$^2$ $L : \mathcal{C} \leftrightarrows \mathcal{D} : R$. Then, $L$ restricts to a coclan morphism $L : \mathcal{C}^{\text{COF}} \rightarrow \mathcal{D}^{\text{COF}}$, which following theorem 2.29 we have a (unique) comparison map

$$\alpha_L : \mathbb{L}^\mathcal{C}_\lambda \rightarrow L^* \mathbb{L}^\mathcal{D}_\lambda$$

obtained from the fact that $\mathbb{L}^\mathcal{C}_\lambda$ is an initial boolean algebra over $\mathcal{C}$. As before, if $\phi \in \mathbb{L}^\mathcal{C}_\lambda(C)$, we often write $L(\phi)$ instead of $\alpha_L(\Phi)$. Note that $L(\phi) \in \mathbb{L}^\mathcal{D}_\lambda(L(C))$.

Finally, exactly as in theorem 2.29, we have:

**Proposition 2.41.** *For a Quillen adjunction $L : \mathcal{C} \leftrightarrows \mathcal{D} : R$, any$^3$ object $X \in \mathcal{D}$, and cofibrant object $C \in \mathcal{C}$, any map $v : C \rightarrow R(X)$ corresponding to $\tilde{v} : LC \rightarrow X$, and $\phi \in \mathbb{L}^\mathcal{C}_\lambda$ we have*

$$R(X) \vdash \phi(v) \Leftrightarrow X \vdash L(\phi)(\tilde{v}).$$

*Proof.* See theorem 2.29. $\square$

The $4^{th}$ invariance theorem that we will establish in section 4 as theorem 4.2 shows that for a Quillen equivalence, this construction gives an equivalence between the language of $\mathcal{C}$ and of $\mathcal{D}$ in an appropriate sense.

### 3 Examples of languages of model categories

In this section, we examine some examples of the language associated to a model category by applying the construction as described in section 2. We include examples we believe to be of interest. Furthermore, we start with some general considerations that allow us to construct the language of a model category.

$^2$Or more generally a weak Quillen adjunction in the sense of [Hen20].

$^3$If $L$ and $R$ are only a weak Quillen adjunction, then $X$ needs to be fibrant.

29

When applying the theory introduced in section 2 to a model category $\mathcal{M}$, we have two possible approaches: we can manipulate formulas as elements of the free Boolean algebra over $\mathcal{M}^{\text{COF}}$, following the approach from section 2.3, or we can try to build a generalized algebraic theory whose first-order language is the same as the language of $\mathcal{M}$. For example, we could try to realize $\mathcal{M}$ as the category of models of some generalized $\kappa$-algebraic theory, or if that is not possible we could try to realize the category of $\kappa$-presentable cofibrant objects of $\mathcal{M}$ as the opposite of the syntactic category of some generalized $\kappa$-algebraic theory.

We believe that, once we are familiar with how this language works, the first approach is simpler. But in order to build familiarity with the languages, in all the examples we will cover below we will try to use the second approach and build a more or less explicit generalized algebraic theory associated to each example, in order to show the reader what can be done in the logic of each case.

It is shown in section B that any $\kappa$-clan is equivalent to the syntactic category of a generalized $\kappa$-algebraic theory. So in general, given $\mathcal{M}$ a combinatorial (weak) model category, we can always find a regular cardinal $\kappa$ and a generalized $\kappa$-algebraic theory such that the language associated to $\mathcal{M}$ is the language of this generalized algebraic theory. Unfortunately, the construction of this theory following section B is extremely unexplicit.

What we would like to do here is to give some tools to help “guess” a simpler generalized algebraic theory that works on concrete examples. Given that our goal is only to guess the correct theory for a few examples, we will not try to make this completely formal and rigorous – though it might be possible.

To that end, let us recall some facts about a generalized $\kappa$-algebraic theory $T$, and of the $\kappa$-contextual category $\mathbb{C}_T$ associated to it. Theorem A.3 states inductively what it means for a judgment $\Gamma \vdash \Delta \text{ Type}$ in a $\kappa$-pretheory to be well-formed in $T$; this is the case whenever $\Gamma$ is a context, and this itself entails that any constituent of $\Gamma$ is obtained from a derived rule of the $\kappa$-pretheory $T$. In turn, each derived rule is deduced from the list of theorem A.4, or using a rule previously derived. In a generalized $\kappa$-algebraic theory, each type introduction axiom (derived judgment) is well-formed by theorem A.12. Concretely, this means that in order to build new types in context $\Gamma'$ we must know that all the variables used in $\Gamma'$ must previously be constructed in some context $\Gamma$. In a sense, each type must be constructed from more primitive types.

30

We can use the above in the following:

*Remark 3.1.* Let $T$ be a generalized $\kappa$-algebraic theory and $\mathbb{C}_T$ the syntactic $\kappa$-contextual category of $T$ with the natural $\kappa$-clan structure *i.e.*, in which the fibrations are the generalized display maps. Each type axiom $\Gamma \vdash A$ Type of $T$ corresponds to a display map $(\Gamma \cdot A \rightarrow \Gamma)$. Now, the set of axioms of $T$ admits a well-founded transitive relation $<$ such that for each type axiom $\Gamma \vdash A$ Type we can show that $\Gamma$ is a context using only type axioms “smaller” than $\Gamma \vdash A$ Type. In particular, it means that only types “smaller than A” can appear in the context $\Gamma$. Formulated categorically, this means that the map $\Gamma \rightarrow 1$ can be constructed as $\kappa$-small composite of pullbacks of display maps $\Gamma' \cdot B \rightarrow \Gamma'$, for $\Gamma' \vdash B$ Type type axioms that are smaller than $\Gamma \vdash A$ Type. Recall from theorem 2.14 that $\text{Mod}(T)$ has a weak factorization system which is cofibrantly generated by the set

$$I = \{ \updownarrow_A \hookrightarrow \updownarrow_B \in \text{Mod}(T) | B \rightarrow A \in \mathbb{C}_T \}.$$

Given that every display map is a $\kappa$-small composite of pullback of the display map corresponding to type axioms. We can restrict the set of generators to the display maps corresponding to type axioms, which then comes with this additional well-founded relation.

The previous example motivates:

**Definition 3.2.** Let $\mathcal{C}$ be a model category and $\text{COF}(\mathcal{C})$ the class of cofibrations. Assume that the cofibrations are generated by a set $I$. We say that the set of generating cofibrations is *well-founded* if there exists a well-founded relation $<$ on $I$ such that for all $i \in I$, the map $\emptyset \rightarrow Dom(i)$ can be written as a $\kappa$-composite of pushouts of maps $j \in I$ with $j < i$.

**Example 3.3.** As explained in theorem 3.1, if $T$ is a generalized $\kappa$-algebraic theory, then the weak factorization from theorem 2.14 on $\text{Mod}(T)$ has a well-founded set of generators corresponding to the type of axioms of $T$.

The general idea is; if we start from a combinatorial weak factorization system, and we want to see it as coming from an explicitly given generalized algebraic theory, we start by finding a well-founded set of generators, and then we build a theory whose type axioms correspond to these generators.

Note that in particular, we need the factorization system to be generated by map with cofibrant domain, or at least we need the generating cofibrations to have cofibrant domain. Most model structures we work with in practice, in fact all the examples we will encounter here have this property (this is closely related to the notion of tractable model category from

31

[Bar10]). But in general this is not an obstruction: lemma 4.7 of [Hen23] allows to modify any combinatorial or accessible model category into one that has this property—maybe at the cost of moving to semi-model category.

**Proposition 3.4** ([Hen23, 4.7 Lemma]). *Fix $\kappa$ an uncountable regular cardinal. Let $(L_1, R_1)$ and $(L_2, R_2)$ two $\kappa$-accessible weak factorization systems on a locally $\kappa$-presentable category $\mathcal{C}$ such that $L_1 \subset L_2$ or $R_2 \subset R_1$. There is a $\kappa$-accessible weak factorization system $(L_3, R_3)$ on $\mathcal{C}$ such that $R_3$ is the class of maps that have the right lifting property against all $L_1$-maps whose domain is $L_2$-cofibrant. If $(L_1, R_1)$ is $\kappa$-combinatorial, then $(L_3, R_3)$ is also $\kappa$-combinatorial.*

*Observation 3.5.* If $\mathcal{M}$ is a combinatorial weak model category, then there exists another combinatorial weak model category structure on $\mathcal{M}$ with the same core cofibrations and core acyclic cofibrations, but where the cofibrations and acyclic cofibrations are generated by core cofibrations. In order to see this, we apply theorem 3.4 taking $(L_1, R_1)$=(acyclic cofibrations, fibrations) and $(L_2, R_2)$=(cofibrations, acyclic fibrations). This produces a weak factorization system $(L_3, R_3)$ where the class $R_3$ of fibrations is generated by acyclic cofibrations with cofibrant domain. We apply the result again, but on (cofibrations, acyclic fibrations)$=(L_2, R_2)$=( $L_1, R_1$ ) to get another weak factorization system $(L'_3, R'_3)$ where the class $R'_3$ is generated by cofibrations with cofibrant domain. Note this process does not change the core (acyclic) cofibrations or core (acyclic) fibrations, and hence preserves the fact that we have a weak model category.

Once we have generating cofibrations with cofibrant domain, there is always an easy way to get a well-founded set of generators:

**Example 3.6.** If $L$ is a set of generating cofibrations with cofibrant domain of a combinatorial weak model category, then we can get a well-founded class of cofibrations by setting $L' := \{\emptyset \rightarrow Dom(l) | l \in L\} \coprod L$. In this case, we can set $(\emptyset \rightarrow Dom(l)) < f$ for $f \in L$ and $l \in L$.

Theorem 3.3 shows that starting with a $\kappa$-clan, one can get a cofibrantly generated weak factorization system on the category of models $\text{Mod}(\mathcal{C})$ such that the generating set of cofibrations is well-founded. We can reverse this process in the sense that if we are given a weak factorization system with a well-founded set of generating cofibrations, then we can produce a generalized $\kappa$-algebraic theory from it, and therefore the $\kappa$-clan associated to it.

The next example is similar to theorem 3.1.

32

**Construction 3.7.** Let $\mathcal{C}$ be a $\kappa$-clan. Assume that $\mathcal{C}$ has a weak factorization system that is cofibrantly generated by a set $I$ with a well-founded relation. Recall that this means that for a cofibration $i: A \hookrightarrow B$ the map $\emptyset \to A$ is a $\kappa$-composite of pushouts of maps $j \in I$ with $j < i$. Therefore, we can introduce a type axiom:

$$\overline{A} \vdash \overline{B} \text{ Type}$$

for $i: A \hookrightarrow B \in I$. The notation $\overline{A}$ denotes the context in which the new type $\overline{B}$ is built, and the context $\overline{A}$ is obtained using types strictly smaller than $\overline{B}$, which reflects the decomposition of the map $\emptyset \hookrightarrow A$ as a $\kappa$-composite of pushouts of maps $j \in I$ smaller than $i$.

We can think of this construction as similar to the functor $U: \kappa\text{-CON} \to \kappa\text{-GAT}$ from section B.3.2 which produces a generalized $\kappa$-algebraic theory $U(\mathcal{C})$ from a $\kappa$-contextual category $\mathcal{C}$. In particular, for a display map $B_{\lambda+1} \twoheadrightarrow B_\lambda \in \mathcal{C}$ it gives a type axiom $\overline{B_\lambda} \vdash \overline{B_{\lambda+1}}$ Type.

*Remark 3.8.* For each of the examples below, we start with a Quillen model category $\mathcal{M}$ and apply theorem 3.7 to obtain a theory $T_{\mathcal{M}}$. In general, this is the guiding principle that will allow us to identify the statements, and the language, to which the invariance theorems apply.

Furthermore, using the theory $T_{\mathcal{M}}$ we can consider the category $\text{Mod}(T_{\mathcal{M}})$ and use theorem 2.14 to obtain a weak factorization system. Through this process, the cofibrations and trivial fibrations we obtain coincide with those from the Quillen model category we start with. However, in general we do not have an equivalence of categories $\text{Mod}(T_{\mathcal{M}}) \cong \mathcal{M}$.

### 3.1 Categories

Let us illustrate our construction on this prime example we have been referring to throughout the paper. Recall that $\mathbf{0}$ is the empty category, $\mathbf{1} := \{0\}$ is the category with a single object, $\mathbf{2} := \{0 \to 1\}$ the arrow category and $P := \{0 \Rightarrow 1\}$ the category with two parallel arrows. Finally, $\mathcal{J} := \{0 \Rightarrow 1\}$ denotes the walking isomorphism category. The following result appears in [Rez96].

**Theorem 3.9.** *There is Quillen model structure on the category $\mathbf{Cat}$ such that:*

1. *Weak equivalences are the equivalences of categories,*
2. *Cofibrations are the functors injective on objects,*

33

# 3. *Fibrations are the isofibrations.*

*Furthermore, this models structure is cofibrantly generated. The sets*

$$I := \{ \mathbf{0} \xrightarrow{u} \mathbf{1}, \{0\} \sqcup \{1\} \xrightarrow{v} \mathbf{2}, P \xrightarrow{w} \mathbf{2} \} \text{ and } J := \{ \mathbf{1} \to \mathcal{J} \}$$

*are the generating cofibrations and trivial cofibrations respectively.*

In this model structure all objects are cofibrant. We can immediately associate for each generator in $I$ a sort in the following way:

$$\begin{array}{ccc} \mathbf{0} \to \mathbf{1} & \longmapsto & \vdash \text{Ob Type} \\ \{0\} \sqcup \{1\} \to \mathbf{2} & \longmapsto & x, y : \text{Ob} \vdash \text{Hom}(x, y) \text{ Type} \\ P & \longmapsto & x, y : \text{Ob}, f, g : \text{Hom}(x, y) \vdash \text{Eq}(f, g) \text{ Type} \end{array}$$

Note that while the type $\text{Ob}$ has no dependencies, the type $\text{Hom}(x, y)$ depends on two elements of type $\text{Ob}$, which is encoded in the cofibration $\{0\} \sqcup \{1\} \to \mathbf{2}$. The same situation applies with the type $\text{Eq}$ which furthermore has dependencies on the types $\text{Ob}$ and $\text{Hom}$, now the cofibration $P \hookrightarrow \mathbf{2}$ expresses this.

*Remark 3.10.* The reason the previous association is well-defined is that the set of generating cofibrations $I$ of the model structure on $\text{Cat}$ from theorem 3.9 has a natural well-founded order—in the sense of theorem 3.2. Indeed, we can set $\mathbf{0} \to \mathbf{1}$ as the least element. Since the domain of the cofibration $\{0\} \sqcup \{1\} \to \mathbf{2}$ is a pushout of $\mathbf{0} \to \mathbf{1}$, we can declare $(\mathbf{0} \to \mathbf{1}) < (\{0\} \sqcup \{1\} \to \mathbf{2})$. Following the same reasoning, we see that the domain of the cofibration $P \to \mathbf{2}$ is the pushout of two copies of $\{0\} \sqcup \{1\} \to \mathbf{2}$. Therefore, we can also set $(\{0\} \sqcup \{1\} \to \mathbf{2}) < (P \to \mathbf{2})$. This completely determines the order $<$ on $I$, which is well-founded by construction. For all the subsequent examples, one can induce the corresponding well-founded orders analogously.

The resulting theory is what we introduced earlier, $\text{Cat}_=$, which for convenience we recall here. This is defined as:

1. Type of objects: $\vdash \text{Ob Type}$.
2. Type of morphisms: $x : \text{Ob}, y : \text{Ob} \vdash \text{Hom}(x, y) \text{ Type}$.
3. Equality type: $x, y : \text{Ob}, f, g : \text{Hom}(x, y) \vdash \text{Eq}(f, g) \text{ Type}$
4. Composition operation: $x, y, z : \text{Ob}, f : \text{Hom}(x, y), g : \text{Hom}(y, z) \vdash g \circ f : \text{Hom}(x, z)$.

34

5. Identity operator: $x : \mathsf{Ob} \vdash \mathsf{id}_x : \mathsf{Hom}(x, x)$.

Subject to the following axioms:

- $x : \mathsf{Ob}, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash \mathsf{id}_y \circ f \equiv f$.
- $x : \mathsf{Ob}, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash f \circ \mathsf{id}_x \equiv f$.
- $x : \mathsf{Ob}, y : \mathsf{Ob}, z : \mathsf{Ob}, w : \mathsf{Ob}, f : \mathsf{Hom}(x, y), g : \mathsf{Hom}(y, z), h : \mathsf{Hom}(z, w) \vdash (h \circ g) \circ f \equiv h \circ (g \circ f)$.
- $x, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash r_f : \mathsf{Eq}(f, f)$.
- $x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash f \equiv g$.
- $x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash a \equiv r_f$.

*Remark 3.11.* In the example above, we have imposed additional axioms for terms of type Hom and Eq. The reason behind this is solely so that the models of the theory $Cat_{\equiv}$ are exactly the categories.

As pointed out in theorem 2.4 the language we obtain is the same as the one given by [Bla78] and [Fre76]. In the introduction we presented the formula for an object $x$ to be terminal:

$$\forall y \in \mathsf{Ob}, (\exists v \in \mathsf{Hom}(y, x) \wedge \forall u, w \in \mathsf{Hom}(y, x), \mathsf{Eq}(u, w)).$$

Such formula is written in the language of categories.

*Observation 3.12.* We verify the above differently to showcase the fact that we do not need to explicitly know the language (type theory) associated to a model category, we only need to know that it can be constructed out of cofibrations. The formula above is constructed by first quantifying universally over the cofibration $\mathbf{0} \rightarrow \mathbf{1}$ to give $\forall y \in \mathsf{Ob}$. Note that applying the existential quantifier to $\{0\} \sqcup \{1\} \rightarrow \mathbf{2}$ gives us $\exists v \in \mathsf{Hom}(y, x)$ and the universal quantifier on $\mathbf{1} \rightarrow \mathcal{J}$. In the end, the formula can be seen as a composition pushouts “in context $x$.” Building the context of a formula is not an easy task, however, it might be easier to describe a pushout.

*Remark 3.13.* We mentioned at the beginning of the section that the association we do from cofibrations to types is not extremely formal. Again, the reason is that the equivalence between $\kappa$-clans and generalized $\kappa$-algebraic theories, section B, is not explicit. The association we make, for categories and the other examples below, is the obvious one and ad-hoc to the expected theory. From the start, we know what our intended models are, so once we have the types we define the operations and impose the equations that our intended models satisfy. We stress that this is informal and not very precise.

35

*Remark 3.14.* In general, a cofibration in a model category could be decomposed as a pushouts of cofibrations in more than one way. Depending on our choices, it might happen that we end up with different, but equivalent, theories.

One of the worst case scenarios is when we do not have a straightforward well-ordering. See the case for unbounded chain complexes below section 3.4.

### 3.2 2-categories and Bicategories

In this section we examine the language associated to the canonical model structures on the categories **2-Cat** and **Bicat$_{s}$**, respectively. The model structure for these two categories was defined in [Lac02] and [Lac04].

Given a category $C$ its suspension $\sum C$, is defined as the 2-category with two objects $X, Y$, the hom categories are $\sum C(X, X) = \sum C(Y, Y) = \sum C(Y, X) = \emptyset$ and $\sum C(X, Y) = C$. Furthermore, each bicategory $\mathcal{B} \in \mathbf{Bicat_s}$ has an underlying **Cat-graph**, in the sense of [Wol74]. This induces a functor $U : \mathbf{Bicat_s} \rightarrow \mathbf{Cat-graph}$ which has left adjoint $F$; this gives us the free bicategory generated by a **Cat**-graph. The suspension of a category $C$ can be seen as a **Cat**-graph associated to $C$. The free bicategory generated by the suspension of a category is denoted by $\sum C$. Moreover, this construction is functorial.

[Lac04, Theorem 3] constructs a model structure for the category of bicategories. This model structure is cofibrantly generated with generating cofibrations given by the suspension of the generating cofibrations of the canonical model structure on **Cat** and an additional functor we specify below. Finally, $\mathcal{E}$ is the “free-living adjoint equivalence” is the bicategory with objects $x, y$, freely generated by 1-cells $f : x \rightarrow y$ and $g : y \rightarrow x$, and two invertible 2-cells $\eta : 1_x \Rightarrow gf$, $\varepsilon : fg \Rightarrow 1_y$ satisfying the familiar triangle identities.

**Theorem 3.15** ([Lac04, Theorem 3]). *There is a model structure on the category $\mathbf{Bicat_s}$ of bicategories and strict bifunctors such that:*

1. *Weak equivalences are the biequivalences,*
2. *Fibrations are the strict bifunctors with the equivalence lifting property.*
*Furthermore, the model structure is cofibrantly generated by the sets*

$$I := \{ \mathbb{O} \rightarrow \mathbb{1}, \Sigma u, \Sigma v, \Sigma w \} \text{ and } J := \{ \mathbb{1} \rightarrow \mathcal{E} \}$$

*where $\mathbb{O}$ is the empty bicategory, $\mathbb{1}$ is the bicategory with a single object and no non-identity 2-cells, the functors $u, v, w$ come from theorem 3.9, and the bifunctor in $J$ picks the object $x$.*

36

When we analyze the set of generating cofibrations $I$ we rediscover the generalized algebraic theory of bicategories $Bicat_{=}$:

- $\mathbb{O} \to \mathbb{1} \longmapsto \vdash \mathsf{Ob}\,\mathsf{Type}$
- $\{x\} \sqcup \{y\} \xrightarrow{\sum w} \{x \to y\} \mapsto x, y : \mathsf{Ob} \vdash \mathsf{Hom}(x, y)$
- $x \xrightarrow[1]{0} y \xrightarrow{\sum w} x \xrightarrow[1]{0} y \mapsto x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y) \vdash \mathsf{Hom}(f, g)\,\mathsf{Type}$
- $x \xrightarrow[1]{0} y \xrightarrow{\sum w} x \xrightarrow[1]{0} y \mapsto \begin{cases} x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), \\ \alpha, \beta : \mathsf{Hom}(f, g) \vdash \mathsf{Eq}(\alpha, \beta)\,\mathsf{Type} \end{cases}$

Moreover, we can also introduce the composition and identity operations for arrows and cells:

- Composition operation for arrows: \( x: \mathsf{Ob}, y: \mathsf{Ob}, z: \mathsf{Ob}, f: \mathsf{Hom}(x, y), g: \mathsf{Hom}(y, z) \vdash g \circ f: \mathsf{Hom}(x, z) \).
- Identity operator for arrows: \( x: \mathsf{Ob} \vdash \mathsf{id}_x: \mathsf{Hom}(x, x) \).
- Vertical composition of cells: \( x, y: \mathsf{Ob}, f, g, h: \mathsf{Hom}(x, y), \alpha: \mathsf{Hom}(f, g), \beta: \mathsf{Hom}(g, h) \vdash \beta \circ \alpha: \mathsf{Hom}(f, h) \).
- Horizontal composition of cells: \( x, y, z: \mathsf{Ob}, f, g: \mathsf{Hom}(x, y), h, k: \mathsf{Hom}(y, z), \alpha: \mathsf{Hom}(f, g), \beta: \mathsf{Hom}(h, k) \vdash \alpha * \beta: \mathsf{Hom}(h \circ f, k \circ g) \).
- Identity operator for cells: \( x, y: \mathsf{Ob}, f: \mathsf{Hom}(x, y) \vdash \mathsf{id}_f: \mathsf{Hom}(f, f) \).

One can also attempt to list all the axioms that the above theory ought to satisfy, with the risk of running out of space. We simply exemplify this with the associator:

$$
\begin{aligned}
w, x, y, z : \mathsf{Ob}, f : \mathsf{Hom}(w, x), g : \mathsf{Hom}(x, y), h : \mathsf{Hom}(y, z), \\
\alpha : \mathsf{Hom}((h \circ g) \circ f, h \circ (g \circ f)), \beta : \mathsf{Hom}((h \circ (g \circ f), h \circ g) \circ f) \\
\quad \vdash r : \mathsf{Eq}(\alpha \circ \beta, \mathsf{id}_{(h \circ (g \circ f)}) \wedge s : \mathsf{Eq}(\beta \circ \alpha, \mathsf{id}_{(h \circ g) \circ f}).
\end{aligned}
$$

We also include the axioms for Eq — the same ones as for categories — that gives us the expected behaviour.

37

Remark 3.16. If we now try to obtain the associated theory $2Cat_{=}$ using the generating cofibration of [Lac04], we see that the resulting theory has similar types and operations as the theory $Bicat_{=}$ of bicategories. The notable differences are that we do not need associators or unitors, but we need to include equations for the associativity and unitality of the composition of arrows and cells, and also the interchange law relating horizontal and vertical composition of cells. All these axioms are the appropriate ones to obtain 2-categories as the models of the theory $2Cat_{=}$.

Definition 3.17. Let $\mathcal{C}$ be a 2-category. An object $x \in \mathcal{C}$ is bi-terminal if for all $y \in \mathcal{C}$ there is an equivalence of categories $\mathcal{C}(y, x) \cong \mathbf{1}$.

Note that $f : a \to b$ being an equivalence can be written as

$$\exists h : \operatorname{Hom}(b, a), \exists \eta : \operatorname{Hom}(\mathrm{id}_a, h \circ f), \exists \varepsilon : \operatorname{Hom}(f \circ h, \mathrm{id}_b), \mathrm{islso}(\eta) \wedge \mathrm{islso}(\varepsilon), \top.$$

Observe that the statement $\mathrm{islso}(\eta)$, which says that $\eta : f \Rightarrow g$ is a natural isomorphism, only involves equality of natural transformations:

$$\mathrm{islso}(\eta)) := \exists \epsilon : \operatorname{Hom}(g, f), s : \mathsf{Eq}(\epsilon \circ \eta, \mathrm{id}_f) \wedge r : \mathsf{Eq}(\eta \circ \epsilon, \mathrm{id}_g), \top.$$

We can then conclude that the notion of bi-terminal object is invariant.

Remark 3.18. Other natural, but somewhat different, higher categories to consider in this progression are the double categories. Fortunately, this question has been described in Paula Verdugo's PhD thesis [Ver24], or [Ver25]. In particular, she builds a model structure on double categories where the fibrant objects are the equipments. The language for this model structure produces formulas that express properties of equipments. Therefore, we can use our invariance theorems for this "language of equipments". The details of this are exposed in Verdugo's PhD thesis cited above.

### 3.3 Bounded below chain complexes

In this section, we examine the language of the projective model structure on bounded below chain complexes $Ch(R)$ over a commutative ring $R$. We start by recalling some facts about this model structure. The detailed proofs can be found elsewhere, e.g. [Hov99].

Given an $R$-module $M$, for each $n \in \mathbb{Z}$ define $S^n(M) \in Ch(R)$ by

$$S^n(M)_k := \begin{cases} M, & k = n \\ 0, & k \neq n. \end{cases}$$

38

Similarly, $D^n(M) \in Ch(R)$ is defined as

$$D^n(M)_k := \begin{cases} M, & k = n - 1, \ n \\ 0, & \text{otherwise.} \end{cases}$$

where the only non-trivial differential $d_n : M \rightarrow M$ is the identity. Obviously, we get an inclusion $S^{n-1}(M) \rightarrow D^n(M)$.

These constructions induce functors $S^n : R\text{-}Mod \rightarrow Ch(R)$ and $D^n : R\text{-}Mod \rightarrow Ch(R)$ for each $n \in \mathbb{Z}$. Both functors have right adjoints $Z_n : Ch(R) \rightarrow R\text{-}Mod$ and $Ev_n : Ch(R) \rightarrow R\text{-}Mod$, respectively, where $Z_n X := Ker(d_n)$ and $Ev_n X := X_n$.

In particular, when $M = R$ the chains above are denoted by $S^n$ and $D^n$, respectively. We can define the sets

$$I := \{S^{n-1} \rightarrow D^n | n \in \mathbb{Z}\} \text{ and } J := \{0 \rightarrow D^n | n \in \mathbb{Z}\}.$$

All constructions above work on unbounded chain complexes too. In the next result we restrict to bounded below chains, *i.e.*, $n \geq 0$. By definition $(D^0)_{-1} = 0$, so that $S^0 = D^0$. With this information, what we need to know about the projective model structure is summarized in the following:

**Theorem 3.19** ([Qui06]). *The category of chain complexes $Ch(R)$ admits a model structure where:*

1. *Weak equivalences are the quasi-isomorphisms*
2. *Fibrations are the degree-wise epimorphisms.*
3. *Cofibrations are the degree-wise monomorphisms with projective cokernel.*

*Furthermore, this model structure is proper, cofibrantly generated and combinatorial. Cofibrations and trivial cofibrations are generated by $I$ and $J$, respectively.*

The cofibrant objects in the mode structure from theorem 3.19 are complexes such that each $R$-module is projective. However, this is not the case for unbounded chain complexes, where not every chain complex with projective modules is cofibrant. Nevertheless, in both cases, all objects are fibrant.

39

Remark 3.20. Using the adjunction $S^n \dashv Z_n$, for any chain complex $X$, a map $S^n \to X$ is simply a map $R \to Z_n X$ of $R$-modules. And from $D^n \dashv E v_n$, a map $D^n \to X$ corresponds to $y \in X_n$. Therefore, a commutative square

$$\begin{array}{c} S^{n-1} \xrightarrow{x} X \\ i_n \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ D^n \xrightarrow{Y} Y \end{array}$$

means that $x \in Z_{n-1}X \subseteq X_{n-1}$ i.e., $d_{n-1}x = 0$ and that $fx = y \in Y_n$. Therefore, taking a pushout simply means we freely add $(n-1)$-cycles to $X_{n-1}$ with a specified boundary.

The first element i.e., $n = 0$, of the set $I$ is the cofibration

$$\begin{array}{c c c c c c c c} 0 & & 0 \longleftarrow & 0 \longleftarrow & 0 \longleftarrow & \dots \\ i_0 \downarrow & & \downarrow & \downarrow & \downarrow & \\ D^0 & & 0 \longleftarrow & R \longleftarrow & 0 \longleftarrow & \dots \end{array}$$

For any $n \ge 1$ we have cofibrations $i_n$

$$\begin{array}{c c c c c c c c c} S^{n-1} & & 0 \longleftarrow & \dots \longleftarrow & R \longleftarrow & 0 \longleftarrow & 0 \longleftarrow & \dots \\ i_n \downarrow & & \downarrow & & 1_R & \downarrow & \downarrow & \\ D^n & & 0 \longleftarrow & \dots \longleftarrow & R \longleftarrow 1_R - R \longleftarrow & 0 \longleftarrow & \dots \end{array}$$

We then see immediately that $I$ has a natural, well-founded, order, where we can set $i_0$ to be the minimal element of the set.

From theorem 3.20, we get cycles $y \in X_n$ and for each $x \in X_{n-1}$ such that $dx = 0$ and $\mathsf{C}_n(x) := \{y \in X_n | dy = x\}$, this is for each generating cofibration $i_n : S^{n-1} \to D^n$. This tells us that the $\omega$-generalized algebraic theory has types $\mathsf{C}_n(x)$ for $n \ge 1$. We sum up the discussion in the following table:

$$i_0 : 0 \to D^0 \qquad \mapsto \qquad \vdash \mathsf{C}_0 \text{ Type}$$

$$i_n : S^{n-1} \to D^n \qquad \mapsto \qquad x : \mathsf{C}_{n-1}(0) \vdash \mathsf{C}_n(x) \text{ Type}$$

for $n \ge 1$. Note that the differential is already included in the information that defines the types $\mathsf{C}_n(x)$. We should also add, not included in the table, “+” operations on each type $\mathsf{C}_n(x)$, and axioms, that ensure is an abelian group:

$$a : \mathsf{C}_n(x), b : \mathsf{C}_n(y) \vdash a + b : \mathsf{C}_n(x+y).$$

40

Observation 3.21. It is important to note that in the theory we do not have equality between chains. The only possibility is to consider $\mathsf{C}_n(x)$ for $x : \mathsf{C}_{n-1}(0)$. However, this is enough to speak about chains satisfying a boundary condition $x - y = d_n z$ which is written in our language as

$$\exists z : \mathsf{C}_n(x - y), \top.$$

### 3.4 Unbounded chain complexes

When we work with unbounded chain complexes theorem 3.19 becomes:

**Theorem 3.22** ([Hov99, Theorem 2.3.10]). *The category of chain complexes $Ch(R)$ admits a model structure where:*

1. Weak equivalences are the quasi-isomorphisms
2. Fibrations are the degree-wise epimorphisms.
3. Cofibrations are the degree-wise split monomorphisms with cofibrant cokernel.

Furthermore, this model structure is proper, cofibrantly generated and combinatorial. Cofibrations and trivial cofibrations are generated by $I$ and $J$, respectively.

Unlike the case for bounded chains, the set $I$ of generating cofibrations, is not well-founded in the sense of theorem 3.2. However, we can obtain a new generating set of cofibrations following theorem 3.6. We consider the new set $I' := I \cup \{0 \to S^n | n \in \mathbb{Z}\}$. Note that since $0 \to S^n$ is already a cofibration, we are not altering the model structure. The resulting theory is similar to the bounded case, we now must have the following association:

$$0 \to S^n \qquad \mapsto \qquad \vdash \mathsf{Z}_n \text{ Type}$$

$$i_n : S^{n-1} \to D^n \qquad \mapsto \qquad x : \mathsf{Z}_{n-1} \vdash \mathsf{C}_n(x) \text{ Type}$$

for $n \in \mathbb{Z}$.

Again, we need to add some non-type axioms. For example, we need each $Z_n$ to contain an element $0$, and $C_n(0) = Z_n$, then each $C_n$ has an abelian group structure as in the case of bounded complexes.

41

### 3.5 Topological spaces

Here we recall the Quillen model structure on the category of topological spaces **Top** [Qui06]. Recall that a map $f : X \to Y \in \mathbf{Top}$ is a *weak homotopy equivalence* if for all $x \in X$ and $n \geq 1$ the induced map $f_* : \pi_n(X, x) \to \pi_n(Y, f(x))$ is an isomorphism of groups and for $n = 0$ is a bijection. Additionally, the map $f$ is a *Serre fibration* if for any $CW$-complex $W$ the following square has a diagonal filler:

![img-4.jpeg](img-4.jpeg)

**Theorem 3.23.** *The category **Top** has a model category structure such that:*

1. *Weak equivalences are the weak homotopy equivalences.*
2. *Fibrations are the Serre fibrations.*
3. *Cofibrations are the maps with the left lifting property against trivial fibrations.*

*Moreover, this model structure is cofibrantly generated. The generating cofibrations is the set of boundary inclusions $\{S^{n-1} \to D^n | n \in \mathbb{N}\}$. The set $\{D^n \to D^n \times [0, 1] | n \in \mathbb{N}\}$ generates trivial cofibrations.*

We can immediately write some of the relevant type axiom of the resulting theory:

- $\vdash 0\text{-CW Type.}$
- $x, y : 0\text{-CW} \vdash 1\text{-CW}(x, y)\text{ Type.}$
- $x : 0\text{-CW}, \gamma : 1\text{-CW}(x, x) \vdash 2\text{-CW}(x, \gamma)\text{ Type.}$
- $\vdots$

Note that the language associated to the model structure allows us to express properties of topological spaces without relying on a specific set of axioms. However, this presents a limitation coming from the fact that we do not have an equality type. It is a classic result that there is no finitary presentation of a topological space. But in our setting, when $X$ is a CW-complex *i.e.*, it is obtained as an iterated pushout of cells, then a continuous map $D^n \to X$ can be written in the language above.

42

**Example 3.24.** We cannot write the formula

$$\exists x : 0\text{-CW} \forall y : 0\text{-CW}, x = y.$$

The only possibility is to write

$$\forall x, y : 0\text{-CW} \exists \alpha : 1\text{-CW}(x, y), \top$$

which simply says that a space is path-connected. Moreover, we can not say that two paths $\alpha, \beta : 1\text{-CW}(x, x)$ are homotopic in the usual sense, only that there exists $\sigma : 3\text{-CW}$ connecting the two loops.

### 3.6 Kan complexes and quasi-categories

In this section, we analyze two very well-known model structures on the category of simplicial sets **sSet**; the Kan–Quillen and the Joyal model structures. One interesting feature is that we obtain the same theory for both models, but under the light of theorem 2.38 meaningful statements are delimited by the fibrant objects. In the first model we are interested in Kan complexes, while in the second model in the quasi-categories. The first model appears in [Qui06] and the second in [Joy08]. These are the first references one can find, but the literature is ample for both models.

Recall that a map $f : X \to Y$ between simplicial sets is a *Kan fibration* if it has the right lifting property for all horn inclusions, *i.e.*, the solid diagram below a diagonal filler

$$\begin{array}{c} \Lambda^k[n] \longrightarrow X \\ \downarrow \quad \nearrow \quad \downarrow f \\ \Delta[n] \longrightarrow Y \end{array}$$

for all $0 \le k \le n \in \mathbb{N}$. The simplicial set $X$ is a *Kan complex* if the unique map to the terminal presheaf is a Kan fibration. This is the result from [Qui06]:

**Theorem 3.25.** *The category of simplicial sets* **sSet** *carries a model structure in which:*

1. *Weak equivalences are maps* $f : X \to Y$ *whose geometric realization* $|f| : |X| \to |Y|$ *is a weak homotopy equivalence in the category of topological spaces* **Top**. *These are called Kan equivalences.*

2. *Fibrations are the Kan fibrations.*

43

### 3. Cofibrations are the monomorphisms.

The class of cofibrations is generated by $I := \{\partial\Delta[n] \hookrightarrow \Delta[n]|n \in \mathbb{N}\}$ and trivial cofibrations are generated by $J := \{\Lambda^k[n] \to \Delta[n]|n \in \mathbb{N} \text{ and } 0 \leq k \leq n\}$.

Similarly, a map $f : X \to Y$ between simplicial sets is an inner Kan fibration if it has the right lifting property for all inner horn inclusions, i.e., the solid diagram below a diagonal filler

![img-5.jpeg](img-5.jpeg)

for all $0 < k < n \in \mathbb{N}$. The simplicial set $X$ is a quasi-category if the unique map to the terminal presheaf is an inner Kan fibration. This is the result from [Joy08]:

**Theorem 3.26.** The category of simplicial sets **sSet** carries a model structure in which:

1. Weak equivalences are the weak categorical equivalences.
2. Fibrations are the inner Kan fibrations.
3. Cofibrations are the monomorphisms.

The class of cofibrations is generated by $I := \{\partial\Delta[n] \hookrightarrow \Delta[n]|n \in \mathbb{N}\}$, the set of boundary inclusions.

Notice that both model structures have the same class of generating cofibrations. Hence, we expect that they have the same theories. We get a type for each cofibration in $I$. The first elements in this list of types are:

- $\vdash$ 0-simplex Type.
- $\sigma_0, \sigma_1 : 0$-simplex $\vdash$ 1-simplex$(\sigma_0, \sigma_1)$ Type.
- $\sigma_0, \sigma_1, \sigma_2 : 0$-simplex, $\quad \sigma_{01} : 1$-simplex$(\sigma_0, \sigma_1)$, $\quad \sigma_{12} : 1$-simplex$(\sigma_1, \sigma_2)$, $\quad \sigma_{02} : 1$-simplex$(\sigma_0, \sigma_2) \vdash 2$-simplex$(\sigma_0, \sigma_1, \sigma_2, \sigma_{01}, \sigma_{12}, \sigma_{02})$ Type.
- $\vdots$

44

The picture we should have in mind on the dependency of types is the usual one about simplices. A 1-simplex depend on two 0-simplicies, a 2-simplex consist of three 0-simplicies and three 1-simplicies connecting them, and so forth.

One can see that the faces of an $n$-simplex are obtained via the dependencies, or context in which is defined. However, we can still adopt the usual notation for faces. Specifically, for each $n \in \mathbb{N}$ one has the faces $d_i(\sigma_{0123...(i-1)i(i+1)...n}) := \sigma_{0123...(i-1)(i+1)...n}$ is the $(n-1)$-simplex “opposite” to the $i$-th vertex of $\sigma_{012...n}$. This simplex is already defined, and it is used in the construction of $\sigma_{012...n}$. We emphasize that this is not part of the theory, but just a convenient and familiar shortcut.

The degeneracy operator is part of the theory and needs to be introduced:

$$\sigma_{0123...(i-1)i(i+1)...n} : n\text{-simplex} \vdash s_i(\sigma_{0123...(i-1)i(i+1)...n}) : (n+1)\text{-simplex}$$

where $s_i(\sigma_{0123...(i-1)i(i+1)...n}) := \sigma_{0123...(i-1)i(i+1)...n}$ is the $(n+1)$-simplex that contains $\sigma_{0123...(i-1)i(i+1)...n}$ as its $i$-th and $(i+1)$-faces. We have one of such operations for $0 \le i \le n$. The way we have introduced this operation is not completely correct as we are missing the dependencies for $n$-simplex and $(n+1)$-simplex and the context, nevertheless we can infer them. For example:

$$x, y : 0\text{-simplex}, f : 1\text{-simplex}(x, y) \vdash s_1(f) : 2\text{-simplex}(x, y, y, f, s_0(y), f)$$

where $s_0(y)$ is the degeneracy of $y$ or the “identity of $y$” and is constructed previously.

We also expect the simplicial identities to be satisfied. However, we do not need to postulate all of them as axioms of the theory since some of them are given via dependencies or by the typing of the operations. The only equation we postulate is $s_i s_j = s_{j+1} s_i$ for $i \le j$. On the one hand, the usual equation $d_i d_j = d_{j-1} d_i$ for $i < j$ only involves faces, therefore everything is encoded in the dependency. On the other hand, the equation

$$d_i s_j = \begin{cases} s_{j-1} d_i, & i < j \\ Id, & i = j, j+1 \\ s_j d_{i-1}, & i > j+1 \end{cases}$$

is valid from the definition of degeneracies and dependency of the faces.

We should note again that there is no visible difference in the language of the Joyal model structure and the language of the Kan-Quillen model structure as these have the same cofibrations. The only difference is that

45

the language of the Kan-Quillen model structure is only meant to be applied to Kan complexes, while the language of the Joyal model structure can be applied to quasi-categories.

**Example 3.27.** A Kan complex $X$ is contractible if it is weakly homotopy equivalent to $\mathbf{1}$. This is just to say that for any $n \geq 0$ we can find a lift

![img-6.jpeg](img-6.jpeg)

which expresses the fact that the unique map $X \rightarrow \mathbf{1}$ is a weak homotopy equivalence. Note that $X$ must satisfy an infinite number of conditions:

- For $n = 0$ this says: $\exists \sigma_0 : 0\text{-simplex}$,
- For $n = 1$ this says: $\forall \sigma_0, \sigma_1 : 0\text{-simplex}, \exists \sigma_{01} : 1\text{-simplex}(\sigma_0, \sigma_1)$,
- For $n = 2$ this says:

$$\begin{aligned} &\forall \sigma_0, \sigma_1 : 0\text{-simplex} \, \sigma_{01} : 1\text{-simplex}(\sigma_0, \sigma_1), \sigma_{12} : 1\text{-simplex}(\sigma_1, \sigma_2), \\ &\sigma_{02} : 1\text{-simplex}(\sigma_0, \sigma_2), \exists \sigma_{012} : 2\text{-simplex}(\sigma_0, \sigma_1, \sigma_2, \sigma_{01}, \sigma_{12}, \sigma_{02}). \end{aligned}$$

One continues unpacking the conditions and takes the infinite conjunction of the formulas.

Alternatively, we can note that the domain of a trivial cofibration $i_n : \partial \Delta^n \hookrightarrow \Delta^n$ give us the context, or hypotheses, of the statement. In this case, the codomain gives us the type where the conclusion holds. If we accept this, let us write, $t \in \mathbb{L}^{\mathbf{sSet}}(\partial \Delta^n)$ for a term (formula) which expresses a property in the context $\partial \Delta^n$, similarly $t' \in \mathbb{L}^{\mathbf{sSet}}(\Delta^n)$ for a formula in the context $\Delta^n$. With this convention, we do not have to use the theory explicitly. When we apply the quantifiers, universal or existential, we move these formulas to $\mathbb{L}^{\mathbf{sSet}}(\emptyset)$ and ask whether a fibrant object satisfies the resulting formula. For $\top \in \mathbb{L}^{\mathbf{sSet}}(\Delta^n)$ then for $i_n : \partial \Delta^n \hookrightarrow \Delta^n$ and $j_n : \emptyset \to \partial \Delta^n$ we get maps

$$\exists_{i_n} : \mathbb{L}^{\mathbf{sSet}}(\Delta^n) \to \mathbb{L}^{\mathbf{sSet}}(\partial \Delta^n) \text{ and } \forall_{j_n} : \mathbb{L}^{\mathbf{sSet}}(\partial \Delta^n) \to \mathbb{L}^{\mathbf{sSet}}(\emptyset),$$

and thus the formula $\forall_{j_n} \exists_{i_n} \top : \mathbb{L}^{\mathbf{sSet}}(\emptyset)$ would say that a Kan complex satisfies the corresponding lifting problem. For a Kan complex to be contractible, it needs to satisfy formulas for all $n \in \mathbb{N}$. Therefore,

$$\text{isContr}(X) := (X \vdash \bigwedge_{n \in \mathbb{N}} \forall_{j_n} \exists_{i_n} \top).$$

46

We are now convinced that contractibility can be written in the language we just described. Theorem 3.27 indicates that we might not need to get an explicit syntax from the generating set of cofibrations. Instead, we might just quantify over the required cofibrations. The main reason this is preferable over explicitly defining the syntax is that in general such syntax is complicated to write, see for example section 3.8. The previous example shows that we might prefer to choose simplifications that make our sentences easier to read. This is specially true for contexts like the ones covered in the following section.

### 3.7 Reedy languages

The purpose of this subsection is to describe the language for the category $\mathcal{M}^{K^{op}}$, where $K$ is a Reedy category and $\mathcal{M}$ is a model category whose language we know. This encompasses some of the previous examples and opens the door to further applications.

Recall that if $\mathcal{M}$ is a cofibrantly generated model category whose cofibrations are generated by a well-founded set of cofibrations $I$, then for each cofibration $A \hookrightarrow B \in I$ we can associate a type introduction axiom $\bar{A} \vdash \bar{B}$ Type, where $\bar{A}$ is a well-formed context previously constructed.

Let $K$ be a Reedy category with degree function $\deg : K \to \omega$. This restriction is artificial since we could consider more general Reedy categories, however, for the examples this construction is aimed at, this is enough. The objects of $K$ have a well-founded order relation induced by the degree function.

**Construction 3.28.** Let $\partial \updownarrow_k$ be the latching object of the representable functor $\updownarrow_k$ and $d_k : \partial \updownarrow_k \to \updownarrow_k$ the induced map. There is a bifunctor

$$\otimes : \mathbf{Set}^{K^{op}} \times \mathcal{M} \to \mathcal{M}^{K^{op}}$$

defined by $(A \otimes X)_k := \coprod_{A_k} X$. Let $I$ be as above, given $i : X \to Y \in I$ and $k \in K$ we apply the usual Leibniz construction and obtain the dashed arrow below

![img-7.jpeg](img-7.jpeg)

47

We now consider the set of maps $K \hat{\otimes} I := \{d_k \hat{\otimes} i | k \in K, i \in I\}$. By identifying each map $d_k \hat{\otimes} i \in K \hat{\otimes} I$ with a pair $(k, i)$, we see that $K \hat{\otimes} I$ is also a well-founded set with a relation, which we denote by $\leq_{\otimes}$. Here the relation is defined entry by entry *i.e.*, $(k', i') \leq_{\otimes} (k, i)$ if and only if $\deg(k') \leq \deg(k)$ and $i' \leq_I i$, where $\leq_I$ is the well-founded relation on $I$.

The previous construction is further justified by [Bar19, Proposition 2.3.22] for premodel categories, but a similar description is abundant in the literature for Quillen model categories.

**Proposition 3.29.** *The Reedy weak factorization system on $\mathcal{M}^{K^{\text{op}}}$ is generated by $K \hat{\otimes} I$, and therefore the Reedy model category structure on $\mathcal{M}^{K^{\text{op}}}$ is combinatorial whenever $\mathcal{M}$ is combinatorial.*

A useful result we can have in mind is the following:

**Lemma 3.30.** *Given any $i: A \rightarrow B \in \mathcal{M}$, a morphism $f: X \rightarrow Y \in \mathcal{M}^{K^{\text{op}}}$ has the lifting property with respect to $d_k \hat{\otimes} i$, if and only if $\hat{f}^k: X_k \rightarrow Y_k \times_{M_k Y} M_k X$ has the right lifting property with respect to $i$.*

*Proof.* As written, this is [Bar19, Lemma 2.3.21], but it is also a classical result found in [Hov99]. $\square$

*Remark 3.31.* The matching objects in theorem 3.30 are computed with respect to the Reedy structure of $K^{\text{op}}$. This means that the relevant diagram in $M_k X$ is given by maps in $(K^{\text{op}})_- = K_+$.

*Observation 3.32.* Many models for higher categories are built starting with presheaves over a Reedy category. Then to obtain the desired model one takes a left Bousfield localization for an appropriate class of maps. Importantly, this localization does not change the generating cofibrations. This is just to say that the language of $\mathcal{M}^{K^{\text{op}}}$ remains unchanged after localization.

The cofibrations for the Reedy model structure are usually rather complicated, we can sometimes proceed as in theorem 3.27. This is, if $\Gamma' \hookrightarrow \Gamma$ is a generating cofibration, then we might simply consider a formula $\phi' \in \mathbb{L}^{\mathcal{M}^{K^{\text{op}}}}(\Gamma')$ or $\phi \in \mathbb{L}^{\mathcal{M}^{K^{\text{op}}}}(\Gamma)$ with no explicit description of the type associated to the cofibration.

As an interesting case, in the following section we examine the Reedy language for Segal spaces. However, the construction applies to any other model category constructed similarly.

48

### 3.8 Segal spaces

We denote $\mathbf{ssSet} := [\Delta^{\mathrm{op}}, \mathbf{sSet}] = [\Delta^{\mathrm{op}} \times \Delta^{\mathrm{op}}, \mathbf{Set}]$ as the category of simplicial spaces, or bisimplicial sets. This category has two model structures that are obtained as left Bousfield localizations of the Reedy model structure. For both of these localizations, we use the Kan–Quillen model structure from the previous section. Recall that this model structure is cofibrantly generated. The set of generating cofibrations is the set of boundary inclusions. We will use the following facts and notation.

- There is an adjunction of two variables $\square : \mathbf{sSet} \times \mathbf{sSet} \rightarrow \mathbf{ssSet}$ defined as $(X \square Y)_{mn} := X_m \times Y_n$ for each $m, n \in \mathbb{N}$. This is called the box product.
- $\mathbf{sSet}$ can be seen as vertically embedded into $\mathbf{ssSet}$. If $X \in \mathbf{sSet}$, then it can be seen as a simplicial space $X \square \Delta[0]$. There is also a horizontal embedding by setting $\Delta[0] \square X$.
- For $[m] \in \Delta$ we write $F(n) := \Delta[n] \square \Delta[0]$ and $\partial F(n) := \partial \Delta[n] \square \Delta[0]$.
- The simplicial spaces $F(n)$ represent the $n$-th mapping space functors, respectively $Map(F(n), X) = X_n$.

There is map $\iota : F(1) \coprod_{F(0)} \cdots \coprod_{F(0)} F(1) \rightarrow F(n)$, where the colimit on left has $n$ factors. The following two model category structures were constructed by Rezk [Rez01].

**Theorem 3.33.** *The category admits a unique simplicial model category structure such that:*

1. *The cofibrations are the monomorphisms.*
2. *Fibrant objects are simplicial spaces $X$ such that the map*

$$X_n \rightarrow X_1 \times_{X_0} \cdots \times_{X_0} X_1$$

*induced by $\iota$ is a Kan equivalence. The fibrant objects are called Segal spaces.*

3. *The weak equivalences are the maps $f : X \rightarrow Y \in \mathbf{ssSet}$ such that*

$$Map(f, W) : Map(Y, W) \rightarrow Map(X, W)$$

*is a Kan equivalence for every Segal space $W$.*

49

4. A map $f : X \to Y$ between Segal spaces is a fibration (weak equivalence) if and only if is a Reedy fibration (Reedy weak equivalence).

Recall that $\mathcal{J}$ denotes the category with two objects and two arrows that are mutually inverses. It is usual to denote by $E(1)$ to the Segal space which is obtained by considering the nerve $N\mathcal{J}$ as a discrete simplicial space. This produces a map $F(1) \to E(1)$.

**Theorem 3.34.** *The category admits a unique simplicial model category structure such that:*

1. The cofibrations are the monomorphisms.
2. Fibrant objects are Segal spaces $X$ such that the map

$$Map(E(1), X) \to Map(F(0), X)$$

is a Kan equivalence. The fibrant objects are called complete Segal spaces.

3. The weak equivalences are the maps $f : X \to Y \in \mathbf{ssSet}$ such that

$$Map(f, W) : Map(Y, W) \to Map(X, W)$$

is a Kan equivalence for every complete Segal space $W$.

4. A map $f : X \to Y$ between complete Segal spaces is a fibration (weak equivalence) if and only if is a Reedy fibration (Reedy weak equivalence).

These models are cofibrantly generated. The set of generating cofibrations can be described using the box product [JT07, Proposition 2.2]. This set is given by $\hat{I} := \{d_m \hat{\square} d_n | m, n \in \mathbb{N}\}$. Explicitly, a map in $\hat{I}$ is of the form

$$d_m \hat{\square} d_n : \partial \Delta[m] \square \Delta[n] \coprod_{\partial \Delta[m] \square \partial \Delta[n]} \Delta[m] \square \partial \Delta[n] \to \Delta[m] \square \Delta[n]$$

We can obtain the generalized algebraic theory for (complete) Segal space. The domains of these maps provide the context in which a new type is formed. To get a sense of the theory, consider the following picture of a

50

bisimplicial set $X$:

![img-8.jpeg](img-8.jpeg)

The arrows indicate the degeneracy and face maps. Now we go back to consider the maps $d_m \square d_n$. When $m = n = 0$ then we simply get a map $\emptyset \to \Delta[0] \square \Delta[0]$, and allow us to introduce the type

$$\vdash \mathsf{Set}_{00} \mathsf{Type}.$$

When $n = 0$ the resulting subset of maps is of the form

$$d_m \square \Delta[0] : \partial \Delta[m] \square \Delta[0] \to \Delta[m] \square \Delta[0].$$

In this setting, since for $m = 0$ we obtain the previous cofibration $\emptyset \to \mathbf{1}$, for each $m \ge 1$ we can write the following types:

- \(x, y: \mathsf{Set}_{00} \vdash \mathsf{Set}_{10}(x, y)\) Type.
- \(x, y, z: \mathsf{Set}_{00}, f: \mathsf{Set}_{10}(x, y), g: \mathsf{Set}_{10}(y, z), h: \mathsf{Set}_{10}(x, z) \vdash \mathsf{Set}_{20}(x, y, z, f, g, h)\).
：

When $m = 0$ we obtain the theory of the categorical direction. Now suppose that $m = 1 = n$, then resulting generating cofibration is the map

$$d_1 \square d_1 : \partial \Delta[1] \square \Delta[1] \coprod_{\partial \Delta[1] \square \partial \Delta[1]} \Delta[1] \square \partial \Delta[1] \to \Delta[1] \square \Delta[1]$$

From here we see that the type associated to this map has the following form:

$$\begin{array}{l} x_0, x_1, x_2, x_3: \mathsf{Set}_{00}, f_{01}: \mathsf{Set}_{01}(x_0, x_1), f_{23}: \mathsf{Set}_{01}(x_2, x_3), f_{02}: \mathsf{Set}_{10}(x_0, x_2), \\ f_{13}: \mathsf{Set}_{10}(x_1, x_3) \vdash \mathsf{Set}_{11}(x_0, x_1, x_2, x_3, f_{01}, f_{23}, f_{02}, f_{13}) \mathsf{Type}. \end{array}$$

We think of this new type as the type of squares where the solid boundary is the given context

51

![img-9.jpeg](img-9.jpeg)

For different $m, n$ the context are simply more involved, but the dependencies can be inferred. Note we still need to add the degeneracy operators satisfying the usual axioms. We can see that as we build more complex contexts, it will be computationally difficult to obtain an explicit description of the types. We might instead proceed as in theorem 3.27.

**Example 3.35.** Two elements $x, y : \mathsf{Set}_{00}$ are said to be *homotopic* if there exists $\alpha : \mathsf{Set}_{10}(x, y)$. This sentence only involves types in the language of Segal spaces. In contrast to topological spaces, we can express the fact that two maps are homotopic.

*Remark 3.36.* Note in particular that the language of spaces or Kan complexes is available for us to use. This in combination with our construction in section 3.7 allow us to realize many properties of (complete) Segal spaces, for example the ones found in [Ras23], are written in this language.

### 3.9 Functors and Isofibrations

We denote $[1] := \{0 \to 1\}$ the category with two objects and single non-identity arrow. This category can be viewed as a Reedy category in two ways. The first one respects the direction of the arrow, so we take $[1]_+$ to be the non-identity map, while for the second we take the same map to be in $[1]_-$. Recall that if $K$ is a Reedy category, then $K^{\mathsf{op}}$ is also a Reedy category where $(K^{\mathsf{op}})_+ = K_-$ and $(K^{\mathsf{op}})_- = K_+$. In order to match the computations of theorem 3.28, we use the same notation as there. By which we mean that for a model category $\mathcal{C}$ we use $\mathcal{C}^{([1]_+)^{\mathsf{op}}}$ and $\mathcal{C}^{([1]_-)^{\mathsf{op}}}$ with the corresponding Reedy model structures, ignoring the fact that $\mathcal{C}^{([1]_+)^{\mathsf{op}}} = \mathcal{C}^{[1]_-}$ and $\mathcal{C}^{([1]_-)^{\mathsf{op}}} = \mathcal{C}^{[1]_+}$.

**Proposition 3.37.** *The Reedy model structure on $\mathcal{C}_{Reedy}^{([1]_-)^{\mathsf{op}}}$ coincides with the projective model structure. In particular, weak equivalences and fibrations are the level-wise weak equivalences and fibrations in $\mathcal{C}$.*

*Proof.* This is a classical and well-known result. $\square$

We are interested in the particular case of $\mathcal{C} = \mathbf{Cat}$. It is immediate to see that all objects are fibrant. The language we obtain should be the

52

language for functors. Since **Cat** is cofibrantly generated by $I = \{0 \xrightarrow{u} 1, \{0\} \sqcup \{1\} \xrightarrow{v} 2, P \xrightarrow{w} 2\}$ we have that $[1] \hat{\otimes} I$ generates $\mathcal{C}_{Reedy}^{([1]_-)^{\mathrm{sp}}}$, by theorem 3.28. This gives us the set of maps

$$\{d_0 \hat{\otimes} u, d_0 \hat{\otimes} v, d_0 \hat{\otimes} w, d_1 \hat{\otimes} u, d_1 \hat{\otimes} v, d_1 \hat{\otimes} w\}.$$

To explain what it means for a map $f: X \to Y$ to have the lifting property against these cofibration we can use theorem 3.30, for which we need the matching objects. We observe from theorem 3.31 that $M_0 X = 1 = M_1 X$ since $([1]_-)_+$ has no non-identity maps, and the same applies to $Y$. Therefore, for $i \in I$ and $k = 0, 1$ we have $(d_k \hat{\otimes} i) \pitchfork f$ in $\mathbf{Cat}^{[1]_-^{\mathrm{sp}}}$ if and only if $i \pitchfork \hat{f}^k$, but $\hat{f}^k$ is either $X_0 \to Y_0$ or $X_1 \to Y_1$. Diagrammatically we have:

$$\begin{array}{ccc} \partial \mathfrak{L}_k \otimes b \coprod_{\partial \mathfrak{L}_k \otimes a} \mathfrak{L}_k \otimes a & \longrightarrow & X \\ d_k \hat{\otimes} i \downarrow & & \downarrow f \iff & i \downarrow \quad \nearrow \quad \downarrow f^k \\ \mathfrak{L}_k \otimes b & \longrightarrow & Y & b \longrightarrow Y_k \end{array}$$

Specializing to $Y = 1$, it gives us an idea of how types are introduced:

$$\begin{array}{ccc} 0 & \longrightarrow & X_k \\ u \downarrow & & \downarrow \\ 1 & & \end{array} \qquad \begin{array}{ccc} \{0\} \sqcup \{1\} & \longrightarrow & X_k \\ v \downarrow & & \downarrow \\ 2 & & \end{array} \qquad \begin{array}{ccc} P & \longrightarrow & X_k \\ w \downarrow & & \downarrow \\ 2 & & \end{array}$$

for $k = 0, 1$. This means that we introduce objects, arrows between two objects and equality between arrows to $X_0$ or $X_1$. This indicates that corresponding generating cofibration produce the following type axioms:

$$\begin{aligned} \vdash X_0 \text{ Type} & a, b: X_0 \vdash X_0(a, b) \text{ Type} & a, b: X_0, f, g: X_0(a, b) \vdash f =_{X_0} g \text{ Type} \\ \vdash X_1 \text{ Type} & a, b: X_k \vdash X_k(a, b) \text{ Type} & a, b: X_1, f, g: X_k(a, b) \vdash f =_{X_k} g \text{ Type} \end{aligned}$$

and we introduce the operation symbol for the functor as an operation

$$a: X_0 \vdash Fa: X_1 \qquad f: X_0(a, b) \vdash Ff: X_1(Fa, Fb)$$

On top of it, we add the usual axioms that ensure we have the expected behaviour with respect to the identity and composition operations. Let us call denote this language by $\mathbb{L}^{Fun}$.

Now we examine the language for the other model structure.

53

**Proposition 3.38.** *The Reedy model structure on $\mathcal{C}_{Reedy}^{([1]_+)^{\mathrm{op}}}$ coincides with the injective model structure. In particular, weak equivalences and cofibrations are the level-wise weak equivalences and cofibrations in $\mathcal{C}$.*

*Proof.* The result is folklore. $\square$

We find that fibrant objects are those such that $X_0 \to X_1$ is an isofibration. Therefore, the language in this case refers to isofibrations. Again, this model structure has generating cofibrations

$$\{d_0 \hat{\otimes} u, d_0 \hat{\otimes} v, d_0 \hat{\otimes} w, d_1 \hat{\otimes} u, d_1 \hat{\otimes} v, d_1 \hat{\otimes} w\}.$$

Next, observe that $\partial \updownarrow_0 = 0$ and $\partial \updownarrow_1 = \updownarrow_0$. We have the maps $d_0 : 0 \to \updownarrow_0$ and $d_1 : \updownarrow_0 \to \updownarrow_1$. Therefore, if $i : a \to b \in I$, then this give us the following cofibrations

- $\updownarrow_0 \otimes a \to \updownarrow_0 \otimes b$,
- $\updownarrow_1 \otimes a \coprod_{\updownarrow_0 \otimes a} \updownarrow_0 \otimes b \to \updownarrow_1 \otimes b$.

The map $\updownarrow_0 \otimes a \to \updownarrow_0 \otimes b$ for $i \in I$ corresponds to the following type introduction:

$$\vdash X_0 \text{ Type} \quad x, y : X_0 \vdash X_0(x, y) \text{ Type} \quad x, y : X_0, f, g : X_0(x, y) \vdash f =_{X_0} g \text{ Type}$$

which we can think of as a category. The analysis of the second map is more intricate. Let us denote the evaluation of the representables by $\updownarrow_{k0}$ and $\updownarrow_{k1}$ for $k = 0, 1$, and for simplicity we keep the '$\otimes$' symbol. Evaluating the cofibration $\updownarrow_1 \otimes a \coprod_{\updownarrow_0 \otimes a} \updownarrow_0 \otimes b \to \updownarrow_1 \otimes b$ at $[1]_+^\mathrm{op}$ give us the square,

$$\begin{array}{ccc} \updownarrow_{11} \otimes a \coprod_{\updownarrow_{10} \otimes a} \updownarrow_{10} \otimes b & \longrightarrow & \updownarrow_{01} \otimes a \coprod_{\updownarrow_{00} \otimes a} \updownarrow_{00} \otimes b \\ \updownarrow & & \updownarrow \\ \updownarrow_{11} \otimes b & \longrightarrow & \updownarrow_{01} \otimes b, \end{array}$$

where the horizontal arrows are induced by the diagram $[1]_+^\mathrm{op}$. This simplifies to

$$\begin{array}{ccc} a & \longrightarrow & a \coprod_a b \\ \updownarrow & & \updownarrow \\ b & \longrightarrow & b, \end{array}$$

54

which we now compute for $i \in I$, so the pictures take the following form:

![img-10.jpeg](img-10.jpeg)

![img-11.jpeg](img-11.jpeg)

![img-12.jpeg](img-12.jpeg)

From the above we deduce that the type axioms introduced by these cofibrations take, respectively, the following form:

$$x : X_0 \vdash X_1(x) \text{ Type},$$

$$x, y : X_0, f : X_0(x, y), a : X_1(x), b : X_1(y) \vdash X_1(a, b, f) \text{ Type},$$

$$x, y : X_0, f : X_0(x, y), a : X_1(x), b : X_1(y), j, k : X_1(a, b, f) \vdash j =_{X_1(a, b, f)} k \text{ Type}.$$

Unlike the language for functors $\mathbb{L}^{Fun}$, here we do not need a symbol for $F : X_0 \to X_1$. We denote this language for isofibrations as $\mathbb{L}^{Iso}$.

For the observation below, it will be useful to remember that given a functor $F : X \to Y$, an arrow $f : x \to y \in X$ is cartesian if for any $h : x' \to y$ and $w : F(x') \to F(x)$ with $F(f) \circ w = F(h)$, there exists a unique $u : x' \to x$ such that $f \circ u = h$. The following diagram illustrates this definition:

![img-13.jpeg](img-13.jpeg)

A Grothendieck fibration is a functor $F : X \to Y$ such that for any $y \in Y$ and $f : a \to F(y)$, there exists a cartesian arrow $\phi_f : f^*y \to y$ such that $F(\phi_f) = f$. The functor $F : X \to Y$ is a Street fibration if for any $y \in Y$ and $f : a \to F(y)$, there exists a cartesian arrow $\hat{f} : e \to y$ and an isomorphism $F(e) \cong a$ that makes the resulting triangle commutative.

Remark 3.39. It is a classical result that a Grothendieck fibration is the same as a Street fibration which is also an isofibration. On the one hand, note that a Grothendieck fibration can be written in the language $\mathbb{L}^{Iso}$ of isofibrations, but not in $\mathbb{L}^{Fun}$ of functors since it contains an equality between objects,

55

such equality is salvaged in $\mathbb{L}^{Iso}$ thanks to the dependencies. On the other hand, a Street fibration is a formula in $\mathbb{L}^{Fun}$. We also know that the two Reedy model structures on the category $\mathbf{Cat}^{[1]}$ are Quillen equivalent. The above result can also be automatically obtained as an elementary application of $4^{th}$ invariance theorem, whose proof is the heart of the next section.

## 4 Language invariance under Quillen equivalences

### 4.1 The third and fourth invariance theorem

The main goal of this section is to show two more invariance properties of the first order language from section 2.4, that we can phrase informally$^4$ as:

1. $3^{rd}$ invariance theorem: If two cofibrant objects $X$ and $Y$ are equivalent, then any formula in context $X$ can be translated into a formula in context $Y$.
2. $4^{th}$ invariance theorem: If two (weak) model categories $\mathcal{M}$ and $\mathcal{N}$ are Quillen equivalent, then any formula in the language of $\mathcal{M}$ can be translated into a formula in the language of $\mathcal{N}$.

These “translations” are equivalent to the original formula in the sense that they are interpreted in the same way in any fibrant model, but they might not be equivalent in the more syntactic sense introduced in theorem 2.10. More precisely, we introduce the following equivalence relation on formulas:

**Definition 4.1.** Let $A$ be a cofibrant object of $\mathcal{M}$. Two formulas $\phi, \psi \in \mathbb{L}^M_\lambda(A)$ are said to be *semantically equivalent* if for all fibrant objects $X \in \mathcal{M}$ we have $|\phi|_X = |\psi|_X$. In this situation we write $\phi \approx \psi$.

We define $h\mathbb{L}^M_\lambda(A)$ to be the quotient of $\mathbb{L}^M_\lambda(A)$ by the relation $\approx$. We easily check that this is still a Boolean algebra.

By definition of $\approx$ we have that for $\phi, \psi \in \mathbb{L}^M_\lambda(\Gamma)$, $\phi \approx \psi$ if and only if all maps $v : \Gamma \to X$ with $X$ fibrant

$$\Gamma \vdash \phi(v) \Leftrightarrow \Gamma \vdash \psi(v).$$

We can now state our theorems.

### Theorem 4.2.

---$^4$The precise statement is just below as theorem 4.2.

56

- • $3^{rd}$ **invariance theorem:** Let $A, B \in \mathcal{M}$ two cofibrant objects of a weak Quillen model category $\mathcal{M}$ and $f: A \to B$ a weak equivalence between them. Then the map $f^*: \mathbb{L}_\lambda(B) \to \mathbb{L}_\lambda(A)$ induces a bijection

$$h\mathbb{L}_\lambda(B) \simeq h\mathbb{L}_\lambda(A).$$

- • $4^{th}$ **invariance theorem:** If $F: \mathcal{M} \to \mathcal{N}$ is a left Quillen equivalence between two weak model categories, then for any cofibrant object $A \in \mathcal{M}$ the induced map

$$h\mathbb{L}F_A: h\mathbb{L}_\lambda^{\mathcal{M}}(A) \to h\mathbb{L}_\lambda^{\mathcal{N}}(FA)$$

from theorem 4.5 is an isomorphism.

**Remark 4.3.** Note that if $F: \mathcal{M} \rightleftarrows \mathcal{N}: G$ a Quillen equivalence between weak model categories and $B$ is a cofibrant object of $\mathcal{N}$ which is not of the form $F(A)$ for $A \in \mathcal{M}$, then one can still use the $4^{th}$ invariance theorem to transfer a formula in $h\mathbb{L}(B)$ to a formula in $\mathcal{M}$. We do this by first finding an object of the form $F(A)$ which is homotopically equivalent to $B$, which is always possible as $F$ is a Quillen equivalence, and then transferring our formula $\phi \in h\mathbb{L}(B)$ to a formula in $h\mathbb{L}(F(A))$ using the $3^{rd}$ invariance theorem.

**Observation 4.4.** For any cofibrant object $\Gamma \in \mathcal{M}$, $\phi, \psi \in \mathbb{L}_\lambda^{\mathcal{M}}(\Gamma)$ we defined $\phi \approx \psi$ if and only if $|\phi|_X = |\psi|_X$ for all fibrant objects. However, note that if we take a cofibrant replacement $X^{\mathrm{COF}}$ of $X$, then by theorem 2.38 ($2^{nd}$ invariance theorem) we have, $X \vdash \phi(fv)$ if and only if $X^{\mathrm{COF}} \vdash \phi(v)$, where $f: X^{\mathrm{COF}} \xrightarrow{\sim} X$ and $v: \Gamma \to X^{\mathrm{COF}}$.

Therefore, when testing the relation $\approx$, it is enough to use bifibrant objects. More precisely, define $\phi \approx_b \psi$ if $|\phi|_X = |\psi|_X$ for any bifibrant object $X$. Then

$$\phi \approx \psi \text{ if and only if } \phi \approx_b \psi.$$

We now explain the construction of the map $h\mathbb{L}F_A: h\mathbb{L}_\lambda^{\mathcal{M}}(A) \to h\mathbb{L}_\lambda^{\mathcal{N}}(FA)$ mentioned in the $4^{th}$ invariance theorem.

**Construction 4.5.** The map $h\mathbb{L}F_A$ in the $4^{th}$ invariance theorem is the map coming from $\mathbb{L}F_A: \mathbb{L}_\lambda^{\mathcal{M}}(A) \to \mathbb{L}_\lambda^{\mathcal{N}}(FA)$ constructed in theorem 2.40. It just comes from the fact that $\mathbb{L}_\lambda^{\mathcal{M}}$ is the initial boolean algebra. Recall that it satisfies the formula:

$$G(X) \vdash \phi(v) \Leftrightarrow X \vdash F(\phi)(\tilde{v}).$$

57

for any object $X \in \mathcal{N}$, and cofibrant object $C \in \mathcal{M}$, any map $v : C \to G(X)$ corresponding to $\tilde{v} : F(C) \to X$, and $\phi \in \mathbb{L}_{\lambda}^{\mathcal{M}}(C)$.

This immediately imply the following proposition that shows that the map $h\mathbb{L}_A$ mentioned in the $4^{th}$ invariance theorem is well-defined.

**Proposition 4.6.** *For any Quillen adjunction $F : \mathcal{M} \leftrightarrows \mathcal{N} : G$ and $A \in \mathcal{M}$ a cofibrant object, the map $F : \mathbb{L}_{\lambda}(A) \to \mathbb{L}_{\lambda}(FA)$ is compatible with the relation $\approx$ and induces a morphism of $\lambda$-boolean algebras*

$$F : h\mathbb{L}_{\lambda}(A) \to h\mathbb{L}_{\lambda}(FA).$$

*Proof.* If $\phi$ and $\psi$ are semantically equivalent formulas in $\mathbb{L}_{\lambda}(A)$, then for any fibrant object $X \in \mathcal{N}$, and a map $\tilde{v} : FA \to X$ corresponding to $v : A \to GX$ we have

$$X \vdash F(\phi)(\tilde{v}) \Leftrightarrow G(X) \vdash \phi(v) \Leftrightarrow G(X) \vdash \psi(v) \Leftrightarrow X \vdash F(\psi)(\tilde{v})$$

which shows that $F(\phi) \approx F(\psi)$ and concludes the proof. $\square$

We are now ready prove the $3^{rd}$ invariance theorem. We start with a special case:

**Lemma 4.7.** *Let $\Gamma, \Gamma' \in \mathcal{M}^{\mathrm{COF}}$ and $\pi : \Gamma \xrightarrow{\sim} \Gamma'$ be a core trivial cofibration, then the induced map $h\mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma) \to h\mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma')$ is an isomorphism of $\lambda$-boolean algebras.*

*Proof.* Assume that $\pi : \Gamma \xrightarrow{\sim} \Gamma'$ is a core trivial cofibration. Since to define the language of $\mathcal{M}$ we take the $\kappa$-clan $(\mathcal{M}^{\mathrm{COF}})^{\mathrm{op}}$, when constructing the language we get a covariant functor $\mathcal{M}^{\mathrm{COF}} \to \mathbf{Bool}_{\lambda}$. Therefore, we obtain a map $\pi^* : \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma) \to \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma')$ and its left adjoint $\exists_{\pi} : \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma') \to \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma)$, which furthermore descends to the adjoint pair $h\exists_{\pi} : h\mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma') \rightleftarrows h\mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma) : h\pi^*$ between the $\lambda$-boolean algebras.

We claim that $h\exists_{\pi}$ is the inverse for $h\pi^*$. It is enough to show that for any $\phi : \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma)$ and $\psi \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma')$ we have $\exists_{\pi}\pi^*(\phi) \approx \phi$ and $\pi^*\exists_{\pi}(\psi) \approx \psi$.

Firstly, let $X \in \mathcal{M}^{\mathrm{FIB}}$ be a fibrant object and $x : \Gamma \to X$. Note that $x \in |\exists_{\pi}\psi|_X \subseteq \mathrm{hom}_{\mathcal{M}}(\Gamma, X)$ if and only if there exists $x' : \Gamma' \to X$ such that $x' \in |\psi|_X \subseteq \mathrm{hom}_{\mathcal{M}}(\Gamma', X)$ and that makes the following triangle commutative:

![img-14.jpeg](img-14.jpeg)

58

Since $X$ is fibrant, the map $x'$ always exists. Such $x'$ is not necessarily unique, however, in a situation in which we have two arrows

![img-15.jpeg](img-15.jpeg)

that make the triangle commutative, then using that $\pi$ is a trivial cofibration we see that $y$ and $z$ are homotopic. By the first invariant theorem (theorem 2.38) we have $y \in |\psi|_X$ if and only if $z \in |\psi|_X$. Therefore, the existence of $x' \in |\psi|_X$ is independent of choices.

From here, the result is immediate: $x \in |\exists_\pi \pi^* \phi|_X$ if and only if there exists $x' : \Gamma' \to X$ such that $x'\pi = x$ such that $X \vdash \phi(\pi^* x')$ i.e., if and only $x \in |\phi|_X$. This shows that $|\exists_\pi \pi^* \phi|_X = |\phi|_X$ for any fibrant object. Conversely, for $y : \Gamma' \to X$ we have $y \in |\pi^* \exists_\pi \psi|$ if and only if there exists $z : \Gamma' \to X$ such that $z\pi = y\pi$ and $X \vdash \psi(z)$, which is equivalent to $y \in |\psi|_X$, showing that $|\exists_\pi \pi^* \psi|_X = |\psi|_X$. This concludes the proof that $h\exists_\pi$ is the inverse for $h\pi^*$.

We are now ready to prove the $3^{rd}$ invariance theorem:

Proof of the $3^{rd}$ invariance theorem: The idea is to use theorem 4.7 together with Brown's factorization lemma from [Bro73], or rather an adaptation of it to the setting of weak model structures that we present now. If $f : X \to Y$ is a weak equivalence between cofibrant objects in a weak model category. In general we cannot form a cylinder object for $X$, but instead a "weak cylinder" for $X$, that is a diagram:

![img-16.jpeg](img-16.jpeg)

we then take the pushout of this whole diagram by the map $X \to Y$, using either of the two canonical maps $X \to X \coprod X$:

![img-17.jpeg](img-17.jpeg)

59

and by precomposing with the coproduct inclusion $X \rightarrow X \coprod Y$, we obtain a diagram:

![img-18.jpeg](img-18.jpeg)

three of the four maps here are weak equivalence, so it follows by the 2-out-of-3 property that the left vertical map is also a weak equivalence, hence a trivial cofibration. Applying $h\mathbb{L}$ we obtain a diagram:

![img-19.jpeg](img-19.jpeg)

The two vertical arrows are bijections because of theorem 4.7, so in order to show that $f^*$ is a bijection, it is enough to show that the bottom map is a bijection. This bottom horizontal map fits into a commutative diagram:

![img-20.jpeg](img-20.jpeg)

where the arrow $Y \rightarrow IX \coprod_X Y$ is obtained as the pushout:

![img-21.jpeg](img-21.jpeg)

Applying the $h\mathbb{L}$ functor, we get a triangle:

![img-22.jpeg](img-22.jpeg)

the two vertical and diagonal arrows are bijections because of theorem 4.7, and so the third, horizontal, arrows also is, which concludes the proof.

60

We can also show the injectivity part of the $4^{th}$ invariance theorem.

**Lemma 4.8.** *Let $F : \mathcal{M} \rightleftarrows \mathcal{N} : G$ a Quillen equivalence. Then, for any cofibrant object $\Gamma \in \mathcal{M}$, the induced map $h\mathbb{L}F_\Gamma : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \rightarrow h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$ is injective.*

*Proof.* Let $\phi$ and $\psi$ be formulas in $\mathbb{L}_\lambda^\mathcal{M}(\Gamma)$ such that $F(\phi) \approx F(\psi)$ *i.e.*, $F(\phi)$ and $F(\psi)$ are equal in $h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$. We must show that $\psi \approx \phi$. Alternatively, by theorem 4.4 we can show that $\psi \approx_b \phi$. The Quillen equivalence induces an equivalence between homotopy categories $Ho(G) : Ho(\mathcal{N}^{\mathrm{BiF}}) \rightarrow Ho(\mathcal{M}^{\mathrm{BiF}})$. Hence, there is a bifibrant object $Y \in \mathcal{N}$ such that $GY$ is isomorphic to $X$ in $Ho(\mathcal{M}^{\mathrm{BiF}})$. Given any $x : \Gamma \rightarrow X$, denote by $y : \Gamma \rightarrow GY$ any map such that the following triangle

![img-23.jpeg](img-23.jpeg)

commutes in $\mathrm{Ho}(\mathcal{M}^{\mathrm{BiF}})$. Lastly, let $y' : F\Gamma \rightarrow Y$ the transpose of $y$ via the Quillen adjunction. It follows from the first invariance theorem 2.38 that $X \vdash \phi(x)$ if and only if $GY \vdash \phi(y)$. From theorem 4.6, this is equivalent to $Y \vdash F(\psi)(y')$. By assumption $F(\phi) \approx F(\psi)$, so $Y \vdash F(\psi)(y')$. Again, this is $GY \vdash \psi(y)$ and $X \vdash \psi(x)$. This establishes the equality $|\phi|_X = |\psi|_X$ for all $X \in \mathcal{M}$ bifibrant, which proves $\psi \approx_b \phi$, and hence $\psi \approx \phi$. This concludes the proof of the statement. $\square$

We now explain our strategy to prove the rest of theorem 4.2, that is the surjectivity part of the $4^{th}$ invariance theorem.

In [Bar19], Reid Barton constructs a model 2-category structure on the 2-category of simplicial model categories. The trivial fibrations satisfy a property, that Barton called “extensible” (see theorem 4.9). In this section, we introduce a version of these in the non-enriched case, and we call those functors *Barton trivial fibrations*. In section 4.2 we show that the result holds for Barton trivial fibrations. After that, the idea is to use the same strategy as for the proof of the $3^{rd}$ invariance theorem based on this modified Brown factorization lemma to conclude the result holds for general Quillen equivalences. We could do this immediately for combinatorial simplicial model categories using Brown’s lemma in Barton’s model structure, but for the general case we give a direct proof of the existence of the appropriate diagram which is inspired by how it would be done in Barton’s model structure, but without relying on it directly. This is done in theorem 4.52 using section 4.3.

61

## 4.2 Invariance along Barton trivial fibrations

In this section we introduce a class of left Quillen functor that we call *Barton trivial fibrations* as they are essentially a non-simplicial version of the trivial fibrations of the model structure constructed by Barton in [Bar19], and we establish that theorem 4.2 holds for these particular functors.

**Definition 4.9.** Let $F : \mathcal{C} \to \mathcal{D}$ a morphism between $\kappa$-coclans. We say that $F$ is *extensible* if for every object in $X \in \mathcal{C}$ and for any cofibration $g : FX \hookrightarrow Y \in \mathcal{D}$ there exists $f : X \hookrightarrow Z$ and an isomorphism $F(Z) \cong Y$ making the obvious triangle commutative.

Dually, $F : \mathcal{C} \to \mathcal{D}$ a morphism between $\kappa$-clans is *extensible* if the induced map of $\kappa$-coclans $F^{\mathrm{op}} : \mathcal{C}^{\mathrm{op}} \to \mathcal{D}^{\mathrm{op}}$ is extensible.

In our setting, a functor $F : \mathcal{M} \to \mathcal{N}$ between weak model categories will be called extensible if the cocclan morphism $F : \mathcal{M}^{\mathrm{COF}} \to \mathcal{N}^{\mathrm{COF}}$ is extensible.

The terminology *extensible* in the definition above for both clans and cocclans, instead of “extensible” and “co-extensible”, is simply because it is always clear whether it refers to cofibrations or fibrations. This is because, for example, when considering a morphism between clans the relevant structure that ought to be preserved is that related to fibrations. The name extensible from theorem 4.9 is adapted from Reid Barton’s PhD thesis [Bar19, Definition 8.3.1].

**Definition 4.10.** A left Quillen functor $F : \mathcal{M} \to \mathcal{N}$ between weak model categories is called *weakly conservative* if for any core cofibration $x \hookrightarrow y \in \mathcal{M}^{\mathrm{COF}}$ such that $h : Fx \xrightarrow{\sim} Fy$ is a trivial cofibration, the map $x \hookrightarrow y$ is a trivial cofibration.

The ‘weakly’ part in the previous definition does not come from weak model categories, but rather from the fact that core trivial cofibrations are weak equivalences.

**Definition 4.11.** Let $F : \mathcal{M} \to \mathcal{N}$ a left Quillen functor between weak model categories. We say that $F$ is a *Barton trivial fibration* if it is extensible as a morphism between of the cocclans $\mathcal{M}^{\mathrm{COF}}$ and $\mathcal{N}^{\mathrm{COF}}$ and weakly conservative.

*Remark 4.12.* Barton trivial fibrations which are also simplicial Quillen functors between combinatorial simplicial model categories are exactly the trivial fibrations in [Bar19] in the model 2-category of pre-model categories. As the reader might anticipate, the notion of fibration between (simplicial) model categories exists as well, but we will make no use of it.

62

The reason why we isolate the two properties in the definition above is because the first one is well-behaved with respect to the language we constructed, see theorem 4.15. In theorem 4.14, we justify the “trivial” part of theorem 4.11 by showing that an extensible and weakly conservative left Quillen functor is a left Quillen equivalence, to do this we need an intermediate result.

**Lemma 4.13.** *Let be $F : \mathcal{M} \to \mathcal{N}$ a left Quillen functor which is extensible and weakly conservative. Suppose there are diagrams*

$$\begin{array}{c c} A \xrightarrow{f} C & FA \xrightarrow{Ff} FC \\ i \Big\downarrow & Fi \Big\downarrow \qquad v \Big\downarrow \sim \\ B & FB \xrightarrow{u} Z \end{array}$$

in $\mathcal{M}$ and $\mathcal{N}$, respectively, where $C \in \mathcal{M}^{\mathrm{BIF}}$ and $Z \in \mathcal{N}^{\mathrm{BIF}}$ are bifibrant and the right square is commutative. Then, there exists $g : B \to C$ that makes the triangle commutative and such that in the diagram

$$\begin{array}{c} FA \xrightarrow{Ff} FC \\ Fi \Big\downarrow \qquad \nearrow Fg \nearrow v \Big\downarrow \sim \\ FB \xrightarrow{u} Z \end{array}$$

the lower triangle commutes up to homotopy relative to $FA$.

*Proof.* Since $F$ is left Quillen then we have $F(B \coprod_A C) \cong FB \coprod_{FA} FC$ and is cofibrant. Up to this isomorphism, we factor the map $F(B \coprod_A C) \to Z$ as $F(B \coprod_A C) \hookrightarrow Y \xrightarrow{\sim} Z$. Since $F$ is extensible we can lift this cofibration to a cofibration $B \coprod_A C \hookrightarrow D$ together with the isomorphism $FD \cong Y$ making the resulting triangle commutative, which also implies that $FD$ is bifibrant since $Y$ is. Furthermore, this produces a commutative diagram as on the left,

$$\begin{array}{c c c} A \xrightarrow{f} C & FC \xrightarrow{\sim} Z \\ i \Big\downarrow & \Big\downarrow \searrow & \searrow \\ B \xrightarrow{} B \coprod_A C \xrightarrow{h} F & FD \xrightarrow{\sim} Y \\ k & \searrow \searrow & \searrow \\ & D \end{array}$$

while the diagram on the right is the result of applying $F$, we introduce the name $\rho : FD \xrightarrow{\sim} Z$ for the evident resulting trivial fibration. We can

63

use the 2-out-of-3 property of weak equivalences between cofibrant-fibrant objects to conclude that $FC \hookrightarrow Y$ is a weak equivalence, and hence a trivial cofibration. Since $F$ is weakly conservative, the map $C \hookrightarrow D$ must be a weak equivalence too. Using that $C$ is bifibrant we can obtain a dashed arrow which is a homotopy inverse of $h$

$$\begin{array}{c} A \xrightarrow{f} C \xrightarrow{Id} C \\ i \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \xrightarrow{k} D, \end{array}$$

we can take $g := rk$ to be a diagonal filler of the square. Observe that when we apply $F$ to the resulting diagram, it gives us the square and the diagonal in the diagram

$$\begin{array}{c} FA \xrightarrow{Ff} FC \\ Fi \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ FB \xrightarrow{Fk} FD \xrightarrow{\sim} Z \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad u \end{array}$$

where a priori the outer triangle involving $u$ is not commutative. However, we can realize this diagram in the homotopy category $\mathrm{Ho}(FA/\mathcal{N})$. So working in the homotopy category we have $hr = Id$ and $FhFr = Id$. By construction, we also get $Fg = FrFk$, therefore $FhFg = FhFrFk = Fk$ in the homotopy category, and $\rho : FD \xrightarrow{\sim} Z$ becoming an isomorphism implies $vFg = u$ up to homotopy relative to $FA$. $\square$

**Corollary 4.14.** *Let $F : \mathcal{M} \to \mathcal{N}$ a left Quillen functor between weak model categories. Assume that $F : \mathcal{M}^{\mathrm{COF}} \to \mathcal{N}^{\mathrm{COF}}$ is extensible and weakly conservative, then $F$ is a left Quillen equivalence.*

*Proof.* We show directly that $F$ induces an equivalence of categories between the homotopy categories.

Assume that $X \in \mathcal{N}^{\mathrm{COF}}$ is cofibrant. Then we can use that $F$ is extensible for the cofibration $0 \hookrightarrow X$ to obtain a cofibrant object $A \in \mathcal{M}^{\mathrm{COF}}$ and an isomorphism $FA \cong X \in \mathcal{N}$. This shows that the induced functor is essentially surjective.

We now show that for $\mathrm{Ho}(\mathcal{M}) \to \mathrm{Ho}(\mathcal{N})$ is full. Let $B, C \in \mathcal{M}^{\mathrm{COF}}$ cofibrant objects. We could take a fibrant replacement $C^{\mathrm{FIB}}$ and use this instead, so we can freely assume that $C$ is bifibrant. A map $FB \to FC \in$

64

$\mathrm{Ho}(\mathcal{N})$ can be represented by a cospan

$$FB \to (FC)^{\mathrm{FIB}} \stackrel{\sim}{\leftarrow} FC \in \mathcal{N}.$$

Therefore, we can use theorem 4.13 to find a map $B \to C$ in $\mathrm{Ho}(\mathcal{M})$ which is in the preimage.

Lastly, we see that the induced functor is faithful. Let $A, C \in \mathcal{M}^{\mathrm{COF}}$ cofibrant and two maps $f, g : A \to C \in \mathcal{M}$ which become equal in $\mathrm{Ho}(\mathcal{N})$ under the functor induced by $F$. This is just saying that the maps $F\bar{f}, F\bar{g} : FA \to F(C^{\mathrm{FIB}})$ are homotopic where $\bar{f}, \bar{g} : A \to C^{\mathrm{FIB}}$ are maps in $\mathcal{M}$. It will be enough to show that $\bar{f}$ and $\bar{g}$ are homotopic *i.e.*, there is a diagonal filler for the diagram

$$\begin{array}{c} A \coprod A \xrightarrow{(\bar{f}, \bar{g})} C^{\mathrm{FIB}} \\ \Big\downarrow \\ IA \end{array}$$

where $IA$ is a weak cylinder object for $A$. Since $F$ is a left Quillen functor, we can assume that cylinders are preserved. Furthermore, homotopies are independent of the choice of cylinders. We can express the homotopy between of $F\bar{f}$ and $F\bar{g}$ in $\mathcal{N}$ as the commutative square

$$\begin{array}{c} F(A \coprod A) \xrightarrow{(F\bar{f}, F\bar{g})} F(B^{\mathrm{FIB}}) \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F(IA) \xrightarrow{h} F(B^{\mathrm{FIB}})^{\mathrm{FIB}}, \end{array}$$

where $h$ is the homotopy, and the fibrant replacement $F(C^{\mathrm{FIB}})^{\mathrm{FIB}}$ is necessary since $F(C^{\mathrm{FIB}})$ is not fibrant as $F$ is only left Quillen. The assumptions of theorem 4.13 are now satisfied, so this produces a diagonal as on the left whose image fits on the right square up to homotopy:

$$\begin{array}{c} A \coprod A \xrightarrow{(\bar{f}, \bar{g})} C^{\mathrm{FIB}} \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ IA \end{array}$$

$$\begin{array}{c} F(A \coprod A) \xrightarrow{(F\bar{f}, F\bar{g})} F(C^{\mathrm{FIB}}) \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F(IA) \xrightarrow{h} F(C^{\mathrm{FIB}})^{\mathrm{FIB}} \end{array}$$

The above shows that $\mathrm{Ho}(\mathcal{M}) \to \mathrm{Ho}(\mathcal{N})$ is faithful, concluding the proof that $F$ is a left Quillen equivalence. $\square$

65

We now return to show the $4^{th}$ invariance theorem for the case in which the functor is a Barton trivial fibration. First, we observe that extensible functors always induce a surjection between the languages of clans.

**Lemma 4.15.** *Let $F : \mathcal{M} \to \mathcal{N}$ be an extensible morphism between $\kappa$-clans and $\Gamma \in \mathcal{M}$. Then, any formula $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(F\Gamma)$ is the image under $F$ of a formula $\Phi_0 \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma)$.*

*Proof.* Since every $\kappa$-clan is of the form $\mathbb{C}_T$ for some $T$ generalized $\kappa$-algebraic theory, it is enough to show the result is valid for the syntactic definition of language as in theorem 2.1. We prove by induction on formulas $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(\Delta)$ that, given any context $\Gamma$ and $f : \Delta \cong F(\Gamma)$, there is a formula $\Phi_0 \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma)$ such that $f^*(F\Phi_0) = \Phi$.

1. When $\Phi = \top$ or $\Phi = \bot$, then this can clearly be lifted to $\top$ and $\bot$.
2. If $\Phi = \neg\Psi$ or $\Phi = \bigvee_{i \in I} \Psi_i$ or $\Phi = \bigwedge_{i \in I} \Psi_i$ then it is also clear that $\Phi$ can be lifted. Indeed, we can simply use the inductive hypothesis to lift each $\Psi_i$ and then use the boolean algebra structure to conclude.
3. Suppose that $\Phi$ is of the form $\exists_{\pi}\Psi$ or $\forall_{\pi}\Psi$ for some fibration $\pi : \Gamma' \twoheadrightarrow F(\Gamma)$. The formula $\Psi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(\Gamma')$, so $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(F\Gamma)$. Furthermore, we assume that $\Psi$ can be lifted. Since $F$ is extensible, there is a lift $\bar{\pi} : \bar{\Gamma}' \to \Gamma \in \mathcal{M}$ of $\pi : \Gamma' \twoheadrightarrow F(\Gamma)$, which comes with an isomorphism $g : \Gamma' \cong F(\bar{\Gamma}')$ such that the following triangle commutes

$$\begin{array}{c} \Gamma' \xrightarrow{\pi} F(\Gamma) \\ \cong \Biggl\downarrow g \quad \nearrow \\ F(\bar{\Gamma}'). \end{array}$$

Therefore, we get a commutative square as in the left below, and at the level of languages as on the right below

$$\begin{array}{ccc} \Gamma' \xrightarrow{\pi'} \Delta & & \mathbb{L}_{\lambda}^{\mathcal{N}}(F(\bar{\Gamma}')) \xrightarrow{\exists_{\pi'}} \mathbb{L}_{\lambda}^{\mathcal{N}}(F(\Gamma)) \\ \cong \Biggl\downarrow g \quad f \Biggl\downarrow \cong & & g^* \Biggl\downarrow \quad \Biggl\downarrow f^* \\ F(\bar{\Gamma}') \xrightarrow[F(\bar{\pi})]{} F(\Gamma) & & \mathbb{L}_{\lambda}^{\mathcal{N}}(\Gamma') \xrightarrow{\exists_{F(\bar{\pi})}} \mathbb{L}_{\lambda}^{\mathcal{N}}(\Delta). \end{array}$$

By assumption $\psi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(\Gamma')$ can be lifted. Hence, there is a formula $\Psi_0 \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\bar{\Gamma}')$ such that $g^*(F\Psi_0) = \Psi$. Using the right hand square above, one can see that $\exists_{\bar{\pi}}\Psi_0$ is a lift for $\Phi$.

66

This shows that the map is surjective.

As an immediate consequence of theorem 4.15, we can establish the $4^{th}$ invariance theorem in the special case where $F : \mathcal{M} \to \mathcal{N}$ is a Barton trivial fibration. We will use this result to be able to establish $4^{th}$ invariance theorem for the general case later on.

**Theorem 4.16.** *Let $F : \mathcal{M} \to \mathcal{N}$ be a Barton trivial fibration between weak model categories. Then for any cofibrant $\Gamma \in \mathcal{M}$ the induced map $h\mathbb{L}F_A : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \to h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$ is an isomorphism.*

*Proof.* By the previous theorem 4.8 we know that $h\mathbb{L}F_\Gamma : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \to h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$ is injective. Next we can use theorem 4.15 by observing that this surjectivity also descends to the level of $h\mathbb{L}F_\Gamma : h\mathbb{L}_\lambda^\mathcal{M}(\Gamma) \to h\mathbb{L}_\lambda^\mathcal{N}(F\Gamma)$. $\square$

Since our next goal is to prove $4^{th}$ invariance theorem, with theorem 4.16 at hand, we simply need to reduce our problem to the case in which we have Barton trivial fibrations. The constructions to come are essentially the necessary steps for this reduction process.

### 4.3 Path objects for weak model categories

The next step is to build some sort of “path object” for (weak) model category so that we can emulate Brown Factorization lemma to factor a general Quillen equivalence into a retract of a Barton trivial fibration followed by a Barton fibration. Ideally, we would want for a model category $\mathcal{M}$, we would like to build a diagram of left Quillen functors

$$\mathcal{M} \to P\mathcal{M} \to \mathcal{M} \times \mathcal{M}$$

where the maps $P\mathcal{M} \to \mathcal{M}$ are Barton trivial fibrations, and then try to use it to follow the proof of Brown’s Factorization Lemma. Unfortunately, that is not going to be quite possible: we will not be able to construct a map $\mathcal{M} \to P\mathcal{M}$. Instead, similarly to the proof of the $3^{rd}$ invariance theorem, we will construct, a diagram of the form

$$\begin{array}{ccc} R\mathcal{M} & \longrightarrow & P\mathcal{M} \\ \downarrow^p & & \downarrow \\ \mathcal{M} & \longrightarrow & \mathcal{M} \times \mathcal{M} \end{array}$$

where the arrow $p$ is a Barton trivial fibration. This will turn out to be sufficient to build our desired Brown style factorization. The weak model

67

categories $RM$ and $PM$ will be constructed as certain category of functors $\mathcal{M}^J$ and $\mathcal{M}^I$, equipped with certain localization of the Reedy model structure. So we get a diagram

![img-24.jpeg](img-24.jpeg)

where the arrow on the left and the two maps $\mathcal{M}^I \rightarrow \mathcal{M}$ induced by the projections are Barton trivial fibrations. More precisely, the construction we do takes as input a left Quillen equivalence $F : \mathcal{M} \rightarrow \mathcal{N}$ between weak model categories and produces a diagram

![img-25.jpeg](img-25.jpeg)

where again the arrow on the left and the two maps $\mathcal{N}_F^I \rightarrow \mathcal{N}$ induced by the projections are Barton trivial fibrations. Hence, the first diagram is a particular case when $F = Id_{\mathcal{M}}$.

*Remark 4.17.* The core idea of the outline above is already present in the proof of the $3^{rd}$ invariance theorem. This can be seen as the analogue (or rather a dual) of the diagram (1) that appears in the proof of the $3^{rd}$ invariance theorem, and it will play the exact same role. In both cases, the idea is to obtain some sort of Brown factorization.

The bulk of the work lies in endowing the categories $\mathcal{M}^I$ and $\mathcal{M}^J$ with the correct weak model structures. This can be summarized as follows: We start with the Reedy weak model structure on the category $\mathcal{M}^J$, or $\mathcal{N}^I$, and perform a “right Bousfield localization” to obtain our desired models.

*Remark 4.18.* The weak model structure on $\mathcal{N}^I$ encodes a pair of objects $A, B$ in $\mathcal{N}$ with a “correspondence” between them; that is, a homotopy equivalence encoded by a cofibration $A \coprod B \rightarrow C$ where both maps $A \rightarrow C$ and $B \rightarrow C$ are trivial cofibrations. The weak model structure we obtain on $\mathcal{M}^J$ encodes objects $X$ in $\mathcal{M}$ equipped with a (weak) cylinder object, so that we can send such an object $X$ with a cylinder $IX$ to the correspondence $X \coprod X \rightarrow IX$.

68

### 4.3.1 Weak model for objects with weak cylinders

We start by fixing a weak model category $\mathcal{M}$ and let $J$ be the category

$$a \xrightarrow[j]{i} b \xrightarrow{k} c$$

such that $ki = kj$. Consider the degree function making $J$ into a direct category, $\deg(a) = 0$, $\deg(b) = 1$, $\deg(c) = 2$. Our first goal is to prove:

**Theorem 4.19.** *The category of diagrams $\mathcal{M}^J$ has a weak model structure where:*

1. *A map between diagrams $X \rightarrow Y$ is a cofibration if*

(a) *It is a Reedy cofibration,*
(b) $Y_a \sqcup_{X_a} X_c \xrightarrow{\sim} Y_c$ and $Y_b \sqcup_{X_b} X_c \xrightarrow{\sim} Y_c$ are trivial cofibrations in $\mathcal{M}$.

2. *Fibrations are level-wise fibrations.*

*Remark 4.20.* The theorem above make reference to Reedy cofibrations, therefore we must justify first that $\mathcal{M}^J$ carries the Reedy weak model structure. Fortunately, this has been addressed in theorem C.11.

*Notation 4.21.* For the sake of clarity, we denote by $\mathcal{M}^J_{Reedy}$ when referring to the Reedy weak model structure and $\mathcal{M}^J_{Loc}$ for the weak model structure of theorem 4.19. Of course, *a priori*, we have yet to prove that the latter is indeed a weak model structure. Therefore, whenever we say, for example, that a map $f : X \rightarrow Y$ is a cofibration we just mean that $f$ satisfies the corresponding condition of theorem 4.19.

We will justify that the following construction, which is simply the conditions of the theorem, is the correct one.

*Observation 4.22.* One can verify that in this new model structure, the core fibrations and core trivial cofibrations coincide with the ones in the Reedy weak model structure (see theorem 4.25).

The reader might suspect that this is not a fortuitous coincidence, these suspicions are well justified. As we mentioned, what we have done is a right Bousfield localization of a Reedy weak model structure on $\mathcal{M}^J$. Such localizations are studied in [Hen23] in the case when $\mathcal{M}$ is a combinatorial (accessible) weak model category. Due to the lack of a general theorem that justifies the existence of these localizations producing a weak model category, we verify all required conditions by hand.

69

We examine the class of cofibrations. For a diagram $X \in \mathcal{M}^J$, the latching objects are $L_a X = \emptyset$, $L_b X = X_a \sqcup X_a$ and $L_c X = X_b \sqcup_{X_a} X_b$. These are cofibrant in $\mathcal{M}$. Then a map $f : X \to Y$ being a cofibration means that $X_a \hookrightarrow Y_a$,

$$X_b \sqcup_{X_a \sqcup X_a} (Y_a \sqcup Y_a) \hookrightarrow Y_b \text{ and } X_c \sqcup_{(X_b \sqcup_{X_a} X_b)} (Y_b \sqcup_{Y_a} Y_b) \hookrightarrow Y_c$$

are cofibrations in $\mathcal{M}$, and additionally $Y_a \sqcup_{X_a} X_c \xrightarrow{\sim} Y_c$ and $Y_b \sqcup_{X_b} X_c \xrightarrow{\sim} Y_c$ are trivial cofibrations in $\mathcal{M}$.

Therefore, a diagram $Y \in \mathcal{M}^J$ is *cofibrant* if $Y_a$ is a cofibrant object in $\mathcal{M}$,

$$Y_a \sqcup Y_a \hookrightarrow Y_b \text{ and } Y_b \sqcup_{Y_a} Y_b \hookrightarrow Y_c$$

are cofibrations, and additionally $Y_a \xrightarrow{\sim} Y_c$ and $Y_b \xrightarrow{\sim} Y_c$ are trivial cofibrations. Spelling out the second Reedy condition gives us the following commutative diagram:

![img-26.jpeg](img-26.jpeg)

This says that both maps $Y_a \xrightarrow[Y_j]{Y_i} Y_b$ are cofibrations. We can use this on the following diagram

![img-27.jpeg](img-27.jpeg)

to conclude that $Y_b \hookrightarrow Y_c$ is a cofibration. Of course this is in principle not necessary since we also have $Y_b \xrightarrow{\sim} Y_c$ is a trivial cofibration, but the novel aspect is that this follows only from Reedy cofibrancy. We also have a trivial cofibration $Y_a \xrightarrow{\sim} Y_c$, by the two-out-of-three property the maps $Y_a \xrightarrow[Y_j]{Y_i} Y_b$ are trivial cofibrations. We collect the above in the following:

70

*Remark 4.23.* If $Y$ is cofibrant then we obtain the following diagram:

$$\begin{array}{ccc} Y_a \sqcup Y_a & \xrightarrow{\nabla} & Y_a \\ \downarrow & & \downarrow^\sim \\ Y_b & \xrightarrow{\sim} & Y_c. \end{array}$$

This is just to say that cofibrant diagrams of $\mathcal{M}_{Loc}^J$ encode objects of $\mathcal{M}$ for which a weak cylinder exists in the sense of theorem C.6.

We reiterate that our goal is to show that the category of diagrams $\mathcal{M}_{Loc}^J$ has a weak model structure on it, where the cofibrations are the ones as specified in theorem 4.19. We begin by showing the following lemmas which are expected results in the theory of right Bousfield localizations.

**Lemma 4.24.** *Let $X, Y \in \mathcal{M}_{Loc}^J$ cofibrant. Then, a map $X \to Y$ is a cofibration in $\mathcal{M}_{Loc}^J$ if and only if it is a cofibration in $\mathcal{M}_{Reedy}^J$.*

*Proof.* We only prove the interesting direction; assume that $X, Y$ are cofibrant in $\mathcal{M}_{Loc}^J$ and that $X \to Y \in \mathcal{M}_{Reedy}^J$ is a Reedy cofibration. Remains to show that

$$X_c \sqcup_{X_a} Y_a \to Y_c \text{ and } X_c \sqcup_{X_b} Y_b \to Y_c$$

are trivial cofibrations. The fact that the maps are weak equivalences follows by applying the 2-out-of-3 property to the diagrams:

![img-28.jpeg](img-28.jpeg)

![img-29.jpeg](img-29.jpeg)

The vertical maps $X_a \xrightarrow{\sim} X_c$, $X_b \xrightarrow{\sim} X_c$, $Y_a \xrightarrow{\sim} Y_c$ and $Y_b \xrightarrow{\sim} Y_c$, are trivial cofibrations since $X$ and $Y$ are cofibrant in $\mathcal{M}_{Loc}^J$. Remains to see that they are cofibrations. From the Reedy condition we have that the map $X_c \sqcup_{L_c X} L_c Y \hookrightarrow Y_c$ is a cofibration, and observe that the domains of the maps $X_c \sqcup_{X_a} Y_a \to Y_c$ and $X_c \sqcup_{X_b} Y_b \to Y_c$ are contained in the colimit $X_c \sqcup_{L_c X} L_c Y$. Therefore, the maps factor as composition of cofibrations

$$X_c \sqcup_{X_a} Y_a \hookrightarrow X_c \sqcup_{L_c X} L_c Y \hookrightarrow Y_c \text{ and } X_c \sqcup_{X_b} Y_b \hookrightarrow X_c \sqcup_{L_c X} L_c Y \hookrightarrow Y_c,$$

which concludes the proof.

71

**Lemma 4.25.** Let $X \in \mathcal{M}_{Loc}^{J}$ cofibrant and $X \to Z \in \mathcal{M}_{Reedy}^{J}$ a Reedy trivial cofibration. Then $Z$ is cofibrant in $\mathcal{M}_{Loc}^{J}$. Furthermore, $X \to Z$ is a trivial cofibration in $\mathcal{M}_{Loc}^{J}$.

*Proof.* Since $X \xrightarrow{\sim} Z$ is a Reedy trivial cofibration, then $X_{a} \xrightarrow{\sim} Z_{a}$, $X_{b} \sqcup_{X_{a} \sqcup X_{a}} (Z_{a} \sqcup Z_{a}) \xrightarrow{\sim} Z_{b}$ and $X_{c} \sqcup_{(X_{b} \sqcup X_{a} X_{b})} (Z_{b} \sqcup_{Z_{a}} Z_{b}) \xrightarrow{\sim} Z_{c}$ are trivial cofibrations. We then obtain the following diagram:

![img-30.jpeg](img-30.jpeg)

This shows that $X_{b} \xrightarrow{\sim} Z_{b}$ is a trivial cofibration. Since $X$ is cofibrant then all the maps in the diagram

$$X_{a} \longrightarrow X_{b} \longrightarrow X_{c}$$

are trivial cofibrations. Consider the commutative diagram where the back and front faces are pushouts

![img-31.jpeg](img-31.jpeg)

which, by the two-out-of-three, shows that $X_{b} \sqcup_{X_{a}} X_{b} \xrightarrow{\sim} Z_{b} \sqcup_{Z_{a}} Z_{b}$ is a trivial cofibration. Remains to prove that $Z_{b} \xrightarrow{\sim} Z_{c}$ is a trivial cofibration.

72

The pushout

![img-32.jpeg](img-32.jpeg)

shows that $X_c \xrightarrow{\sim} Z_c$ is a trivial cofibration. Note that $Z$ is Reedy cofibrant, hence $Z_b \hookrightarrow Z_c$ is a cofibration. By the two-out-of-three property, we can conclude that $Z_b \xrightarrow{\sim} Z_c$ is indeed a trivial cofibration. The above says that $Z$ is cofibrant.

The second part is also true, since $X \rightarrow Z$ is a level-wise weak equivalence. $\square$

**Corollary 4.26.** *Any map between diagrams $f: X \rightarrow Y$, where $X$ is a cofibrant diagram $X$ and $Y$ is a fibrant diagram in $\mathcal{M}_{Loc}^J$, can be factored as a trivial cofibration followed by a fibration.*

*Proof.* We factor $f: X \rightarrow Y$ in $\mathcal{M}_{Reedy}^J$ to obtain $X \xrightarrow{\sim} Z \rightarrow Y$. $Z \rightarrow Y$ is also a fibration in $\mathcal{M}_{Loc}^J$ as is it is level-wise. Finally, $X \xrightarrow{\sim} Z \in \mathcal{M}_{Loc}^J$ by the previous theorem 4.25. $\square$

For the factorization of a diagram map $f: X \rightarrow Y$ in $\mathcal{M}^J$, with $X$ cofibrant and $Y$ fibrant, into a cofibration followed by a trivial fibration we will need an auxiliary class of diagrams.

**Construction 4.27.** Denote by $K$ the category $J$ with the opposite Reedy structure given above (the degree function reversed). We endow $\mathcal{M}^K$ with the Reedy model structure. Then a diagram $Y \in \mathcal{M}_{Reedy}^K$ is fibrant if $Y_c \rightarrow 1$, $Y_b \rightarrow Y_c$ and $Y_a \rightarrow Y_b \times_{Y_c} Y_b$ are fibrations in $\mathcal{M}$. In this situation $Y_b$ is also fibrant.

The limit of a diagram $Y \in \mathcal{M}^K$ is simply the equalizer $Eq(Y_i, Y_j)$. Note that the following pullback also computes the limit of $Y$:

![img-33.jpeg](img-33.jpeg)

73

From this we conclude that $\operatorname{Lim} Y$ is a fibrant object of $\mathcal{M}$ if $Y \in \mathcal{M}_{Reedy}^K$ is fibrant, and letting $Z$ to denote the constant diagram at $\operatorname{Lim} Y$ then this comes with a diagram map $Z \to Y$ of the following form

![img-34.jpeg](img-34.jpeg)

where all top arrows are identities. Finally, note that $Y$ being fibrant in $\mathcal{M}_{Reedy}^K$ implies that both maps $Y_a \longrightarrow Y_b$ are fibrations. This can be deduced from the following diagram:

![img-35.jpeg](img-35.jpeg)

Observation 4.28. Recall that the fibrations in $\mathcal{M}_{Loc}^J$ are the level-wise fibrations. Since $Z \in \mathcal{M}^K$ is point-wise fibrant then it is Reedy fibrant in $\mathcal{M}_{Loc}^J$. Similarly, $Y$ is Reedy fibrant in $\mathcal{M}_{Reedy}^K$, in particular, implies that is object-wise fibrant, so it is fibrant in $\mathcal{M}_{Loc}^J$. We will use this diagram $Z$ throughout this section.

Lemma 4.29. The map $Z \to Y$ from above is a trivial fibration in $\mathcal{M}_{Loc}^J$.

Proof. We show that the map has the right lifting property against any cofibration $A \hookrightarrow B \in \mathcal{M}_{Loc}^J$. First, assume that $A = \emptyset$, and $B$ is a cofibrant object in $\mathcal{M}_{Loc}^J$ and $Y$ a fibrant diagram in $\mathcal{M}_{Reedy}^K$. We consider the lifting problem in $\mathcal{M}_{Loc}^J$:

![img-36.jpeg](img-36.jpeg)

From the discussion above we obtain the following commutative diagram:

![img-37.jpeg](img-37.jpeg)

74

Thus, we obtain the following lifts:

$$\begin{array}{ccc} B_a \rightarrow Y_a & B_a \rightarrow Y_a & B_b \rightarrow Y_b \\ B_i \downarrow \sim \nearrow l_i \downarrow Y_i & B_j \downarrow \sim \nearrow l_j \downarrow Y_j & B_k \downarrow \sim \nearrow l_k \downarrow Y_k \\ B_b \rightarrow Y_b & B_b \rightarrow Y_b & B_c \rightarrow Y_c \end{array}$$

Using this we can construct the following commutative diagram:

$$\begin{array}{ccc} B_a & \searrow \nearrow & B_b \\ \downarrow \searrow & \searrow & \downarrow \searrow \nearrow \\ B_b & \searrow & B_b \sqcup_{B_a} B_b \\ B_k & \searrow & \downarrow \searrow \nearrow \\ & & B_c \\ & & \downarrow \searrow \nearrow \\ & & B_c \\ & & \downarrow \searrow \nearrow \\ & & Y_b \end{array} \begin{array}{ccc} Y_a & \searrow & Y_j \\ \downarrow \searrow & \searrow & Y_b \\ Y_b & \searrow Y_c & Y_b \\ \downarrow & \searrow & \downarrow \\ Y_b & \searrow & Y_c \end{array}$$

where the middle trivial cofibration and fibration come from $B$ being cofibrant in $\mathcal{M}_{Loc}^J$ and $Y$ being fibrant in $\mathcal{M}_{Reedy}^K$ respectively. Then there exist a map $B_c \xrightarrow{r} Y_a$ that fits in the diagram. Furthermore, we readily see from the diagram that $Y_j r = l_k = Y_i r$. Therefore, there is a unique arrow $B_c \xrightarrow{t} Eq(Y_i, Y_j) = \text{Lim } Y$ making the obvious triangle commutative. By taking the appropriate compositions with the map $t$ we can construct a diagram map $B \rightarrow Z$ such that is a solution to the lifting problem.

For the general case

$$\begin{array}{ccc} A & \longrightarrow & Z \\ \downarrow & & \downarrow \\ B & \longrightarrow & Y \end{array}$$

one can play the same game, the only change is that the diagram is a bit more involved. $\square$

The diagram $Z$ from theorem 4.27 is not necessarily Reedy cofibrant, but it is almost cofibrant in $\mathcal{M}_{Loc}^J$ as the maps in it are trivial cofibrations. The only missing part is that $\lim Y$ is not cofibrant in $\mathcal{M}$. In order to obtain cofibrant diagram in $\mathcal{M}_{Loc}^J$, we include the following result.

**Lemma 4.30.** If $Y \in \mathcal{M}_{Reedy}^K$ is fibrant then there exists a trivial fibration $W \twoheadrightarrow Y \in \mathcal{M}_{Loc}^J$ with $W \in \mathcal{M}_{Loc}^J$ cofibrant.

75

*Proof.* Since $Y$ is fibrant in $\mathcal{M}_{Reedy}^K$, then it is fibrant in $\mathcal{M}_{Loc}^J$ as these are level-wise fibrant. Similarly, $Z$ from theorem 4.27 is fibrant in $\mathcal{M}_{Loc}^J$, which also comes with a trivial fibration $Z \xrightarrow{\sim} Y$ by theorem 4.29. We can take a Reedy cofibrant replacement $W \xrightarrow{\sim} Z$. Since this last map is in particular a level-wise weak equivalence, it implies that the maps in $W$ are weak equivalences. By 2-out-of-3 property, the maps in $W$ are trivial cofibrations. This makes $W$ a cofibrant replacement in $\mathcal{M}^J$ of $Y$ by composing the trivial fibrations $W \xrightarrow{\sim} Z \xrightarrow{\sim} Y$. $\square$

Before giving the factorization, we need a technical result that follows from the next lemma.

*Remark 4.31.* From [Hen20, 2.1.11 Proposition], if $A \in \mathcal{M}$ is cofibrant then the coslice category $A/\mathcal{M}$ inherits a weak model structure from $\mathcal{M}$ where a map in $A/\mathcal{M}$ is cofibration, fibration and weak equivalences if it is one in $\mathcal{M}$. Dually, one induces a weak model structure on the slice $\mathcal{M}/Y$ if $Y$ is fibrant.

**Construction 4.32.** Consider a map $f : A \to Y$ in $\mathcal{M}$ where $A$ is cofibrant and $Y$ is fibrant. Consider $A/\mathcal{M}$ with the weak model structure described in the previous theorem 4.31.

The map $f : A \to Y$ allows us to see $Y$ as an object in $A/\mathcal{M}$, which is fibrant as $Y$ is fibrant in $\mathcal{M}$. So, we can take the slice $(A/\mathcal{M})/Y$. Objects of $(A/\mathcal{M})/Y$ are factorizations of the form

![img-38.jpeg](img-38.jpeg)

Let two objects in this category

![img-39.jpeg](img-39.jpeg)

and

![img-40.jpeg](img-40.jpeg)

which we refer to as $B$ and $X$. A map from $B$ to $X$ is a diagonal filler of the resulting commutative square:

![img-41.jpeg](img-41.jpeg)

76

A cofibrant object in $(A/\mathcal{M})/Y$ is one in which the first map is a cofibration in $\mathcal{M}$, and a fibrant object when the last map is a fibration i.e.,

![img-42.jpeg](img-42.jpeg)

respectively. Also note that the category $(A/\mathcal{M})/Y$ coincides with $A/(\mathcal{M}/Y)$, both as categories and as model categories.

Observation 4.33. [Hen20, 2.4.3 Proposition] observed that the Quillen adjunction descends to the homotopy categories: If $F : \mathcal{C} \rightleftarrows \mathcal{D} : G$ is a Quillen pair, then we obtain a natural isomorphism

$$\mathrm{Ho}(\mathcal{C}^{\mathrm{BIF}})(W, G(Z)) \cong \mathrm{Ho}(\mathcal{D}^{\mathrm{BIF}})(F(W), Z)$$

of the homotopy categories.

The category $\mathrm{Ho}(\mathcal{C}^{\mathrm{BIF}})$ is the localization of the subcategory of bifibrant objects at trivial (co)fibrations. This is the content of [Hen20, 2.2.6 Theorem], which also proves that there are equivalences

$$\mathrm{Ho}(\mathcal{C}^{\mathrm{COF}}) \cong \mathrm{Ho}(\mathcal{C}^{\mathrm{BIF}}) \cong \mathrm{Ho}(\mathcal{C}^{\mathrm{FIB}})$$

where the first category is the localization of $\mathcal{C}^{\mathrm{COF}}$ at trivial cofibrations, and the second is the localization of $\mathcal{C}^{\mathrm{FIB}}$ at trivial fibrations. Therefore, up to these equivalences of categories, we say that $\mathrm{Ho}(F) : \mathrm{Ho}(\mathcal{C}^{\mathrm{COF}}) \to \mathrm{Ho}(\mathcal{D}^{\mathrm{COF}})$ and $\mathrm{Ho}(G) : \mathrm{Ho}(\mathcal{D}^{\mathrm{FIB}}) \to \mathrm{Ho}(\mathcal{C}^{\mathrm{FIB}})$ are "adjoint".

Lemma 4.34. For all $i : A \hookrightarrow B$ and $i' : A' \hookrightarrow B'$ cofibrations between cofibrant objects, for all $p : X \twoheadrightarrow Y$ fibration between fibrant objects, if there is a commutative diagram:

![img-43.jpeg](img-43.jpeg)

then $i \pitchfork p$ if and only if $i' \pitchfork p$. The dual statement also holds: For all $i : A \hookrightarrow B$ core cofibrations, for all $p : X \twoheadrightarrow Y$ and $p' : X' \twoheadrightarrow Y'$ fibrations between fibrant objects, if there is a commutative diagram:

![img-44.jpeg](img-44.jpeg)

77

then $i \pitchfork p$ if and only if $i \pitchfork p'$.

*Proof.* We prove the first part of the lemma, the second part is dual. We have the following commutative squares

$$\begin{array}{ccc} A \xrightarrow[\sim]{k} A' & A \xrightarrow{f} X & A' \xrightarrow{f'} X \\ i \downarrow & i \downarrow & \downarrow p \\ B \xrightarrow[\sim]{l} B' & B \xrightarrow[g]{} Y & B' \xrightarrow[g]{} Y \end{array}$$

The proof relies heavily on theorem 4.32: The middle square above corresponds to a pair of objects $B, X$ in a double slice category $A/\mathcal{M}/Y$, and a diagonal filler witnessing that $i \pitchfork p$ is a map in this double slice category.

We start with the induced weak model structure on the slice $\mathcal{M}/Y$. Note that from [Hen20, 2.4.2 Example] the weak equivalence $k: A \rightarrow A'$ induces a weak Quillen equivalence $P_k: A/(\mathcal{M}/Y) \leftrightarrows A'/(\mathcal{M}/Y): U_k$. Observe that $B, B'$ are cofibrant and $Y$ is fibrant. In what follows we leave $Y$ implicit as we work in the slice $(A/\mathcal{M})/Y$, here we use that $(A/\mathcal{M})/Y = A/(\mathcal{M}/Y)$ from theorem 4.32.

The functor $P_k$ takes a cofibration $A \hookrightarrow C$ along $k: A \rightarrow A'$, while $U_k$ precomposes with $k$. Using the following diagram, since $P_k B$ is cofibrant, by the 2-out-of-3 property

![img-45.jpeg](img-45.jpeg)

we see that there is a weak equivalence $P_k B \xrightarrow{\sim} B'$, this implies they are isomorphic in $\mathrm{Ho}(A'/(\mathcal{M}/Y))$. We have:

$$\begin{aligned} \mathrm{Hom}_{\mathrm{Ho}(A'/(\mathcal{M}/Y))}(B', X) &\cong \mathrm{Hom}_{\mathrm{Ho}(A'/(\mathcal{M}/Y))}(P_k(B), X) \\ &\cong \mathrm{Hom}_{\mathrm{Ho}(A/(\mathcal{M}/Y))}(B, U_k(X)) \\ &\cong \mathrm{Hom}_{\mathrm{Ho}(A/(\mathcal{M}/Y))}(B, X). \end{aligned}$$

The first isomorphism follows from $B' \cong P_k(B)$ in $\mathrm{Ho}(A'/(\mathcal{M}/Y))$, the second is the weak Quillen adjunction $P_k \dashv U_k$ applied to the cofibrant object $B \in (A/\mathcal{M})/Y$ and the fibrant object $X \in (A'/\mathcal{M})/Y$. We crucially

78

use theorem 4.33, so the second isomorphism is really up to some equivalence of categories.

Now we use $\mathrm{Hom}_{\mathrm{Ho}(A' / (\mathcal{M} / Y))}(B', X) \cong \mathrm{Hom}_{\mathrm{Ho}(A / (\mathcal{M} / Y))}(B, X)$ to conclude. First, recall that a diagonal filler of

![img-46.jpeg](img-46.jpeg)

is the same as a map $B \to X$ in $A / \mathcal{M} / Y$, and similarly for $B'$ and $X$. Assume that $i \pitchfork p$, this give us a map $B \to X$ in $\mathrm{Ho}(A / \mathcal{M} / Y)$. Using the isomorphism, we have a map $B' \to X$ in $\mathrm{Ho}(A' / \mathcal{M} / Y)$, from which we can select a representative of the homotopy class, which implies that $i' \pitchfork p$. Similarly, we get that $i' \pitchfork p$ implies $i \pitchfork p$. $\square$

**Lemma 4.35.** *Let $X \to Y$ be a map in $\mathcal{M}^J$ with $X$ cofibrant and $Y$ fibrant. Then such a map can be factored as a cofibration followed by a trivial fibration.*

*Proof.* Observe first that $Y$ can be assumed to be Reedy cofibrant in $\mathcal{M}^J$. Indeed, we can simply take a Reedy cofibrant replacement $Y' \xrightarrow{\sim} Y$, and instead use the dashed arrow

![img-47.jpeg](img-47.jpeg)

Under this assumption, $Y$ is point-wise cofibrant, whence Reedy cofibrant in $\mathcal{M}^K$. Therefore, we can take a fibrant replacement in $\mathcal{M}^K$, $Y \xrightarrow{\sim} Y'$. Using [Hen20, Corollary 2.4.4] equivalences are preserved under pullbacks along fibrations, so we get the pullback square

![img-48.jpeg](img-48.jpeg)

Furthermore, we know from theorem 4.30 that $W \twoheadrightarrow Y'$ is a trivial fibration in $\mathcal{M}^J$. Therefore, it has the right lifting property against any cofibration between cofibrant objects in $\mathcal{M}^J$. We can use theorem 4.34 to conclude

79

that $LY \rightarrow Y$ satisfies the same property, *i.e.*, it is a trivial fibration in $\mathcal{M}^J$. Since $X$ is cofibrant, we obtain a lift

![img-49.jpeg](img-49.jpeg)

The map $X \rightarrow LY$ can be factored in the Reedy model structure $\mathcal{M}^J$ as $X \hookrightarrow X' \xrightarrow{\sim} LY$. The diagram $X'$ is cofibrant in $\mathcal{M}^J$ since it is equivalent to the cofibrant diagram $LY$, and $X$ is cofibrant by assumption. Therefore, it follows from theorem 4.25 that the Reedy cofibration $X \hookrightarrow X'$ is a cofibration in the model $\mathcal{M}^J$. This gives us the desired factorization in $\mathcal{M}^J$, $X \hookrightarrow X' \xrightarrow{\sim} Y$. $\square$

All the previous work can be summarized in the following proof of theorem 4.19. This proves that the category of diagrams $\mathcal{M}^J$ has a weak model structure with the specified cofibrations and fibrations, which, as explained above, encodes objects with a weak cylinder object. We remark that our proof will show that the conditions of [Hen20, 2.1.10 Definition] are satisfied instead of theorem C.1. The reason is for this is that in theorem 4.19 we do not have an explicit class of weak equivalences. More precisely, we will use [Hen20, 2.3.3 Proposition] which gives some alternative criteria to obtain a weak model structure in this sense.

*Proof.* (theorem 4.19) Note first that we have the Reedy weak model structure on $\mathcal{M}^J$ by virtue of theorem C.11. Also, the existence of initial and terminal diagrams is clear. We must justify that the class of (co)fibrations form a class of (co)fibrations in $\mathcal{M}^J$. For fibrations, since these are level-wise, it is immediate that: the terminal diagram is fibrant, any isomorphism with fibrant codomain is a fibration, the class is closed under compositions, and stable under pullbacks along maps between fibrant objects.

The dual conditions must be verified for the class of cofibrations. That the initial diagram is cofibrant it is immediate to verify. To see other stability conditions, we observe these are true for $\mathcal{M}^J_{Reedy}$. In addition, for stability under isomorphisms we use repeatedly that maps in $\mathcal{M}$ isomorphic to trivial cofibration are also trivial cofibrations. This simply because the new condition we added involves the requirement that certain maps trivial cofibrations. Stability under pushouts follows from the stability in $\mathcal{M}^J_{Reedy}$ and the fact that trivial cofibrations in the weak model $\mathcal{M}$ are pushout stable.

80

The factorization of a map $f : X \to Y$, where $X$ is cofibrant and $Y$ is fibrant, into a cofibration followed by a trivial fibration is the content of theorem 4.35.

The factorization of a map $f : X \to Y$, where $X$ is cofibrant and $Y$ is fibrant, into a trivial cofibration followed by a fibration is guaranteed by theorem 4.26.

In order to conclude, we use [Hen20, 2.3.3 Proposition]. For which we need to verify that a cofibration $X \to Y \in \mathcal{M}_{Loc}^J$ with $X$ cofibrant and $Y$ fibrant admit a relative strong cylinder object. Firstly, we know that the map admits a relative cylinder object in $\mathcal{M}_{Reedy}^J$:

![img-50.jpeg](img-50.jpeg)

with $Y \hookrightarrow Y \coprod_X Y \hookrightarrow I_X Y$ a Reedy trivial cofibration. Since $Y$ is cofibrant in $\mathcal{M}_{Loc}^J$ we can use theorem 4.25 to conclude that $I_X Y$ is also cofibrant in $\mathcal{M}_{Loc}^J$, and that the map $Y \to I_X Y$ is a trivial cofibration in $\mathcal{M}_{Loc}^J$. Now we have cofibrant objects $Y \coprod_X Y$, $I_X Y$ in $\mathcal{M}_{Loc}^J$ and a Reedy cofibration between them, so we use theorem 4.24 to conclude it is actually a cofibration in $\mathcal{M}_{Loc}^J$. This gives us the relative cylinder objects.

Finally, the 2-out-of-3 property for trivial cofibrations between bifibrant objects follows using that $\mathcal{M}_{Reedy}^J$ is a weak model category, so the property is true in this Reedy weak model structure. By which we mean that the property is true for the underlying Reedy trivial cofibrations between bifibrant objects of $\mathcal{M}_{Loc}^J$. Theorem 4.25 allows us to conclude that such Reedy trivial cofibrations are indeed trivial cofibrations in $\mathcal{M}_{Loc}^J$. Now [Hen20, 2.3.3 Proposition] allows us to conclude that $\mathcal{M}_{Loc}^J$, with the specified classes of maps, is a weak model category. $\square$

### 4.3.2 Weak model on correspondences

Next, we consider another diagram category $I$:

$$0 \to 2 \leftarrow 1$$

Where $\deg(0) = \deg(1) = 0$ and $\deg(2) = 1$. Similarly to the previous section, we construct a “right Bousfield localization” of the Reedy weak model structure on $\mathcal{N}^I$.

81

**Theorem 4.36.** *There is a weak model structure $\mathcal{N}_{Loc}^{I}$ on the category of diagrams $\mathcal{N}^{I}$ obtained from the Reedy weak model structure $\mathcal{N}_{Reedy}^{I}$, where:*

1. *A map between diagrams $X \to Y$ is a cofibration if*

(a) *It is a Reedy cofibration,*
(b) $X_2 \sqcup_{X_1} Y_1 \xrightarrow{\sim} Y_2$ and $X_2 \sqcup_{X_0} Y_0 \xrightarrow{\sim} Y_2$ are trivial cofibrations in $\mathcal{N}$.

2. *Fibrations are level-wise fibrations.*

It will be useful to have in mind that for an object $X \in \mathcal{N}^{I}$ we have $L_0 X = 0$ and $L_1 X = X_0 \sqcup X_1$. So a map $X \to Y$ is a Reedy cofibration if the maps $X_0 \hookrightarrow Y_0$, $X_1 \hookrightarrow Y_1$ and $(Y_0 \sqcup Y_1) \sqcup_{(X_0 \sqcup X_1)} X_2 \hookrightarrow Y_2$ are cofibrations.
*Observation 4.37.* Unwinding the definitions, a diagram $X \in \mathcal{N}_{Loc}^{I}$ is cofibrant if both maps $X_0 \xrightarrow{\sim} X_2$ and $X_1 \xrightarrow{\sim} X_2$ are trivial cofibrations.

The proof of the theorem is completely analogous to theorem 4.19. We state the lemmas necessary for this and only comment on the proofs when adequate.

**Lemma 4.38.** *Let $X, Y \in \mathcal{N}_{Loc}^{I}$ cofibrant. Then, a map $X \to Y$ is a cofibration in $\mathcal{N}_{Loc}^{I}$ if and only if it is a cofibration in $\mathcal{N}_{Reedy}^{I}$.*

*Proof.* Just as in theorem 4.24 we only prove the interesting direction; assume that $X, Y$ are cofibrant in $\mathcal{N}_{Loc}^{I}$ and that $X \to Y \in \mathcal{N}_{Reedy}^{I}$ is a Reedy cofibration. Remains to show that

$$X_2 \sqcup_{X_0} Y_0 \to Y_2 \text{ and } X_2 \sqcup_{X_1} Y_1 \to Y_2$$

are trivial cofibrations. Again, the fact that the maps are weak equivalences follow from $X, Y$ being cofibrant and the 2-out-of-3 property. To see that they are cofibrations we can use the Reedy condition just as in theorem 4.24.

□

**Lemma 4.39.** *Let $X \in \mathcal{N}_{Loc}^{I}$ cofibrant and $X \to Z \in \mathcal{N}_{Reedy}^{I}$ a Reedy trivial cofibration. Then $Z$ is cofibrant in $\mathcal{N}_{Loc}^{I}$. Furthermore, $X \to Z$ is a trivial cofibration in $\mathcal{N}_{Loc}^{I}$.*

*Proof.* The difficult part is to show that $Z$ is cofibrant. Since $X \to Z$ is a Reedy trivial cofibration, then by theorem C.16 we have it is a levelwise trivial cofibration. Then $Z$ is cofibrant by the 2-out-of-3 property. □

82

**Corollary 4.40.** *Any map between diagrams $f : X \rightarrow Y$, where $X$ is a cofibrant diagram and $Y$ is a fibrant diagram in $\mathcal{N}_{Loc}^I$, can be factored as a trivial cofibration followed by a fibration.*

*Proof.* Now that we have theorem 4.39, we can proceed as in theorem 4.26 by first taking the factorization in $\mathcal{N}_{Reedy}^I$. $\square$

**Construction 4.41.** Denote by $K'$ the category $I$ with the opposite Reedy structure given above (the degree function reversed). We endow $\mathcal{N}^{K'}$ with the Reedy model structure. Then a diagram $Y \in \mathcal{N}_{Reedy}^{K'}$ is fibrant if $Y_2 \rightarrow 1$, $Y_0 \rightarrow Y_2$ and $Y_1 \rightarrow Y_2$ are fibrations in $\mathcal{N}$.

In this situation we can see that $\lim Y = Y_0 \times_{Y_2} Y_1$ and is fibrant in $\mathcal{N}$. We can again take a $Z \in \mathcal{N}^I$ to be the correspondence with constant value $\lim Y$. So it comes with a map $Z \rightarrow Y$.

**Lemma 4.42.** *The map $Z \rightarrow Y$ from above is a trivial fibration in $\mathcal{N}_{Loc}^I$.*

*Proof.* The same idea as in theorem 4.29 carries over here. The diagrams are even simpler. $\square$

**Lemma 4.43.** *If $Y \in \mathcal{N}_{Reedy}^{K'}$ is fibrant then there exists a trivial fibration $W \rightarrow Y \in \mathcal{N}_{Loc}^I$ with $W \in \mathcal{N}_{Loc}^I$ cofibrant.*

*Proof.* The argument of theorem 4.30 applies here too. $\square$

**Lemma 4.44.** *Let $X \rightarrow Y$ be a map in $\mathcal{N}^I$ with $X$ cofibrant and $Y$ fibrant. Then such a map can be factored as a cofibration followed by a trivial fibration.*

*Proof.* We have all ingredients to proceed as in theorem 4.35. Firstly, we can assume that $Y$ is Reedy cofibrant in $\mathcal{N}^I$ and we can take a fibrant replacement in $\mathcal{N}^K$. So we can construct the following pullback square:

$$\begin{array}{c} LY \xrightarrow{\sim} W \\ \sim \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Then we can obtain a map $X \rightarrow LY$. Factoring this map as $X \hookrightarrow X' \xrightarrow{\sim} LY$, the first map is moreover a cofibration in $\mathcal{N}_{Loc}^I$ in view of theorem 4.39. This produces the factorization $X \hookrightarrow X' \xrightarrow{\sim} Y$. $\square$

The proof of theorem 4.36 is a carbon copy from the one of theorem 4.19, the lemmas of this section provide us with all the required steps.

83

### 4.3.3 Projections are Barton trivial fibrations

**Lemma 4.45.** *The functor $\mathcal{N}^I \to \mathcal{N}$ such that $A \to B \leftarrow C \in \mathcal{N}^I \mapsto A \in \mathcal{N}$, is extensible. Also, the functor $\mathcal{N}^I \to \mathcal{N}$ such that $A \to B \leftarrow C \in \mathcal{N}^I \mapsto C \in \mathcal{N}$ is extensible.*

*Proof.* Let $A := a \xrightarrow{\sim} b \xleftarrow{\sim} c \in \mathcal{N}^I_{Loc}$ be a cofibrant diagram and $x \in \mathcal{N}^{\mathrm{COF}}$ a cofibrant object and a cofibration $a \hookrightarrow x$. We take the fibrant replacement of $x$ and consider the pushout as indicated below, and we obtain a solution to the lifting problem on the right:

![img-51.jpeg](img-51.jpeg)

The resulting map $c \to x^{fib}$ can be factored as $c \hookrightarrow z \xrightarrow{\sim} x^{fib}$. We can take further pushouts

![img-52.jpeg](img-52.jpeg)

There is a map $P \to x^{fib}$ which we can factor as $P \hookrightarrow y \xrightarrow{\sim} x^{fib}$, and the resulting diagram we get

![img-53.jpeg](img-53.jpeg)

Furthermore, there is a map $b \sqcup_a x \to y$ which is a cofibration as it is the composite of the two cofibrations. Using the 2-out-of-3 property repeatedly,

84

one concludes that the map $z \sqcup_c b \to y$ is a trivial cofibration. Thus, we have constructed the cofibrant object $X := z \xrightarrow{\sim} y \xleftarrow{\sim} x \in \mathcal{N}_{Loc}^I$. The induced map $A \to X$ is a level-wise cofibration. The maps $b \sqcup_a x \to y$ and $b \sqcup_a z \to y$ are trivial cofibrations.

Remains to show that $A \to X$ is a Reedy cofibration. We already have that $a \to x$ and $c \to z$ are cofibrations. We now need to show that the induced map

![img-54.jpeg](img-54.jpeg)

is a cofibration. By diagram chasing, one can show that the diagram

![img-55.jpeg](img-55.jpeg)

commutes. One shows that the bottom right corner computes the pushout of the span. Using that the map $P \hookrightarrow y$ is a cofibration one concludes that $(x \sqcup) \sqcup_{a \sqcup c} b \to y$ is also a cofibration. This concludes the proof that $A \to X$ is a Reedy core cofibration in $\mathcal{N}^I$. Therefore, it must a cofibration. We summarize our construction with the following diagram:

![img-56.jpeg](img-56.jpeg)

This cofibration is a (strict) lift of $a \hookrightarrow x$, showing that the functor $\mathcal{N}^I \to N$ is an extensible functor. The second part of the lemma is analogous. $\square$

85

Observation 4.46. Note that in the previous theorem 4.45, using 2-out-of-3 property, if we start with a trivial cofibration $a \stackrel{\sim}{\hookrightarrow} x$ then we obtain a level-wise equivalence between cofibrant objects in $\mathcal{N}_{Loc}^{I}$. We conclude that the projections are weakly conservative.

Corollary 4.47. The functor $\mathcal{N}^{I} \to \mathcal{N}$ such that $A \to B \leftarrow C \in \mathcal{N}^{I} \mapsto A \in \mathcal{N}$, is a Barton trivial fibration. Also, the functor $\mathcal{N}^{I} \to \mathcal{N}$ such that $A \to B \leftarrow C \in \mathcal{N}^{I} \mapsto C \in \mathcal{N}$, is a Barton trivial fibration.

Proof. We saw in theorem 4.45 that the projections are extensible and from theorem 4.46 that is weakly conservative. It is also straightforward to see that it preserve cofibrations and trivial cofibrations. □

We now want to see that any left Quillen functor $F : \mathcal{M} \to \mathcal{N}$ part of a Quillen equivalence between weak model categories admits a Brown-like factorization. To this end, consider the following:

Construction 4.48. We define the category of diagrams

$$\mathcal{N}_{F}^{I} := \{Fa \to b \leftarrow c | a \in \mathcal{M}^{\mathrm{COF}}, b, c \in \mathcal{N}\}.$$

The weak model structure on this category is similar to that of $\mathcal{N}^{I}$, the only difference is that $X \to Y$ is a cofibration if $X_{b} \sqcup_{FX_{a}} FY_{a} \to Y_{b}$ is a trivial cofibration.

When $F$ is the identity functor we recover $\mathcal{N}^{I}$ from theorem 4.36. A cofibrant object in $\mathcal{N}_{F}^{I}$ is a diagram of the form

$$Fa \stackrel{\sim}{\hookrightarrow} b \stackrel{\sim}{\longleftarrow} c.$$

Observation 4.49. With the set up above, it follows from theorem 4.47 that the projection $\pi_{1} : \mathcal{N}_{F}^{I} \to \mathcal{M}$, sending each diagram $Fa \to b \leftarrow c$ to $a$, is a Barton trivial fibration.

To show that the projection from $\pi_{2} : \mathcal{N}_{F}^{I} \to \mathcal{N}$ sending each diagram $Fa \to b \leftarrow c$ to $c \in \mathcal{N}$ is a trivial fibration we make use of the following:

Lemma 4.50. Let $F : \mathcal{M} \to \mathcal{N}$ be a left Quillen equivalence between weak model categories. For any objects $x \in \mathcal{M}^{\mathrm{COF}}$, $y \in \mathcal{N}^{\mathrm{FIB}}$ and a map $f : Fx \to y$ there exists an object $z \in \mathcal{M}^{\mathrm{COF}}$ such that $f$ factors as

![img-57.jpeg](img-57.jpeg)

86

Proof. We know that there is an isomorphism

$$\varphi : \operatorname{Hom}_{\mathcal{N}}(Fx, y) \simeq \operatorname{Hom}_{\mathcal{M}}(x, Gy) : \varphi^{-1}$$

given by the Quillen adjunction, natural in $x \in \mathcal{M}^{\mathrm{COF}}$ and $y \in \mathcal{N}^{\mathrm{FIB}}$. Recall from [Hen20, 2.4.3 Proposition] that $F : \mathcal{M}^{\mathrm{COF}} \to \mathcal{N}^{\mathrm{COF}}$ and $G : \mathcal{N}^{\mathrm{FIB}} \to \mathcal{M}^{\mathrm{FIB}}$ preserve equivalences. Take $\varphi f$ the adjoint transpose of $f$. We can take a factorization

![img-58.jpeg](img-58.jpeg)

By naturality, one checks that $f = \varphi^{-1}sFr$ where $Fr$ is a cofibration. Since the Quillen pair is an equivalence, we deduce from [Hen20, 2.4.5 Proposition (i)] that $\varphi^{-1}s$ is an equivalence. □

Corollary 4.51. Let $F : \mathcal{M} \rightleftarrows \mathcal{N} : G$ be a Quillen equivalence. Then the projection $\pi_2 : \mathcal{N}_F^I \to \mathcal{N}$ sending each diagram $Fa \to b \leftarrow c$ to $c \in \mathcal{N}$ is a Barton trivial fibration.

Proof. We show that in a situation as in the diagram

![img-59.jpeg](img-59.jpeg)

there is a cofibrant object over $z$ that projects onto $c \hookrightarrow z$. By taking a fibrant replacement, we can assume that the diagram is point-wise fibrant. From [Hen20, 2.2.3 Proposition] there exists a homotopy inverse of $c \xrightarrow{\sim} b$, this give us a map $Fa \to c$. Using theorem 4.50 this last map can be factored as $Fa \hookrightarrow Fx \xrightarrow{\sim} c$. The rest of the proof continues as in theorem 4.47. □

87

**Theorem 4.52.** Given $F : \mathcal{M} \rightleftarrows \mathcal{N}$ be a left Quillen equivalence between weak model categories. Then, we have a diagram of weak model categories

$$\begin{array}{c} \mathcal{M}^J \xrightarrow{H} \mathcal{N}_F^I \\ B \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{M}_{\overline{(Id_{\mathcal{M}},F)}} \xrightarrow{\mathcal{M}} \mathcal{N}, \end{array}$$

where $\pi_1$ and $\pi_2$ are Barton trivial fibrations.

*Proof.* The work we have done produces a diagram as on the left below, and the action of the functors on objects is spelled out on the right:

$$\begin{array}{ccc} \mathcal{M}^J & \xrightarrow{H} & \mathcal{N}_F^I \\ B \Big\downarrow & & \Big\downarrow_{(\pi_1,\pi_2)} \\ \mathcal{M}_{\overline{(Id_{\mathcal{M}},F)}} \xrightarrow{\mathcal{M}} \mathcal{N} & & X_a \Rightarrow X_b \rightarrow X_c \xmapsto{H} FX_a \Rightarrow FX_b \\ & & B \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ & & & X_a \longmapsto (X_a, FX_a) \end{array}$$

We have shown in theorem 4.47 and theorem 4.51 that both projections are Barton trivial fibrations. $\square$

It will be essential to highlight that there is a diagonal functor which is a Barton trivial fibration, making the lower triangle commutative.

**Corollary 4.53.** Let $F : \mathcal{M} \rightarrow \mathcal{M}$ be a left Quillen equivalence. There exists a Barton trivial fibration $P : \mathcal{N}_F^I \rightarrow \mathcal{M}$.

*Proof.* Theorem 4.52 can be further specialized to a diagram

$$\begin{array}{ccc} \mathcal{M}^J & \longrightarrow & \mathcal{N}_F^I \\ \Big\downarrow & & \Big\downarrow^{\pi_1} \\ \mathcal{M}_{\overline{(Id_{\mathcal{M}})}} \xrightarrow{\mathcal{M}} \mathcal{M} \end{array}$$

from which we see that there is a functor $P : \mathcal{N}_F^I \rightarrow \mathcal{M}$. This is an immediate consequence of theorem 4.52. $\square$

#### 4.4 Proof of main theorem

**Theorem 4.54.** Let $F : \mathcal{M} \rightleftarrows \mathcal{N} : G$ a Quillen equivalence. Then, for any cofibrant object $A \in \mathcal{M}$. The induced map $h \mathbb{L} F_A : h \mathbb{L}_\lambda^{\mathcal{M}}(A) \rightarrow h \mathbb{L}_\lambda^{\mathcal{N}}(FA)$ is an isomorphism.

88

Proof. Recall from theorem 4.8 that for any cofibrant object $A$ the induced map $h\mathbb{L}F_A$ is injective. Remains to show that it is surjective. Using theorem 4.53, we obtain a diagram

![img-60.jpeg](img-60.jpeg)

where $P$ is a Barton trivial fibration. $P : \mathcal{N}_F^I \to \mathcal{M}$ induces, for any cofibrant object $X \in \mathcal{N}_F^I$, an isomorphism $(h\mathbb{L}\pi_1)_X : h\mathbb{L}_{\lambda}^{\mathcal{N}_F^I}(X) \to h\mathbb{L}_{\lambda}^{\mathcal{M}}(\pi_1 X)$. Indeed, this follows from theorem 4.16. Similarly, the map $(h\mathbb{L}\pi_2)_X : h\mathbb{L}_{\lambda}^{\mathcal{N}_F^I}(X) \to h\mathbb{L}_{\lambda}^{\mathcal{N}}(\pi_2 X)$ is an isomorphism of $\lambda$-boolean algebras. For $A \in \mathcal{M}^{\mathrm{COF}}$ cofibrant we can get a correspondence in $C_{FA} \in \mathcal{N}_F^I$ with all objects $FA$ and maps the identities. We can conclude that $h\mathbb{L}F_A$ is surjective by chasing through the maps $(h\mathbb{L}\pi_2)_{C_A}$ and $(h\mathbb{L}P)_{C_A}$ which we already know are isomorphisms.

It is an immediate that:

Corollary 4.55. For any Quillen equivalence $F : \mathcal{M} \rightleftarrows \mathcal{N} : G$. The functors $Ho(F) \circ h\mathbb{L}_{\lambda}^{\mathcal{M}}$ and $h\mathbb{L}_{\lambda}^{\mathcal{N}} : Ho(\mathcal{N}) \to \mathbf{Bool}_{\lambda}$ are naturally isomorphic via $h\mathbb{L}F$.

### A Infinitary Cartmell theories

We introduce a generalization of Cartmell theories, also known as generalized algebraic theories, Cartmell [Car78]. This is straightforward and most of the proofs will be omitted since they are similar to those in [Car78]. In very few cases we will need to provide new proofs. We claim no originality other than the generalization itself. We begin by recalling some definitions given in Ibid. We assume to have a set of variables $V$ whose size is $\aleph_0$ and an alphabet $A$. Informally, a Cartmell generalized algebraic theory consists of:

i) A set \(S\), called the set of sort symbols,
ii) A set \(O\), called the set of operation symbols,
iii) An introductory rule for each sort symbol,
iv) An introductory rule for each operation symbol,

89

v) A set of axioms.

To understand our generalization let us examine the previous definition in more detail, for this we need some preliminary notions. An *expression* is a finite sequence of $A \cup V \cup \{\{\} \cup \{\}\} \cup \{,\}$. Inductively:

i) Elements of $V$ and $A$ are expressions,
ii) If $f \in A$ and $e_1, e_2, ..., e_n$ are expressions, then $f(e_1, e_2, ..., e_n)$ is an expression.

The set of expressions is denoted by $E$. This is simply to say that an expression is a finite string taken from the set $A \cup V \cup \{\{\} \cup \{\}\} \cup \{,\}$. A *premise* is a finite (possibly empty) sequence of $V \times E$. A *conclusion* is an n-tuple of expressions, i.e. any element of $E^n$ for some $n \in \mathbb{N}$. Finally, a *rule* is given by a premise $P$ and a conclusion $C$. Rules are written as: $P \vdash C$. This intends to convey the idea that under the premise $P$, the conclusion $C$ is a valid expression. Whenever $P$ is a premise we will write $x_1 : \Delta_1, x_2 : \Delta_2, ..., x_n : \Delta_n$. For a conclusion, this is slightly more involved since we differentiate depending on the size of the tuple. For example, if we have a 1-tuple $\Delta$, then we write $\Delta_{\text{Type}}$. We favour the notation “:” from type theory instead of the set theoretic one “$\epsilon$” used by Cartmell. Furthermore, we will take advantage of conventions and notation from type theory.

The most important definition we will need to change is that of a *context*. In a Cartmell theory, a *context* is the premise such that a rule

$$x_1 : \Delta_1, x_2 : \Delta_2(x_1), ..., x_n : \Delta_n(x_1, x_2, \cdots, x_{n-1}) \vdash \Delta(x_1, x_2, \cdots, x_n) \text{ Type}$$

is a *derived rule*.

The only difference between Cartmell theories and infinitary Cartmell theories is that in we allow infinitely many variables in the contexts. Just as any Cartmell theory gives rise to a contextual category, the same is true for the infinitary case with the appropriate generalized version of a contextual category.

### A.1 Generalized algebraic theories

In this section, we give the formal definition of an infinitary Cartmell theory. We follow Cartmell [Car78] to develop the theory; however, there will be some instances where a change has to be made. We could say that by

90

changing in the definition every instance of “finite” by “size strictly less than $\kappa$” we get the correct notion, this is indeed the case. We carve out the definition with a fair amount of detail, since the applications we have in mind benefit from having an explicit syntax. The technicalities and motivations for introducing a generalized algebraic in the following way are presented in Cartmell [Car78].

From now on, we fix a regular cardinal $\kappa$, unless otherwise stated, all other ordinals mentioned will be strictly smaller than $\kappa$.

Let $V$ be a set such that $|V| = \kappa$, this set will be called the set of *variables*. We make an additional assumption on this set: Its elements have *canonical names*, this is $V = \{x_\alpha\}_{\alpha < \kappa}$. This is also known as an *enumeration*. This is a minor assumption that allows to change variables. Otherwise, we would need to prove a result similar to [Car78, Corollary, pp 1.32]$^5$. Let $A$ be any set, which as before is called *alphabet*. Following [Car78] we define inductively the collection of *expressions* $A^*$ over the alphabet $A$. An expression is any $\lambda$-sequence of $A \cup V \cup \{\{\} \cup \{\}\} \cup \{,\}$ subject to:

i) If $x_\alpha \in V$ then $x_\alpha \in A^*$,
ii) If $F \in A$ then $F \in A^*$,
iii) If $F \in A$ and $\{e_\alpha\}_{\alpha < \lambda} \subseteq A^*$ then $F(e_\alpha)_{\alpha < \lambda} \in A^*$.

A *premise* is any $\lambda$-sequence of $V \times A^*$. We will usually write premises as $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ where $x_\alpha$ are variables and $\Delta_\alpha$ are expressions for $\alpha < \lambda$. Suppose we have a premise $\Gamma$, or later a *context*, and we need an extra premise (or *context*), according to our variable numbering, formally, we must write $\Gamma$, $\{x_\alpha : \Delta_\alpha\}_{\lambda \leq \alpha < \mu}$, where $\lambda$ represents the number of variables in $\Gamma$. This is clearly a problem when the expression complexity increases. In order to avoid overloading the notation, we choose to reset the variable counting to only the essential variables in use. Under this convention, we will write $\Gamma$, $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ instead. We will freely assume that $\Gamma$ is a premise unless otherwise specified.

**Definition A.1.** A *judgment* is an expression over the alphabet $A$ that has one of the following forms:

1. Type judgment: $\Gamma \vdash \Delta \text{ Type}$.
2. Element judgment: $\Gamma \vdash t : \Delta$.

5This result states that under the substitution property the derived rules are stable under substitution of variables by another variables

91

3. Type equality judgment: $\Gamma \vdash \Delta \equiv \Delta'$.
4. Term equality judgment: $\Gamma \vdash t \equiv_\Delta t'$.

where $\Gamma$ is a premise.

Given a premise $\Gamma$, $\{e_\alpha\}_{\alpha < \lambda}$ expression and $\{x_\alpha\}_{\alpha < \lambda}$ variables then the new expression

$$\Gamma[e_\alpha | x_\alpha]_{\alpha < \lambda}$$

it is obtained by simultaneously changing the variables in $\Gamma$ by the expressions. This process, unsurprisingly, is called *substitution* of variables. Along with the infinitary substitutions, we will also allow operations to have possibly infinite arity. This is made explicit:

**Definition A.2.** A $\kappa$-*pretheory* $T$ consists of the following data:

i) A set $S$, called the set of *sort symbols*,
ii) A set $O$, called the set of *operation symbols*,
iii) For each sort symbol $B$, a judgment of the form:

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash B(x_\alpha)_{\alpha < \lambda} \text{ Type}$$

where $\lambda$ is some ordinal strictly smaller than $\kappa$,

iv) For each operator symbol $F$, a judgment:

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash F(x_\alpha)_{\alpha < \lambda} : \Delta$$

where $\lambda$ is an ordinal strictly smaller than $\kappa$,

v) A set of judgments, each of which is either a type equality judgment or a term equality judgment, listed in theorem A.1. This is the set of *axioms* of the $\kappa$-pretheory.

The following definitions are of inductive nature:

**Definition A.3.** 1. A premise $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a *context* if the judgment

$$\{x_\beta : \Delta_\beta\}_{\beta < \alpha} \vdash \Delta_\alpha \text{ Type}$$

is a *derived judgment* of $T$ for every $\alpha < \lambda$. Whenever we want to specify that a premise $\Gamma$ is a context we will write $\vdash \Gamma \text{ Ctxt}$.

92

2. The judgment

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type}$$

is a *well-formed judgment* of $T$ if and only if $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context.

3. The judgment

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta$$

is *well-formed* if and only if

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type}$$

is a *derived judgment* of $T$.

**Definition A.4.** Let $T$ be a $\kappa$-pretheory. The set of *derived judgments* of $T$ are the ones that can be derived from the following list of rules:

1.

$$\frac{\Gamma \vdash A \text{ Type}}{\Gamma \vdash A \equiv A}$$

2.

$$\frac{\Gamma \vdash t : A}{\Gamma \vdash t \equiv_A t}$$

3.

$$\frac{\Gamma \vdash A_1 \equiv A_2}{\Gamma \vdash A_2 \equiv A_1}$$

4.

$$\frac{\Gamma \vdash t_1 \equiv_A t_2}{\Gamma \vdash t_2 \equiv_A t_1}$$

5.

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad \Gamma \vdash A_2 \equiv A_3}{\Gamma \vdash A_1 \equiv A_3}$$

6.

$$\frac{\Gamma \vdash t_1 \equiv_A t_2 \quad \Gamma \vdash t_2 \equiv_A t_3}{\Gamma \vdash t_1 \equiv_A t_3}$$

93

7.

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad \Gamma \vdash t_1 \equiv_{A_1} t_2}{\Gamma \vdash t_2 \equiv_{A_2} t_1}$$

8.

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad \Gamma \vdash t : A_1}{\Gamma \vdash t : A_2}$$

9.

$$\frac{\Gamma, \{x_\delta : A_\delta\}_{\delta < \beta < \lambda} \vdash A_\beta \text{ Type}}{\Gamma, \{x_\alpha : A_\alpha\}_{\alpha < \lambda} \vdash x_\alpha : A_\alpha}$$

10. For any $B$ sort symbol with a well-formed introduction type judgment:

$$\frac{\{x_\alpha : A_\alpha\}_{\alpha < \lambda} \vdash B(x_\lambda) \text{ Type}, \quad \vdash \Gamma \text{ Ctxt}, \quad \Gamma \vdash t_\alpha : B[t_\alpha | x_\alpha]}{\Gamma \vdash B(t_\lambda) \text{ Type}}$$

11. For any $F$ operator symbol with a well-formed introduction type element judgment:

$$\frac{\Gamma, \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash F(x_\lambda) : \Delta, \quad \Gamma \vdash t_\alpha : \Delta_\alpha[t_\alpha | x_\alpha]}{\Gamma, \{t_\alpha : \Delta_\alpha[t_\alpha | x_\alpha]\}_{\alpha < \lambda} \vdash F(t_\lambda) : \Delta[t_\lambda | x_\lambda]}$$

12.

$$\begin{array}{c} \vdash \Gamma \text{ Ctxt} \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta' \\ \Gamma, t_\alpha : \Delta_\alpha[t_\beta | x_\beta]_{\beta < \alpha}, t'_\alpha : \Delta'_\alpha[t'_\beta | x_\beta]_{\beta < \alpha} \vdash t_\alpha \equiv_{\Delta_\alpha[t_\beta | x_\beta]_{\beta < \alpha}} t'_\alpha \\ \hline \Gamma, \{t_\alpha : \Delta_\alpha[t_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda}, \{t'_\alpha : \Delta'_\alpha[t'_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda} \\ \vdash \Delta[t_\alpha | x_\alpha]_{\alpha < \lambda} \equiv \Delta'[t'_\alpha | x_\alpha]_{\alpha < \lambda} \end{array}$$

13.

$$\begin{array}{c} \vdash \Gamma \text{ Ctxt} \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t' \\ \Gamma, s_\alpha : \Delta_\alpha[s_\beta | x_\beta]_{\beta < \alpha}, s'_\alpha : \Delta_\alpha[s'_\beta | x_\beta]_{\beta < \alpha} \vdash s_\alpha \equiv_{\Delta_\alpha[s'_\beta | x_\beta]_{\beta < \alpha}} s'_\alpha \\ \hline \Gamma, \{s_\alpha : \Delta_\alpha[s_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda}, \{s'_\alpha : \Delta_\alpha[s'_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda} \\ \vdash t[s_\alpha | x_\alpha]_{\alpha < \lambda} \equiv_{\Delta[s_\alpha | x_\alpha]_{\alpha < \lambda}} t'[s'_\alpha | x_\alpha]_{\alpha < \lambda} \end{array}$$

94

14. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta'$ is an axiom then

$$\frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type} \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta' \text{ Type},}{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta'}$$

15. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t'$ is an axiom then

$$\frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t' : \Delta}{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t'}$$

We are now ready for the following:

**Definition A.5.** A $\kappa$-pretheory $T$ is *well-formed* if all its rules are well-formed. A *generalized $\kappa$-algebraic theory* is a well-formed $\kappa$-pretheory.

*Remark A.6.* Observe that a generalized algebraic theory as defined by Cartmell [Car78] is the same as an $\omega$-generalized algebraic theory in our sense.

We introduce an important example of $\kappa$-algebraic theories.

**Example A.7.** Let *Cat* denote the $\omega$-algebraic theory defined in the following way:

1. Type of objects: $\vdash$ **Ob Type**.
2. Type of morphisms: $x : \mathbf{Ob}, y : \mathbf{Ob} \vdash \mathbf{Hom}(x, y)$ **Type**.
3. Composition operation: $x : \mathbf{Ob}, y : \mathbf{Ob}, z : \mathbf{Ob}, f : \mathbf{Hom}(x, y), g : \mathbf{Hom}(y, z) \vdash g \circ f : \mathbf{Hom}(x, z)$.
4. Identity operator: $x : \mathbf{Ob} \vdash \mathsf{id}_x : \mathbf{Hom}(x, x)$.

Subject to the following axioms:

$$\frac{x : \mathbf{Ob}, y : \mathbf{Ob}, f : \mathbf{Hom}(x, y)}{\mathsf{id}_y \circ f \equiv f} \quad \frac{x : \mathbf{Ob}, y : \mathbf{Ob}, f : \mathbf{Hom}(x, y)}{f \circ \mathsf{id}_x \equiv f}$$
$$\frac{x : \mathbf{Ob}, y :: \mathbf{Ob}, z : \mathbf{Ob}, w : \mathbf{Ob}, f : \mathbf{Hom}(x, y), g : \mathbf{Hom}(y, z), h : \mathbf{Hom}(z, w)}{(h \circ g) \circ f \equiv h \circ (g \circ f)}$$

95

## A.2 Substitution property

Let $T$ be a generalized $\kappa$-algebraic theory. Recall that given $\Delta$, $\{t_\alpha\}_{\alpha < \lambda}$ expressions and $\{x_\alpha\}_{\alpha < \lambda}$ variables, then the new expression $\Delta[e_\alpha|x_\alpha]_{\alpha < \lambda}$ denotes the substitution of variables by the expressions.

**Definition A.8.** Let $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ be a derived judgment of $T$. We say that this judgment has the *substitution property* if for every $\vdash \Gamma$ Ctxt and expressions $\{t_\alpha\}_{\alpha < \lambda}$, such that for all $\alpha < \lambda$

$$\Gamma, \{t_\beta : \Delta_\beta[t_\gamma|x_\gamma]_{\gamma < \beta}\}_{\beta < \alpha} \vdash t_\alpha : \Delta_\alpha[t_\beta|x_\beta]_{\beta < \alpha}$$

are derived rules, then

$$\Gamma \vdash \Delta[t_\alpha|x_\alpha]_{\alpha < \lambda}$$

is a derived rule of $T$.

In [Car78] it is proven that all derived judgment of a generalized algebraic theory satisfy the substitution property. This is done through a series of results that can be generalized to our setting. The proofs are omitted since they are the same as in the original reference.

**Lemma A.9.** If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ is a derived judgment of $T$, then the variables that appear in $\Delta$ is a subset of $\{x_\alpha\}_{\alpha < \lambda}$

*Proof.* See [Car78, Lemma 1, Section 1.7]. $\square$

**Lemma A.10.** 1. *The premise of a derived judgment is a context.*

2. If $\vdash \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ Ctxt then for $\alpha < \lambda$, we have

$$\{x_\beta : \Delta_\beta\}_{\beta < \alpha} \vdash \Delta_\alpha \text{ Type}$$

*Proof.* See [Car78, Lemma 2, Section 1.7]. $\square$

**Theorem A.11.** *Every derived judgment of a generalized $\kappa$-algebraic theory has the substitution property.*

*Proof.* The same proof as in [Car78, 1.7] applies. This goes by proving that each judgment has the substitution property. For the last two judgments in theorem A.1, this is a consequence of rules (11) and (12) in theorem A.4. While for the first two it is done by induction on the derivations. It is shown that each derivation rule of theorem A.4 preserve the substitution property. $\square$

96

This result has similar consequences of those in [Car78]. The proofs are analogous or the same. For us, it is only relevant to know that our generalized $\kappa$-algebraic theories are well-defined. That is:

**Proposition A.12.** *The derived judgments of a generalized $\kappa$-algebraic theory are well-formed.*

*Proof.* Again, by induction on the derivations [Car78, pp. 1.33]. $\square$

Both the statement and proof of the next lemma are the same as The Derivation Lemma [Car78, pp. 1.34]. The proof does not rely on the context size.

**Lemma A.13.** 1. *Every derived type judgment of $T$ is of the form*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash A(t_\alpha)_{\alpha < \lambda}$$

*for some type symbol $A$ with introductory rule*

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash A(x_\alpha)_{\alpha < \lambda} \text{ Type}$$

*and $\{t_\alpha\}_{\alpha < \lambda}$ are expressions such that for all $\alpha < \lambda$ the rule*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \Delta_\alpha[t_\delta \mid x_\delta]_{\delta < \alpha}.$$

2. *Every term element judgment of $T$ is of the form*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash x_\beta : \Omega$$

*for some $x_\beta$ and such that $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega_\beta \equiv \Omega$, or is of the form*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash f(t_\alpha)_{\alpha < \lambda} : \Omega$$

*for some operator symbol $f$ of $T$ with introductory judgment of the form*

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash f(x_\alpha)_{\alpha < \lambda} : \Delta$$

*such that for each $\alpha < \lambda$ the rules*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \Delta_\alpha[t_\delta \mid x_\delta]_{\delta < \alpha}$$

*and*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Delta[t_\alpha \mid x_\alpha]_{\alpha < \lambda} \equiv \Omega$$

*are derived rules of $T$.*

*Proof.* This follows from theorem A.4 (10) and (11). $\square$

97

### A.3 Equivalence relation on judgments

Throughout this section we work in a generalized $\kappa$-algebraic theory. We first introduce a relation that allows us to identify contexts which express the same meaning, but differ on the variables that are used in them [Car78, 1.13].

There is a relation defined on the judgments of the generalized $\kappa$-algebraic theory $T$.

**Definition A.14.** Let $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \vdash \Delta_\lambda \text{ Type}$ and $\{x_\beta : \Omega_\beta\}_{\beta<\mu} \vdash \Omega_\mu \text{ Type}$ be two type judgments of $T$. We say that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \vdash \Delta_\lambda \text{ Type} \approx \{x_\beta : \Omega_\beta\}_{\beta<\mu} \vdash \Omega_\mu \text{ Type}$$

if either:

1. Both ordinals are successor such that $\lambda = \mu = \nu + 1$ and for all $\alpha \leq \nu$ we have

$$\{x_\delta : \Delta_\delta\}_{\delta<\alpha} \vdash \Delta_\alpha \equiv \Omega_\alpha$$

is a derived rule of $T$.

2. Both ordinals are limit ordinals with $\lambda = \mu$ and for any successor ordinal $\nu + 1 < \lambda$ we have

$$\{x_\alpha : \Delta_\alpha\}_{\alpha<\nu} \vdash \Delta_\nu \text{ Type} \approx \{x_\beta : \Omega_\beta\}_{\beta<\nu} \vdash \Omega_\nu \text{ Type}.$$

**Lemma A.15.** *The relation $\approx$ is an equivalence relation on type judgments of the theory $T$.*

*Proof.* This is an immediate result since we have assumed canonical names for variables. Otherwise, we could repeat the argument as in [Car78, 1.13].

$\square$

**Definition A.16.** Let $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}$ and $\{x_\beta : \Omega_\beta\}_{\beta<\mu}$ be two contexts. We say that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \approx \{x_\beta : \Omega_\beta\}_{\beta<\mu}$$

if and only if $\lambda = \mu$ and for all $\alpha < \lambda$

$$\{x_\delta : \Delta_\delta\}_{\delta<\alpha} \vdash \Delta_\alpha \text{ Type} \approx \{x_\gamma : \Omega_\gamma\}_{\gamma<\alpha} \vdash \Omega_\alpha \text{ Type}$$

It follows that this induces an equivalence relation on contexts.

98

**Definition A.17.** We say that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta \approx \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash s : \Omega$$

if and only if $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type} \approx \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega \text{ Type}$ and $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv s$.

*Remark A.18.* Let $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ and $\{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be two contexts. Assume further that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x_\beta : \Omega_\beta\}_{\beta < \mu}.$$

Then for all derived rules

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega,$$

the rule

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Omega$$

is also a derived rule.

Regardless of its simplicity, this remark is useful in the next:

**Corollary A.19.** *The relation $\approx$ is an equivalence relation on judgments of the form $\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash t : \Delta$.*

*Proof.* Reflexivity is a consequence of 2 from theorem A.4. Assume that $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta \approx \{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash s : \Omega$. Hence, the contexts satisfy $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda}$. Applying the symmetry of the relation $\approx$ to contexts, and using theorem A.18, we see that $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash t \equiv s$. Then we must have $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash s : \Delta$ and $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash \Omega \equiv \Delta$. We can apply 4 from theorem A.4 to conclude that $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash s \equiv t$, thus proving symmetry. Transitivity is a straightforward application of theorem A.18. $\square$

**Definition A.20.** A *morphism* between contexts

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \rightarrow \{x_\beta : \Omega_\beta\}_{\beta < \mu}$$

is $\mu$-sequence of terms $\{t_\beta\}_{\beta < \mu}$ such that for all $\beta < \mu$ we have

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\beta : \Omega_\beta [t_\gamma | x_\gamma]_{\gamma < \beta}.$$

99

Just as in the finite case, with the substitution as composition and the obvious identity, it can be shown that contexts form a category with morphisms as defined above. This is called the *category of realizations* of the theory $T$. The composition of

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$$

and

$$\langle s_\delta \rangle_{\delta < \nu} : \{x_\beta : \Omega_\beta\}_{\beta < \mu} \to \{x_\delta : \Omega'_\delta\}_{\delta < \nu}$$

is the map

$$\langle s_\delta \rangle_{\delta < \nu} \circ \langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\delta : \Omega'_\delta\}_{\delta < \nu}$$

defined as the sequence $\langle s_\delta [\langle t_\beta | x_\beta \rangle_{\beta < \mu}] \rangle_{\delta < \nu}$.

Using the previous relation $\approx$ on contexts and rules we induce one on morphisms between contexts. If we have morphisms

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu} \text{ and } \langle t'_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta'_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega'_\beta\}_{\beta < \mu}$$

Then

$$\langle t_\beta \rangle_{\beta < \mu} \approx \langle t'_\beta \rangle_{\beta < \mu}$$

if and only if

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \approx \{x'_\beta : \Omega'_\beta\}_{\beta < \mu}$$

and for all $\gamma < \mu$

$$\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash t_\gamma : \Omega_\gamma [t_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma} \approx \{x_\beta : \Delta'_\beta\}_{\beta < \mu} \vdash t'_\gamma : \Omega'_\gamma [t'_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma}.$$

Unfolding the definition this means that

$$\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash \Omega_\gamma [t_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma} \text{ Type} \approx \{x_\beta : \Delta'_\beta\}_{\beta < \mu} \vdash \Omega'_\gamma [t'_{\gamma'} | x_{\gamma'}]_{\gamma' < \gamma} \text{ Type}$$

and that $\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash t_\gamma \equiv t'_\gamma$ for all $\gamma < \mu$.

The following remarks are results from [Car78] whose proofs are completely similar. However, it is important to make them explicit, since they imply that we can define a composition operation of equivalence classes of morphisms between contexts.

*Remark* A.21. Let $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ and $\langle t'_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega'_\beta\}_{\beta < \mu}$ two morphisms between contexts with $\langle t_\beta \rangle_{\beta < \mu} \approx \langle t'_\beta \rangle_{\beta < \mu}$.

100

1. If $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega \text{ Type}$ and $\{x_\beta : \Omega'_\beta\}_{\beta < \mu} \vdash \Omega' \text{ Type}$ are derived judgment of the theory such that

$$\{x_\beta : \Omega_\beta, x_\mu : \Omega\}_{\beta < \mu} \approx \{x_\beta : \Omega'_\beta, x_\mu : \Omega'\}_{\beta < \mu}$$

then

$$\{x_\alpha : \Delta_\alpha, x_\mu : \Omega[t_\beta|x_\beta]_{\beta < \mu}\}_{\alpha < \lambda} \approx \{x_\alpha : \Delta'_\alpha, x_\mu : \Omega'[t'_\beta|x'_\beta]_{\beta < \mu}\}_{\alpha < \lambda}$$

This follows by unwinding the relation $\approx$ and applying the principle 12 in theorem A.4. This simply means that we can extend contexts by a fresh variable. Moreover, there is a more general result:

For all $\varepsilon > 0$, if $\{x_\beta : \Omega_\beta\}_{\beta < \mu + \varepsilon}$ and $\{x_\beta : \Omega'_\beta\}_{\beta < \mu + \varepsilon}$ are contexts then

$$\{x_\alpha : \Delta_\alpha, x_\beta : \Omega_\beta[t_\gamma|x_\gamma]_{\gamma < \beta}\}_{\substack{\alpha < \lambda, \\ \mu \leq \beta < \mu + \varepsilon}} \approx \{x_\alpha : \Delta'_\alpha, x_\beta : \Omega'_\beta[t'_\gamma|x_\gamma]_{\gamma < \beta}\}_{\substack{\alpha < \lambda, \\ \mu \leq \beta < \mu + \varepsilon}}$$

2. If $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash s : \Omega$ and $\{x_\beta : \Omega'_\beta\}_{\beta < \mu} \vdash s' : \Omega'$ are derived judgment such that

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash s \equiv_\Omega s'.$$

Then

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash s[t_\beta|x_\beta]_{\beta < \mu} \equiv_{\Omega[t_\beta|x_\beta]_{\beta < \mu}} s'[t'_\beta|x_\beta]_{\beta < \mu}.$$

Observe that the principle 13 from theorem A.4 implies this result.

*Remark A.22.* 1. Let $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be a morphism between two contexts. If

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda} \text{ and } \{x_\beta : \Omega_\beta\}_{\beta < \mu} \approx \{x'_\beta : \Omega'_\beta\}_{\beta < \mu}$$

then $\langle t_\beta \rangle_{\beta < \mu} : \{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda} \to \{x'_\beta : \Omega'_\beta\}_{\beta < \mu}$ is also a morphism between these contexts.

2. If we have a context $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 1}$ and $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda}$ then we can extend the context $\{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda}$ to $\{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda + 1}$ such that $x'_\alpha : \Delta'_\alpha$ is $x_\lambda : \Delta_\lambda$.

*Remark A.23.* Let $\langle t_\beta \rangle_{\beta < \mu + 1} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu + 1}$ and $\langle s_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be morphisms between contexts. Then we have a morphism

$$\langle s_\beta \rangle_{\beta < \mu + 1} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu + 1}$$

where $s_\mu \equiv t_\mu$, and such that $\{s_\beta\}_{\beta < \mu + 1} \approx \{t_\beta\}_{\beta < \mu + 1}$.

101

#### A.4 The category of generalized $\kappa$-algebraic theories

We construct a category where the objects are generalized $\kappa$-algebraic theories with maps *interpretations*. This is analogous to the category that Cartmell constructs in [Car78, 1.11], all the results can be copied from there to our setting. Since we work with different theories, the alphabets, expressions and rules are marked accordingly. If $T$ is a theory then these sets are denoted $Alp(T)$, $Exp(T)$, $Rul(T)$ respectively.

Let $T$ and $T'$ two generalized $\kappa$-algebraic theories. Let $I: Alp(T) \rightarrow Exp(T')$ be a function. Using this function, we can define a *preinterpretation* $\bar{I}: Exp(T) \rightarrow Exp(T')$ by induction on the construction of expressions:

1. If $x \in V$

$$\bar{I}(x) := x,$$

2. If $F \in Alp(T)$

$$\bar{I}(F) := I(F),$$

3. If $L \in Alp(T)$ is an alphabet symbol and $\{t_\alpha\}_{\alpha < \lambda}$ are expressions

$$\bar{I}(L(t_\alpha)_{\alpha < \lambda}) := I(L)(\bar{I}(t_\alpha))_{\alpha < \lambda}.$$

**Definition A.24.** Given a preinterpretation $\bar{I}$ we define a new function $\hat{I}: Rul(T) \rightarrow Rul(T')$.

1. $\hat{I}(\Gamma \vdash \Delta \text{ Type}) := \bar{I}(\Gamma) \vdash \bar{I}(\Delta) \text{ Type}$
2. $\hat{I}(\Delta \vdash t : \Delta) := \bar{I}(\Delta) \vdash \bar{I}(t) : \bar{I}(\Delta)$
3. $\hat{I}(\Delta, \Delta' \vdash \Delta \equiv \Delta') := \bar{I}(\Delta), \bar{I}(\Delta') \vdash \bar{I}(\Delta) \equiv \bar{I}(\Delta').$
4. $\hat{I}(\Delta, t, t' : \Delta \vdash t \equiv_\Delta t') := \bar{I}(\Delta), \bar{I}(t), \bar{I}(t') : \bar{I}(\Delta) \vdash \bar{I}(t) \equiv_{\bar{I}(\Delta)} \bar{I}(t').$

This function is an *interpretation* from $T$ into $T'$ if all introductory judgments and axioms of $T$ are sent to derived rules of $T'$, we will simply denote this as $I: T \rightarrow T'$.

Just as in [Car78] it is possible to prove that:

**Lemma A.25.** *If $I$ is an interpretation from $T$ to $T'$, then it preserves the derived judgments of the theory $T$.*

102

Proof. From Lemma 2 [Car78, pp 1.52]. To illustrate how this is done, we show that the derived judgment theorem A.4 (13) it is preserved by I. Consider the derived judgment

$$\begin{array}{r l r} & & {\vdash \Gamma \mathsf {C t x t} \qquad \{x _ {\alpha}: \Delta_ {\alpha} \} _ {\alpha <   \lambda} \vdash t \equiv_ {\Delta} t ^ {\prime}} \\ & & {\Gamma , s _ {\alpha}: \Delta_ {\alpha} [ s _ {\beta} \mid x _ {\beta} ] _ {\beta <   \alpha}, s _ {\alpha} ^ {\prime}: \Delta_ {\alpha} [ s _ {\beta} ^ {\prime} \mid x _ {\beta} ] _ {\beta <   \alpha} \vdash s _ {\alpha} \equiv_ {\Delta_ {\alpha} [ s _ {\beta} ^ {\prime} | x _ {\beta} ] _ {\beta <   \alpha}} s _ {\alpha} ^ {\prime}} \\ & & {\hline \Gamma , \{s _ {\alpha}: \Delta_ {\alpha} [ s _ {\beta} \mid x _ {\beta} ] _ {\beta <   \alpha} \} _ {\alpha <   \lambda}, \{s _ {\alpha} ^ {\prime}: \Delta_ {\alpha} [ s _ {\beta} ^ {\prime} \mid x _ {\beta} ] _ {\beta <   \alpha} \} _ {\alpha <   \lambda}} \\ & & {\quad \vdash t [ s _ {\alpha} \mid x _ {\alpha} ] _ {\alpha <   \lambda} \equiv_ {\Delta [ s _ {\alpha} | x _ {\alpha} ] _ {\alpha <   \lambda}} t ^ {\prime} [ s _ {\alpha} ^ {\prime} \mid x _ {\alpha} ] _ {\alpha <   \lambda}} \end{array}$$

in the theory T. We may assume that the context Γ is of the form {x_β : Ω_β}_{β<μ}, so we get

$$\begin{array}{r l r} & & {\vdash \{x _ {\beta}: \Omega_ {\beta} \} _ {\beta <   \mu} \mathsf {C t x t} \qquad \{x _ {\alpha}: \Delta_ {\alpha} \} _ {\alpha <   \lambda} \vdash t \equiv_ {\Delta} t ^ {\prime}} \\ & & {\{x _ {\beta}: \Omega_ {\beta} \} _ {\beta <   \mu}, s _ {\alpha}: \Delta_ {\alpha} [ s _ {\beta} \mid x _ {\beta} ] _ {\beta <   \alpha}, s _ {\alpha} ^ {\prime}: \Delta_ {\alpha} [ s _ {\beta} ^ {\prime} \mid x _ {\beta} ] _ {\beta <   \alpha} \vdash s _ {\alpha} \equiv_ {\Delta_ {\alpha} [ s _ {\beta} ^ {\prime} | x _ {\beta} ] _ {\beta <   \alpha}} s _ {\alpha} ^ {\prime}} \\ & & {\hline \{x _ {\beta}: \Omega_ {\beta} \} _ {\beta <   \mu}, \{s _ {\alpha}: \Delta_ {\alpha} [ s _ {\beta} \mid x _ {\beta} ] _ {\beta <   \alpha} \} _ {\alpha <   \lambda}, \{s _ {\alpha} ^ {\prime}: \Delta_ {\alpha} [ s _ {\beta} ^ {\prime} \mid x _ {\beta} ] _ {\beta <   \alpha} \} _ {\alpha <   \lambda}} \\ & & {\quad \vdash t [ s _ {\alpha} \mid x _ {\alpha} ] _ {\alpha <   \lambda} \equiv_ {\Delta [ s _ {\alpha} | x _ {\alpha} ] _ {\alpha <   \lambda}} t ^ {\prime} [ s _ {\alpha} ^ {\prime} \mid x _ {\alpha} ] _ {\alpha <   \lambda}} \end{array}$$

Applying the I to the hypothesis and by theorem A.26 we obtain the following derivations in T'.

$$\begin{array}{l} \bullet \vdash \{x _ {\beta}: \widetilde {I} (\Omega_ {\beta}) \} _ {\beta <   \mu} \mathsf {C t x t}, \\ \bullet \{x _ {\alpha}: \widetilde {I} (\Delta_ {\alpha}) \} _ {\alpha <   \lambda} \vdash \widetilde {I} (t) \equiv_ {\Delta} \widetilde {I} (t ^ {\prime}), \\ \bullet \{x _ {\beta}: \widetilde {I} (\Omega_ {\beta}) \} _ {\beta <   \mu}, s _ {\alpha}: \widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta}) \mid x _ {\beta} ] _ {\beta <   \alpha}, \widetilde {I} (s _ {\alpha} ^ {\prime}): \widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta} ^ {\prime}) \mid x _ {\beta} ] _ {\beta <   \alpha} \vdash \widetilde {I} (s _ {\alpha}) \equiv_ {\widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta} ^ {\prime}) | x _ {\beta} ] _ {\beta <   \alpha}} \widetilde {I} (s _ {\alpha} ^ {\prime}). \end{array}$$

We have all the requirements to use theorem A.4 (13) for the theory T'. Thus,

$$\begin{array}{r l r} & & {\vdash \{x _ {\beta}: \widetilde {I} (\Omega_ {\beta}) \} _ {\beta <   \mu} \mathsf {C t x t} \qquad \{x _ {\alpha}: \widetilde {I} (\Delta_ {\alpha}) \} _ {\alpha <   \lambda} \vdash \widetilde {I} (t) \equiv_ {\Delta} \widetilde {I} (t ^ {\prime})} \\ & & {\{x _ {\beta}: \widetilde {I} (\Omega_ {\beta}) \} _ {\beta <   \mu}, s _ {\alpha}: \widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta}) \mid x _ {\beta} ] _ {\beta <   \alpha}, \widetilde {I} (s _ {\alpha} ^ {\prime}): \widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta} ^ {\prime}) \mid x _ {\beta} ] _ {\beta <   \alpha}} \\ & & {\quad \vdash \widetilde {I} (s _ {\alpha}) \equiv_ {\widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta} ^ {\prime}) | x _ {\beta} ] _ {\beta <   \alpha}} \widetilde {I} (s _ {\alpha} ^ {\prime})} \\ & & {\hline \{x _ {\beta}: \widetilde {I} (\Omega_ {\beta}) \} _ {\beta <   \mu}, \{\widetilde {I} (s _ {\alpha}): \widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta}) \mid x _ {\beta} ] _ {\beta <   \alpha} \} _ {\alpha <   \lambda}, \{\widetilde {I} (s _ {\alpha} ^ {\prime}): \widetilde {I} (\Delta_ {\alpha}) [ \widetilde {I} (s _ {\beta} ^ {\prime}) \mid x _ {\beta} ] _ {\beta <   \alpha} \} _ {\alpha <   \lambda}} \\ & & {\quad \vdash \widetilde {I} (t) [ \widetilde {I} (s _ {\alpha}) \mid x _ {\alpha} ] _ {\alpha <   \lambda} \equiv_ {\widetilde {I} (\Delta) [ \widetilde {I} (s _ {\alpha}) | x _ {\alpha} ] _ {\alpha <   \lambda}} \widetilde {I} (t ^ {\prime}) [ \widetilde {I} (s _ {\alpha} ^ {\prime}) \mid x _ {\alpha} ] _ {\alpha <   \lambda}} \end{array}$$

is a derived rule of T'. Therefore, the rule is preserved by the interpretation I.

□

The following lemma fills the gap:

103

**Lemma A.26.** *If $I$ is an interpretation of $T$ into $T'$ and we have expressions $f$ and $\{t_\alpha\}_{\alpha<\lambda}$ on the alphabet $A_T$, then*

$$\widetilde{I}(f[t_\alpha \mid x_\alpha]_{\alpha<\lambda}) = \widetilde{I}(f)[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda}.$$

*Proof.* This is done by induction on the length of $f$ in [Car78, Lemma 1, pp. 1.52]. The interesting case is when $f = F(e_\beta)_{\beta<\mu}$ for some $F$ in the alphabet and expressions $\{e_\beta\}_{\beta<\mu}$. We assume inductively the result true for the expressions $\{e_\beta\}_{\beta<\mu}$. Then we have:

$$\begin{aligned} \widetilde{I}(f[t_\alpha \mid x_\alpha]_{\alpha<\lambda}) &= \widetilde{I}(F(e_\beta[t_\alpha \mid x_\alpha]_{\alpha<\lambda})_{\beta<\mu}) \\ &= I(F)(\widetilde{I}(e_\beta[t_\alpha \mid x_\alpha]_{\alpha<\lambda}))_{\beta<\mu} \\ &= I(F)(\widetilde{I}(e_\beta)[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda})_{\beta<\mu}, \text{ by induction hypothesis} \\ &= I(F)(\widetilde{I}(e_\beta))_{\beta<\mu}[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda} \\ &= \widetilde{I}(F(e_\beta)_{\beta<\mu})[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda} \\ &= \widetilde{I}(f)[\widetilde{I}(t_\alpha) \mid x_\alpha]_{\alpha<\lambda} \end{aligned}$$

□

There is also a notion of composition of interpretations: If $I : S \rightarrow T$ and $J : T \rightarrow U$ are interpretations, then there is an interpretation $J \circ I : S \rightarrow U$ that is defined in the obvious way. It is also easy to infer what is the identity for this composition. A crucial result to define these compositions is:

**Lemma A.27.** *If $I : S \rightarrow T$ and $J : T \rightarrow U$ are interpretations then $\widetilde{J \circ I}(e) = \widetilde{J}(\widetilde{I}(e))$*

*Proof.* This is by induction of the expression $e$ see [Car78, Lemma 3, pp. 1.55]. □

We can define the category $\kappa$-GAT of $\kappa$-generalized algebraic theories. There is an equivalence relation on interpretations between two theories $T$ and $T'$. If $I, J : T \rightarrow T'$ are two interpretations, then $I \approx J$ if an only if for every rule $r \in R_U$ we have $I(r) \approx J(r)$ in the theory $T'$.

**Lemma A.28.** *If $I$ and $J$ are interpretations from $T$ to $T'$ such that $I \approx J$ then for all type and element judgments $\mathcal{J}$ of $U$, $\widetilde{I}(\mathcal{J}) \approx \widetilde{J}(\mathcal{J})$ in $T'$.*

*Proof.* See [Car78, Lemma 1, Section 1.14]. □

□

104

Then theorem A.28 implies that the compositions as given is well-defined. Finally, in order to get the correct morphisms, we need to know that the equivalence relation on interpretations is compatible with the composition. Another advantageous consequence is that this it gives us criteria to establish whether two interpretations are equivalent.

**Corollary A.29.** *If $I$ and $J$ are interpretations from $T$ to $T'$ then $I \approx J$ if and only if for any type element judgment $r$, $\widehat{I}(r) \approx \widehat{J}(r)$.*

*Proof.* This follows from theorem A.28 and (3) of theorem A.3. $\square$

**Corollary A.30.** *If $I$ and $J$ are interpretations from $T$ to $T'$ and $I'$ and $J'$ are interpretations from $T'$ to $T''$ then from $I \approx J$ and $I' \approx J'$ we conclude that $I' \circ I \approx J' \circ J$.*

*Proof.* [Car78, pp. 1.72]. $\square$

The category $\kappa$-GAT has morphisms equivalence classes of interpretations [Car78, pp. 1.72].

### A.5 Construction and properties of the syntactic category $\mathbb{C}_T$

Let $T$ be a generalized $\kappa$-algebraic theory. The category $\mathbb{C}_T$ has the following data:

- Objects: Equivalence classes of contexts under the relation $\approx$. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context then the object in $\mathbb{C}_T$ is denoted $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$.
- Morphisms: A morphism between $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$ and $[\{x_\beta : \Omega_\mu\}_{\beta < \mu}]$ is the equivalence class of a map

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$$

induced by the relation $\approx$. We denote this set by

$$\hom_{\mathbb{C}_T}([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}], [\{x_\beta : \Omega_\mu\}_{\beta < \mu}]).$$

- Composition: This is induced by the composition of maps between contexts. This is again well-defined in view of 2 of theorem A.21.
- Identity: For a context $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ its identity is the equivalence class of the obvious map $\langle x_\alpha \rangle_{\alpha < \lambda}$.

105

*Remark A.31.* The category $\mathbb{C}_T$ has a unique object $1 := [\emptyset]$, the equivalence class of the empty context. Note that this is a terminal object.

*Remark A.32.* Let $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$ be an object of $\mathbb{C}_T$. Then for any $\mu < \lambda$ we get a morphism $[\langle x_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \rightarrow [\{x_\beta : \Delta_\beta\}_{\beta < \mu}]$. Indeed, since $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context then for any $\beta < \lambda$ we have $\{x_\beta : \Delta_\beta\}_{\beta < \beta} \vdash \Delta_\beta$ Type. Therefore, it follows from (theorem A.4, 9) that $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash x_\alpha : \Delta_\alpha$ for all $\alpha < \lambda$. In particular this is true for all $\beta < \mu$, which gives the morphism above.

Following the same argument, if $\nu < \mu$, then we also have a map $[\langle x_\gamma \rangle_{\gamma < \nu}] : [\{x_\beta : \Delta_\beta\}_{\beta < \mu}] \rightarrow [\{x_\gamma : \Delta_\gamma\}_{\gamma < \nu}]$. Furthermore, we get a commutative diagram:

$$\begin{array}{ccc} [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] & \xrightarrow{[\langle x_\beta \rangle_{\beta < \mu}]} & [\{x_\beta : \Delta_\beta\}_{\beta < \mu}] \\ & \searrow [\langle x_\gamma \rangle_{\gamma < \nu}] & \downarrow [\langle x_\gamma \rangle_{\gamma < \nu}] \\ & & [\{x_\gamma : \Delta_\gamma\}_{\gamma < \nu}] \end{array}$$

*Remark A.33.* Since these morphisms are somewhat canonical we will use the notation “ $\rightarrow$ ”, and whenever we use this arrow for a morphism it must be assumed that such map is of this form. These morphisms are called display, which is Cartmell's terminology. In contrast, our 'display' maps can be of arbitrary length, which we will often refer to as *generalized display* maps.

Suppose there is a context $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + \varepsilon}]$ with $\varepsilon \geq 0$. Then we can consider an $\varepsilon$-indexed sequence of display morphisms:

$$\cdots \quad [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 2}] \longrightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 1}] \longrightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$$

Also, there is a display map $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + \varepsilon}] \rightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$. This display morphism will be by definition the composition for the sequence. If $\varepsilon = 0$, then this map is simply the identity. We also get a factorization of the map $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \rightarrow 1$ via display maps for any $\lambda \geq 0$.

*Observation A.34.* From the previous theorem A.32 we can observe that if $\lambda$ is a limit ordinal then $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$ is the limit of the sequence

$$\cdots \quad [\{x_1 : \Delta_1, x_2 : \Delta_2\}] \longrightarrow [\{x_1 : \Delta_1\}] \longrightarrow 1.$$

If there is another context $[\{x_\delta : \Gamma_\delta\}_{\delta < \gamma}]$ and maps

$$[\langle t_\beta \rangle_{\beta < \alpha}] : [\{x_\delta : \Gamma_\delta\}_{\delta < \gamma}] \rightarrow [\{x_\beta : \Delta_\beta\}_{\beta < \alpha}]$$

106

for all $\alpha < \lambda$ then we can simply take the map

$$[\langle t_\alpha \rangle_{\alpha < \lambda} : [\{x_\delta : \Gamma_\delta\}_{\delta < \gamma}] \rightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}].$$

This can be shown to be the cone map (which is unique). This verifies our claim.

Using theorem A.32 we can define a function:

$$\nu : Ob(\mathbb{C}_T) \longrightarrow \kappa$$

as $\nu([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]) := \lambda$. We call this the *length function*. We can use $\nu$ to construct a filtration on the objects of $\mathbb{C}_T$: we define

$$Ob_\lambda(\mathbb{C}_T) := \nu^{-1}(\lambda)$$

then $Ob(\mathbb{C}_T) = \coprod_{\lambda < \kappa} Ob_\lambda(\mathbb{C}_T)$, and so if $\alpha \leq \beta$ then $Ob_\alpha(\mathbb{C}_T) \subseteq Ob_\beta(\mathbb{C}_T)$. Furthermore, if $p : A \rightarrow B$ is a display morphism, then $\nu(B) \leq \nu(A)$. For $\alpha < \beta$ there are functions

$$\pi_\beta : Ob_\beta(\mathbb{C}_T) \rightarrow Ob_\alpha(\mathbb{C}_T)$$

that are defined in the obvious way. Additionally, $1 \in Ob_0(\mathbb{C}_T)$ is unique.

The proof of the following lemma is the same as in [Car78].

**Lemma A.35.** *The pullback of a display map along arbitrary morphisms in $\mathbb{C}_T$ exists, and it is also display.*

*Proof.* We use induction over the context length. Assume we have the following diagram in $\mathbb{C}_T$:

$$\begin{array}{c} [\{x_\beta : \Omega_\beta\}_{\beta < \mu+1}] \\ \downarrow [\langle x_\beta \rangle_{\beta < \mu}] \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \xrightarrow{[\langle t_\beta \rangle_{\beta < \mu}]} [\{x_\beta : \Omega_\beta\}_{\beta < \mu}] \end{array}$$

Then the pullback is given using theorem A.21, and the context is

$$[\{x_\alpha : \Delta_\alpha, x_\mu : \Omega_\mu[t_\beta \mid x_\beta]_{\beta < \mu}\}_{\alpha < \lambda}].$$

Therefore we have a commutative square

$$\begin{array}{c} [\{x_\alpha : \Delta_\alpha, x_\mu : \Omega_\mu[t_\beta \mid x_\beta]_{\beta < \mu}\}_{\alpha < \lambda}] \xrightarrow{[\langle t_\beta, x_\mu \rangle_{\beta < \mu}]} [\{x_\beta : \Omega_\beta\}_{\beta < \mu+1}] \\ [\langle x_\alpha \rangle_{\alpha < \lambda}] \downarrow \downarrow [\langle x_\beta \rangle_{\beta < \mu}] \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \xrightarrow{[\langle t_\beta \rangle_{\beta < \mu}]} [\{x_\beta : \Omega_\beta\}_{\beta < \mu}] \end{array} \quad (2)$$

107

Note that by definition the left vertical morphism is also display. If there is another commutative square

$$\begin{array}{c} [\{x_{\zeta}:\Gamma_{\zeta}\}_{\zeta<\xi}] \xrightarrow{[\langle g_{\beta}\rangle_{\beta<\mu+1}]} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\mu+1}] \\ [\langle f_{\alpha}\rangle_{\alpha<\lambda}] \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [\{x_{\alpha}:\Delta_{\alpha}\}_{\alpha<\lambda}] \xrightarrow{[\langle t_{\beta}\rangle_{\beta<\mu}]} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\mu}], \end{array}$$

the map

$$[\langle f_{\alpha},g_{\mu}\rangle_{\alpha<\lambda}]:[\{x_{\zeta}:\Gamma_{\zeta}\}_{\zeta<\xi}] \to [\{x_{\alpha}:\Delta_{\alpha}, x_{\mu}:\Omega_{\mu}[t_{\beta} \mid x_{\beta}]_{\beta<\mu}\}_{\alpha<\lambda}]$$

shows that the square (2) is the pullback.

Next, assume that we have a diagram

$$\begin{array}{c} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\mu}] \\ \Big\downarrow [\langle x_{\beta}\rangle_{\beta<\mu}] \\ [\{x_{\alpha}:\Delta_{\alpha}\}_{\alpha<\lambda}] \xrightarrow{[\langle t_{\beta}\rangle_{\beta<\nu}]} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\nu}] \end{array}$$

where $\mu$ is a limit ordinal and $\mu > \nu$. We simplify the notation as follows:

$$\begin{array}{c} B_{\mu} \\ \Big\downarrow \\ A_{\lambda} \xrightarrow[\langle t_{\beta}\rangle_{\beta<\nu}]{} B_{\nu} \end{array}$$

Assume that the factorization of the map $B_{\mu} \twoheadrightarrow B_{\nu}$ is of the form

$$\dots \twoheadrightarrow B_{\nu+2} \twoheadrightarrow B_{\nu+1} \twoheadrightarrow B_{\nu}$$

and therefore $B_{\mu}$ is the limit (obtained similarly as in theorem A.34 and theorem A.32). Then we can take the successive pullback

$$\begin{array}{c} f^{*}B_{\mu} \xrightarrow{q(f,B_{\mu})} B_{\mu} \\ \vdots \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ q(f,B_{\nu+1})^{*}B_{\nu+2} \xrightarrow{q(q(f,B_{\nu+1}),B_{\nu+2})} B_{\nu+2} \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ f^{*}B_{\nu+1} \xrightarrow{q(f,B_{\nu+1})} B_{\nu+1} \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A_{\lambda} \xrightarrow{f} B_{\nu} \end{array} \tag{3}$$

108

where at each successor stage it is given as before, $f := \langle t_\beta \rangle_{\beta < \nu}$, the context

$$f^* B_\mu := [\{x_\alpha : \Delta_\alpha, x_\beta : \Omega_\beta[t_\delta \mid x_\delta]_{\delta < \beta}\}_{\substack{\alpha < \lambda \\ \nu < \beta < \mu}}]$$

is the limit of the sequence on the left-hand side, with the obvious display maps to each object in the sequence, and

$$q(f, B_\mu) := [\langle t_\beta, x_\gamma \rangle_{\beta < \nu < \gamma < \mu}].$$

This makes the outer rectangle in (3) commutative. Moreover, the map $q(f, B_\mu)$ is the unique cone map induced by the family of maps

$$\{[\langle t_\beta, x_\gamma \rangle_{\beta < \nu < \gamma < \delta} : f^* B_\mu \to B_\delta\}_{\nu < \delta < \mu}.$$

Using the same notation as in the lemma above, we have:

Remark A.36. 1. If $f = Id_{B_\nu}$ then $(Id_{B_\nu})^* B_\mu = B_\mu$ and $q(Id_{B_\nu}, B_\mu) = Id_{B_\mu}$.

2. For a diagram

$$D \xrightarrow{g} C \xrightarrow{f} B,$$

we have that $g^*(f^*(A)) = (fg)^*(A)$ and $q(fg, A) = q(f, A)(g, f^*A)$.

We will refer to the category $\mathbb{C}_T$ as the syntactic category associated to the generalized $\kappa$-algebraic theory $T$.

Observation A.37. We note that theorem A.35 give us an explicit construction of pullbacks in $\mathbb{C}_T$, as well as the pullback of the maps and an explicit description of $q(f, B_\mu)$.

We finish this section by characterizing the display maps in the category $\mathbb{C}_T$. This result says that display maps are somehow generic. We start with a preparatory result.

Lemma A.38. Let $T$ be a generalized $\kappa$-algebraic theory and $\mathbb{C}_T$ its syntactic $\kappa$-contextual category. Assume that there is a $f : \Delta \to \Gamma$, then any display map $B \twoheadrightarrow \Delta$ of length 1 can be obtained as a pullback of the form

$$\begin{array}{c} B \longrightarrow \Gamma' \\ \downarrow \quad \downarrow \\ \Delta \xrightarrow{f} \Gamma \end{array}$$

109

where $\Gamma' \rightarrow \Gamma$ is of length 1.

*Proof.* This is simply a reformulation of theorem A.13. Assume that

$$f = [\langle t_\beta \rangle_{\beta < \mu} ] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \rightarrow [\{x_\beta : \Gamma_\beta\}_{\beta < \mu}].$$

Therefore, when the display map is of the form

$$[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda+1}] \rightarrow [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}].$$

We can construct the square

$$\begin{array}{ccc} [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda+1}] & \xrightarrow{\langle t_\beta, x_\lambda \rangle_{\beta < \mu}} & [\{x : \Gamma_\beta, x_\lambda : \Delta_\lambda\}_{\beta < \mu}] \\ \downarrow & & \downarrow \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] & \xrightarrow{\langle t_\beta \rangle_{\beta < \mu}} & [\{x : \Gamma_\beta\}_{\beta < \mu}]. \end{array}$$

Since for all $\beta < \mu$, $x_\beta$ does not occur in $\Delta_\lambda$ we have that $\Delta_\lambda[t_\beta|x_\beta]_{\beta < \mu} \equiv \Delta_\lambda$. Hence, it follows from the construction of pullbacks in $\mathbb{C}_T$ (theorem A.35) that the square above is indeed a pullback diagram. $\square$

We are ready to give the full description of display maps.

**Proposition A.39.** *Every display map $B \rightarrow \Delta$ in $\mathbb{C}_T$ is a limit of a $\kappa$-small tower $V : \lambda \rightarrow \mathbb{C}_T$ where for each limit ordinal $\beta < \lambda$*

$$V(\beta) = \text{Lim}_{\alpha < \beta} V(\alpha)$$

*and the map $V(\alpha + 1) \rightarrow V(\alpha)$ is a pullback of a length one display map of the form $(\Gamma, A) \rightarrow \Gamma$ where $\Gamma \vdash A$ Type is a type axiom of the theory $T$.*

*Proof.* Each display map in $\mathbb{C}_T$ has a length $\lambda$. Just as in theorem A.32 it admits a decomposition into display maps. It will be enough to prove the second claim, and this follows by an inductive argument in conjunction with the previous theorem A.38. The inductive step provides us with the required map $f : V(\alpha) \rightarrow \Gamma$ in theorem A.38. $\square$

## B Contextual categories and Cartmell theories

This section is the most relevant part. We will show that from the syntax of a generalized $\kappa$-algebraic theory we can construct a category, called $\kappa$-contextual category, which we now introduce.

110

## B.1 $\kappa$-contextual categories

The discussion in section A.5 on the properties of the syntactic category $\mathbb{C}_T$ can be summarized with the next definition, which is the natural generalization of Cartmell's [Car78] or [KL18]. We present our definition in the same way as in the latter reference. Recall that $\kappa$ is a regular cardinal.

**Definition B.1.** A category $\mathcal{C}$ is said to be a $\kappa$-contextual category if:

1. The objects of $\mathcal{C}$ have grading $Ob(\mathcal{C}) = \coprod_{\lambda < \kappa} Ob_\lambda(\mathcal{C})$. This grading determines the *height* of any object $B \in \mathcal{C}$, which we write as $ht(B)$.
2. There is a terminal object $1 \in \mathcal{C}$, it is unique up to equality and has height 0.
3. There is a wide subcategory $Dis(\mathcal{C})$ with distinguished maps “$\twoheadrightarrow$” called *display morphisms*,
4. The subcategory $Dis(\mathcal{C})$ is closed under transfinite compositions: if we have

$$\cdots \longrightarrow B_3 \longrightarrow B_2 \longrightarrow B_1 \longrightarrow B_0$$

a $\lambda$-sequence of display maps, then there is a unique object $B$ in $Dis(\mathcal{C})$ with height $\lambda$ and for each $\mu \leq \lambda$ a display map $B \twoheadrightarrow B_\mu$ such that for any $\alpha < \lambda$ we have a factorization

$$\begin{array}{c} B \xrightarrow{} B_0 \\ \searrow B_\alpha \end{array}$$

5. The inclusion functor preserves $i : Dis(\mathcal{C}) \hookrightarrow \mathcal{C}$ transfinite compositions.
6. If $A \twoheadrightarrow B$ is an arrow in $Dis(\mathcal{C})$ then $B \in Ob_\mu(\mathcal{C})$ and $A \in Ob_\lambda(\mathcal{C})$ for some ordinals $\lambda, \mu$ with $\mu \leq \lambda$.
7. For any object $A \in Ob_\lambda(\mathcal{C})$ and any $\mu \leq \lambda$ there exists a unique object $B \in Ob_\mu(\mathcal{C})$ and a unique display map $A \twoheadrightarrow B$. The *length* of this display map is the unique ordinal $\alpha$ such that $\lambda = \mu + \alpha$, is such situation, we write $lt(p)$.

111

8. For any $A \in Ob_\lambda(\mathcal{C})$, a map $A \twoheadrightarrow B$ and any map $f: C \to B$ there is a pullback square

$$\begin{array}{ccc} f^*A & \xrightarrow{q(f,A)} & A \\ f^*p \downarrow & & \downarrow^p \\ C & \xrightarrow{f} & B \end{array}$$

called *canonical pullback* of $A$ along $f$, and we require $lt(f^*p) = lt(p)$.

9. Canonical pullbacks are strictly functorial: for ordinals with $\mu \leq \lambda$, $A \in Ob_\lambda(\mathcal{C})$

- (a) If $f = id_B$ then $id_B^*A = A$ and $q(id_B, A) = id_A$.
- (b) For a diagram

$$\begin{array}{ccc} & & A \\ & & \downarrow^p \\ D & \xrightarrow{g} & C \xrightarrow{f} & B, \end{array}$$

we have that $g^*(f^*(A)) = (fg)^*(A)$ and $q(fg, A) = q(f, A)q(g, f^*A)$.

10. Given display maps $p: A \twoheadrightarrow B$ and $q: B \to C$ and any $f: X \to C$, in the diagram

$$\begin{array}{ccc} q(f,B)^*A & \xrightarrow{q(q(f,B),A)} & A \\ q(f,B)^*p \downarrow & & \downarrow^p \\ f^*B & \xrightarrow{q(f,B)} & B \\ f^*r \downarrow & & \downarrow^r \\ X & \xrightarrow{f} & C, \end{array}$$

we have that $f^*r \circ (q(f,B)^*p) = f^*(r \circ p)$ and $q(q(f,B), A) = q(f, A)$.

*Remark B.2.* We use the term “display map” in a rather different way to Cartmell. For us, a display map can have any height, and it is only bounded by the regular cardinal $\kappa$.

We have already seen one example of such a category.

**Corollary B.3.** *For any generalized $\kappa$-algebraic theory $T$ the syntactic category $\mathbb{C}_T$ is a $\kappa$-contextual category.*

*Proof.* This is done throughout section A.5. $\square$

112

*Remark B.4.* It follows from theorem B.1 that for any object $B \in \mathcal{C}$ the map $B \rightarrow 1$ can be decomposed as a transfinite composition of display maps

$$B_\lambda \rightarrow \dots \rightarrow B_1 \rightarrow 1.$$

The length of the decomposition above is given by the degree of $B$. This is what [Car78] calls the tree structure of the category. Whenever we refer to objects in a $\kappa$-contextual category as above, we will emphasize its height by writing $B_\lambda$. Likewise, we will denote the display maps as $p_\alpha : B_\lambda \rightarrow B_\alpha$ for each $\alpha < \lambda$.

The following lemma is a consequence of theorem B.1 and theorem B.4.

**Lemma B.5.** *Let $B \in Ob_\lambda(\mathcal{C})$ such that $\lambda$ is a limit ordinal. Then $B$ itself is a limit object in $\mathcal{C}$.*

*Proof.* From theorem A.32 we obtain a sequence

$$\dots \longrightarrow B_3 \longrightarrow B_2 \longrightarrow B_1 \longrightarrow 1.$$

It follows from Axiom 4 of theorem B.1 that $B$ must be the limit of the sequence. Finally, we use that the inclusion $Dis(\mathcal{C}) \rightarrow \mathcal{C}$ preserve limits. $\square$

**Definition B.6.** Let $\mathcal{C}, \mathcal{D}$ contextual categories. A functor $F : \mathcal{C} \rightarrow \mathcal{D}$ it is called a *contextual functor* if it satisfies the following conditions:

1. $F(Ob_\lambda(\mathcal{C})) \subseteq Ob_\lambda(\mathcal{D})$ for all $\lambda < \kappa$,
2. $F$ restricts to a functor $Dis(\mathcal{C}) \rightarrow Dis(\mathcal{D})$,
3. $F$ preserves canonical pullbacks up to equality, meaning that for any square in $\mathcal{C}$

$$\begin{array}{c} f^*A \xrightarrow{q(f,A)} A \\ f^*p \downarrow \quad \downarrow p \\ C \xrightarrow{f} B \end{array}$$

we have $F(f^*A) = (Ff)^*(FA)$ and $F(q(f,A)) = q(Ff, FA)$.

Since the degree of each object is preserved by a $\kappa$-contextual functor, it makes sense to denote $F(A_\lambda) := F(A)_\lambda$ for $A_\lambda \in \mathcal{C}$. Another piece of notation we can introduce is from the functor $F : Dis(\mathcal{C}) \rightarrow Dis(\mathcal{D})$. Since any display map $p_\alpha : A_\lambda \rightarrow A_\alpha$ is sent to a display map $F(p_\alpha) : F(A)_\lambda \rightarrow F(A)_\alpha$, and the degrees are preserved, we agree to omit $F$ on these maps.

Contextual functors are the morphisms of the category of $\kappa$-contextual categories, which we will denote it as $\kappa$-CON.

113

## B.2 Interlude: categorical facts

We collect and recall some categorical facts about general $\kappa$-contextual categories.

**Proposition B.7** (The slice $\kappa$-contextual category). *Let $\mathcal{C}$ be a $\kappa$-contextual category. For any object $B \in Ob_\mu(\mathcal{C})$ there is a $\kappa$-contextual category which is a full subcategory of the slice $\mathcal{C}_{/B}$ which has objects display maps $A \twoheadrightarrow B$ where $A \in Ob_\lambda(\mathcal{C})$ with $\lambda \geq \mu$.*

Since we will rarely use categories other than $\kappa$-contextual categories, we will employ the slice notation $\mathcal{C}_{/B}$ for the category from the previous proposition.

*Proof.* The proof is completely formal. The important fact to remember is that the pullback of a display map is also a display map. $\square$

It is a well known fact that the pasting of two pullbacks give us a pullback, in our case consider the following diagram:

$$\begin{array}{ccc} f^*B_\mu & \xrightarrow{q(f, B_\mu)} & B_\mu \\ \vdots & & \vdots \\ q(f, B_{\nu+1})^*B_{\nu+2} & \xrightarrow{q(q(f, B_{\nu+1}), B_{\nu+2})} & B_{\nu+2} \\ \downarrow & & \downarrow \\ f^*B_{\nu+1} & \xrightarrow{q(f, B_{\nu+1})} & B_{\nu+1} \\ \downarrow & & \downarrow \\ A_\lambda & \xrightarrow{f} & B_\nu \end{array}$$

Then if $\mu$ is a limit ordinal, the object $B_\mu$ is the limit of the sequence on the right-hand side. Thus, $f^*B_\mu$ is the limit of the sequence on the left-hand side. Note that pairwise we have $q(f, B_{\nu+1})^*B_{\nu+2} = f^*B_{\nu+2}$ and $q(f, B_{\mu+2}) = q(q(f, B_{\mu+1}), B_{\mu+2})$.

If $f: A_\lambda \to B_\nu$ and $p_\nu: B_\mu \twoheadrightarrow B_\nu$ is a display map with $\mu = \nu + 1$, using the

114

universal property of the pullback, we can construct the following diagram:

![img-61.jpeg](img-61.jpeg)

The map $\delta_f^\nu$ makes both triangles commutative. We will focus on the fact that $((f_\nu)^*p_\nu)\delta_f^\nu = Id_{A_\lambda}$, where $f_\nu = p_\nu f$. Assume that we have a map $p: B_\mu \to B_\nu$ with $\mu$ a limit ordinal, in particular the length of $p$ is a limit ordinal. Then a map $f: A_\lambda \to B_\mu$ is determinate by a family of maps $\{f_\gamma: A_\lambda \to B_\gamma\}$. Then we obtain:

![img-62.jpeg](img-62.jpeg)

where the map $\delta_f^\nu$ is given as the family of maps $(\delta_f^\nu)_\gamma$, each given by an intermediate pullback square in the diagram above.

Notation B.8. If the situation above, for $f: A_\lambda \to B_\mu$ we denote

$$\Gamma(B_\nu^\mu) := \{h: A_\lambda \to (p_\nu f)^* B_\mu \mid ((p_\nu f)^* p_\nu)h = Id_{A_\lambda}\}.$$

We can consider a more general case, if $A_\lambda \in Ob_\lambda(\mathcal{C})$ and $B_\mu \in Ob_\mu(\mathcal{C})$ with $\lambda < \mu$, then there is a unique display map $p: B_\mu \to A_\lambda$. We set

$$\Gamma(B_\lambda^\mu) := \{s: A_\lambda \to B_\mu \mid ps = Id_{A_\lambda}\}$$

115

for this situation as well, since the object $A_\lambda$ will be inferred from the context.

If the contextual category is $\mathbb{C}_T$, then recalling theorem A.35, we can give an explicit description of the map $\delta_f^\nu$.

**Lemma B.9.** Assume that $f := [\langle t_\beta \rangle_{\beta < \nu}] : [\{x_\alpha : A_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : B_\beta\}_{\beta < \nu}]$ and there is a display map $p : [\{x_\beta : B_\beta\}_{\beta < \mu}] \to [\{x_\beta : B_\beta\}_{\beta < \nu}]$, then $\delta_f^\nu = [\langle x_\alpha, t_\beta \rangle_{\substack{\alpha < \lambda \\ \nu < \beta < \mu}}]$.

*Proof.* This follows by induction on $\mu$ and the explicit construction of pullbacks from theorem A.35. $\square$

In certain situations, the property above characterizes the map $\delta_f^\nu$.

**Lemma B.10.** If $[\{x_\beta : B_\beta\}_{\beta < \mu}]$ is an object of $\mathbb{C}_T$ and $\nu < \mu$ then $f \in \Gamma(B_\nu^\mu)$ if and only if $f = [\langle x_\beta, t_\gamma \rangle_{\beta < \nu < \gamma < \mu}]$, where for all $\nu < \gamma < \mu$, the rule $\{x_\beta : B_\beta\}_{\beta < \nu}, \{t_{\gamma'} : B_{\gamma'}\}_{\gamma' < \gamma} \vdash t_\gamma : B_\gamma$ is a derived rule.

The next result follows from the previous lemma, and is used in theorem B.41.

**Lemma B.11.** Let $A_\lambda, B_\mu$ objects of $\mathcal{C}$ and for each $\beta < \mu$ we have maps $r_{\beta+1} \in \Gamma(r_\beta^* \cdots r_1^* p^* B_{\beta+1})$ then there exists a unique sequence of maps $\{g_\beta : A_\lambda \to B_\beta\}_{\beta < \mu}$ such that for all $\beta < \mu$ we have $p_\beta g_{\beta+1} = g_\beta$ and $\delta_{g_\beta} = r_\beta$.

Some words about the previous lemma are in order. The expression $r_\beta^* \cdots r_1^* p^* B_{\beta+1}$ can be illustrated by the first two steps:

![img-63.jpeg](img-63.jpeg)

### B.3 The equivalence between $\kappa$-GAT and $\kappa$-CON

#### B.3.1 The functor $\mathbb{C} : \kappa$-GAT $\to \kappa$-CON

To establish this equivalence of categories, we first define a functor $\mathbb{C} : \kappa$-GAT $\to \kappa$-CON using the construction of section A.5. The proof again comes from [Car78, Section 2.4.1]. We register all preliminary results needed

116

to define this functor, however again we omit the proofs since they are similar to the original ones given by Cartmell.

On objects $\mathbb{C} : \kappa$-GAT $\to \kappa$-CON is defined as $\mathbb{C}_T$ for $T$ a generalized $\kappa$-algebraic theory. For a map $[I] : T \to T'$ between theories, we need a functor $\mathbb{C}(I) : \mathbb{C}_T \to \mathbb{C}_{T'}$:

1. On objects; $\mathbb{C}(I)([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]) := [\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda}],
2. On morphisms: If $[\langle t_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : \Delta_\beta\}_{\beta < \mu}]$ then $\mathbb{C}(I)([\langle t_\beta \rangle_{\beta < \mu}]) := [\langle \widetilde{I}(\langle t_\beta \rangle_{\beta < \mu})]$.

If there is an interpretation $J$ in the equivalence class $[I]$, then by theorem A.28 any rule $r$ of $T$ we get $\widetilde{I}(r) \approx \widetilde{J}(r)$. Therefore, it follows that the definition of $\mathbb{C}(I)$ does not depend on the representative of $[I]$.

It remains to verify that $\mathbb{C}(I)$ is indeed a contextual functor. Firstly, it is essential to verify that it is well-defined.

**Lemma B.12.** *Let $[I] : T \to T'$ be a map in $\kappa$-GAT then the following hold:*

1. *The interpretation $I$ preserves contexts: If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context in the theory $T$ then $\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda}$ is a context in the theory $T'$.*
2. *The interpretation $I$ preserves the equivalence relation $\approx$ between contexts: If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ and $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda}$ are contexts in the theory $U$ with $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda}$ then $\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda} \approx \{x_\alpha : \widetilde{I}(\Omega_\alpha)\}_{\alpha < \lambda}$.*
3. *The interpretation $I$ preserves morphisms between contexts: If $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ is a morphism between contexts in the theory $T$ then $\langle \widetilde{I}(t_\beta) \rangle_{\beta < \mu} : \{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda} \to \{x_\beta : \widetilde{I}(\Omega_\beta)\}_{\beta < \mu}$ is a morphism between contexts in the theory $T'$.*
4. *The interpretation $I$ preserves the equivalence relation $\approx$ between morphisms of contexts: If $\langle s_\beta \rangle_{\beta < \mu}$, $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ are morphisms between contexts in the theory $T$ with $\langle s_\beta \rangle_{\beta < \mu} \approx \langle t_\beta \rangle_{\beta < \mu}$ then $\langle \widetilde{I}(s_\beta) \rangle_{\beta < \mu} \approx \langle \widetilde{I}(t_\beta) \rangle_{\beta < \mu}$.*

*Proof.* The proof of each statement is consequence of theorem A.26 or theorem A.25. Our enumeration of variables give us a notation simplification of the proof given by [Car78].

For example, to prove 4; we have by assumption that $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\gamma \equiv_{\Omega_\gamma [t_\beta | x_\beta]_{\beta < \gamma}} s_\gamma$ for all $0 < \gamma \leq \mu$. Therefore, since the interpretation preserves this rule $\circ T$ we get that $\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda} \vdash \widetilde{I}(t_\gamma) \equiv_{\widetilde{I}(\Omega_\gamma)[\widetilde{I}(t_\beta)|x_\beta]_{\beta < \gamma}}$

117

$\widetilde{I}(s_\gamma)$ for all $0 < \gamma \leq \mu$. This exactly establishes $\langle \widetilde{I}(s_\beta) \rangle_{\beta < \mu} \approx \langle \widetilde{I}(t_\beta) \rangle_{\beta < \mu}$.

We have seen that the definition of $\mathbb{C}(I)$ give us the correct objects and morphisms. Now we show that it is indeed a contextual functor.

**Lemma B.13.** *Let $I : T \rightarrow T'$ be a morphism in $\kappa$-GAT. Then the map $\mathbb{C}(I) : \mathbb{C}_T \rightarrow \mathbb{C}_{T'}$ is a contextual functor.*

*Proof.* The map is a functor trivially. That it preserves the grading and restricts to a functor between the display subcategories $Dis(\mathbb{C}_T)$ and $Dis(\mathbb{C}_{T'})$ is also immediate. To prove it preserves canonical pullbacks, consider the following pullback square in the category $\mathbb{C}_T$:

$$\begin{array}{ccc} [\{x_\alpha : \Delta_\alpha, x_\gamma : \Omega_\gamma [t_\beta \mid x_\beta]_{\beta < \mu}\} \xrightarrow[\mu \leq \gamma < \mu + \varepsilon]{\{(t_\beta, x_\gamma) \quad \beta < \mu, \quad \}} & [\{x_\beta : \Omega_\beta\}_{\beta < \mu + \varepsilon}] \\ [\{x_\alpha\}_{\alpha < \kappa}] \downarrow & & \downarrow [\{x_\beta\}_{\beta < \mu}] \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \kappa}] & \xrightarrow{[\{t_\beta\}_{\beta < \mu}]} & [\{x_\beta : \Omega_\beta\}_{\beta < \mu}] \end{array}$$

Then a straightforward computation, using the definition of $\mathbb{C}(I)$, shows that this is sent to a pullback square in the category $\mathbb{C}_{T'}$.

**Corollary B.14.** *There is a functor $\mathbb{C} : \kappa\text{-GAT} \rightarrow \kappa\text{-CON}$.*

### B.3.2 The functor $U : \kappa\text{-CON} \rightarrow \kappa\text{-GAT}$

We now turn to construct a functor that associates a generalized $\kappa$-algebraic theory $U(\mathcal{C})$ to each $\kappa$-contextual category $\mathcal{C}$. This is part of [Car78, Section 2.4]. We will use the notation introduced in theorem B.4. This means we identify each object by its height, say $B_\lambda$, and write display maps as $p_\alpha : B_\lambda \rightarrow B_\alpha$ if $\lambda > 0$ and $\alpha < \lambda$. If $\alpha = 0$ then $B_0 = 1$ the terminal object. A morphism $f : A_\lambda \rightarrow B_\mu$ is trivial when $B_\mu$ is trivial, *i.e.*, $\mu = 0$.

**Definition B.15.** We define $U(\mathcal{C}) \in \kappa\text{-GAT}$ as:

1. For each non-trivial object $B_\mu$ with $\mu = \lambda + 1$, there is a type symbol $\overline{B_\mu}$ with the introductory rule: $\{x_\beta : \overline{B_\beta}\}_{\beta < \mu} \vdash \overline{B_\mu}(x_\beta)_{\beta < \mu}$ Type. The notation emphasizes the fact that $\overline{B_\mu}$ depends on the indicated variables.
2. If $f : A_\lambda \rightarrow B_\mu$ is morphism of $\mathcal{C}$ with $\mu = \nu + 1$, we get an operator symbol $\overline{f}$. It has the introductory rule:

118

- If $f: A_\lambda \to B_{\mu+1}$, let $\rho_\mu: B_{\mu+1} \twoheadrightarrow B_\mu$ be the display map. Then the operator symbol has introductory rule:

$$\{x_\alpha: \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{f}(x_\alpha)_{\alpha<\lambda}: \overline{(\rho_\mu f)^* B_{\mu+1}}(x_\alpha)_{\alpha<\lambda}.$$

This does not clash with the notation from the previous point since it always refer to an object of $\mathcal{C}$ and in this case refers to a map.

Subject to the following axioms in $U(\mathcal{C})$:

1. Let $A_\lambda, B_\mu, C_{\nu+1}$ be objects of $\mathcal{C}$ and maps $f: A_\lambda \to B_\mu, g: B_\mu \to C_{\nu+1}$:

$$\{x_\alpha: \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{gf}(x_\alpha)_{\alpha<\lambda} \equiv_{\overline{(p_\nu gf)^* C_{\nu+1}}(x_\alpha)_{\alpha<\lambda}} \overline{g}(\overline{p_\beta f}(x_\alpha)_{\alpha<\lambda})_{\beta<\mu}.$$

2. Let $B_\mu$ be a non-trivial object of $\mathcal{C}$. For each $\delta < \mu$ we have

$$\{x_\beta: \overline{B}_\beta\}_{\beta<\mu} \vdash \overline{p_\delta}(x_\beta)_{\beta<\mu} \equiv_{\overline{B}_\delta(x_\beta)_{\beta<\delta}} x_\delta.$$

3. Let $A_\lambda, B_{\mu+1}$ objects of $\mathcal{C}$ and a map $f: A_\lambda \to B_\mu$ then

$$\{x_\alpha: \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{f^* B_{\mu+1}}(x_\alpha)_{\alpha<\lambda} \equiv \overline{B_{\mu+1}}(\overline{p_\beta f}(x_\alpha)_{\alpha<\lambda})_{\beta<\mu}$$

and

$$\{x_\alpha: \overline{A}_\alpha, x_\delta: \overline{f^* B_{\mu+1}}(x_\alpha)_{\alpha<\lambda}\}_{\alpha<\lambda} \vdash \overline{q(f, B_{\mu+1})}(x_\alpha, x_\delta)_{\alpha<\lambda} \equiv_{\overline{f^* B_\mu}(x_\alpha)_{\alpha<\lambda}} x_\delta.$$

Observation B.16. It is immediate to observe that $U(\mathcal{C})$ as defined is a $\kappa$-pretheory. We have type and operator symbols introduced by the type and type element judgments respectively. Note that the list of axioms we provided are well-formed rules. This is because the premise of each axiom is by definition a context.

Remark B.17. If $f: A_\lambda \to B_\mu$ is a map in $\mathcal{C}$, where $\mu$ is a limit ordinal, i.e., $B_\mu$ is a limit object, then we get a family of maps $\{f_\nu: A_\lambda \to B_\nu\}_{\nu<\mu}$. Therefore, the associated operator $\overline{f}$ is uniquely determined by the family of operators $\overline{f_\nu}$, for which in this case we can assume that $\nu$ is a successor ordinal.

If $F: \mathcal{C} \to \mathcal{D}$ is a functor between $\kappa$-contextual categories, then we need an interpretation $U(F): U(\mathcal{C}) \to U(\mathcal{D})$;

1. For an object $A_\lambda$, the interpretation is defined as

$$U(F)(\overline{A_\lambda}) := \overline{FA_\lambda}(x_\alpha)_{\alpha<\lambda}.$$

119

2. For a morphism $f: A_\lambda \to B_{\mu+1}$, the operator $\overline{f}$ is interpreted as

$$U(F)(\overline{f}) := \overline{F(f)}(x_\alpha)_{\alpha < \lambda}.$$

The next step is to prove that this is indeed a map between the generalized $\kappa$-algebraic theories, this is done in [Car78, pp 2.29]. For this, it is enough to show that rules and axioms of $U(\mathcal{C})$ are sent to rules of $U(\mathcal{D})$. The functoriality of $U: \kappa$-CON $\to \kappa$-GAT is also immediate from its definition. This is tested on each type and operator symbol. It is then enough to take the equivalence class $[U(F)]$.

### B.3.3 The natural isomorphism $U \circ \mathbb{C} \cong Id_{\kappa-GAT}$

For each $T \in \kappa$-GAT we want to define an interpretation $[\varphi_T]: T \to U(\mathbb{C}_T)$, we do this by defining a preinterpretation $\varphi_T: Exp(T) \to Exp(U(\mathbb{C}_T))$:

1. If $\Delta$ is a type symbol of $T$ with introduction rule

$$\{x_\alpha : \Delta_\beta\}_{\beta < \mu} \vdash \Delta(x_\beta)_{\beta < \mu} \text{ Type}$$

then

$$\varphi_T(\Delta) := \overline{[\{x_\beta : \Delta_\beta, x_\delta : \Delta(x_\beta)_{\beta < \mu}\}_{\beta < \mu}]}(x_\beta)_{\beta < \mu}$$

2. If $f$ is an operator symbol with introductory rule

$$\{x_\alpha : \Delta_\beta\}_{\beta < \mu} \vdash f(x_\beta)_{\beta < \mu}: \Delta,$$

then

$$\varphi_T(f) := \overline{[\langle x_\beta, f(x_\beta)_{\beta < \mu} \rangle_{\beta < \mu}]}(x_\beta)_{\beta < \mu},$$

where $\langle x_\beta, f(x_\beta)_{\beta < \mu} \rangle_{\beta < \mu}$ is the morphism $\{x_\alpha : \Delta_\beta\}_{\beta < \mu} \to \{x_\alpha : \Delta_\beta, x_\delta : \Delta\}_{\beta < \mu}$.

We proceed to verify that as defined $\varphi_T: T \to U(\mathbb{C}_T)$ is an interpretation as defined. This is a crucial point in the proof, so we spell out some details in theorem B.26. The results below are the technical steps towards it.

Lemma B.18. If $\mathcal{C}$ is a contextual category, objects $A_\lambda$, $B_\mu$ and $f: A_\lambda \to B_\mu$ is map with $\mu = \nu + 1$ (in particular it is non-trivial), then the rule

$$\{x_\alpha : \overline{A}_\alpha(x_\gamma)_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{f}(x_\alpha)_{\alpha < \lambda}: \overline{B_\mu}(\overline{p_\beta \circ f}(x_\alpha)_{\alpha < \lambda})_{\beta < \mu}$$

is a derived rule of $U(\mathcal{C})$.

120

Proof. We have the axiom

$$\{x_\alpha : \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{f^* B_\mu}(x_\alpha)_{\alpha<\lambda} \equiv \overline{B_\mu}(\overline{p_\beta \circ f}(x_\alpha)_{\alpha<\lambda})_{\beta<\mu}$$

for $U(\mathcal{C})$ and the derivation rule for $\kappa$-GAT

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad t : A_1}{\Gamma \vdash t : A_2}.$$

These put together give us the result.

Lemma B.19. Let $\mathcal{C}$ a $\kappa$-contextual category, objects $\{A_\alpha\}_{\alpha<\lambda}$, $\{B_\beta\}_{\beta<\mu+1}$, $\{C_\gamma\}_{\gamma<\varepsilon}$ and a commutative diagram

$$\begin{array}{c} C_\varepsilon \xrightarrow{\ell} B_{\mu+1} \\ k \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A_\lambda \xrightarrow{\quad f\quad} B_\mu. \end{array}$$

If $h : C_\varepsilon \to f^* B_{\mu+1}$ is the unique map given by the pullback, then the rule

$$\{x_\gamma : \overline{C_\gamma}(x_\delta)_{\delta<\gamma}\}_{\gamma<\varepsilon} \vdash \overline{h}(x_\gamma)_{\gamma<\varepsilon} \equiv \overline{(fk)^* B_{\mu+1}(x_\gamma)_{\gamma<\varepsilon}} \, \overline{l}(x_\gamma)_{\gamma<\varepsilon}$$

is a derived rule of $U(\mathcal{C})$.

Proof. The proof is the same as [Car78, Lemma 2 pp. 2.32] using theorem B.18.

Lemma B.20. Let $\mathcal{C}$ a $\kappa$-contextual category, objects $\{A_\alpha\}_{\alpha<\lambda}$, $\{B_\beta\}_{\beta<\mu}$, $\{C_\gamma\}_{\gamma<\varepsilon}$ and for $0 < \nu < \mu$ a commutative diagram

$$\begin{array}{c} C_\varepsilon \xrightarrow{\iota_\nu} B_\mu \\ k_\nu \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A_\lambda \xrightarrow{\quad f\quad} B_\nu. \end{array}$$

If $h_\nu : C_\varepsilon \to f^* B_\mu$ is the unique map given by the pullback, then the rule

$$\{x_\gamma : \overline{C_\gamma}(x_\delta)_{\delta<\gamma}\}_{\gamma<\varepsilon} \vdash \overline{h_\nu}(x_\gamma)_{\gamma<\varepsilon} \equiv \overline{(fk_\nu)^* B_\mu(x_\gamma)_{\gamma<\varepsilon}} \, \overline{l_\nu}(x_\gamma)_{\gamma<\varepsilon}$$

is a derived rule of $U(\mathcal{C})$.

121

Proof. This by induction on the height of $p_\nu$. When it is a successor ordinal, this is the previous lemma. When it is a limit ordinal $B_\mu$ is a limit object, therefore the result reduces to the inductive hypothesis, which is the successor case again. □

Recall from section B.2 we defined the set of maps $\Gamma(B)$. It follows from the previous result that

Corollary B.21. If $\mathcal{C}$ is a $\kappa$-contextual category and $f: A_\lambda \to B_\mu$ is a map in $\mathcal{C}$, then for all $\nu < \mu$

$$\{x_\alpha: A_\alpha(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{\delta_f^\nu}(x_\alpha)_{\alpha < \lambda} \equiv \overline{f}(x_\alpha)_{\alpha < \lambda}.$$

is a derived rule of $U(\mathcal{C})$.

If we specialize theorem B.21 to the syntactic $\kappa$-contextual category of a generalized $\kappa$-algebraic theory $T$, then

Corollary B.22. Assume that $\{x_\beta: B_\beta\}_{\beta < \mu}$ is a context, $\nu < \mu$ and

$$f_\nu := [\langle t_\beta \rangle_{\beta < \nu}]: [\{x_\alpha: A_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta: B_\beta\}_{\beta < \nu}]$$

a map in $\mathbb{C}_T$ then

$$\{x_\alpha: \overline{A_\alpha}(x_\gamma)_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash [\langle x_\alpha, t_\varepsilon \rangle_{\substack{\alpha < \lambda \\ \nu \leq \varepsilon < \mu}}] \equiv [\langle t_\beta, t_\varepsilon \rangle_{\beta < \nu \leq \varepsilon < \mu}]$$

is a derived rule of $U(\mathbb{C}_T)$.

Proof. This follows from theorem B.21 and the explicit description of $\delta_{f_\nu}^\nu$ given in theorem B.9. □

Lemma B.23. If $A_\lambda, B_\mu$ are objects and $f_\nu: A_\lambda \to B_\nu$, with $\nu < \mu$, is a map in a $\kappa$-contextual category $\mathcal{C}$, then:

1. The rule

$$\{x_\alpha: \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{f_\nu^* B_\mu}(x_\alpha)_{\alpha < \lambda} \equiv \overline{B}(\delta_{(p_\gamma f)}^\gamma(x_\alpha)_{\alpha < \lambda})_{\gamma < \nu}$$

is a derived rule of $U(\mathcal{C})$.

2. If $g: \Gamma(B_\nu^\mu)$ then the rule

$$\{x_\alpha: \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{\delta_{gf}^\nu}(x_\alpha)_{\alpha < \lambda} \equiv \overline{\delta_g^\nu}(\overline{\delta_{p_\gamma f}}^\gamma(x_\alpha)_{\alpha < \lambda})_{\gamma < \nu}$$

is a derived rule of $U(\mathcal{C})$.

122

**Corollary B.24.** If $T$ is a generalized $\kappa$-algebraic theory, $\{x_\beta : B_\beta\}_{\beta < \mu}$ is a context, $\nu < \mu$ and

$$f_\nu := [\langle t_\beta \rangle_{\beta < \nu} ] : [\{x_\alpha : A_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : B_\beta\}_{\beta < \nu}]$$

is a map in $\mathbb{C}_T$ then;

1.

$$\frac{\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda}}{[\{x_\alpha, x_\gamma : B_\gamma[t_\delta|x_\delta]_{\delta < \gamma}\}_{\substack{\alpha < \lambda \\ \nu \leq \gamma < \mu}}\}(x_\alpha)_{\alpha < \lambda} \equiv [\{x_\beta : B_\beta\}_{\beta < \nu}](\overline{g_\beta}(x_\alpha)_{\alpha < \lambda})_{\beta < \nu}}$$

where for each $\beta < \nu$ the map $g_\beta := [\langle x_\alpha, t_\beta \rangle_{\alpha < \lambda}]$.

2. If for all $\gamma$, with $\nu < \gamma < \mu$, the rule

$$\{x_\beta : B_\beta\}_{\beta < \nu}, \{t_{\gamma'} : B_{\gamma'}\}_{\gamma' < \gamma} \vdash t_\gamma : B_\gamma$$

is a derived rule then

$$\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash [\langle x_\alpha, t_\gamma[t_{\gamma'} \mid x_{\gamma'}]_{\gamma' < \gamma} \rangle_{\substack{\alpha < \lambda \\ \nu < \gamma < \mu}}\equiv \overline{h}(\overline{g_\beta}(x_\alpha)_{\alpha < \lambda})_{\beta < \nu}$$

where $g_\beta$ is defined as in the previous point and $h := [\langle x_\beta, t_\gamma \rangle_{\substack{\beta < \nu \\ \nu < \gamma < \mu}}]$.

Proof. This is a direct application of theorem B.23. We remark that the assumption of point (2) simply gives us an element of $\Gamma(B_\nu^\mu)$ and the map on the left depends on variables that, according to our convention, we leave implicit. □

The following lemma is key to prove that we have an interpretation $\varphi_T : T \to U(\mathbb{C}_T)$, the results above are used to prove:

**Lemma B.25.** If $T$ is a generalized $\kappa$-algebraic theory then:

1. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ Type is a type judgment of $T$, then the rule

$$\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{A}(x_\alpha)_{\alpha < \lambda + 1} \equiv \widetilde{\varphi_T}(\Delta)$$

is a derived rule of $U(\mathbb{C}_T)$ where $A := \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 1}$ and $A_\alpha := \{x_\delta : \Delta_\delta\}_{\delta \leq \alpha}$.

2. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta$ is a type element judgment of $T$, then the rule

$$\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{\langle x_\alpha, t \rangle_{\alpha < \lambda}}(x_\alpha)_{\alpha < \lambda + 1} \equiv_{\overline{A}(x_\alpha)_{\alpha < \lambda}} \widetilde{\varphi_T}(t)$$

is a derived rule of $U(\mathbb{C}_T)$.

123

Proof. The proof is by induction on the derivations, by showing that rule derivation preserves the properties above. □

The important result of this section is the following.

Corollary B.26. For every generalized $\kappa$-algebraic theory $T$, the map $\varphi_T: T \to U(\mathbb{C}_T)$ is an interpretation.

Proof. We see that the function $\widehat{\varphi_T}: Rul(T) \to Rul(U(\mathbb{C}_T))$ is well-defined. We start with a rule $\mathcal{J}$ of $T$ and show that $\widehat{\varphi_T}(\mathcal{J})$ is a rule of $U(\mathbb{C}_T)$

1. Type judgment: Assume that $\mathcal{J} := \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ Type is a rule of $T$, from theorem A.24 it follows that

$$\widehat{\varphi_T}(\mathcal{J}) = \{x_\alpha : \widetilde{\varphi}(\Delta_\alpha)\}_{\alpha < \lambda} \vdash \widetilde{\varphi_T}(\Delta) \text{ Type}.$$

From theorem B.25 we have for any $\gamma < \lambda + 1$, the rule

$$\{x_\alpha : \overline{\Delta_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\gamma+1}}(x_\alpha)_{\alpha < \gamma+1} \equiv \widetilde{\varphi_T}(\Delta_\gamma)$$

is a derived rule of $U(\mathbb{C}_T)$. Thus, the following is also a derived rule

$$\{x_\alpha : \widetilde{\varphi_T}(\Delta_\alpha)(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\gamma+1}}(x_\alpha)_{\alpha < \lambda+1} \equiv \widetilde{\varphi_T}(\Delta).$$

Then it must be the case that $\{x_\alpha : \widetilde{\varphi}(\Delta_\alpha)\}_{\alpha < \lambda} \vdash \widetilde{\varphi_T}(\Delta)$ Type is a rule of $U(\mathbb{C}_T)$.

2. Element judgment: $\Gamma \vdash t : \Delta$. This very similar to the previous rule.
3. Type equality judgment: $\Gamma \vdash \Delta \equiv \Delta'$. Also follows from theorem B.25.
4. Term equality judgment: $\Gamma \vdash t \equiv_\Delta t'$. The same argument works.

Corollary B.27. For every generalized $\kappa$-algebraic theory $T$, the map $[\varphi_T]: T \to U(\mathbb{C}_T)$ is morphism in the category $\kappa$-GAT.

Next, we will now show that $[\varphi_-]: Id_{\kappa\text{-GAT}} \Rightarrow U \circ \mathbb{C}$ is a natural transformation.

Lemma B.28. Let $T, T'$ two generalized $\kappa$-algebraic theories and $I: T \to T'$ an interpretation between them. Then, we have a commutative diagram

$$\begin{array}{c} T \xrightarrow{[\varphi_T]} U(\mathbb{C}_T) \\ [I] \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ T' \xrightarrow{[\varphi_{T'}]} U(\mathbb{C}_{T'}). \end{array}$$

124

Proof. We use theorem A.29. It will therefore be enough to test the commutativity of the diagram on type element judgments. Let $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta_\lambda$ a type element judgment of $T$. For any $\alpha \leq \lambda$ we denote $A_\alpha := [\{x_\delta : \Delta_\delta\}_{\delta \leq \alpha}]$. It follows from theorem B.25 that

$$\widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) \approx \frac{\{x_\alpha : \overline{A_\alpha}\}_{\alpha < \lambda}}{[\langle x_\alpha, t \rangle_{\alpha < \lambda}] : \overline{A_\lambda}(x_\alpha)_{\alpha < \lambda}}.$$

We conclude that

$$U(\mathbb{C}(I)) \left( \widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) \right) \approx \frac{\{x_\alpha : \overline{\mathbb{C}(I)(A_\alpha)}\}_{\alpha < \lambda}}{\overline{\mathbb{C}(I)([\langle x_\alpha, t \rangle_{\alpha < \lambda}]) : \overline{\mathbb{C}(I)(A_\lambda)}(x_\alpha)_{\alpha < \lambda}}}.$$

Looking at the other composition: we get

$$\widehat{I} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) = \frac{\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda}}{\widetilde{I}(t) : \widetilde{I}(\Delta_\lambda)}.$$

A second use of theorem B.25 give us that

$$\widehat{\varphi_{T'}} \left( \widehat{I} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) \right) \approx \frac{\{x_\alpha : \overline{B_\alpha}\}_{\alpha < \lambda}}{[\langle x_\alpha, \widetilde{I}(t) \rangle_{\alpha < \lambda}] : \overline{B_\lambda}(x_\alpha)_{\alpha < \lambda}},$$

where for $\alpha \leq \lambda$, $B_\alpha := [\{x_\delta : \widetilde{I}(\Delta_\delta)\}_{\delta \leq \alpha}]$. However, by definition we have $\mathbb{C}(I)(A_\alpha) = B_\alpha$ for $\alpha \leq \lambda$. This completes our verification.

Remains to show that $[\varphi_T]$ is an isomorphism, and natural in $T$. We proceed to give an inverse $\psi_T : U(\mathbb{C}_T) \to T$. Recall that a type symbol of $U(\mathbb{C}_T)$ is of the form $\overline{A_\lambda} = [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$. If $\lambda = \nu + 1$, then by choosing a representative of this equivalence class of the context we can define $\psi_T(\overline{A_\lambda}) := \Delta_\nu$.

If $\lambda$ is a limit ordinal, once we chose a representative, $\Delta_\lambda = \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$. Then we know that $[\Delta_\lambda] = \lim_{\alpha < \lambda} [\Delta_\alpha]$ in $\mathbb{C}_T$, and this limit is unique. In this case, the value of $\psi_T$ is determined by non-limit ordinals $\alpha < \lambda$, which are $\psi_T(\overline{\Delta_\alpha}) = \Delta_\alpha$. Therefore, we define $\psi_T([\overline{\Delta_\lambda}]) := \Delta_\lambda$ for some choice of a representative of the equivalence class. However, note that the successor case determinate the limit case.

Operator symbols of $U(\mathbb{C}_T)$ come from morphisms of $\mathbb{C}_T$. Therefore, for a morphism $\overline{f} := [\langle t_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : \Omega_\beta\}_{\beta < \mu}]$ in order to define $\psi_T$ on the associated operator, it is enough to assume that $\mu$ is a successor ordinal. Firstly, we need to make choices for the contexts and

125

morphism. However, the definition does not depend on these choices because of (1) from theorem A.22. This allows us to define $\psi_T$ as

$$\psi_T(\overline{f}) := t_\mu$$

where $t_\mu : \Omega_\mu[t_\beta|x_\beta]_{\beta<\mu}$.

**Lemma B.29.** *The function $\psi_T$ is an interpretation from $U(\mathbb{C}_T) \to T$.*

*Proof.* We need to check that rules and axioms are preserved by $\psi_T$. It will be enough to deal with the case where $\lambda = \nu + 1$. Suppose that $\overline{A_\lambda}$ has

$$\frac{\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta<\alpha}\}_{\alpha<\nu}}{\overline{A_\nu}(x_\alpha)_{\alpha<\nu} \text{ Type}}$$

Furthermore, we assume that $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}$ is such that $A_\lambda = [\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}]$. By definition,

$$\widehat{\psi_T} \left( \frac{\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta<\alpha}\}_{\alpha<\nu}}{\overline{A_\lambda}(x_\alpha)_{\alpha<\lambda} \text{ Type}} \right) = \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\nu}}{\Delta_\nu \text{ Type}}.$$

This is obviously a derived rule of $T$. Preservation of the rule for operator symbols is straightforward.

**Lemma B.30.** *For any generalized $\kappa$-algebraic theory $T$ we have $\psi_T \circ \varphi_T \approx Id_T$.*

*Proof.* From theorem A.29 it is enough to verify the statement on type element judgments. Let $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \vdash t : \Delta_\lambda$ a type element judgment. For any $\alpha \le \lambda$ we denote $A_\alpha := [\{x_\delta : \Delta_\delta\}_{\delta\le\alpha}]$. It follows from theorem B.25 that

$$\widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}}{t : \Delta_\lambda} \right) \approx \frac{\{x_\alpha : \overline{A_\alpha}\}_{\alpha<\lambda}}{[\langle x_\alpha, t \rangle_{\alpha<\lambda}] : \overline{A_\lambda}(x_\alpha)_{\alpha<\lambda}}.$$

Hence

$$\widehat{\psi_T} \left( \widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}}{t : \Delta_\lambda} \right) \right) \approx \widehat{\psi_T} \left( \frac{\{x_\alpha : \overline{A_\alpha}\}_{\alpha<\lambda}}{[\langle x_\alpha, t \rangle_{\alpha<\lambda}] : \overline{A_\lambda}(x_\alpha)_{\alpha<\lambda}} \right) = \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}}{t : \Delta_\lambda}.$$

$\square$

**Lemma B.31.** *For any generalized $\kappa$-algebraic theory $T$ we have $\psi_T \circ \varphi_T \approx Id_T$.*

126

*Proof.* The proof is similar to the previous lemma. All the definitions and technical results have been established, especially theorem B.25. $\square$

**Corollary B.32.** *There is a natural isomorphism $Id_{\kappa-GAT} \Rightarrow U \circ \mathbb{C}$.*

*Proof.* We have constructed $[\varphi_-]: Id_{\kappa-GAT} \Rightarrow U \circ \mathbb{C}$. $\square$

### B.3.4 The natural isomorphism $\mathbb{C} \circ U \cong Id_{\kappa-CON}$

In this section we aim to construct a natural isomorphism $\eta: Id_{\kappa-CON} \Rightarrow \mathbb{C} \circ U$. Let $\mathcal{C}$ be a $\kappa$-contextual category. For this, we first construct a $\kappa$-contextual functor $\eta_{\mathcal{C}}: \mathcal{C} \rightarrow \mathbb{C}_{U(\mathcal{C})}$. Recall that if $A_\lambda$ is an object in $\mathcal{C}$ then for any $\alpha \leq \lambda$, we denote $p_\alpha: A_\lambda \rightarrow A_\alpha$ as the canonical display map that exists. Then we can make the following definition:

1. For $\eta_{\mathcal{C}}(1) := 1$.
2. If $A_\mu$ is an object with $\mu = \lambda + 1$, then

$$\eta_{\mathcal{C}}(A_\mu) := [\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha \leq \mu}].$$

3. For an object $A_\lambda$, we define $\eta_{\mathcal{C}}(p_0) := \eta_{\mathcal{C}}(p)_0$ where $\eta_{\mathcal{C}}(p)_0: \eta_{\mathcal{C}}(A) \rightarrow 1$.
4. If $A_\lambda, B_\mu$ are non-trivial objects, with $\mu$ a successor ordinal, and $f: A_\lambda \rightarrow B_\mu$ is a morphism in $\mathcal{C}$, then

$$\eta_{\mathcal{C}}(f) := [\langle \overline{p_\beta f}(x_\alpha)_{\alpha < \lambda} \rangle_{\beta \leq \mu}].$$

We observe that if $\mu$ is a limit ordinal, then any map $f: A_\lambda \rightarrow B_\mu$ is determined by a family of maps $\{f_\nu: A_\lambda \rightarrow B_\nu\}_{\nu < \mu}$. Thus, in order to define $\eta$ on such map, it is enough to do it on ordinals $\nu < \mu$ which we can assume to be successor ordinals. The map $\eta(f)$ is the map induced by the family of maps $\{\eta(f_\nu): \eta(A_\lambda) \rightarrow \eta(B_\nu)\}_{\nu < \mu}$. In conclusion, we simply need to prove properties of $\eta$ for successor ordinals; the property for limit ordinals follows using the universal property of the limit object.

**Lemma B.33.** *For any $\mathcal{C}$, $\eta_{\mathcal{C}}: \mathcal{C} \rightarrow \mathbb{C}_{U(\mathcal{C})}$ is a $\kappa$-contextual functor.*

*Proof.* First we verify that it is a functor. Since for any $\alpha < \lambda$ we have $\overline{p_\alpha}(x_\alpha)_{\alpha < \lambda} = x_\alpha$, then it is immediate to see that $\eta_{\mathcal{C}}$ preserves the identities. Assume we have non-trivial morphisms $f: A_\lambda \rightarrow B_\mu$ and $g: B_\mu \rightarrow C_\nu$, then

$$\eta_{\mathcal{C}}(gf) = [\langle \overline{p_\gamma gf}(x_\alpha)_{\alpha < \lambda} \rangle_{\beta \leq \nu}]$$

127

From the first axiom in theorem B.15 of $U(\mathcal{C})$, it follows that the above must be $\eta_{\mathcal{C}}(g)\eta_{\mathcal{C}}(f)$ whenever $\mu$ and $\nu$ are successor ordinals. When we have limits, it follows by the universal property.

Now we must verify that it preserves display maps and canonical pullbacks. Both statements are direct consequences of the definitions. Furthermore, the proof from [Car78] works without mayor changes.

For the preservation of pullbacks: We let $f: A_{\lambda} \to B_{\mu+1}$ then

$$
\begin{aligned}
\eta_{\mathcal{C}}(f^*B) &= [\langle x_{\alpha}: \overline{A_{\delta}}(x_{\gamma})_{\gamma<\alpha}, x_{\epsilon}: \overline{f^*B_{\mu+1}}(x_{\alpha})_{\alpha<\lambda} \rangle_{\alpha<\lambda}] \\
&= [\langle x_{\alpha}: \overline{A_{\delta}}(x_{\gamma})_{\gamma<\alpha}, x_{\epsilon}: \overline{B_{\mu+1}}(\overline{p_{\beta}f}(x_{\alpha})_{\alpha<\lambda})_{\beta<\mu} \rangle_{\alpha<\lambda}] \\
&= [\langle \overline{p_{\beta}f}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}]^*[\langle x_{\beta}: \overline{B_{\beta}}(x_{\gamma})_{\gamma<\beta} \rangle_{\beta\le\mu}] \\
&= \eta_{\mathcal{C}}(f)^*\eta_{\mathcal{C}}(B).
\end{aligned}
$$

For a display map of $p_{\nu}: B_{\mu} \to B_{\nu}$ with height a successor ordinal, the same argument shows that the pullback along $f_{\nu}: A_{\lambda} \to B_{\nu}$ is preserved. When the height is a limit ordinal, we combine the previous case and the fact that in any $\kappa$-contextual category canonical pullbacks are unique. $\square$

**Lemma B.34.** *Let $\mathcal{C}, \mathcal{C}'$ be $\kappa$-contextual categories and a contextual functor $F: \mathcal{C} \to \mathcal{C}'$. Then the following diagram is commutative:*

$$
\begin{array}{ccc}
\mathcal{C} & \xrightarrow{\eta_{\mathcal{C}}} & \mathbb{C}_{U(\mathcal{C})} \\
F \downarrow & & \downarrow \mathbb{C}(U(F)) \\
\mathcal{C}' & \xrightarrow{\eta_{\mathcal{C}'}} & \mathbb{C}_{U(\mathcal{C}')}.
\end{array}
$$

*Proof.* If $f: A_{\lambda} \to B_{\mu}$ is a map in $\mathcal{C}$ then

$$
\begin{aligned}
\mathbb{C}(U(F))(\eta_{\mathcal{C}}(f)) &= \mathbb{C}(U(F))([\langle \overline{p_{\beta}f}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}]) \\
&= [\langle \overline{F(p_{\beta}f)}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}] \\
&= [\langle \overline{p_{\beta}F(f)}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}] \\
&= \eta_{\mathcal{C}'}(Ff).
\end{aligned}
$$

**Corollary B.35.** *There is a natural transformation $Id_{\kappa-CON} \Rightarrow \mathbb{C} \circ U$.*

It remains to show that this natural transformation is an isomorphism. For each $\kappa$-contextual category $\mathcal{C}$ we construct a $\kappa$-contextual functor

$$
\xi_{\mathcal{C}}: \mathbb{C}_{U(\mathcal{C})} \to \mathcal{C}
$$

which is a two-sided inverse to $\eta_{\mathcal{C}}$. From theorem A.13 we see that:

128

1. Every derived type judgment of $U(\mathcal{C})$ is of the form

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{A_\lambda}(t_\alpha)_{\alpha < \lambda} \text{ Type}$$

for some object $A_\lambda$ of $\mathcal{C}$ where for $\alpha \leq \lambda$ the rule

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \overline{A_\alpha}[t_\delta \mid x_\delta]_{\delta < \alpha}$$

is a derived rule of $U(\mathcal{C})$.

2. Every type element judgment of $U(\mathcal{C})$ is of the form

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash x_\beta : \Omega_\beta$$

for some $\beta < \mu$, or is of the form

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{f}(t_\alpha)_{\alpha < \lambda} : \Omega$$

for some map $f : A_\lambda \rightarrow B_\mu$ of $\mathcal{C}$ such that for each $\alpha < \lambda$ the rules

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \overline{A_\alpha}[t_\delta \mid x_\delta]_{\delta < \alpha}$$

and

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{B_\mu}(t_\beta)_{\beta < \mu} \equiv \Omega$$

are derived rules of $U(\mathcal{C})$.

We may assume that $\mu = \nu + 1$, the limit case will follow by induction. Let $\mathcal{R}_\mathcal{C}$ be the set of type and element type judgments of $U(\mathcal{C})$. Next, we define $\mathcal{J} : \mathcal{R}_\mathcal{C} \rightarrow \mathcal{C}$ inductively. First we get maps:

1. A rule $r_{\Omega_\mu} := \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega_\mu$ is sent an object $\mathcal{J}(r_{\Omega_\mu}) \in \mathcal{C}$.
2. For any $\alpha < \lambda$ the judgment $r_{t_\alpha} := \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \overline{A_\alpha}[t_\delta \mid x_\delta]_{\delta < \alpha}$ is sent to a map $\mathcal{J}(r_{t_\alpha})$.

The we can make the following definitions:

1. $\mathcal{J}(r_{A_\mu}) := (\mathcal{J}(t_\alpha)_{\alpha < \lambda})^* A_\mu$,
where $\mathcal{J}(t_\alpha)_{\alpha < \lambda}$ denotes the pullbacks as in theorem B.11.
2. $\mathcal{J}(\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \overline{f}(t_\alpha)_{\alpha < \lambda} : \Omega) := (\mathcal{J}(t_\alpha)_{\alpha < \lambda})^* \delta_f^\nu$.
3. $\mathcal{J}(\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash x_\beta : \Omega_\beta) := \delta_{p_\beta}^\beta$ where $p_\beta : \mathcal{J}(r_{\Omega_\mu}) \rightarrow \mathcal{J}(r_{\Omega_\beta})$.

129

The burden of the proof falls into showing that the function $\mathcal{J}$ is well-defined. The proof is by induction on the derived rules of $U(\mathcal{C})$. We will focus on writing down the inductive hypothesis $H$ as in [Car78] for this induction.

- For rules $r_{\Omega_\mu}$ of the form $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega_\mu \text{ Type}$ then $H(r_{\Omega_\mu})$ is either:

1. If the premise of $r_{\Omega_\mu}$ is a non-empty context then $H(r_{\Omega_\beta})$ for all $\beta < \mu$.
2. If $r_{\Omega_\mu}$ is the rule $\vdash \Delta \text{ Type}$ then $ht(\mathcal{J}(r_{\Omega_\mu})) = 1$. Otherwise, for all $\beta < \mu$ we have $ht(\mathcal{J}(r_{\Omega_\beta})) < ht(\mathcal{J}(r_{\Omega_\mu}))$.
3. For a map $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$. If for each $\beta + 1 < \mu$ we have $\mathcal{J}(r_{t_\beta + 1}) \in \Gamma(\mathcal{J}(r_{\Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta}}))$ where $r_{\Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta}}$ is the rule $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta} \text{ Type}$ then

$$\mathcal{J}(r_{\Omega_\mu[t_\beta|x_\beta]_{\beta < \mu}}) = (\mathcal{J}(t_\beta)_{\beta < \mu})^* \mathcal{J}(r_{\Omega_\mu})$$

- For rules $r_{t_\mu}$ of the form $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\mu : \Omega_\mu$ then $H(r_{t_\mu})$ is either:

1. $H(r_{\Omega_\mu})$.
2. $\mathcal{J}(r_{t_\mu}) \in \Gamma(\mathcal{J}(r_{\Omega_\mu}))$.
3. For a map $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$. If for each $\beta + 1 < \mu$ we have $\mathcal{J}(r_{t_\beta + 1}) \in \Gamma(\mathcal{J}(r_{\Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta}}))$ then

$$\mathcal{J}(r_{t_\mu[t_\beta|x_\beta]_{\beta < \mu}}) = (\mathcal{J}(t_\beta)_{\beta < \mu})^* \mathcal{J}(r_{t_\mu})$$

where $r_{t_\mu[t_\beta|x_\beta]_{\beta < \mu}}$ is the rule $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\mu[t_\beta|x_\beta]_{\beta < \mu} : \Omega_\mu[t_\beta|x_\beta]_{\beta < \mu}$.

- For rules $r_\equiv$ or of the form $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta'$, the hypothesis $H(r_\equiv)$ is either:

1. $H(r_{\Delta'})$ and $\mathcal{J}(r_\Delta) = \mathcal{J}(r_{\Delta'})$.
2. $H(r_\Delta)$ and $\mathcal{J}(r_\Delta) = \mathcal{J}(r_{\Delta'})$.

- For rules $r_\epsilon$ or of the form $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t'$, the hypothesis $H(r_\epsilon)$ is either:

1. $H(r_t)$ and $\mathcal{J}(r_t) = \mathcal{J}(r_{t'})$.
2. $H(r_{t'})$ and $\mathcal{J}(r_t) = \mathcal{J}(r_{t'})$.

130

**Lemma B.36.** Let $\{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu} \vdash \Omega$ a rule such that $H$ is satisfied. If $\langle t_{\beta} \rangle_{\beta < \mu} : \{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \to \{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu}$ is a map such that $H(r_{t_{\beta}})$ for all $\beta < \mu$ then $H(\{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu} \vdash \Omega[t_{\beta}|x_{\beta}]_{\beta < \mu})$

*Proof.* By induction on $\mu$ and treating all the different cases for $H$. The proof in [Car78, Lemma 11 pp.2.56] works here too. $\square$

**Lemma B.37.** 1. For any object $A_{\lambda} \in \mathcal{C}$, we have:

(a) $A\lambda = \mathcal{J}(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\lambda}}(x_{\alpha})_{\alpha < \lambda} \text{ Type})$.
(b) For all $\alpha < \lambda$, $\delta_{p_{\alpha}^{\lambda}} = \mathcal{J}(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha})$ where $p_{\alpha}^{\lambda} : A_{\lambda} \twoheadrightarrow A_{\alpha}$.

2. For any non-trivial object $A_{\lambda}$ and $f : A_{\lambda} \to B_{\mu+1}$, $\delta_f = \mathcal{J}(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{f}(x_{\alpha})_{\alpha < \lambda} \overline{(p_{\mu}f)^*B}(x_{\alpha})_{\alpha < \lambda})$ where $p_{\mu} : B_{\mu+1} \twoheadrightarrow B_{\mu}$.

*Proof.* This is [Car78, Lemma 12 pp.263]. $\square$

**Lemma B.38.** Every derived rule of $U(\mathcal{C})$ satisfies the hypothesis $H$.

*Proof.* This is by induction on derived rules of $U(\mathcal{C})$. Indeed, [Car78, Lemma pp.2.65] shows that every derivation from theorem A.4 preserves $H$. $\square$

**Corollary B.39.** 1. For any type symbol $\overline{A_{\lambda}}$ of the theory $U(\mathcal{C})$ we have $H(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{A_{\lambda}}(x_{\alpha})_{\alpha < \lambda} \text{ Type})$.

2. For every operator symbol $\overline{f}$ in $U(\mathcal{C})$ where $f : A_{\lambda} \to B_{\mu+1}$ we have $H(\{x_{\alpha} : \overline{A_{\alpha}}(x_{\gamma})_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{f}(x_{\alpha})_{\alpha < \lambda} \overline{(p_{\mu}f)^*B}(x_{\alpha})_{\alpha < \lambda})$.

The foremost important result, which summarizes the above, is:

**Corollary B.40.** 1. If $\{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda}$ is a context of the theory then for any $\alpha < \delta < \lambda$ we have $ht(r_{\Delta_{\alpha}}) < ht(r_{\Delta_{\beta}})$.

2. If there is a map $\langle t_{\beta} \rangle_{\beta < \mu} : \{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \to \{x_{\beta} : \Omega_{\beta}\}_{\beta < \mu}$ then for each $\beta < \mu$ we have $\mathcal{J}(r_{t_{\beta}}) \in \Gamma(\mathcal{J}(r_{\Omega_{\beta}[t_{\gamma}|x_{\gamma}]_{\gamma < \beta}}))$ where $r_{\Omega_{\beta}[t_{\gamma}|x_{\gamma}]_{\gamma < \beta}}$ is the rule $\{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \vdash \Omega_{\beta}[t_{\gamma}|x_{\gamma}]_{\gamma < \beta} \text{ Type}$.
3. If $\{x_{\alpha} : \Delta_{\alpha}\}_{\alpha < \lambda} \equiv \{x_{\alpha} : \Delta'_{\alpha}\}_{\alpha < \lambda}$ then $\mathcal{J}(r_{\Delta_{\lambda}}) = \mathcal{J}(r_{\Delta'_{\lambda}})$.
4. If $\langle t_{\alpha} \rangle_{\alpha < \lambda} \equiv \langle t'_{\alpha} \rangle_{\alpha < \lambda}$ then for each $\beta < \mu$, $\mathcal{J}(r_{t_{\beta}}) = \mathcal{J}(r_{t'_{\beta}})$.

We are almost ready to define a contextual functor $\xi_{\mathcal{C}} : \mathcal{C}_{U(\mathcal{C})} \to \mathcal{C}$. We only need the next:

131

Observation B.41. Let $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be a map, then there are maps $\{g_\beta : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\beta})\}_{\beta < \mu}$ with $\delta_{g_\beta} = \mathcal{J}(r_{t_b \text{eta}})$ and $pg_{\beta+1} = g_\beta$. This is a consequence of theorem B.40 and theorem B.11. Therefore, there exists a unique $g : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\mu})$ such that for all $\beta < \mu$ we have $\delta_{pg} = \mathcal{J}(r_{t_\beta})$ where $p : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\beta})$.

**Definition B.42.** We define a function

$$\xi_{\mathcal{C}} : \mathcal{C}_{U(\mathcal{C})} \to \mathcal{C}$$

by:

1. For an object $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \in \mathcal{C}_{U(\mathcal{C})}$,

$$\xi([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]) := \mathcal{J}(r_{\Delta_\lambda}).$$

2. For a morphism $[\langle t_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : \Omega_\beta\}_{\beta < \mu}]$

$$\xi([\langle t_\beta \rangle_{\beta < \mu}]) := g,$$

where $g : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\mu})$ is the unique map from theorem B.41.

**Lemma B.43.** 1. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta_\lambda$ Type is a derived rule of $U(\mathcal{C})$ then for all $\alpha \leq \lambda$, $\{x_\gamma : \Delta_\gamma\}_{\gamma < \lambda} \vdash \Delta_\alpha \equiv \mathcal{J}(r_{\Delta_\alpha})(x_\gamma)_{\gamma < \alpha}$ is a derived rule of $U(\mathcal{C})$.

2. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\lambda : \Delta_\lambda$ is a derived rule of $U(\mathcal{C})$ then $\{x_\gamma : \Delta_\gamma\}_{\gamma < \lambda} \vdash t \equiv \mathcal{J}(r_{t_\lambda})(x_\alpha)_{\alpha < \lambda}$ is a derived rule of $U(\mathcal{C})$.

Proof. See [Car78, Lemma 15 pp. 2.74].

**Corollary B.44.** As functions, we have that $\eta_{\mathcal{C}}\xi_{\mathcal{C}} = id_{\mathcal{C}_{U(\mathcal{C})}}$ and $\xi_{\mathcal{C}}\eta_{\mathcal{C}} = Id_{\mathcal{C}}$

The results needed for this have been introduced throughout the section. Using that we have a bijection and that $\eta_{\mathcal{C}}$ is already a functor, it follows:

**Corollary B.45.** The function $\xi_{\mathcal{C}} : \mathcal{C}_{U(\mathcal{C})} \to \mathcal{C}$ is a contextual functor.

The main result that is of our interest is:

**Theorem B.46.** There is a natural isomorphism $\mathbb{C}_- \circ U \cong Id_{\kappa\text{-}CON}$.

Finally,

**Corollary B.47.** The categories $\kappa$-CON of $\kappa$-contextual categories and $\kappa$-GAT of $\kappa$-algebraic theories are equivalent.

132

*Remark B.48.* In theorem B.26 we defined a map $T \to U(\mathbb{C}_T)$ simply by interpreting the axioms of the theory $T$ *i.e.*, by defining an interpretation sending axioms of the theory $T$ to derived rules of $U(\mathbb{C}_T)$. In the same way, given a $\kappa$-contextual category $\mathcal{C}$, we can define a map $T \to U(\mathcal{C})$ by sending axioms of $T$ to derived rules in $U(\mathcal{C})$. It follows that we have a $\kappa$-contextual functor $\mathbb{C}_T \to \mathcal{C}$.

### B.4 Models of a generalized Cartmell theory

In this section, we aim to make precise what we mean by a model of a generalized $\kappa$-algebraic theory $T$. Furthermore, if we were to prove a theorem in the same spirit of Lawvere's Functorial semantics, we would prove that there is an equivalence of categories

$$T\text{-}\mathbf{Alg}_\kappa \cong [\mathbb{C}_T, \mathbf{Fam}_\kappa]$$

where $T\text{-}\mathbf{Alg}_\kappa$ is the category of models of the theory $T$ and $\mathbf{Fam}_\kappa$ is a certain $\kappa$-contextual category of 'sets' or rather families of sets, and $[\mathbb{C}_T, \mathbf{Fam}_\kappa]$ is the category of $\kappa$-contextual functors between these two $\kappa$-contextual categories. Since in the paper we do not use the category $T\text{-}\mathbf{Alg}_\kappa$, we are simply interested in constructing the (large) $\kappa$-contextual category $\mathbf{Fam}_\kappa$. Then we can define a model of the theory $T$ simply as a $\kappa$-contextual functor $M : \mathbb{C}_T \to \mathbf{Fam}_\kappa$. Once more, this is a straightforward generalization of Cartmell's construction of the contextual category $\mathbf{Fam}$ [Car78, Section 2.2 pag. 2.9].

We fix a set of sets $\mathcal{U}$, which will play the role of the set of all sets. Ideally, $\mathcal{U}$ is a Grothendieck universe and in some places we will assume this, though this is technically not needed for the definition to make sense.

An object $X$ of $\mathbf{Fam}_\kappa$ of height $\alpha$ is a functor $X : (\alpha + 1)^{\mathrm{op}} \to \mathcal{U}$, such that:

- $X_0 = 1$,
- For each $\beta < \alpha$ there is map $f : X_\beta \to \mathcal{U}$ such that

$$X_{\beta+1} = \coprod_{x \in X_\beta} f(x)$$

where the map $X_{\beta+1} \to X_\beta$ is the canonical map $\coprod_{x \in X_\beta} f(x) \to X_\beta$,

- For each limit ordinal $\beta$, $X_\beta = \lim_{\gamma < \beta} X_\gamma$.

133

Note that in the definitions above, we do mean equality of sets. Alternatively, we can give a more categorical definition by asking for some compatible isomorphisms and identify objects that have isomorphism compatible to the map to $\mathcal{U}$, or we can give an inductive presentation of the notion, but this makes the exposition slightly more complicated.

Morphisms in $\mathbf{Fam}_{\kappa}$ between two objects $X$ and $Y$ of height $\alpha$ and $\beta$, respectively, are just functions $X_{\alpha} \rightarrow Y_{\beta}$. We call $X_{\alpha}$ and the underlying set of $X$: by construction, this underlying set gives us a functor $\mathbf{Fam}_{\kappa} \rightarrow \mathbf{Set}$, which is an equivalence of categories (or at last a fully faithful functor depending on $\mathcal{U}$). Display maps are functions from $X$ to the restriction of $X$ to an ordinal $\beta \leqslant \alpha$ given by the obvious map $X_{\alpha} \rightarrow X_{\beta}$.

Given a map $v: X_{\alpha} \rightarrow Y_{\beta}$ and a display map $Y_{\beta+\lambda} \rightarrow Y_{\beta}$, we can extend $X$ from $X_{\alpha}$ to $X_{\alpha+\lambda}$ with pullback squares

$$\begin{array}{ccc} X_{\alpha+\lambda} & \longrightarrow & Y_{\beta+\lambda} \\ \downarrow & & \downarrow \\ X_{\alpha} & \stackrel{v}{\longrightarrow} & Y_{\beta} \end{array}$$

where at each successor stage, we condition that the composite function $X_{\alpha+\lambda} \rightarrow Y_{\beta+\lambda} \rightarrow \mathcal{U}$ to define $X_{\alpha+\lambda+1}$, and at a limit stage we just define $X$ to be the limit.

One can easily check that $\mathbf{Fam}_{\kappa}$ and the datum specified above, constitute a $\kappa$-contextual category.

**Definition B.49.** Let $T$ be a generalized $\kappa$-algebraic theory. A *model* for $T$ is a $\kappa$-contextual functor $M: \mathbb{C}_T \rightarrow \mathbf{Fam}_{\kappa}$.

*Remark B.50.* Our definition of model might seem ad hoc; however, thanks to theorem B.48, in order to specify such a model we just need to specify how the axioms of $T$ are interpreted in $\mathbf{Fam}_{\kappa}$, and this corresponds to the naive notion of model—a structure where types are interpreted as sets, terms as functions and all equation axioms are valid. In other words, a model for a theory $T$ is really an interpretation of its axioms into the contextual category $\mathbf{Fam}_{\kappa}$.

Recall that a context $\Gamma \in \mathbb{C}_T$ has an associated length or height. If $\Gamma$ is a context of height $\alpha$, then we extend it by adding a fresh variable to obtain a context of height $\alpha+1$. Moreover, we saw that a context whose height is a limit ordinal is obtained as a limit of generalized display maps. Throughout section 2, and particularly in theorem 2.8, we use the notion of model of a generalized $\kappa$-algebraic theory. We take the time explain the notation used there.

134

Remark B.51. Recall that we have an “underlying set” functor $\mathbf{Fam}_{\kappa} \to \mathbf{Set}$. So given any model $X : \mathbb{C}_T \to \mathbf{Fam}_{\kappa}$, we get a composite functor $\mathbb{C}_T \to \mathbf{Fam}_{\kappa} \to \mathbf{Set}$, so that each model of $\mathbb{C}_T$ provides a functor from $\mathbb{C}_T$ to $\mathbf{Set}$. We will denote also this functor $X$, so that given a model $X$ and a context $\Gamma$, we can form the set $X(\Gamma)$, which is just $X(\Gamma)_{\alpha}$ where $\alpha$ is the height of the context $\Gamma$.

Remark B.52. One could also define models more naively as functors $\mathbb{C}_T \to \mathbf{Set}$ that preserve the pullbacks of display maps, the terminal object and limits of $\kappa$-small tower of display maps (in the usual up-to-isomorphisms sense). We call this alternative notion of models the models of the underlying $\kappa$-clan of $\mathbb{C}_T$. There is an obvious forgetful functor from the category of models of $T$ to the category of models of the underlying $\kappa$-clan of $\mathbb{C}_T$, using theorem B.51. This functor $\mathbf{Fam}_{\kappa} \to \mathbf{Set}$ is fully faithful by definition of morphisms in $\mathbf{Fam}_{\kappa}$, and this allows us to show the forgetful functor from models of $T$ to models of $\mathbb{C}_T$ as a $\kappa$-clan is also fully faithful.

If the theory $T$ has no type equality axiom, then it is also easy to show using theorem B.50 that this forgetful functor is essentially surjective, i.e., that every model of the underlying $\kappa$-clan of $\mathbb{C}_T$ is isomorphic to a model of $T$. But if $T$ has type equality axioms this is no longer always possible, see theorem B.54 below.

Construction B.53. If $\Gamma \in \mathbb{C}_T$ is a context of $T$, then, assuming $\mathcal{U}$ is a universe and the theory is (locally) $\mathcal{U}$-small, the corresponding representable functor $\mathbb{C}_T \to \mathbf{Set}$ can be promoted to a model $\Gamma^*$ of $T$. Indeed, to any context $\Delta = (x_i : X_i)_{i<\alpha}$, we can associate the tower of sets $\operatorname{Hom}(\Gamma, \Delta_{\gamma})$ where $\Delta_{\gamma} = (x_i : X_i)_{i<\gamma}$, is the subcontext of $\Gamma$ containing the first $\gamma$-variables. Given any morphism $f : \Gamma \to \Delta_{\gamma}$, a lift of this as a morphism $\Gamma \to \Delta_{\gamma+1}$ is the same as a term $\Gamma \vdash t : f^*(X_{\gamma})$. We can therefore iteratively replace the set $\operatorname{Hom}(\Gamma, \Delta_{\gamma})$ such that these identifications become equalities. One can then check that this does provide a morphism of contextual categories. Note that, as morphisms of models are just natural transformations, the Yoneda Lemma applies here and for any model $M$ of $T$ we have that $\operatorname{Hom}(\Gamma^*, M) \simeq M(\Gamma)$.

This defines a functor from $\mathbb{C}_T^{\mathrm{op}}$ to the category of models of $T$.

Remark B.54. In [Fre25], J. Frey has given a characterization of the categories (with their weak factorization systems as discussed in section 2.2) that arise as categories of models of an $\omega$-clan.

Consider the theory $T$ with two type axioms:

$$\vdash X \text{ Type} \quad x : X \vdash O(x) \text{ Type}$$

135

One term axiom

$$x : X \vdash s(x) : X$$

and one type equality axiom

$$x : X \vdash O(x) = O(s(x))$$

Models of $T$ are given by a set $X$, with a function $s : X \to X$ together with a collection of set indexed by the quotient $X/s$. It is then possible to prove ( we omit the details here) that:

- The category of models of $T$, equipped with its weak factorization system as defined in section 2.2, does not satisfy J. Frey's characterization, hence is not the category of model of a clan.
- The category of models of the underlying clan of $\mathbb{C}_T$ is equivalent to the category of models of the theory $T'$, similar to $T$ but where the type equality axiom is replaced by the existence of a bijection between $O(x)$ and $O(s(x))$.

### B.5 Coclans and contextual categories

In this section, we prove that every $\kappa$-contextual category can be obtained by strictification of a $\kappa$-clan. Clans were introduced in [Joy17], a related definition appears in [Hen20] under the name category with fibrations.

**Definition B.55.** We say that a category $\mathcal{C}$ is a $\kappa$-coclan if it has a collection of maps $\operatorname{COF}(\mathcal{C})$ satisfying the following conditions:

1. $\mathcal{C}$ has initial object 0.
2. For any $X \in \mathcal{C}$, the map $0 \to X$ is an element in $\operatorname{COF}(\mathcal{C})$.
3. Any isomorphism is an element of $\operatorname{COF}(\mathcal{C})$.
4. $\operatorname{COF}(\mathcal{C})$ is closed under compositions.
5. $\operatorname{COF}(\mathcal{C})$ is closed under pushouts: If $f : A \to C$ is a morphism in $\mathcal{C}$ and $A \to B \in \operatorname{COF}(\mathcal{C})$, then the map $C \to C \coprod_A B$ is an element in $\operatorname{COF}(\mathcal{C})$.
6. $\operatorname{COF}(\mathcal{C})$ is closed under transfinite compositions: for any $\lambda < \kappa$ and any $\lambda$-diagram of maps in $\operatorname{COF}(\mathcal{C})$

$$A_0 \longrightarrow A_1 \longrightarrow A_2 \longrightarrow \cdots$$

$\operatorname{Colim}_\lambda A_\alpha$ exists and the map $A_0 \to \operatorname{Colim}_\lambda A_\alpha$ belongs to $\operatorname{COF}(\mathcal{C})$.

136

As is usual, maps in $\mathrm{COF}(\mathcal{C})$ are called *cofibrations* and they are indicated by arrows “$\rightharpoonup$”.

Dually, a category $\mathcal{C}$ is $\kappa$-*clan* if $\mathcal{C}^{op}$ is a $\kappa$-coclan. The distinguished maps are called *fibrations* and they are denoted by $\mathrm{FIB}(\mathcal{C})$. The fibrations are indicated by arrows “$\rightharpoonup$”. When working with $\kappa$-clans we keep the terminology “transfinite compositions” from $\kappa$-coclans as there is no risk of confusion.

*Observation B.56.* The $\kappa$-contextual category $\mathbb{C}_T$ associated to a generalized $\kappa$-algebraic theory $T$ has a natural $\kappa$-clan structure. Indeed, we can take $\mathrm{FIB}(\mathbb{C}_T)$ as the set of display maps. All the axioms are easily verified. Moreover, this is true for any $\kappa$-contextual category not only for $\mathbb{C}_T$.

Recall that a *comprehension category* consists of a category $\mathcal{C}$, a fibration $p: \mathcal{E} \to \mathcal{C}$ and a functor $F: \mathcal{E} \to \mathcal{C}^{\to}$ such that:

1. \(\partial_0F = p\)
2. If \( f \) is a cartesian arrow in \( \mathcal{E} \), then \( Ff \) is a pullback in \( \mathcal{C} \); equivalently, \( Ff \) is a cartesian arrow with respect to the codomain functor \( \partial_0: \mathcal{C}^{\rightarrow} \rightarrow \mathcal{C} \).

The fibration $p$ is *cloven* if it comes with a choice of cartesian lifts. The comprehension category is said to be *split* is $p$ is a split fibration. We also say that is *full* if $F$ is fully faithful, we use the notation $(\mathcal{C}, \mathcal{E}, p, F)$ for a comprehension category.

The following example appears in [Jac93, Example 4.5], we rewrite it in our setting of $\kappa$-clans. Let us fix a $\kappa$-clan $\mathcal{C}$, then the inclusion functor $\iota: \mathrm{FIB}(\mathcal{C}) \hookrightarrow \mathcal{C}^{\to}$ and $P = \partial_0 \iota$ form a full comprehension category. More precisely: $\mathrm{FIB}(\mathcal{C})$ has objects fibrations in $\mathcal{C}$ and arrows between two fibrations $\alpha: f \to g$ are commutative squares of the form

$$
\begin{array}{c}
A \xrightarrow{k} B \\
f \downarrow \qquad \qquad \qquad \downarrow g \\
\Delta \xrightarrow{l} \Gamma.
\end{array}
$$

Hence, an object in $\mathrm{FIB}(\mathcal{C})_{\Gamma}$ over $\Gamma \in \mathcal{C}$ is a fibration $A \twoheadrightarrow \Gamma$. Observe that an arrow $\alpha: f \to g$ as above is cartesian if and only if it is a pullback square in $\mathcal{C}$. In conclusion, for an arrow $l: \Delta \to \Gamma$ and $g: B \twoheadrightarrow \Gamma \in \mathrm{FIB}(\mathcal{C})_{\Gamma}$, a

137

cartesian lift in $\mathrm{FIB}(\mathcal{C})$ is a pullback square

$$\begin{array}{c} A \xrightarrow{k} B \\ f \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \xrightarrow{l} \Gamma. \end{array}$$

This comprehension category is not necessarily split, reflecting the fact that taking pullbacks is not strictly functorial. Nevertheless, we can replace it by a split one via the functor

$$(-)_! : \mathbf{CompCat}(\mathcal{C}) \to \mathbf{SplCompCat}(\mathcal{C})$$

from the category of comprehension categories over $\mathcal{C}$ to the category of split comprehension categories over $\mathcal{C}$, the description of this functor appears in [LW15, 3.1] which we now recall. This produces a split comprehension category $(\mathcal{C}_!, \mathrm{FIB}(\mathcal{C})_!, p_!, F_!)$ which is equivalent to the one we started with. Unfolding the result, we take the $\mathcal{C}_!$ to be simply $\mathcal{C}$.

The category $\mathrm{FIB}(\mathcal{C})_!$ has:

- Objects: for each $\Gamma \in \mathcal{C}$ an object is a tuple $A := (V_A, E_A, f_A)$ where $V_A \in \mathcal{C}$, $E_A \twoheadrightarrow V_A \in \mathrm{FIB}(\mathcal{C})_{V_A}$ and $f_A : \Gamma \to V_A \in \mathcal{C}$. We also employ the notation $[A] := f_A^* E_A$ given by taking the pullback of $E_A \twoheadrightarrow V_A$ along $f_A$, so we get a fibration $[A] \twoheadrightarrow \Gamma$. In addition, we write $(E_A)_{f_A}$ for the arrow $[A] \to E_A$. Thus, an object over $\Gamma$ is a diagram in $\mathcal{C}$ of the form

$$\begin{array}{c} E_A \\ \Big\downarrow \\ \Gamma \xrightarrow{f_A} V_A. \end{array}$$

- Morphisms: A map between $(V_B, E_B, f_B) \to (V_A, E_A, f_A)$ over $\sigma : \Delta \to \Gamma$ is a map in $\mathcal{E}$ between $[B] \twoheadrightarrow \Delta$ and $[A] \twoheadrightarrow \Gamma$, i.e., a commutative square

$$\begin{array}{c} [B] \longrightarrow [A] \\ \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \xrightarrow{\sigma} \Gamma. \end{array}$$

- Composition is induced by the composition in $\mathcal{E}$, consequently, given by pasting commutative squares.

138

- The identity for $(V_A, E_A, f_A)$ is the identity of $[A] \twoheadrightarrow \Gamma$ as an object in $\mathcal{C}^\to$.

We now unpack the cartesian lifts for the induced functor $p_! : \mathrm{FIB}(\mathcal{C})_! \to \mathcal{C}_!$. Let $\sigma : \Delta \to \Gamma$ and $(V_A, E_A, f_A) \in \mathrm{FIB}(\mathcal{C})_!$ over $\Gamma$. Set $A[\sigma] := (V_A, E_A, f_A\sigma)$, pulling back along $f_A\sigma$, we obtain the commutative outer rectangle below

![img-64.jpeg](img-64.jpeg)

The universal property of the pullback on the right give us the unique map $A_\sigma : [A[\sigma]] \to [A]$. Therefore, a lift for $\sigma$ is given by the evident map $A_\sigma : (V_A, E_A, f_A\sigma) \to (V_A, E_A, f_A)$. From the definition of $A_\sigma$ the square

![img-65.jpeg](img-65.jpeg)

is a pullback, this implies that the square as a map in $\mathrm{FIB}(\mathcal{C})_!$ is a cartesian lift of $\sigma$ for $p_!$. Most importantly, this lift is uniquely determined by the composition $f_A\sigma$. Note that the transfinite composition of fibrations play no role in the construction. We summarize the discussion above in the following:

**Theorem B.57.** *For any $\kappa$-clan $\mathcal{C}$ there exist a full split comprehension category $(\mathcal{C}', \mathcal{E}, p_!, \iota_!)$ equivalent to $(\mathcal{C}, \mathrm{FIB}(\mathcal{C}), p, \iota)$.*

*Proof.* We apply the previous construction, this give us $(\mathcal{C}_!, \mathrm{FIB}(\mathcal{C})_!, p_!)$. Since the putative cartesian map is uniquely determined by the composition $f_A\sigma$, we can use a slight abuse of notation and write $A_\sigma := f_A\sigma$. Thus, if $\chi : \Xi \to \Delta$ is another map then $f(\sigma\chi) = (f\sigma)\chi$. This shows that the fibration $p_! : \mathrm{FIB}(\mathcal{C})_! \to \mathcal{C}_!$ is indeed split. The functor $\iota_! : \mathrm{FIB}(\mathcal{C})_! \to \mathcal{C}^\to$ is defined as $\iota_!(V_A, E_A, f_A) := \iota([A] \twoheadrightarrow \Gamma) = [A] \twoheadrightarrow \Gamma$; similarly for arrows. The comprehension category $(\mathcal{C}_!, \mathrm{FIB}(\mathcal{C})_!, p_!, \iota_!)$ is full, since $(\mathcal{C}, \mathrm{FIB}(\mathcal{C}), p, \iota)$ is full. $\square$

A *category with attributes* is a comprehension category $(\mathcal{C}, \mathcal{E}, p, F)$ such that $p$ is a discrete fibration. Equivalently, a category with attributes can be defined by the following data:

139

1. A category $\mathcal{C}$ with a terminal object 1.
2. A presheaf $\mathsf{Ty} : \mathcal{C}^{op} \to \mathbf{Set}$.
3. A function that assigns to each object $A \in \mathsf{Ty}(\Gamma)$, an object $\Gamma.A \in \mathcal{C}$, together with a map $\Gamma.A \to \Gamma$.
4. For each $A \in \mathsf{Ty}(\Gamma)$ and $\sigma : \Delta \to \Gamma$, a pullback square

![img-66.jpeg](img-66.jpeg)

**Corollary B.58.** *For any $\kappa$-clan $\mathcal{C}$ there exist a category with attributes equivalent to $\mathcal{C}$.*

*Proof.* Theorem B.57 give us a full split comprehension category $(\mathcal{C}_!, \mathsf{FIB}(\mathcal{C})_!, p_!, \iota_!)$. We take the category to be $\mathcal{C}_! = \mathcal{C}$. The additional data is given in the obvious way. Defining $\mathsf{Ty}(\Gamma) := (\mathsf{FIB}(\mathcal{C})_!)_\Gamma$, for each $A \in \mathsf{Ty}(\Gamma)$, we get $[A] \to \Gamma$ as described above. The required pullbacks are given by the cartesian lifts of $p_!$. Furthermore, these pullbacks are computed strictly along compositions, since $p_!$ is a split fibration. $\square$

Our next goal is to define a $\kappa$-contextual category equivalent to $\mathcal{C}$ from the category with attributes given by theorem B.58. In particular, for each object $\Gamma \in \mathcal{C}$, we get a $\kappa$-contextual category $\mathcal{C}(\Gamma)$. We start with the following:

**Definition B.59.** The category structure is given by the following data:

- **Objects:** For each ordinal $\mu < \kappa$, we define the set $Ob_\mu(\mathcal{C}(\Gamma))$ inductively over $\mu$;
  - If $\mu = \lambda + 1$, then we define $Ob_\mu(\mathcal{C}(\Gamma)) := \mathsf{Ty}([A_\lambda])$. More explicitly, an object $A_\mu \in Ob_\mu(\mathcal{C}(\Gamma))$ can be represented as the sequence
    $$A_\mu \to A_\lambda \to \cdots \to \Gamma$$
    and comes with a fibration $A_\mu \to \Gamma$.
  - If $\mu$ is a limit ordinal, then $Ob_\mu(\mathcal{C}(\Gamma))$ is the collection of objects of the form $A_\mu := \mathsf{Lim}_{\lambda < \mu} A_\lambda$ obtained as the transfinite composition of a sequence

$$\cdots \to A_\lambda \to \cdots \to \Gamma.$$

140

Each object comes with a fibration $A_\mu \to \Gamma$. This is given by the transfinite composition axiom of $\mathcal{C}$.

- **Morphisms:** For ordinals $\mu \leq \lambda < \kappa$ and objects $B_\lambda \in Ob_\lambda(\mathcal{C}(\Gamma))$, $A_\mu \in Ob_\mu(\mathcal{C}(\Gamma))$, we set

$$\operatorname{Hom}_{\mathcal{C}(\Gamma)}(B_\lambda, A_\mu) := \operatorname{Hom}_{\mathcal{C}/\Gamma}(B_\lambda, A_\mu).$$

- The rest of the structure of $\mathcal{C}(\Gamma)$ is induced by $\mathcal{C}/\Gamma$, in particular, the transfinite composition is that of $\mathcal{C}/\Gamma$.

Before proving that this gives us a $\kappa$-contextual category, let us explain the objects of this category. Recall that for $A \in \mathsf{Ty}(\Gamma)$ means we have a diagram of the form

$$\begin{array}{c} E_A \\ \downarrow \\ \Gamma \xrightarrow{f_A} V_A. \end{array}$$

When we identify this object with $[A]$, then $\mathsf{Ty}([A])$ is the set of objects of the form

$$\begin{array}{c} E_B \\ \downarrow \\ [A] \xrightarrow{(E_A)_{f_A}} E_A. \end{array}$$

Each of such objects gives $(V_A, f_A, E_B) \in \mathsf{Ty}(\Gamma)$, where $E_B \to V_A$ is the composition $E_B \to E_A \to V_A$. Equivalently, this is the composition $[B] \to [A] \to \Gamma$. Furthermore, if we write $\Gamma.A := [A]$, then we can rewrite this in a more familiar fashion $\Gamma.A.B \to \Gamma.A \to \Gamma$. This illustrates the general procedure for successor ordinals. A related construction appears in [KL18, Definition 4.3].

**Lemma B.60.** *For any $\kappa$-clan $\mathcal{C}$ and any $\Gamma \in \mathcal{C}$, the category $\mathcal{C}(\Gamma)$ is a $\kappa$-contextual category.*

Each axiom can be verified more or less immediately. We start with the category with attributes in theorem B.58 and the construction from theorem B.59.

*Proof.* 1. The objects of $\mathcal{C}(\Gamma)$ have grading $Ob(\mathcal{C}(\Gamma)) = \prod_{\mu < \kappa} Ob_\mu(\mathcal{C}(\Gamma))$ as in theorem B.59. This grading determines the height of each object.

141

2. The terminal object is $\Gamma$.
3. Given ordinals $\mu \leq \lambda < \kappa$ and objects $A_\lambda, A_\mu \in \mathcal{C}(\Gamma)$, the display maps between them are the maps in $Hom_{\mathcal{C}(\Gamma)}(A_\lambda, A_\mu)$ which are also fibrations of $\mathcal{C}$. We group these maps and objects in $Dis(\mathcal{C}(\Gamma))$, which is easily seen to be a subcategory.
4. $Dis(\mathcal{C}(\Gamma))$ is closed under transfinite compositions, since $\mathcal{C}$ is itself closed under such compositions.
5. The inclusion functor $i: Dis(\mathcal{C}(\Gamma)) \hookrightarrow \mathcal{C}(\Gamma)$ preserve transfinite compositions.
6. If $A \twoheadrightarrow B$ is an arrow in $Dis(\mathcal{C}(\Gamma))$, then $B \in Ob_\mu(\mathcal{C}(\Gamma))$ and $A \in Ob_\lambda(\mathcal{C}(\Gamma))$ for some ordinals $\lambda, \mu$ with $\mu \leq \lambda$: This follows directly by the definition of the objects of $\mathcal{C}(\Gamma)$
7. For any object $A \in Ob_\lambda(\mathcal{C}(\Gamma))$ and any $\mu \leq \lambda$, there exists a unique object $B \in Ob_\mu(\mathcal{C}(\Gamma))$ and a unique display map $A \twoheadrightarrow B$: We can easily obtain this by induction on $\lambda$ and verify that the map has the correct length.
8. Canonical pullbacks: This is given by the category with attributes structure on $\mathcal{C}$, as explained in theorem B.58.
9. Canonical pullbacks are strictly functorial: This is exactly what theorem B.58 achieves.
10. It follows from the description of objects given above.

Before we can state our main result, we first need to state the appropriate notion of equivalence between $\kappa$-clans. We borrow the definitions from [Joy17] adapted to our setting. Let $\mathcal{C}$ and $\mathcal{E}$ be two $\kappa$-coclans. We say that a functor $F: \mathcal{C} \to \mathcal{E}$ is a *morphism of $\kappa$-coclans* if

1. sends initial objects to initial objects,
2. preserves cofibrations,
3. preserves pushouts of cofibrations along any map
4. preserves transfinite compositions.

142

Furthermore, a morphism between $\kappa$-coclans $F : \mathcal{C} \to \mathcal{E}$ is an equivalence of $\kappa$-coclans if there exists another morphism of $\kappa$-coclans $G : \mathcal{E} \to \mathcal{C}$ and natural isomorphisms $GF \cong Id_{\mathcal{C}}$ and $FG \cong Id_{\mathcal{E}}$.

Similarly, $F : \mathcal{C} \to \mathcal{E}$ is a morphism of $\kappa$-clans simply if $F^{op} : \mathcal{C}^{op} \to \mathcal{E}^{op}$ morphism of $\kappa$-coclans, and an equivalence of $\kappa$-clans if $F^{op} : \mathcal{C}^{op} \to \mathcal{E}^{op}$ is an equivalence $\kappa$-coclans.

**Proposition B.61.** A morphism of clans $F : \mathcal{C} \to \mathcal{E}$ is an equivalence of clans if and only if $F$ reflects fibrations and transfinite compositions in $Dis(\mathcal{E})$; that is, if $F(Lim_{\lambda}A_{\alpha}) \twoheadrightarrow F(A_0)$ is the transfinite composition of the sequence

$$F(Lim_{\lambda}A_{\alpha}) \cdots \twoheadrightarrow FA_2 \twoheadrightarrow FA_1 \twoheadrightarrow FA_0$$

then $Lim_{\lambda}A_{\alpha} \twoheadrightarrow A_0$ is the transfinite composition of the sequence

$$\cdots \twoheadrightarrow A_2 \twoheadrightarrow A_1 \twoheadrightarrow A_0.$$

The equivalence of theorem B.57 give us an equivalence between clans.

**Corollary B.62.** For any $\kappa$-coclan $\mathcal{C}$ there exists a $\kappa$-contextual category equivalent to it.

Proof. Let us take the $\kappa$-clan given by $\mathcal{D} := \mathcal{C}^{op}$. We can then observe that $\mathcal{D} \cong \mathcal{D}(1)$, where $\mathcal{D}(1)$ is the $\kappa$-contextual category obtained from theorem B.60. We can take the opposites again to get $\mathcal{C}$. $\square$

### C Weak model categories

The most general setting in which we will show good homotopy-theoretic properties of the language introduced in section 2 is the framework of weak model categories introduced in [Hen20], which we will briefly recall here. In practice this extra generality compared to a Quillen model structure is not extremely useful — all the examples we will consider in section 3 are Quillen model structures — so it would not be unreasonable to skip the present subsection. There are two reasons why we need weak model categories:

- A key construction toward the proof of the third invariance theorem in section 4 is in general only a weak model structure, and we need to use its language as an intermediate tool.
- Future applications to left and right semi-model structures — actual weak model structure that are not left or right semi-model structures — are fairly uncommon, but the weak model categories which include both left and right semi-model structure at the same time, are considerably more common.

143

## C.1 Review

**Definition C.1.** A *weak model category* is a category $\mathcal{M}$ with three classes of maps: *cofibrations*, *fibrations* and *weak equivalences* satisfying the following conditions:

1. $\mathcal{M}$ has an initial object 0 and a terminal object 1, the identity of 0 is a cofibration, the identity of 1 is a fibration.
2. A composite of cofibrations with cofibrant domain is a cofibration. A composite of fibrations with fibrant codomain is a fibration.
3. Given two composable arrows $X \xrightarrow{f} Y \xrightarrow{g} Z$ where each of $X, Y$ and $Z$ are fibrant or cofibrant, if two of $f, g, g \circ f$ are weak equivalences, then the third is also a weak equivalence.
4. Every isomorphism between objects that are either fibrant or cofibrant is a weak equivalence.
5. Given a solid diagram:

$$\begin{array}{c} A \longrightarrow B \\ \downarrow i \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Where $i$ is a cofibration and $A$ and $B$ are cofibrant, then the pushout $j$ exists and is a cofibration.

6. The dual of condition 5 holds for fibrations between fibrant objects.
7. Every arrow isomorphic to a fibration, cofibration, or weak equivalence is also one.
8. Every arrow from a cofibrant to a fibrant object can be factored as a cofibration followed by a trivial fibration.
9. Every arrow from a cofibrant to a fibrant object can be factored as a trivial cofibration followed by a fibration.
10. Given a solid square:

$$\begin{array}{c} A \longrightarrow X \\ \downarrow i \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

144

Where $A$ and $B$ are cofibrant, $i$ is a cofibration, $X$ and $Y$ are fibrant, $p$ is a fibration and either $p$ or $i$ is a weak equivalence, then there exists a dotted map that makes the diagram to commute.

*Remark C.2.* In theorem C.1 we use the usual conventions: a *cofibrant object* is an object such that the unique map $0 \rightarrow X$ is a cofibration, and a *fibrant object* is an object such that the unique map $X \rightarrow 1$ is a fibration. A trivial (co)fibration is a map which is both an equivalence and a (co)fibration. We will also use the term *core cofibrations* to mean “cofibration between cofibrant objects” and *core fibrations* to mean “fibration between fibrant objects”.

*Remark C.3.* It is crucial to observe that theorem C.1 only involve the core cofibrations, core fibrations and weak equivalences between objects that are either fibrant or cofibrant. By that we mean that if given $\mathcal{M}$ a category with these three classes of maps, then ($\mathcal{M}$, cofibrations, fibrations, weak equivalences) is a weak model structure if and only if ($\mathcal{M}$, core cofibrations, core fibrations, weak equivalences between objects that are either fibrant or cofibrant) is a model structure.

For this reason, we generally consider that only core cofibrations, core fibrations and weak equivalence between objects that are either fibrant or cofibrant are to be treated as relevant notions. Nothing we will do here depends on the three class of maps outside these restrictions. In [Hen20] it was even considered that the words cofibrations, fibrations and weak equivalences to mean “core cofibrations”, “core fibrations” and “weak equivalences between fibrant or cofibrant objects”.

*Remark C.4.* The definition of weak model structure in [Hen20] is different from theorem C.1, but it is equivalent. It is stated without reference to the class of weak equivalence, and using the notion of (weak relative) path object and cylinder object. It is easy to show that a weak model structure in the sense of theorem C.1 is a weak model structure in the sense of [Hen20] by constructing the cylinder and path objects as factorization of the codiagonal and diagonal maps (see C.5 below). Conversely, it is shown in [Hen20] that given a weak model structure, it admits a (unique$^6$) class of weak equivalences such that all conditions of theorem C.1 are satisfied.

It is shown in [Hen20] that most of the basic theory of Quillen model categories carries over to weak model categories, with only some additional

$^6$Keeping in mind theorem C.3. Only the class of weak equivalence between fibrant or cofibrant objects is uniquely defined, outside of this, there are no restriction whatsoever on weak equivalence from theorem C.1.

145

care taken - mostly replacing objects by fibrant and cofibrant replacement of objects before applying the usual construction. The main significant difference is that the homotopy category (defined in terms of homotopy class of maps between bifibrant objects as we will recall below) is no longer equivalent to $\mathcal{M}[W^{-1}]$ - the localization of $\mathcal{M}$ at weak equivalence, but only to $\mathcal{M}^{\mathrm{cof\vee fib}}[W^{-1}]$ the localization the full subcategory of objects that are either fibrant or cofibrant at the weak equivalences. The problem is that the axioms of a weak model category allows us to take a fibrant replacement of a cofibrant object $C$ as a (trivial cofibration/fibration) factorization of $C \to 1$. Similarly we can take a cofibrant replacement of a fibrant objects, but there is no way to do similar replacement with an object which is neither fibrant nor cofibrant.

We now quickly go over some aspects of the construction of the homotopy category of a weak model category, the results mentioned below are all proven in section 2.1 and 2.2 of [Hen20].

**Construction C.5.** If $X$ is a bifibrant object (i.e. fibrant and cofibrant), we can form a *cylinder objects* $IX$ for $X$ as a (cofibration, trivial fibration) factorization:

$$X \coprod X \hookrightarrow IX \xrightarrow{\sim} X$$

and a path objects for $X$ as a (trivial cofibration, fibration) factorization

$$X \stackrel{\sim}{\hookrightarrow} PX \twoheadrightarrow X \times X.$$

Given a pair of maps $f, g : X \rightrightarrows Y$ between bifibrant objects, we say they are homotopic if there is a dotted map $h$ making the diagram below commutative:

![img-67.jpeg](img-67.jpeg)

or equivalently a map $h$

![img-68.jpeg](img-68.jpeg)

146

This is an equivalence relation, and the homotopy category $\mathrm{Ho}(\mathcal{M})$ of $\mathcal{M}$ can be defined as the category of bifibrant objects with homotopy class of maps between them. Moreover, this category is equivalent to the formal localization $\mathcal{M}^{\mathrm{cof\vee fib}}[W^{-1}]$.

**Construction C.6.** Note that if an object $C \in \mathcal{M}$ is only cofibrant and not fibrant we cannot define a cylinder object in the same way as above since the factorization axiom does not allow us to factor the maps $X \coprod X \to X$ if $X$ is not fibrant. In place of this, we can consider a fibrant replacement $X \stackrel{\sim}{\hookrightarrow} X^{\mathrm{FIB}} \twoheadrightarrow 1$, and then form a factorization:

![img-69.jpeg](img-69.jpeg)

This object $IX$, and more generally any object fitting into a diagram:

![img-70.jpeg](img-70.jpeg)

is called a weak cylinder object. Dually, if $Y$ is fibrant we define a weak path object of $Y$ as any object $PY$ that fits into a diagram:

![img-71.jpeg](img-71.jpeg)

We can then show that for a pair of maps $X \Rightarrow Y$ from a cofibrant object $X$ to a fibrant object $Y$ the following are equivalent:

- $f$ is homotopic to $g$ in terms of a weak cylinder object for $X$.
- $f$ is homotopic to $g$ in terms of a weak path object for $Y$.
- $f$ and $g$ are equal in the localization $\mathcal{M}^{\mathrm{cof\vee fib}}[W^{-1}]$.

Moreover, any arrow $X \to Y$ in the localization $\mathcal{M}^{\mathrm{cof\vee fib}}[W^{-1}]$ comes from an arrow $X \to Y$ in $\mathcal{M}$.

147

## C.2 Weak Reedy model structure

Before doing all the constructions, we need to set up the formalism needed for them. In this section, we study Reedy weak model categories. These are, as the name suggests, the counterpart of Reedy model categories. Most of the proofs are straightforward adaptation of the classical ones, so they are omitted.

**Definition C.7.** A *Reedy category* is a category $R$ together with two wide subcategories $R_+$ and $R_-$ and a functor $deg : R \to \alpha$, where $\alpha$ is an ordinal, such that:

1. For every non-identity arrow $a \to b \in R_+$, $\deg(a) < \deg(b)$.
2. For every $a \to b \in R_-$ a non-identity arrow, $\deg(b) < \deg(a)$.
3. Every arrow in $R$ factors uniquely as an arrow in $R_-$ followed by an arrow in $R_+$.

When the subcategory $R_-$ consists of identity arrows only, then $R$ is called a *direct category*. Similarly, when the subcategory $R_+$ consists of identity arrows only, then $R$ is called an *inverse category*.

Let $R$ be a Reedy category and $\mathcal{M}$ be a weak model category. Consider $\mathcal{M}^R$ the category of $R$-shaped diagram in $\mathcal{M}$. Given $X : R \to \mathcal{M}$ such a diagram and $r \in R$ any object. The *latching object* at $r$ is the colimit (if it exists)

$$L_r X := \mathsf{Colim}_{s \in (R_+/r) - \{Id_r\}} X_s.$$

Dually, the *matching object* at $r$ is the limit (if it exists)

$$M_r X := \mathsf{Lim}_{s \in (r/R_-) - \{Id_r\}} X_s.$$

**Definition C.8.** A map $f : X \to Y$ in $\mathcal{M}^R$ is said to be a *(trivial) Reedy cofibration* at $r \in R$ if the colimit $L_r Y \sqcup_{L_r X} X_r$ exists and the induced dotted map in the diagram below

![img-72.jpeg](img-72.jpeg)

148

is a (trivial) cofibration in $\mathcal{M}$.

Dually, $f : X \to Y$ in $\mathcal{M}^R$ is said to be a (trivial) Reedy fibration at $r \in R$ if the limit $M_r X \times_{M_r Y} Y_r$ exists and the induced dotted map in the diagram below

![img-73.jpeg](img-73.jpeg)

exists and is a (trivial) fibration in $\mathcal{M}$.

A map is said to be a (trivial) Reedy (co)fibration if it is one at each $r \in R$.

Remark C.9. We want to clarify that in theorem C.8 the colimit $L_r Y \sqcup_{L_r X} X_r$ is considered as a single colimit and not as a pushout using the objects $L_r X$ and $L_r Y$. It is possible that $L_r Y \sqcup_{L_r X} X_r$ exists without the colimit $L_r Y$ or $L_r X$ existing. Explicitly, it is the colimits of all the $X_i$ for $i \in R^+/r$ and of the $Y_i$ for $i \in R^+/r - \{id_r\}$, with all the maps coming from the functoriality in $i$ and the natural map $X_i \to Y_i$. We apply the same logic to the limit $M_r X \times_{M_r Y} Y_r$.

Definition C.10. A Reedy category is said to be locally finite if for any object $X \in R$ the categories $(R_+/X)$ and $(R_-/X)$ are finite.

It is a classical result that for any Quillen model category $\mathcal{M}$ and a Reedy category $R$ that the category of functors $\mathcal{M}^R$ carries a model structure in which the weak equivalences are the level-wise weak equivalences, the (trivial) (co)fibrations are precisely the Reedy (trivial) (co)fibrations. The same result can be obtained if we simply assume that the base category carries a weak model structure.

Theorem C.11. Assume that $\mathcal{M}$ is a weak model category and that $R$ is a locally finite Reedy category. Then there is a weak model structure on $\mathcal{M}^R$ such that a map $f : X \to Y$ is:

1. A weak equivalence if and only if $f_r : X_r \to Y_r$ is a weak equivalence for all $r \in R$.

149

2. An (trivial) cofibration if it is a (trivial) Reedy cofibration.
3. An (trivial) fibration if it is a (trivial) Reedy fibration.

Remark C.12. When the Reedy category is directed, this model structure coincides with the projective weak model structure. It is straightforward to define this last weak model category. In this weak model, the weak equivalences and the fibrations are the level-wise weak equivalences and fibrations respectively. Similarly, when the Reedy category is an inverse category, then the Reedy weak model structure is Quillen equivalent to the injective model structure. In this other case, weak equivalences and cofibrations are given level-wise.

We now prove the theorem:

Lemma C.13. Let I be a direct category and X : I → M be a diagram. Let U ⊂ V ⊂ I be two sieves of I, such that V - U has a finite number of objects. Assume that the colimit

$$X(U) := \text{Colim}_{u \in U} X(u)$$

exists and is cofibrant, and that for each v ∈ V - U, the latching object L_v X exists and is cofibrant, and the map L_v X → X(v) is a cofibration. Then X(V) exists and the comparison map X(U) → X(V) is a cofibration. If L_v X → X(v) is actually a trivial cofibration for every v ∈ V - U, then X(U) → X(V) is a trivial cofibration.

Proof. This is immediate by induction on the number of objects of V - U. If it only has one object, then X(U) → X(V) can be seen to be a pushout of the core cofibration L_v X → X_v to the cofibrant object X(U). If V - U has several objects, we iterate this process once for each object of V - U. □

Corollary C.14. Let R be a locally finite Reedy category, X : R → M be a diagram and let k ∈ R an object. Assume that X is Reedy cofibrant at every r such that deg(r) < deg(k), then the latching object L_k(X) exists and is cofibrant.

Proof. Using a proof by induction on deg(x), we can freely assume that all the latching object L_r(X) are cofibrant for all r such that deg(r) < deg(x). We can then just apply the theorem C.13 to the finite direct category I = R⁺/x and U = ∅, V = I. □

That is subcategories with the property that if there is an arrow x → x' and x' ∈ V then x ∈ V.

150

**Corollary C.15.** *Let $I$ be a finite direct category, and let $X : I \to \mathcal{M}$ be a Reedy cofibrant diagram and $U \subset I$ be a sieve, then $\mathsf{Colim}_I X$ and $\mathsf{Colim}_U X$ exist, are cofibrant and the obvious comparison map $\mathsf{Colim}_U X \to \mathsf{Colim}_I X$ is a cofibration.*

*If furthermore the latching map $L_r X \to X(r)$ is a trivial cofibration for each $r \in I - U$, then the map $\mathsf{Colim}_U X \to \mathsf{Colim}_I X$ is a trivial cofibration.*

*Proof.* By theorem C.14 all the latching objects of $X$ are cofibrant, so we can simply apply theorem C.13 and conclude. $\square$

**Corollary C.16.** *Let $R$ be a locally finite Reedy category.*

- *Any core (trivial) Reedy cofibration $X \to Y$ in $\mathcal{M}^R$ is in particular a levelwise (trivial) cofibration. That is, the map $X(r) \to Y(r)$ are (trivial) cofibrations for any $r \in R$.*
- *A map $X \to Y$ in $\mathcal{M}^R$ which is both a core Reedy cofibration and a level-wise weak equivalence is a trivial Reedy cofibration.*

Dually, the same is true for fibrations and trivial fibrations.

*Proof.* As both statement only depends on the restriction to the subcategory $R^+$, we can freely assume that $R$ is a (locally finite) direct category. In both cases, we consider the natural transformation $X \to Y$ as a diagram $T : R \times \{0 < 1\} \to \mathcal{M}$. We then observe that the latching map of $T$ at an object $(r, 0)$ is just $L_r X \to X$, and the latching map of $T$ at $(r, 1)$ is

$$L_r Y \sqcup_{L_r X} X(r) \to Y(r)$$

Hence the assumption that $X \to Y$ is a core Reedy cofibration translates into the fact that $T$ is Reedy cofibrant. For any object $r \in R$, the composite $R \times \{0 < 1\}/(r, 1) \to R \times \{0 < 1\} \to \mathcal{M}$ is immediately seen to be Reedy cofibrant as well, and we can then apply theorem C.15 to the sieve $U = R/r \times \{0\}$ to conclude that $X(r) \to Y(r)$ is a cofibration.

If $X \to Y$ is further assumed to be trivial, then the latching map of $T$ at all objects of the form $(r, 1)$ are trivial, and hence using the “trivial” case of theorem C.15, we conclude that $X(r) \to Y(r)$ is trivial.

If instead we assume that $X(r) \to Y(r)$ is a weak equivalence for all $r$, then we proceed by strong induction on $\deg(r)$. Assume that we already know that at all $k$ such that $\deg(k) < \deg(r)$.

151

If $\deg(r) = 0$, then the latching map is just $X(r) \to Y(r)$ itself, so it is a trivial cofibration as it is a cofibration and a weak equivalence. Assume now that we already know that all the latching maps

$$L_r Y \sqcup_{L_r X} X(r) \to Y(r)$$

are trivial cofibrations for any $r$ such that $\deg(r) < \deg(k)$. We can then deduce by the same argument as above that the map $L_k(X) \to L_k(Y)$ is a core trivial cofibration, which shows that the map $X(r) \to L_r Y \sqcup_{L_r X} X(r)$ is a trivial cofibration, hence an equivalence, and hence by 2-out-of-3 for equivalences, the map $L_r Y \sqcup_{L_r X} X(r) \to Y(r)$, is both an equivalence and a core cofibration, so it is a (core) trivial cofibration. $\square$

Note that we have also proved that:

**Lemma C.17.** *Let $R$ be a locally finite Reedy category, and $i : X \to Y$ be a core Reedy cofibration in $\mathcal{M}^R$. Then the domain of the latching map $L_r Y \sqcup_{L_r X} X(r)$ is cofibrant.*

*Proof.* At the beginning of the proof of theorem C.16 we observed that it could be written as a latching object $L_{(r,1)}T$ of a cofibrant Reedy diagram $T$. Hence, the result follows from theorem C.14. $\square$

**Proposition C.18.** *For any locally finite Reedy category $R$, in $\mathcal{M}^R$, the composite of two Reedy core cofibrations is a Reedy core cofibrations.*

*Proof.* We use a strategy very similar to the proof of theorem C.16. Here again, the result only depends on the restriction to $R^+$ so we can freely assume that $R$ is a direct category. Let $X \to Y \to Z$ be two composable Reedy core cofibrations in $\mathcal{M}^R$. We consider this as a diagram $T : R \times \{0 < 1 < 2\} \to \mathcal{M}$. As in the proof of theorem C.16. We observe that the latching map at an element of the form $(r, 0)$ is the latching map $L_r X \to X$ of $X$ hence is a cofibration as $X$ is Reedy cofibrant. The latching map at an element $(r, 1)$ is the map

$$L_r Y \sqcup_{L_r X} X(r) \to Y(r)$$

which is a cofibration as $X \to Y$ is assumed to be a Reedy cofibration. And finally, the latching map at $(r, 2)$ is the map

$$L_r Z \sqcup_{L_r Y} Y(r) \to Z(r)$$

which is also a cofibration. So this diagram $R \times \{0 < 1 < 2\} \to \mathcal{M}$ is Reedy cofibrant. It immediately follows that, for any $r \in R$ the composite

152

$R \times \{0 < 1 < 2\} / (r, 2) \to R^- \times \{0 < 1 < 2\} \to \mathcal{M}$ is a Reedy cofibrant diagram. Hence, applying theorem C.15, we can deduce that the map

$$\operatorname{Colim}_U T \to Z(r)$$

is a cofibration, where $U \subset R \times \{0 < 1 < 2\} / (r, 2)$ is the sieve containing all the objects except $(r, 1)$ and $(r, 2)$. But this map can be seen to be exactly

$$L_r Z \sqcup_{L_r X} X(r) \to Z(r)$$

by theorem C.12. This concludes the proof, as this can be applied to any object $r \in R$. $\square$

**Proposition C.19.** *Consider a cospan $Y \leftarrow X \to Z$ of diagram $R \to \mathcal{M}$, such that $X, Y, Z$ are all Reedy cofibrant and the arrow $X \to Y$ is a Reedy cofibration. Then the (level-wise) pushout $Y \sqcup_X Z$ exists in $\mathcal{M}^R$ and the natural transformation $Z \to Y \sqcup_X Z$ is a Reedy cofibration.*

*Proof.* It follows from theorem C.16 that for each $r \in R$ the three objects in the diagram $Y(r) \leftarrow X(r) \to Z(r)$ are cofibrant and the map $X(r) \to Y(r)$ is a cofibration, so the levelwise pushout $Y(r) \sqcup_{X(r)} Z(r)$ exists and by general category-theoretic results is functorial in $r$ and is a pushout in the category of diagrams $\mathcal{M}^R$. We only need to check that the map $Z(r) \to Y(r) \sqcup_{X(r)} Z(r)$ is a Reedy cofibration. For this observe that as colimits commute with colimits we have:

$$L_r(Y \sqcup_X Z) = \operatorname{Colim}_{r' \to r \in R^+} Y(r') \sqcup_{X(r')} Z(r') = L_r Y \sqcup_{L_r X} L_r Z$$

So that in the latching map

$$L_r(Y \sqcup_X Z) \sqcup_{L_r Z} Z \to Y \sqcup_X Z$$

the domain can be identified with

$$(L_r Y \sqcup_{L_r X} L_r Z) \sqcup_{L_r Z} Z = L_r Y \sqcup_{L_r X} Z = (L_r Y \sqcup_{L_r X} X) \sqcup_X Z$$

so the latching map is

$$(L_r Y \sqcup_{L_r X} X) \sqcup_X Z \to Y \sqcup_X Z$$

which is a pushout of the latching map $L_r Y \sqcup_{L_r X} X \to Y$. The latter map is itself a core cofibration since $X \to Y$ is a core Reedy cofibration. Hence, this concludes the proof. $\square$

153

We are now ready to prove theorem C.11:

*Proof.* We go over all the conditions of theorem C.1. The validity of conditions 1, 3, 7 and 4 is trivial. Condition 2 is theorem C.18 together with its dual. Condition 5 is theorem C.19, and condition 6 is the dual statement.

The proof of conditions 10 is essentially the same as the proof for ordinary model categories, as for example in Chapter 15 of [Hir03] or in Chapter 5.2 of [Hov99]. The key step in the proof is that in order to construct a diagonal lift in a square:

$$\begin{array}{c} A \longrightarrow X \\ \downarrow i \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

where say $i$ is a core cofibration and $p$ is a core fibration, one of them being a (level-wise) weak equivalence. Then we proceed by induction as in the usual proof, at each step we need to produce a diagonal lift in a square of the form

$$\begin{array}{c} A(r) \sqcup_{L_r A} L_r(B) \longrightarrow X(r) \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Now, by theorem C.17 (and its dual) the object $A(r) \sqcup_{L_r A} L_r(B)$ is cofibrant and $Y(r) \times_{M_r Y} M_r X$ is fibrant. By definition of Reedy cofibration and fibration, the left vertical map is a cofibration and the right vertical is a fibration, and if one of $i$ or $p$ (say $i$) is a weak equivalence. Then the second point of theorem C.16 shows that the left vertical map is a trivial cofibration, hence the square admits a diagonal lift, which concludes the proof.

The proof of condition 8 and (dually of condition 9), also follows very closely the classical proof, as in Chapter 15 of [Hir03] or in Chapter 5.2 of [Hov99]. Given $A \rightarrow X$ a map from a Reedy cofibrant diagram to a Reedy fibrant diagram that we want to factor as a core trivial Reedy cofibration followed by a core Reedy fibration, $A \rightarrow B \rightarrow X$. We proceed by induction to construct the diagram, the object $B(r)$, and the maps $A(r) \rightarrow B(r) \rightarrow X(r)$ gradually by induction on the degree of $r$. Following the classical proof, at each stage, we need to construct a factorization of a map in $\mathcal{M}$:

$$A(r) \sqcup_{L_r A} L_r B \rightarrow X(r) \times_{M_r X} M_r B$$

as a trivial cofibration followed by a fibration. But as observed above, the domain is cofibrant and the target is fibrant, so this is indeed possible in

154

$\mathcal{M}$. The case of condition 9 is done in the exact same way, but factoring the map above as a cofibration followed by a trivial fibration

□

## References

- [Bar10] Clark Barwick. On left and right model categories and left and right bousfield localizations. *Homology, Homotopy and Applications*, 12(2):245–320, 2010.
- [Bar19] Reid William Barton. *A model 2-category of enriched combinatorial premodel categories*. PhD thesis, Harvard University, 2019.
- [Bla78] Georges Blanc. Equivalence naturelle et formules logiques en théorie des catégories. *Archiv für mathematische Logik und Grundlagenforschung*, 19(1):131–137, Dec 1978.
- [Bro73] Kenneth S Brown. Abstract homotopy theory and generalized sheaf cohomology. *Transactions of the American Mathematical Society*, 186:419–458, 1973.
- [Car78] John Cartmell. *Generalised algebraic theories and contextual categories*. PhD thesis, Oxford University, 1978.
- [Fre76] Peter Freyd. Properties invariant within equivalence types of categories. In *Algebra, topology, and category theory (a collection of papers in honor of Samuel Eilenberg)*, (1):55–61, 1976.
- [Fre25] Jonas Frey. Duality for clans: an extension of gabriel–ulmer duality. *The Journal of Symbolic Logic*, pages 1–38, 2025.
- [Hen16] Simon Henry. Algebraic models of homotopy types and the homotopy hypothesis. *arXiv preprint arXiv:1609.04622*, 2016.
- [Hen20] Simon Henry. Weak model categories in classical and constructive mathematics. *Theory & Applications of Categories*, 35, 2020.
- [Hen23] Simon Henry. Combinatorial and accessible weak model categories. *Journal of Pure and Applied Algebra*, 227(2):107191, 2023.
- [Hir03] Philip S Hirschhorn. *Model categories and their localizations*. Number 99. American Mathematical Soc., 2003.

155

[Hov99] Mark Hovey. *Model categories*, volume 63 of *Mathematical Surveys and Monographs*. American Mathematical Society, Providence, RI, 1999.

[Jac93] Bart Jacobs. Comprehension categories and the semantics of type dependency. *Theoretical Computer Science*, 107(2):169–207, 1993.

[Joy08] André Joyal. The Theory of Quasi-categories and its Applications. *Lecture notes at Advanced Course on Simplicial Methods in Higher Categories*, 2008. Available online at: https://mat.uab.cat/~kock/crm/hocat/advanced-course/Quadern45-2.pdf.

[Joy17] Andre Joyal. Notes on clans and tribes. *arXiv:1710.10238*, 2017.

[JT07] André Joyal and Myles Tierney. Quasi-categories vs segal spaces. *Contemporary Mathematics*, 431(277-326):10, 2007.

[KL18] Krzysztof Kapulkin and Peter LeFanu Lumsdaine. The homotopy theory of type theories. *Advances in Mathematics*, 337:1–38, 2018.

[Lac02] Stephen Lack. A quillen model structure for 2categories. *K-theory*, 26:171–205, 06 2002.

[Lac04] Stephen Lack. A quillen model structure for bicategories. *K-Theory*, 33:185–197, 11 2004.

[Law69] F William Lawvere. Adjointness in foundations. *Dialectica*, pages 281–296, 1969.

[Law70] F William Lawvere. Equality in hyperdoctrines and comprehension schema as an adjoint functor. *Applications of Categorical Algebra*, 17:1–14, 1970.

[LW15] Peter LeFanu Lumsdaine and Michael A Warren. The local universes model: An overlooked coherence construction for dependent type theories. *ACM Transactions on Computational Logic (TOCL)*, 16(3):1–31, 2015.

[Mak95] Michael Makkai. First order logic with dependent sorts, with applications to category theory. http://www.math.mcgill.ca/makkai/folds/, 1995.

[Qui06] Daniel G Quillen. *Homotopical algebra*, volume 43. Springer, 2006.

156

[Ras23] Nima Rasekh. Yoneda lemma for simplicial spaces. *Applied Categorical Structures*, 31(4):27, 2023.

[Rez96] Charles Rezk. A model category for categories. *Available from the author's web page*, 1996.

[Rez01] Charles Rezk. A model for the homotopy theory of homotopy theory. *Transactions of the American Mathematical Society*, 353(3):973–1007, 2001.

[Ver24] Paula Verdugo. *On the homotopy theory of double categories and the equivalence invariance of formal category theory*. PhD thesis, Macquarie University, 2024.

[Ver25] Paula Verdugo. On the equivalence invariance of formal category theory. *arXiv preprint* https://arxiv.org/abs/2509.04255, 2025.

[Wol74] Harvey Wolff. V-cat and v-graph. *Journal of Pure and Applied Algebra*, 4(2):123–135, 1974.

157