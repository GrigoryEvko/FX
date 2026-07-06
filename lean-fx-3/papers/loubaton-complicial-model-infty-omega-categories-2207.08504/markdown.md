arXiv:2207.08504v2 [math.CT] 13 Mar 2024

# The complicial model of $(\infty, \omega)$-categories

Félix Loubaton

2

# Contents

|  **Introduction** | **5**  |
| --- | --- |
|  Summary of results | 6  |
|  **1 (0,ω)-Categories and presheaves on Θ** | **11**  |
|  1.1 Basic constructions | 13  |
|  1.1.1 (0,ω)-Categories | 13  |
|  1.1.2 The category Θ | 16  |
|  1.1.3 The link between presheaves on Θ and on Δ[Θ] | 20  |
|  1.2 Gray Operations | 25  |
|  1.2.1 Recollection on Steiner theory | 25  |
|  1.2.2 2-Polygraphs and presheaves on Θ₂ | 30  |
|  1.2.3 Gray operations on augmented directed complexes | 40  |
|  1.2.4 Gray operations on (0,ω)-categories | 46  |
|  1.2.5 Gray tensor product of simplicial sets | 52  |
|  **2 Study of complicial sets** | **61**  |
|  2.1 Preliminaries | 62  |
|  2.1.1 Generalities on model categories | 62  |
|  2.1.2 Marked and stratified presheaves | 65  |
|  2.2 The complicial model | 68  |
|  2.2.1 Model structure on marked simplicial sets | 68  |
|  2.2.2 Gray operations on marked simplicial sets | 72  |
|  2.2.3 Street nerve | 77  |
|  2.3 Suspension and Gray operations | 79  |
|  2.3.1 Formula for the Gray cylinder | 79  |
|  2.3.2 Formulas for the Gray cone and the Gray o-cone | 82  |
|  2.4 Globular equivalences | 84  |
|  2.4.1 Homotopy categories | 84  |
|  2.4.2 A criterion to be a weak equivalence | 87  |
|  2.4.3 A criterion to be a weakly invertible transformation | 91  |
|  2.4.4 Weak characterization of the identity | 92  |
|  **3 Complicial sets as a model of (∞,ω)-categories** | **101**  |
|  3.1 Preliminaries | 102  |
|  3.1.1 Segal A-precategories | 102  |

3

CONTENTS

|  3.1.2 | Stratified Segal $A$-precategories | 105  |
| --- | --- | --- |
|  3.1.3 | Models of $(\infty, n)$-categories | 109  |
|  3.1.4 | Gray module | 109  |
|  3.1.5 | Complicial Gray module | 113  |
|  3.2 | Complicial Gray module structure on tSeg($A$) | 114  |
|  3.2.1 | o-cone in tSeg($A$) | 114  |
|  3.2.2 | Adjunction with tPsh($\Delta$) | 117  |
|  3.2.3 | Complicial horn inclusions | 118  |
|  3.2.4 | Complicial thinness extensions | 125  |
|  3.2.5 | Saturation extensions | 133  |
|  3.2.6 | Conclusion | 134  |
|  3.3 | Complicial sets as of model of $(\infty, n)$-categories | 134  |
|  3.3.1 | The case $n < \omega$ | 134  |
|  3.3.2 | The case $n = \omega$ | 138  |
|  **Index of symbols** |   | **141**  |
|  **Index of notions** |   | **143**  |
|  **Bibliography** |   | **145**  |

4

# Introduction

A *category* consists of a set of objects, and for any pair of objects $a, b$, a set of morphisms $\hom_C(a, b)$ equipped with composition operations satisfying associativity laws.

$(\infty, 1)$-*Categories* are a homotopical generalization of categories. Intuitively, they are defined similarly to categories, except that we replace sets of objects and morphisms with spaces of objects and morphisms, and the associativity and unit laws are no longer satisfied strictly but homotopically.

Thanks in particular to the work of Joyal ([Joy02]) and Lurie ([Lur09]), most of the important concepts and theorems of category theory now have their $(\infty, 1)$-categorical analogues. These objects have become important tools in many areas of mathematics, including algebraic geometry, algebraic topology, and representation theory.

Another generalization of the notion of category is obtained by replacing the set of morphisms between two objects $a$ and $b$ with a category of morphisms between $a$ and $b$. These new objects are called *2-categories*. By replacing sets of morphisms between two objects $a$ and $b$ with $(n-1)$-categories of morphisms between $a$ and $b$, one can define by induction the notion of $n$-*category* for any integer $n$, and by limit, the notion of $(\infty, \omega)$-category.

For $n \in \mathbb{N} \cup \{\omega\}$, the notion of $(\infty, n)$-category is obtained by making both of these generalizations simultaneously. These objects are now found in many areas, including derived algebraic geometry, where the 6-functors formalism is expressed and manipulated using the theory of $(\infty, 2)$-categories ([GR19]), and in topological quantum field theory, where $(\infty, n)$-categories are essential for formulating and proving the cobordism hypothesis ([BD95], [Lur08], [GP21], [CS19]).

This text is devoted to the study of *models of $(\infty, n)$-categories*. By this, we mean any model category whose associated $(\infty, 1)$-category is $(\infty, n)$-cat. Among the known models of $(\infty, n)$-categories, we have for example Rezk's complete Segal $\Theta_n$-spaces, $n$-fold Segal spaces, and Segal $n$-categories (we refer to [BSP21] for a comprehensive presentation of these models and their equivalence). The common feature of all the models we have mentioned is that they rely on a globular combinatoric.

The main result of this text is to demonstrate that *complicial sets*, defined and extensively studied by Verity, are a model for $(\infty, n)$-categories. Unlike the other models, complicial sets rely on the combinatorics of the iterated lax cone, i.e. the combinatorics of simplices.

Let's now try to explain the intuition underlying the definition of complicial sets. To do this, we must first introduce stratified simplicial sets. A *stratified simplicial set* is a pair $(K, tK)$ where $K$ is a simplicial set and $tK$ is a subset of the simplices of $K$ containing the degenerate simplices. A simplex in $tK$ is called *marked*. We denote by $\text{tPsh}(\Delta)$ the category of stratified simplicial sets.

5

CONTENTS

Given a stratified simplicial set $(K, tK)$, we would like to view it as a "sort of $\omega$-category". The 0-simplices correspond to objects, the 1-simplices

$$a - u - b$$

to 1-cells between $a$ and $b$, the 2-simplices

![img-0.jpeg](img-0.jpeg)

to 2-cells with source $w$ and target the composite of $u$ and $v$, and more generally the $n$-simplices to $n$-cells whose source is a composition of odd faces and target a composition of even faces. Marked $n$-simplices are those whose corresponding $n$-cell is weakly invertible.

For this interpretation to be viable, some conditions on $(K, tK)$ must be imposed so that these "cells" "compose", and so that the marked simplices (i.e., "weakly invertible cells") satisfy a (2 out of 6)-type axiom$^1$. These conditions have been formalized by Verity in [Ver08c]. A stratified simplicial set satisfying them is called a *complicial set*.$^2$

In practice, these conditions are expressed using lifting properties. As these liftings are non-unique, compositions are not unique either. However, it can be shown that they are unique up to homotopy. Thus, a complicial set resembles a "weak $\omega$-category". Similarly, an $n$-complicial set (i.e., a complicial set where all simplices of dimension strictly greater than $n$ are marked) is a kind of "weak $n$-category".

It was therefore conjectured ([Str87], [Ver17], [BSP21]) that that for any $n \in \mathbb{N} \cup \{\omega\}$, the Verity model structure for $n$-complicial sets (whose fibrants-cofibrants are exactly $n$-complicial sets) was a model for $(\infty, n)$-categories.

The case $n = 1$ is an easy exercise, and the case $n = 2$ was proven by Gagna, Harpaz, and Lanari in [GHL22]. The goal of this text is to provide a positive answer to this conjecture in the general case, i.e. for any $n \in \mathbb{N} \cup \{\omega\}$.

## Summary of results

**Chapter 1.** The first section is devoted to the definition of $(0, \omega)$-categories and of the category $\Theta$ of Joyal. We also show that the category $\Theta$ presents the category of $(0, \omega)$-categories, and we also exhibit an other presentation of this category (corollary 1.1.3.4).

The second section begins with a review of Steiner theory, which is an extremely useful tool for providing concise and computational descriptions of $(0, \omega)$-categories. Following Ara and Maltsiniotis, we employ this theory to define the Gray tensor product, denoted by $\otimes$, in $(0, \omega)$-categories. We then introduce the Gray operations, starting with the Gray cylinder $_\otimes [1]$ which is the Gray tensor product with the directed interval $[1] := 0 \to 1$. Then, we have the *Gray cone*, the *Gray $\circ$-cone* and the *Gray*

$^1$Given a category $C$, a class $W$ of morphisms of $C$ satisfies (2 out of 6) if for any triple of morphisms $f$, $g$, and $h$ such that $fg$ and $gh$ are in $W$, then $f$, $g$, $h$, and $fgh$ are in $W$.

$^2$This notion is sometimes called a *saturated complicial set*.

6

CONTENTS

op-cone, denoted by \(\_ \star 1\), \(1 \stackrel{\infty}{\star}\) and \(1 \star\) , that send an \((0,\omega)\)-category \(C\) onto the following pushouts:

![img-1.jpeg](img-1.jpeg)

![img-2.jpeg](img-2.jpeg)

![img-3.jpeg](img-3.jpeg)

We also present a formula that illustrates the interaction between the suspension and the Gray cylinder. As this formula plays a crucial role in this text, we provide its intuition at this stage.

If \( A \) is any \( (0, \omega) \)-category, the suspension of \( A \), denoted by \( [A, 1] \), is the \( (0, \omega) \)-category having two objects - denoted by 0 and 1- and such that

\[
\operatorname{Hom} _ {[ A, 1 ]} (0, 1) := A, \quad \operatorname{Hom} _ {[ A, 1 ]} (1, 0) := \emptyset , \quad \operatorname{Hom} _ {[ A, 1 ]} (0, 0) = \operatorname{Hom} _ {[ A, 1 ]} (1, 1) := \{i d \}.
\]

We also define \([1] \vee [A, 1]\) as the gluing of \([1]\) and \([A, 1]\) along the 0-target of \([1]\) and the 0-source of \([A, 1]\). We define similarly \([A, 1] \vee [1]\). These two objects come along with whiskerings:

\[
\nabla : [ A, 1 ] \to [ 1 ] \vee [ A, 1 ] \quad \text { and } \quad \nabla : [ A, 1 ] \to [ A, 1 ] \vee [ 1 ]
\]

that preserve the extremal points.

The \((0,\omega)\)-category \([1]\otimes [1]\) is induced by the diagram:

![img-4.jpeg](img-4.jpeg)

and is then equal to the colimit of the following diagram:

\[
[ 1 ] \vee [ 1 ] \xleftarrow {\nabla} [ 1 ] \hookrightarrow [ [ 1 ], 1 ] \leftarrow [ 1 ] \xrightarrow {\nabla} [ 1 ] \vee [ 1 ].
\]

The \((0,\omega)\)-category \([1],1]\otimes [1]\) is induced by the diagram:

![img-5.jpeg](img-5.jpeg)

and is then equal to the colimit of the following diagram:

\[
[ 1 ] \vee [ [ 1 ], 1 ] \xleftarrow {\nabla} [ [ 1 ] \otimes \{0 \}, 1 ] \hookrightarrow [ [ 1 ] \otimes [ 1 ], 1 ] \leftarrow [ [ 1 ] \otimes \{1 \}, 1 ] \xrightarrow {\nabla} [ [ 1 ], 1 ] \vee [ 1 ]
\]

We prove a formula that combines these two examples:

Theorem 1.2.4.13. In the category of \((0,\omega)\)-categories, there exists an isomorphism, natural in \(A\), between \([A,1]\otimes [1]\) and the colimit of the following diagram

\[
[ 1 ] \vee [ A, 1 ] \xleftarrow {\nabla} [ A \otimes \{0 \}, 1 ] \longrightarrow [ A \otimes [ 1 ], 1 ] \longleftarrow [ A \otimes \{1 \}, 1 ] \xrightarrow {\nabla} [ A, 1 ] \vee [ 1 ]
\]

We also provide similar formulas for the Gray cone, the Gray o-cone and the Gray op-cone.

7

CONTENTS

**Theorem 1.2.4.14.** *There is a natural identification between $1 \stackrel{co}{\star} [A, 1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $[A, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{co}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

*There is a natural identification between $1 \star [A, 1]$ and the colimit of the following diagram.*

$$[1 \star A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [1] \vee [A, 1]$$

**Chapter 2.** This chapter is dedicated to the study of *Verity complicial sets*, defined and extensively studied by Verity ([Ver08c])

One of the benefits of complicial sets is that they admit a simple definition of the Gray tensor product. Being strongly linked to $(0, \omega)$-categories by the Street nerve, they are also a privileged framework for stating and proving strictification results, as done in [OR20a], [GOR21], [OR22] and [Mae23]. However, they do not interact *a priori* well with the globular language. The goal of this chapter is to show that, with some computation, it is possible to have a globular point of view on theses objects.

The first section is a recollection of usual results and definitions about complicial sets. In the second section, we aim to prove an analogue of the formula given in 1.2.4.13 to the complicial setting. We also have a suspension in this category, which is denoted by $X \mapsto \Sigma X$. Objects $[1] \vee \Sigma X$ and $\Sigma X \vee [1]$ are defined in 2.2.2.18, but for now, we can suppose that they are fibrant replacements of respectively $[1] \coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \vee [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:*

$$\Sigma X \vee [1] \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \vee \Sigma X.$$

We also provide similar formulas for the *Gray cone* and Gray $\circ$-*cone*:

**Theorem 2.3.2.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \star [0]$ and the colimit of the following diagram:*

$$\Sigma X \vee [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{co}{\star} X).$$

*There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{co}{\star} \Sigma X$ and the colimit of the following diagram:*

$$\Sigma(X \star [0]) \leftarrow \Sigma X \to [1] \vee \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[\iota_0^-]{i_0^+} \mathbf{D}_1 \xrightarrow[\iota_1^-]{i_1^+} \mathbf{D}_2 \xrightarrow[\iota_2^-]{i_2^+} \dots$$

8

CONTENTS

**Theorem 2.4.4.13.** *Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.*

Proposition 15.10 of [BSP21] provides a similar result for models of $(\infty, n)$-categories.

**Chapter 3.** Results of Gagna, Harpaz et Lanari ([GHL22]) states that 2-complicial sets are a model of $(\infty, 2)$-categories The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

The heart of the proof corresponds to constructing a Quillen adjunction between complicial sets and Segal precategories enriched in a model category $A$. We begin with the study (stratified) $A$-Segal categories. We then introduce the concept of *complicial Gray module* (definition 3.1.5.4). In short, a model category $A$ is a complicial Gray module when it admits a *Gray $\circ$-cylinder* $C \mapsto I \otimes C$ and a *Gray op-cone* $C \mapsto e \star C$, and when the assignment $[n] \to e \star e \star \dots e \star \emptyset$ lifts to a Quillen adjunction with stratified simplicial sets endowed with the model structure for complicial sets.

We then prove the following stability result:

**Theorem 3.2.6.2.** *If $A$ is a complicial Gray module, then the category of stratified Segal precategories enriched in $A$ is also a complicial Gray module.*

We will apply this theorem to the case where $A$ is the category of stratified simplicial sets endowed with the model structure for $n$-complicial sets. Bergner results imply that stratified Segal precategories enriched in a model of $(\infty, n)$-categories form models of $(\infty, n + 1)$-categories. By induction, we then prove the following theorem:

**Theorem 3.3.1.11.** *Let $n \in \mathbb{N}$. The model structure for $n$-complicial sets is a model of $(\infty, n)$-categories.*

Finally, in 3.3.2.1, we construct a Quillen adjunction between $\Theta$-spaces and $\omega$-complicial sets and prove the following result:

**Theorem 3.3.2.5.** *The adjunction*

$$\mathrm{Psh}(\Theta \times \Delta) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)$$

*constructed in 3.3.2.1 is a Quillen equivalence. Hence, the model structure for $\omega$-complicial sets is a model of $(\infty, \omega)$-categories.*

9

CONTENTS

10

# Chapter 1

## $(0, \omega)$-Categories and presheaves on $\Theta$

### Contents

|  **1.1 Basic constructions** | **13**  |
| --- | --- |
|  1.1.1 $(0, \omega)$-Categories | 13  |
|  1.1.2 The category $\Theta$ | 16  |
|  1.1.3 The link between presheaves on $\Theta$ and on $\Delta[\Theta]$ | 20  |
|  **1.2 Gray Operations** | **25**  |
|  1.2.1 Recollection on Steiner theory | 25  |
|  1.2.2 2-Polygraphs and presheaves on $\Theta_2$ | 30  |
|  1.2.3 Gray operations on augmented directed complexes | 40  |
|  1.2.4 Gray operations on $(0, \omega)$-categories | 46  |
|  1.2.5 Gray tensor product of simplicial sets | 52  |

The first section is devoted to the definition of $(0, \omega)$-categories and of the category $\Theta$ of Joyal. We also show that the category $\Theta$ presents the category of $(0, \omega)$-categories, and we also exhibit an other presentation of this category (corollary 1.1.3.4).

The second section begins with a review of Steiner theory, which is an extremely useful tool for providing concise and computational descriptions of $(0, \omega)$-categories. Following Ara and Maltsiniotis, we employ this theory to define the Gray tensor product, denoted by $\otimes$, in $(0, \omega)$-categories. We then introduce the Gray operations, starting with the Gray cylinder $\_ \otimes [1]$ which is the Gray tensor product with the directed interval $[1] := 0 \rightarrow 1$. Then, we have the *Gray cone*, the *Gray o-cone* and the *Gray op-cone*, denoted by $\_ \star 1$, $1 \star \_ \_ \_ \_ \_ and $1 \star \_ \_$, that send an $(0, \omega)$-category $C$ onto the following pushouts:

$$\begin{array}{ccc} C \otimes \{1\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & C \star 1 \end{array} \qquad \begin{array}{ccc} C \otimes \{0\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \star C \end{array} \qquad \begin{array}{ccc} \{0\} \otimes C & \longrightarrow & [1] \otimes C \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \star C \end{array}$$

We also present a formula that illustrates the interaction between the suspension and the Gray cylinder. As this formula plays a crucial role in this text, we provide its intuition at this stage.

11

CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

If $$A$$ is any $$(0, \omega)$$-category, the *suspension* of $$A$$, denoted by $$[A, 1]$$, is the $$(0, \omega)$$-category having two objects - denoted by 0 and 1- and such that

$$\operatorname{Hom}_{[A,1]}(0, 1) := A, \quad \operatorname{Hom}_{[A,1]}(1, 0) := \emptyset, \quad \operatorname{Hom}_{[A,1]}(0, 0) = \operatorname{Hom}_{[A,1]}(1, 1) := \{id\}.$$

We also define $$[1] \vee [A, 1]$$ as the gluing of $$[1]$$ and $$[A, 1]$$ along the 0-target of $$[1]$$ and the 0-source of $$[A, 1]$$. We define similarly $$[A, 1] \vee [1]$$. These two objects come along with *whiskerings*:

$$\nabla : [A, 1] \to [1] \vee [A, 1] \quad \text{and} \quad \nabla : [A, 1] \to [A, 1] \vee [1]$$

that preserve the extremal points.

The $$(0, \omega)$$-category $$[1] \otimes [1]$$ is induced by the diagram:

![img-6.jpeg](img-6.jpeg)

and is then equal to the colimit of the following diagram:

$$[1] \vee [1] \xleftarrow{\nabla} [1] \hookrightarrow [[1], 1] \leftarrow [1] \xrightarrow{\nabla} [1] \vee [1].$$

The $$(0, \omega)$$-category $$[[1], 1] \otimes [1]$$ is induced by the diagram:

![img-7.jpeg](img-7.jpeg)

and is then equal to the colimit of the following diagram:

$$[1] \vee [[1], 1] \xleftarrow{\nabla} [[1] \otimes \{0\}, 1] \hookrightarrow [[1] \otimes [1], 1] \leftarrow [[1] \otimes \{1\}, 1] \xrightarrow{\nabla} [[1], 1] \vee [1]$$

We prove a formula that combines these two examples:

**Theorem 1.2.4.13.** *In the category of $$(0, \omega)$$-categories, there exists an isomorphism, natural in $$A$$, between $$[A, 1] \otimes [1]$$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A \otimes \{0\}, 1] \longrightarrow [A \otimes [1], 1] \longleftarrow [A \otimes \{1\}, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

We also provide similar formulas for the Gray cone, the Gray o-cone and the Gray op-cone.

**Theorem 1.2.4.14.** *There is a natural identification between $$1 \stackrel{\circ}{\star} [A, 1]$$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\nabla} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $$[A, 1] \star 1$$ and the colimit of the following diagram*

$$[1 \stackrel{\circ}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [A, 1] \vee [1]$$

*There is a natural identification between $$1 \star [A, 1]$$ and the colimit of the following diagram.*

$$[1 \star A, 1] \longleftarrow [A, 1] \xrightarrow{\nabla} [1] \vee [A, 1]$$

12

1.1. BASIC CONSTRUCTIONS

## 1.1 Basic constructions

### 1.1.1 $(0, \omega)$-Categories

Definition 1.1.1.1. A globular set is a presheaf on the category of globes G, which is the category induces by the diagram

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

with the relations $i_n^+ i_{n-1}^\epsilon = i_n^- i_{n-1}^\epsilon$ for any $n > 0$ and $\epsilon \in \{+, -\}$. For any $n > k$ and $\epsilon \in \{+, -\}$, we also denote by $i_k^\epsilon$ the composite $\mathbf{D}_k \xrightarrow{i_k} \mathbf{D}_{k+1} \xrightarrow{f} \mathbf{D}_n$ where $f$ is any map. These and the identity arrows are the only maps in the category G.

If $X$ is a globular set, we denote by $X_n$ the set $X(\mathbf{D}_n)$. Its elements are called $n$-cells. The 0-cells are sometimes called objects. The maps $X_n \to X_k$ induced by $i_k^\epsilon : \mathbf{D}_k \to \mathbf{D}_n$ is denoted by $\pi_k^\epsilon$.

Definition 1.1.1.2. An $\omega$-category is a globular set $X$ together with

(1) operations of compositions

$$X_n \times_{X_k} X_n \to X_n \quad (0 \le k < n)$$

which associate to two $n$-cells $(x, y)$ verifying $\pi_k^-(x) = \pi_k^+(y)$, a $n$-cells $x \circ_k y$,

(2) as well as units

$$X_n \to X_{n+1}$$

which associate to an $n$-cell $x$, a $(n+1)$-cell $\mathbb{I}_x$,

and satisfying the following axioms:

(1) \(\forall x\in X_n,\pi_n^\epsilon (\mathbb{I}_x) = x.\)
(2) \(\pi_k^+(x\circ_n y) = \pi_k^+(x)\) and \(\pi_k^-(x\circ_n y) = \pi_k^-(y)\) whenever the composition is defined and \(k\leqslant n\)
(3) \(\pi_k^\epsilon (x\circ_n y) = \pi_k^\epsilon (x)\circ_n\pi_k^\epsilon (y)\) whenever the composition is defined and \(k > n\)
(4) \(x\circ_{n}\mathbb{I}_{\pi_{n}^{-}x} = x\) and \(\mathbb{I}_{\pi_n^+ x}\circ_n x = x.\)
(5) \((x\circ_{n}y)\circ_{n}z = x\circ_{n}(y\circ_{n}z)\) as soon as one of these is defined.
(6) If \( k < n \)

$$(x \circ_n y) \circ_k (z \circ_n w) = (x \circ_k z) \circ_n (y \circ_k w)$$

when the left-hand side is defined.

A $n$-cell $a$ is non trivial if is not in the image of the application $\mathbb{I} : X_{n-1} \to X_n$.

A morphism of $\omega$-categories is a map of globular sets commuting with compositions and units. The category of $\omega$-categories is denoted by $\omega$-cat.

Definition 1.1.1.3. By abuse of notation, we also denote by $\mathbf{D}_n$ the $\omega$-category that admits for any $k < n$ only two $k$-non-trivial cells, denoted by $e_k^-$ and $e_k^+$, and a single $n$-non-trivial cell, denoted by $e_n$ verifying :

$$\pi_l^-(e_k^\epsilon) = e_l^- \quad \pi_l^+(e_k^\epsilon) = e_l^+ \quad \text{for } l \le k < n$$

$$\pi_l^-(e_n) = e_l^- \quad \pi_l^+(e_n) = e_l^+ \quad \text{for } l \le n$$

13

CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Remark furthermore that the ω-category D_n represents n-cells, in the sense that Hom(D_n, C) ≅ C_n. We will not make the difference between n-cells and the corresponding morphism D_n → C.

Definition 1.1.1.4. The ω-category ∂D_n is obtained from D_n by removing the n-cell e_n. We thus have a morphism

$$i_n : \partial\mathbf{D}_n \to \mathbf{D}_n.$$

Note that ∂D_0 = ∅.

Definition 1.1.1.5. We say that an (0,ω)-category X is a polygraph if it can be constructed from the empty (0,ω)-category by freely adding arrows with specified source and target. That is if X can be obtained as a transfinite composition ∅ = X_0 → X_1 → ⋯ → X_i → colim X_i = X where for each i, the map X_i → X_{i+1} is a pushout of Π_S ∂D_n → Π_S D_{n+1}.

An arrow of a polygraph is said to be a generator if it is one of the arrows that has been freely added at some stage.

Each cell in a polygraph can be written as a composite of generators or iterated unit of generators (not necessarily in a unique way). For a n-cell f, the set of generators of dimension n that appear in such an expression (and even the number of times they appear) is the same for all such expressions. As a consequence, a composition of non trivial cells is always non trivial.

Definition 1.1.1.6. For any subset S of N*, we define the functor (_)^S : ω-cat → ω-cat sending a ω-category C to the category C^S such that for any n, there is an isomorphism C_n → C_n^S that sends every n-cell f to a cell f̅ fulfilling

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^+(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^-(f)}$$

if i ∈ S and

$$\pi_{n-1}^-(\overline{f}) = \overline{\pi_{n-1}^-(f)} \quad \pi_{n-1}^+(\overline{f}) = \overline{\pi_{n-1}^+(f)}$$

if i ∉ S. These functors are called dualities as they are inverse of themselves. Even if there are plenty of them, we will be interested in only a few of them. In particular, we have the odd duality (_)^{op}, corresponding to the set of odd integers, the even duality (_)^{co}, corresponding to the set of non negative even integers and the full duality (_)^o, corresponding to the set of all non negative integers. Eventually, we have equivalences

$$((_)^{co})^{op} \sim (_)^o \sim ((_)^{op})^{co}.$$

Definition 1.1.1.7. Let Psh(G)_{*,* be the category of globular set with two distinguished points, i.e. of triples (X, a, b) where a and b are elements of X_0. Let [_, 1] : G → Psh(G)_{*,* be the functor sending D_n on (D_{n+1}, {0}, {1}) and i_n^e on i_{n+1}^e. This induces by left Kan extension a functor [_, 1] : Psh(G) → Psh(G)_{*,* that we call the suspension. We leave it to the reader to check that whenever C has a structure of ω-category, [C, 1] inherits one from it. This functor then induces a functor

$$[\_, 1] : \omega\text{-cat} \to \omega\text{-cat}$$

that we calls again the suspension. Eventually, we denote by i_0^- : {0} → [C, 1] (resp. i_0^+ : {1} → [C, 1]) the morphism corresponding to the left point (resp. to the right point). For an integer n, we define by induction the functor Σ^n : Psh(G) → Psh(G) with the formula:

$$\Sigma^0 := id \quad \Sigma^{n+1} := \Sigma^n[\_, 1].$$

14

1.1. BASIC CONSTRUCTIONS

Definition 1.1.1.8. Let $n$ be a non null integer. A $n$-cells $f : s \to t$ is an equivalence if there exists $n$-cells $g : t \to s$ and $g' : t \to s$ such that

$$f \circ_{n-1} g = \mathbb{I}_t \qquad g \circ_{n-1} f = \mathbb{I}_s$$

Definition 1.1.1.9. A $(0, \omega)$-category is an $\omega$-category whose only equivalences are the identities. These objects are called Gaunt $\omega$-categories in [BSP21] and rigid $\omega$-categories in [Rez10]. Remark that $(0, \omega)$-categories are stable under suspensions and dualities.

We denote by $(0, \omega)$-cat the full subcategory of $\omega$-cat whose objects are the $(0, \omega)$-categories.

Definition 1.1.1.10. Let $n$ be an integer. An $(0, n)$-category is an $(0, \omega)$-category whose cell of dimension strictly higher than $n$ are units. The category of $n$-categories is denoted by $(0, n)$-cat and is the full subcategory of $(0, \omega)$-cat whose objects are $(0, n)$-categories.

Construction 1.1.1.11. Remark that the category $(0, n)$-cat is the localization of $(0, \omega)$-cat along morphisms $\mathbf{D}_k \to \mathbf{D}_n$ for $k \ge n$. We then have for any $n$ an adjunction

$$i_n : (0, n)\text{-cat} \xrightarrow{\perp} (0, \omega)\text{-cat} : \tau_n$$

The right adjoint is called the $n$-truncation.

Construction 1.1.1.12. For any $n$, we define the colimit preserving functor $\tau_n^i : (0, \omega)\text{-cat} \to (0, n)\text{-cat}$, called the intelligent $n$-truncation, sending $\mathbf{D}_k$ on $\mathbf{D}_{\min(n,k)}$. The functor $\tau_n^i$ fits in an adjunction

$$\tau_n^i : (0, \omega)\text{-cat} \xrightarrow{\perp} (0, n)\text{-cat} : i_n$$

Notation 1.1.1.13. We will identify objects of $(0, n)$-cat with their image in $(0, \omega)$-cat and we will then also note by $\tau_n$ and $\tau_n^i$ the composites $i_n \tau_n^i$ and $i_n \tau_n^i$.

Remark 1.1.1.14. The family of truncation functor induces a sequence

$$\dots \to (0, n+1)\text{-cat} \xrightarrow{\tau_n} (0, n)\text{-cat} \to \dots \to (0, 1)\text{-cat} \xrightarrow{\tau_0} (0, 0)\text{-cat}.$$

The canonical morphism

$$(0, \omega)\text{-cat} \to \lim_{n:\mathbb{N}} (0, n)\text{-cat},$$

that sends an $(0, \omega)$-category $C$ to the sequence $(\tau_n C, \tau_n \tau_{n+1} C \cong \tau_n C)$, has an inverse given by the functor

$$\underset{\mathbb{N}}{\text{colim}} : \lim_{n:\mathbb{N}} (0, n)\text{-cat} \to (0, \omega)\text{-cat}$$

that sends a sequence $(C_n, \tau_n C_{n+1} \cong C_n)$ to the colimit of the induced sequence:

$$i_0 C_0 \to i_1 C_1 \to \dots \to i_n C_n \to \dots$$

We then have an equivalence

$$(0, \omega)\text{-cat} \cong \lim_{n:\mathbb{N}} (0, n)\text{-cat}.$$

15

CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

### 1.1.2 The category $$\Theta$$

Definition 1.1.2.1. Let $$n$$ be a non negative integer and $$\mathbf{a} := \{a_0, a_1, ..., a_{n-1}\}$$ a sequence of $$(0, \omega)$$-categories. We denote $$[\mathbf{a}, n]$$ the colimit of the following diagram

![img-8.jpeg](img-8.jpeg)

where $$[\_, 1]$$ is the suspension functor defined in 1.1.1.7.

Definition 1.1.2.2. We define $$\Theta$$ as the smallest full subcategory of $$(0, \omega)$$-cat that includes the terminal $$(0, \omega)$$-category $$[0]$$, and such that for any non negative integer $$n$$, and any finite sequence $$\mathbf{a} := \{a_0, a_1, ..., a_{n-1}\}$$ of objects of $$\Theta$$, it includes the $$(0, \omega)$$-category $$[\mathbf{a}, n]$$. Objects of $$\Theta$$ are called globular sum.

Remark 1.1.2.3. A morphism $$g : [\mathbf{a}, n] \to [\mathbf{b}, m]$$ is exactly the data of a morphism $$f : [n] \to [m]$$, and for any integer $$i$$, a morphism

$$a_i \to \prod_{f(i) \le k < f(i+1)} b_k.$$

Example 1.1.2.4. For any $$n$$, $$\mathbf{D}_n$$ is a globular sum. The $$(0, \omega)$$-category induced by the $$\omega$$-graph

![img-9.jpeg](img-9.jpeg)

is a globular sum.

Definition 1.1.2.5. For a globular sum $$a$$ and an integer $$n$$, we define $$[a, n] := [\{a, a, ..., a\}, n]$$. For a sequence of integer $$\{n_0, .., n_k\}$$ and a sequence of globular sum $$\{a_0, .., a_k\}$$, we define $$[a_0, n_0] \lor [a_1, n_1] \lor ... \lor [a_k, n_k]$$ as the globular sum $$[\{a_0, .., a_1, ..., a_k, ...\}, n_0 + n_1 + ... + n_k]$$.

We denote by $$[0]$$ the terminal $$(\infty, \omega)$$-category, and $$[n]$$ the globular sum $$[[0], n]$$. This induces a fully faithful functor $$\Delta \to \Theta$$ sending $$[n]$$ onto $$[n]$$..

Definition 1.1.2.6. We define by induction the dimension of a globular sum $$a$$, denoted by $$|a|$$. The dimension of $$[0]$$ is 0, and the dimension of $$[\mathbf{a}, n]$$ is the maximum of the set $$\{|a_k| + 1\}_{k < n}$$. We denote by $$\Theta_n$$ the full subcategory of $$\Theta$$ whose objects are the globular sum of dimension inferior or equal to $$n$$. We set by convention $$\Theta_\omega := \Theta$$.

Notation 1.1.2.7. We set by convention $$\omega + 1 := \omega$$.

An important property of the category $$\Theta$$ is that it is a Reedy elegant.

Definition 1.1.2.8. A Reedy category is a small category $$A$$ equipped with two subcategories $$A_+$$, $$A_-$$ and a degree function $$d : ob(A) \to \mathbb{N}$$ such that:

(1) for every non identity morphism $$f : a \to b$$, if $$f$$ belongs to $$A_-$$, $$d(a) > d(b)$$, and if $$f$$ belongs to $$A_+$$, $$d(a) < d(b)$$.

16

1.1. BASIC CONSTRUCTIONS

(2) every morphism of $A$ uniquely factors as a morphism of $A_{-}$ followed by a morphism of $A_{+}$.

A Reedy category $A$ is *elegant* if for any presheaf $X$ on $A$, for any $a \in A$ and any $c \in X(a)$, there exists a unique morphism $f : a \to a' \in A_{-}$ and a unique non degenerate object $c' \in X(a')$ such that $c = X(f)(c')$.

**Proposition 1.1.2.9.** *Let $X$ be a presheaf on an elegant Reedy category $A$. The category $A_{/X}$ is an elegant Reedy category.*

*Proof.* We have a canonical projection $\pi : A_{/X} \to A$. A morphism is positive (resp. negative) if it's image by $\pi$ is. The degree of an element $c$ of $A_{/X}$ is the degree of $\pi(c)$. We leave it to the reader to check that this endows $A_{/X}$ with a structure of Reedy category.

The fact that $A_{/X}$ is elegant is a direct consequence of the isomorphism $\mathrm{Psh}(A_{/X}) \cong \mathrm{Psh}(A)_{/X}$. $\square$

**Proposition 1.1.2.10** (Berger, Bergner-Rezk). *For any $n \in \mathbb{N} \cup \{\omega\}$, the category $\Theta_n$ are elegant Reedy category.*

*A morphism $g : [\mathbf{a}, n] \to [\mathbf{b}, m]$ is degenerate (i.e a morphism of $\Theta_{-}$) if the corresponding morphism $f : [n] \to [m]$ is a degenerate morphism of $\Delta$, and for any $i < n$ and any $f(i) \leq k < f(k+1)$, the corresponding morphism $a_i \to b_k$ is degenerate. Furthermore, a morphism is degenerate if and only if it is a epimorphism in $\mathrm{Psh}(\Theta)$.*

*A morphism is in $\Theta^{+}$ if and only if it is a monomorphism in $\mathrm{Psh}(\Theta)$.*

*Proof.* The Reedy structure is a consequence of lemma 2.4 of [Ber02]. The fact that for any $n < \omega$, $\Theta_n$ is elegant is [BR13, corollary 4.5.]. As for any $n < \omega$, the inclusion $\Theta_n \to \Theta$ preserves strong pushout, the characterization of elegant Reedy category given by [BR13, proposition 3.8.] implies that $\Theta$ is also elegant. $\square$

**Definition 1.1.2.11.** We recall that a morphism $g : [\mathbf{a}, n] \to [\mathbf{b}, m]$ is exactly the data of a morphism $f : [n] \to [m]$, and for any integer $i$, a morphism

$$a_i \to \prod_{f(i) \leq k < f(i+1)} b_k.$$

The morphism $g$ is *globular* if for any $k < n$, $f(k+1) = f(k) + 1$ and the morphism $a_k \to b_k$ is globular. The morphism $g$ is *algebraic* if it cannot be written as a composite $ig'$ where $i$ is a globular morphism.

**Example 1.1.2.12.** The morphism

![img-10.jpeg](img-10.jpeg)

is globular. This is not the case for the morphism

![img-11.jpeg](img-11.jpeg)

that sends the 2-cell of the left globular sum on the 1-composite of the two 2-cells of the right globular sum.

17

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

**Proposition 1.1.2.13** ([Ara10, Proposition 3.3.10]). *Every morphism in Θ can be factored uniquely in an algebraic morphism followed by a globular morphism.*

**Remark 1.1.2.14.** Globular morphisms belong to Θ₊ (and so morphisms of Θ₋ are algebraic) but the converse is false. For example, the second morphism of example 1.1.2.12 is not globular but belongs to Θ₊. We then have two different factorizations on Θ: the one coming from the Reedy elegant structure, and the one given in proposition 1.1.2.13.

**Definition 1.1.2.15.** The suspension functor [_, 1] : Θ → Θ induces by left Kan extension a functor

$$[\_, 1] : \mathrm{Psh}(\Theta) \to \mathrm{Psh}(\Theta).$$

We define by induction on a → Θ-presheaf Spₐ and a morphism Spₐ → a. If a is [0], we set Sp[0] := [0]. For n > 0, we define Sp[ₐ,ₙ] as the set valued presheaf on Θ obtained as the colimit of the diagram

![img-12.jpeg](img-12.jpeg)

We define Eᵉq as the set valued preheaves on Δ obtained as the colimit of the diagram

![img-13.jpeg](img-13.jpeg)

For any integer n, the functor Σⁿ : Θ → Θ, which is the n-iteration of [_, 1], induces by left Kan extension a functor

$$\Sigma^n : \mathrm{Psh}(\Theta) \to \mathrm{Psh}(\Theta).$$

We define two sets of morphisms of Psh(Θ):

$$\mathrm{W}_{\mathrm{Seg}} := \{\mathrm{Sp}_a \to a, a \in \Theta\} \quad \mathrm{W}_{\mathrm{Sat}} := \{\Sigma^n E^{eq} \to \mathbf{D}_n\}$$

and we set

$$\mathrm{W} := \mathrm{W}_{\mathrm{Seg}} \cup \mathrm{W}_{\mathrm{Sat}}.$$

For any n, we also define

$$\mathrm{W}_n := \mathrm{W} \cap \Theta_n.$$

**Definition 1.1.2.16.** We recall that for an integer n and a globular sum a, we defined [a, n] := [{a, a, ..., a}, n]. This defines a functor i : Δ[Θ] → Θ sending (n, a) on [a, n] where Δ[Θ] is the following pushout of category:

![img-14.jpeg](img-14.jpeg)

For the sake of simplicity, we will also denote by [a, n] (resp. [n]) the object of Δ[Θ] corresponding to (n, a) (resp. to (n, [0])). We define two sets of morphisms:

$$\mathrm{M}_{\mathrm{Seg}} := \{[a, \mathrm{Sp}_n] \to [a, n], a : \Theta\} \cup \{[f, 1], f \in \mathrm{W}_{\mathrm{Seg}}\}$$

$$\mathrm{M}_{\mathrm{Sat}} := \{E^{eq} \to [0]\} \cup \{[f, 1], f \in \mathrm{W}_{\mathrm{Sat}}\}$$

18

1.1. BASIC CONSTRUCTIONS

and we set

$$\mathrm{M} := \mathrm{M}_{\mathrm{Seg}} \cup \mathrm{M}_{\mathrm{Sat}}.$$

For an integer $n$, we define $\Delta[\Theta_n]$ as the following pushout of category:

$$\begin{array}{c} \{[0]\} \times \Theta_n \longrightarrow \Delta \times \Theta_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \longrightarrow \Delta[\Theta_n] \end{array}$$

and the functor $i$ induces a functor $\Delta[\Theta_n] \to \Theta_{n+1}$. For any $n$, we define

$$\mathrm{M}_n := \mathrm{M} \cap \Delta[\Theta_n].$$

**Definition 1.1.2.17.** Let $C$ be a category and $S$ a set of monomorphisms. A morphism is $f : x \to y$ is $S$-local if it has the unique right lifting property against morphisms of $S$. An object $x$ is $S$-local if $x \to 1$ is $S$-local, or equivalently, if for any $i : a \to b \in S$, the induced functor $\operatorname{Hom}(i, x) : \operatorname{Hom}(b, x) \to \operatorname{Hom}(a, x)$ is an isomorphism.

We can easily check that $S$-local morphisms are stable by composition, left cancellation and pullback. As a consequence, any morphism between $S$-local objects is $S$-local.

**Construction 1.1.2.18.** Let $C$ be a presentable category and $S$ a set of monomorphisms with small codomains. We define $C_S$ as the full subcategory of $C$ composed of $S$-local objects. The theorem 4.1 of [Bou77] implies that $\iota : C_S \to C$ is part of an adjunction

$$\mathbf{F}_S : C \xrightarrow{\iota} C_S : \iota$$

where $\mathbf{F}_S : C \to C_S$ is the localization of $C$ by the smallest class of morphisms containing $S$ and stable under composition and colimit.

**Theorem 1.1.2.19 (Berger).** Let $n \in \mathbb{N} \cup \{\omega\}$. The functor $\operatorname{Psh}(\Theta_n) \to (\infty, n)$-cat defined as the left Kan extension of the canonical inclusion $\Theta \to (\infty, \omega)$-cat induces an isomorphism

$$\operatorname{Psh}(\Theta_n)_{\mathrm{W}_n} \cong (\infty, n)\text{-cat}$$

*Proof.* This is [BSP21, corollary 12.3].

**Remark 1.1.2.20.** Suppose given an other category $D$ fitting in an adjunction

$$F : C \xrightarrow{\iota} D : G$$

with unit $\nu$ and counit $\epsilon$, as well as a set of morphisms $T$ of $D$ such that $F(S) \subset T$. By adjunction property, it implies that for any $T$-local object $d \in D$, $G(d)$ is $S$-local. The previous adjunction induces a derived adjunction

$$\mathbf{L}F : C_S \xrightarrow{\iota} D_T : \mathbf{R}G$$

where $\mathbf{L}F$ is defined by the formula $c \mapsto \mathbf{F}_T F(c)$ and $\mathbf{R}G$ is the restriction of $G$ to $D_T$. The unit is given by $\nu \circ \mathbf{F}_S$ and the counit by the restriction of $\epsilon$ to $D_T$.

19

CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Construction 1.1.2.21. Let n ∈ ℕ ∪ {ω}. The functor i : Δ[Θₙ] → Θₙ₊₁ defined in definition 1.1.2.16 induces an adjunction:

$$i_{!}: \mathrm{Psh}(\Delta[\Theta_{n}]) \xleftarrow{\longleftrightarrow} \mathrm{Psh}(\Theta_{n+1}): i^{*}$$

where the left adjoint is the left Kan extension of the functor Δ[Θₙ] → Θ → Psh(Θₙ₊₁). Remark that there is an obvious inclusion iₗ(Mₙ₊₁) ⊂ Wₙ₊₁. In virtue of the last construction, this induces an adjunction between derived categories:

$$\mathbf{L}i_{!}: \mathrm{Psh}(\Delta[\Theta_{n}])_{\mathrm{M}_{n+1}} \xleftarrow{\longleftrightarrow} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n+1}}: \mathbf{R}i^{*} \tag{1.1.2.22}$$

The theorem 1.1.2.19 and the corollary 1.1.3.4 (which is proved in the next section) induce equivalences

$$(0, \omega)\text{-cat} \cong \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n+1}} \cong \mathrm{Psh}(\Delta[\Theta_{n}])_{\mathrm{M}_{n+1}}.$$

### 1.1.3 The link between presheaves on Θ and on Δ[Θ]

Definition 1.1.3.1. Let C be a cocomplete category. A functor F : A → C is Reedy cofibrant if A has a structure of Reedy elegant category (definition 1.1.2.8) and for every object a, the induced morphism colim_∂ₐ F → F(a) is a monomorphism.

Definition 1.1.3.2. A class of monomorphism T of a cocomplete category C is precocomplete if

- It is closed by transfinite compositions and pushouts.
- It is closed by left cancellation, i.e for any pair of composable morphisms f and g, if gf and f are in S, so is g.
- For any Reedy cofibrant diagram F : A → Arr(C) that is pointwise in S, the morphism colim_A F is in S.

For a set of morphisms S, we denote S̅ the smallest precocomplete class of morphisms containing S.

The aim of this subsection is to demonstrate the following proposition:

Theorem 1.1.3.3. For any a ∈ Θ and b ∈ Δ[Θ], morphisms iₗi*a → a and b → i*iₗb are respectively in W̅ and M̅.

As a corollary, we directly have:

Corollary 1.1.3.4. For any n ∈ ℕ ∪ {ω}, the adjunction

$$\mathbf{L}i_{!}: \mathrm{Psh}(\Delta[\Theta]_{n})_{\mathrm{M}_{n}} \xleftarrow{\longleftrightarrow} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n}}: \mathbf{R}i^{*}$$

given in (1.1.2.22) is an adjoint equivalence.

Proof. This is a consequence of theorem 1.1.3.3 and of the fact that W̅ₙ (resp. M̅ₙ) is a included in the smallest class containing Wₙ (resp. Mₙ) and stable by two out of three and colimits. □

Definition 1.1.3.5. We denote by

$$[\_, \_] : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$$

20

1.1. BASIC CONSTRUCTIONS

the left Kan extension of the functor $\Theta \times \Delta \to \mathrm{Psh}(\Delta[\Theta])$ sending $(a, n)$ onto $[a, n]$. For an integer $n$, we denote

$$[\_, n] : \mathrm{Psh}(\Theta)^n \to \mathrm{Psh}(\Theta)$$

the left Kan extension of the functor $\Theta^n \to \mathrm{Psh}(\Theta)$ sending $\mathbf{a} := \{a_1, ..., a_n\}$ onto $[\mathbf{a}, n]$. Eventually, we define

$$[\_, d^0 \cup d^n] : \mathrm{Psh}(\Theta)^n \to \mathrm{Psh}(\Theta)$$

the left Kan extension of the functor $\Theta^n \to \mathrm{Psh}(\Theta)$ sending $\mathbf{a} := \{a_1, ..., a_n\}$ onto the colimit of the span.

$$[\{a_0, ..., a_{n-2}\}, n-1] \leftarrow [\{a_1, ..., a_{n-2}\}, n-2] \to [\{a_1, ..., a_{n-1}\}, n-1]$$

Lemma 1.1.3.6. The image of $\overline{\mathbf{W}} \times \overline{\mathbf{W}_1}$ by the functor $[\_, \_] : $\mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$ is included in $\overline{\mathbf{W}}$.

Proof. As $[\_, \_]$ preserves colimits and monomorphisms, it is enough to show that for any pair $f, g \in \mathbf{W} \times \mathbf{W}_1$, $[f, g]$ is in $\mathbf{W}$, which is obvious.

Lemma 1.1.3.7. For any globular sum $v$, and any integer $n$, the morphism $[v, d^0 \cup d^n] \cup [\partial v, n] \to [v, n]$ appearing in the diagram

![img-15.jpeg](img-15.jpeg)

is in $\overline{\mathbf{M}}$.

Proof. Let $a$ be a globular sum. Remark that the morphism $[a, \mathrm{Sp}_n] \to [a, d^0 \cup d^n]$ is in $\overline{\mathbf{M}}$. By left cancellation, this implies that $[a, d^0 \cup d^n] \to [a, n]$ is in $\overline{\mathbf{M}}$. Let $X$ be a presheaf on $\Theta$. As $X$ is a colimit of globular sum indexed by the Reedy cofibrant diagram $\Theta_{/X} \to \mathrm{Psh}(\Theta)$ (definition 1.1.3.1), and as $[\_, d^0 \cup d^n] \to [\_, n]$ preserve cofibrations, this implies that $[X, d^0 \cup d^n] \to [X, n]$ is in $\overline{\mathbf{M}}$. In particular, $[\partial v, d^0 \cup d^n] \to [\partial v, n]$ is in $\overline{\mathbf{M}}$, and so is $[v, d^0 \cup d^n] \to [\partial v, n] \cup [v, d^0 \cup d^n]$ by stability by coproduct. A last use of the stability by left cancellation then concludes the proof.

Definition 1.1.3.8. Let $[b, m]$ be an element of $\Delta[\Theta]$. We denote $\mathrm{Hom}^*(i([b, m]), [\mathbf{a}, n])$ the subset of $\mathrm{Hom}(i([b, m]), [\mathbf{a}, n])$ that consists of morphisms that preserve extremal objects. The explicit expression of morphism in $\Theta$ given in remark 1.1.2.3 implies the bijection:

$$\mathrm{Hom}^*(i([b, m]), [\mathbf{a}, n]) \cong \mathrm{Hom}_\Delta([n], [m])^* \times \prod_{i < n} \mathrm{Hom}_\Theta(b, a_i) \tag{1.1.3.9}$$

where $\mathrm{Hom}^*(_\Delta[n], [m])$ is the subset of $\mathrm{Hom}_\Delta([n], [m])$ consisting of morphisms that preserve extremal objects.

Let $\mathbf{a} := \{a_0, a_1, ..., a_{n-1}\}$ be a finite sequence of globular sums. We define $\Theta_{/\mathbf{a}}^*$ as the category whose objects are collections of maps $\{b \to a_i\}_{i < n}$ such that there exists no degenerate morphism $b \to b'$ factorizing all $b \to a_i$. Morphisms are monomorphisms $b \to b'$ making all induced triangles commute.

21

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

The bijection (1.1.3.9) induces a bijection between the objects of Θ→/a and the morphisms [b, n] → i*[a, n] that are the identity on objects and that can not be factored through any degenerate morphism [b, n] → [b̄, n].

Lemma 1.1.3.10. For any morphism p : [b, m] → i*[a, n] in Psh(Δ[Θ]) that preserves extremal objects, there exists a unique pair ({b' → a_i}i<n, [f, i] : [b, m] → [b', n]) where {b' → a_i}i<n is an element of Θ→/a, f is a degenerate morphism, and such that the induced triangle

![img-16.jpeg](img-16.jpeg)

commutes.

Proof. By adjunction and thanks to the bijection (1.1.3.9), p corresponds to a pair (j : [m] → [n], {b → a_i}i<n), and i has to be equal to j.

Using once again this bijection, and the fact that degeneracies are epimorphisms, we have to show that there exists a unique degenerate morphism g : b → b' that factors the morphisms b → a_i for all i < n, and such that the induced family of morphisms {b' → a_i}i<n is an element of Θ→/a.

As any infinite sequence of degenerate morphisms is constant at some point, the existence is immediate.

Suppose given two morphisms b → b', b → b'' fulfilling the previous condition. The proposition 3.8 of [BR13] implies that there exists a globular sum b̃ and two degenerate morphisms b' → b̃ and b'' → b̃ such that the induced square

![img-17.jpeg](img-17.jpeg)

is cartesian. The universal property of pushout implies that b → b̃ also fulfills the previous condition. By definition of b' and b'', this implies that they are equal to b̃, and this shows the uniqueness. □

Lemma 1.1.3.11. Let {b → a_i}i<n be an element of Θ→/a and i : b' → b a monomorphism of Θ. The induced family {b' → b → a_i}i<n is an object of Θ→/a.

Proof. The lemma 1.1.3.10 implies that there exists a unique degenerate morphism j : b' → b̃ that factors all the morphism b' → b → a_i for i < n, and such the induced family of morphisms {b̃ → a_i}i<n is an element of Θ→/a. We proceed by contradiction, and we then suppose that j is different from the identity.

We then have, for any i < n, a commutative square

![img-18.jpeg](img-18.jpeg)

As the morphism j is degenerate and different of the identity, there exists an integer k and a non trivial k-cell d of b' that is sent to an identity by j. Now, let d' be a k-generator of the polygraph b that appears in the decomposition of i(d). The commutativity of the previous square and the fact that the (0, ω)-categories a_i are polygraphs implies that for any i, the k-cell a' is sent to an identity by the morphism

22

1.1. BASIC CONSTRUCTIONS

$b \to a_i$. As for any $i < n$ and any $l \ge k$, there is no non trivial $l$-cell in $a_i$ whose $(k-1)$-source and $(k-1)$-target are the same, this implies that every $l$-cell of $b$ that is $(k-1)$-parallel with $d'$ is send to the identity by the morphism $b \to a_i$.

We denote $\bar{b}$ the globular sum obtained by crushing all $l$-cells of $b$ that are $(k-1)$-parallel with $d'$. The induced degenerate morphism $b \to \bar{b}$ factors all the morphisms $b \to a_i$ which is in contradiction with the fact that $\{b \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\rightarrow}$.

**Definition 1.1.3.12.** We say that an element $\{v \to a_i\}_{i<n}$ in the category $\Theta_{/\mathbf{a}}^{\rightarrow}$ is of height 0 if $v \to a_0$ factors through $\partial a_0$ or $v \to a_{n-1}$ factors through $\partial a_{n-1}$. The height of an element $w$ is the maximal integer $m$ such that there exists a sequence $v_0 \to v_1 \to \dots \to v_m = w$ in $\Theta_{/\mathbf{a}}^{\rightarrow}$ with $v_i \neq v_{i+1}$ for any $i < m$ and such that $v_0$ is of height 0 and $v_1$ is not. As $\Theta$ is a Reedy category, all elements have finite height.

**Lemma 1.1.3.13.** For any morphism $p : [b, m] \to i^*[\mathbf{a}, n]$ that preserves extremal objects, there exists a unique integer $k$, a unique element $\{b' \to a_i\}_{i<n}$ of height $k$, and a unique morphism $[f, i] : [b, m] \to [b', n]$ that doesn't factors through $[\partial b', n]$, and such that the induced triangle

$$\begin{array}{c} [b, m] \xrightarrow{[f,i]} [b', n] \\ \searrow \quad \downarrow p' \\ i^*[\mathbf{a}, n] \end{array}$$

commutes.

If $\{\bar{b} \to a_i\}_{i<n}$ is any other object of non negative height, and $[\bar{f}, j] : [b, m] \to [\bar{b}, n]$ is a morphism that make the induced triangle

$$\begin{array}{c} [b, m] \xrightarrow{[\bar{f}, j]} [\bar{b}, n] \\ \searrow \quad \downarrow \bar{p} \\ i^*[\mathbf{a}, n] \end{array}$$

commutative, then $\{\bar{b} \to a_i\}_{i<n}$ is of height strictly superior to $k$ and $[\bar{f}, j]$ factors through $[\partial \bar{b}, n]$.

Proof. The lemma 1.1.3.10 implies the first assertion. For the second one, suppose given an object $\{\bar{b} \to a_i\}_{i<n}$ of non negative height and a morphism $[\bar{f}, j] : [b, m] \to [\bar{b}, n]$ fulfilling the desired condition. The bijection (1.1.3.9) directly implies that $j$ is equal to $i$, and the first assertion implies that $\bar{f}$ is non degenerate.

We can then factor $\bar{f} : b \to \bar{b}$ in a degenerate morphism $b \to \bar{b}$ followed by a monomorphism $\bar{b} \to \bar{b}$ which is not the identity. The lemma 1.1.3.11 then implies that $\{\bar{b} \to \bar{b} \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\rightarrow}$. The first assertion then implies that the two morphisms $[b, m] \to [b', n]$ and $[b, m] \to [\bar{b}, n]$ are equals. As the monomorphism $[b', n] = [\bar{b}, n] \to [\bar{b}, n]$ is not the identity, this concludes the proof.

**Lemma 1.1.3.14.** The morphism $i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n] \to i^*[\mathbf{a}, n]$ is in $\overline{\mathbf{M}}$, where $\partial^j \mathbf{a}$ corresponds to the sequence $\{a_1, \dots, \partial a_j, \dots, a_n\}$.

Proof. For $k \in \mathbb{N} \cup \{\infty\}$, we define $x_k$ as the smallest sub object of $i^*[\mathbf{a}, n]$ such that for any element of height inferior or equal to $k$ of $\Theta_{/\mathbf{a}}^{\rightarrow}$, the corresponding morphism $[b, n] \to i^*[\mathbf{a}, n]$ factors through $x_k$. In particular we have $x_0 = i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n]$, and the lemma 1.1.3.10 implies that $x_\infty = i^*[\mathbf{a}, n]$. We denote $(\Theta_{/\mathbf{a}}^{\rightarrow})_k$ the set of element of $\Theta_{/\mathbf{a}}^{\rightarrow}$ of height $k$.

23

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Every morphism [b, m] → i*[a, n] that does not preserve extremal points then factors through x₀. The lemma 1.1.3.13 implies that for any integer k, the canonical square

$$\coprod_{(\Theta_{/\mathbf{a}}^{-\rightarrow})_{k+1}} [b, d^0 \cup d^n] \cup [\partial b, n] \longrightarrow x_k$$
$$\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(1.1.3.15)}$$
$$\coprod_{(\Theta_{/\mathbf{a}}^{-\rightarrow})_{k+1}} [b, n] \longrightarrow x_{k+1}$$

is cocartesian. The lemma 1.1.3.7 and the stability under pushout of M̅ imply that xₖ → xₖ₊₁ is in M̅. As i*[a, n] is the transfinite composition of the sequence x₀ → x₁ → ..., this implies that x₀ → i*[a, n] is in M̅ which conclude the proof.

**Lemma 1.1.3.16.** *The morphism i* Spₐ → i*a is in M̅ for any globular sum a.*

*Proof.* Let [a, n] := a. As M̅ is closed under pushouts and composition, lemma 1.1.3.14 implies that the morphism

$$i^*[\{a_0, ..., a_{n-2}\}, n-1] \cup i^*[\{a_1, ..., a_{n-1}\}, n-1] \to i^*[a, n]$$

is in M̅. An easy induction on n shows that this is also the case for the morphism

$$[a_0, 1] \cup ... \cup [a_{n-1}, 1] = i^*[a_0, 1] \cup ... \cup i^*[a_{n-1}, 1] \to i^*[a, n].$$

Now remark that i* Spₐ,ₙ is equivalent to

$$[\text{Sp}_{a_0}, 1] \cup ... \cup [\text{Sp}_{a_{n-1}}, 1].$$

As the morphisms [Spᵢ, 1] → [aᵢ, 1] are by definition in M, this concludes the proof.

**Proposition 1.1.3.17.** *There is an inclusion i* W ⊂ M̅.*

*Proof.* For Segal extensions, this is precisely the content of the last lemma. For saturation extensions, remark that i* Wₛₐₜ = Mₛₐₜ.

*Proof of theorem 1.1.3.3.* Let a be a globe. We then have iₜi*a = a. Suppose now that a is any globular sum. We then have a commutative diagram

$$\begin{array}{c} i_t i^* \text{Sp}_a \xlongequal{\quad} \text{Sp}_a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ i_t i^* a \longrightarrow a \end{array}$$

where the upper horizontal morphism is an identity. The proposition 1.1.3.17 and the fact that iₜ(M) ⊂ W implies that the vertical morphisms of the previous diagram are in W̅. By left cancellation, this implies that iₜi*a → a belongs to W̅ for any globular sum. We proceed analogously to show that for any b ∈ Δ[Θ], b → i*iₜb is in M̅.

24

1.2. GRAY OPERATIONS

## 1.2 Gray Operations

### 1.2.1 Recollection on Steiner theory

We present here the Steiner theory developed in [Ste04].

Definition 1.2.1.1. An augmented directed complex $(K, K^*, e)$ is given by a complex of abelian groups $K$, with an augmentation $e$:

$$\mathbb{Z} \xleftarrow{e} K_0 \xleftarrow{\partial_0} K_1 \xleftarrow{\partial_1} K_2 \xleftarrow{\partial_2} K_3 \xleftarrow{\partial_3} \dots$$

and a graded set $K^* = (K_n^*)_{n \in \mathbb{N}}$ such that for any $n$, $K_n^*$ is a submonoid of $K_n$. A morphism of directed complexes between $(K, K^*, e)$ and $(L, L^*, e')$ is given by a morphism of augmented complexes of abelian groups $f : (K, e) \to (L, e')$ such that $f(K_n^*) \subset L_n^*$ for any $n$. We note by ADC the category of augmented directed complexes.

Steiner then constructs an adjunction

$$\lambda : \omega\text{-cat} \xrightarrow{\perp} \mathrm{ADC} : \nu$$

The functor $\lambda$ is the simplest to define:

Construction 1.2.1.2. Let $C$ be a $\omega$-category. We denote by $(\lambda C)_n$ the abelian group generated by the set $\{[x]_n : x \in C_n\}$ and the relations

$$[x *_m y]_n \sim [x]_n + [y]_n \text{ for } m < n.$$

We define the morphism $\partial_n : (\lambda C)_{n+1} \to (\lambda C)_n$ on generators by the formula:

$$\partial_n([x]_{n+1}) := [d_n^+ x]_n - [d_n^- x]_n.$$

We can easily check that the morphism $\partial$ is a differential. We define an augmentation $e : (\lambda C)_0 \to \mathbb{Z}$ by setting $e([x]_0) = 1$ on generators. We denote by $(\lambda C)_n^*$ the additive submonoid generated by the elements $[x]_n$. We then set:

$$\lambda C := (\{(\lambda C)_n\}_{n \in \mathbb{N}}, \{(\lambda C)_n^*\}_{n \in \mathbb{N}}, e).$$

This assignation lifts to a functor:

$$\lambda : \omega\text{-cat} \to \mathrm{ADC}$$

$$C \mapsto \lambda C.$$

# Example 1.2.1.3.

(1) For any integer $n$, $\lambda \mathbf{D}_n$ is the augmented directed complex whose underlying chain complex is given by:

$$\mathbb{Z} \xleftarrow{e} \mathbb{Z}[e_0^-, e_0^+] \xleftarrow{\partial_0} \dots \xleftarrow{\partial_{n-2}} \mathbb{Z}[e_{n-1}^-, e_{n-1}^+] \xleftarrow{\partial_{n-1}} \mathbb{Z}[e_n] \xleftarrow{\partial_n} 0 \leftarrow \dots$$

where for any $0 < k < n$ and $\alpha \in \{-, +\}$

$$e(e_0^\alpha) = 1 \quad \partial_{k-1}(e_k^\alpha) = e_{k-1}^+ - e_{k-1}^- \quad \partial_{n-1}(e_n) = e_{n-1}^+ - e_{n-1}^-.$$

25

CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

(2) The augmented directed complex λ[n] has for underlying chain complex:

$$\mathbb{Z} \stackrel{e}{\leftarrow} \mathbb{Z}[v_0, v_1, ..., v_n] \stackrel{\partial_0}{\leftarrow} \mathbb{Z}[v_{0,1}, v_{1,2}..., v_{n-1,n}] \stackrel{\partial_1}{\leftarrow} 0 \leftarrow ...$$

where for any k < n and α ∈ {−,+}

$$e(v_k) = e(v_n) = 1 \quad \partial_1(v_{k,k+1}) = v_{k+1} - v_k.$$

Definition 1.2.1.4. We now define the functor ν : ADC → ω-cat. Throughout, we fix an augmented directed complex (K, K*, e). A Steiner array (or simply a array) of dimension n is the data of a finite double sequence:

$$\begin{pmatrix} x_0^- & x_1^- & x_2^- & x_3^- & ... & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & x_3^+ & ... & x_n^+ \end{pmatrix}$$

such that

(1) $x_n^- = x_n^+$;
(2) For any $i \le n$ and α ∈ {−,+}, $x_i^\alpha$ is an element of $K_i^*$;
(3) For any $0 < i \le n$, $\partial_{i-1}(x_i^\alpha) = x_{i-1}^+ - x_{i-1}^-$;

An array is said to be coherent if $e(x_0^+) = e(x_0^-) = 1$.

Definition 1.2.1.5. We define the globular set νK, whose n-cells are the coherent arrays of dimension n. The source and target maps are defined for k < n by the formula:

$$d_k^\alpha \begin{pmatrix} x_0^- & x_1^- & x_2^- & ... & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & ... & x_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- & x_1^- & x_2^- & ... & x_{k-1}^- & x_k^\alpha \\ x_0^+ & x_1^+ & x_2^+ & ... & x_{k-1}^+ & x_k^\alpha \end{pmatrix}$$

There is an obvious group structure on the arrays:

$$\begin{pmatrix} x_0^- & x_1^- & ... & x_n^- \\ x_0^+ & x_1^+ & ... & x_n^+ \end{pmatrix} + \begin{pmatrix} y_0^- & y_1^- & ... & y_n^- \\ y_0^+ & y_1^+ & ... & y_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- + y_0^- & x_1^- + y_1^- & ... & x_n^- + y_n^- \\ x_0^+ + y_0^+ & x_1^+ + y_1^+ & ... & x_n^+ + y_n^+ \end{pmatrix}$$

- For two coherent arrays x and y such that $d_k^-(x) = d_k^+(y) = z$, we define their k-composition by the following formula:

$$x *_k y := x - z + y.$$

More explicitly:

$$\begin{pmatrix} x_0^- & ... & x_n^- \\ x_0^+ & ... & x_n^+ \end{pmatrix} *_k \begin{pmatrix} y_0^- & ... & y_n^- \\ y_0^+ & ... & y_n^+ \end{pmatrix} := \begin{pmatrix} y_0^- & ... & y_k^- & y_{k+1}^- + x_{k+1}^- & ... & y_n^- + x_n^- \\ x_0^+ & ... & x_k^+ & y_{k+1}^+ + x_{k+1}^+ & ... & y_n^+ + x_n^+ \end{pmatrix}$$

- For an integer m > n, we define the m-sized array $1_x^m$ as follows:

$$1_x^m := \begin{pmatrix} x_0^- & ... & x_n^- & 0 & ... & 0 \\ x_0^+ & ... & x_n^+ & 0 & ... & 0 \end{pmatrix}$$

The globular set νK, equipped with these compositions and units is an ω-category.

26

1.2. GRAY OPERATIONS

Construction 1.2.1.6. We define the functor $\nu : \mathrm{ADC} \to \omega$-cat which associates to an augmented directed complex $K$, the $\omega$-category $\nu K$, and to a morphism of augmented directed complexes $f : K \to L$, the morphism of $\omega$-categories.

$$\begin{array}{c c c c c} \nu f : & \nu K & \to & \nu L \\ & \left( \begin{array}{c c c} x _ {0} ^ {-} & \dots & x _ {n} ^ {-} \\ x _ {0} ^ {+} & \dots & x _ {n} ^ {+} \end{array} \right) & \mapsto & \left( \begin{array}{c c c} f _ {0} (x _ {0} ^ {-}) & \dots & f _ {n} (x _ {n} ^ {-}) \\ f _ {0} (x _ {0} ^ {+}) & \dots & f _ {n} (x _ {n} ^ {+}) \end{array} \right) \end{array}$$

Theorem 1.2.1.7 (Steiner). The functors $\lambda$ and $\nu$ form an adjoint pair

$$\lambda : \omega\text{-cat} \xrightarrow{\quad} \mathrm{ADC} : \nu$$

For a $\omega$-category $C$, the unit of the adjunction is given by:

$$\begin{array}{r c l} \eta : & C & \to \quad \nu \lambda C \\ & x \in C _ {n} & \mapsto \quad \left( \begin{array}{c c c} [ d _ {0} ^ {-} (x) ] _ {0} & \dots & [ d _ {n - 1} ^ {-} (x) ] _ {n - 1} \\ [ d _ {0} ^ {+} (x) ] _ {0} & \dots & [ d _ {n - 1} ^ {+} (x) ] _ {n - 1} \end{array} \right) \end{array}$$

For an augmented directed complex $K$, the counit is given by:

$$\begin{array}{r c l} \pi : & \lambda \nu K & \to \quad K \\ & [ x ] _ {n} \in (\lambda \nu K) _ {n} & \mapsto \quad x _ {n} ^ {+} = x _ {n} ^ {-} \end{array}$$

Proof. This is [Ste04, theorem 2.11].

Definition 1.2.1.8. A basis for an augmented directed complex $(K, K^{*}, e)$ is a graded set $B = (B_{n})_{n \in \mathbb{N}}$ such that for every $n$, $B_{n}$ is both a basis for the monoid $K_{n}^{*}$ and for the group $K_{n}$.

Remark 1.2.1.9. The elements of $B_{n}$ can be characterized as the minimal elements of $K_{n}^{*}\backslash 0$ for the following order relation:

$$x \leq y \text { iff } y - x \in K _ {n} ^ {*}$$

This shows that if a basis exists, it is unique.

Any element of $K_{n}$ can then be written uniquely as a sum $\sum_{b\in B_n}\lambda_b b$. This leads us to define new operations:

Definition 1.2.1.10. For an element $x := \sum_{b \in B_n} \lambda_b b$ of $K_n$, we define the positive part and the negative part:

$$\begin{array}{l} (x) _ {+} := \sum_ {b \in B _ {n}, \lambda_ {b} > 0} \lambda_ {b} b \\ (x) _ {-} := \sum_ {b \in B _ {n}, \lambda_ {b} < 0} - \lambda_ {b} b \end{array}$$

We then have $x = (x)_{+} - (x)_{-}$. An element $x$ is positive (resp. negative) when $x = (x)_{+}$ (resp. when $x = -(x)_{-}$). Let $y = \sum_{b \in B_n} \mu_b b$, we set :

$$x \wedge y := \sum_ {b \in B _ {n}} \min (\lambda_ {b}, \mu_ {b}) b$$

Eventually, we set

$$\begin{array}{l} \partial_ {n} ^ {+} (\_) := (\partial_ {n} (\_)) _ {+}: K _ {n + 1} \to K _ {n} ^ {*} \\ \partial_ {n} ^ {-} (\_) := (\partial_ {n} (\_)) _ {-}: K _ {n + 1} \to K _ {n} ^ {*} \end{array}$$

When an element $b$ of the basis is in the support of $x$, i.e $\lambda_{b} \neq 0$, we say that $b$ belongs to $x$, which is denoted by $b \in x$.

27

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

**Example 1.2.1.11.** For any integer $n$, $\lambda\mathbf{D}_n$ admits a basis, given by the graded set $B_{\lambda\mathbf{D}_n}$ fulfilling:

$$(B_{\lambda\mathbf{D}_n})_k := \begin{cases} \{e_k^-, e_k^+\} & \text{if } k < n \\ \{e_n\} & \text{if } k = n \\ \emptyset & \text{if } k > n \end{cases}$$

The augmented directed complex $\lambda[n]$ also admits a basis, given by the graded set $B_{\lambda\mathbf{D}_n}$ fulfilling:

$$(B_{\lambda\mathbf{D}_n})_k := \begin{cases} \{v_0, v_1, \dots, v_n\} & \text{if } k = 0 \\ \{v_{0,1}, v_{1,2}, \dots, v_{n-1,n}\} & \text{if } k = 1 \\ \emptyset & \text{if } k > 1 \end{cases}$$

**Definition 1.2.1.12.** Let $a \in K_n^*$. We set by a decreasing induction on $k \leq n$:

$$\begin{aligned} \langle a \rangle_k^\alpha &:= a & \text{if } k = n \\ &:= \partial_k^\alpha \langle a \rangle_{k+1}^\alpha & \text{if not} \end{aligned}$$

The array associated to $a$ is then:

$$\langle a \rangle := \begin{pmatrix} \langle a \rangle_0^- & \dots & \langle a \rangle_{n-1}^- & a \\ \langle a \rangle_0^+ & \dots & \langle a \rangle_{n-1}^+ & a \end{pmatrix}$$

The basis is said to be *unitary* when for any $b \in B$, the array $\langle b \rangle$ is coherent.

**Definition 1.2.1.13.** We define the relation $\odot$ on $B$ as being the smallest transitive and reflexive relation such that for any pair of elements of the basis $a, b$,

$$a \odot b \text{ if } (|a| > 0 \text{ and } b \in \langle a \rangle_{|a|-1}^-) \text{ or } (|b| > 0 \text{ and } a \in \langle b \rangle_{|b|-1}^+)$$

A basis is said to be *loop free* the relation $\odot$ is a (partial) order on $B$.

**Remark 1.2.1.14.** In [AM20], this notion is called *strongly loop free*.

**Example 1.2.1.15.** For any integer $n$, $\lambda\mathbf{D}_n$ and $\lambda[n]$ admit a loop free and unitary basis.

**Definition 1.2.1.16.** We now define the subcategory $\text{ADC}_B$ of ADC composed of augmented directed complexes which admit a unitary and loop free basis.

We will now describe the analog of the notion of basis for $\omega$-categories.

**Definition 1.2.1.17.** A $\omega$-category $C$ is *generated by composition* by a set $E \subset C$ when any cell can be written as a composition of elements of $E$ and iterated units of elements of $E$. This set is a *basis* if $\{[e]_{d(e)}\}_{e \in E}$ is a basis of the augmented directed complex $\lambda C$.

**Proposition 1.2.1.18.** *An $\omega$-category $C$ that admits a basis is an $(0, \omega)$-category.*

*Proof.* Let $C$ be an $\omega$-category that admits a basis $E$. Suppose that there exists a non trivial $n$-cell $\alpha$ that admits an inverse $\beta$. We then have $[\alpha]_n + [\beta]_n = [\alpha \circ_{n-1} \beta]_n = 0$. As $\lambda C$ is free, we have $[\alpha]_n = 0$. This implies the equality $[e]_n = 0$ for any element $e \in E$ of dimension $n$ that appears in a decomposition of $\alpha$. This is obviously in contradiction with the fact that $\{[e]_{d(e)}\}_{e \in E}$ is a basis of the augmented directed complex $\lambda C$. □

28

1.2. GRAY OPERATIONS

Definition 1.2.1.19. A basis $E$ of an $(0, \omega)$-category is :

(1) Loop free when $\{[e]_{d(e)}\}_{e \in E}$ is.
(2) Atomic when $[d_n^+ e]_n \wedge [d_n^- e]_n = 0$ for any $e \in E$ and any natural number $n$ strictly smaller than the dimension of $e$.

Proposition 1.2.1.20. If a loop free basis $E$ is atomic then $\{[e]\}_{e \in E}$ is unitary.

Proof. This is [Ste04, proposition 4.6].

Example 1.2.1.21. For any integer $n$, $\mathbf{D}_n$ and $[n]$ admit a loop free and atomic basis. More generally, [AM20, proposition 4.13] states that any globular sum admits a loop free and atomic basis.

Definition 1.2.1.22. Proposition 1.23 of [AGOR23] states that if an $(0, \omega)$-category admits a loop-free and atomic basis, it is unique. We then define the category $(0, \omega)$-cat$_\mathrm{B}$ as the full subcategory of $\omega$-cat composed of $(0, \omega)$-categories admitting an atomic and loop-free basis.

Theorem 1.2.1.23 (Steiner). Once restricted to $(0, \omega)$-cat$_\mathrm{B}$ and ADC$_\mathrm{B}$, the adjunction

$$\lambda : \omega\text{-cat} \xrightarrow{\perp} \mathrm{ADC} : \nu$$

becomes an adjoint equivalence, i.e. :

$$\lambda_{|(0, \omega)\text{-cat}_\mathrm{B}} \circ \nu_{|\mathrm{ADC}_\mathrm{B}} \cong id_{|\mathrm{ADC}_\mathrm{B}} \qquad id_{|(0, \omega)\text{-cat}_\mathrm{B}} \cong \nu_{|\mathrm{ADC}_\mathrm{B}} \circ \lambda_{|(0, \omega)\text{-cat}_\mathrm{B}}$$

Proof. See [Ste04, theorem 5.11].

Remark 1.2.1.24. If $K$ is an augmented directed complex admitting a unitary and loop-free basis $B$, then the $(0, \omega)$-category $\nu K$ admits an atomic and loop-free basis given by the set $\langle B \rangle := \{\langle b \rangle, b \in B\}$. Conversely if an $(0, \omega)$-category $C$ admits an atomic and loop-free basis $E$, then the augmented directed complex $\lambda C$ admits a unitary and loop-free basis given by the family of sets $[E_n] := \{[e]_{d(e)}, e \in E_n\}$. The isomorphisms

$$\lambda \nu K \cong K \quad \text{and} \quad C \cong \nu \lambda C$$

induce isomorphisms:

$$[\langle B \rangle] \cong B \quad \text{and} \quad E \cong \langle [E] \rangle.$$

Definition 1.2.1.25. Let $f : M \to N$ be a morphism between two augmented directed complexes admitting unitary and loop-free bases $B_M$ and $B_N$. The morphism $f$ is quasi-rigid if for any $n$, and any $b \in (B_M)_n$,

$$f_n(b) \neq 0 \Rightarrow f_n(b) \in B_N \text{ and } \nu(f)\langle b \rangle = \langle f_n(b) \rangle.$$

Theorem 1.2.1.26. Suppose given a commutative square in ADC$_\mathrm{B}$

$$\begin{array}{c} K \xrightarrow{k^0} M_1 \\ k^0 \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ M_0 \xrightarrow{l^0} M \end{array}$$

and such that all morphisms are quasi-rigid. Let $B_K$, $B_{M_0}$, $B_{M_1}$, $B_M$ be the bases of $K$, $M_0$, $M_1$, $M$.

29

CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

Then, this square is cocartesian if and only if for any $$n$$, the induced diagram of sets

$$\begin{array}{c} (B_K)_n \cup \{0\} \xrightarrow{k_n^0} (B_{M_1})_n \cup \{0\} \\ k_n^0 \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (B_{M_0})_n \cup \{0\} \xrightarrow{l_n^0} (B_M)_n \cup \{0\} \end{array}$$

is cocartesian. Furthermore, the induced square in $$(0, \omega)$$-cat

$$\begin{array}{c} \nu K \xrightarrow{\nu k^0} \nu M_1 \\ \nu k^0 \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \nu M_0 \xrightarrow{\nu l^0} \nu M \end{array}$$

is cocartesian.

Proof. This is a combination of theorems 3.1.2 and 3.2.7 of [Lou23].

### 1.2.2 2-Polygraphs and presheaves on $$\Theta_2$$

The objective of this section is to prove the following theorem

**Theorem 1.2.2.1.** Let $$k \le 1$$ be an integer, and let $$C$$ and $$D$$ be two $$(0, 2)$$-categories admitting loop-free and atomic bases (definition 1.2.1.19). Suppose there is a cocartesian square in $$(0, \omega)$$-cat of shape:

$$\begin{array}{c} \partial[[k], 1] \xrightarrow{\partial x} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [[k], 1] \xrightarrow{x} D \end{array}$$

Then, viewed as a morphism of $$\mathrm{Psh}(\Theta_2)$$, the morphism $$j: C \cup x \to D$$ is in $$\overline{\mathbf{W}_2}$$ which is the smallest precomplete class of morphism (definition 1.1.3.2) containing $$\mathbf{W}_2$$ (definition 1.1.2.15).

Informally, this theorem shows that the square appearing in the previous statement is homotopically cocartesian. This result is therefore a special case of the similar but much more general theorem proved by Campion in [Cam23b].

We fix a $$(0, 2)$$-category $$D$$ admitting a loop free and atomic basis until the end of this section.

**Definition 1.2.2.2.** Let $$v$$ be a 2-cell of $$D$$. The 2-support of $$v$$, denoted $$B_2^v$$, is the support of $$[v]_2$$ (definition 1.2.1.10). The 1-support of $$v$$, denoted $$B_1^v$$, is the union of the support of $$[\pi_1^+ v]_1$$ with $$(\partial_1^- B_2^v) \cup B_2^v$$.

For $$i = 1, 2$$, we define the relation $$<_i^v$$ as the smallest transitive relation on $$B_i^v$$ such that $$c <_i d$$ whenever

$$\langle c \rangle_i^- \wedge \langle d \rangle_i^+ \neq 0.$$

**Remark 1.2.2.3.** Remark that the two inclusions $$(B_0^v, <_0^v) \to (B, \odot)$$ and $$(B_1^v, <_1^v) \to (B, \odot)$$ are strictly increasing. As a consequence, $$<_0^v$$ and $$<_1^v$$ are (partial) orders.

30

1.2. GRAY OPERATIONS

Remark 1.2.2.4. The theorem 1.2.1.23 implies that $B_1^v$ is also equal to the union of the support of $[\pi_1^- v]_1$ with $(\partial_1^+ B_2^v) \cup B_2^v$.

Lemma 1.2.2.5. Let $v$ be a 2-cell of $D$, and $b, b'$ be two elements of $B_1^v$. The assertion $b <_0^v b'$ holds if and only if there exists a well-defined 0-composite

$$b *_0 \dots *_0 b'.$$

Proof. Straightforward.

Definition 1.2.2.6. Given a finite set $E$ endowed with a strict order $<$, an ordering of $E$ is a bijective sequence $(x_i)_{i \le n}$ of elements of $E$ such that for every $i < j$, $\neg(x_j < x_i)$.

Theorem 1.2.2.7. Let $v$ be a 2-cell of $D$, and $(w_i)_{i \le n}$ an ordering of $B_2^v$. There exists a decomposition of $v$ as

$$v := v_0 *_1 \dots *_1 v_n$$

such that for every $i < n$, $v_i$ is a 0-composition of an element of $w_i$ with several 1-generators of $D$.

Moreover, for any decomposition of $v$ as

$$v := v'_0 *_1 \dots *_1 v'_n$$

such that $v'_i$ is a 0-composition of a unique element $w'_i$ of $B_2^v$ with several 1-generators of $D$, then the sequence $\{w_i\}_{i \le n}$ is an ordering of $B_2^v$.

Proof. The first assertion is a consequence of [Lou23, theorem 2.47].

To show the second assertion, suppose given such a decomposition. We will proceed by contradiction and then suppose that there exist $i < j$ such that $w'_j < w'_i$. We can suppose without loss of generality that $i = 0$ and $j = n$.

By a direct induction on $n$ using [Lou23, lemma 2.43], we have

$$\partial_1^+([v'_0]_2) \le \partial_1^+([v'_0 *_1 \dots *_1 v'_n]_2) = \partial_1^+([v]_2)$$

$$\partial_1^-([v'_n]_2) \le \partial_1^-([v'_0 *_1 \dots *_1 v'_n]_2) = \partial_1^-([v]_2)$$

Moreover, the inequality $w'_n < w'_0$ implies

$$\partial_1^+([v'_0]_2) \wedge \partial_1^-([v'_n]_2) \neq 0$$

and then

$$\partial_1^+([v]_2) \wedge \partial_1^-([v]_2) \neq 0$$

which is absurd as $\partial_1^+([v]_2)$ and $\partial_1^-([v]_2)$ are respectively defined as the positive part and the negative part of $\partial([v]_2)$.

Lemma 1.2.2.8. Let $D$ be a $(0, 2)$-category and $f : C \to D$ be a morphism. Let $v$ be a 2-cell of $C$ and $b, b'$ two elements in the 1-support of $v$.

(1) $b <_0^v b'$ implies that for all $c \in B_1^{f(b)}$ and $c' \in B_1^{f(b')}$, $c <_0^{f(v)} c'$.
(2) $b <_1^v b'$ implies that for all $c \in B_2^{f(b)}$ and $c' \in B_2^{f(b')}$, $\neg(c' <_1^{f(v)} c)$.

31

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Proof. According to lemma 1.2.2.5, we have a well defined 0-composite

$$b * _ { 0 } \ldots * _ { 0 } b ^ { \prime }$$

and so a well defined 0-composite

$$f ( b ) * _ { 0 } \ldots * _ { 0 } f ( b ^ { \prime } )$$

Applying the decomposition given in theorem 1.2.2.7 to $f(b)$ and $f(b')$, we get a well-defined composite

$$w * _ { 0 } \ldots * _ { 0 } w ^ { \prime } .$$

where $w$ (resp. $w'$) is a 0-composite of $c$ (resp. $c'$) with 1-generators. This then implies $c < _ { 0 } ^ { f ( v ) } c'$.

We now deal with the second case. Let $c \in B _ { 2 } ^ { f ( b ) }$ and $c' \in B _ { 2 } ^ { f ( b ' ) }$. According to theorem 1.2.2.7 there exists a decomposition of $v$ of shape

$$v : = v _ { 0 } * v _ { 1 } * _ { 1 } \ldots * _ { 1 } v _ { n }$$

where for all $i \leq n$, $v_0$ is a 0-composite of a unique 2-generator with 1-generators. Moreover, the unique $i$ (resp. the unique $j$) such that $b$ belongs to $v_i$ (resp. such that $b'$ belongs to $v_j$) verifies $i < j$.

Applying the morphism $f$ and decomposing each $f(v_i)$ the same way, we get a decomposition

$$f ( v ) : = u _ { 0 } * u _ { 1 } * _ { 1 } \ldots * _ { 1 } u _ { m }$$

where for all $i \leq m$, $u_0$ is a 0-composite of a 2-generator with 1-generators, and such that the unique $i$ (resp. the unique $j$) such that $c$ belongs to $u_i$ (resp. such that $c'$ belongs to $w_j$) verifies $i < j$. The second assertion of theorem 1.2.2.7 then implies that $\neg(c' < _ { 1 } ^ { f ( v ) } c)$. □

Lemma 1.2.2.9. Let $v$ be a 2-cell, and $b, b'$ two different elements of the 2-support of $v$. Then $\neg(b < _ { 1 } ^ { v } b') \wedge \neg(b' < _ { 1 } ^ { v } b)$ implies that $(b < _ { 0 } ^ { v } b') \vee (b' < _ { 0 } ^ { v } b)$ holds.

Proof. We suppose that $\neg(b < _ { 1 } ^ { v } x) \wedge \neg(x < _ { 1 } ^ { v } b)$. We can then find an ordering with respect to $< _ { i } ^ { v }$ of $B _ { 2 } ^ { v }$ such that $b$ and $b'$ are one after the other. According to theorem 1.2.2.7, we have a decomposition of $v$ of shape $\ldots * _ { 1 } v _ { i } * _ { 1 } v _ { i + 1 } * _ { 1 } \ldots$ such that $v_i$ can be written as a 0-composite of $b$ and 1-generators and $v_{i+1}$ can be written in a 0-composite of $b'$ and 1-generators. We then have

$$v _ { i } : = \ldots * _ { 0 } b * _ { 0 } \ldots \quad v _ { i + 1 } : = \ldots * _ { 0 } b ^ { \prime } * _ { 0 } \ldots$$

and then an equality between the following 1-cells

$$\ldots * _ { 0 } \pi _ { 1 } ^ { - } b * _ { 0 } \ldots = \pi _ { 1 } ^ { - } v _ { i } = \pi _ { 1 } ^ { + } v _ { i + 1 } = \ldots * _ { 0 } \pi _ { 1 } ^ { + } b ^ { \prime } * _ { 0 } \ldots$$

As $\pi _ { 1 } ^ { - } b \wedge \pi _ { 1 } ^ { + } b ^ { \prime } = 0$, this implies that $\pi _ { 1 } ^ { - } v _ { i } = \pi _ { 1 } ^ { + } v _ { i + 1 }$ can be written as

$$\ldots * _ { 0 } \pi _ { 1 } ^ { - } b * _ { 0 } \ldots * _ { 0 } \pi _ { 1 } ^ { + } b ^ { \prime } * _ { 0 } \ldots \quad \mathrm { o r ~ a s } \quad \ldots * _ { 0 } \pi _ { 1 } ^ { + } b ^ { \prime } * _ { 0 } \ldots * _ { 0 } \pi _ { 1 } ^ { - } b * _ { 0 } \ldots$$

The cell $v_i * _ { 1 } v_{i+1}$ can then be written as

$$\ldots * _ { 0 } b * _ { 0 } \ldots * _ { 0 } b ^ { \prime } * _ { 0 } \ldots \quad \mathrm { o r ~ a s } \quad \ldots * _ { 0 } b ^ { \prime } * _ { 0 } \ldots * _ { 0 } b * _ { 0 } \ldots$$

This implies that $(b < _ { 0 } x) \vee (x < _ { 0 } b)$ holds.

Lemma 1.2.2.10. Let $v$ be a 2-cell, and $b, b'$ two elements of the 2-support of $v$. Then $b < _ { 0 } ^ { v } b'$ implies that for all $\alpha \in \{ -, + \}$, for all $c$ in $\langle b \rangle _ { 1 } ^ { \alpha }$, $c < _ { 0 } ^ { v } b'$ holds.

32

1.2. GRAY OPERATIONS

Proof. By lemma 1.2.2.5, there exists a sequence $(b_i)_{i \le n}$ such that $b_0 = b$, $b_n = b'$ and for all $i < n$, $b_i$ and $b_{i+1}$ are 0-composable. The sequence

$$b *_0 b_1 *_0 \dots *_0 b_{n-1} *_0 b'$$

is well defined, and then so is the sequence

$$\pi_1^\alpha b *_0 b_1 *_0 \dots *_0 b_{n-1} *_0 b'.$$

As $\pi_1^\alpha b$ is a 0-composite of $c$ with other elements of $B_1^c$, this concludes the proof.

Lemma 1.2.2.11. Let $r, u$ be two 2-cells of $D$ such that $B_1^u \subset B_1^r$. Let $x$ in $B_2^u$. Then there exists a unique decomposition of $u$ of shape

$$u = v *_1 w *_1 t$$

such that

(1) for any element $b$ in $B_2^v$, $b <_1^r x$;
(2) for any element $b$ in $B_2^t$, $x <_1^r b$;
(3) for any element $b$ in $B_2^w$, $\neg(b <_1^r x) \lor \neg(x <_1^r b)$

If for any element of $b$ in $B_2^u$ different from $x$, $\neg(b <_1^r x) \lor \neg(x <_1^r b)$, then there exists a unique decomposition of $u$ of shape

$$u = v *_0 w *_0 t$$

such that

(1) for any element $b$ in $B_1^v$, $b <_0^r x$;
(2) for any element $b$ in $B_1^t$, $x <_0^r b$;
(3) $w$ is either $x$ or a cell of lower dimension.

Proof. We will construct these two decompositions at the same time. To this extend, we will use the Steiner theory recalled in section 1.2.1.

Let $i$ be either 1 or 0. If $i = 0$, we then suppose furthermore that for any element of $b$ in $B_2^u$ different from $x$, $\neg(b <_1^r x) \lor \neg(x <_1^r b)$. We denote by

$$\left( \begin{array}{ccc} u_0^- & u_1^- & u_2^- \\ u_0^+ & u_1^+ & u_2^+ \end{array} \right)$$

the array corresponding to the cell $u$. For any $i < j \le 2$ and $\alpha \in \{-, +1\}$, we denote

$$\begin{array}{l} v_j^\alpha := \sum \{b \in [u]_j^\alpha, \ b <_i x\} \quad t_j^\alpha := \sum \{b \in [u]_j^\alpha, \ b >_i x\} \\ w_j^\alpha := \sum \{b \in [u]_j^\alpha, \ \neg(b <_j x) \land \neg(b <_j x)\} \end{array}$$

and

$$\begin{array}{lll} v_i^+ := u_i^+ & w_i^+ := v_i^- & t_i^+ := w_i^- \\ v_i^- := u_i^+ - \partial(v_{i+1}^-) & w_i^- := v_i^- - \partial(w_{i+1}^-) & t_i^- := u_i^- \end{array}$$

and for any $j < i$ and $\alpha \in \{-, +1\}$

$$v_j^\alpha := u_j^\alpha \quad w_j^\alpha := u_j^\alpha \quad t_j^\alpha := u_j^\alpha$$

33

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

By construction, we then have for any i ≤ j ≤ 2

$$u_j^\alpha = v_j^\alpha + w_j^\alpha + t_j^\alpha.$$

and

$$\partial(v_{i+1}^-) = v_i^+ - v_i^- \quad \partial(w_{i+1}^-) = w_i^+ - w_i^- \quad \partial(t_{i+1}^-) = t_i^+ - t_i^-$$

and

$$\partial(u_i^\alpha) = \partial(v_i^\alpha) = \partial(w_i^\alpha) = \partial(t_i^\alpha)$$

It then remains to show that for any i + 1 < j ≤ 2

$$\partial v_j^\alpha = v_{j-1}^+ - v_{j-1}^- \quad \partial w_j^\alpha = w_{j-1}^+ - w_{j-1}^- \quad \partial t_j^\alpha = t_{j-1}^+ - t_{j-1}^- \tag{1.2.2.12}$$

and

$$v_i^- \ge 0 \quad w_i^- \ge 0 \tag{1.2.2.13}$$

Indeed, if the assertions (1.2.2.12) and (1.2.2.13) are fulfilled, this implies that the sequences {v_j^β}, {w_j^β} and {t_j^β} are arrays and then correspond respectively to the unique cells v, w and t fulfilling the desired condition.

We first deal with the assertion (1.2.2.12). Suppose first that there exists an integer j such that i + 1 < j ≤ 2. This implies that i = 0. The lemma 1.2.2.9 then implies that w_2^α = λx with λ ∈ {0, 1}. By assumption, we have

$$\partial(u_2^\beta) = u_1^+ - u_1^-$$

and then

$$\partial(v_2^\beta) + \partial(w_2^\beta) + \partial(t_2^\beta) = v_1^+ - v_1^- + w_1^+ - w_1^- + t_1^+ - t_1^-$$

The lemma 1.2.2.10 implies that any element of the base belonging to ∂(v_2^β) (resp. to ∂(t_2^β)) is 0-inferior to x (resp. 0-superior to x). Moreover, for any b ∈ ∂(w_2^β) = λ∂x, we have ¬(b < 1^r x) ∨ ¬(x < 1^r b).

The previous equality then implies

$$\partial(v_2^\beta) = v_1^+ - v_1^- \quad \partial(w_2^\beta) = w_1^+ - w_1^- \quad \partial(t_2^\beta) = t_1^+ - t_1^-$$

We now deal with the assertion (1.2.2.12). We claim that we have

$$\partial^+ v_{i+1}^\alpha \wedge \partial^- w_{i+1}^\alpha = 0 \quad \partial^+ w_{i+1}^\alpha \wedge \partial^- t_{i+1}^\alpha = 0 \quad \partial^+ v_{i+1}^\alpha \wedge \partial^- t_{i+1}^\alpha = 0$$

Indeed, suppose that ∂+v_{i+1}^α ∧ ∂-w_{i+1}^α ≠ 0. This implies that there exists an element of the base b ∈ w_{i+1}^α and c ∈ v_{i+1}^α such that b < i c. As we have by definition c < i x, this directly implies that b < i x which is absurd. We show similarly the two other equalities. This implies that

$$\begin{array}{l} u_i^+ \ge \partial(u_{i+1}^-) \\ = \partial^+(v_{i+1}^- + w_{i+1}^- + t_{i+1}^-) \\ = \partial^+(v_{i+1}^-) + (\partial^+(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + (\partial^+(t_{i+1}^-) - \partial^-(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ \end{array}$$

As a consequence, we have

$$\begin{array}{l} v_i^- = u_i^+ - \partial(v_{i+1}^-) \\ = u_i^+ - \partial^+(v_{i+1}^-) + \partial^-(v_{i+1}^-) \\ \ge (\partial^+(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + (\partial^+(t_{i+1}^-) - \partial^-(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + \partial^-(v_{i+1}^-) \\ \ge (\partial^+(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + \partial^-(v_{i+1}^-) \\ \ge \partial^+(w_{i+1}^-) \end{array}$$

34

1.2. GRAY OPERATIONS

and

$$w _ { i } ^ { - } = v _ { i } ^ { - } - \partial ( w _ { i + 1 } ^ { - } ) = v _ { i } ^ { - } - \partial ^ { + } ( w _ { i + 1 } ^ { - } ) + \partial ^ { - } ( w _ { i + 1 } ^ { - } ) \geq 0$$

The two assertions (1.2.2.12) and (1.2.2.13) are then fulfilled, which concludes the proof.

Lemma 1.2.2.14. Let $C$ be a $(0, 2)$-category with a atomic and loop free basis. Let $x$ be a element of the base of $C$, and $y$ an element of the base of $D$. Let $f : C \to D$ be a morphism such that $\lambda f x = y$. Let $u$ be an 2-cell of $C$. We denote by $u =: u_0 *_0 u_1 *_0 u_2$ and $f(u) =: v_0 *_1 v_1 *_1 v_2$ the decomposition given by the lemma 1.2.2.11. Then

$$f ( u _ { 0 } ) = v _ { 0 } \quad f ( u _ { 1 } ) = v _ { 1 } \quad f ( u _ { 2 } ) = v _ { 2 }$$

Proof. This is a direct consequence of lemma 1.2.2.14.

Lemma 1.2.2.15. Let $C$ be a $(0, 2)$-category with a atomic and loop free basis. Let $x$ be a element of the base of $C$, and $y$ an element of the base of $D$. Let $f : C \to D$ be a morphism such that $y$ belongs to $\lambda f x$. Let $u$ be an 2-cell of $C$. We denote by $u =: u_0 *_1 u_1 *_1 u_2$ and $f(u) =: v_0 *_1 v_1 *_1 v_2$ the decompositions given by lemma 1.2.2.11. For any $i \leq 2$, we denote by $f(u_i) =: u_{i0} *_1 u_{i1} *_1 u_{i2}$ the decomposition given by lemma op cit. Then

$$v _ { 0 } = u _ { 0 0 } \quad v _ { 1 } = u _ { 0 1 } * _ { 1 } u _ { 0 2 } * _ { 1 } u _ { 1 0 } * _ { 1 } u _ { 1 1 } * _ { 1 } u _ { 1 2 } * _ { 1 } u _ { 2 0 } * _ { 1 } u _ { 2 1 } \quad v _ { 2 } = u _ { 2 2 }$$

Proof. This is a direct consequence of lemma 1.2.2.14.

Notation 1.2.2.16. Let $a$ be a globular sum of dimension lower or equal to 2. We denote by $\nabla$ the unique algebraic morphism $\mathbf{D}_2 \to a$. The 2-cell $\nabla$ is called the composite cell of $a$.

Remark 1.2.2.17. If $i : a \to a'$ is an algebraic morphism, and $f : a' \to C$ any morphism, the composite cell of $f : a' \to C$ is the same as the composite cell of $f i : a \to C$.

Definition 1.2.2.18. Let $b$ be an element of the base of $D$. A 2-cell $v$ of $D$ is 0-comparable with $b$ if $b \in B_2^v$ and if for any $b' \in B_2^v$, the assertion $\neg(b <_1^v b') \land \neg(b' <_1^v b)$ holds.

Lemma 1.2.2.19. Let $a$ be a globular sum of dimension lower or equal to 2. Let $x$ be a 2-cell of $D$. Let $f : a \to D$ be a morphism such that $f(\nabla)$ is 0-comparable with $x$. Then there exists a commutative triangle

$$\begin{array}{c} a ^ { \prime } \vee [ [ 1 ], 1 ] \vee a ^ { \prime \prime } \\ \xrightarrow [ f ] { i } \xrightarrow [ f ^ { \prime } \vee x \vee f ^ { \prime \prime } ] { } \\ D \end{array}$$

Moreover, this factorization is functorial in $C$.

Proof. Let $d$ be the (necessarily unique) element of the basis of $a$ such that $x \in [f(d)]_2$. Let $k \leq 1$ and $j : [[k], 1] \to \mathrm{Sp}_a$ be an element of the basis, i.e., a globular morphism.

If $j = d$, we consider the diagram

$$\begin{array}{c} [ [ 1 ], 1 ] \vee [ [ 1 ], 1 ] \vee [ [ 1 ], 1 ] \\ \xrightarrow [ f j ] { } \xrightarrow [ f ^ { \prime } \vee x \vee f ^ { \prime \prime } ] { } \\ D \end{array}$$

35

CHAPTER 1. \((0,\omega)\)-CATEGORIES AND PRESHEAVES ON \(\Theta\)

and if \( j \) is different of \( d \) by share the same 0-source and 0-target, we consider the diagram

![img-19.jpeg](img-19.jpeg)

where these two decompositions are induced by lemma 1.2.2.11. If the 0-source and 0-target of \( j \) are different of the one of \( d \), we consider the diagram

![img-20.jpeg](img-20.jpeg)

Taking the colimit over all such \(j: [[k], 1] \to a\), this induces a factorization

![img-21.jpeg](img-21.jpeg)

fulfilling the desired property. Eventually, the functoriality of this factorization is a consequence of the unicity of the decomposition given in lemma 1.2.2.11 and of lemma 1.2.2.8.

Until the end of this section, we fix an other  \( (0,2) \) -category C admitting a loop-free and atomic basis, and fitting in a cocartesian square of  \( (0,\omega) \) -cat of shape:

![img-22.jpeg](img-22.jpeg)

Construction 1.2.2.20. We define \(\Gamma_0\) as the full subcategory of \((\Theta_2)_{/D}\) whose objects are morphisms \(f:a\to D\) such that either \(f\) factors through \(C\), or the following conditions are fulfilled:

(1) \(f(\nabla)\) is 0-comparable with \(x\).
(2) \(\mathrm{Sp}_a\to a\to D\) factors through the \(\Theta\) -set \(C\cup x\)

We define \(\Gamma_1\) as the full subcategory of \((\Theta_2)_{/D}\) whose objects are morphisms \(v:a\to D\) such that \(\mathrm{Sp}_a\to a\to D\) factors through the \(\Theta\)-set \(C\cup \mathrm{colim}_{\Gamma_0}a\).

Lemma 1.2.2.21. The canonical morphism of \(\Theta\)-sets \(\iota: \operatorname{colim}_{\Gamma_0} a \to D\) is injective. Its image corresponds to morphisms \(f: a \to D\) such that either \(f\) factors through \(C\), or the 2-cell \(f(\nabla)\) is 0-comparable with \(x\).

Proof. First, remark that the morphism \( C \to \operatorname{colim}_{\Gamma_0} a \) is injective. To complete the characterization of the image of \( \iota \), let \( f: a \to D \) be a morphism such that \( f(\nabla) \) is 0-comparable with \( x \).

Consider now the factorization \( a \xrightarrow{i} a' \xrightarrow{g} D \) of \( f \) given by lemma 1.2.2.19. Every element of \( \mathrm{Sp}a' \) is sent to either an element of \( C \) or to \( x \). This implies that \( g \) belongs to \( \Gamma_0 \), which concludes the characterization of the image of \( \iota \).

36

1.2. GRAY OPERATIONS

Now, for the injectivity, suppose that there exists another element $h : b \to D$ of $\Gamma_0$ and a decomposition $a \xrightarrow{j} b \xrightarrow{h} D$ of $f : a \to D$. Up to further factorization, we can suppose that $j$ is algebraic and, according to lemma 1.2.2.19, that $j(\nabla)$ is 0-comparable with the (necessarily unique) element of the basis $c$ of $b$ such that $g(c) = x$.

Using once again the factorization lemma 1.2.2.19 on the morphism $j$ and the object $c$, and using the functoriality of this factorization, we get a commutative diagram

![img-23.jpeg](img-23.jpeg)

completing the proof of injectivity.

**Lemma 1.2.2.22.** *The canonical morphism of $\Theta$-sets $\iota : \operatorname{colim}_{\Gamma_1} a \to D$ is an equivalence.*

*Proof.* First, remark that the morphism $C \to \operatorname{colim}_{\Gamma_1} a$ is injective. To complete the surjectivity of $\iota$, let $f : a \to D$ be a morphism such that $x$ belongs to $[f(\nabla)]_2$. We denote by $c$ as the (necessary) unique element of the base of $a$ such that $x \in [f(c)]_2$.

Let $k \leq 1$ and $j : [[k], 1] \to \operatorname{Sp}_a$ be an element of the basis. If $j$ is $c$, we consider the following diagram

$$[[1], 1] \to [[3], 1] \to D$$

induced by the decomposition of lemma 1.2.2.11. Moreover, lemma 1.2.2.21 implies that $l$ belongs to $\Gamma_1$. If $j$ is different from $c$, we consider the diagram

$$[[k], 1] \to [[k], 1] \to D$$

Moreover, $fj$ factors through $C$ and then belongs to $\Gamma_1$. Taking the colimit over all such $j$, this induces a diagram

$$a \xrightarrow{i} a' \xrightarrow{g} D$$

whose composite is $f$ and such that $g$ is in $\Gamma_1$. This concludes the proof of the surjectivity of $\iota$.

To prove the injectivity, suppose now that there exists another element $h : b \to D$ and a decomposition $a \xrightarrow{j} b \xrightarrow{h} D$ of $f : a \to D$ with $h$ in $\Gamma_1$. If $j$ is $c$, we consider the diagram

![img-24.jpeg](img-24.jpeg)

where the left vertical morphisms are induced by the decomposition of lemma 1.2.2.11, the morphism $t$ obtained in applying for each 2-cell the decomposition of lemma *op cit*, and the morphism $\sigma$ send 0 on 0, 1 on 1, 2 on 8 and 3 on 9. The commutativity of this diagram is a consequence of lemma 1.2.2.15.

37

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

If j is different from c, we consider the diagram

![img-25.jpeg](img-25.jpeg)

Taking the colimit over all such j, this induces a diagram

![img-26.jpeg](img-26.jpeg)

where a'' → D is in Γ₁, which concludes the proof of injectivity.

Lemma 1.2.2.23. Let f : a → D be a morphism of Γ₀. We denote by Λ^Γ₀ a the subobject of a composed of all i ∈ Θ₂/ₐ such that fi factors through the Θ₂-set C ∪ x. Then the morphism Λ^Γ₀ a → a is in W̅₂.

Proof. If f factors through C, then Λ^Γ₀ a is equal to a. Suppose then that there exists a (necessarily unique) element of the base b such that f(b) = x.

There exists a unique decomposition of a as

$$a \cong a' \vee [[k] \vee [1] \vee [k'], 1] \vee a''$$

where the cell [[1], 1] → a is b and where

$$[[k], 1] \to a \to D \quad \text{and} \quad [[k'], 1] \to a \to D$$

factors through C.

We then have

$$\Lambda^{\Gamma_0} a \cong a' \vee [[k] \coprod_{[0]} [1] \coprod_{[0]} [k'], 1] \vee a''$$

As the functor a' ∨ [_, 1] ∨ a : Psh(Δ) → Psh(Θ) sends W̅₁ to W̅₂, and as

$$[k] \coprod_{[0]} b \coprod_{[0]} [k'] \to [k + 1 + k']$$

is in W̅₁, this concludes the proof.

Lemma 1.2.2.24. Let f : a → D be a morphism of Γ₁. We denote by Λ^Γ₁ a the subobject of a composed of all i ∈ Θ/ₐ such that fi factors through colim_Γ₀ a. Then the morphism Λ^Γ₁ a → a is in W̅₂.

Proof. If f factors through C, then Λ^Γ₁ a is equal to a. Suppose then that there exists a (necessarily unique) element of the base b such that x belongs to [f(b)]₂.

38

1.2. GRAY OPERATIONS

There exists a unique decomposition of $a$ as

$$a \cong a' \vee [[n] \vee [k] \vee [1] \vee [k'] \vee [n'], 1] \vee a''$$

where the cell $[[1], 1] \to a$ is $b$, and where $k$ and $k'$ are the maximal integers such that the image by the composite cell of

$$[[k] \vee [1] \vee [k'], 1] \to a$$

is 0-comparable with $x$, and such that

$$[[k], 1] \coprod [[k'], 1] \to a \to D$$

factors through $C$.

We then have

$$\Lambda^{\Gamma_0} a \cong a' \vee [[n + k] \coprod_{[k]} [k + 1 + k'] \coprod_{[k']} [k' + n'], 1] \vee a''$$

As the functor $a' \vee [\_, 1] \vee a : \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Theta)$ sends $\overline{\mathrm{W}_1}$ to $\overline{\mathrm{W}_2}$, and as

$$[n + k] \coprod_{[k]} [k + 1 + k'] \coprod_{[k']} [k' + n'] \to [n + k + 1 + k' + n']$$

is in $\overline{\mathrm{W}_1}$, this concludes the proof.

**Proposition 1.2.2.25.** *Let $C$ and $D$ be two $(0, 2)$-categories admitting loop-free and atomic bases, fitting in a cocartesian square of shape:*

$$\begin{array}{c} \partial [[1], 1] \xrightarrow{\partial x} C \\ \downarrow \qquad \qquad \qquad \downarrow f \\ [[1], 1] \xrightarrow{x} D \end{array}$$

*Then, viewed as a morphism of $\mathrm{Psh}(\Theta_2)$, the morphism $j : C \cup x \to D$ is in $\overline{\mathrm{W}_2}$.*

*Proof.* The category $\Gamma_0$ inherits from $\Theta_{/D}$ a structure of Reedy elegant category. The two functors

$$\begin{array}{c c c c c c} \Gamma_0 & \to & \mathrm{Psh}(\Delta) & \qquad \Gamma_0 & \to & \mathrm{Psh}(\Delta) \\ a \to D & \mapsto & \Lambda^{\Gamma_0} a & a \to D & \mapsto & a \end{array}$$

are Reedy cofibrant (definition 1.1.3.1). The morphism

$$C \cup x \cong \underset{\Gamma_0}{\mathrm{colim}} \, \Lambda^{\Gamma_0} a \to \underset{\Gamma_0}{\mathrm{colim}} \, \Lambda^{\Gamma_0} a$$

is then in $\overline{\mathrm{W}_2}$. We proceed similarly to demonstrate that the morphism

$$\underset{\Gamma_0}{\mathrm{colim}} \, \Lambda^{\Gamma_0} a \cong \underset{\Gamma_1}{\mathrm{colim}} \, \Lambda^{\Gamma_1} a \to \Lambda^{\Gamma_1} a \cong D$$

is in $\overline{\mathrm{W}_2}$. By stability by composition of $\overline{\mathrm{W}_2}$, this concludes the proof.

**Proposition 1.2.2.26.** *Let $C$ and $D$ be two $(0, 1)$-categories admitting loop-free and atomic bases, fitting in a cocartesian square of shape:*

$$\begin{array}{c} \partial [1] \xrightarrow{\partial x} C \\ \downarrow \qquad \qquad \qquad \downarrow f \\ [1] \xrightarrow{x} D \end{array}$$

*Then, viewed as a morphism of $\mathrm{Psh}(\Delta)$, the morphism $j : C \cup x \to D$ is in $\overline{\mathrm{W}_1}$.*

39

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Proof. We denote by Υ the full subcategory of Δ/D whose objects are morphisms f : [n] → D such that Sp[n] → [n] → D factors through the Θ-set C ∪ x.

Given f : [n] → D in Υ, we denote by Λ^Υ[n] the subobject of [n] composed of all i ∈ Δ/[n] such that fi factors through C ∪ x. We can proceed as in lemma 1.2.2.23 to show that the canonical morphism Λ^Υ[n] → [n] is in W̅₁.

Now, remark that the category Υ inherits from Δ/D a structure of Reedy elegant category. The two functors

$$\begin{array}{c c c c c c} \Upsilon & \to & \mathrm{Psh}(\Delta) & \Upsilon & \to & \mathrm{Psh}(\Delta) \\ [n] \to D & \mapsto & \Lambda^\Upsilon[n] & [n] \to D & \mapsto & [n] \end{array}$$

are Reedy cofibrant (definition 1.1.3.1). As the colimit of the first one is C ∪ x and the colimit of the second one is D, this concludes the proof.

proof of theorem 1.2.2.1. If n = 0, this is straightforward, and if n = 2, it follows from proposition 1.2.2.25.

It then remains to prove the case n = 1. Let S be the set of generators of C of dimension 2. A repeated application of proposition 1.2.2.25 and the stability by pushout and transfinite composition of W̅₂ implies that the two vertical morphisms of the following square are in W̅₂:

$$\begin{array}{c} \tau_1 C \cup x \cup_{y \in S} y \longrightarrow \tau_1 D \cup_{y \in S} y \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ C \cup x \longrightarrow D \end{array}$$

Moreover, the proposition 1.2.2.26 implies that the canonical morphism

$$\tau_1 C \cup x \to \tau_1 D$$

is in W̅₂, and so is the top horizontal morphism of the previous square. By stability of left cancellation of W̅₂, this concludes the proof.

### 1.2.3 Gray operations on augmented directed complexes

We follow Steiner ([Ste04]) and Ara-Maltsiniotis ([AM20]) for the definitions and first properties of Gray operations on augmented directed complexes.

Definition 1.2.3.1. Let (K, K*, e) and (L, L*, f) be two augmented directed complexes. We define the Gray tensor product of (K, K*, e) and (L, L*, f) as the augmented directed complex

$$(K, K^*, e) \otimes (L, L^*, f) := (K \otimes L, (K \otimes L)^*, e \otimes f)$$

where

- K ⊗ L is the chain complex whose value on n is:

$$(K \otimes L)_n := \oplus_{k+l=n} K_k \otimes L_l$$

and the differential is the unique graded group morphism fulfilling:

$$\partial(x \otimes y) := \partial x \otimes y + (-1)^{|x|} x \otimes \partial y$$

where we set the convention ∂x := 0 if |x| = 0.

40

1.2. GRAY OPERATIONS

- $$(K \otimes L)^*$$ is given on all integer $$n$$ by :

$$(K \otimes L)_n^* := \oplus_{k+l=n} K_k^* \otimes L_l^*.$$

- $$e \otimes f : K_0 \otimes L_0 \to \mathbb{Z}$$ is the unique morphism fulfilling

$$(e \otimes f)(x \otimes y) = e(x)f(y).$$

The Gray tensor product induces a monoidal structure on ADC. Its unit is given by $$\lambda\mathbf{D}_0$$. Furthermore, Steiner shows that if $$K$$ and $$L$$ admit loop free and unitary bases, so does $$K \otimes L$$. The basis of $$K \otimes L$$ is given by the set of elements of shape $$b \otimes b'$$ where $$b$$ and $$b'$$ are respectively elements of the bases of $$K$$ and $$L$$. The monoidal structure then restricts to a monoidal structure on $$\mathrm{ADC_B}$$.

**Notation 1.2.3.2.** To simplify notation, the augmented directed complex $$\lambda[1]$$ will simply be denoted by [1].

**Definition 1.2.3.3.** The induced functor

$$\_ \otimes [1] : \mathrm{ADC} \to \mathrm{ADC}$$

is called the *Gray cylinder*. For $$(K, K^*, e)$$ an augmented directed complex, we then have

$$(K, K^*, e) \otimes [1] := (K \otimes [1], (K \otimes [1])^*, e)$$

where

- $$K \otimes [1]$$ is the chain complex whose value on $$n$$ is:

$$(K \otimes [1])_n := \begin{cases} \{x \otimes \{\epsilon\}, x \in K_0, \epsilon = 0, 1\} & \text{if } n = 0 \\ \{x \otimes \{\epsilon\}, x \in K_n, \epsilon = 0, 1\} \oplus \{x \otimes [1], x \in K_{n-1}\} & \text{if } n > 0 \end{cases}$$

and the differential is the unique graded group morphism fulfilling:

$$\partial(x \otimes [1]) := \partial x \otimes [1] + (-1)^{|x|} (x \otimes \{1\} - x \otimes \{0\}) \quad \partial(x \otimes \{\epsilon\}) = (\partial x) \otimes \{\epsilon\}$$

for $$\epsilon \in \{0, 1\}$$, and where we set the convention $$\partial x := 0$$ if $$|x| = 0$$.

- $$(K \otimes [1])^*$$ is given on all integer $$n$$ by :

$$(K \otimes [1])_n^* := \begin{cases} \{x \otimes \{\epsilon\}, x \in K_0^*, \epsilon = 0, 1\} & \text{if } n = 0 \\ \{x \otimes \{\epsilon\}, x \in K_n^*, \epsilon = 0, 1\} \oplus \{x \otimes [1], x \in K_{n-1}^*\} & \text{if } n > 0 \end{cases}$$

- $$e : (K \otimes [1])_0 \to \mathbb{Z}$$ is the unique morphism fulfilling

$$e(x \otimes \{0\}) = e(x \otimes \{1\}) = e(x).$$

**Proposition 1.2.3.4.** *Let $$A$$ be an augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexe $$A \otimes [1]$$ has no non-trivial automorphisms.*

*Proof.* Let $$\phi : A \otimes [1] \to A \otimes [1]$$ be an automorphism. The morphism $$\phi$$ then induces a bijection on the elements of the basis of $$A \otimes [1]$$.

Let $$(E, F)$$ be a partition of the set $$(B_{A \otimes [1]})_0$$ such that

41

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

(1) there exists no element of (B_{A⊗[1])_1} whose source is in is F and target in E.
(2) for any x, y ∈ E and v ∈ (B_{A⊗[1])_1} such that ∂v = y - x, there exist an element w ∈ (B_{A⊗[1])_1} such that ∂⁻w = y and an element α ∈ (B_{A⊗[1])_2} with ∂⁺α = w + v.
(3) for any x, y ∈ F and v ∈ (B_{A⊗[1])_1} such that ∂v = y - x, there exist an element w ∈ (B_{A⊗[1])_1} such that ∂⁺w = x and an element α ∈ (B_{A⊗[1])_2} with ∂⁻α = w + v.

Suppose now that there exists an object a of (B_A)_0 such that a ⊗ {1} in E. As we have ∂a ⊗ [1] = a ⊗ {1} - a ⊗ {0}, a ⊗ {1} is in E. There exist then an element α ∈ (B_{A⊗[1])_2} with ∂⁺α = a ⊗ [1] + w with ∂⁺a ⊗ [1] = ∂⁻w. However, by construction of A ⊗ [1], there exist no such element α. This implies that any element of E is of shape a ⊗ {0} and we can show similarly that every element of F is of shape a ⊗ {1}.

Conversely, we claim that the partition ((B_{A⊗{0})_0}, (B_{A⊗{1})_0}) fulfills these conditions. The first one is obvious. For the second, there exist a ∈ (B_A)_0 and u ∈ (B_A)_0 such that y = a ⊗ {0} and v := u ⊗ {0} and we then choose w := a ⊗ [1] and α := u ⊗ [1]. We proceed similarly for the last condition.

The partition ((B_{A⊗{0})_0}, (B_{A⊗{1})_0}) is then the unique one fulfilling the previous three condition. As φ preserves such partition, this implies that φ(B_{A⊗{0})}) = B_{A⊗{0}} and φ(B_{A⊗{1})}) = B_{A⊗{1}}.

Now, remark that for any element e ∈ (A ⊗ [1])_{n+1}^*, there exists x ∈ A_n^* such that x ⊗ [1] ≤ e if and only if there exists y ∈ A_{n-1}^* such that y ⊗ [1] ≤ ∂⁺e. By a direct induction, this implies that there exists x ∈ A_n^* such that x ⊗ [1] ≤ e if and only if ∂₀⁻e is in A₀^* ⊗ {0} and ∂₀⁺e is in A₀^* ⊗ {1}.

Combined with the previous observation, this implies that for any element x of the basis of A_n, φ(x ⊗ {ε}) is of shape x' ⊗ {ε} with ε ∈ {0, 1}. The automorphism φ then induces by restriction automorphisms φ_{A⊗{0}}: A ⊗ {0} → A ⊗ {0} and φ_{A⊗{1}}: A ⊗ {1} → A ⊗ {1}, and the hypothesis implies that they are the identity.

We now show by induction on n that φ_n : (A ⊗ [1])_n → (A ⊗ [1])_n is the identity. Suppose the result true at the stage n. For any element x of the basis of A_n, we then have

$$\partial\phi(x \otimes [1]) = \phi(\partial(x \otimes [1])) = \partial(x \otimes [1]).$$

By the definition of the derivative of A ⊗ [1], and as φ preserves the basis, this forces the equality φ(x ⊗ [1]) = x ⊗ [1]. As we already know that for any element x of the basis of A_{n+1} we have φ(x ⊗ {ε}) = x ⊗ {ε}t for any ε ∈ {0, 1}, this concludes the induction.

We then have φ = id and A ⊗ [1] has no non trivial automorphisms.

Definition 1.2.3.5. We define the Gray cone

$$\begin{array}{c c c} \text{ADC} & \to & \text{ADC} \\ K & \mapsto & K \star 1 \end{array}$$

where K ⋆ 1 is defined as the following pushout:

$$\begin{array}{c} K \otimes \{1\} \longrightarrow K \otimes [1] \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(1.2.3.6)} \\ 1 \longrightarrow K \star 1 \end{array}$$

According to [AM20, corollary 6.21], if K admits a loop free and unitary basis, this is also the case for K ⋆ 1. The Gray cone then induces a functor:

$$\begin{array}{c c c} \text{ADC}_\text{B} & \to & \text{ADC}_\text{B} \\ K & \mapsto & K \star 1 \end{array}$$

42

1.2. GRAY OPERATIONS

Remark 1.2.3.7. Unfolding the definition, we have

$$(K, K', e) \star 1 := (K \star 1, (K \star 1)^*, e)$$

where

- $K \star 1$ is the chain complex whose value on $n$ is:

$$(K \star 1)_n := \begin{cases} \mathbb{Z}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n\} \oplus \{x \star 1, x \in K_{n-1}\} & \text{if } n > 0 \end{cases}$$

and the differentials are the unique graded group morphisms fulfilling:

$$\partial(x \star 1) = \partial x \star 1 + (-1)^{|x|} x \star \emptyset \quad \partial(x \star \emptyset) = \partial x \star \emptyset$$

where we set the convention $\partial x := 0$ if $|x| = 0$.

- The graded monoids $(K \star 1)^*$ is given on any integer $n$ by :

$$(K \star 1)^* := \begin{cases} \mathbb{N}[\emptyset \star 1] \oplus \{x \star \emptyset, x \in K_0^*\} & \text{if } n = 0 \\ \{\emptyset \star x, x \in K_n^*\} \oplus \{x \star 1, x \in K_{n-1}^*\} & \text{if } n > 0 \end{cases}$$

- The augmentation $e : (K \star 1)_0 \to \mathbb{Z}$ is the unique ones fulfilling

$$e(\emptyset \star 1) = 1 \quad e(x \star \emptyset) = e(x)$$

The basis of $K \star 1$ is given by the reunion of $\emptyset \star 1$ and of the set of elements of shape $b \star 1$ where $b$ is an element of the basis of $K$.

Proposition 1.2.3.8. Let $A$ be an augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexe $A \star 1$ has no non-trivial automorphisms.

Proof. Let $\phi : A \star 1 \to A \star 1$ be an automorphism. The morphism $\phi$ then induces a bijection on the elements of the basis of $A \star 1$.

As the element $\emptyset \star 1 \in (A \star 1)_0$ is the only element of the basis such that for all $v \in (A \star 1)_1$ $\partial_0^-(v) \neq \emptyset \star 1$, it is preserved by $\phi$. As a consequence, for any element $x$ of the basis of $A_0$, $\phi(x \star \emptyset)$ is of shape $x' \star \emptyset$. The morphism $\phi$ then preserves $(A \star \emptyset)_0$.

Now, remark that for any element $e \in (A \star 1)_{n+1}^*$, there exists $x \in A_n^*$ such that $x \star 1 \leq e$ if and only if there exists $y \in A_{n-1}^*$ such that $y \star 1 \leq \partial^+ e$. By a direct induction, this implies that there exists $x \in (A \star 1)_n^*$ such that $x \star 1 \leq e$ if and only if $\partial_0^+ e \in \mathbb{Z}[\emptyset \star 1]$.

Combined with the previous observation, this implies that for any element $x$ of the basis of $A_n$, $\phi(x \star \emptyset)$ is of shape $x' \star \emptyset$. The automorphism $\phi$ then induces by restriction an automorphism $\phi_{|A \star \emptyset} : A \to A$, and the hypothesis implies that it is the identity.

We now show by induction on $n$ that $\phi_n : (A \star 1)_n \to (A \star 1)_n$ is the identity. Suppose the result true at the stage $n$. For any element $x$ of the basis of $A_n$, we then have

$$\partial \phi(x \star 1) = \phi(\partial(x \star 1)) = \partial(x \star 1).$$

By the definition of the derivative of $A \star 1$, and as $\phi$ preserves the basis, this forces the equality $\phi(x \star 1) = x \star 1$. As we already know that for any element $x$ of the basis of $A_{n+1}$ we have $\phi(x \star \emptyset) = x \star \emptyset$, this concludes the induction.

We then have $\phi = id$ and $A \star 1$ has no non trivial automorphisms.

43

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Definition 1.2.3.9. We define the suspension as the functor

$$[\_, 1] : \mathrm{ADC} \to \mathrm{ADC}$$

where $[K, 1]$ is defined as the following pushout:

$$\begin{array}{c} K \otimes \{0, 1\} \longrightarrow K \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ 1 \coprod 1 \longrightarrow [K, 1] \end{array} \tag{1.2.3.10}$$

We leave to the reader to check that $[K, 1]$ admits a loop free and unitary basis when this is the case for $K$. This functor then induces a functor:

$$[\_, 1] : \mathrm{ADC_B} \to \mathrm{ADC_B}$$

Remark 1.2.3.11. Unfolding the definition, we have

$$[(K, K', e), 1] := ([K, 1], ([K, 1])^*, e)$$

where

- $[K, 1]$ is the chain complex whose value on $n$ is:

$$[K, 1] := \left\{ \begin{array}{ll} \mathbb{Z}[\{0\}, \{1\}] & \text{if } n = 0 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 0 \end{array} \right.$$

and the differential is the unique graded group morphism fulfilling:

$$\partial([x, 1]) := \left\{ \begin{array}{ll} \{1\} - \{0\} & \text{if } |x| = 0 \\ [\partial x, 1] & \text{if } |x| > 0 \end{array} \right.$$

- $([K, 1])^*$ is given on all integer $n$ by:

$$([K, 1])_n^* := \left\{ \begin{array}{ll} \mathbb{N}[0, 1] & \text{if } n = 0 \\ \{[x, 1], x \in K_{n-1}^*\} & \text{if } n > 0 \end{array} \right.$$

- $e : ([K, 1])_0 \to \mathbb{Z}$ is the unique morphism fulfilling

$$e(0) = e(1) = e(x).$$

The basis of $[K, 1]$ is given by the reunion of $\{0\}$, $\{1\}$ and of the set of elements of shape $[b, 1]$ where $b$ is an element of the basis of $K$.

Proposition 1.2.3.12. Let $A$ be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complex $[A, 1]$ has no non-trivial automorphisms.

Proof. Let $\phi : [A, 1] \to [A, 1]$ be an automorphism. As the element $\{1\} \in ([A, 1])_0$ is the only element of the basis such that for all $v \in [A, 1]_1$ $\partial_0^-(v) \neq \{1\}$, it is preserved by $\phi$. As a consequence, $\phi$ also preserves $\{0\}$. The induced morphism $\phi_0 : [A, 1]_0 \to [A, 1]_0$ is then the identity.

Now, remark that $(\phi_{n+1})_{n \in \mathbb{N}} : A \to A$ is an automorphism and is then the identity. This implies that for all $n > 0$, $\phi_n : [A, 1]_n \to [A, 1]_n$ is then identity, which concludes the proof.

44

1.2. GRAY OPERATIONS

Definition 1.2.3.13. We define the wedges as the functors

$$[\_, 1] \vee [1] : \mathrm{ADC} \to \mathrm{ADC} \qquad [1] \vee [\_, 1] : \mathrm{ADC} \to \mathrm{ADC}$$

where $[K, 1] \vee [1]$ and $[1] \vee [K, 1]$ are defined as the following pushouts:

$$\begin{array}{c} \lambda[0] \xrightarrow{\{0}} [1] \\ \{1\} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [K, 1] \longrightarrow [K, 1] \vee [1] \end{array}$$

$$\begin{array}{c} \lambda[0] \xrightarrow{\{0}} [K, 1] \\ \{1\} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \longrightarrow [1] \vee [K, 1] \end{array}$$

Once again, we can easily check that $[K, 1] \vee [1]$ and $[1] \vee [K, 1]$ have a loop free and unitary basis when this is the case for $K$. These functors then induce functors

$$[\_, 1] \vee [1] : \mathrm{ADC}_{\mathrm{B}} \to \mathrm{ADC}_{\mathrm{B}} \qquad [1] \vee [\_, 1] : \mathrm{ADC}_{\mathrm{B}} \to \mathrm{ADC}_{\mathrm{B}}$$

Unfolding the definition, we have

$$[(K, K', e), 1] \vee [1] := ([K, 1] \vee [1], ([K, 1] \vee [1])^*, e)$$

$$[1] \vee (K, K', e), 1] := ([1] \vee [K, 1], ([1] \vee [K, 1])^*, e)$$

where

- $[K, 1] \vee [1]$ and $[1] \vee [K, 1]$ are the chain complexes whose value on $n$ are:

$$[K, 1] \vee [1] := \left\{ \begin{array}{ll} \mathbb{Z}[\{0\}, \{1\}, \{2\}] & \text{if } n = 0 \\ \{[x, 1], x \in K_0\} \oplus \mathbb{Z}[e_1] & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 1 \end{array} \right.$$

$$[1] \vee [K, 1] := \left\{ \begin{array}{ll} \mathbb{Z}[\{0\}, \{1\}, \{2\}] & \text{if } n = 0 \\ \mathbb{Z}[e_1] \oplus \{[x, 1], x \in K_0\} & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 1 \end{array} \right.$$

and the differentials are the unique graded group morphism fulfilling:

$$\partial_{[K, 1] \vee [1]}(e_1) := \{2\} - \{1\} \quad \partial_{[K, 1] \vee [1]}([x, 1]) := \left\{ \begin{array}{ll} \{1\} - \{0\} & \text{if } |x| = 0 \\ [\partial x, 1] & \text{if } |x| > 0 \end{array} \right.$$

$$\partial_{[1] \vee [K, 1]}(e_1) := \{1\} - \{0\} \quad \partial_{[1] \vee [K, 1]}([x, 1]) := \left\{ \begin{array}{ll} \{2\} - \{1\} & \text{if } |x| = 0 \\ [\partial x, 1] & \text{if } |x| > 0 \end{array} \right.$$

- $([K, 1] \vee [1])^*$ and $([1] \vee [K, 1])^*$ are given on all integer $n$ by:

$$([K, 1] \vee [1])^* := \left\{ \begin{array}{ll} \{\{0\}, \{1\}, \{2\}\} & \text{if } n = 0 \\ \{[x, 1], x \in K_0^*\} \oplus \mathbb{N}[e_1] & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 1 \end{array} \right.$$

$$([1] \vee [K, 1])^* := \left\{ \begin{array}{ll} \{\{0\}, \{1\}, \{2\}\} & \text{if } n = 0 \\ \mathbb{N}[e_1] \oplus \cup\{[x, 1], x \in K_0^*\} & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}^*\} & \text{if } n > 1 \end{array} \right.$$

45

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

- The augmentations e are the unique morphism fulfilling

$$e(\{0\}) = e(\{1\}) = e(\{2\}) = 1.$$

**Proposition 1.2.3.14.** Let A be a non null augmented directed complex admitting no non-trivial automorphisms. Then the augmented directed complexes [A, 1] ∨ [1] and [1] ∨ [A, 1] have no non-trivial automorphisms.

Proof. The proof is similar to the one of proposition 1.2.3.12 and we leave it to the reader.

**Definition 1.2.3.15.** There are two canonical morphisms

$$\nabla : \Sigma K \to \Sigma K \vee [1] \qquad \nabla : \Sigma K \to [1] \vee \Sigma K$$

that are the unique ones fulfilling

$$\nabla(\{0\}) := \{0\} \quad \nabla(\{1\}) := \{2\} \quad \nabla([x, 1]) := \left\{ \begin{array}{ll} [x, 1] + e_1 & \text{if } |x| = 0 \\ [x, 1] & \text{if } |x| > 0 \end{array} \right.$$

When we write ΣK → ΣK ∨ [1] and ΣK → [1] ∨ ΣK and nothing more is specified, it will always mean that we considered the morphisms ∇.

**Proposition 1.2.3.16.** Let K be an augmented directed complex. There is a natural transformation between the colimit of the following diagram

$$[1] \vee [K, 1] \longleftarrow [K \otimes \{0\}, 1] \longrightarrow [K \otimes [1], 1] \longleftarrow [K \otimes \{1\}, 1] \longrightarrow [K, 1] \vee [1]$$

and [K, 1] ⊗ [1].

Proof. The cone is induced by morphisms

$$\begin{array}{c} [1] \vee [K, 1] \to [K, 1] \otimes [1] \\ (\text{resp. } [K, 1] \vee [1] \to [K, 1] \otimes [1]) \end{array}$$

sending an element x in the basis of [1] to {0} ⊗ x (resp. {1} ⊗ x), an element y in the basis of [K, 1] to y ⊗ {1} (resp. y ⊗ {0}), and by the morphism

$$f : [K \otimes [1], 1] \to [K, 1] \otimes [1]$$

defined by the formula

$$f([x \otimes y, 1]) := [x, 1] \otimes y$$

for x in the basis of K and y in the basis of [1]. We leave it to the reader to check the compatibilities of this three morphisms.

### 1.2.4 Gray operations on (0, ω)-categories

We follow Ara-Maltsiniotis [AM20] for the definitions and first properties of Gray operations on (0, ω)-categories. Originally, these authors work with ω-categories, and not with (0, ω)-categories. However, this modification does not affect proof, and we then allow ourselves to use their results in our framework.

46

1.2. GRAY OPERATIONS

**Theorem 1.2.4.1** (Steiner, Ara-Maltsiniotis). *There is a unique colimit preserving monoidal structure on $(0, \omega)$-cat, up to a unique monoidal isomorphism, making the functor $\nu_{|\mathrm{ADC}_{\mathrm{B}}}: \mathrm{ADC}_{\mathrm{B}} \to (0, \omega)$-cat a monoidal functor, when $\mathrm{ADC}_{\mathrm{B}}$ is endowed with the monoidal structure given by the Gray tensor product.*

*Proof.* This is [AM20, theorem A.15].

**Definition 1.2.4.2.** The monoidal product on $(0, \omega)$-cat induced by the previous theorem is called the *Gray tensor product* and is denoted by $\otimes$. It's unit is $\mathbf{D}_0$. If $C$ and $D$ are $(0, \omega)$-categories with an atomic and loop free basis, we have by construction

$$C \otimes D := \nu(\lambda C \otimes \lambda D).$$

**Proposition 1.2.4.3.** *There are equivalences*

$$(C \otimes D)^{\mathrm{op}} \cong D^{\mathrm{op}} \otimes C^{\mathrm{op}} \qquad (C \otimes D)^{\circ} \cong C^{\circ} \otimes D^{\circ} \qquad (C \otimes D)^{\mathrm{co}} \cong D^{\mathrm{co}} \otimes C^{\mathrm{co}}$$

*natural in $C, D : (0, \omega)$-cat.*

*Proof.* This is [AM20, proposition A.20].

**Definition 1.2.4.4.** The functors

$$\_ \otimes [1] : (0, \omega)\text{-cat} \to (0, \omega)\text{-cat} \quad [1] \otimes \_ : (0, \omega)\text{-cat} \to (0, \omega)\text{-cat}$$

are respectively called the *Gray cylinder* and the *Gray $\circ$-cylinder*.

**Proposition 1.2.4.5.** *Let $C$ be an $(\infty, \omega)$-category. The following canonical square*

$$\begin{array}{c} C \otimes \{0, 1\} \longrightarrow C \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \coprod 1 \longrightarrow [C, 1] \end{array}$$

*is cocartesian*

*Proof.* As all these functors commute with colimits, it is sufficient to demonstrate this assertion when $C$ is a globular sum, and *a fortiori* when $C$ admits a loop free and atomic basis. In this case, remark that all the morphisms appearing in canonical cartesian square

$$\begin{array}{c} \lambda C \otimes \{0, 1\} \longrightarrow \lambda C \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \coprod 1 \longrightarrow [\lambda C, 1] \end{array}$$

are quasi-rigid. The results then follow from an application of theorem 1.2.1.26.

**Remark 1.2.4.6.** Applying the duality $(\_)^{\mathrm{op}}$ to the computation achieved in appendix B.1 of [AM20], we can give an explicit expression of $\mathbf{D}_n \otimes [1]$. As a polygraph, the generating arrows of $\mathbf{D}_n \otimes [1]$ are:

$$\begin{array}{l} e_k^{\epsilon} \otimes \{0\} \quad e_k^{\epsilon} \otimes \{1\} \quad e_k^{\epsilon} \otimes [1] \\ a_0^- \otimes e_k^{\epsilon} \qquad a_0^+ \otimes e_k^{\epsilon} \qquad a \otimes e_k^{\epsilon} \end{array}$$

47

CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

where $$\epsilon$$ is either $$+$$ or $$-$$, $$k \leqslant n$$ and $$e_n^+ = e_n^-$$. Their source and target are given as follows:

$$\pi^-(e_k^\epsilon \otimes \{0\}) = e_{k-1}^- \otimes \{0\} \quad \pi^+(e_k^\epsilon \otimes \{0\}) = e_{k-1}^+ \otimes \{0\}$$

$$\pi^-(e_k^\epsilon \otimes \{1\}) = e_{k-1}^- \otimes \{1\} \quad \pi^+(e_k^\epsilon \otimes \{1\}) = e_{k-1}^+ \otimes \{1\}$$

$$\pi^-(e_{2k}^\epsilon \otimes [1]) = \dots \circ_2 (e_0^+ \otimes [1]) \circ_0 (e_{2k}^\epsilon \otimes \{0\}) \circ_1 (e_1^- \otimes [1]) \circ_3 \dots \circ_{2k-1} (e_{2k-1}^- \otimes [1])$$

$$\pi^+(e_{2k}^\epsilon \otimes [1]) = (e_{2k-1}^+ \otimes [1]) \circ_{2k-1} \dots \circ_3 (e_1^+ \otimes [1]) \circ_1 (e_{2k}^\epsilon \otimes \{1\}) \circ_0 (e_0^- \otimes [1]) \circ_2 \dots$$

$$\pi^-(e_{2k+1}^\epsilon \otimes [1]) = \dots \circ_3 (e_1^+ \otimes [1]) \circ_1 (e_{2k+1}^\epsilon \otimes \{1\}) \circ_0 (e_0^- \otimes [1]) \circ_2 \dots \circ_{2k} (e_{2k}^- \otimes [1])$$

$$\pi^+(e_{2k+1}^\epsilon \otimes [1]) = (e_{2k}^+ \otimes [1]) \circ_{2k} \dots \circ_2 (e_0^+ \otimes [1]) \circ_0 (e_{2k+1}^\epsilon \otimes \{0\}) \circ_1 (e_1^- \otimes [1]) \circ_3 \dots$$

We did not put parenthesis in the expression above, to keep them shorter, the default convention is to do the composition $$\circ_i$$ in order of increasing values of $$i$$.

**Example 1.2.4.7.** The $$(0, \omega)$$-category $$\mathbf{D}_1 \otimes [1]$$ is the polygraph:

![img-27.jpeg](img-27.jpeg)

The $$(0, \omega)$$-category $$\mathbf{D}_2 \otimes [1]$$ is the polygraph:

![img-28.jpeg](img-28.jpeg)

**Construction 1.2.4.8.** We define the *Gray cone*, the *Gray o-cone* and the *Gray op-cone*:

$$\begin{array}{c c c c c c c c} (0, \omega)\text{-cat} & \to & (0, \omega)\text{-cat.} & (0, \omega)\text{-cat} & \to & (0, \omega)\text{-cat.} & (0, \omega)\text{-cat} & \to & (0, \omega)\text{-cat.} \\ C & \mapsto & C \star 1 & C & \mapsto & 1 \stackrel{co}{\star} C & C & \mapsto & 1 \star C \end{array}$$

where $$C \star 1$$, $$1 \stackrel{co}{\star} C$$ and $$1 \star C$$ are defined as the following pushouts:

![img-29.jpeg](img-29.jpeg)

**Remark 1.2.4.9.** We could also define the *Gray co-cone* $$C \stackrel{co}{\star} 1$$, but we have omitted it as it will not appear in this text.

**Proposition 1.2.4.10.** *There are equivalences*

$$(C \star 1)^\circ \cong 1 \stackrel{co}{\star} C^\circ \quad (1 \star C)^{op} \cong C^{op} \star 1 \quad (1 \stackrel{co}{\star} C)^{co} \cong 1 \star C^{co}$$

*natural in $$C : (0, \omega)$$-cat.*

*Proof.* This directly follows from the definition of these operations and from proposition 1.2.4.3. $$\square$$

48

1.2. GRAY OPERATIONS

**Example 1.2.4.11.** The $(0, \omega)$-categories $\mathbf{D}_1 \star 1$ and $1 \stackrel{\text{co}}{\star} \mathbf{D}_1$ correspond respectively to the polygraphs:

![img-30.jpeg](img-30.jpeg)

The $(0, \omega)$-categories $\mathbf{D}_2 \star 1$ and $1 \stackrel{\text{co}}{\star} \mathbf{D}_2$ correspond respectively to the polygraphs:

![img-31.jpeg](img-31.jpeg)

**Proposition 1.2.4.12.** *Let $C$ be an $(0, \omega)$-category with an unitary and loop free basis. The canonical comparison*

$$(\lambda C) \star 1 \rightarrow \lambda(C \star 1)$$

*is an equivalence.*

*Let $K$ be an augmented directed complex with a loop free and unitary basis. The canonical comparisons*

$$(\nu K) \star 1 \rightarrow \nu(K \star 1)$$

*is an equivalence.*

*Proof.* The first assertion directly follows from the fact $\lambda$ commutes with colimits. For the second one, we can easily check that all the morphisms appearing in the squares (1.2.3.6) are quasi-rigid. The results then follow from an application of theorem 1.2.1.26. $\square$

The following theorems express the link between the Gray operations and the suspension. They will play a fundamental role in the rest of this work.

**Theorem 1.2.4.13.** *Let $C$ be an $(0, \omega)$-category. There is a natural identification between $[C, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [C, 1] \longleftarrow [C \otimes \{0\}, 1] \longrightarrow [C \otimes [1], 1] \longleftarrow [C \otimes \{1\}, 1] \longrightarrow [C, 1] \vee [1]$$

*Proof.* As all these functors preserve colimits, it is sufficient to construct the comparison when $C$ is a globular sum, and to show that it is an equivalence when $C$ is a globe. As globular sums have atomic and loop free bases, the comparison is induced by proposition 1.2.3.16. Using the explicit description of the $(0, \omega)$-category $\mathbf{D}_n \otimes [1]$ given in definition 1.2.4.6, it is straightforward to see that it induces an equivalence on globes. $\square$

**Theorem 1.2.4.14.** *There is a natural identification between $1 \stackrel{\text{co}}{\star} [C, 1]$ and the colimit of the following diagram*

$$[1] \vee [C, 1] \longleftarrow [C, 1] \longrightarrow [C \star 1, 1]$$

*There is a natural identification between $[C, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\text{co}}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1]$$

*There is a natural identification between $1 \star [C, 1]$ and the colimit of the following diagram*

$$[1 \star C, 1] \longleftarrow [C, 1] \longrightarrow [1] \vee [C, 1]$$

49

CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Proof. This directly follows from the definition of these operations, from theorem 1.2.4.13 and from proposition 1.2.4.10. □

We are now willing to show the following theorem:

Theorem 1.2.4.15. Let F be an endofunctor of (0,ω)-cat such that the induced functor (0,ω)-cat → (0,ω)-cat_{F(0)/} is colimit preserving and ψ an invertible natural transformation between F(D_n) and G(D_n) where G is either the Gray cylinder, the Gray cone, the Gray o-cone, the Gray op-cone or an iterated suspension.

Then, the natural transformation ψ can be uniquely extended to an natural transformation between F and G. Moreover, this natural transformation is unique.

The previous theorem implies that the equations given in theorem 1.2.4.13 and 1.2.4.14 characterize respectively the Gray cylinder, the Gray cone, the Gray o-cone and the Gray op-cone.

Lemma 1.2.4.16. A sub category Θ' of Θ, stable by colimit is equal to Θ iff

(1) for any integer n and α ∈ {−,+1}, i_n^α : D_n → D_{n+1} belongs to Θ'.
(2) For any integer n, the unit I_n : D_{n+1} → D_n belongs to Θ'.
(3) For any pair of integers k < n, the composition ∇_{k,n} : D_n → D_n ∐_k D_n belongs to Θ'.

Proof. Suppose that Θ' fulfills these conditions. As globular morphisms are compositions of pushouts along morphisms of shape i_n^α, they belong to Θ'. As algebraic morphisms are compositions of colimits of morphism of shape ∇_{k,n} or I_n, they belong to Θ'. The result then follows from proposition 1.1.2.13 that states that every morphism factors as an algebraic morphism followed by a globular morphism. □

Lemma 1.2.4.17. Let n be an integer, and G be either the Gray cylinder, the Gray cone, the Gray o-cone, the Gray op-cone or an iterated suspension, and suppose given a square

![img-32.jpeg](img-32.jpeg)

Then, the morphism f is G(I_n).

Proof. As the proof for any possibilities of G are similar, we will show only the case G := _ ⊗ [1]. As for any integer n, D_n ⊗ [1] admits a loop free and atomic basis, we can then show the desired assertion after applying the functor λ. Remark first that the assumption implies that ∂f((e_{n+1} ⊗ {α}) = 0, and so f((e_{n+1} ⊗ {α}) = 0. We also have f(e_{n+1} ⊗ [1]) = 0 as λ(D_n ⊗ [1])_{n+2} = 0. This implies that f is equal to λ(G(I_n)). □

50

1.2. GRAY OPERATIONS

Lemma 1.2.4.18. Let $k < n$ be two integers, and $G$ be either the Gray cylinder, the Gray cone, the Gray o-cone or an iterated suspension, and suppose given a square

$$\begin{array}{c} G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \\ \searrow G(i_n^-) \xrightarrow{} G(\mathbf{D}_n) \xrightarrow{f} G(\mathbf{D}_n \coprod_k G(i_n^-) \xrightarrow{} G(\mathbf{D}_n \coprod_k \mathbf{D}_n) \\ \searrow G(i_n^+) \xrightarrow{} G(i_n^+) \coprod_k G(i_n^+) \\ G(\mathbf{D}_{n-1}) \xrightarrow{\nabla_{n-1,k}} G(\mathbf{D}_{n-1} \coprod_k \mathbf{D}_{n-1}) \end{array}$$

where we set $\nabla_{n,n} := id$. Then, the morphism $f$ is $G(\nabla_{n,k})$.

Proof. As the proof for any possibilities of $G$ are similar, we will show only the case $G := \_ \otimes [1]$. As for any integer $n$, $\mathbf{D}_n \otimes [1]$ admits a loop free and atomic basis, we can then show the desired assertion after applying the functor $\lambda$. Suppose first that $k < n - 1$. By assumption, we have

$$\begin{array}{rcl} \partial f(e_n \otimes \{\alpha\}) & = & \partial(e_n^0 \otimes \{\alpha\}) + e_n^1 \otimes \{\alpha\}) \\ \partial f(e_n \otimes [1]) & = & \partial(e_n^0 \otimes [1]) + \partial(e_n^1 \otimes [1]) \end{array}$$

This forces the equalities

$$\begin{array}{rcl} f(e_n \otimes \{\alpha\}) & = & e_n^0 \otimes \{\alpha\} + e_n^1 \otimes \{\alpha\} \\ f(e_n \otimes [1]) & = & e_n^0 \otimes [1] + e_n^1 \otimes [1] \end{array}$$

and $f$ is then equal to $\nabla_{n,k} \otimes [1]$. The case $k = n - 1$ is similar.

Proof of theorem 1.2.4.15. As every globular sum is a colimit of globes, we can extend $\psi$ to a (a priori non natural) transformation, $\psi : F_{|\Theta} \to G_{|\Theta}$. Let $\Theta'$ be the maximal sub category of $\Theta$ such that $\psi_{|\Theta'}$ is natural. The category $\Theta'$ is closed by colimit. The assumption implies that $\Theta'$ fulfills the first condition of lemma 1.2.4.16. The lemma 1.2.4.17 implies that it fulfills the second condition, and an easy induction on $(n - k)$ using lemma 1.2.4.18 implies that it fulfills the last condition. Applying the lemma 1.2.4.16, $\psi : F_{|\Theta} \to G_{|\Theta}$ is then pointwise an isomorphism, and can be extended by colimits to a invertible natural transformation between $F$ and $G$. The unicity of this extension is a consequence of lemma 1.2.4.19.

We conclude this section by giving some technical results that we will use later.

Lemma 1.2.4.19. The set of $(0, \omega)$-categories admitting no non-trivial automorphisms is stable

(1) by isomorphisms,
(2) by $[\_, 1] \vee [1]$ and $[1] \vee [\_, 1]$,
(3) by the Gray cylinder, the Gray cone, the Gray o-cone, the Gray op-cone and the iterated suspensions,

and contains globular sums.

Proof. Let $S$ be the smallest set of $(0, \omega)$-categories stable by isomorphism, $[\_, 1] \vee [1]$, $[1] \vee [\_, 1]$, the Gray cylinder, the Gray cone and by iterated suspensions. As the set of $(0, \omega)$-categories admitting no non-trivial automorphisms is stable by dualities and by proposition 1.2.4.10, we have to show that it includes $S$.

51

CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

Remarks now that $$S$$ is contained in the set of $$(0, \omega)$$-categories admitting an atomic and loop free basis also fulfills. Using theorem 1.2.1.23, it is then sufficient to show that any augmented directed complex in $$\lambda(S)$$ has no non-trivial automorphisms. This directly follows from propositions 1.2.3.4, 1.2.3.8, 1.2.3.12 and 1.2.3.14.

It remains to show that $$S$$ contains globular sums. We proceed by induction, and we suppose that $$S$$ contains any globular sum of dimension $$k$$. Let $$[\mathbf{a}, n]$$ be a globular sum of dimension $$k + 1$$, and let $$\phi : [\mathbf{a}, n] \to [\mathbf{a}, n]$$ be an isomorphism. In particular $$\phi$$ induces an automorphism on $$[n]$$, and we then have $$\phi_i = i$$ for any $$i \leq n$$. The automorphism $$\phi$$ then induces for all $$i < n$$ an automorphism $$\phi_i : [a_i, 1] \cong [a_i, 1]$$. However, the stability by suspension of $$S$$ and the induction hypothesis implies that for any $$i < n$$, $$[a_i, 1]$$ has no non trivial automorphisms and $$\phi_i$$ is then the identity. This implies that $$\phi$$ is also the identity which concludes the proof.

**Proposition 1.2.4.20.** *Let $$n$$ be an integer $$n$$. The $$(0, \omega)$$-categories $$\mathbf{D}_n$$ and $$\underbrace{1 * 1 * \dots * 1}_{n}$$ have no non-trivial automorphisms.*

*Proof.* This is a direct consequence of lemma 1.2.4.19 as these two $$(0, \omega)$$-categories belong to $$S$$.

### 1.2.5 Gray tensor product of simplicial sets

**Notation 1.2.5.1.** We denote by

$$\mathrm{Psh}(\Theta) \xrightarrow[\iota]{\mathbf{F}} (0, \omega)\text{-cat}$$

the adjunction between presheaves on $$\Theta$$ and $$(0, \omega)$$-categories.

**Construction 1.2.5.2.** We define the functor $$_\otimes_- : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Theta) \to \mathrm{Psh}(\Theta)$$, called once again the *Gray tensor product*, as the left Kan extension of the functor

$$\Theta \times \Theta \xrightarrow{\otimes} (0, \omega)\text{-cat} \xrightarrow{\iota} \mathrm{Psh}(\Theta)$$

where $$\otimes : \Theta \times \Theta \to (0, \omega)$$-cat is the Gray tensor product defined in theorem 1.2.4.1.

By construction, the functor $$\mathbf{F}$$ preserves the Gray tensor product, and the functor $$\iota$$ preserves the Gray tensor product of globular sums.

The aim of this section is to prove the following result:

**Theorem 1.2.5.3.** *The functor*

$$_\otimes_- : \mathrm{Psh}(\Delta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Theta_2)$$

sends $$\mathrm{W}_1 \times \mathrm{W}_1$$ onto $$\overline{\mathrm{W}_2}$$, where $$\mathrm{W}_0$$ and $$\mathrm{W}_1$$ are defined in 1.1.2.15, and $$(\_)$$ in 1.1.3.2.

Informally, this result implies that we can define a Gray tensor product for $$(\infty, 1)$$-categories. It is therefore a special case of the main theorem of Campion's paper [Cam23a].

In the second part of this section, we will show a similar result for the op-joint.

**Proposition 1.2.5.4.** *The $$\Theta$$-set $$[1] \otimes [1]$$ is the colimit, computed in $$\mathrm{Psh}(\Theta)$$, of the diagram*

$$[2] \xleftarrow{\nabla} [1] \xrightarrow{[d^1, 1]} [[1], 1] \xleftarrow{[d^0, 1]} [1] \xrightarrow{\nabla} [2]$$

52

1.2. GRAY OPERATIONS

Proof. We denote by $P$ the colimit of this diagram. Remark that $\mathbf{F}P$ is the $(0, \omega)$-category generated by the diagram

![img-33.jpeg](img-33.jpeg)

and we then have $\mathbf{F}P \cong [1] \otimes [1]$. To conclude the proof, we have to show that $P$ is a $(0, \omega)$-category, i.e. that it has the unique right lifting property against W.

Let $f : [\mathbf{a}, n] \to P$ (resp. $f : \mathrm{Sp}_{[\mathbf{a}, n]} \to p$) be a morphism. If there exists an integer $i < n$ such that $f(i) = 00$ and $f(i + 1) = 11$, then $f$ uniquely factors through $[[1], 1] \to P$. If there exists an integer $i$ such that $f(i) = 10$, then $f$ uniquely factors through the left inclusion $[2] \to P$. If there exists an integer $i$ such that $f(i) = 01$, then $f$ uniquely factors through the right inclusion $[2] \to P$. If none of these conditions is satisfied, then $f$ factors through 00 or 11.

As $[2]$ and $[[1], 1]$ are $(0, \omega)$-categories, they have the unique right lifting property against W, and so has $P$. $\square$

Lemma 1.2.5.5. Let $C, D, E$ be three $(0, \omega)$-categories with loop-free and atomic bases. Let $f : C \to D$ be a morphism such that $f$ sends every generator of $C$ to a cell which is not a unit. The following square is then cartesian:

![img-34.jpeg](img-34.jpeg)

Proof. We can show this result at the level of the corresponding augmented directed complex, where it is an easy computation. $\square$

Lemma 1.2.5.6. Let $(a)_{i \leq n}$ be a sequence of elements of $\Theta$. There exists a diagram $F : I \to \Theta^+$ such that the presheaf $a_0 \times \ldots \times a_n$ is the colimit of $F$.

Proof. Let $I$ be the full subcategory of $\Theta_{/a_0 \times \ldots \times a_n}$ whose objects are $n$-tuples of morphisms $(j_i : b \to a_i)_{i \leq n}$ such that there exists no morphism $b \to b'$ in $\Theta^-$ that factors all the $j_i$. Morphisms are the ones such that $b \to b'$ in $\Theta^+$.

Let $(j_i : b \to a_i)_{i \leq n}$ be any element of $\Theta_{/a_0 \times \ldots \times a_n}$. We will show that there exists a unique degenerate morphism $g : b \to b'$ that factors the morphisms $b \to a_i$ for all $i < n$, and such that the induced family of morphisms $\{b' \to a_i\}_{i < n}$ is an element of $I$. It will implies that $g$ is an initial object of the category $I_{(j_i)_{i \leq n}/}$, and then that $\alpha : I \to \Theta_{/a_0 \times \ldots \times a_n}$ is final, which will concludes the proof.

As any infinite sequence of degenerate morphisms is constant at some point, the existence is immediate. Suppose given two morphisms $b \to b'$, $b \to b''$ fulfilling the previous condition. By proposition 1.1.2.10, the category $\Theta$ is Reedy elegant and the proposition 3.8 of [BR13] then implies that there exists a globular sum $\tilde{b}$ and two degenerate morphisms $b' \to \tilde{b}$ and $b'' \to \tilde{b}$ such that the induced square

![img-35.jpeg](img-35.jpeg)

is cocartesian. The universal property of pushout implies that $b \to \tilde{b}$ also fulfills the previous condition. By definition of $b'$ and $b''$, this implies that they are equal to $\tilde{b}$, and this shows the uniqueness. $\square$

53

CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Lemma 1.2.5.7. Let C be a (0,ω)-category such that there exists a diagram F : I → Θ⁺ with ι(C) being the colimit of F. Let a be an element of Θ. The canonical morphism ι(C) ⊗ a → ι(C ⊗ a) is an isomorphism.

Proof. The lemma 1.2.5.5 implies that the natural transformation F(i) ⊗ b → F(i) is cartesian. As a consequence, for any i, the square

$$\begin{array}{c} F(i) \otimes a \longrightarrow (\operatorname{colim}_I F) \otimes a \cong \iota(C) \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ F(i) \longrightarrow \operatorname{colim}_I F \cong \iota(C) \end{array}$$

is cartesian.

Now, to show the desired result, we have to demonstrate that the Θ-set ι(C) ⊗ a already has a structure of (∞,ω)-category, i.e. that it is W-local. It is sufficient to show that for all f : X → Y in W, any square

$$\begin{array}{c} X \longrightarrow \iota(C) \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \\ Y \longrightarrow \iota(C) \end{array}$$

admits a unique lift. Indeed, as ι(C) is an (0,ω)-category, it is W-local, and this will imply that ι(C) ⊗ a also is. Suppose then given such a square. As every codomain of morphism of W is representable, there exists a (not necessarily unique) element i of I, such that the bottom morphism factors as Y → F(i) → ι(C). The previous square then factors as

$$\begin{array}{c} X \longrightarrow F(i) \otimes a \longrightarrow \iota(C) \otimes a \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \\ Y \longrightarrow F(i) \longrightarrow \iota(C) \end{array}$$

where the right square is a pullback. The middle vertical morphism is W-local because it's domain and codomain are, and this concludes the proof.

Lemma 1.2.5.8. Given (a)ᵢ≤ₙ and b elements of Θ, we have

$$\iota((a_0 \times \dots \times a_n \otimes b) \cong (a_0 \times \dots \times a_n) \otimes b$$

Proof. This is a direct consequence of lemmas 1.2.5.6 and 1.2.5.7

Lemma 1.2.5.9. Let A, B, C be three presheaves on Θ. We have a canonical morphism

$$A \otimes (B \otimes C) \to (A \times B) \otimes C$$

Proof. It is sufficient to demonstrate the result when A, B and D are representable. In this case the lemma 1.2.5.8 implies that (A × B) ⊗ C is in the image of ι. By adjunction, the desired comparaison morphism is induced by

$$\iota(A \otimes (B \otimes C)) \cong \iota(A) \otimes (\iota(B) \otimes \iota(C))) \cong (\iota(A) \otimes \iota(B)) \otimes \iota(X) \to (\iota(A) \times \iota(B)) \otimes \iota(C)$$

54

1.2. GRAY OPERATIONS

Lemma 1.2.5.10. Let A, B, C, D, and E be presheaves on Θ, and k, m, n be integers. There exists a natural morphism

$$(\_)_A : \operatorname{Hom}([B, m], C \otimes [D, n]) \to \operatorname{Hom}([A \otimes B, m], C \otimes [A \otimes D, n])$$

such that for any pair of morphisms $f : [B, m] \to C \otimes [n]$ and $g : [F, k] \to E \otimes [m]$,

$$\mathbf{F}(((E \otimes f) \circ g_B)_A) = \mathbf{F}((E \otimes f_A) \circ (g_B)_A)$$

Proof. It is sufficient to describe this morphism when $A, B, C, D$, and $E$ are representable. This allows us the use of Steiner theory to construct this application. Let $f : [B, m] \to C \otimes [D, n]$ be a morphism. We set $f_A : [A \otimes B, m] \to C \otimes [A \otimes D, n]$ as the unique morphism of $(0, \omega)$-categories such that for every $a \in B_A$, $b \in B_B$, and $m \in B_m$

$$\lambda f_A([a \otimes b, m]) := \sum_{i \le n} c_i \otimes [a \otimes d_i, n_i]$$

where $(c_i, d_i, n_i)$ is the unique sequence of elements of $B_C \times B_D \times B_{[n]}$ such that $\lambda f([b, m]) = \sum_{i \le n} c_i \otimes [d_i, n_i]$. The equality $\lambda f_A \partial = \partial \lambda f_A$ and the equality $\mathbf{F}(((E \otimes f) \circ g_B)_A) = \mathbf{F}((E \otimes f_A) \circ (g_B)_A)$ is a straightforward calculation using Steiner theory.

Lemma 1.2.5.11. Let A, B, C, D, E, and F be presheaves on Δ, and k, m, n, l be integers. There exists a natural morphism

$$\alpha : \operatorname{Hom}([A, k], B \otimes [m]) \times \operatorname{Hom}([C, m], D \otimes [n]) \to \operatorname{Hom}([C \times A, k], (B \times D) \otimes [n])$$

and such that for any $f : [A, k] \to B \otimes [m]$, $g : [C, m] \to D \otimes [n]$, and $h : [E, n] \to F \otimes [l]$,

$$\alpha(\alpha(f, g), h) = \alpha(f, \alpha(g, h)) \tag{1.2.5.12}$$

Proof. Let $f : [A, k] \to B \otimes [m]$ and $g : [C, m] \to D \otimes [n]$ be two morphisms. Using the application of lemma 1.2.5.10 and the canonical morphism of 1.2.5.9, we get a sequence of arrows

$$[C \otimes A, k] \xrightarrow{f_C} B \otimes [C, m] \xrightarrow{B \otimes g} B \otimes (D \otimes [n]) \longrightarrow (B \times D) \otimes [n]$$

whose composite is denoted $\alpha'(f, g)$. Remark now that $(B \times D) \otimes [n]$ is a Θ₂-set. Moreover, we have an isomorphism

$$\tau_2^i([C \otimes A, k]) \cong [\tau_1^i(C \otimes A), k] \cong [C \times A, k]$$

We then set

$$\alpha(f, g) := \tau_2^i(\alpha'(f, g)) := [C \times A, k] \to (B \times D) \otimes [n].$$

Now, suppose given two arrows $f : [A, k] \to B \otimes [m]$, $g : [C, m] \to D \otimes [n]$, and $h : [E, n] \to F \otimes [l]$. Unfolding the definition, we have that $\alpha(\alpha(f, g), h)$ and $\alpha(f, \alpha(g, h))$ are respectively the image by $\tau_2^i$ of the morphism

$$[E \otimes (C \otimes A), k] \xrightarrow{(B \otimes g_E) \circ (f_C)_E} B \otimes (D \otimes [E, n]) \xrightarrow{B \otimes (D \otimes h)} B \otimes (D \otimes (F \otimes [k])) \longrightarrow (B \times D \times F) \otimes [l]$$

and

$$[E \otimes (C \otimes A), k] \xrightarrow{(B \otimes g \circ (f_C)_E)} B \otimes (D \otimes [E, n]) \xrightarrow{B \otimes (D \otimes h)} B \otimes (D \otimes (F \otimes [k])) \longrightarrow (B \times D \times F) \otimes [l]$$

55

CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Remark moreover that if A, B, C, D, and E are representable, lemma 1.2.5.8 implies that α(α(f, g), h) and α(f, α(g, h)) are morphisms of (0, ω)-categories, and they are then equal to the image by τ₂ⁱ and F of the two previous morphism. The equality given in lemma 1.2.5.10 then implies

$$\alpha(\alpha(f, g), h) = \alpha(f, \alpha(g, h))$$

Lemma 1.2.5.13. Let n and m be two integers. The canonical morphism

$$\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]} \to [n] \otimes [m]$$

is in W̅₂.

Proof. Let Δᵍˡᵒᵇ be the subcategory of Δ whose morphisms are the globular ones. We consider the functor g : Δᵍˡᵒᵇ × Δᵍˡᵒᵇ → Psh(Θ₂) by the formula

$$g([n], [m]) := \tau_0([n] \otimes [m]) \cup_{x \in S_{n,m}} x$$

where Sₙ,ₘ is the set of 1-generators of τ₁([n] ⊗ [m]). We have a canonical transformation g(n, m) → τ₁([n] ⊗ [m]) which is pointwise in W̅₂ by repeated application of theorem 1.2.2.1. For any pair of integers n, m, the morphism

$$g([n], [m]) \cong \underset{\mathrm{Sp}_{[n]} \times \mathrm{Sp}_{[m]}}{\mathrm{colim}} g \to \tau_1(\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]})$$

then also belongs to W̅₂. By two out of three, so is the morphism

$$\tau_1(\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]}) \to \tau_1([n] \otimes [m])$$

Remark now that we have a cocartesian square

$$\begin{array}{c} \tau_1(\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]}) \longrightarrow \mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \tau_1([n] \otimes [m]) \longrightarrow \tau_1([n] \otimes [m]) \cup_{x \in T_{n,m}} x \end{array}$$

where Tₙ,ₘ is the set of 2-generators of [n] ⊗ [m]. The theorem 1.2.2.1 implies that

$$\tau_1([n] \otimes [m]) \cup_{x \in T_{n,m}} x \to [n] \otimes [m]$$

is in W̅₂, and by stability by composition and pushout, so is

$$\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]} \to [n] \otimes [m].$$

Proposition 1.2.5.14. Let K be a simplicial set. The canonical morphism

$$1 \coprod_{K \otimes \{0\}} K \otimes [1] \coprod_{K \otimes \{1\}} 1 \to [K, 1]$$

is in W̅₂.

56

1.2. GRAY OPERATIONS

Proof. As $K$ is a colimit of representables indexed by the Reedy cofibrant diagram $\Delta_{/K} \to \mathrm{Psh}(\Delta)$ (definition 1.1.3.1), and as $1 \coprod_{-\otimes\{0\}} - \otimes [1] \coprod_{-\otimes\{1\}} 1$ and $[\_, 1]$ preserve cofibrations, it is sufficient to demonstrate the result when $K := [n]$ for $n$ an integer. As $[\_, 1]$ and, by lemma 1.2.5.13, $\_ \otimes [1]$ send $\mathrm{Sp}_{[n]} \to [n]$ to $\overline{\mathrm{W}_2}$, it is sufficient to demonstrate the result when $[n] = [1]$. By proposition 1.2.5.4, the morphism

$$1 \coprod_{[1] \otimes\{0\}} [1] \otimes [1] \coprod_{[1] \otimes\{1\}} 1 \to [[1], 1]$$

fits in the cocartesian square

$$\begin{array}{ccc} [0] \coprod_{[1]} [2] & \coprod & [0] \coprod_{[1]} [2] \longrightarrow 1 \coprod_{[1] \otimes\{0\}} [1] \otimes [1] \coprod_{[1] \otimes\{1\}} 1 \\ & \downarrow & \downarrow \\ [1] & \coprod & [1] \xrightarrow{\quad} [[1], 1] \end{array}$$

As the canonical morphisms $[0] \coprod_{[1]} [2] \to [1]$ and $[2] \coprod_{[1]} \to [1]$ are in $\overline{\mathrm{W}_2}$, this concludes the proof. $\square$

Lemma 1.2.5.15. Let $n$ be an integer. The two morphisms

$$E^{eq} \otimes [n] \to [n] \quad \text{and} \quad [n] \otimes E^{eq} \to [n]$$

are in $\overline{\mathrm{W}_2}$.

Proof. As $\otimes$ sends spine inclusions to $\overline{\mathrm{W}_2}$, we can reduce to the case where $n = 1$. By stability by pushouts along monomorphisms, and using lemma 1.2.5.14, the composite

$$E^{eq} \otimes [1] \to 1 \coprod_{E^{eq} \otimes\{0\}} E^{eq} \otimes [1] \coprod_{E^{eq} \otimes\{1\}} 1 \to [E^{eq}, 1]$$

is in $\overline{\mathrm{W}_2}$. As $[E^{eq}, 1] \to [1]$ is in $\mathrm{W}_2$, this concludes the first assertion. We show the second one similarly. $\square$

proof of theorem 1.2.5.3. This is the content of lemmas 1.2.5.13 and 1.2.5.15. $\square$

We will also need the same analysis for the op-cone.

Construction 1.2.5.16. We define $1 \star \_ : \mathrm{Psh}(\Theta) \to \mathrm{Psh}(\Theta)$ as the left Kan extension of the functor

$$\Theta \xrightarrow{1 \star} (0, \omega)\text{-cat} \xrightarrow{\iota} \mathrm{Psh}(\Theta).$$

Proposition 1.2.5.17. The $\Theta$-set $1 \star [1]$ is the colimit, computed in $\mathrm{Psh}(\Theta)$, of the diagram

$$[[1], 1] \xleftarrow{[d^0, 1]} [1] \xrightarrow{d^1} [2]$$

Proof. We denote by $P$ the colimit of this diagram. Remark that $\mathbf{F}P$ is the $(0, \omega)$-category

$$\begin{array}{c} 1 \star \emptyset \\ \downarrow \\ \emptyset \star \{0\} \longrightarrow \emptyset \star \{1\} \end{array}$$

57

CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

and we then have $$\mathbf{F}P \cong 1 \star [1]$$. To conclude the proof, we have to show that $$P$$ is a $$(0, \omega)$$-category, i.e. that it has the unique right lifting property against W.

Let $$f : [\mathbf{a}, n] \to P$$ (resp. $$f : \mathrm{Sp}_{[\mathbf{a}, n]} \to P$$) be a morphism. If there exists an integer $$i < n$$ such that $$f(i) = 1 \star \emptyset$$ and $$f(i+1) = \emptyset \star \{1\}$$, then $$f$$ uniquely factors through $$[[1], 1] \to P$$. If there exists an integer $$i$$ such that $$f(i) = \emptyset \star \{0\}$$, then $$f$$ uniquely factors through $$[2] \to P$$. If none of these conditions is satisfied, then $$f$$ factors through $$1 \star \emptyset$$ or $$\emptyset \star \{1\}$$.

As $$[2]$$ and $$[[1], 1]$$ are $$(0, \omega)$$-categories, they have the unique right lifting property against W, and so have $$P$$.

**Lemma 1.2.5.18.** *The $$\Theta$$-set $$\iota(1 \star [1] \coprod_{\emptyset \star \{1\}} [1])$$ is the colimit, computed in $$\mathrm{Psh}(\Theta)$$, of the diagram*

$$[[1], 1] \vee [1] \xleftarrow{[d^0, 2]} [2] \xrightarrow{d^1} [3]$$

*Proof.* We denote by $$P$$ the colimit of this diagram. Remark that $$\mathbf{F}P$$ is the $$(0, \omega)$$-category

$$\begin{array}{c} 1 \star \emptyset \\ \downarrow \\ \emptyset \star \{0\} \longrightarrow \emptyset \star \{1\} \longrightarrow \emptyset \star \{2\} \end{array}$$

and we then have $$\mathbf{F}P \cong 1 \star [1] \coprod_{\emptyset \star \{1\}} [1]$$. To conclude the proof, we have to show that $$P$$ is a $$(0, \omega)$$-category, i.e. that it has the unique right lifting property against W. The proof of this assertion is an easy adaptation of the one of lemma 1.2.5.17.

**Proposition 1.2.5.19.** *The $$\Theta$$-set $$1 \star [2]$$ is the colimit, computed in $$\mathrm{Psh}(\Theta)$$, of the diagram*

$$[[2], 1] \xleftarrow{[d^0, 1]} [[1], 1] \xrightarrow{[[1], d^1]} [[1], 1] \vee [1] \xleftarrow{[d^0, 2]} [2] \xrightarrow{d^1} [3]$$

*Proof.* We recall that lemma 1.2.5.18 states that the colimit of the subdiagram

$$[[1], 1] \vee [1] \xleftarrow{[d^0, 2]} [2] \xrightarrow{d^1} [3]$$

is equivalent to $$\iota(1 \star [1] \coprod_{\emptyset \star \{1\}} [1])$$.

We denote by $$P$$ the colimit of this diagram given in the statement of the proposition. Remark that $$\mathbf{F}P$$ is the $$(0, \omega)$$-category

$$\begin{array}{c} 1 \star \emptyset \\ \downarrow \\ \emptyset \star \{0\} \longrightarrow \emptyset \star \{1\} \longrightarrow \emptyset \star \{2\} \end{array}$$

and we then have $$\mathbf{F}P \cong 1 \star [2]$$. To conclude the proof, we have to show that $$P$$ is a $$(0, \omega)$$-category, i.e. that it has the unique right lifting property against W.

Let $$f : [\mathbf{a}, n] \to P$$ (resp. $$f : \mathrm{Sp}_{[\mathbf{a}, n]} \to P$$) be a morphism. If there exists an integer $$i < n$$ such that $$f(i) = 1 \star \emptyset$$ and $$f(i+1) = \emptyset \star \{2\}$$, then $$f$$ uniquely factors through $$[[2], 1] \to P$$. If there exists an integer $$i$$ such that $$f(i) = \emptyset \star \{0\}$$, then $$f$$ uniquely factors through $$\iota(1 \star [1] \coprod_{\emptyset \star \{1\}} [1])$$. If none of these conditions is satisfied, then $$f$$ factors through $$1 \star \emptyset$$ or $$\emptyset \star \{2\}$$.

As $$[2]$$ and $$\iota(1 \star [1] \coprod_{\emptyset \star \{1\}} [1])$$ are $$(0, \omega)$$-categories, they have the unique right lifting property against W, and so have $$P$$.

58

1.2. GRAY OPERATIONS

**Lemma 1.2.5.20.** Let $A$, $B$ be presheaves on $\Delta$, and $k, m, n, l$ be integers. There exists a natural morphism

$$\beta : \operatorname{Hom}([A, k], 1 \star [m]) \times \operatorname{Hom}([B, m], 1 \star [n]) \to \operatorname{Hom}([B \times A, k], 1 \star [n])$$

such that for any $f : [A, k] \to 1 \star [m]$, $g : [B, m] \to 1 \star [n]$ and $h : [B, n] \to 1 \star [l]$,

$$\beta(\beta(f, g), h) = \beta(f, \beta(g, h)) \tag{1.2.5.21}$$

*Proof.* Similar to the proof of lemma 1.2.5.11.

**Theorem 1.2.5.22.** *The functor*

$$1 \star \_ : \operatorname{Psh}(\Delta) \to \operatorname{Psh}(\Theta_2)$$

sends $\mathrm{W}_1$ onto $\overline{\mathrm{W}_2}$.

*Proof.* Similar to the proof of theorem 1.2.5.3.

**Proposition 1.2.5.23.** *Let $K$ be a simplicial set. The canonical morphism*

$$1 \coprod_{\{0\} \otimes K} [1] \otimes K \to 1 \star K$$

is in $\overline{\mathrm{W}_2}$.

*Proof.* As $K$ is a colimit of representables indexed by the Reedy cofibrant diagram $\Delta_{/K} \to \operatorname{Psh}(\Delta)$ (definition 1.1.3.1), and as $1 \coprod_{\{0\} \otimes \_} [1] \otimes \_$ and $1 \star \_$ preserve cofibrations, it is sufficient to demonstrate the result when $K := [n]$ for $n$ an integer. By theorems 1.2.5.3 and 1.2.5.22, the functors $1 \coprod_{\{0\} \otimes \_} [1] \otimes \_$ and $1 \star \_$ send $\operatorname{Sp}_{[n]} \to [n]$ to $\overline{\mathrm{W}_2}$. It is then sufficient to demonstrate the result when $[n] = [1]$. By propositions 1.2.5.4 and 1.2.5.17, the morphism

$$1 \coprod_{\{0\} \otimes [1]} [1] \otimes [1] \to 1 \star [1]$$

fits in the cocartesian square

$$\begin{array}{ccc} [0] \coprod_{[1]} [2] & \longrightarrow & 1 \coprod_{\{0\} \otimes [1]} [1] \otimes [1] \\ \downarrow & & \downarrow \\ [1] & \longrightarrow & 1 \star [1] \end{array}$$

As the canonical morphism $[0] \coprod_{[1]} [2] \to [1]$ is in $\overline{\mathrm{W}_2}$, this concludes the proof.

59

CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

60

## Chapter 2

# Study of complicial sets

### Contents

|  **2.1 Preliminaries** | **62**  |
| --- | --- |
|  2.1.1 Generalities on model categories | 62  |
|  2.1.2 Marked and stratified presheaves | 65  |
|  **2.2 The complicial model** | **68**  |
|  2.2.1 Model structure on marked simplicial sets | 68  |
|  2.2.2 Gray operations on marked simplicial sets | 72  |
|  2.2.3 Street nerve | 77  |
|  **2.3 Suspension and Gray operations** | **79**  |
|  2.3.1 Formula for the Gray cylinder | 79  |
|  2.3.2 Formulas for the Gray cone and the Gray o-cone | 82  |
|  **2.4 Globular equivalences** | **84**  |
|  2.4.1 Homotopy categories | 84  |
|  2.4.2 A criterion to be a weak equivalence | 87  |
|  2.4.3 A criterion to be a weakly invertible transformation | 91  |
|  2.4.4 Weak characterization of the identity | 92  |

This chapter is dedicated to the study of *Verity complicial sets*, defined and extensively studied by Verity ([Ver08c])

One of the benefits of complicial sets is that they admit a simple definition of the Gray tensor product. Being strongly linked to $(0, \omega)$-categories by the Street nerve, they are also a privileged framework for stating and proving strictification results, as done in [OR20a], [GOR21], [OR22] and [Mae23]. However, they do not interact *a priori* well with the globular language. The goal of this chapter is to show that, with some computation, it is possible to have a globular point of view on theses objects.

The first section is a recollection of usual results and definitions about complicial sets. In the second section, we aim to prove an analogue of the formula given in 1.2.4.13 to the complicial setting. We also have a suspension in this category, which is denoted by $X \mapsto \Sigma X$. Objects $[1] \vee \Sigma X$ and $\Sigma X \vee [1]$ are defined in 2.2.2.18, but for now, we can suppose that they are fibrant replacements of respectively

61

CHAPTER 2. STUDY OF COMPLICIAL SETS

[1] $\coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \, \forall \, \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \, \forall \, [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:*

$$\Sigma X \, \forall \, [1] \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \, \forall \, \Sigma X.$$

We also provide similar formulas for the *Gray cone* and *Gray o-cone*:

**Theorem 2.3.2.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \star [0]$ and the colimit of the following diagram:*

$$\Sigma X \, \forall \, [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{\infty}{\star} X).$$

*There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{\infty}{\star} \Sigma X$ and the colimit of the following diagram:*

$$\Sigma(X \star [0]) \leftarrow \Sigma X \to [1] \, \forall \, \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

**Theorem 2.4.4.13.** *Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.*

Proposition 15.10 of [BSP21] provides a similar result for models of $(\infty, n)$-categories.

## 2.1 Preliminaries

### 2.1.1 Generalities on model categories

For this chapter, we fix a model category $C$ whose cofibrations are monomorphisms.

We give first some results on homotopy colimits. These results will be used freely throughout these text.

62

2.1. PRELIMINARIES

Proposition 2.1.1.1. Suppose given a square

such that the two horizontal morphisms are weak equivalences. Then this square is homotopy cocartesian.

Proof. This is [Cis19, proposition 2.3.26].

Proposition 2.1.1.2. Suppose given a cocartesian square

where the left vertical morphism is a cofibration. Then this square is homotopy cocartesian.

Proof. This is [Cis19, corollary 2.3.28].

Proposition 2.1.1.3. Weak equivalences are stable by pushout along cofibrations.

Proof. This is [Hir03, proposition 13.1.2].

Proposition 2.1.1.4. Let $F : \alpha \to C$ be a diagram indexed by an ordinal. The transfinite composition $\operatorname{colim}_{\alpha} F$ is the homotopy colimit of the diagram $F$.

Proof. This is [Cis19, proposition 2.3.13].

Proposition 2.1.1.5. Suppose given a diagram

![img-36.jpeg](img-36.jpeg)

where all morphisms labelled by $\hookrightarrow$ are cofibrations. The colimit of this diagram is also the homotopy colimit of this diagram.

Proof. Let $I_n$ be the category indexing the previous diagram. We denote by $i_0, j_0, \ldots, i_{n-1}, j_{n-1}, i_n$ it's objects. The projective model structure on $\operatorname{Fun}(I_n, C)$ is given by functor $G$ such that for any $k < n$, $F(j_k) \to F(i_k)$, $F(j_k) \to F(i_{k+1})$ are monomorphisms, and such that for any $0 < k < n$, $F(j_k) \coprod F(j_{k+1}) \to F(i_k)$ is a monomorphism. Remark that such presheaves verify the condition given in the statement of the proposition.

We will show on induction on $n$ that a natural transformation $\psi$ between two diagrams $F, G : I_n \to C$ that fulfills the desired condition induces a weak equivalence between their colimits. As we can always chose $F$ to be the cofibrant replacement of $G$ in the projective model structure on $\operatorname{Fun}(I_n, C)$, it will imply the desired result.

The case $n = 1$ is proposition 2.1.1.2. Suppose now the result is true at the stage $(n - 1)$ and let $\psi$ be a weakly invertible natural transformation between two diagram $F, G : I_n \to C$ that fulfills the desired

63

CHAPTER 2. STUDY OF COMPLICIAL SETS

condition. We denote by $\iota : I_{n-1} \to I_n$ the canonical inclusion that sends $i_k(\text{resp. } j_k)$ on $i_k(\text{resp. } j_k)$ for $k < n$ (resp. $k < n-1$). We then have a diagram

$$\begin{array}{c} \operatorname{colim}_{I_{n-1}} F \circ \iota \longleftarrow F(j_{n-1}) \longmapsto F(i_n) \\ \sim \Big\downarrow \qquad \qquad \qquad \sim \Big\downarrow \qquad \qquad \sim \Big\downarrow \\ \operatorname{colim}_{I_{n-1}} G \circ \iota \longleftarrow G(j_{n-1}) \longmapsto G(i_n) \end{array}$$

where all arrows labeled by $\sim$ are weak equivalences. Remark furthermore that the limit of the two lines are respectively $\operatorname{colim}_{I_n} F$ and $\operatorname{colim}_{I_n} G$. A last application of proposition 2.1.1.2 concludes the proof. $\square$

**Definition 2.1.1.6.** A model structure is *nice* if it is simplicial, combinatorial, cartesian and its cofibrations are monomorphisms.

The definition of elegant Reedy category and of Reedy cofibrant diagram are given in definitions 1.1.2.8 and 1.1.3.1. As all the presheaves categories that we will encounter through this text are presheaves on elegant Reedy categories, we will use freely the following theorem:

**Theorem 2.1.1.7** (Hirschhorn). *We suppose that $C$ is a nice model category. Let $A$ be a elegant Reedy category, and $F : A \to C$ a Reedy cofibrant diagram. The object $\operatorname{colim}_A F$ is the homotopy colimit of $F$. In particular, if $C$ is $\operatorname{Psh}(A)$, every object $X$ is the homotopy colimit of the diagram $A_{/X} \to A \to \operatorname{Psh}(A)$.*

*Proof.* Using the characterization of elegant Reedy category given by proposition 3.8 of [BR13], and [Hir03, proposition 15.10.2], it's easy to see that they have fibrant constant in the sens of [Hir03, definition 15.10.1]. We can then apply the theorem 19.9.1 of [Hir03]. $\square$

**Proposition 2.1.1.8.** *Weak equivalences of a nice model category form a precomplete class in the sense of definition 1.1.3.2.*

*Proof.* The first two conditions of definition 1.1.3.2 are obviously fulfilled by the class of weak equivalences. The last one follows from theorem 2.1.1.7. $\square$

**Notation 2.1.1.9.** Let $\_ \square \_ : C \times D \to E$ be a bifunctor. If $f : a \to b$ and $g : x \to y$ are respectively morphisms of $C$ and $D$, we will note by $f \stackrel{\circ}{=} g$ the induced morphism $a \square y \coprod_{a \square x} b \square x \to b \square y$.

**Proposition 2.1.1.10.** *Let $A$ be a nice model structure and $S$ a set of cofibrations. There exists a model structure $A_S$ on the same category, and a left Quillen adjoint $L : A \to A_S$, such that an object is fibrant in $A_S$ if and only if it is fibrant in $A$ and has the right lifting property against all morphisms of shape $i \stackrel{\circ}{\times} f$ where $i$ is a cofibration and $f$ in $S$. Moreover, a left Quillen functor $F : A \to C$ lifts to $A_S$ if and only if for any cofibration $i$ and morphism $f \in S$, $F(i \stackrel{\circ}{\times} f)$ is a weak equivalence.*

*Proof.* This is [[Lur09, proposition A.3.7.3]].

**Corollary 2.1.1.11.** *Let $A$, $C$ be two nice model categories, $F : A \to C$ a left Quillen functor, $S$ a set of cofibrations and $T$ a set of morphisms such that for any cofibrations $i$ and morphisms $f \in S$, the morphism $i \stackrel{\circ}{\times} f$ is included in the smallest saturated class stable by two out of three, containing weak equivalences and $T$. Then a left Quillen functor $F : A \to C$ lifts to $A$ if and only if it sends morphisms of $T$ to weak equivalences.*

64

2.1. PRELIMINARIES

*Proof.* Let $U$ be the class of morphisms in $A$ that are sent to weak equivalences by $F$. This class is obviously stable by two out of three, retracts and contains weak equivalences. As the model structure on $C$ is combinatorial and left proper, it is saturated. The class $U$ then includes all morphisms of shape $i \times f$ for $i$ a cofibration and $f \in S$, which implies that $F$ can be lifted to $A_S$. $\square$

**Definition 2.1.1.12.** Let $i : A \to B$ and $i' : A' \to B'$ be two cofibrations. A *zigzag of acyclic cofibration* between $i$ and $i'$, denoted $i \rightsquigarrow i'$ is a zigzag in the category of arrows such that all the horizontal maps are acyclic cofibrations, and all the vertical maps are cofibrations.

**Lemma 2.1.1.13.** *Let $i$ and $j$ be two cofibrations, and $f : X \to Y$ a fibration between fibrant objects. Suppose that we have a morphism in the category of arrows $i \to j$ which is pointwise an acyclic cofibration. Then, if $j$ has the left lifting property against $f$, so has $i$.*

*Proof.* We consider a diagram of the following shape:

![img-37.jpeg](img-37.jpeg)

We construct, one after the other, the lifting $l_0$, $l_1$ and $l_2$. $\square$

**Lemma 2.1.1.14.** *Let $i$ and $j$ be two cofibrations, and $f : X \to Y$ a fibration between fibrant objects. Suppose that we have a morphism in the category of arrows $i \to j$ which is pointwise an acyclic cofibration. Then, if $i$ has the right lifting property against $f$, so has $j$.*

*Proof.* We consider a diagram of the following shape:

![img-38.jpeg](img-38.jpeg)

We construct, one after the other, the lifting $l_0$, $l_1$. $\square$

**Proposition 2.1.1.15.** *Let $f$ be a fibration between fibrant objects and $i$ and $j$ two cofibrations such that there exists a zigzag of acyclic cofibrations $i \rightsquigarrow j$. Then $f$ has the right lifting property against $i$ if and only if it has the right lifting property against $j$.*

*Proof.* This is a direct consequence of the last two lemmas. $\square$

## 2.1.2 Marked and stratified presheaves

**Definition 2.1.2.1.** Let $B$ be an elegant Reedy category and $M$ a subset of the set of objects of $B$. A $M$-*stratified presheaf on $B$*, or just a *stratified presheaf on $B$* when the subset $M$ will be non-ambiguous, is a pair $(X, tX)$ where $X$ is a presheaf on $B$ and $tX := \coprod_{a \in M} tX_a$ is the disjoint union of sets, such that

65

CHAPTER 2. STUDY OF COMPLICIAL SETS

for any $a \in M$, $tX_a$ is a subset of $X_a$ including degeneracies, i.e the image of morphisms $X_p : X_b \to X_a$ for $p : b \to a$ in $B_-$.

A stratified morphism $f : (X, tX) \to (Y, tY)$ is the data of a morphism on the underlying presheaf such that $f(tX_n) \subset tY_n$. The category of stratified presheaves is denoted by $\mathrm{tPsh}_M(B)$.

Definition 2.1.2.2. A morphism between two stratified presheaves is entire if it is the identity on the underlying presheaves.

Construction 2.1.2.3. We have an adjunction

$$(\_)^\flat : \mathrm{Psh}(B) \xleftrightarrow{\perp} \mathrm{tPsh}_M(B) : (\_)^\sharp$$

where the left adjoint is a fully faithful inclusion that sends a presheaf $X$ onto $(X, S)$ where $S$ is the smaller stratification on $X$, and where the right adjoint is the obvious forgetful functor. We will identify presheaves on $B$ with their image by the functor $(\_)^\flat$.

Construction 2.1.2.4. If $b$ is an object of $M$, we denote by $b_t$ the stratified presheaf $(b, S)$, where $S$ is the smaller stratification that includes $id : b \to b$.

We then define $t_M B$ as the full subcategory of $\mathrm{tPsh}_M(B)$ spanned by the objects of shape $a$ or $b_t$ with $a \in B$ and $b \in M$. We then have equalities:

$$\mathrm{Hom}_{t_M B}(a, b) := \mathrm{Hom}_B(a, b),$$

$$\mathrm{Hom}_{t_M B}(a, b_t) := \mathrm{Hom}_B(a, b),$$

$$\mathrm{Hom}_{t_M B}(a_t, b) := \mathrm{Hom}_B(a, b) \cap B_- \setminus \{id_a\},$$

$$\mathrm{Hom}_{t_M B}(a_t, b_t) := \mathrm{Hom}_B(a, b) \cap B_-.$$

The canonical functor $B \to t_M B$ is then fully faithful and we will identify object of $B$ with their image through this functor.

The category of $M$-stratified presheaves is then equivalent to the fully faithful subcategory of presheaves $X$ on $t_M B$ such that for any $b \in M$, $X(b_t) \to X(b)$ is a monomorphism. In particular, we have an adjunction

$$\pi : \mathrm{Psh}(t_M B) \xleftrightarrow{\perp} \mathrm{tPsh}_M(B) : \iota \tag{2.1.2.5}$$

Proposition 2.1.2.6. The category $t_M B$ admits a structure of elegant Reedy category, that makes the inclusion $B \to t_M B$ a morphism of Reedy category. There is no non trivial negative morphism whose codomain is of shape $b_t$ for $b \in M$. There is no non trivial positive morphism whose domain is of shape $b_t$ for $b \in M$.

Proof. We define the degree degree function $ob(t_M B) \to \mathbb{N}$ by the assignment

$$d'(b) := 2d(b) \quad d'(b_t) := 2d(b) + 1$$

The category $(t_M B)_+$ is the smallest that includes $B_+$ and morphisms of shape $a \to a_t$. The category $(t_M B)_-$ is the smallest that includes $B_-$ and morphisms of shape $b_t \to a$.

To prove the axioms of Reedy category, we can replicate the strategy used in proposition C.2 of [OR20b] with obvious modification to this more general framework.

We still have to show that $tB$ is elegant. Let $X$ be a presheaf on $t_M B$, $a$ an element of $t_M B$, $f : a \to a'$ and $g : a \to a'$ two negative morphisms, an element $x$ of $X(a)$, two non degenerate elements $y \in X(a')$ and $z \in X(a'')$ such that $f^*y = x$, $g^*z = x$.

66

2.1. PRELIMINARIES

Suppose first that $a$ is in $B$. In this case, $f$ and $g$ are also in $B$, and as this Reedy category is elegant by assumption, this implies $f = g$ and $y = z$. Suppose now that $a$ is of shape $b_t$ for $b \in B$. We denote by $\alpha$ the canonical morphism $\alpha : b \to b_t$. By definition of negative morphism, the codomain of $f$ and $g$ are in $B$. The morphisms $\alpha f$ and $\alpha g$ then are in $B$. Moreover, these two morphisms are negative, and we have $(\alpha f)^* y = \alpha^* x$, $(\alpha g)^* z = \alpha^* x$. As $B$ is elegant, $\alpha f = \alpha g$ and $y = z$. Eventually, remark that the first equality implies that $f$ is equal to $g$. $\square$

**Remark 2.1.2.7.** A cellular model for $t_M B$ is given by $C \cup \{b \to b_t, b \in M\}$ where $C$ is a cellular model for $B$.

**Proposition 2.1.2.8.** *Suppose given a combinatorial model structure on $\mathrm{Psh}(t_M B)$ whose cofibrations are monomorphisms. Then there exists a combinatorial model structure on $\mathrm{tPsh}_M(B)$ making the adjunction 2.1.2.5 a Quillen equivalence.*

*A morphism of $\mathrm{tPsh}_M(B)$ is a cofibration if and only if it is a monomorphism. A morphism is a fibration (resp. a weak equivalence) if and only if its image by $\iota$ is.*

*Proof.* We are willing to apply [Hir03, theorem 11.3.2]. As two adjoints of (2.1.2.5) preserve smallness, the first condition is obviously fulfilled. Using the fact that $\iota$ is fully faithful, the second condition of theorem *op cit* is equivalent to asking that for any acyclic cofibration $i$ of $\mathrm{Psh}(t_M B)$, the morphism $\iota \pi i$ is a weak equivalence.

However, remark that the unit $X \to \iota \pi X$ is a trivial fibration. Indeed, a cellular model is given $C \cup \{b \to b_t, b \in M\}$, where $C$ is a cellular model for $B$, and the unit obviously has the right lifting property against it. The result then directly follows from the stability of weak equivalences by two out of three.

This provides the model structure. As the unit is pointwise a trivial fibration and the counit is the identity, the adjunction (2.1.2.5) induces a Quillen equivalence. $\square$

We now fix a Reedy category $B$, a subset $M$ of objects of $B$, and we suppose given a nice model structure on $\mathrm{tPsh}_M(B)$ (as defined in definition 2.1.1.6).

**Definition 2.1.2.9.** A $M$-marked presheaf on $B$ is a stratified presheaf having the unique right lifting property against all entire acyclic cofibrations. In particular, any fibrant objects is marked.

We denote by $\mathrm{mPsh}_M(B)$ the full subcategory of marked presheaves on $B$. We then have an adjunction:

$$
(\_)_{\mathrm{mk}} : \mathrm{tPsh}_M(B) \xrightarrow{\perp} \mathrm{mPsh}_M(B) : \iota \tag{2.1.2.10}
$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified presheaf $(X, tX)$ to the marked presheaf $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$ a marked presheaf, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of presheaves, these two adjoints are the identity.

**Proposition 2.1.2.11.** *Let $X$ be a $M$-stratified presheaf on $B$. The canonical morphism $X \to \iota(X_{\mathrm{mk}})$ is an entire acyclic cofibration.*

67

CHAPTER 2. STUDY OF COMPLICIAL SETS

*Proof.* Let $\kappa$ be a regular cardinal such that $X$ is $\kappa$-small. Remark first the domain of a entire monomorphism is $\kappa$-small if and only if its codomain is.

Let $I$ be the set of entire acyclic cofibrations with $\kappa$-small codomains and domains. This set generates via the small object argument a weak factorization system, and we denote by $X \rightarrow X' \rightarrow 1$ the factorization of $X \rightarrow 1$. We are willing to show that $X'$ is $M$-marked. As $X \rightarrow X'$ is an entire acyclic cofibration by construction, this will directly imply that $X'$ is equal to $\iota(X_{\mathrm{mk}})$ and so demonstrate the desired result.

Suppose then given a diagram

![img-39.jpeg](img-39.jpeg)

with $i$ an entire acyclic cofibration. We have to show that it admits a lift. Remark that this square factors as:

![img-40.jpeg](img-40.jpeg)

The morphism $i'$ is an entire acyclic cofibration with $\kappa$-small codomain and domain and then belongs to $i$. The right square of the previous diagram then admits a lift. This induces a lift in the original square, and this concludes the proof. $\square$

**Proposition 2.1.2.12.** *Suppose given a nice model structure on $\mathrm{tPsh}_M(B)$. This induces a nice model structure on $\mathrm{mPsh}_M(B)$, making the adjunction (2.1.2.10) a Quillen equivalence. A morphism between two marked presheaves is a cofibration (resp. a fibration) (resp. a weak equivalence) if it is a cofibration (resp. a fibration) (resp. a weak equivalence) when seen as a morphism of $\mathrm{tPsh}_M(B)$.*

*Proof.* Let $f : X \rightarrow Y$ be a fibration between stratified presheaves. If $Y$ is marked, so is $X$. The two weak factorization systems on $\mathrm{mPsh}_M(B)$ are then induced by the one of $\mathrm{tPsh}_M(B)$. We leave it to the reader to check that this model structure is nice.

The unit is pointwise a weak equivalence according to proposition 2.1.2.11 and the counit is the identity. The adjunction (2.1.2.10) is then a Quillen equivalence. $\square$

## 2.2 The complicial model

### 2.2.1 Model structure on marked simplicial sets

The theory of complicial sets has been extensively developed by Verity ([Ver08c]). However, Verity uses a definition slightly different from complicial sets, as he does not require the marking to be *saturated*.

In [OR20b], Ozornova and Rovelli adapt the arguments of Verity to the saturated case. This section is a recollection of the principal results of this article.

**Definition 2.2.1.1.** A *stratified simplicial set* is a pair $(X, tX)$ where $X$ is a simplicial set and $tX := \cup_{n>0} tX_n$ a graded set such that for any $n \geq 1$, $tX_n$ is a subset of $X_n$ that includes all degenerate simplices. A simplex in $tX$ is called *thin*.

A *stratified morphism* $f : (X, tX) \rightarrow (Y, tY)$ is the data of a morphism on the underlying simplicial set such that $f(tX_n) \subset tY_n$. The category of stratified simplicial sets is denoted by $\mathrm{tPsh}(\Delta)$.

68

2.2. THE COMPLICIAL MODEL

**Remark 2.2.1.2.** Given a functor $i : I \mapsto (F(i), tF(i))$ with value in stratified simplicial sets, its colimit is given by $(\operatorname{colim} F(i), M)$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \operatorname{colim} F(i)$ for any $i : I$.

**Definition 2.2.1.3 (Verity).** We can extend the join to stratified simplicial sets as follows: If $(X, tX)$ and $(Y, tY)$ are two stratified simplicial sets, we define $tX \star tY$ as the set of simplices of $X \star Y$ of shape $x \star y$ where either $x$ or $y$ are thin. We then define

$$(X, tX) \star (Y, tY) := (X \star Y, tX \star tY).$$

**Definition 2.2.1.4.** A stratified monomorphism $f : X \to Y$ is

(1) *entire* if it is an identity on underlying simplicial sets.
(2) *regular* if for every $n \geq 1$ the following diagram is a pullback:

$$\begin{array}{ccc} tX_n & \longrightarrow & X_n \\ \downarrow & \downarrow & \downarrow \\ tY_n & \longrightarrow & Y_n. \end{array}$$

**Definition 2.2.1.5 (Verity).** We define several stratified structures on $[n]$.

(1) $[n]_t$. The top $n$-simplex is thin. All degeneracies are thin.
(2) $[n]^k$. All simplices that include $\{k-1, k, k+1\} \cap [n]$ are thin. All degeneracies are thin.
(3) $([n]^k)'$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(4) $([n]^k)''$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face, the $k$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(5) $[3]^{eq}$. All simplices of dimension strictly higher than 2, together with $[0, 2]$ and $[1, 3]$ are thin. All degeneracies are thin.
(6) $[n]^2$. All simplices are thin.

**Definition 2.2.1.6.** An *elementary anodyne extension* is one of the following:

(1) The *complicial horn inclusions* are the regular extensions:

$$\Lambda^k[n] \to [n]^k, \ n \geq 1, \ n \geq k \geq 0.$$

(2) The *complicial thinness extensions*:

$$([n]^k)' \to ([n]^k)'', \ n \geq 2, \ n \geq k \geq 0.$$

(3) The *saturation extensions*:

$$[n] \star [3]^{eq} \star [m] \to [n] \star [3]^2 \star [m], \ n, m \geq -1.$$

The set of complicial horn inclusions is $\Lambda$ and the reunion of *complicial thinness extensions* and of *saturation extensions* is $S$.

69

CHAPTER 2. STUDY OF COMPLICIAL SETS

Definition 2.2.1.7 (Verity). Let $n \in \mathbb{N} \cup \{\omega\}$. A $n$-complicial set is a stratified set having the right lifting property against all elementary anodyne extensions and against all morphisms $[k] \to [k]_t$ for $k > n$.

Theorem 2.2.1.8 (Ozornova, Rovelli, Verity). Let $n \in \mathbb{N} \cup \{\omega\}$. There exists a nice model structure on stratified simplicial sets, denoted by $\mathrm{tPsh}(\Delta)^n$, whose fibrant objects are $n$-complicial sets.

A left adjoint $F : \mathrm{tPsh}(\Delta) \to D$ to a model category is a left Quillen functor if it preserves cofibrations and sends all elementary anodyne extensions and morphisms $[k] \to [k]_t$, for $k > n$, to weak equivalences.

Proof. This is [OR20b, theorem 1.25].

Remark 2.2.1.9. The corresponding theorem for non-saturated complicial sets was originally proven by Verity in [Ver08c].

During this chapter, we will only be interested in the model structure for $\omega$-complicial sets, and we will therefore drop the index $\omega$. The $\omega$-complicial sets will then just be called complicial sets and we will denote by $\mathrm{tPsh}(\Delta)$ the model category $\mathrm{tPsh}(\Delta)^\omega$.

Proposition 2.2.1.10. Let $C$ be a nice model structure, and $F : \mathrm{tPsh}(\Delta)^1 \to C$ a left adjoint that preserves monomorphisms. The functor $F$ is a left Quillen functor if and only if it sends the following morphisms to weak equivalences:

(1) the morphisms of the set $\mathrm{W}_1$ defined in 1.1.2.15.
(2) for any integer $n \ge 2$, the morphism $[n] \to [n]_t$.
(3) the morphism $[1]_t \to [0]$.

Proof. Suppose first that $F$ is a left Quillen functor. According to [RV22, proposition E.2.8.], the functor $F(\_)^b : \mathrm{Psh}(\Delta) \to C$ is a left Quillen functor when $\mathrm{Psh}(\Delta)$ is endowed with the Joyal model structure. According to proposition 3.7.4 of [Cis19], it sends spine inclusions to weak equivalences. As $E^{eq} \to [0]$ is a weak equivalence of this model structure, it is also sent to a weak equivalence. Finally, as $[n] \to [n]_t$ for $n \ge 2$, and $[1]_t \to [0]$ are weak equivalences in $\mathrm{tPsh}(\Delta)^1$, they are sent to weak equivalences by $F$.

To show the other direction, suppose given a functor $F$ fulfilling the desired property. We denote by $S$ the class of cofibrations that are sent to weak equivalences by $F$. The class $S$ is then closed under 2 out of 3, by pushouts and contains the spine inclusions $\mathrm{Sp}_{[n]} \to [n]$.

Remark that for all integer $n$, the morphism $\mathrm{Sp}_{[n+1]} \to \mathrm{Sp}_{[n]} \star [0]$ is a sequence of pushouts along $\mathrm{Sp}_{[2]} \to [2]$ and then is in $S$. By two out of three, so is the morphism $\mathrm{Sp}_{[n]} \star [0] \to [n+1]$.

As a consequence, $S$ is closed under the functor $\_ \star [0]$, and so for any integer $n$, by the functor $\_ \star [n]$. As any simplicial set $K$ is the colimit of the Reedy cofibrant diagram $\Delta_{/K} \to \Delta \to \mathrm{Psh}(\Delta)$, and as $\star$ preserves monomorphisms, the theorem 2.1.1.7 implies that $S$ is closed under $\_ \star K$.

Now let $f : X \to Y$ be a morphism in $S$. By stability under pushout of $S$, the morphism

$$X \star [n] \to X \star [n] \coprod_{X \star \partial[n]} Y \star [n]$$

is in $S$. By two out of three, so is the morphism

$$X \star [n] \coprod_{X \star \partial[n]} Y \star \partial[n] \to Y \star [n].$$

70

2.2. THE COMPLICIAL MODEL

The set $S$ is then closed under the Leibniz product $\_ \star (\partial[n] \to [n])$. We can show similarly that $S$ is closed under the Leibniz product $(\partial[n] \to [n]) \star \_$.

As for any pair of integers $0 < i < n$, $\Lambda^i[n] \to [n]$ is the Leibniz product

$$(\partial[i - 1] \to [i - 1]) \star (\mathrm{Sp}_2 \to [2]) \star (\partial[n - i - 1] \to [n - i - 1])$$

this morphism belongs to $S$, which concludes the proof.

The functor $F((\_)^\flat)$ then preserves inner anodyne extensions and sends $E^{eq} \to 1$ to a weak equivalence. It is then a left Quillen functor when $\mathrm{Psh}(\Delta)$ is endowed with the Joyal model structure. As we have a cocartesian square

$$\begin{array}{c} E^{eq} \longrightarrow (E^{eq})^\sharp \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \longrightarrow 1 \end{array}$$

the functor $F$ sends $(E^{eq})^\sharp \to 1$ to a weak equivalence, and by two out of three, also $[1]_t \to (E^{eq})^\sharp$. Combined with [RV22, proposition D.4.8], the right adjoint of $F$ preserves fibrations between fibrant objects, and $F$ is then a left adjoint according to corollary A.2 of [Dug01].

**Definition 2.2.1.11.** A *marked simplicial set* is a stratified simplicial set that has the right lifting property against entire acyclic cofibrations. In particular, all complicial sets are marked. The category of marked simplicial sets is denoted by $\mathrm{mPsh}(\Delta)$. There is an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow[\leftarrow]{\perp} \mathrm{mPsh}(\Delta) : \iota \tag{2.2.1.12}$$

The left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified simplicial set $(X, tX)$ to the marked simplicial set $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$ a marked simplicial set. Moreover, the proposition 2.1.2.11 implies that the canonical morphism $X \to \iota(X)_{\mathrm{mk}}$ is an entire acyclic cofibration.

**Remark 2.2.1.13.** Given a functor $i : I \mapsto (F(i), tF(i))$ with value in marked simplicial sets, its colimit is given by $(\operatorname{colim} F(i), \overline{M})$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \operatorname{colim} F(i)$ for any $i : I$.

**Proposition 2.2.1.14.** *The category $\mathrm{mPsh}(\Delta)$ admits a nice model structure that makes the adjunction 2.2.1.12 a Quillen equivalence.*

*Proof.* This is a direct consequence of proposition 2.1.2.12 and theorem 2.2.1.8.

**Construction 2.2.1.15.** Let $n$ be an integer, and $(X, tX)$ a marked simplicial set. We define $\tau_n^i(tX)$ as the reunion of $tX$ and all simplices of dimension strictly superior to $n$. This induces a functor, called the *intelligent $n$-truncation*:

$$\begin{array}{rcl} \tau_n^i : & \mathrm{mPsh}(\Delta) & \mapsto & \mathrm{mPsh}(\Delta) \\ & (X, tX) & \mapsto & (X, \overline{\tau_n^i(tX)}) \end{array}$$

This functor preserves cofibrations. Given the explicit description of colimits in marked simplicial sets, it is easy to see that $\tau_n^i$ preserves colimits. For every elementary anodyne extension $i : K \to L$, we have a pushout

$$\begin{array}{c} K \longrightarrow L \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \tau_n^i(K) \longrightarrow \tau_n^i(L). \end{array}$$

71

CHAPTER 2. STUDY OF COMPLICIAL SETS

The intelligent $n$-truncation is then a left Quillen functor.

It's associated right adjoint is called the $n$-truncation and is denoted by

$$\tau_n : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta).$$

### 2.2.2 Gray operations on marked simplicial sets

Construction 2.2.2.1 (Verity). For any $n, p, q \ge 0$ such that $n = p + q$, we define:

- the degeneration partition operator:

$$\begin{array}{rcll} \Pi^1_{p,q} : & [n] & \to & [p] \\ & k & \mapsto & k \quad \text{if } k \le p \\ & k & \mapsto & p \quad \text{if } k > p \end{array} \qquad \qquad \begin{array}{rcll} \Pi^2_{p,q} : & [n] & \to & [q] \\ & k & \mapsto & 0 \quad \text{if } k \le p \\ & k & \mapsto & k - p \quad \text{if } k > p. \end{array}$$

- the face partition operator:

$$\begin{array}{rcl} \Pi^1_{p,q} : & [p] & \to & [n] \\ & k & \mapsto & k \end{array} \qquad \qquad \begin{array}{rcll} \Pi^2_{p,q} : & [q] & \to & [n] \\ & k & \mapsto & k + p. \end{array}$$

Definition 2.2.2.2 (Verity). Let $(X, tX)$ and $(Y, tY)$ be two stratified simplicial sets. We define the Gray tensor product of $(X, tX)$ and $(Y, tY)$ as the stratified simplicial set

$$(X, tX) \otimes (Y, tY) := (X \times Y, tX \otimes tY)$$

where $tX \otimes tY$ is the set of pairs $(x, y)$ such that for any partitions $(p, q)$ of $n$ either $\Pi^1_{p,q}x$ or $\Pi^2_{p,q}y$ is thin.

Remark 2.2.2.3. Let $X, Y$ be two stratified simplicial sets such that all simplices of $X$ are thin. The morphism $X \otimes Y \to X \times Y$ is then an isomorphism.

Proposition 2.2.2.4. There is a canonical isomorphism

$$(X \otimes Y)^{\mathrm{op}} \cong Y^{\mathrm{op}} \otimes X^{\mathrm{op}}$$

natural in $X$ and $Y$.

Proof. At the level of simplicial sets, this two objects are obviously isomorphic in a unique way. It is sufficient to check that the unique isomorphism preserves the marking, which is left to the reader. $\square$

Remark 2.2.2.5. In [Ver08c], it is shown that the Gray tensor is associative. The problem of this operation comes from the fact that it doesn't commute with colimits. Verity then defines an other binary operation, which is cocontinuous, the Gray pretensor ([Ver08c, definition 135]) $(X, tX) \boxtimes (Y, tY) := (X \times Y, tX \boxtimes tY)$, together with a natural transformation:

$$\_ \boxtimes \_ \to \_ \otimes \_$$

that is pointwise an entire acyclic cofibration ([Ver08b, lemma 149]). Moreover, in [ORV20], it is shown that this pretensor is a Quillen bifunctor for the model structure on $\mathrm{tPsh}(\Delta)$.

72

2.2. THE COMPLICIAL MODEL

**Definition 2.2.2.6.** Let $X$ and $Y$ be two marked simplicial sets. We define the *Gray tensor product* of $X$ and $Y$ as the marked simplicial set

$$X \otimes Y := (\iota(X) \otimes \iota(Y))_{\mathrm{mk}}$$

where $(\iota_{(\underline{\quad})}_{\mathrm{mk}}, \iota)$ is the adjunction 2.2.1.12. As $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration, we have an equality:

$$X \otimes Y := (\iota(X) \boxtimes \iota(Y))_{\mathrm{mk}}.$$

**Proposition 2.2.2.7.** *We have equalities*

$$(\_ \boxtimes \_)_{\mathrm{mk}} = (\_ \otimes \_)_{\mathrm{mk}} = (\_)_{\mathrm{mk}} \otimes (\_)_{\mathrm{mk}}.$$

*Proof.* The first equality is a consequence of the fact that $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration.

For the second one, we have to show that $(X \otimes Y)_{\mathrm{mk}} = (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. The unit of the adjunction $(\iota, (\_)_{\mathrm{mk}})$ induces a morphism $h : (X \otimes Y)_{\mathrm{mk}} \to (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. This morphism is an entire acyclic cofibration according to proposition 2.1.2.11, and the corollary 2.2 of [ORV20] and the fact that $(\_)_{\mathrm{mk}}$ is a left Quillen functor.

We then have lifts in the following diagram:

$$\begin{array}{c} (X \otimes Y)_{\mathrm{mk}} \xrightarrow{id} (X \otimes Y)_{\mathrm{mk}} \\ h \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}} \end{array}$$

As both $k$ and $h$ are the identity on the underlying simplicial sets, this implies that the stratifications of $(X \otimes Y)_{\mathrm{mk}}$ and $(X \otimes Y)_{\mathrm{mk}}$ coincide, and this two objects are then equal.

We can then deduce the following proposition:

**Proposition 2.2.2.8.** *The Gray tensor product is associative, and is a left Quillen bifunctor in $\mathrm{mPsh}(\Delta)$.*

*Proof.* The first assertion is a consequence of proposition 2.2.2.7 and the fact that the binary operation $\otimes$ on $\mathrm{tPsh}(\Delta)$ is associative. The second one is a consequence of proposition 2.2.2.7 and [ORV20, Theorem 2.1].

**Construction 2.2.2.9.** Let $X$ be a marked simplicial set. We define the *suspension* of $X$, noted by $\Sigma X$, as the following pushout:

$$\begin{array}{c} X \otimes \partial[1] \longrightarrow X \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \partial[1] \longrightarrow \Sigma X \end{array}$$

This assignation defines a cocontinuous functor $\Sigma : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{\partial[1]}$. For every acyclic cofibration $K \to L$, we have cartesian squares

$$\begin{array}{c} L \otimes \partial[1] \longrightarrow K \otimes [1] \cup L \otimes \partial[1] \longrightarrow L \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \partial[1] \longrightarrow \Sigma K \longrightarrow \Sigma L \end{array}$$

73

CHAPTER 2. STUDY OF COMPLICIAL SETS

The suspension then preserves acyclic cofibration and is then a left Quillen functor.

This functor admits a right adjoint, that sends a pair $(a, b, C)$ to $C(a, b)$ where $a, b$ are two 0-simplices of $C$. If $p : C \to D$ is a morphism between complicial sets, and $a, b$ two 0-simplices of $C$, we denote by

$$p(a, b) : C(a, b) \to D(pa, pb)$$

the induced morphism.

Construction 2.2.2.10. We introduce an other operation, the diamond product, that makes the link between the Gray tensor product and the join. Let $X$ and $Y$ be two marked simplicial sets. We define $X \diamond Y$ as the colimit of the diagram:

$$X \longleftarrow X \otimes \{0\} \otimes Y \longrightarrow X \otimes [1] \otimes Y \longleftarrow X \otimes \{1\} \otimes Y \longrightarrow Y$$

The functors

$$\_ \diamond X : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X} \quad \text{and} \quad X \diamond \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X}$$

are colimit preserving. Furthermore, for every acyclic cofibration $K \to L$, the morphism $K \diamond X \to L \diamond X$ is the horizontal colimit of the diagram:

$$\begin{array}{c} K \amalg X \longleftarrow K \otimes \partial[1] \otimes X \longrightarrow K \otimes [1] \otimes X \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ L \amalg X \longleftarrow L \otimes \partial[1] \otimes X \longrightarrow L \otimes [1] \otimes X \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that $\_ \diamond X$ is a left Quillen functor. We show analogously that $X \diamond \_$ is a left Quillen functor.

Proposition 2.2.2.11. There is a canonical isomorphism

$$(X \diamond Y)^{\mathrm{op}} \cong Y^{\mathrm{op}} \diamond X^{\mathrm{op}}$$

natural in $X$ and $Y$.

Proof. This directly follows from proposition 2.2.2.4.

Lemma 2.2.2.12. There exists a unique natural transformation $\gamma_{X,Y} : X \diamond Y \to X \star Y$ that fits in the following diagram:

$$\begin{array}{c} X \coprod Y \longrightarrow X \star Y \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \diamond Y \longrightarrow [1] \end{array}$$

Proof. We begin by defining this morphism on simplicial sets, and for this we can suppose that both $X$ and $Y$ are representables, ie $X := [n]$, $Y := [m]$. On object, this morphism is induced by the assignation:

$$p(k, 0, l) := k \quad p(k, 1, l) := l.$$

We need to verify that this morphism preserves thin cells. Suppose now that $(x, v, y)$ is a thin $n$-simplex of $X \diamond Y$. There are several cases to consider. Case $v_n = 0$. The simplex $x$ is then thin, and is sent to $x \star \emptyset$ which is also thin. Case $v_0 = 1$. Similar. Case $v_0 = 0$ and $v_n = 1$. Let $p$ be the smaller integer such that $v_p = 1$. Either $\amalg_{p-1, n-p+1}^1(x)$ or $\amalg_{p, n-p}^2(y)$ is thin. This implies that $\phi_{X,Y}(x, v, y) = \amalg_{p-1, n-p+1}^1(x) \star \amalg_{p, n-p}^2(y)$ is thin.

74

2.2. THE COMPLICIAL MODEL

**Proposition 2.2.2.13.** *For any marked simplicial sets $X, Y$, the morphism $\gamma_{X,Y}$ is a weak equivalence.*

*Proof.* The functor

$$t\Delta_{/X} \times t\Delta_{/Y} \to \mathrm{mPsh}(\Delta) \times \mathrm{mPsh}(\Delta) \xrightarrow{\gamma} \mathrm{Arr}(\mathrm{mPsh}(\Delta))$$

is Reedy cofibrant (definition 1.1.3.1). It is then enough to show the result for any couples of representables.

Let's start by the case $(X, Y) = ([n], [m])$. Let $s: X \star Y \to X \diamond Y$ be the morphism defined on objects by the formula:

$$s(k \star \emptyset) := (k, 0, 0) \quad s(\emptyset \star l) := (n, 1, l)$$

We have

$$\gamma_{X,Y} s = id \quad s\gamma_{X,Y}(k, \epsilon, l) = (k + \epsilon(n - k), \epsilon, \epsilon l).$$

Let $\eta: [n] \diamond [m] \to [n] \diamond [m]$ be induced by the application

$$(k, \epsilon, l) \mapsto (k, \epsilon, \epsilon l).$$

We are now going to construct two morphisms

$$\epsilon_0: ([n] \diamond [m]) \times [1]_t \to [n] \diamond [m] \quad \text{and} \quad \epsilon_1: ([n] \diamond [m]) \times [1]_t \to [n] \diamond [m]$$

such that

$$\epsilon_0(\_, 0) = \eta \quad \epsilon_0(\_, 1) = s\gamma_{X,Y}$$

$$\epsilon_1(\_, 0) = \eta \quad \epsilon_1(\_, 1) = id$$

The first one is induced on the level of simplicial sets by

$$(k, \epsilon, l, \alpha) \mapsto (k + \alpha\epsilon(n - k), \epsilon, \epsilon l),$$

and the second one by

$$(k, \epsilon, l, \alpha) \mapsto (k, \epsilon, (\epsilon \vee \alpha)l),$$

where $\epsilon \vee \alpha := \epsilon + \alpha - \epsilon\alpha$. These two morphisms extend to marked simplicial sets.

We proceed in a similar way with cases $(X, Y) = ([n]_t, [m]), ([n], [m]_t)$ or $([n]_t, [m]_t)$. $\square$

**Remark 2.2.2.14.** As we already now that functors $\_ \diamond X$ and $X \diamond \_$ preserve weak equivalences, the previous proposition implies that for any marked simplicial sets $X$, functors $\_ \star X$ and $X \star \_$ preserves weak equivalences and are then left Quillen functors.

**Construction 2.2.2.15.** Let $X$ be a marked simplicial set. We now describe an variation on the suspension. We define $\Sigma^* X$, as the following pushout:

$$\begin{array}{c} X \longrightarrow X \star [0] \\ \downarrow \qquad \qquad \downarrow \\ 1 \longrightarrow \Sigma^* X \end{array}$$

This assignation defines a cocontinuous functor $\Sigma^*: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{\partial[1]}$. Using proposition 2.2.2.13, all the vertical morphisms of the following diagram are weak equivalences:

$$\begin{array}{c} 1 \longleftarrow X \longrightarrow X \diamond 1 \\ \downarrow \qquad \downarrow \qquad \downarrow \\ 1 \longleftarrow X \longrightarrow X \star 1 \end{array}$$

75

CHAPTER 2. STUDY OF COMPLICIAL SETS

Remark furthermore that the colimits of these lines are also homotopy colimits. Taking the horizontal colimit, this induces a weak equivalence

$$\Sigma X \to \Sigma^* X \tag{2.2.2.16}$$

natural in $X$, where $\Sigma$ is the functor constructed in 2.2.2.9.

Construction 2.2.2.17. We define the co-join of $X$ and $Y$, denoted by $X \stackrel{co}{\star} Y$, as the colimit of the following diagram:

$$Y \longleftarrow Y \otimes \{1\} \otimes X \longrightarrow Y \otimes [1] \otimes X \longleftarrow Y \otimes \{0\} \otimes X \longrightarrow X$$

The functors

$$_{\star} \stackrel{co}{\star} X : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X} \quad \text{and} \quad X \stackrel{co}{\star} _{-} : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{/X}$$

are colimit preserving. Furthermore, for every acyclic cofibration $K \to L$, the morphism $K \stackrel{co}{\star} X \to L \stackrel{co}{\star} X$ is the horizontal colimit of the diagram:

$$\begin{array}{c} K \amalg X \longleftarrow X \otimes \partial[1] \otimes K \longrightarrow X \otimes [1] \otimes K \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ L \amalg X \longleftarrow X \otimes \partial[1] \otimes L \longrightarrow X \otimes [1] \otimes K \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that $_{\star} \stackrel{co}{\star} X$ is a left Quillen functor. We show analogously that $X \stackrel{co}{\star} _{-}$ is a left Quillen functor.

Construction 2.2.2.18. Let $X$ be a simplicial set. We define the wedge of $\Sigma X$ and $[1]$, noted by $\Sigma X \vee [1]$, as the colimit of the following diagram:

$$\begin{array}{c} X \otimes [0, 1] \longrightarrow X \otimes [2]_t \longleftarrow X \otimes [1, 2] \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ \Sigma X \longrightarrow X \vee [1] \longleftarrow [1, 2] \end{array}$$

This assignation defines a cocontinuous functor $_{\star} \vee [1] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0] \amalg [1]/}$. For every acyclic cofibration $K \to L$, the morphism $K \vee [1] \to L \vee [1]$ is the horizontal colimit of the diagram:

$$\begin{array}{c} [0] \amalg [1] \longleftarrow K \otimes ([0] \amalg [1, 2]) \longrightarrow K \otimes [2]_t \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ K \otimes [2]_t \longleftarrow L \otimes [2]_t \longrightarrow L \otimes [2]_t \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that this functor is a left Quillen functor. We denote by

$$\nabla : \Sigma X \to \Sigma X \vee [1]$$

the morphism induced by the inclusion $X \otimes [0, 2] \subset X \otimes [2]_t$ and

$$\Sigma X \hookrightarrow \Sigma X \vee [1]$$

76

2.2. THE COMPLICIAL MODEL

the morphism induced by the inclusion $X \otimes [1, 2] \subset X \otimes [2]_t$. We define similarly the left Quillen functor

$$[1] \vee \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[1]\amalg[0]}/$$

and the morphisms

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \Sigma X \hookrightarrow [1] \vee \Sigma X.$$

**Proposition 2.2.2.19.** *Morphisms*

$$\Sigma X \coprod_{[0]} [1] \to \Sigma X \vee [1] \quad \text{and} \quad [1] \coprod_{[0]} \Sigma X \to [1] \vee \Sigma X$$

*are acyclic cofibrations.*

*Proof.* We have cartesian squares:

$$\begin{array}{c} X \otimes ([0] \coprod [1, 2]) \longrightarrow X \otimes \Lambda^1[2] \longrightarrow X \otimes [2]_t \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [0] \coprod [1] \longrightarrow \Sigma X \coprod_{[0]} [1] \longrightarrow \Sigma X \vee [1]. \end{array}$$

The upper right horizontal morphism is an acyclic cofibration, and so is the downer right horizontal one. We proceed similarly for the other morphism. $\square$

**Definition 2.2.2.20.** The Gray tensor product induced a left Quillen functor

$$\_ \otimes [1] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$$

called the *Gray cylinder*. The join and the co-join also induce two left Quillen functors

$$\_ \star [0] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0]}/ \qquad [0] \stackrel{\circ}{\star} \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0]}/$$

called the *Gray cone* and the *Gray $\circ$-cone*. We denote by

$$\begin{array}{c c c c c} \mathrm{mPsh}(\Delta). & \to & \mathrm{mPsh}(\Delta) & \mathrm{mPsh}(\Delta). & \to & \mathrm{mPsh}(\Delta) \\ (X, x) & \mapsto & X_{/x} & (X, x) & \mapsto & X_{x/} \end{array}$$

respectively called the *slice of $X$ over $x$* and the *slice of $X$ under $x$*, the right adjoints of the Gray cone and the Gray $\circ$-cone.

Remark furthermore that we have canonical natural transformation $X_{x/} \to X$ and $X_{/x} \to X$, induced by the natural transformation $X \to X \star [0]$ and $X \to [0] \stackrel{\circ}{\star} X$.

### 2.2.3 Street nerve

We recall that $(0, \omega)$-categories are defined in section 1.1.1. The Gray operations on $(0, \omega)$-categories - $\_ \otimes [1]$, $\_ \star 1$, $1 \stackrel{\circ}{\star} \_ -$ are defined in section 1.2.4.

**Construction 2.2.3.1.** In [Str87], Street defines a cosimplicial object in $(0, \omega)$-cat, that associates to $n$, the $n^{th}$ *oriental* $O_n$. The original construction of this object is complicated, but Ara and Maltsiniotis have shown that it can be easily defined using Gray operations. Indeed, in [AM20, Corollaire 7.10], these authors construct an isomorphism

$$O_n \cong \overbrace{1 \star \dots \star 1}^{n+1}$$

77

CHAPTER 2. STUDY OF COMPLICIAL SETS

natural in $n$.

We can extend the functor $O_{-}: \Delta \to (0, \omega)$-cat to $t\Delta$ by defining

$$(O_{n})_{t} := \tau_{n-1}^{i}(O_{n}),$$

where $\tau_{n-1}^{i}$ denote the intelligent truncation defined in construction 2.2.1.15.

By extention by colimit, this induces a functor

$$\mathrm{R}: \mathrm{tPsh}(\Delta) \to (0, \omega)\text{-cat}.$$

As explained in example 11 of [Ver06], R preserves the Gray tensor product, and so also the suspension, the wedge, the Gray cone and the Gray o-cone. Moreover, [Ver08a, Theorem 249] states that this functor sends complicial horn inclusions and complicial thinness extensions to isomorphisms. It obviously also sends saturation extensions to isomorphisms. This functor then sends every weak equivalences to isomorphisms, and then lifts to a colimit preserving functor $\mathrm{R}: \mathrm{mPsh}(\Delta) \to (0, \omega)$-cat and induces an adjoint pair:

$$\mathrm{R}: \mathrm{mPsh}(\Delta) \xrightarrow{\quad} (0, \omega)\text{-cat}: \mathrm{N}$$

We now recall two fundamental results of strictification:

**Theorem 2.2.3.2** (Gagna, Ozornova, Rovelli). *Let $n$ be an integer. The canonical morphism*

$$[n] \to \mathrm{N}(\mathrm{R}([n]))$$

*is an acyclic cofibration.*

*Proof.* This is [GOR21, corollary 5.4].

**Theorem 2.2.3.3** (Ozornova, Rovelli). *Let $C$ be an $(0, \omega)$-category. The canonical morphism*

$$\Sigma \mathrm{N} C \to \mathrm{N}([C, 1])$$

*is an acyclic cofibration.*

*Proof.* The morphism (2.2.2.16) provides a weak equivalence $\Sigma \mathrm{N} C \to \Sigma^{*} \mathrm{N} C$. As $R$ preserves the Gray tensor product and the Gray cone, it sends this morphism to an isomorphism. We then have a commutative triangle

![img-41.jpeg](img-41.jpeg)

The theorem 3.22 of [OR22] stipulates that $\Sigma^{*} \mathrm{N} C \to \mathrm{N}([C, 1])$ is a weak equivalence, which concludes the proof.

**Definition 2.2.3.4.** We define the *Street endofunctor* $i_{str}$ to be the colimit preserving functor defined on representables by:

$$i_{str}([n]) := \mathrm{N}(\mathrm{R}([n])) \quad \text{and} \quad i_{str}([n]_{t}) := \tau_{n-1}^{i}(i_{str}([n]))$$

**Proposition 2.2.3.5.** *The functor $i_{srt}$ is left Quillen and the natural transformation*

$$id \to i_{srt}$$

*is weakly invertible.*

78

2.3. SUSPENSION AND GRAY OPERATIONS

Proof. As noticed earlier, for any integer $n$, the map $[n] \to i_{srt}([n])$ is a weak equivalence. We recall that the intelligent truncation functor $\tau_{n-1}^i : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ is a left Quillen functor, and so preserves weak equivalences between cofibrant objects. The morphism $[n]_t \to i_{str}([n]_t)$ is then a weak equivalence. The set of objects $X$ such that the morphism $X \to i_{srt}X$ is a weak equivalence is closed by homotopy colimits and includes all representables. As $i_{srt}$ preserves monomorphisms, it then consists of all marked simplicial sets. Now let $K \to L$ be an acyclic cofibration. We have a commutative square:

![img-42.jpeg](img-42.jpeg)

By two out of three, $i_{str}(K) \to i_{str}(L)$ is then an acyclic cofibration. The functor $i_{srt}$ is then left Quillen.

## 2.3 Suspension and Gray operations

### 2.3.1 Formula for the Gray cylinder

The aim of this subsection is to demonstrate the following theorem, which is the analogue in stratified simplicial sets of the theorem 1.2.4.13.

**Theorem 2.3.1.1.** *There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram*

$$[1] \forall \Sigma X \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} \Sigma X \forall [1]$$

and $(\Sigma X) \otimes [1]$.

**Construction 2.3.1.2.** Let $C$ be the following colimit:

![img-43.jpeg](img-43.jpeg)

We define several marked simplicial sets whose underlying simplicial sets are sub objects of C:

![img-44.jpeg](img-44.jpeg)

where arrows labeled by $=$ are degenerate and simplices labeled by $\sim$ are thin.

Let $B_0$ be the sub object corresponding to the image of $[0, 1, 2] \times [0, 1]$ where the marking includes all cells of dimension $\le 2$, except $[10, 20, 21]$ and $[00, 20, 21]$.

79

CHAPTER 2. STUDY OF COMPLICIAL SETS

Let $B_1$ be the sub object corresponding to the image of $[0, 2, 3] \times [0, 1]$ where the marking includes all cells of dimension $\le 2$, except $[00, 20, 21]$, $[00, 30, 31]$ and $[00, 20, 31]$.

Let $B$ be the reunion of $[0, 1, 2] \times [0, 1]$ and $[0, 2, 3] \times [0, 1]$ where the marking is the reunion of $B_0$ and $B_1$.

Lemma 2.3.1.3. Morphisms $A_0 \cup A_1 \to B_0$ and $A_3 \to B_0$ are acyclic cofibrations.

Proof. The cofibration $A_0 \cup A_1 \to B_0$ fits in the following pushout square:

$$\begin{array}{c} \Lambda^1[2] \otimes [1] \cup [2]_t \otimes \partial[1] \longrightarrow A_1 \cup A_2 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [2]_t \otimes [1] \xrightarrow{[0,1,2] \times [0,1]} B_0 \end{array}$$

The cofibration $A_3 \to B_0$ is a sequence of inclusions:

$$A_3 =: (D_0, M_0) \subset (D_1, M_1) \subset (D_2, M_2) \subset (D_3, M_3) \subset (D_4, M_4) \subset (D_5, M_5) \subset (D_6, M_6) := B_0,$$

where

- $D_1 = D_0 \cup [00, 01, 11]$;
- $D_2 = D_1 \cup [00, 10, 11]$;
- $D_2 = D_1 \cup [00, 10, 21]$;
- $D_4 = D_3 \cup [00, 01, 11, 21]$;
- $D_5 = D_4 \cup [00, 10, 11, 21]$;
- $D_6 = D_5 \cup [00, 10, 20, 21]$;

and

- $(D_0, M_0) \to (D_1, M_1)$ is a pushout of $\Lambda^1[2] \to [2]^1$;
- $(D_1, M_1) \to (D_2, M_2)$ is a pushout of $\Lambda^0[2] \to [2]^0$;
- $(D_2, M_2) \to (D_3, M_3)$ is a pushout of $\Lambda^0[2] \to [2]^0$;
- $(D_3, M_3) \to (D_4, M_4)$ is a pushout of $\Lambda^1[3] \to [3]^1$;
- $(D_4, M_4) \to (D_5, M_5)$ is a pushout of $\Lambda^0[3] \to [3]^0$;
- $(D_5, M_5) \to (D_6, M_6)$ is a pushout of $\Lambda^0[3] \to [3]^0$.

□

Lemma 2.3.1.4. Morphisms $A_2 \cup A_3 \to B_1$ and $A_4 \to B_1$ are acyclic cofibrations.

Proof. The cofibration $A_2 \cup A_3 \to B_1$ fits in the pushout square:

$$\begin{array}{c} \Lambda^1[2] \otimes [1] \cup [2]_t \otimes \partial[1] \longrightarrow A_2 \cup A_3 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [2]_t \otimes [1] \xrightarrow{[0,2,3] \times [0,1]} B_1 \end{array}$$

The cofibration $A_4 \to B_1$ is a sequence of inclusions:

$$A_4 =: (D_0, M_0) \subset (D_1, M_1) \subset (D_2, M_2) \subset (D_3, M_3) \subset (D_4, M_4) \subset (D_5, M_5) \subset (D_6, M_6) := B_1$$

where

- $D_1 = D_0 \cup [00, 21, 31]$;

80

2.3. SUSPENSION AND GRAY OPERATIONS

- $D_2 = D_1 \cup [20, 30, 31]$ ;
- $D_3 = D_2 \cup [20, 21, 31]$ ;
- $D_4 = D_3 \cup [00, 01, 21, 31]$ ;
- $D_5 = D_4 \cup [00, 20, 30, 31]$ ;
- $D_6 = D_5 \cup [00, 20, 21, 31]$ ;

and

- $(D_0, M_0) \to (D_1, M_1)$ is a pushout of $\Lambda^2[2] \to [2]^2$ ;
- $(D_1, M_1) \to (D_2, M_2)$ is a pushout of $\Lambda^1[2] \to [2]^1$ ;
- $(D_2, M_2) \to (D_3, M_3)$ is a pushout of $\Lambda^2[2] \to [2]^2$ ;
- $(D_3, M_3) \to (D_4, M_4)$ is a pushout of $\Lambda^3[3] \to [3]^3$ ;
- $(D_4, M_4) \to (D_5, M_5)$ is a pushout of $\Lambda^2[3] \to [3]^2$ ;
- $(D_5, M_5) \to (D_6, M_6)$ is a pushout of $\Lambda^3[3] \to [3]^3$ .

Lemma 2.3.1.5. The maps $A_0 \cup A_1 \cup A_2 \to B$ and $A_4 \to B$ are acyclic cofibrations.

Proof. This is a direct consequence of the last two lemmas.

Construction 2.3.1.6. The marked simplicial set $\overline{X \otimes B}$ is the pushout:

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes B}. \end{array}$$

Let $\overline{X \otimes A_i}$ and $\overline{X \otimes B_i}$ be the sub-objects of $\overline{X \otimes B}$ corresponding to image of $X \otimes A_i$ and $X \otimes B_i$.

Lemma 2.3.1.7. The inclusion $\overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \to \overline{X \otimes B}$ and $\overline{X \otimes A_4} \to \overline{X \otimes B}$ are acyclic cofibrations.

Proof. Remark that we have cocartesian squares

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes A_0 \cup X \otimes A_1 \cup X \otimes A_2 \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \longrightarrow \overline{X \otimes B} \end{array}$$

and

$$\begin{array}{c} X \otimes ([00, 01] \coprod [30, 31]) \longrightarrow X \otimes A_4 \longrightarrow X \otimes B \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod [30, 31] \longrightarrow \overline{X \otimes A_4} \longrightarrow \overline{X \otimes B} \end{array}$$

The result then follows from lemma 2.3.1.5.

Lemma 2.3.1.8. The morphisms $\overline{X \otimes A_0} \to [1] \vee \Sigma X$ and $\overline{X \otimes A_2} \to \Sigma X \vee [1]$, induced by the morphism $A_0 \to [00, 01, 11]_t$ and $A_2 \to [20, 30, 31]_t$, are acyclic cofibrations.

81

CHAPTER 2. STUDY OF COMPLICIAL SETS

Proof. We have cocartesian squares

$$\begin{array}{c} X \otimes ([00, 01] \coprod \{11\}) \longrightarrow X \otimes [00, 01] \coprod_{X \otimes [01]} X \otimes [01, 11] \xrightarrow{\sim} X \otimes A_0 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [00, 01] \coprod \{11\} \xrightarrow{\quad} [1] \coprod_{[0]} \Sigma X \xrightarrow{\sim} \overline{X \otimes A_0} \end{array}$$

That shows that $[1] \coprod_{[0]} \Sigma X \to \overline{X \otimes A_0}$ is an acyclic cofibration. We then have a commutative diagram:

$$[1] \coprod_{[0]} \Sigma X \xrightarrow{\sim} \overline{X \otimes A_0} \longrightarrow [1] \vee \Sigma X$$

and by two out of three, this shows that $\overline{X \otimes A_0} \to [1] \vee \Sigma X$ is an acyclic cofibration. We proceed similarly for the second morphism.

Lemma 2.3.1.9. Marked simplicial sets $\overline{X \otimes A_1}$ and $\overline{X \otimes A_4}$ are respectively equal to $\Sigma(X \otimes [1])$ and $(\Sigma X) \otimes [1]$.

Proof. This is true by the definition of these objects.

Proof of theorem 2.3.1.1. According to lemma 2.3.1.9 we have a cocartesian square

$$\begin{array}{c} \overline{X \otimes A_0} \coprod \overline{X \otimes A_2} \longrightarrow \overline{X \otimes A_0} \cup \overline{X \otimes A_1} \cup \overline{X \otimes A_2} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \vee \Sigma X \coprod \Sigma X \vee [1] \longrightarrow [1] \vee \Sigma X \coprod_{\Sigma(X \otimes \{0\})} \Sigma(X \otimes [1]) \coprod_{\Sigma(X \otimes \{1\})} \Sigma X \vee [1] \end{array}$$

The left vertical morphism is a weak equivalence according to lemma 2.3.1.8, and the horizontal morphisms are cofibrations. By left properness, the right vertical morphism is a weak equivalence. Combined with lemmas 2.3.1.7 and 2.3.1.9, this provides a zigzag of weak equivalences between $[1] \vee \Sigma X \coprod_{\Sigma(X \otimes \{0\})} \Sigma(X \otimes [1]) \coprod_{\Sigma(X \otimes \{1\})} \Sigma X \vee [1]$ and $(\Sigma X) \otimes [1]$.

### 2.3.2 Formulas for the Gray cone and the Gray o-cone

The aim of this subsection is to demonstrate the following theorem, which is the analogue in stratified simplicial sets of the theorem 1.2.4.14.

Theorem 2.3.2.1. There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram

$$\Sigma X \vee [1] \leftarrow \Sigma X \rightarrow \Sigma([0] \stackrel{co}{\star} X)$$

and $\Sigma X \star [0]$.

There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram

$$\Sigma(X \star [0]) \leftarrow \Sigma X \rightarrow [1] \vee \Sigma X$$

and $[0] \stackrel{co}{\star} \Sigma X$.

82

2.3. SUSPENSION AND GRAY OPERATIONS

Proof. We consider the diagram:

$$\begin{array}{c} [1] \longleftarrow [1] \coprod_{[0]} \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \\ \downarrow{id} \qquad \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow{id} \\ [1] \longleftarrow [1] \vee \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \end{array}$$

All vertical morphisms are weak equivalences. We denote by $A$ the colimit of the first line. The theorem 2.3.1.1 implies that there is a zigzag of acyclic cofibrations between $A$ and $X \diamond [0]$. Colimits of the two lines are homotopy colimits, and the comparison morphism is then an acyclic cofibration. We then have a zigzag of acyclic cofibrations:

$$X \star [0] \leftarrow X \diamond [0] \rightsquigarrow A \rightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma([0] \stackrel{co}{\star} X)$$

The second assertion is demonstrated similarly.

Corollary 2.3.2.2. Let $f : C \to D$ be a fibration between complicial sets, and $K \to L$ a cofibration. If $f$ has the right lifting property against

$$\Sigma([0] \stackrel{co}{\star} K \cup \emptyset \star L) \rightarrow \Sigma([0] \stackrel{co}{\star} L),$$

then $f$ has the right lifting property against

$$(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \rightarrow \Sigma K \star [0].$$

If $f$ has the right lifting property against $\Sigma[1] \rightarrow \Sigma[1]_t$, then $f$ has the right lifting property against

$$[1]_t \star \emptyset \cup [1] \star [0] \rightarrow [1]_t \star [0]$$

Proof. Suppose that $f$ fulfills the condition. The class of cofibration having the right lifting property against $f$ is closed by pushouts and, according to 2.1.1.15, by zigzag of acyclic cofibration. The morphism

$$\alpha : \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K \coprod_{\emptyset \star K} \emptyset \star L) \rightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} L)$$

is then in this class. Remark that we have a cocartesian square

$$\begin{array}{c} \Sigma L \cup [1] \coprod_{\Sigma K \cup [1]} \Sigma K \vee [1] \longrightarrow \Sigma L \cup [1] \coprod_{\Sigma K \cup [1]} \Sigma K \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \Sigma L \vee [1] \longrightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K \coprod_{\emptyset \star K} \emptyset \star L) \end{array}$$

where the left vertical morphism, and so also the right vertical morphism, is an acyclic cofibration. This induces a zigzag of acyclic cofibration between $\alpha$ and $\beta$ where $\beta$ is

$$\Sigma L \cup [1] \coprod_{\Sigma K \cup [1]} \Sigma K \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K) \rightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} L)$$

Eventually, the theorem 2.3.2.1 induces a zigzag of acyclic cofibration between $\beta$ and $(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \rightarrow \Sigma K \star [0]$ which concludes the proof of the first assertion.

83

CHAPTER 2. STUDY OF COMPLICIAL SETS

For the second assertion, remark that $[1]_t \star [0]$ is $\tau_1^i([1]_t \star \emptyset \cup [1] \star [0])$. As $\tau_1^i$ is a left Quillen functor, the theorem 2.3.2.1 induces a zigzag of acyclic cofibration between $[1]_t \star \emptyset \cup [1] \star [0] \to [1]_t \star [0]$ and

$$[1]_t \forall [1] \coprod_{[1]} \Sigma[1] \to [1]_t \forall [1] \coprod_{[1]} \Sigma[1]_t.$$

As this cofibration is a pushout of $\Sigma[1] \to \Sigma[1]_t$, this concludes the proof.

Corollary 2.3.2.3. Let $f : C \to D$ be a fibration between complicial sets, and $K \to L$ a cofibration. If $f$ has the right lifting property against

$$\Sigma(L \star \emptyset \cup K \star [0]) \to \Sigma(L \star [0]),$$

then $f$ has the right lifting property against

$$[0] \stackrel{co}{\star} \Sigma K \cup \emptyset \star \Sigma L \to [0] \stackrel{co}{\star} \Sigma L.$$

If $f$ has the right lifting property against $\Sigma[1] \to \Sigma[1]_t$, then $f$ has the right lifting property against

$$[0] \stackrel{co}{\star} [1] \cup \emptyset \star [1]_t \to [0] \stackrel{co}{\star} [1]_t$$

Proof. The proof is similar to the one of corollary 2.3.2.2.

## 2.4 Globular equivalences

### 2.4.1 Homotopy categories

Definition 2.4.1.1. The $n$-globe is the marked simplicial set $\mathbf{D}_n := \Sigma^n[0]$. We then have $\mathbf{D}_0 := [0]$ and $\mathbf{D}_{n+1} := \Sigma \mathbf{D}_n$. This defines a globular object in $\mathrm{mPsh}(\Delta)$:

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

and we have equalities:

$$i_{n+1}^- i_n^+ = i_{n+1}^+ i_n^- \quad i_{n+1}^+ i_n^- = i_{n+1}^+ i_n^+.$$

We also set $(\mathbf{D}_n)_t := \tau_{n-1}^i(\mathbf{D}_n)$ for $n > 0$ and $\partial \mathbf{D}_n := \Sigma^n \emptyset$. We then have a canonical inclusions

$$\partial \mathbf{D}_0 \to \mathbf{D}_0$$

and for any $n > 0$, we have canonical inclusions

$$\partial \mathbf{D}_n \to \mathbf{D}_n \to (\mathbf{D}_n)_t.$$

Let $C$ be a complicial set. A $n$-cell $a$ of $C$ is a morphism $a : \mathbf{D}_n \to C$. If $n$ is non null, the source of $a$ (resp. the target of $a$) is the $(n-1)$-cell $a \circ i_{n-1}^-$ (resp. $a \circ i_{n-1}^+$). The cell $a$ is marked if the corresponding morphism $\mathbf{D}_n \to C$ factorizes via $(\mathbf{D}_n)_t$.

84

2.4. GLOBULAR EQUIVALENCES

From now on, and until the end of this section, we fix a complicial set $C$. All considered cells are cells of $C$.

**Definition 2.4.1.2.** Let $n$ be a non null integer, and $a, b$ two $n$-cells. Cells $a$ and $b$ are *parallel* if they share the same source and the same target. They are *composable* if the source of $a$ is the target of $b$.

Let $a$ and $b$ be two parallel cells. The cell $a$ is *equivalent* to the cell $b$ if there exists a marked $(n + 1)$-cell $d : a \to b$, or equivalently, if there exists a homotopy $\mathbf{D}_n \times [1]_t$ between $a$ and $b$, and constant on $\partial \mathbf{D}_n \times [1]_t$. This relation is denoted by $\sim$.

**Lemma 2.4.1.3.** *The relation $\sim$ is reflexive, symmetric and transitive.*

*Proof.* This comes from usual properties of fibrant objects.

**Lemma 2.4.1.4.** *Let $a, b$ be two equivalent cells. If $a$ is marked, so is $b$.*

*Proof.* As $\{0\} \to [1]_t$ is a weak equivalence, so is $\mathbf{D}_n \times [1]_t \cup (\mathbf{D}_n)_t \times \{0\} \to (\mathbf{D}_n)_t \times [1]_t$. As $C$ is fibrant, this directly implies the result.

**Construction 2.4.1.5.** Let $a, b$ be two composable $n$-cells. A composition of $a$ and $b$ is a $n$-cell $a \circ b$ that fits in a diagram:

![img-45.jpeg](img-45.jpeg)

As $C$ is a fibrant object, if $(a \circ b)'$ is any other composition, $(a \circ b)' \sim a \circ b$.

**Lemma 2.4.1.6.** *Let $a, b, c$ be three composable cells. There exists compositions such that $(a \circ b) \circ c = a \circ (b \circ c)$.*

*Proof.* Let $M$ be the marking on $[3]$ that includes all simplices of dimension superior or equal to 2. We define $\mathrm{Sp}_{[3]}$ as the simplicial set $[1] \coprod_{[0]} [1] \coprod_{[0]} [1]$. Remark that the cofibration $\mathrm{Sp}_{[3]} \to ([3], M)$ is acyclic. We then have a lift $f$ in the following diagram

![img-46.jpeg](img-46.jpeg)

The morphism $f$ provides all the desired compositions.

**Definition 2.4.1.7.** We define the category $\pi_0(C)$ whose objects are 0-cells $x : s \to t$, and edges between $x, y : s \to t$ are equivalence classes of the set of 1-cells $f : x \to y$ quotiented by the relation $\sim$. The composition is given by construction 2.4.1.5 which is associative according to lemma 2.4.1.6.

Let $n > 0$ be an integer, and $s, t$ two parallel $(n - 1)$-cells. We define the category $\pi_n(s, t, C)$ whose objects are $n$-cells $x : s \to t$, and edges between $x, y : s \to t$ are equivalence classes of the set of $(n + 1)$-cells $f : x \to y$ quotiented by the relation $\sim$. The composition is given by construction 2.4.1.5 which is associative according to lemma 2.4.1.6.

85

CHAPTER 2. STUDY OF COMPLICIAL SETS

Proposition 2.4.1.8. Let $x, y : s \to t$ be two parallel $n$-cells, and $f : x \to y$ a $n + 1$-cell. The cell $f$ is marked if and only if $[f] : x \to y$ is an isomorphism in $\pi_n(s, t, C)$.

Proof. Suppose first that $f$ is marked. There are liftings in the following diagrams:

![img-47.jpeg](img-47.jpeg)

Let $g : y \to z$ be the restriction of $h$ to $\Sigma^n[1, 2]$ and $l : y \to z$ be the restriction of $k$ to $\Sigma^n[0, 1]$. We then have $[f][g] = id$, and $[h][f] = id$, and $[f]$ is then an isomorphism.

For the other direction, suppose that $[f]$ is an isomorphism. Let $M$ be the marking on $[3]$ that includes all simplices of dimension superior or equal to 2. As $\mathrm{Sp}_{[3]} \to ([3], M)$ is a weak equivalence, there is a lifting in the following diagram:

![img-48.jpeg](img-48.jpeg)

Now $h(\Sigma^n[0, 3])$ and $h(\Sigma^n[0, 2])$ are respectively compositions of $(f, f^{-1})$ and $(f^{-1}, f)$. Hypotheses imply that these compositions are equivalent to identities, and so are marked. The morphism then lifts to $\Sigma^n[3]^{eq}$. The object $C$ being fibrant, $h$ lifts to $\Sigma^n[3]^2$, and $f$ is then marked.

Lemma 2.4.1.9. Let $s, t$ and $s', t'$ be two pairs of parallel cells, and $\psi : \partial\mathbf{D}_n \times [1]_t \to C$ a homotopy between $s \cup t : \partial\mathbf{D}_n \to C$ and $s' \cup t' : \partial\mathbf{D}_n \to C$. Then

$$\pi_n(s, t, C) \cong \pi_n(s', t', C)$$

Proof. For each $x : s \to t$, there exists a lifting $h_x$ in the following diagram:

![img-49.jpeg](img-49.jpeg)

and we define $F(x)$ as the restriction of $h_x$ to $\mathbf{D}_n \times \{1\}$. For a $(n + 1)$-cell $f : x \to y$, there exists a lifting $h_f$ in the following diagram:

![img-50.jpeg](img-50.jpeg)

and we define $F(f)$ as the restriction of $h_f$ to $\mathbf{D}_{n+1} \times \{1\}$. Furthermore, the unicity up to homotopy of lifting implies that $[F(f)]$ is independent of the choice of the lifting, and that $f \sim g$ implies $[F(f)] = [F(g)]$. If $g : y \to z$ is an other morphism, and $\psi : \Sigma^n[2]_t \to C$ corresponds to the composition of $f$ and $g$, there is a lift in the following diagram:

![img-51.jpeg](img-51.jpeg)

86

2.4. GLOBULAR EQUIVALENCES

Restricted to $\Sigma^n[2]_t \times \{1\}$ this shows that $F$ commutes with compositions. We then have defined a functor

$$F : \pi_n(s, t, C) \to \pi_n(s', t', C).$$

Using exactly the same procedure, where we just invert 0 and 1, we define a functor:

$$G : \pi_n(s', t', C) \to \pi_n(s, t, C).$$

Now, we have a lift in the following diagram:

$$\begin{array}{c} \mathbf{D}_n \times \Lambda^2[2]^\sharp \cup \partial \mathbf{D}_n \times [2]^\sharp \xrightarrow{h_x \cup h_{F(x)} \cup \psi(id \times s^0)} C \\ \downarrow \\ \mathbf{D}_n \times [2]^\sharp \end{array}$$

The restriction of $k_x$ to $\mathbf{D}_n \times [0,1]_t$ provides a marked cell $x \to G(F(x))$, which corresponds to an isomorphism in $\pi_n(s, t, C)$ according to proposition 2.4.1.8. If $f : x \to y$ is a $(n+1)$-cell, there is a lifting in the following diagram:

$$\begin{array}{c} \mathbf{D}_{n+1} \times \Lambda^2[2]^\sharp \cup \partial \mathbf{D}_{n+1} \times [2]^\sharp \xrightarrow{h_f \cup h_{F(f)} \cup k_x \cup k_y} C \\ \downarrow \\ \mathbf{D}_{n+1} \times [2]^\sharp \end{array}$$

The restriction of $k_f$ to $\mathbf{D}_{n+1} \times [0,1]_t$ induces in $\pi_n(s, t, C)$ a commutative diagram:

$$\begin{array}{c} x \longrightarrow GFx \\ [f] \downarrow \qquad \downarrow [GFf] \\ y \longrightarrow GFy. \end{array}$$

We then have an invertible natural transformation $\psi : id \to GF$. Similarly we can construct an other natural transformation $id \to GF$, which shows the desired equivalence of categories.

**Definition 2.4.1.10.** Let $a$ be an element of $\mathrm{Hom}_{h\circ(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, C)$. We define

$$\pi_n(a, C) := \pi_n(s, t, C) \tag{2.4.1.11}$$

where $s, t$ is a pair of parallel arrows such that $s \cup t$ represents $a$. The previous proposition shows that this is well defined.

### 2.4.2 A criterion to be a weak equivalence

**Definition 2.4.2.1.** A morphism $p : C \to D$ between complicial sets is a **D**-equivalence if

$$\pi_0(C) \to \pi_0(D)$$

is an equivalence of categories, and for any $n > 0$ and pair of parallel arrow $s, t$, the induced functor

$$\pi_n(s, t, C) \to \pi_n(ps, pt, D)$$

is an equivalence of categories.

A **D**-trivial *fibration* is a fibration having the right lifting property against $\partial \mathbf{D}_n \to \mathbf{D}_n$ and $\mathbf{D}_n \to (\mathbf{D}_n)_t$.

87

CHAPTER 2. STUDY OF COMPLICIAL SETS

Lemma 2.4.2.2. Let \(\alpha \in \{-, +\}\). The morphism \(i_{n+1}^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t\) is an acyclic cofibration.

Proof. We have a pushout diagram

\[
\begin{array}{c} \mathbf {D} _ {n} \times \{\alpha \} \cup \partial \mathbf {D} _ {n} \times [ 1 ] _ {t} \xrightarrow {i d \cup \partial \times s ^ {\theta}} \mathbf {D} _ {n} \times \{\alpha \} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf {D} _ {n} \times [ 1 ] _ {t} \xrightarrow {} (\mathbf {D} _ {n}) _ {t} \end{array}
\]

The left hand morphism being an acyclic cofibration, this concludes the proof.

Lemma 2.4.2.3. Acyclic cofibrations between complicial sets are D-equivalences.

Proof. Let \( i: A \to B \) be an acyclic cofibration. The morphism \( i \) admits a retraction \( r: B \to A \):

![img-52.jpeg](img-52.jpeg)

and a homotopy \(\psi\) between \(id_B\) and \(ir\) which is constant on the image of \(i\), obtained as the lift in the following diagram:

\[
\begin{array}{c} B \times \{0 \} \coprod_ {A \times \{0 \}} A \times [ 1 ] _ {t} \longrightarrow B \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ B \times [ 1 ] _ {t} \end{array}
\]

Let \( n > 0 \) be an integer, and \( s, t \) be two \( (n - 1) \)-cells of \( C \). The retraction implies that \( i_{!} \) is an injection on morphisms. For any \( n \)-cell \( y: i(s) \to i(t) \) in \( B \), the homotopy \( \psi \) induces a marked cell \( y \to ir(y) \) which corresponds to an isomorphism in \( \pi_n(is, it, B) \) according to proposition 2.4.1.8. The functor \( i_{!} \) is then essentially surjective. For any \( (n + 1) \)-cell \( f: i(x) \to i(y) \), the homotopy \( \psi \) induces an equivalence \( [ir(f)] \sim [f] \). The morphism \( i_{!} \) is a surjection on morphisms. All put together, \( i_{!} \) is fully faithfull and essentially surjective, and is then an equivalence. We proceed similarly to show that \( i_{!}: \pi_0(A) \to \pi_0(B) \) is an equivalence.

Lemma 2.4.2.4. Suppose given a commutative triangle between complicial sets

![img-53.jpeg](img-53.jpeg)

If \(i\) is an acyclic cofibration, and \(g\) is a \(\mathbf{D}\)-equivalence, then \(f\) is a \(\mathbf{D}\)-equivalence.

Proof. Let \( s, t \) be any pair of parallel arrows in \( B \). There exists a pair of parallel arrows \( s', t' \) in \( A \) such that \( s \cup t \) and \( is' \cup it' \) correspond to the same element in \( [\partial \mathbf{D}_n, B] \). We then have a diagram:

\[
\begin{array}{c} \pi (s, t, B) \longrightarrow \pi (f s, f t, C) \\ \Big \downarrow^ {\sim} \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow^ {\sim} \\ \pi (s, t, B) \xrightarrow {\sim} \pi (i s, i t, B) \longrightarrow \pi (g s, g t, C). \\ \sim \end{array}
\]

where arrows labeled by \(\sim\) are isomorphisms according to lemmas 2.4.1.9 and 2.4.2.3. By two out of three, this shows that \(\pi(s,t,B) \to \pi(fs,ft,C)\) is an isomorphism, and \(f\) is then a \(\mathbf{D}\) equivalence.

88

2.4. GLOBULAR EQUIVALENCES

**Proposition 2.4.2.5.** Let $p : C \to D$ be a fibration between complicial sets. The morphism $p$ is a **D**-trivial fibration if and only if it is a **D**-equivalence.

*Proof.* If $p$ is a **D**-trivial fibration, it is obvious that it is a **D**-equivalence. For the converse, suppose $p$ is a fibration and a **D**-equivalence, and consider a diagram

$$\begin{array}{c} \partial \mathbf {D} _ {n} \longrightarrow C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow p \\ \mathbf {D} _ {n} \xrightarrow [ x ]{} D \end{array}$$

As $p$ is a **D**-equivalence this implies that there exists a cell $\overline{x} : \mathbf{D}_n \to C$ together with a marked $(n+1)$-cell $y : p(\overline{x}) \to y$. All this data corresponds to a diagram:

$$\begin{array}{c} \mathbf {D} _ {n} \xrightarrow {\bar {x}} C \\ \Big \downarrow_ {n + 1} \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow p \\ (\mathbf {D} _ {n + 1}) _ {t} \xrightarrow [ y ]{} D \end{array}$$

The left hand morphism being an acyclic cofibration according to 2.4.2.2, this diagram admits a lift $h : (\mathbf{D}_{n+1})_t \to C$. The restriction of $h$ to $i_{n+1}^+$ provides a lift in the first diagram. Now, we consider a diagram of shape:

$$\begin{array}{c} \mathbf {D} _ {n} \xrightarrow {g} C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow p \\ (\mathbf {D} _ {n}) _ {t} \longrightarrow D \end{array}$$

with $n > 1$. Let $s, t$ be respectively the $(n - 1)$-source and the $(n - 1)$-target of $g$. Hypotheses imply that $[p(g)]$ is an isomorphism in $\pi_n(s, t, D)$ and because $p$ is a **D**-equivalence, so is $[g]$. According to lemma 2.4.1.8, this implies that $g$ is marked. There exists then a lifting in the previous diagram. The case $n = 1$ is similar. The morphism $f$ is then a **D**-trivial fibration. $\square$

**Lemma 2.4.2.6.** Let $p : X \to Y$ be a **D**-trivial fibration between complicial sets. Then for any $x \in X_0$, the induced fibrations

$$X _ { / x } \to X \times _ { Y } Y _ { / p ( x ) } \quad a n d \quad X _ { x / } \to X \times _ { Y } Y _ { p ( x ) / }$$

are **D**-trivial fibrations.

*Proof.* We define $\mathbb{P}(p, n)$ to be the statement that $p$ has the right lifting property against

$$\mathbf {D} _ {n} \cup \partial \mathbf {D} _ {n} \star [ 0 ] \to \mathbf {D} _ {n + 1} \star [ 0 ] \mathrm {a n d} (\mathbf {D} _ {n}) _ {t} \cup \mathbf {D} _ {n} \star [ 0 ] \to (\mathbf {D} _ {n}) _ {t} \star [ 0 ]$$

and against

$$[ 0 ] \stackrel {c o} {\star} \partial \mathbf {D} _ {n} \cup \mathbf {D} _ {n} \to [ 0 ] \stackrel {c o} {\star} \mathbf {D} _ {n + 1} \mathrm {a n d} [ 0 ] \star \mathbf {D} _ {n} \cup (\mathbf {D} _ {n}) _ {t} \to [ 0 ] \stackrel {c o} {\star} (\mathbf {D} _ {n}) _ {t}$$

We then have to show that for any $n$, $\mathbb{P}(p, n)$ holds.

First, it is obvious that each **D**-equivalence $p$ satisfies $\mathbb{P}(p, 0)$. As $p$ is a fibration, the corollaries 2.3.2.2 and 2.3.2.3 then imply that $\mathbb{P}(p, n + 1)$ is equivalent to $\mathbb{P}(p(a, b), n)$ for any $a, b \in X_0$, where $p(a, b)$ is the induced morphism: $X(a, b) \to Y(p(a), p(b))$.

Using the fact that $p(a, b)$ is a **D**-trivial fibration as soon as $p$ is, this shows the desired result. $\square$

89

CHAPTER 2. STUDY OF COMPLICIAL SETS

Lemma 2.4.2.7. D-Trivial fibrations between complicial sets have the right lifting property against $\partial[n] \to [n]$.

Proof. Let $C$ be the class of cofibrations having the right lifting property against D-equivalences. The lemma 2.4.2.6 implies that for any $K \to L$ in $C$, the induced morphism:

$$L \cup K \star [0] \to L \star [0]$$

is in $C$. The class $C$ is then closed under Leibniz join. Furthermore, it includes $\partial[1] \to [1]$, and then, by induction, it includes $\partial[n] \to [n]$ for any integer $n$. $\square$

Lemma 2.4.2.8. D-Trivial fibrations between complicial sets have the right lifting property against $[n] \to [n]_t$.

Proof. Let $p$ be D-trivial fibrations between complicial sets, and $C_{n,p}$ be the set of objects $A$ such that $p$ has the right lifting property against:

$$A \to \tau_{n-1}^i(A).$$

This set is then closed under colimits, and by zigzags of acyclic cofibrations. Let $k \le n$ be two integers. We define $\mathbb{P}(k, n, p)$ to be the statement that

$$\Sigma[n-k]_\circ \star [k-1] \quad \text{and} \quad [k-1]_\circ \overset{\text{co}}{\star} \Sigma[n-k]$$

are in $C_{n+1,p}$. The statement $\mathbb{P}(0, 0, f)$ corresponds to the belonging of $\mathbf{D}_1$ to $C_{1,p}$, which is obviously true. Suppose that $0 < k$ and $\mathbb{P}(k-1, n, p)$. According to theorem 2.3.2.1, the object $\Sigma[n-k]_\circ \star [k-1]$ is linked by a zigzag of acyclic cofibrations to the colimit of

$$(\Sigma[n-k]_\circ \vee [1]) \star [k-2] \leftarrow (\Sigma[n-k]_\circ) \star [k-2] \to (\Sigma[n-k+1]_\circ) \star [k-2]$$

The center object and the left hand object are in $C_{n+1,p}$ because there are invariant under $\tau_n^i$, and the right hand object is in $C_{n+1,p}$ by induction hypothesis. The object $\Sigma[n-k]_\circ \star [k-1]$ is then in $C_{n+1,p}$. We demonstrate similarly that $[k-1]_\circ \overset{\text{co}}{\star} \Sigma[n-k]$ is in $C_{n+1,p}$.

This then implies $\mathbb{P}(k, n, p)$. Eventually, $\mathbb{P}(0, n+1, p)$ is equivalent to $\mathbb{P}(n, n, p(a, b))$ for any pair of objects $(a, b) \in X_0$. The statement $\mathbb{P}(k, n, p)$ is then true for any $k, n$ and D-trivial fibrations between complicial sets $p$. This implies that $p$ has the right lifting property against $[n] \to [n]_t$. $\square$

Theorem 2.4.2.9. Let $p$ be a map between complicial sets. Then $p$ is a weak equivalence if and only if it is a D-equivalence.

Proof. According to lemmas 2.4.2.3 and 2.4.2.4 we can restrict ourselves to the case where $p$ is a fibration. If it is a weak equivalence, $p$ is then a trivial fibration and is then a D-equivalence. Suppose now that $p$ is a D-equivalence. According to proposition 2.4.2.5, $p$ is then a D-trivial fibration. Lemmas 2.4.2.7 and 2.4.2.8 imply that $p$ is a trivial fibration. $\square$

Definition 2.4.2.10. Let $p: X \to Y$ be a morphism between complicial sets. The morphism $p$ is essentially surjective for marked simplicial sets if for any $x \in Y_0$, there exists $\bar{x} \in X_0$ together with a marked cell $\bar{x} \to x$. The morphism $f$ is fully faithful if the induced morphisms:

$$X(a, b) \to Y(pa, pb)$$

are weak equivalences for any $a, b \in X_0$.

90

2.4. GLOBULAR EQUIVALENCES

Corollary 2.4.2.11. Let p be a map between complicial sets. Then p is a weak equivalence if and only if it is fully faithfull and essentially surjective.

Proof. If p is a weak equivalence, it is then fully faithfull and essentially surjective. Conversely, suppose p is fully faithfull and essentially surjective. The morphism π₀(X) → π₀(Y) is fully faithfull and essentially surjective, and then an equivalence of category. For (a, b) a pair of 0-cells, we have equalities:

$$\begin{array}{c} \pi_{1}(a, b, X) = \pi_{0}(X(a, b)) \\ \pi_{1}p \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \pi_{1}(pa, pb, Y) = \pi_{0}(Y(pa, pb)). \end{array}$$

The morphism π₁(a, b, p) is then an equivalence of categories. For (s, t) a pair of parallel arrows of dimension > 1, if we denote by a and b the 0-source and the 0-target of s and t, we have a diagram:

$$\begin{array}{c} \pi_{n}(s, t, X) = \pi_{n-1}(s, t, X(a, b)) \\ \pi_{n}p \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \pi_{n}(pa, pb, Y) = \pi_{n-1}(s, t, Y(pa, pb)). \end{array}$$

The morphism πₙ(a, b, p) is then an equivalence of categories. The morphism p is then a D-equivalence, and according to 2.4.2.9, a weak equivalence.

### 2.4.3 A criterion to be a weakly invertible transformation

The purpose of this section is to show the following proposition:

Proposition 2.4.3.1. Let i : mPsh(Δ) → mPsh(Δ) and j : mPsh(Δ) → mPsh(Δ) be two left Quillen functors and ψ : i → j a natural transformation. If ψ(Dₙ) : i(Dₙ) → j(Dₙ) is a weak equivalence for any n, then ψ(X) : i(X) → j(X) is a weak equivalence for any X.

For the remaining of this section, we fix two left Quillen functors i, j and a natural transformation ψ : i → j satisfying the previous hypothesis. We denote by Nᵢ and Nⱼ the right adjoints of i and j.

Lemma 2.4.3.2. Morphisms ψ(∂Dₙ) : i(∂Dₙ) → j(∂Dₙ) are weak equivalences.

Proof. We proceed by induction on n. The case n = 0 is trivial. Suppose then the result true at the stage n - 1. Remark then that ∂Dₙ is the colimit and the homotopy colimit of the span

$$\mathbf{D}_{n-1} \leftarrow \partial \mathbf{D}_{n-1} \rightarrow \mathbf{D}_{n-1}$$

As i and j are left Quillen functors, the induction hypothesis implies that ψ(∂Dₙ) : i(∂Dₙ) → j(∂Dₙ) is a weak equivalence.

Lemma 2.4.3.3. Morphisms ψ((Dₙ)ₜ) : i((Dₙ)ₜ) → j((Dₙ)ₜ) are weak equivalences.

Proof. There is a diagram:

$$\begin{array}{c} i_{!}\mathbf{D}_{n-1} \xrightarrow[\sim]{\psi(\mathbf{D}_{n})} j_{!}\mathbf{D}_{n-1} \\ i_{!}(i_{n}^{-}) \downarrow \sim \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ i_{!}(\mathbf{D}_{n})_{t} \xrightarrow[\psi((\mathbf{D}_{n})_{t})]{} j_{!}(\mathbf{D}_{n})_{t} \end{array}$$

By two out of three, this shows that ψ((Dₙ)ₜ) is a weak equivalence.

91

CHAPTER 2. STUDY OF COMPLICIAL SETS

**Lemma 2.4.3.4.** *For any complicial set $Y$, the canonical morphism $N_j Y \to N_i Y$ is a weak equivalence.*

*Proof.* Let $Y$ be a complicial set. For any integer $n$, we have by adjunction a bijection

$$\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_i Y)$$

and according to lemmas 2.4.3.2 and 2.4.3.3, we have bijections

$$\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, N_i Y)$$

$$\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_i Y).$$

Let $a$ be an element of $\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, N_j Y)$. We recall that the category $\pi_n(a, N_j Y)$ is defined in 2.4.1.11. The previous equivalences implies that we have an isomorphism of category

$$\pi_n(a, N_j Y) \cong \pi_n(a, N_j Y).$$

which concludes the proof according to theorem 2.4.2.9. $\square$

*Proof of the proposition 2.4.3.1.* Let $X$ be any marked simplicial set and $Y$ a complicial set. We have equalities:

$$\begin{array}{ccc} \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(j_! X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, j^* Y) \\ \downarrow & & \downarrow \\ \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(i! X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, i^* Y) \end{array}$$

Lemma 2.4.3.4 implies that the right hand morphism is a bijection, and so is the left hand morphism. For any $X$, $\psi(X)$ is then a weak equivalence. $\square$

## 2.4.4 Weak characterization of the identity

For the rest of this section, we fix a left Quillen functor $i: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ such that there exists a zigzag of weakly invertible natural transformations:

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

**Lemma 2.4.4.1.** *Let $n$ be any integer, the following natural transformations are pointwise acyclic cofibrations:*

$$i\tau_n^i \to \tau_n^i i \tau_n^i \leftarrow \tau_n^i i.$$

*Proof.* These are natural transformations between left Quillen functors. The hypothesis implies that they induce weak equivalences on globes of dimension inferior or equal to $n$. Remark that for any $k > n$, as $i_{k-1}^-: \mathbf{D}_{k-1} \to (\mathbf{D}_k)_t$ is an acyclic cofibration and $\tau_n^i$ preserves them, $\tau_n^i \mathbf{D}_{k-1} \to \tau_n^i \mathbf{D}_k$ is an acyclic cofibration. A direct induction implies that $\mathbf{D}_n = \tau_n^i \mathbf{D}_n \to \tau_n^i \mathbf{D}_k$ is an acyclic cofibration. We then have a commutative diagram:

$$\begin{array}{ccc} i\tau_n^i(\mathbf{D}_k) & \longrightarrow & \tau_n^i i \tau_n^i(\mathbf{D}_k) \longleftarrow \tau_n^i i(\mathbf{D}_k) \\ & \searrow & \uparrow \searrow \\ & & i(\mathbf{D}_n) \end{array}$$

where all morphisms labelled by $\sim$ are weak equivalences.

By two out of three, this implies that these natural transformations induce weak equivalences on all globes, and proposition 2.4.3.1 concludes the proof. $\square$

92

2.4. GLOBULAR EQUIVALENCES

**Proposition 2.4.4.2.** *There exists a zigzag of weakly invertible natural transformations*

$$i \rightsquigarrow j$$

where $j$ is a left Quillen functor such that $j([n]) = i([n])$ and $j([n]_t) = \tau_{n-1}^i i([n])$, and such that the image of $[n] \to [n]_t$ by $j$ is induced by the canonical morphism $id \to \tau_{n-1}^i(id)$.

*Proof.* We define $\tilde{i}$ (resp. $j$) to be the colimit preserving functor defined on representables by $\tilde{i}([n]) := i([n])$ and $\tilde{i} := ([n]_t) = \tau_{n-1}^i i([n]_t)$ (resp. $j([n]) := i([n])$ and $j([n]_t) := \tau_{n-1}^i i([n]))$. We then have a zigzag of natural transformations

$$i \xrightarrow{\sim} \tilde{i} \xleftarrow{\sim} j.$$

that are pointwise acyclic cofibrations according to 2.4.4.1. This implies that both $\tilde{i}$ and $j$ are left Quillen functors.

In the following lemmas, we use the Steiner theory recalled in section 1.2.1.

**Lemma 2.4.4.3.** *Let $m$ be an integer and $X$ and $Y$ be two $(0, \omega)$-categories admitting a loop free and atomic basis. We denote by $0$, $1$ and $t$ the three points of $\Sigma X \vee [1]$. Let*

$$f : \Sigma^m([X, 1] \star Y) \to \Sigma^m(([X, 1] \vee [1]) \star Y)$$

*be a morphism fitting in the following diagram:*

$$\begin{array}{ccc} \Sigma^m((\{0\} \coprod \{1\}) \star Y) & \xrightarrow{\Sigma^m(g \star Y)} & \Sigma^m(([X, 1] \vee [1]) \star Y) \\ \downarrow & \xrightarrow{f} & \downarrow \\ \Sigma^m([X, 1] \star Y) & \xrightarrow{id} & \Sigma^m([X, 1] \star Y) \end{array}$$

where $g$ sends $0$ on $0$, and sends $1$ on $t$ and the right vertical morphism induced by the retraction $[X, 1] \vee [1] \to [X, 1]$.

Then $f$ is $\Sigma^m(\nabla \star Y)$.

*Proof.* All these categories admit loop free and atomic basis. We can then show this lemma in the category of augmented directed complexes. Furthermore, in this category, the suspension only makes an index shift, so we can assume without loss of generality that $m = 0$.

The commutativity of the diagram implies that

$$\begin{array}{rcl} f(0 \star x) & = & 0 \star x \\ f(1 \star x) & = & t \star x \\ f([x, 1] \star y) & = & [x, 1] \star y + r_{x,y} \end{array}$$

where $r_{x,y}$ is a positive sum of elements of $(B_{[1]\star Y})_{|x|+|y|+1}$. We show by induction on $|x| + |y|$ that:

$$\begin{array}{rcl} r_{x,y} & = & [1] \star y \quad \text{if } |x| = 0 \\ & = & 0 \quad \text{if } |x| > 0. \end{array}$$

93

CHAPTER 2. STUDY OF COMPLICIAL SETS

Suppose the result true when the sum of dimensions of $x$ and $y$ is $(k - 1)$. Let $x, y$ be two cells such that $|x| + |y| = k$. Case $|x| = 0$. The commutativity of $f$ with $\partial$ and the induction hypothesis imply that

$$\begin{array}{l} \partial r_{x, y} = f(\partial([x, 1] \star y)) - \partial([x, 1] \star y) \\ = \{t\} \star y - \{0\} \star y + f([x, 1] \star \partial y) - \{1\} \star y + \{0\} \star y - [x, 1] \star \partial y \\ = \{t\} \star y - \{1\} \star y + [1] \star \partial y \end{array}$$

and $r_{x,y}$ is then equal to $[1] \star y$. Case $|x| > 0$. The commutativity of $f$ with $\partial$ implies that

$$\partial r_{x, y} = 0$$

and $r_{x,y}$ is then equal to 0.

Lemma 2.4.4.4. Let $m$ be an integer and $X$ and $Y$ be two $(0, \omega)$-categories admitting a loop free and atomic basis. We denote by 0, 1 and $t$ the three points of $\Sigma X \vee [1]$. Let

$$f: \Sigma^m([X, 1] \star Y) \to \Sigma^m(([X, 1] \vee [1]) \star Y)$$

be a morphism fitting in the following diagram:

![img-54.jpeg](img-54.jpeg)

Then $f$ is the morphism induced by the retraction $[X, 1] \vee [1] \to [X, 1]$.

Proof. The proof is an easy computation using Steiner theory, similar to the one done in lemma 2.4.4.3, and left to the reader.

Definition 2.4.4.5. Let $C$ be the subcategory of marked simplicial sets whose

- objects are the marked simplicial sets $X$ such that $\mathrm{R}(X)$ has no non-trivial automorphisms, and such that there exists a (necessary unique) isomorphism

$$\phi_X: \mathrm{R}(iX) \to \mathrm{R}(X),$$

- morphisms are the maps $f: X \to Y$ making the induced diagram

$$\begin{array}{c} \mathrm{R}(i(X)) \xrightarrow{\phi_X} \mathrm{R}(X) \\ \mathrm{R}(i(f)) \downarrow \qquad \qquad \qquad \qquad \downarrow \mathrm{R}(f) \\ \mathrm{R}(i(Y)) \xrightarrow{\phi_Y} \mathrm{R}(Y) \end{array}$$

commutative.

We recall that the functor $R: \mathrm{mPsh}(\Delta) \to (0, \omega)$-cat is defined in construction 2.2.3.1.

94

2.4. GLOBULAR EQUIVALENCES

**Remark 2.4.4.6.** As R sends acyclic cofibrations to isomorphisms, $C$ is stable by zigzags of acyclic cofibrations. Moreover, as R and $i$ preserve colimits, for any diagram $F: I \to C$ such that the $(0, \omega)$-category $\mathrm{R}(\mathrm{colim}_I F)$ has no non-trivial automorphisms, $\mathrm{colim}_I F$ is in $C$. Eventually, the colimit of any natural transformation between two such diagrams is in $C$.

**Lemma 2.4.4.7.** *Let $(k, n)$ be a couple of integers such that $k \leq n$. We set the convention $[-1] := \emptyset$. For any integer $m$, the following assertion holds:*

(1) $\Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ and $\Sigma^m([k-1]_\circ \stackrel{co}{\star} \Sigma[n-k])$ are in $C$.
(2) For any $-1 \leq l \leq k-1$ and $0 \leq p \leq n-k$, and any monomorphisms $[l] \to [k-1]$ and $[p] \to [n-k]$, the morphisms

$$\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([l]_\circ \stackrel{co}{\star} \Sigma[p]) \to \Sigma^m([k-1]_\circ \stackrel{co}{\star} \Sigma[n-k])$$

are in $C$.

(3) For any $\epsilon \in \{0, 1\}$, the morphisms

$$\Sigma^m(\{\epsilon\} \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([k-1]_\circ \stackrel{co}{\star} \{\epsilon\}) \to \Sigma^m([k-1]_\circ \stackrel{co}{\star} \Sigma[n-k])$$

are in $C$.

(4) If $k > 0$, the morphisms

$$\Sigma^m(\emptyset \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([k-1]_\circ \stackrel{co}{\star} \emptyset) \to \Sigma^m([k-1]_\circ \stackrel{co}{\star} \Sigma[n-k])$$

are in $C$.

*Proof.* We will proceed by induction on $(k, n)$.

- The case $(0, 0)$ corresponds to the belonging of globes to $C$, which is true by the assumptions we made on the functor $i$ and by the proposition 1.2.4.20 that assert that the globes have no non-trivial automorphisms.
- We now suppose that the case $(n-1, n-1)$ holds and we are willing to show the case $(0, n)$. The assertions (1) and (2) are direct consequences of the case $(n-1, n-1)$ after remarking the isomorphisms:

$$\Sigma^m \Sigma[n] \cong \Sigma^{m+1}((\Sigma[0]_\circ) \star [n-2]) \quad \Sigma^m \Sigma[n]_\circ \cong \Sigma^{m+1}([n-2]_\circ \stackrel{co}{\star} (\Sigma[0]))$$

It remains to show the third assertion. Let $m$ be any integer and $\epsilon \in \{0, 1\}$. By induction hypothesis and by the belonging of globes to $C$, the following morphism

$$\Sigma^m(\{\epsilon\}) \to \Sigma^m(\Sigma\{0\}) \cong \Sigma^{m+1}\{0\} \to \Sigma^{m+1}((\Sigma[0]_\circ) \star [n-2]) \cong \Sigma^m \Sigma[n]$$

is in $C$. As the morphism $\Sigma^m(\{\epsilon\}) \to \Sigma^m \Sigma[n]$ is their composite, it belongs to $C$. We proceed similarly to show that $\Sigma^m(\{\epsilon\}) \to \Sigma^m \Sigma[n]_\circ$ belongs to $C$. This concludes the proof of the case $(0, n)$.

- Suppose the result true for the couples $(k-1, n)$, $(k-1, n-1)$ and $(k-1, k-1)$ for an integer $k$ strictly superior to 0 and inferior or equal to $n$. We are willing to show the case $(k, n)$. Let $m$ be any integer.

As $R$ commutes with Gray operations and pushouts, the lemma 1.2.4.19 implies that $\Sigma^m((\Sigma[n-k]_\circ \coprod_{[0]}[1]) \star [k-2])$ together with all the objects appearing in the statement of this lemma are sent by R to $(0, \omega)$-categories with loop free and atomic basis and admitting no non-trivial automorphisms.

95

CHAPTER 2. STUDY OF COMPLICIAL SETS

Remark 2.4.4.6 implies that for one of these objects (resp. a morphism between them) to belong to $C$, it is sufficient to show that it is linked by a zigzag of acyclic cofibrations to the colimit, computed in $\mathrm{mPsh}(\Delta)$, of a diagram with value in $C$ (resp. in the arrow category of $C$).

As $\Sigma[0]_{\circ} = [1]$, the case $(k - 1, k - 1)$ implies that the morphism

$$\Sigma^{m}(\{0\} \star [k - 1]) \to \Sigma^{m}([1] \star [k - 1])$$

is in $C$. Combined with the case $(k - 1, n - 1)$, this implies that the diagram

$$\begin{array}{c} \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \longrightarrow \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \\ \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \uparrow \\ \Sigma^{m}([0] \star [k - 2]) \xrightarrow{id} \Sigma^{m}([0] \star [k - 2]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \Sigma^{m}([0] \star [k - 2]) \longrightarrow \Sigma^{m}([1] \star [k - 2]) \end{array}$$

is in $C$, and so is it's vertical colimits. As the codomain is weakly equivalent to $\Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2])$, this implies that $C$ includes the canonical morphism

$$\Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \hookrightarrow \Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]). \tag{2.4.4.8}$$

We can show similarly that the canonical morphism

$$\Sigma^{m}([1] \star [k - 2]) \hookrightarrow \Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]). \tag{2.4.4.9}$$

is in $C$.

The image by R of the canonical morphism

$$\Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]) \to \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2])$$

induced by the retraction $\Sigma[n - k]_{\circ} \vee [1] \to \Sigma[n - k]_{\circ}$ fulfills the condition of lemma 2.4.4.4 and then belongs to $C$. The lemma 2.4.4.3 then implies that the morphism

$$\Sigma^{m}(\nabla \star [k - 2]) : \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \to \Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]) \tag{2.4.4.10}$$

is in $C$. We will use freely in the rest of the proof that morphisms (2.4.4.8), (2.4.4.9) and (2.4.4.10) are in $C$.

Theorem 2.3.2.1 implies that the object $\Sigma^{m}(\Sigma[n - k]_{\circ} \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the colimit of

$$\Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]) \leftarrow \Sigma^{m}(\Sigma[n - k]_{\circ} \star [k - 2]) \to \Sigma^{m}(\Sigma[n - k + 1]_{\circ} \star [k - 2])$$

and the induction hypothesis implies that it belongs to $C$. We proceed similarly to show that $\Sigma^{m}([k - 1]_{\circ} \stackrel{\infty}{\star} \Sigma[n - k])$ belongs to $C$.

Let $0 \leq l \leq k - 1$ and $-1 \leq p \leq n - k$ be two integers, and $f : [l] \to [k - 1]$ and $g : [p] \to [n - k]$ be two monomorphisms. Suppose first that $f$ is of shape $[0] \star f'$ for $f' : [l - 1] \to [k - 2]$. In this case,

96

2.4. GLOBULAR EQUIVALENCES

$\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m((\Sigma[p]_\circ \lor [1]) \star [l - 1]) \longrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \uparrow \\ \Sigma^m(\Sigma[p]_\circ \star [l - 1]) \longrightarrow \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \Sigma^m(\Sigma[p + 1]_\circ \star [l - 1]) \longrightarrow \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. Suppose now that $f$ avoids the initial object of $[k - 1]$. In this case, the morphism $\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m(\Sigma[p]_\circ \star [l]) \longrightarrow \Sigma^m((\Sigma[n - k]_\circ) \star [k - 2]) \hookrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^m([l]_\circ \stackrel{co}{\star} \Sigma[p]) \to \Sigma^m([k - 1]_\circ \stackrel{co}{\star} \Sigma[n - k])$$

belongs to $C$.

The morphism $\Sigma^m(\{0\} \star [k - 1]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\{0\} \star [k - 1]) \cong \Sigma^m((\Sigma\{n - k + 1\}) \star [k - 2]) \longrightarrow \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. The morphism $\Sigma^m(\{1\} \star [k - 1]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m(\{1\} \star [k - 1]) \cong \Sigma^m([1] \star [k - 2]) \hookrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that for any $\epsilon \in \{0, 1\}$,

$$\Sigma^m([k - 1]_\circ \stackrel{co}{\star} \{\epsilon\}) \to \Sigma^m([k - 1]_\circ \stackrel{co}{\star} \Sigma[n - k])$$

97

CHAPTER 2. STUDY OF COMPLICIAL SETS

belongs to $C$.

Eventually, the morphism $\Sigma^m(\emptyset \star [k - 1]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m(\{1\} \star [k - 2]) \longrightarrow \Sigma^m([1] \star [k - 2]) \hookrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^m([k - 1]_\circ \stackrel{cp}{\star} \emptyset) \to \Sigma^m([k - 1]_\circ \stackrel{cp}{\star} \Sigma[n - k])$$

belongs to $C$.

We have then proven the case $(k, n)$, and this concludes the proof.

Lemma 2.4.4.11. Let $F : \Delta \to (0, \omega)$-cat be a functor and $\phi : F \to \mathbb{R}$ be a invertible transformation such that for any monomorphism $i : [k] \to [n]$, the induced square

$$\begin{array}{c} F([k]) \xrightarrow{\phi_{[k]}} \mathbb{R}([k]) \\ F(i) \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F([n]) \xrightarrow{\phi_{[n]}} \mathbb{R}([n]) \end{array}$$

commutes. Then $\phi$ is an invertible natural transformation between $F$ and $\mathbb{R}$.

Proof. We can suppose without loss of generality that for all integer $n$, $F([n]) = \mathbb{R}([n])$. The hypotheses implies that for any monomorphism $i : [n] \to [m]$, $F(i) = \mathbb{R}(i)$ and it then remains to show that for any degeneracy $p : [n] \to [m]$, $F(p) = \mathbb{R}(p)$.

We proceed by induction and we then suppose that for any $0 < k \le n$ and any degeneracy $s : [k] \to [k - 1]$, $F(s) = \mathbb{R}(s)$. As any morphism of $\Delta$ factors as a degeneracy followed by a monomorphism, the induction hypothesis implies that for any $f : [k] \to [n]$ with $k \le n$, $F(f) = \mathbb{R}(f)$.

Let $s : [n + 1] \to [n]$ be a degeneracy. We have a a priori non commutative diagram:

$$\begin{array}{c} \operatorname{colim}_{[k] \xrightarrow{\varphi_{id}} [n+1]} \mathbb{R}([k]) \xlongequal{\text{colim}}_{[k] \xrightarrow{\varphi_{id}} [n+1]} \mathbb{R}([k]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{R}([n+1]) \xlongequal{\text{ }} \mathbb{R}([n+1]) \\ F(s) \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{R}([n]) \xlongequal{\text{ }} \mathbb{R}([n]) \end{array}$$

The induction hypothesis implies that the outer and the upper square commute. As $R$ commutes with colimits, $\operatorname{colim}_{[k] \to \partial[n]} \mathbb{R}([k])$ is equivalent to $\mathbb{R}(\partial[n])$. Moreover, the inclusion $\mathbb{R}(\partial[n]) \to \mathbb{R}([n])$ induces an isomorphisms on cells of dimension lower or equal to $n$. For the lower square to commutes, we then only have to check that the top cell of $\mathbb{R}([n+1])$ is sent on the same element on $\mathbb{R}([n])$. That is the case because the two paths send it to an unity as there is no non trivial $(n+1)$-cells in $\mathbb{R}([n])$.

We then have $F(s) = \mathbb{R}(s)$, which concludes the induction and then the proof.

98

2.4. GLOBULAR EQUIVALENCES

**Proposition 2.4.4.12.** *There exists an invertible natural transformation* $\mathrm{R}\,i \to \mathrm{R}$.

*Proof.* As $\Sigma[0]_\circ$ is isomorphic to $[1]$, the case $(n, n)$ for any integer $n$ of the lemma 2.4.4.7 imply that there exists an invertible transformation $\phi : (\mathrm{R}\,i)_{|\Delta} \to \mathrm{R}_{|\Delta}$ which is natural when restricted to the full subcategory of $\Delta$ whose morphisms are the monomorphisms.

The lemma 2.4.4.11 then implies that $\phi : (\mathrm{R}\,i)_{|\Delta} \to \mathrm{R}_{|\Delta}$ is natural. We can extend it to a natural transformation $\phi' : (\mathrm{R}\,i)_{|t\Delta} \to \mathrm{R}_{|t\Delta}$ thanks to the proposition 2.4.4.2.

Eventually, as both $\mathrm{R}\,i$ and $\mathrm{R}$ preserves colimits, we can extend $\phi'$ to a invertible natural transformation between $\mathrm{R}\,i$ and $\mathrm{R}$. $\square$

**Theorem 2.4.4.13.** *Let $i : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ be a left Quillen functor. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$. In particular, $i$ is a left Quillen equivalence.*

*Proof.* The proposition 2.4.4.12 implies that we have a natural transformation $\psi : i \to i_{str}$. Furthermore, hypotheses imply that this natural transformation is a weak equivalence on globes. According to proposition 2.4.3.1, $\psi$ is then a weakly invertible natural transformation. We then have a zigzag of weakly invertible natural transformations:

$$i \xrightarrow{\sim} i_{str} \xleftarrow{\sim} id.$$

**Corollary 2.4.4.14.** *Let $i : \mathrm{tPsh}(\Delta) \to \mathrm{tPsh}(\Delta)$ be a left Quillen functor. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$. In particular, $i$ is a left Quillen equivalence.*

*Proof.* We recall that the adjunction between stratified and marked simplicial sets is denoted by:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow{\perp} \mathrm{mPsh}(\Delta) : \iota$$

The proposition 2.1.2.8 states that this adjunction is a Quillen equivalence and that the functor $\iota$ preserves acyclic cofibrations.

Remark now that the functor $(\_)_{\mathrm{mk}} \circ i \circ \iota : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ verifies the hypothesis of theorem 2.4.4.13 and we then have a zigzag of of weakly invertible natural transformations:

$$(\_)_{\mathrm{mk}} \circ i \circ \iota \rightsquigarrow id$$

This induces a zigzag of of weakly invertible natural transformations:

$$i \to \iota \circ (\_)_{\mathrm{mk}} \circ i \circ \iota \circ (\_)_{\mathrm{mk}} \rightsquigarrow \iota \circ (\_)_{\mathrm{mk}} \leftarrow id$$

99

CHAPTER 2. STUDY OF COMPLICIAL SETS

100

## Chapter 3

# Complicial sets as a model of  $(\infty, \omega)$ -categories

### Contents

|  **3.1** | **Preliminaries** | **102**  |
| --- | --- | --- |
|  3.1.1 | Segal $A$-precategories | 102  |
|  3.1.2 | Stratified Segal $A$-precategories | 105  |
|  3.1.3 | Models of $(\infty, n)$-categories | 109  |
|  3.1.4 | Gray module | 109  |
|  3.1.5 | Complicial Gray module | 113  |
|  **3.2** | **Complicial Gray module structure on tSeg($A$)** | **114**  |
|  3.2.1 | $\circ$-cone in tSeg($A$) | 114  |
|  3.2.2 | Adjunction with tPsh($\Delta$) | 117  |
|  3.2.3 | Complicial horn inclusions | 118  |
|  3.2.4 | Complicial thinness extensions | 125  |
|  3.2.5 | Saturation extensions | 133  |
|  3.2.6 | Conclusion | 134  |
|  **3.3** | **Complicial sets as of model of $(\infty, n)$-categories** | **134**  |
|  3.3.1 | The case $n < \omega$ | 134  |
|  3.3.2 | The case $n = \omega$ | 138  |

Results of Gagna, Harpaz et Lanari ([GHL22]) states that 2-complicial sets are a model of $(\infty, 2)$-categories. The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

The heart of the proof corresponds to constructing a Quillen adjunction between complicial sets and Segal precategories enriched in a model category $A$. We begin with the study (stratified) $A$-Segal categories. We then introduce the concept of *complicial Gray module* (definition 3.1.5.4). In short, a model category $A$ is a complicial Gray module when it admits a *Gray $\circ$-cylinder* $C \mapsto I \otimes C$ and a *Gray op-cone* $C \mapsto e \star C$, and when the assignment $[n] \rightarrow e \star e \star \dots e \star \emptyset$ lifts to a Quillen adjunction with stratified simplicial sets endowed with the model structure for complicial sets.

We then prove the following stability result:

101

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

**Theorem 3.2.6.2.** *If A is a complicial Gray module, then the category of stratified Segal precategories enriched in A is also a complicial Gray module.*

We will apply this theorem to the case where A is the category of stratified simplicial sets endowed with the model structure for n-complicial sets. Bergner results imply that stratified Segal precategories enriched in a model of (∞, n)-categories form models of (∞, n + 1)-categories. By induction, we then prove the following theorem:

**Theorem 3.3.1.11.** *Let n ∈ ℕ. The model structure for n-complicial sets is a model of (∞, n)-categories.*

Finally, in 3.3.2.1, we construct a Quillen adjunction between Θ-spaces and ω-complicial sets and prove the following result:

**Theorem 3.3.2.5.** *The adjunction*

$$\mathrm{Psh}(\Theta \times \Delta) \xleftrightarrow{\perp} \mathrm{tPsh}(\Delta)$$

constructed in 3.3.2.1 is a Quillen equivalence. Hence, the model structure for ω-complicial sets is a model of (∞, ω)-categories.

## 3.1 Preliminaries

### 3.1.1 Segal A-precategories

We fix a category A of stratified presheaves on a elegant Reedy category (as defined in definition 1.1.2.8 and section 2.1.2), endowed with a nice model structure (as defined in definition 2.1.1.6). We suppose furthermore that the terminal element of A, denoted by e, is representable.

**Definition 3.1.1.1.** We have an adjunction

$$\iota : \text{Set} \xleftrightarrow{\perp} A : ob \tag{3.1.1.2}$$

where the left adjoint sends a set S onto Π_S e and the right adjoint is the evaluation at e. The objects lying in the image of ι are called discrete objects.

**Definition 3.1.1.3.** An object C of Fun(Δ^op, A) is a Segal A-precatagory if C₀ is discrete. We denote by Seg(A) the full subcategory of Fun(Δ^op, A) spanned by the Segal A-precategories.

**Construction 3.1.1.4.** Let a be an object of A and n an integer. We denote by |[a, n]| the object of Fun(Δ^op, A) whose value on m is a × ι(Hom_Δ([m], [n])). This assignation defines a functor

$$\begin{array}{l} A \times \Delta \rightarrow \text{Fun}(\Delta^{op}, A) \\ (a, [n]) \mapsto \quad |[a, n]| \end{array}$$

We define the Segal A-precategory [a, n] as the pushout:

$$\begin{array}{c} \bigcup_{k \leq n} |[a, \{k\}]| \longrightarrow |[a, n]| \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ |[e, 0]| \longrightarrow [a, n] \end{array}$$

102

3.1. PRELIMINARIES

The object $[e, 0]$, which is the terminal Segal $A$-precategory, is simply denoted by $[0]$.

The assignation $(a, n) \mapsto [a, n]$ induces by left Kan extension a colimit preserving functor

$$[\_, \_]: A \times \operatorname{Psh}(\Delta) \to \operatorname{Seg}(A).$$

The image of this functor is dense in $\operatorname{Seg}(A)$.

**Construction 3.1.1.5.** For $\{n_i\}_{i \le k}$ and $\{a \to a_i\}_{i \le k}$ two finite sequences, we denote by $[a_0, n_0] \vee [a_1, n_1] \vee \dots \vee [a_k, n_k]$ the Segal $A$-precategory fitting in the following pushout:

$$\begin{array}{ccc} \amalg_{i \le k}[a, n_i] & \longrightarrow & [a, \Sigma_{i \le k} n_i] \\ \downarrow & & \downarrow \\ \amalg_{i \le k}[a_i, n_i] & \longrightarrow & [a_0, n_0] \vee [a_1, n_1] \vee \dots [a_k, n_k] \end{array}$$

The case we will use the most is the one of the Segal $A$-precategories $[e, 1] \vee [a, n]$ and $[a, n] \vee [e, 1]$ corresponding to the sequence $((1, n), (a \to e, a \to a))$ and $((n, 1), (a \to a, a \to e))$.

**Definition 3.1.1.6.** Let $B$ be the Reedy category and $M$ the subset of objects of $B$ such that $A$ is the category of $M$-stratified presheaves on $B$. We define the category $\Delta[B]$ as the fully faithful subcategory of $\operatorname{Seg}(A)$ whose objects are of shape $[b, n]$ for $b \in B$ and $n$ an integer. Eventually, we define $\Delta[M]$ as the set of objects of shape $[b, n]$ for $b \in M$ and $n > 0$. We can easily check that the category $\operatorname{Seg}(A)$ is the category of $\Delta[M]$-stratified presheaves on $\Delta[B]$.

A cellular model for $\operatorname{tSeg}(A)$ is given by the set of morphisms $[b, \partial n] \cup [a, n] \to [b, n]$ for $n$ an integer, and $a \to b$ a generating cofibration of $A$.

Eventually, for any Segal $A$-precategory $C$, we have an isomorphism

$$C \cong \underset{\Delta[tB]/C}{\operatorname{colim}} [b, n].$$

Following the definition of section 2.1.2, a morphism between Segal precategories is *entire* if it is the identity on the underlying $\Delta[B]$-presheaves.

**Proposition 3.1.1.7.** *The category $\Delta[B]$ as a structure of elegant Reedy category.*

*Proof.* Remark first that $\operatorname{Hom}_{\Delta[B]}([a, n], [b, m])$ fits in the following cocartesian square:

$$\begin{array}{ccc} \coprod_{k \le m} \operatorname{Hom}_B(a, b) \times \operatorname{Hom}_\Delta([n], \{k\}) & \longrightarrow & \operatorname{Hom}_B(a, b) \times \operatorname{Hom}_\Delta([n], [m]) \\ \downarrow & & \downarrow \\ \coprod_{k \le m} \operatorname{Hom}_\Delta([n], \{k\}) & \longrightarrow & \operatorname{Hom}_{\Delta[B]}([a, n], [b, m]) \end{array}$$

We then define the degree functor $ob(\Delta[B]) \to \mathbb{N}$ by the formula $d([b, n]) = d(b)d(n)$. The subcategory $(\Delta[B])_+$ is the image of $\Delta_+ \times B_+$, and the subcategory $(\Delta[B])_-$ is the image of $\Delta_- \times B_-$.

We recall that we suppose that the Reedy category $B$ is elegant. Let $X$ be a presheaf on $\Delta[B]$, $[a, n]$ an element of $\Delta[A]$, $[f, g]: [a, n] \to [a', n']$ and $[h, i]: [a, n] \to [a', n']$ two negative morphisms, an element $x$ of $X([a, n])$, two non degenerate elements $y \in X([a', n'])$ and $z \in X([a'', n''])$ such that $[f, g]^* y = x$, $[h, i]^* z = x$.

We suppose first that $n \neq 0$. We denote by $\pi: B \times \Delta \to \Delta[B]$ the canonical projection and

$$\pi^*: \operatorname{Psh}(\Delta[B]) \to \operatorname{Psh}(\Delta \times B)$$

103

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

the functor obtained by precomposing. Remark that for any $a, n$, $(\pi^*X)(a, n) = X([a, n])$. Furthermore, we have again equalities $(f, g)^*y = x$, $(h, i)^*z = x$. As $\Delta \times B$ is Reedy elegant, this implies that $f = h$, $g = i$ and $y = z$.

If $n = 0$, then $[f, g]$ and $[h, i]$ are the identity, and we directly have $y = z$. The Reedy category $\Delta[B]$ is then elegant.

**Definition 3.1.1.8.** An *elementary anodyne extension* is one of the following:

(1) The *generating Reedy cofibrations*:

$$[a, n] \cup [b, \partial[n]] \to [b, n], \text{ for } a \to b \text{ a generating acyclic cofibration of A.}$$

(2) The *Segal extensions*:

$$[a, 1] \cup [a, 1] \cup \dots \cup [a, 1] \to [a, n], \text{ for } a \text{ an object of } A \text{ and } n > 0.$$

(3) The *completeness extensions*:

$$\{0\} \to [e, E^{eq}].$$

where $E^{eq}$ is the object defined in 1.1.2.15.

**Definition 3.1.1.9.** A *Segal A-category* is a Segal $A$-precategory having the right lifting property against all elementary anodyne extensions.

Let $C$ be a Segal $A$-categories. We define the presheaf $ho(C) : \Delta^{op} \to \text{Set}$ sending $[n]$ to $\text{Hom}_{ho(A)}(e, C_n)$. As explained in [Sim11, § 14.5], this simplicial set has the unique right lifting property against Segal's maps, and is then the nerve of a category that we also note by $ho(C)$. An arrow $x : [e, 1] \to C$ is an *isomorphism* if its image in $ho(C)$ is.

We can give an other characterization of isomorphisms in Segal $A$-categories. An arrow $x : [e, 1] \to C$ is an isomorphism if and only if there exists a lifting in the following diagram:

![img-55.jpeg](img-55.jpeg)

A morphism $f : C \to D$ between Segal $A$-categories is an *equivalence of Segal A-categories* if $C_1 \to D_1$ is a weak equivalence in $A$, and for any element $x \in ob(D)$, there exists $y \in ob(C)$ and an isomorphism in $D$ between $f(y)$ and $x$.

**Theorem 3.1.1.10** (Simpson). *There exists a nice model structure on $\text{Seg}(A)$ where fibrant objects are Segal $A$-categories and weak equivalences between Segal $A$-categories are equivalences of Segal $A$-categories.*

*A left adjoint from $\text{Seg}(A)$ to a model category $C$ is a left Quillen functor if it preserves cofibrations, and sends elementary anodyne extensions to weak equivalences.*

*Proof.* This is [Sim11, 21.2.1].

**Proposition 3.1.1.11.** *Any Segal $A$-precategory is a homotopy colimit of objects of shape $[a, n]$.*

*Proof.* Let $C$ be a Segal $A$-precategory. We have $C \cong \text{colim}_{\Delta[tB]/C}$. The result then follows from propositions 1.1.2.9, 2.1.2.6 and 3.1.1.7.

104

3.1. PRELIMINARIES

### 3.1.2 Stratified Segal $A$-precategories

Definition 3.1.2.1. A stratified Segal $A$-precategory is a pair $(C, tC)$ where $tC$ is a subset of $ob(C_1)$ that factors $s^0 : C_0 \to ob(C_1)$. A morphism of stratified Segal $A$-precategory $(C, tC) \to (D, tD)$ is the data of a morphism $f : C \to D$ such that $f(tC) \subset tD$. The category of stratified Segal $A$-precategories is denoted by $\mathrm{tSeg}(A)$.

We have an adjunction

$$(\_)^b : \mathrm{Seg}(A) \xrightarrow{\quad} \mathrm{tSeg}(A) : (\_)^\natural \tag{3.1.2.2}$$

where the left adjoint is a fully faithful inclusion that sends $C$ to $C^b := (C, Im(s^0))$. The right adjoint is the obvious forgetful functor. We will identify Segal $A$-precategories with their images in stratified Segal $A$-precategories under the left adjoint.

Definition 3.1.2.3. We define $[e, 1]_t := ([e, 1], [e, 1]_1)$. The subcategory of objects of shape $[a, n]$ or $[e, 1]_t$ is then dense in $\mathrm{tSeg}(A)$.

Definition 3.1.2.4. Let $B$ be the Reedy category and $M$ the subset of objects of $B$ such that $A$ is the category of $M$-stratified presheaves on $B$. We recall that we defined the category $\Delta[B]$ and the set of morphism $\Delta[M]$ in definition 3.1.1.6. We set $t\Delta[M]$ as the reunion of $\Delta[M]$ and the singleton $\{[e, 1]_t\}$. We can easily check that the category $\mathrm{tSeg}(A)$ is the category of $t\Delta[M]$-stratified presheaves on $\Delta[B]$.

Remark 3.1.2.5. The set of generating cofibrations for $\mathrm{tSeg}(A)$ then consists of morphisms of shape $[e, 1] \to [e, 1]_t$ or $[a, n] \cup [b, \partial n] \to [b, n]$ where $a \to b$ is a generating cofibration of $A$. For any stratified Segal $A$-precategory $C$, we then have an isomorphism

$$C \cong \underset{t\Delta[tB]/C}{\mathrm{colim}}.$$

where $t\Delta[tB]$ is the full subcategory of $\mathrm{tSeg}(A)$ whose objects are of in $\Delta[B]$ or $t\Delta[M]$.

Definition 3.1.2.6. Following the definition of section 2.1.2, a morphism between stratified Segal precategories is entire if it is the identity on the underlying $\Delta[B]$-presheaves.

Definition 3.1.2.7. A marked Segal $A$-category is a pair $(C, C^\cong)$ where $C$ is a Segal $A$-category and $C^\cong$ is the subset of $ob(C_1)$ consisting of all isomorphisms. A morphism $f : (C, C^\cong) \to (D, D^\cong)$ between marked Segal $A$-categories is an equivalence of marked Segal $A$-categories if $C_1 \to D_1$ is a weak equivalence in $A$, and for any element $x \in ob(D)$, there exists $y \in ob(C)$ and $v : f(y) \to x \in D^\cong$.

We are now willing to endow $\mathrm{tSeg}(A)$ with a nice model structure whose fibrant objects are marked Segal $A$-categories and weak equivalences between fibrant objects are equivalences of marked Segal $A$-categories.

Definition 3.1.2.8. We define the stratified Segal $A$-precategory $[e, E^{eq}]^\sharp$ whose underlying Segal $A$-precategory is $[e, E^{eq}]$ and where every element of $ob([e, E^{eq}]_1)$ is marked.

We define the set of map $J$ as the reunion of the set of generating acyclic cofibration of $\mathrm{Seg}(A)$ and of $\{[e, 1]_t \to [e, E^{eq}]^\sharp\}$ and $\{[e, E^{eq}] \to [e, E^{eq}]^\sharp\}$. We suppose furthermore that $J$ includes the acyclic cofibrations $\{0\} \to [e, E^{eq}]$ and $\{1\} \to [e, E^{eq}]$.

105

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Lemma 3.1.2.9. A morphism \( f \) has the right lifting property against \( J \) if and only if \( f^{\sharp} \) is a fibration and \( f \) has the right lifting property against \( [e,1]_t \to [e,E^{eq}]^{\sharp} \) and \( [e,E^{eq}] \to [e,E^{eq}]^{\sharp} \). An object \( X \) has the right lifting property against \( J \) if and only if it is a marked Segal \( A \)-category.

Proof. Straightforward.

Lemma 3.1.2.10. Let \(i: K \to L\) be a cofibration that induces an isomorphism on objects. The morphism

\[
K \times [ e, E ^ {e q} ] \coprod_ {K \times [ e, 1 ]} L \times [ e, 1 ] \rightarrow L \times [ e, E ^ {e q} ]
\]

is an acyclic cofibration of the model structure on \(\operatorname{Seg}(A)\).

Proof. By two out of three, and some diagram chasing, is it sufficient to demonstrate the result for \( K \) being \( L_0 \). We then have to show that the square

\[
\begin{array}{c} L _ {0} \times [ e, 1 ] \longrightarrow L \times [ e, 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ L _ {0} \times [ e, E ^ {e q} ] \longrightarrow L \times [ e, E ^ {e q} ] \end{array}
\]

is homotopy coccartesian. As the model structure is cartesian, and as \([e,E^{eq}]\to 1\) is a weak equivalence, this is sufficient to show that the following square is homotopy cocartesian:

\[
\begin{array}{c} L _ {0} \times [ e, 1 ] \longrightarrow L \times [ e, 1 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ L _ {0} \longrightarrow L \end{array}
\]

As \(\_ \times [e,1]\) and \(\_ \times [e,E^{eq}]\) are left Quillen functors, we can reduce to the case where \(L\) is \([a,n]\) and using Segal extension, to the case where \(L\) is \([a,1]\). We then have to show that the following square is homotopy cocartesian

\[
\begin{array}{c} \left(\{0 \} \cup \{1 \}\right) \times [ e, 1 ] \longrightarrow [ a, 1 ] \times [ e, 1 ] \\ \Biggl \downarrow \quad \Biggl \downarrow \\ \{0 \} \cup \{1 \} \longrightarrow [ a, 1 ] \end{array} \tag {3.1.2.11}
\]

Remark then that  \( [a,1]\times[e,1] \)  is the colimit of the following span:

\[
[ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ]
\]

The pushout of the span of (3.1.2.11) is then the (homotopy) colimit of

\[
[ 0 ] \coprod_ {[ e, 1 ]} [ e, 1 ] \vee [ a, 1 ] \xleftarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \vee [ e, 1 ] \coprod_ {[ e, 1 ]} [ 0 ]
\]

By two out of three, and using Segal extensions, the two morphisms

\[
[ 0 ] \coprod_ {[ e, 1 ]} [ e, 1 ] \vee [ a, 1 ] \rightarrow [ a, 1 ] \quad \text { and } \quad [ a, 1 ] \vee [ e, 1 ] \coprod_ {[ e, 1 ]} [ 0 ] \rightarrow [ a, 1 ]
\]

induced by  \( [a,d^{0}] \)  and  \( [a,d^{2}] \)  are weak equivalences. In particular, this implies that the canonical morphism from the pushout of the span of (3.1.2.11) to  \( [a,1] \)  is a weak equivalence. As the upper horizontal vertical morphisms of (3.1.2.11) is a cofibration, this implies that this square is homotopy cocartesian which concludes the proof.

106

3.1. PRELIMINARIES

Lemma 3.1.2.12. Let $i: K \to L$ be a monomorphism and $f: X \to Y$ a morphism having the right lifting property against $J$. The induced morphism

$$f^i: X^L \to X^K \times_{Y^K} Y^L$$

has the right lifting property against $J$.

Proof. As the model structure on $\operatorname{Seg}(A)$ is cartesian, $(f^i)^\natural$ is a fibration. We then have to show that this morphism has the right lifting property against $[e, 1]_t \to [e, E^{eq}]^\natural$ and $[e, E^{eq}] \to [e, E^{eq}]^\natural$. We can reduce to the case where $i$ is a generating acyclic cofibration. If $i$ is $\emptyset \to [0]$, this is obvious. We then suppose that $i$ is $[e, 1] \to [e, 1]_t$ or $[a, \partial n] \cup [b, n] \to [b, n]$ for $a \to b$ a generating acyclic cofibration of $A$. In both case, $i$ induces an equivalence on objects. The morphism $i \hat{\times}([e, E^{eq}] \to [e, E^{eq}]^\natural)$ is then the identity. Moreover, $i \hat{\times}([e, 1]_t \to [e, E^{eq}]^\natural)$ fits in the following cocartesian square

$$\begin{array}{c} L^\natural \times [e, 1] \coprod_{K^\natural \times [e, 1]} K^\natural \times ([e, E^{eq}]) \longrightarrow L \times [e, 1]_t \coprod_{K \times [e, 1]_t} K \times [e, E^{eq}]^\natural \\ \downarrow \hspace{2em} \downarrow \\ L^\natural \times [e, E^{eq}] \longrightarrow L \times [e, E^{eq}]^\natural \end{array}$$

The lemma 3.1.2.10 implies $f$ has the right lifting property against the left vertical morphism, and so also against the right vertical one. By adjunction, this implies that $f^i$ has the desired lifting property. $\square$

Theorem 3.1.2.13. There exists a nice model structure on $\operatorname{tSeg}(A)$ where fibrant objects are stratified Segal $A$-categories and weak equivalences between marked Segal $A$-categories are stratified equivalences. The adjunction

$$(\_)^\flat: \operatorname{Seg}(A) \xrightarrow{\perp} \operatorname{tSeg}(A): (\_)^\natural$$

induces a Quillen equivalence.

A left adjoint from $\operatorname{tSeg}(A)$ to a nice model category $C$ is a left Quillen functor if and only if it preserves cofibrations and

(1) for any integer $n$, $[\_, n]: A \to C$ is a left Quillen functor,
(2) for any object $a$ of $A$, $[a, \_]: \operatorname{tPsh}(\Delta) \to C$ sends spine inclusions to weak equivalences,
(3) The morphism $[e, 1]_t \to [0]$ and $[e, E^{eq}] \to [0]$ are sent to weak equivalences.

Proof. We recall that we define $J$ as the union of the set of generating acyclic cofibrations of $\operatorname{Seg}(A)$ and of $\{[e, 1]_t \to [e, E^{eq}]^\natural\}$ and $\{[e, E^{eq}] \to [e, E^{eq}]^\natural\}$ and we suppose that it includes the trivial cofibrations $\{0\} \to [e, E^{eq}]$ and $\{1\} \to [e, E^{eq}]$. We denote by $I$ a cellular model for $\operatorname{Psh}(t\Delta[tB])$.

As $\operatorname{tSeg}(A)$ is the category of $t\Delta[M]$ stratified presheaves on $\Delta[B]$, we have an adjunction

$$\pi: \operatorname{Psh}(t\Delta[tB]) \xrightarrow{\perp} \operatorname{tSeg}(A): \iota$$

where the right adjoint is fully faithful.

The set $l(r(\iota(J)\hat{\times}I))$ is a class of anodyne extensions relative to the interval $\_ \times [e, E^{eq}]$ as defined in [Cis06, paragraph 1.3.12]. We then consider $\operatorname{Psh}(t\Delta[tB])$ endowed with the model structure induced by [Cis06, théorème 1.3.22]. An object is fibrant if and only if it has the right lifting property against $\iota(J)\hat{\times}I$. A morphism between fibrant objects is a fibration if and only if it has the right lifting property against $\iota(J)\hat{\times}I$.

107

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

According to proposition 2.1.2.8, this induces a model structure on tSeg(A). By adjunction and using lemma 3.1.2.12, an object is fibrant if and only if it has the right lifting property against J, and a morphism between fibrant objects is a fibration if and only if it has the right lifting property against J. According to lemma 3.1.2.9, the fibrant objects correspond to marked Segal A-categories.

Theorem 3.1.1.10 implies that the adjunction (3.1.2.2) is a Quillen adjunction. Its unit is the identity, and lemma 3.1.2.9 implies that the counit, computed on a fibrant object \((C,C^{\cong})\), is the canonical inclusion \((C,C^{\flat})\to (C,C^{\cong})\). As this morphism is a transfinite composite of \([e,E^{eq}]\to [e,E^{eq}]^{\sharp}\), it is a weak equivalence. The Quillen pair 3.1.2.9 is then a Quillen equivalence. As a consequence, the model structure on tSeg(A) is cartesian and simplicial, and weak equivalences between fibrant objects are stratified equivalences.

It then remains to prove the last assertion. Let \( F: \mathrm{tSeg}(A) \to C \) be a left adjoint that preserves monomorphism. Suppose first that \( F \) is a left Quillen functor. As \( [e,1]_t \to [0] \) is a weak equivalence, it is send to a weak equivalence of \( C \). The restricted functor \( F(\_)^b: \mathrm{Seg}(A) \to C \) is also a left Quillen functor. As all the remaining morphisms of the assertions (1), (2) and (3) are weak equivalences of \( \mathrm{Seg}(A) \), they are send to weak equivalences of \( C \).

Suppose now that \( F \) sends the morphisms of the assertion (1), (2), (3) to weak equivalences. In particular, this implies that the restriction to \( F \) to \( \operatorname{Seg}(A) \) is a left Quillen functor. Moreover, as we have a cocartesian square

![img-56.jpeg](img-56.jpeg)

the morphism \([e,E^{eq}]^{\sharp}\to [0]\) is send to a weak equivalence, and by 2 out of 3, so are the morphism \([e,1]_t\to [e,E^{eq}]^{\sharp}\) and \([e,E^{eq}]\to [e,E^{eq}]^{\sharp}\). The functor \(F\) then sends all the morphisms of \(J\) to acyclic cofibrations, and is then a left Quillen functor.

Definition 3.1.2.14. In this model structure, the morphism \([e,1]_t\to [0]\) is a weak equivalence. For any \(a\in A\) and \(n\in \mathbb{N}\), we define \([e,1]_t\vee [a,n]\) as the pushout:

![img-57.jpeg](img-57.jpeg)

The canonical morphism \([e,1]_t\cup [a,1]\cup \ldots \cup [a,1]\to [e,1]_t\vee [a,n]\) is then a weak equivalence. By two out of three, and using the weak equivalence \([e,1]_t\to [0]\), this implies that \([e,1]_t\vee [a,n]\to [a,n]\) is a weak equivalence.

We define similarly the object \([a,n]\vee [e,1]_t\) that comes along with a weak equivalence \([a,n]\vee [e,1]_t\to [a,n]\).

Proposition 3.1.2.15. Any stratified Segal \(A\)-precategory is a homotopy colimit of objects of shape \([a, n]\) or \([e, 1]_t\).

Proof. Let \( C \) be a stratified Segal \( A \)-precategory. We have \( C \cong \operatorname{colim}_{t\Delta [tB] / C} \). The result then follows from propositions 1.1.2.9, 2.1.2.6 and 3.1.1.7.

108

3.1. PRELIMINARIES

### 3.1.3 Models of $(\infty, n)$-categories

Notation 3.1.3.1. We denote by $\text{ho}(M)$ the homotopy category of a model category $M$.

Construction 3.1.3.2. Let $n \in \mathbb{N} \cup \{\omega\}$. We will consider the model structure on $\text{Psh}(\Theta_n \times \Delta)$ obtained as the left Bousfield localization of the injective model structure on $\text{Fun}(\Theta_n^{op}, \text{Psh}(\Delta)) \cong \text{Psh}(\Theta_n \times \Delta)$ along $\text{W}_n$ (definition 1.1.2.15) where $\text{Psh}(\Delta)$ is endowed with the Kan-Quillen model structure. This model structure is nice according to [Rez10].

Definition 3.1.3.3. Let $n \in \mathbb{N} \cup \{\omega\}$. A model of $(\infty, n)$-categories is a model category $M$ which is linked by a zigzag of Quillen equivalences to $\text{Psh}(\Theta_n \times \Delta)$.

A globular object for a model of $(\infty, n)$-categories $M$ is a functor $\mathbf{D}_-: \text{G}_{\le n} \to M$ such that $\text{G}_{\le n} \to \text{ho } M$ is equivalent to the inclusion of globes $\text{G}_{\le n} \to \Theta_n \to \text{ho } \text{Psh}(\Theta_n \times \Delta)$.

Proposition 3.1.3.4 (Barwick, Schommer-Pries). Let $M, N$ be two models of $(\infty, n)$-categories and $\mathbf{D}_-: \text{G}_{\le n} \to M$, $\mathbf{D}_-: \text{G}_{\le n} \to N$ be two globular objects.

Let $i: M \to N$ be a left Quillen functor that preserves the globes up to a zigzag of weak equivalences. Then $i$ is a Quillen equivalence.

Proof. This is [BSP21, proposition 15.10].

Theorem 3.1.3.5 (Bergner). Let $A$ be a category of stratified presheaves on a Reedy elegant category endowed with a nice model structure. If $A$ is a model of $(\infty, n)$-categories, then $\text{tSeg}(A)$ is a model of $(\infty, n+1)$-categories.

Proof. This is a direct consequence of [BSP21, example 15.8] using the Quillen equivalence between $\text{Seg}(A)$ and $\text{tSeg}(A)$ given in theorem 3.1.2.13.

### 3.1.4 Gray module

Definition 3.1.4.1. A family of intelligent $n$-truncations for $n \in \mathbb{N} \cup \{\omega\}$ for a model category $A$ is a family of left Quillen functors $\tau_i^\cdot: (\mathbb{N} \cup \{\omega\})^{op} \to \text{End}(A)$ such that

- $\tau_i^\omega = id$,
- for any $n \le m$, $\tau_i^n \tau_m^\cdot = \tau_n^\cdot$,
- for any $n \le m$, the natural transformation $\tau_m^\cdot \to \tau_n^\cdot$ is an entire monomorphism,

Definition 3.1.4.2. Let $A$ be a category of stratified presheaves on an elegant Reedy category, endowed with a nice model structure. We suppose furthermore that the terminal element of $A$, denoted by $e$, is representable.

A Gray module structure for the model category $A$ is the data of

- a family of intelligent $n$-truncation for any $n \in \mathbb{N} \cup \{\omega\}$.
- a left Quillen functor $_\otimes_-: \text{tPsh}(\Delta)^1 \times A \to A$,
- for any $a$ in $A$, and any pair of stratified simplicial sets $K, L$, a natural morphism $K \otimes (L \otimes a) \to (K \times L) \otimes a$.

such that

109

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

(1) for any stratified simplicial set $M$, the following square commutes

$$
\begin{array}{c} K \otimes (L \otimes (M \otimes a)) \longrightarrow (K \times L) \otimes (M \otimes a) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ K \otimes ((L \times M) \otimes a) \longrightarrow (K \times L \times M) \otimes a \end{array}
$$

(2) The functor $[0] \otimes \_ : A \to A$ is the identity.

(3) For any integer $n$, for any object $a$ such that $\tau_n^i(a) = a$ and for any stratified simplicial set $K$, we have $\tau_{n+1}^i(K \otimes a) = K \otimes a$.

Here, the model category $\mathrm{tPsh}(\Delta)^1$ corresponds to the model structure for 1-complicial sets on stratified simplicial sets given in theorem 2.2.1.8.

**Construction 3.1.4.3.** Let $A$ be a nice model category of stratified presheaves on an elegant Reedy category, endowed with intelligent $n$-truncation for $n \in \mathbb{N} \cup \{\omega\}$. We now construct a family of intelligent $n$-truncation for $n \in \mathbb{N} \cup \{\omega\}$ for $\mathrm{tSeg}(A)$.

Let $k$ be any non negative integer. The *intelligent $k$-truncation functor*, denoted by $\tau_k^i$, is the colimit-preserving functor such that $\tau_k^i([a, n]) = [\tau_{k-1}^i(a), n]$ and $\tau_k^i[e, 1]_t = [e, 1]_t$. The intelligent $0$-truncation functor, denoted by $\tau_0^i$, is the colimit-preserving functor such that $\tau_0^i([a, n])$ fits in the following pushout

$$
\begin{array}{c} \coprod_{ob(a) \times \mathrm{Hom}([1], [n])} [e, 1] \longrightarrow [\tau_0^i(a), n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \coprod_{ob(a) \times \mathrm{Hom}([1], [n])} [e, 1]_t \longrightarrow \tau_0^i([a, n]) \end{array}
$$

and such that $\tau_0^i[e, 1]_t = [e, 1]_t$. As the intelligent $k$-truncations on $A$ are left Quillen functors, the intelligent $k$-truncations on $\mathrm{tSeg}(A)$ preserve generating Reedy cofibrations and Segal extensions. It is straightforward that they also send $[e, 1]_t \to [0]$ and $E^{\cong} \to (E^{\cong})'$ to weak equivalences. According to theorem 3.1.2.13, they are left Quillen functors.

**Construction 3.1.4.4.** We consider the colimit-preserving functor

$$
\_ \otimes \_ : \mathrm{Psh}(\Delta) \times \mathrm{Seg}(A) \to \mathrm{Seg}(A)
$$

whose value on $([n], [a, m])$ fits in the pushout

$$
\begin{array}{c} \coprod_{l \leq m} \mathrm{colim}_{[k_0, k_1] \to [n] \otimes \{l\}} [[k_0] \otimes a, k_1] \longrightarrow \mathrm{colim}_{[k_0, k_1] \to [n] \otimes [m]} [[k_0] \otimes a, k_1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \coprod_{l \leq m} \mathrm{colim}_{[k_0, k_1] \to [n] \otimes \{l\}} [e, k_1] \longrightarrow [n] \otimes [a, m] \end{array}
$$

where $\_ \otimes \_ : (\infty, 1)$-cat $\times (\infty, 1)$-cat $\to (\infty, 2)$-cat is the Gray tensor product defined in theorem 1.2.4.1. We extend $\_ \otimes \_$ to a functor

$$
\_ \otimes \_ : \mathrm{tPsh}(\Delta) \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)
$$

110

3.1. PRELIMINARIES

by setting $[1]_t \otimes [a, m]$ as the colimit

$$\begin{array}{c} \coprod_{l \leq m} \operatorname{colim}_{[k_0, k_1] \to [1] \otimes \{l\}} [[k_0] \otimes a, k_1] \longrightarrow \operatorname{colim}_{[k_0, k_1] \to [1] \otimes [m]} [[k_0]^\sharp \otimes a, k_1] \\ \downarrow \hspace{2em} \scriptstyle{r} \quad \downarrow \\ \coprod_{l \leq m} \operatorname{colim}_{[k_0, k_1] \to [1] \otimes \{l\}} \tau_0^i[e, k_1] \longrightarrow [1]_t \otimes [a, m] \end{array}$$

and for any integer $k > 1$,

$$[k]_t \otimes [a, n] := [k] \otimes [a, n],$$

and eventually, for any stratified simplicial set $K$, by setting $K \otimes [e, 1]_t$ as the pushout

$$\begin{array}{c} \coprod_{c \in ob(K)} \tau_1^i(\{c\} \otimes [e, 1]) \longrightarrow \tau_1^i(K \otimes [e, 1]) \\ \downarrow \hspace{2em} \scriptstyle{r} \quad \downarrow \\ \coprod_{c \in ob(K)} \{c\} \otimes [e, 1]_t \longrightarrow K \otimes [e, 1]_t \end{array}$$

**Notation 3.1.4.5.** We will denote by $K_1 \otimes \ldots \otimes K_n \otimes C$ the object $(K_1 \otimes (\ldots \otimes (K_n \otimes C) \ldots))$

**Proposition 3.1.4.6.** *The functor $\otimes : \mathrm{tPsh}(\Delta)^1 \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ is a left Quillen functor.*

*Proof.* We first fix an object $[a, n]$ in $\operatorname{Seg}(A)$. The functor $\_ \otimes [a, \_] : \operatorname{Psh}(\Delta) \times \operatorname{Psh}(\Delta) \to \operatorname{Seg}(A)$ is the composite

$$\operatorname{Psh}(\Delta) \times \operatorname{Psh}(\Delta) \xrightarrow{\otimes} \operatorname{Psh}(\Theta_2) \xrightarrow{i^*} \operatorname{Psh}(\Delta[\Delta]) \cong \operatorname{Seg}(\operatorname{Psh}(\Delta)) \xrightarrow{\operatorname{Seg}(\_ \otimes a)} \operatorname{Seg}(A)$$

According to propositions 2.1.1.8 and 1.1.3.17 and theorem 1.2.5.3, this functor then sends $W_1 \times W_1$ to weak equivalence of $\operatorname{Seg}(A)$. We can show similarly that $\_ \otimes [e, 1]_t : \operatorname{Psh}(\Delta) \to \mathrm{tSeg}(A)$ and $[1]_t \otimes [a, \_] : \operatorname{Psh}(\Delta) \to \mathrm{tSeg}(A)$ sends $W_1$ to weak equivalences of $\operatorname{Seg}(A)$.

We now fix a marked simplicial set $K$ and an integer $n$. Let $i : a \to b$ be a weak equivalence of $A$. The morphism $K \otimes [a, n] \to K \otimes [b, n]$ is a colimit of natural transformations that is pointwise a weak equivalence. As this colimit is indexed by the elegant Reedy category $\Theta_{/K \otimes [n]}$ and verifies the condition of theorem 2.1.1.7, the morphism $K \otimes [i, n] : K \otimes [a, n] \to K \otimes [b, n]$ is a weak equivalence.

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

whose left vertical morphisms are weak equivalences. As weak equivalences are stable by pushouts along cofibrations and by composition, the canonical morphism $[1]_t \otimes [a, 1] \to [[1]_t \otimes a, 1]$ is a weak equivalence. As the canonical morphism $[1]_t \otimes [a, 1] \to [a, 1]$ is the composite of $[1]_t \otimes [a, 1] \to [[1]_t \otimes a, 1]$ with the weak equivalence $[[1]_t \otimes a, 1] \to [a, 1]$, it is a weak equivalence.

We proceed similarly to demonstrate that for all marked complicial sets $K$, $K \otimes [e, 1]_t \to K \otimes [0]$ is a weak equivalence.

The theorem 3.1.2.13 and the proposition 2.2.1.10 then imply that the functor $\otimes : \mathrm{tPsh}(\Delta)^1 \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ is a left Quillen functor.

**Construction 3.1.4.7.** Let $a$ be an object of $A$ and $l, m, n$ three integers. By construction, $[l] \otimes [m] \otimes [a, n]$ is a quotient of

$$P_{a,l,m,n} := \underset{[[k_0], k_1] \to [m] \otimes [n]}{\mathrm{colim}} \underset{[[k_2], k_3] \to [l] \otimes [k_1]}{\mathrm{colim}} [[k_2] \otimes [k_0] \otimes a, k_3]$$

while $([l] \times [m]) \otimes [a, n]$ is a quotient of

$$Q_{a,l,m,n} := \underset{[[k_4], k_3] \to ([l] \times [n]) \otimes [m]}{\mathrm{colim}} [[k_4] \otimes a, k_3].$$

Lemma 1.2.5.10 and the Gray module structure on $A$ then induce a morphism

$$P_{a,l,m,n} \to Q_{a,l,m,n}.$$

We can check that this morphism passes to the quotient and then induces a natural morphism

$$[l] \otimes [m] \otimes [a, n] \to ([l] \times [m]) \otimes [a, n].$$

By extension by colimit, this induces, for any Segal $A$-category $C$, and any pair of simplicial sets $K, L$, a morphism

$$K \otimes L \otimes C \to (K \times L) \otimes C.$$

Moreover, we can check that this natural transformation between $\_ \otimes \_ \otimes \_$ and $(\_ \times \_) \otimes \_$ extends to stratified simplicial sets and stratified Segal $A$-categories. Eventually, by construction and using the equality (1.2.5.12), we get a commutative square

$$\begin{array}{c} K \otimes L \otimes M \otimes C \longrightarrow (K \times L) \otimes M \otimes C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ K \otimes (L \times M) \otimes C \longrightarrow (K \times L \times M) \otimes C \end{array}$$

for any stratified Segal $A$-category $C$ and any stratified simplicial sets $K, L, M$.

**Theorem 3.1.4.8.** *A Gray module structure on $A$ induces a Gray module structure on $\mathrm{tSeg}(A)$. The family of intelligent truncations is defined in 3.1.4.3, and the tensoring by $\mathrm{tPsh}(\Delta)^1$ is defined in 3.1.4.4. The natural comparison maps between $K \otimes (L \otimes C)$ and $(K \times L) \otimes C$ are provided by the construction 3.1.4.7.*

*Proof.* The proposition 3.1.4.6 states that the functor $\_ \otimes \_$ constructed in 3.1.4.4 is a left Quillen functor. The first condition of the definition 3.1.4.2 follows from construction 3.1.4.7, and the two other are obviously fulfilled.

112

3.1. PRELIMINARIES

### 3.1.5 Complicial Gray module

Construction 3.1.5.1. Let $A$ be a Gray module and $a$ an object of $A$. We define $e \star a$ as the pushout:

$$\begin{array}{c} \{0\} \times a \longrightarrow [1] \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow e \star a \end{array}$$

We consider the natural transformations $s^0 \star a : e \star e \star a \to e \star a$ and $d^0 \star a : a \to e \star a$, induced respectively by the morphism

$$\begin{array}{rcl} [1] \otimes [1] \otimes a & \to & ([1] \times [1]) \otimes a \quad \to \quad [1] \otimes a \\ & & (\{i\} \times \{j\}) \otimes a \mapsto \{i \wedge j\} \otimes a. \end{array}$$

and the morphism

$$\{1\} \otimes a \to [1] \otimes a.$$

These natural transformations induce commutative diagrams:

$$\begin{array}{c} e \star e \star e \star a \xrightarrow{s^0 \star (e \star a)} e \star e \star a \\ e \star (s^0 \star a) \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star e \star a \xrightarrow{s^0 \star a} e \star a \end{array}$$

$$\begin{array}{c} e \star a \xrightarrow{e \star d^0} e \star e \star a \xrightarrow{d^0 \star (e \star a)} e \star a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ id \longrightarrow e \star a \xleftarrow{id} \end{array}$$

The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of $A$ and the natural transformation $s^0 : e \star e \star \_ \to e \star \_ \}}$ defines a structure of monoid for $e \star \_$. This induces a functor $\Delta \times A \to A$ sending $([n], a)$ to $e \star e \star \dots \star a$. We extend this to a functor $\Delta_t \times A \to A$ in defining $[n]_t \star a$ as the pushout:

$$\begin{array}{c} \coprod_{k \ge -1} \coprod_{b, \tau_k^i(b)=b} \coprod_{b \to a} [n] \star b \longrightarrow [n] \star a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{k \ge -1} \coprod_{b, \tau_k^i(b)=b} \coprod_{b \to a} \tau_{n+k}^i([n] \star b) \longrightarrow [n]_t \star a \end{array}$$

where $\tau_{-1}^i$ is the constant functor with value $\emptyset$.

By left Kan extension, this gives a colimit preserving functor

$$\operatorname{tPsh}(\Delta) \times \operatorname{tSeg}(A) \to \operatorname{tSeg}(A). \tag{3.1.5.2}$$

and evaluated on the empty Segal $A$-category, a colimit preserving functor

$$\operatorname{tPsh}(\Delta) \to \operatorname{tSeg}(A). \tag{3.1.5.3}$$

Definition 3.1.5.4. A Gray module $A$ is a complicial Gray module if

- (1) For any $a$, the morphisms $\Lambda^1[2] \star a \to [2]_t \star a$ and $\{\epsilon\} \star a \to [1]_t \star a$ with $\epsilon \in \{-, +\}$ are acyclic cofibrations.
- (2) The functor $\operatorname{tPsh}(\Delta)^\omega \to \operatorname{tSeg}(A)$ defined in (3.1.5.3) is a left Quillen functor where $\operatorname{tPsh}(\Delta)^\omega$ denotes the model structure for $\omega$-complicial sets given in theorem 2.2.1.8.

Remark 3.1.5.5. In general, $[n] \otimes e$ and $[n] \star \emptyset$ are two very different objects. Indeed $[n] \otimes e$ has to be invariant up to homotopy under $\tau_1^i$ which is not the case for $[n] \star \emptyset$. Analogously $[k] \otimes ([l] \otimes [a])$ and $([k] \otimes [l]) \otimes [a]$ have a priori no links.

113

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Notation 3.1.5.6. We will denote by \([n_0] \otimes [n_1] \otimes ..[n_k] \otimes a\) the object \([n_0] \otimes ([n_1] \otimes ..([n_k] \otimes a))\).

Example 3.1.5.7. For any \(d \in \mathbb{N} \cup \{\omega\}\), the model category \(\mathrm{tPsh}(\Delta)^d\), corresponding to the model structure for \(d\)-complicial sets on stratified simplicial sets, and where \(K \otimes L := \tau_1^i(K) \boxtimes L\), is an example of complicial Gray module.

Indeed, if \( n \) is any integer, we define \( [n]^{\diamond} := [0] \diamond [0] \diamond \ldots \diamond [0] \) and \( [n]_{l}^{\diamond} := \tau_{n}^{i}([n]^{\diamond}) \). This induces a colimit preserving functor \( K \mapsto K^{\diamond} \). The join coming from \( \tau_{1}^{i}(\_) \boxtimes \_ \) then corresponds to the functor \( (K, L) \mapsto K^{\diamond} \diamond L \). The proposition 2.2.2.13 provides a natural transformation \( K^{\diamond} \diamond L \to K \star L \), which implies that the first functor is left Quillen.

### 3.2 Complicial Gray module structure on  \( \operatorname{tSeg}(A) \)

The purpose of this section is to show that for any complicial Gray module \( A \), the Gray module structure on \( \mathrm{tSeg}(A) \) constructed in 3.1.4.8 is complicial. This is achieved in theorem 3.2.6.2.

We fix a complicial Gray module \(A\) until the end of this section.

#### 3.2.1 o-cone in tSeg(A)

To show that the Gray module  \( \operatorname{tSeg}(A) \)  is complicial, we need to demonstrate that the adjunction with marked simplicial sets constructed in 3.1.5.1 is a Quillen adjunction. This adjunction is constructed using an op-cone  \( e \star_{-} : \operatorname{tSeg}(A) \to \operatorname{tSeg}(A) \)  arising from the Gray module structure of  \( \operatorname{tSeg}(A) \) . However, for technical reasons, it will be useful to work with another op-cone that is constructed in 3.2.1.2. We have chosen to also denote this op-cone on  \( \operatorname{tSeg}(A) \)  by  \( e \star_{-} \) , as it is the only one we will use from now on.

Proposition 3.2.1.3 shows that these two op-cones are weakly equivalent, implying that the two adjunctions with stratified simplicial sets they induce are weakly equivalent.

Construction 3.2.1.1. We consider the colimit-preserving functor

\[
e \star_ {-}: \operatorname{Seg} (A) \to \operatorname{Seg} (A)
\]

whose value on \([a, m]\) fits in the pushout

\[
\begin{array}{c} \coprod_ {l \leq m} \operatorname{colim} _ {[ k _ {0}, k _ {1} ] \to 1 \star \{l \}} [ [ k _ {0} ] \otimes a, k _ {1} ] \longrightarrow \operatorname{colim} _ {[ k _ {0}, k _ {1} ] \to 1 \star [ m ]} [ [ k _ {0} ] \otimes a, k _ {1} ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_ {l \leq m} \operatorname{colim} _ {[ k _ {0}, k _ {1} ] \to 1 \star \{l \}} [ e, k _ {1} ] \xrightarrow {} e \star [ a, m ] \end{array}
\]

This functor is called the Gray o-cylinder, where  \( 1 \star_{-} : (\infty, 1) \) -cat  \( \rightarrow (\infty, 2) \) -cat denotes the Gray o-cone defined in 1.2.4.8. The morphism  \( d^{0} : [m] \to 1 \star [m] \)  induces a morphism

\[
d ^ {0} \star [ a, m ]: [ a, m ] \cong \underset {[ k _ {1} ] \to [ m ]} {\operatorname{colim}} [ a, k _ {1} ] \to e \star [ a, m ].
\]

By left Kan extension, this induces a transformation

\[
d ^ {0} \star C: C \to e \star C
\]

natural in \(C:\operatorname {Seg}(A)\)

114

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Construction 3.2.1.2. We extend $e \star \_$ as a functor

$$e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$$

by setting $e \star [e, 1]_t$ as the colimit

$$\begin{array}{c} [e, 1] \xrightarrow{d^0 \star [e, 1]} \tau_1^i(e \star [e, 1]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1]_t \longrightarrow e \star [e, 1]_t \end{array}$$

The natural transformation $d^0 \star \_$ extends to a transformation

$$d^0 \star C : C \to e \star C$$

natural in $C : \mathrm{tSeg}(A)$.

Proposition 3.2.1.3. For any stratified Segal $A$-precategory $X$, there exists a weak equivalence

$$\{0\} \coprod_{\{0\} \otimes X} [1] \otimes X \to e \star X$$

natural in $X$.

Proof. As the two functors $\{0\} \coprod_{\{0\} \otimes \_} [1] \otimes \_$ and $e \star \_$ are left Quillen functors, it is sufficient to construct this comparison when $C$ is of shape $[a, n]$ or $[e, 1]_t$. In this case, the canonical morphism $[1] \otimes [n] \to 1 \star [n]$ of $(0, \omega)$-categories induces comparison morphisms

$$[1] \otimes [a, n] \to e \star [a, n] \quad [1] \otimes [e, 1]_t \to e \star [e, 1]_t$$

that respectively send $\{0\} \otimes [a, n]$ and $\{0\} \otimes [e, 1]_t$ to $e \star \emptyset$. The two previous morphisms then induce natural morphisms

$$\{0\} \coprod_{\{0\} \otimes [a, n]} [1] \otimes [a, n] \to e \star [a, n] \qquad \{0\} \coprod_{\{0\} \otimes [e, 1]_t} [1] \otimes [e, 1]_t \to e \star [e, 1]_t$$

Now, remark that these two morphisms fit in the following cocartesian squares:

$$\begin{array}{c} \operatorname{colim}_{[k_0], k_1] \to \{0\} \coprod_{\{0\} \otimes [n]} [1] \otimes [n]} [[k_0] \otimes a, k_1] \longrightarrow e \coprod_{\{0\} \otimes [a, n]} [1] \otimes [a, n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{colim}_{[k_0], k_1] \to 1 \star [n]} [[k_0] \otimes a, k_1] \longrightarrow e \star [a, n] \\ \operatorname{colim}_{[k_0], k_1] \to \{0\} \coprod_{\{0\} \otimes [1]} [1] \otimes [1]} [[k_0] \otimes a, k_1] \longrightarrow e \coprod_{\{0\} \otimes [a, n]} [1] \otimes [e, 1]_t \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{colim}_{[k_0], k_1] \to 1 \star [1]} [[k_0] \otimes a, k_1] \longrightarrow e \star [e, 1]_t \end{array}$$

We claim that the functor whose value on a $\Theta_2$-set $X$ is $\operatorname{colim}_{[k_0], k_1] \to X} [[k_0] \otimes a, k_1]$ sends $\overline{\mathrm{W}_2}$ to weak equivalences. Combined with proposition 1.2.5.23, it will conclude the proof.

To show the desired claim, remark that this functor is the composite

$$\operatorname{Psh}(\Theta_2) \xrightarrow{1^*} \operatorname{Psh}(\Delta[\Delta]) \cong \operatorname{Seg}(\operatorname{Psh}(\Delta)) \xrightarrow{\operatorname{Seg}(\_ \otimes a)} \operatorname{Seg}(A)$$

and the results follow from propositions 1.1.3.17 and 2.1.1.8.

115

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

**Proposition 3.2.1.4.** *The functor $e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ is a left Quillen functor.*

*Proof.* The proposition 3.2.1.3 implies that $e \star \_$ is pointwise weakly equivalent to the functor $\{0\} \coprod_{\{0\} \otimes \_} [1] \otimes \_$. As this last functor is a homotopy colimit of functors preserving weak equivalence, the functor $e \star \_$ also preserves them. As $e \star \_$ also preserves cofibrations, this concludes the proof. $\square$

**Construction 3.2.1.5.** Let $a$ be an object of $A$ and $l, m$ two integers. By construction, $e \star e[a, m]$ is a quotient of

$$P_{a,l,m} := \underset{[k_0,k_1] \to 1 \star [m]}{\operatorname{colim}} \underset{[k_2,k_3] \to [l] \otimes [k_1]}{\operatorname{colim}} [[k_2] \otimes [k_0] \otimes a, k_3]$$

while $e \star [a, m]$ is a quotient of

$$Q_{a,l,m} := \underset{[k_4,k_3] \to 1 \star [m]}{\operatorname{colim}} [[k_4] \otimes a, k_3].$$

Lemma 1.2.5.20 and the Gray module structure on $A$ then induce a morphism

$$P_{a,l,m} \to Q_{a,l,m}.$$

We can check that this morphism passes to the quotient and then induces a natural morphism

$$s^0 \star [a, n] : e \star e \star [a, n] \to e \star [a, n].$$

By extension by colimit, this induces, for any Segal $A$-category $C$, a morphism

$$s^0 \star C : e \star e \star C \to e \star C.$$

We can moreover check that this natural transformation between $e \star e \star \_$ and $e \star \_$ extends to stratified Segal $A$-categories. Finally, by construction and using the equality (1.2.5.21), we get a commutative square

$$\begin{array}{c} e \star e \star e \star C \xrightarrow{s^0 \star e \star C} e \star e \star C \\ e \star s^0 \star C \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star e \star C \xrightarrow{s^0 \star C} e \star C \end{array}$$

for any stratified Segal $A$-category $C$.

**Proposition 3.2.1.6.** *The stratified Segal $A$-precategory $e \star [a, 1]$ is the colimit of the diagram*

$$[e \star a, 1] \xleftarrow{[d^0 \star a, 1]} [a, 1] \xrightarrow{[a, d^1]} [e, 1] \vee [a, 1]$$

*and the stratified Segal $A$-precategory $e \star [e, 1]_t$ is the colimit of the diagram*

$$[[1]_t, 1] \xleftarrow{[d^0 \star e, 1]} [e, 1] \xrightarrow{[e, d^1]} [e, 1] \vee [e, 1]_t$$

*Proof.* We recall that $e \star a$ is the object of $A$ fitting in the following cocartesian square

$$\begin{array}{c} \{0\} \otimes a \longrightarrow [1] \otimes a \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \longrightarrow e \star a \end{array}$$

The results then directly follow from the construction of the functor $e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ and from proposition 1.2.5.17. $\square$

116

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Remark 3.2.1.7. The last proposition can be seen as an analogue in stratified simplicial sets of the third formula of theorem 1.2.4.14.

Proposition 3.2.1.8. The stratified Segal A-precategory $e \star [a, 2]$ is the colimit of the diagram

$$\begin{array}{c} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^0 \otimes a, 1]} [e \star a, 1] \xrightarrow{[[1] \otimes a, d^1]} [e \star a, 1] \vee [a, 1] \xleftarrow{[d^0 \otimes a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^1]} [e, 1] \vee [a, 2] \end{array}$$

where $[2] \bar{\otimes} a$ and $[e \star a, 1] \vee [a, 1]$ are the pushouts:

$$\begin{array}{ccc} [1] \otimes a \amalg [1] \otimes a & \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a & [[1] \otimes a, 1] \amalg [[1] \otimes a, 2] \xrightarrow{[[1] \otimes a, d^2 \amalg d^1]} [[1] \otimes a, 2] \\ \downarrow & \downarrow & \downarrow \\ e \star a \amalg e \star a & \xrightarrow{d^1 \bar{\otimes} a \amalg d^2 \bar{\otimes} a} [2] \bar{\otimes} a & [e \star a, 1] \amalg [a, 1] \longrightarrow [e \star a, 1] \vee [a, 1] \end{array}$$

Proof. The result directly follows from the construction of the functor $e \star \_ : \text{tSeg}(A) \to \text{tSeg}(A)$ and of proposition 1.2.5.19.

Proposition 3.2.1.9. The stratified Segal A-precategory $e \star e \star [a, 1]$ is the colimit of the diagram

$$\begin{array}{ccc} [[2] \bar{\otimes} a, 1] \xleftarrow{[d^0 \otimes a, 1]} [[1] \otimes a, 1] \xrightarrow{[[1] \otimes a, d^1]} [[1], 1] \vee [a, 1] \xleftarrow{[d^0 \otimes a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^1]} [e, 2] \vee [a, 1] \\ [d^1 \bar{\otimes} a, 1] \uparrow & [a, d^1] \uparrow & \uparrow [a, d^2] \\ [e \star a, 1] \xleftarrow{[d^0 \star a, 1]} [a, 1] \xrightarrow{[a, d^1]} [e, 1] \vee [a, 1] \\ [d^1 \star a, 1] \downarrow & [d^0 \star a, 1] \downarrow & \downarrow [d^0 \star a, 2] \\ [[1] \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \vee [e \star a, 1] \end{array}$$

where $[2] \bar{\otimes} a$ and $[[1], 1] \vee [a, 1]$ are the pushouts:

$$\begin{array}{ccc} [1] \otimes a \amalg [1] \otimes a & \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a & [[1] \otimes a, 1] \amalg [[1] \otimes a, 2] \xrightarrow{[[1] \otimes a, d^2 \amalg d^1]} [[1] \otimes a, 2] \\ \downarrow & \downarrow & \downarrow \\ e \star a \amalg e \star a & \xrightarrow{d^1 \bar{\otimes} a \amalg d^2 \bar{\otimes} a} [2] \bar{\otimes} a & [[1], 1] \amalg [a, 1] \longrightarrow [[1], 1] \vee [a, 1] \end{array}$$

Proof. The proposition 3.2.1.8 implies that the Segal A-precategory $e \star ([e, 1] \vee [a, 1])$ is the colimit of the diagram

$$[[2] \bar{\otimes} a, 1] \xleftarrow{[d^0 \otimes a, 1]} [[1] \otimes a, 1] \xrightarrow{[[1] \otimes a, d^1]} [[1], 1] \vee [a, 1] \xleftarrow{[d^0 \otimes a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^1]} [e, 2] \vee [a, 1]$$

The fact that $e \star e \star [a, 1]$ is the colimit of the given diagram then follows from the explicit expression of $e \star [\_a, 1]$ as a colimit given in proposition 3.2.1.6.

### 3.2.2 Adjunction with tPsh($\Delta$)

Construction 3.2.2.1. The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of tSeg(A). The construction 3.2.1.5 shows that $e \star \_$ is a monoid for this monoidal structure. This induces a cosimplicial object:

$$\begin{array}{rcl} \Delta & \to & \text{End}(\text{tSeg}(A)) \\ [n] & \mapsto & [n] \star \_ := \underbrace{e \star e \star \dots \star e}_{n+1} \star \_ \end{array}$$

117

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

We extend this functor to \(\Delta_t\) by setting, for a stratified Segal \(A\)-precategory \(C\) and an integer \(n > 0\):

\[
\begin{array}{c} \coprod_ {k \geq - 1} \coprod_ {D, \tau_ {k} ^ {i} (D) = D} \coprod_ {D \to C} [ n ] \star D \longrightarrow [ n ] \star C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_ {k \geq - 1} \coprod_ {D, \tau_ {k} ^ {i} (D) = D} \coprod_ {D \to C} \tau_ {n + k} ^ {i} ([ n ] \star D) \longrightarrow [ n ] _ {t} \star C \end{array}
\]

where \(\tau_{-1}^{i}\) is the constant functor with value \(\emptyset\). By left Kan extension, this gives a colimit preserving functor

\[
\mathrm{tPsh} (\Delta) \times \mathrm{tSeg} (A) \rightarrow \mathrm{tSeg} (A). \tag {3.2.2.2}
\]

and evaluated on the empty Segal \(A\)-category, a colimit preserving functor

\[
\mathrm{tPsh} (\Delta) \rightarrow \mathrm{tSeg} (A). \tag {3.2.2.3}
\]

The image of \(([n],\emptyset)\) (resp. \(([n]_t,\emptyset)) is noted as \([n]\) (resp. \([n]_t\)).

By construction, for \( K, L \) two stratified sets and \( D \) a stratified Segal \( A \)-precategory, we have \( K \star (L \star C) \cong (K \star L) \star C \).

Remark 3.2.2.4. We now have two functors from stratified simplicial sets to stratified Segal A-precategories. The one constructed in 3.2.1.1, and the one coming from the Gray module structure of tSeg(A) and constructed in 3.1.5.1. Moreover, Proposition 3.2.1.3 induces a weakly invertible natural transformation between them.

Both are denoted in the same way, but this should not create confusion because we will only consider the one constructed in 3.2.1.1.

Proposition 3.2.2.5. Let \( K \) be a stratified simplicial set. The morphism \( K \star_{-} \) is a left Quillen functor. Moreover, if \( i \) is a cofibration of stratified simplicial sets and \( g \) an acyclic cofibration of stratified Segal \( A \)-precategories, the morphism \( i \star g \) is an acyclic cofibration.

Proof. Since \(\star\) preserves monomorphisms, the functor \(\_ \star \_ : \Delta_{/K} \to \operatorname{End}(\mathrm{tSeg}(A))\) is Reedy cofibrant. The theorem 2.1.1.7 then implies that it is sufficient to show that for any integer \(n\), \([n] \star \_\) is a left Quillen functor. In this case, this is a repeated application of proposition 3.2.1.4. By diagram chasing and the use of two out of three, this implies the second assertion.

#### 3.2.3 Complicial horn inclusions

Notation. In this section, we will often consider morphisms  \( \tilde{a} \rightarrow \tilde{b} \)  that fit into cocartesian squares:

![img-58.jpeg](img-58.jpeg)

where \( a \to \tilde{a} \) and \( b \to \tilde{b} \) are epimorphisms. To avoid complicating the notations unnecessarily, the induced morphism \( \tilde{a} \to \tilde{b} \) will just be denoted \( i \).

118

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Definition 3.2.3.1. A marked Segal A-precategory is a stratified Segal A-precategory having the right lifting property against all entire acyclic cofibrations. We denote by mSeg(A) the full subcategory of marked Segal A-precategory. We then have an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tSeg}(A) \xrightleftharpoons{\perp} \mathrm{mSeg}(A) : \iota$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified Segal A-precategory $(C, tC)$ to the marked Segal A-precategory $(C, \overline{tC})$, where $\overline{tC}$ is the smaller stratification that includes $tC$ and makes $(C, \overline{tC})$ a marked Segal A-precategory, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of preshaves, these two adjoints are the identity. We denote by $r_C : C \to C_{\mathrm{mk}}$ the canonical inclusion. The proposition 2.1.2.11 states that $r_C$ is an entire acyclic cofibration.

There is an isomorphism $(e \star C_{\mathrm{mk}})_{\mathrm{mk}} \cong (e \star C)_{\mathrm{mk}}$. Indeed $e \star \_$ preserves both entire cofibrations and weak equivalences, we have two entire acyclic cofibration $e \star C \to (e \star C)_{\mathrm{mk}}$ and $e \star C \to (e \star C_{\mathrm{mk}})_{\mathrm{mk}}$. As the two codomain are marked, they are isomorphic.

The fact that will be used the most with the marked Segal A-precategory is their right lifting property with respect to morphisms of shape $[\tau_n^i(a), \Lambda^1[2]] \cup [a, 2] \to [\tau_n^i(a), 2]$. This fact will be used freely.

We recall that $[2] \otimes a$ is the following pushout:

$$\begin{array}{c} [1] \otimes a \amalg [1] \otimes a \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star a \amalg e \star a \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a \end{array}$$

Definition 3.2.3.2. We define $[e, 1] \vee (e \star [a, 1])$ as the colimit of the following diagram

$$[e, 1] \vee [e \star a, 1] \xleftarrow{[d^0 \star a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^2]} [e, 2] \vee [a, 1]$$

The canonical composite morphism

$$[e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \vee [e \star a, 1] \to [e, 1] \vee (e \star [a, 1])$$

is also denoted by $[e \star a, d^1]$. Eventually, we define $[\overline{[1] \star [a, 1]}$ as the following pushout

$$\begin{array}{c} [1] \star \{0\} \longrightarrow [1] \star [a, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [2]_t \longrightarrow \overline{[1] \star [a, 1]} \end{array}$$

Lemma 3.2.3.3. There is a weak equivalence from $[\overline{[1] \star [a, 1]}$ to the colimit of the diagram

$$[[1] \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \vee (e \star [a, 1])$$

making $[\overline{[1] \star [a, 1]}$ the homotopy colimit of the previous diagram.

119

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. The proposition 3.2.1.9 implies that \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) is the colimit of the diagram

\[
\begin{array}{c} \left[ [ 2 ] ^ {2} \bar {\otimes} a, 1 \right] \xleftarrow {[ d ^ {0} \otimes a , 1 ]} \left[ [ 1 ] _ {t} \otimes a, 1 \right] \xrightarrow {[ [ 1 ] \otimes a , d ^ {1} ]} \left[ [ 1 ] _ {t}, 1 \right] \vee [ a, 1 ] \xleftarrow {[ d ^ {0} \otimes a , 2 ]} [ e, 1 ] \vee [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 2 ] \vee [ a, 1 ] \\ [ d ^ {1} \bar {\otimes} a, 1 ] \uparrow \\ [ e \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ d ^ {0} \star a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 1 ] \vee [ a, 1 ] \\ [ d ^ {1} \star a, 1 ] \downarrow \\ [ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ d ^ {0} \star a, 1 ] \downarrow \\ [ e \star a, 1 ] \xrightarrow [ [ e \star a , d ^ {1} ] ]{} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.2.3.4}
\]

In the previous diagram, the fact that we have \([ [1]_t \otimes a, 1]\) instead of \([ [1] \otimes a, 1]\) comes from the fact that we have considered \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) instead of \(\overline{[1] \star [a, 1]}\).

Consider now the morphism

\[
[ [ 2 ] ^ {2} \bar {\otimes} a, 1 ] \coprod_ {[ [ 1 ] _ {t} \otimes a, 1 ]} [ [ 1 ] _ {t}, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 1 ] \tag {3.2.3.5}
\]

induces by the vertical colimit of the diagram

\[
\begin{array}{c} \left[ [ 2 ] ^ {2} \bar {\otimes} a, 1 \right] \xleftarrow {[ d ^ {0} \otimes a , 1 ]} \left[ [ 1 ] _ {t} \otimes a, 1 \right] \xrightarrow {[ [ 1 ] \otimes a , d ^ {1} ]} \left[ [ 1 ] _ {t}, 1 \right] \vee [ a, 1 ] \\ \left[ s ^ {0} \bar {\otimes} a, 1 \right] \Bigg \downarrow \quad \Bigg \downarrow \left[ s ^ {0} \otimes a, 1 \right] \quad \Bigg \downarrow \left[ s ^ {0}, 1 \right] \vee [ a, 1 ] \\ [ e \star a, 1 ] \xleftarrow {} [ a, 1 ] \longrightarrow [ e, 1 ] \vee [ a, 1 ] \end{array} \tag {3.2.3.6}
\]

As all the horizontal morphisms of (3.2.3.6) are cofibrations, the colimit of each line is a homotopy colimit. As all the vertical morphisms of (3.2.3.6) are weak equivalences, the morphism (3.2.3.5) also is a weak equivalence.

Consider now the span

\[
e \star [ a, 1 ] \xleftarrow {(3 . 2 . 3 . 5)} [ [ 2 ] ^ {2} \bar {\otimes} a, 1 ] \coprod_ {[ [ 1 ] _ {t} \otimes a, 1 ]} [ [ 1 ] _ {t}, 1 ] \vee [ a, 1 ] \rightarrow (\overline {{[ 1 ] \star [ a , 1 ]}}) _ {\mathrm{mk}} \tag {3.2.3.7}
\]

As the right hand morphism is a cofibration, and as (3.2.3.5) is a weak equivalence, the canonical morphism from \((\overline{[1] \star [a, 1]})_{\mathrm{mk}}\) to the colimit of (3.2.3.7) is a weak equivalence. Using the diagram (3.2.3.4), the colimit of (3.2.3.7) is also the colimit of the following diagram

\[
\begin{array}{c} e \star [ a, 1 ] \xleftarrow {} [ e, 1 ] \vee [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 2 ] \vee [ a, 1 ] \\ \uparrow \quad \text {   } \quad [ a, d ^ {1} ] \uparrow \quad \uparrow [ a, d ^ {2} ] \\ [ e \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ a, 1 ] \xrightarrow {[ a , d ^ {1} ]} [ e, 1 ] \vee [ a, 1 ] \\ [ d ^ {1} \star a, 1 ] \downarrow \quad [ d ^ {0} \star a, 1 ] \downarrow \quad \downarrow [ d ^ {0} \star a, 2 ] \\ [ [ 1 ] \star a, 1 ] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow [ [ e \star a , d ^ {1} ] ]{} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.2.3.8}
\]

As the upper left square is cocartesian, the colimit of the diagram 3.2.3.8 is equivalent to the colimit of the diagram

\[
\begin{array}{c} \left[ e, 2 \right] \vee [ a, 1 ] \\ \uparrow [ a, d ^ {2} ] \\ \left[ e, 1 \right] \vee [ a, 1 ] \\ \downarrow [ d ^ {0} \star a, 2 ] \\ \left[ [ 1 ] \star a, 1 \right] \xleftarrow {[ d ^ {0} \star a , 1 ]} [ e \star a, 1 ] \xrightarrow [ [ e \star a , d ^ {1} ] ]{} [ e, 1 ] \vee [ e \star a, 1 ] \end{array} \tag {3.2.3.9}
\]

120

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

As the proposition 3.2.1.6 implies that the colimit of the the diagram 3.2.3.9 is equivalent to the one of the diagram given in the statement, this concludes the proof. □

**Lemma 3.2.3.10.** *The morphism*

$$[e, 1] \vee (e \star [a, 1]) \cup e \star [e \star a, 1] \rightarrow [e, 1] \vee (e \star [e \star a, 1])$$

*is a weak equivalence.*

*Proof.* We have a cocartesian square

$$\begin{array}{c} [e, 1] \cup e \star [a, 1] \xrightarrow{[e, 1] \cup e \star [d^0 \star a, 1]} [e, 1] \cup e \star [e \star a, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \vee (e \star [a, 1]) \longrightarrow [e, 1] \vee (e \star [a, 1]) \cup e \star [e \star a, 1] \end{array} \tag{3.2.3.11}$$

Remark that the left vertical morphism is the vertical colimit and homotopy colimit of the diagram

$$\begin{array}{c} [e, 1] \cup [e \star a, 1] \longleftarrow [e, 1] \cup [a, 1] \longrightarrow [e, 1] \cup [e, 1] \vee [a, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \vee [e \star a, 1] \longleftarrow [e, 1] \vee [a, 1] \longrightarrow [e, 2] \vee [a, 1] \end{array}$$

and is then a weak equivalence. This implies that the right vertical morphism of (3.2.3.11) is a weak equivalence. Similarly, $[e, 1] \cup e \star [e \star a, 1] \rightarrow [e, 1] \vee (e \star [e \star a, 1])$ is a weak equivalence. By two out of three this concludes the proof. □

**Lemma 3.2.3.12.** *The morphism $\{1\} \star [0] \rightarrow [1]_t \star [0]$ is an acyclic cofibration.*

*Proof.* Using proposition 3.2.1.6 we deduce that $[1]_t \star [0]$ is the colimit of the diagram

$$[[1]_t, 1] \longleftarrow [e, 1] \longrightarrow [e, 1]_t \vee [e, 1]$$

The inclusion $\{1\} \star [0] \rightarrow [1]_t \star [0]$ is then the composite of the following sequence

$$\begin{array}{c} [e, 1] \xrightarrow{[d^0, 1]} [[1]_t, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \xrightarrow{[e, d^0]} [e, 1]_t \vee [e, 1] \longrightarrow [1]_t \star [0] \end{array}$$

As the morphism $[e, d^0]$ and $[d^0, 1]$ are acyclic cofibrations, this concludes the proof. □

**Lemma 3.2.3.13.** *The morphism $\{1\} \star [a, 1] \rightarrow [1]_t \star [a, 1]$ is an acyclic cofibration.*

*Proof.* The Segal $A$-precategory $[1]_t \star [a, 1]$ is the colimit and the homotopy colimit of the diagram

$$\begin{array}{c} [1] \star \emptyset \\ \downarrow \\ [1]_t \star \emptyset \end{array} \xrightarrow{\quad} \begin{array}{c} [[1] \star a, 1] \\ \downarrow \\ [1] \star [a, 1] \end{array} \xleftarrow{\quad} \begin{array}{c} [[1]_t \star a, 1] \\ \downarrow \\ [[1]_t \star a, 1] \end{array}$$

The lemma 3.2.3.3 then implies that we have a weak equivalence from $[1]_t \star [a, 1]$ to the colimit, denoted by $K$, of the diagram

$$[[1]_t \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1]_t \vee (e \star [a, 1])$$

121

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

As the left hand morphism is a weak acyclic cofibration, so is the canonical morphism

\[
[ e, 1 ] _ {t} \vee (e \star [ a, 1 ]) \rightarrow K.
\]

We then have a commutative square

![img-59.jpeg](img-59.jpeg)

where the two horizontal morphisms and the right vertical morphism are weak equivalences. The result the follows by two out of three.

Lemma 3.2.3.14. The morphism \(\Lambda^1 [2]\star [0]\to [2]_t\star [0]\) is an acyclic cofibration.

Proof. The Segal \(A\)-precategory \([2]_t \star [0]\) is the colimit of the following diagram

\[
[ [ 2 ] _ {t}, 1 ] \longleftarrow [ [ 2 ], 1 ] \longrightarrow \overline {{[ 1 ] \star [ 1 ]}}
\]

The lemma 3.2.3.3 then implies that we have a weak equivalence from \([2]_t \star [0]\) to the colimit, denoted by \(K\), of the diagram

\[
[ [ 2 ] _ {t}, 1 ] \xleftarrow {[ d ^ {0} , 1 ]} [ [ 1 ], 1 ] \xrightarrow {[ [ 1 ] , d ^ {1} ]} [ e, 1 ] \vee (e \star [ e, 1 ])
\]

On the other side, \(\Lambda^1 [2]\star [0]\) is the colimit of the diagram

![img-60.jpeg](img-60.jpeg)

The composite \(\Lambda^1 [2]\star [0]\to [2]_t\star [0]\to K\) fits in the sequence of acyclic cofibrations

![img-61.jpeg](img-61.jpeg)

and is then a weak equivalence. By two out of three, this concludes the proof.

Lemma 3.2.3.15. The morphism \(\Lambda^1 [2]\star [a,1]\to [2]_t\star [a,1]\) is an acyclic cofibration.

Proof. The lemma 3.2.3.14 implies that the inclusion \(\Lambda^1 [2]\star [a,1]\to \Lambda^1 [2]\star [a,1]\cup [2]_t\star \{0\}\) is an acyclic cofibration. Using proposition 3.2.1.6, we deduce that the Segal \(A\) -precategory \([2]_t\star [a,1]\) is the colimit of the diagram

![img-62.jpeg](img-62.jpeg)

122

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

while $\Lambda^1[2] \star [a, 1] \cup [2]_t \star \{0\}$ is the colimit of the diagram

![img-63.jpeg](img-63.jpeg)

where $\overline{[1] \star [e, 1]} := [2]_t \star [0]$ and where $\overline{[1] \star [e \star a, 1]}$ is the following pushout:

![img-64.jpeg](img-64.jpeg)

Let $K_1$ be the following pushout:

![img-65.jpeg](img-65.jpeg)

The left-hand morphism is equal to $(d^0 : [0] \to [1]) \star ([e, 1] \cup [a, 1] \to [e, 1] \lor [a, 1])$ which is an acyclic cofibration according to proposition 3.2.2.5. Furthermore, the morphism $K_1 \to [2]_t \star [a, 1]$ fits in the following pushout:

![img-66.jpeg](img-66.jpeg)

To conclude, we will prove that the left vertical morphism is a weak equivalence.

The lemma 3.2.3.3 implies that we have a weak equivalence from $[1] \star [a, 1] \cup \{1\} \star [e \star a, 1]$ to the colimit, denoted by $K_2$, of the diagram

$$[[1] \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \lor (e \star [a, 1]) \cup \{1\} \star [e \star a, 1]$$

We now define $K_3$ as the colimit of the diagram

$$[\Lambda^1[2] \star a, 1] \xleftarrow{[d^0 \star a, 1]} [[1] \star a, 1] \xrightarrow{[[1] \star a, d^1]} [e, 1] \lor (e \star [e \star a, 1])$$

The canonical morphism $K_2 \to K_3$ fits in the cocartesian square

![img-67.jpeg](img-67.jpeg)

and is then a weak equivalence according to the lemma 3.2.3.10.

On the other side, the lemma 3.2.3.3 also implies that we have a weak equivalence from $[1] \star [e \star a, 1]$ to the colimit, denoted by $K_4$, of the diagram

$$[[2]_t \star a, 1] \xleftarrow{[d^0 \star a, 1]} [[1] \star a, 1] \xrightarrow{[[1] \star a, d^1]} [e, 1] \lor (e \star [e \star a, 1])$$

123

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Remark now that all the morphisms appearing in the diagrams that define \( K_{3} \) and \( K_{4} \) are cofibrations. As \( \Lambda^1 [2] \star a \to [2]_t \star a \) is a weak equivalence in \( A \), this implies that the canonical morphism \( K_{3} \to K_{4} \) is also a weak equivalence. We then have commutative diagram:

![img-68.jpeg](img-68.jpeg)

where all arrows labelled by  \( \sim \)  are weak equivalences. By two out of three, this implies the result.

Proposition 3.2.3.16. For any stratified Segal \(A\)-precategory \(C\), the morphisms \(\Lambda^1[2] \star C \to [2]_t \star C\) and \(\{\epsilon\} \star C \to [1]_t \star C\) with \(\epsilon \in \{0,1\}\) are acyclic cofibrations. Moreover, for any cofibration of stratified Segal \(A\)-precategory \(i\), and \(j\) being either \(\{1\} \to [1]_t\) or \(\Lambda^1[2] \to [2]_t\), the morphism \(j \hat{\star} i\) is an acyclic cofibration.

Proof. We begin with the first assertion. By two out of three, we can suppose that \(\epsilon := 1\). The proposition 3.2.2.5 implies that \(\Lambda^1[2] \star_{-}\) and \([2]_t \star_{-}\) are left Quillen functors. As every object is a homotopy colimit of objects of shape \([a, n]\) or \([e, 1]_t\), we can reduce to the case where \(C\) is of this shape. Using Segal extensions, we can reduce to the case where \(C\) is \([a, 1]\), \([0]\) or \([e, 1]_t\).

If \( C \) is \([a,1]\) or \([0]\), the result follows from lemmas 3.2.3.12, 3.2.3.13, 3.2.3.14 and 3.2.3.15. Eventually, for \( C := [e,1]_t \), we have a diagram:

![img-69.jpeg](img-69.jpeg)

![img-70.jpeg](img-70.jpeg)

The proposition 3.2.2.5 and the lemmas 3.2.3.12 and 3.2.3.14 imply that all horizontal morphisms and right vertical morphisms are weak equivalences. By two out of three, this implies that the left vertical morphisms are weak equivalences.

This concludes the proof of the first assertion. The second one is obtained with some diagram chasing.

Proposition 3.2.3.17. The functor \(\mathrm{tPsh}(\Delta) \to \mathrm{tSeg}(A)\) sends complicial horn inclusions to weak equivalences.

Proof. Let \( k \leq n \) be two integers. First, we suppose that \( 0 < k < n \). We then have an equality

\[
(\Lambda^ {k} [ n ] \to [ n ] ^ {k}) = (\partial [ k - 2 ] \to [ k - 2 ]) \hat {\star} (\Lambda^ {1} [ 2 ] \to [ 2 ] _ {t}) \hat {\star} (\partial [ n - k - 2 ] \to [ n - k - 2 ]).
\]

This is an acyclic cofibration according to propositions 3.2.2.5 and 3.2.3.16. If \( k = 0 \), we have an equality

\[
(\Lambda^ {0} [ n ] \to [ n ] ^ {0}) = (\{1 \} \to [ e, 1 ] _ {t}) \hat {\star} (\partial [ n - 2 ] \to [ n - 2 ])
\]

and the right hand morphism is an acyclic cofibration again thanks to proposition 3.2.3.16. Eventually, for \( k = n \), note that

\[
(\Lambda^ {n} [ n ] \to [ n ] ^ {n}) = (\partial [ n - 2 ] \to [ n - 2 ]) \hat {\star} (\{0 \} \to [ e, 1 ] _ {t}).
\]

This morphism is an acyclic cofibration according to proposition 3.2.2.5.

124

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

### 3.2.4 Complicial thinness extensions

Notation. In this section, we will often consider morphisms $\tilde{a} \to \tilde{b}$ that fit into cocartesian squares:

$$\begin{array}{c} a \xrightarrow {i} b \\ \Big \downarrow \quad \Big \downarrow \\ \tilde {a} \longrightarrow \tilde {b} \end{array}$$

where $a \to \tilde{a}$ and $b \to \tilde{b}$ are epimorphisms. To avoid complicating the notations unnecessarily, the induced morphism $\tilde{a} \to \tilde{b}$ will just be denoted $i$.

Lemma 3.2.4.1. Morphisms $([n]^{0})' \to ([n]^{0})''$ and $([n]^{n})' \to ([n]^{n})''$ are acyclic cofibrations.

Proof. For $k$ equal to 0 or $n$, we have pushout diagrams:

$$\begin{array}{c} [ n ] ^ {k} \longrightarrow ([ n ] ^ {k}) ^ {\prime} \longrightarrow ([ n ] ^ {k}) ^ {\prime \prime} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ n - 1 ] \longrightarrow [ n - 1 ] _ {t} \xrightarrow [ i d ]{} [ n - 1 ] _ {t} \end{array}$$

Propositions 3.2.2.5 and 3.2.3.16 imply that both $s^0 : [n]^0 \to [n-1]$ and $s^{n-1} : [n]^{n-1} \to [n-1]$ are weak equivalences. As horizontal morphisms are cofibrations, the left properness imply that all the vertical morphisms are weak equivalences. By two out of three, this shows that $([n]^k)' \to ([n]^k)''$ is a weak equivalence.

Construction 3.2.4.2. The propositions 3.2.1.6 and 3.2.1.8 provide canonical morphisms:

$$\begin{array}{l} \alpha_ {a}: [ e \star a, 1 ] \rightarrow e \star [ a, 1 ] \quad \beta_ {a}: [ e, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 1 ] \\ \delta_ {a}: [ e \star a, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 2 ] \quad \epsilon_ {a}: [ [ 2 ] \bar {\otimes} a, 1 ] \rightarrow e \star [ a, 2 ] \end{array}$$

where $[2] \bar{\otimes} a$ and $[e \star a, 1] \vee [a, 1]$ are the following pushouts:

$$\begin{array}{c} [ 1 ] \otimes a \amalg [ 1 ] \otimes a \xrightarrow {d ^ {1} \otimes a \amalg d ^ {2} \otimes a} [ 2 ] \otimes a \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star a \amalg e \star a \xrightarrow [ d ^ {1} \bar {\otimes} a \amalg d ^ {2} \bar {\otimes} a ]{} [ 2 ] \bar {\otimes} a \end{array}$$

$$\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \amalg [ [ 1 ] \otimes a, 1 ] ^ {[ [ 1 ] \otimes a, d ^ {2} \amalg d ^ {0} ]} [ [ 1 ] \otimes a, 2 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \amalg [ a, 1 ] \longrightarrow [ e \star a, 1 ] \vee [ a, 1 ] \end{array}$$

Moreover they fit in the following commutative diagram:

$$\begin{array}{l} [ a, 1 ] \xrightarrow [ d ^ {0} \star [ a , 1 ] ]{\left[ a , d ^ {0} \right]} [ e, 1 ] \vee [ a, 1 ] \\ \Biggl \downarrow \beta_ {a} \\ e \star [ a, 1 ] \end{array}$$

$$\begin{array}{c} [ a, 1 ] \xrightarrow {\left[ d ^ {0} \star a , 1 \right]} [ e \star a, 1 ] \\ [ a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e, 1 ] \vee [ a, 1 ] \xrightarrow {\beta_ {a}} e \star [ a, 1 ] \end{array} \tag {2}$$

$$\begin{array}{l} [ e \star a, 1 ] \xrightarrow [ e \star [ a , d ^ {2} ] ]{\left[ e \star a, 1 \right]} [ e \star a, 1 ] \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {2} ] ]{\alpha_ {a}} e \star [ a, 2 ] \end{array} \tag {3}$$

$$\begin{array}{c} [ e \star a, 1 ] \xrightarrow [ e \star [ a , d ^ {1} ] ]{\left[ d ^ {1} \bar {\otimes} a, 1 \right]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {1} ] ]{\epsilon_ {a}} e \star [ a, 2 ] \end{array} \tag {4}$$

$$\begin{array}{l} [ [ 1 ] \otimes a, 1 ] \xrightarrow [ d ^ {0} \otimes a, 1 ]{\left[ d ^ {0} \otimes a, 1 \right]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ [ [ 1 ] \otimes a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \vee [ a, 1 ] \xrightarrow [ \delta_ {a} ]{} e \star [ a, 2 ] \end{array} \tag {5}$$

$$\begin{array}{c} [ e \star a, 1 ] \xrightarrow [ d ^ {2} \bar {\otimes} a, 1 ]{\left[ d ^ {2} \bar {\otimes} a, 1 \right]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {0} ] ]{} e \star [ a, 2 ] \end{array} \tag {6}$$

125

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Definition 3.2.4.3. Let \( b \) be an object of \( A \) and \( x: a \to b \), \( x': a' \to b \) two morphisms. The element \( b \) is \( n \)-relying on \( x \) if for any \( k \geq -1 \), the following square is homotopy cocartesian:

![img-71.jpeg](img-71.jpeg)

The element \( b \) is \( n \)-relying on \( x \) and \( x' \) if for any \( k \geq -1 \), the following square is homotopy cocartesian:

![img-72.jpeg](img-72.jpeg)

Remark 3.2.4.4. We recall that we denote by \( C_{\mathrm{mk}} \) the marked Segal \( A \)-precategory associated to a stratified Segal \( A \)-precategory \( C \). The canonical inclusion \( C \to C_{\mathrm{mk}} \) is denoted \( r_C \) and is an acyclic cofibration according to the proposition 2.1.2.11. These notions and notations are defined in definition 3.2.3.1. The fact that will be used the most with the marked Segal \( A \)-precategory is their right lifting property with respect to morphisms of shape \( [\tau_n^i (a),\Lambda^1 [2]]\cup [a,2]\to [\tau_n^i (a),2] \). This fact will be used freely.

Definition 3.2.4.5. Let \( C \) be a Segal \( A \)-precategory. We define the relation \( \geq_{n} \) on morphisms of shape \( [a,1] \to C \) for \( a \) verifying \( \tau_{n}^{i}a = a \), as the smallest reflexive and transitive relation such that \( (x:[a,1] \to C) \geq_{n}(x':[a',1] \to C) \) whenever one of the three following conditions is verified:

(1) The elements \( a \) and \( a' \) are equal and there exists a lifting the following diagram:

![img-73.jpeg](img-73.jpeg)

(2) The elements \( a \) and \( a' \) are equal and there exists a lifting in the following diagram:

![img-74.jpeg](img-74.jpeg)

(3) There exists an element \( b \) which is \( (n - 1) \)-relying on \( a \to b \) and dotted arrows in the following

126

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

diagram:

![img-75.jpeg](img-75.jpeg)

Definition 3.2.4.6. We also set $$(\bar{x} : [\bar{a}, 1] \to C, \bar{x}' : [\bar{a}', 1] \to C) \geq_n \bar{x}'' : [\bar{a}'', 1] \to C$$ if there exists three elements $$x : [a, 1] \to C$$, $$x' : [a', 1] \to C$$ and $$x'' : [a'', 1] \to C$$ such that $$\bar{x} \geq_n x$$, $$\bar{x}' \geq_n x'$$, $$x'' \geq_n \bar{x}''$$ and one of the two following conditions is verified:

(1) The elements $$a$$, $$a'$$ and $$a''$$ are equal and there exists a dotted arrow:

![img-76.jpeg](img-76.jpeg)

(2) There exists an element $$b$$ which is $$(n - 1)$$-relying on $$a \to b$$ and $$a' \to b$$ and dotted arrows in the following diagram:

![img-77.jpeg](img-77.jpeg)

Proposition 3.2.4.7. Let $$C$$ be a stratified Segal $$A$$-precategory and $$x : [a, 1] \to C$$, $$y : [a', 1] \to C$$ two morphisms such that $$x \geq_n y$$. The morphism

$$C \coprod_{[a,1]} \tau_n^i([a,1]) \to \tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1])$$

is an acyclic cofibration.

Proof. By two out of three, we can suppose without loss of generality that $$C$$ is already a marked Segal $$A$$-precategory. We suppose first that $$x$$ and $$y$$ fulfill one of the three cases of definition 3.2.4.5. The following square is then homotopy cartesian:

![img-78.jpeg](img-78.jpeg)

As the cocartesian square:

![img-79.jpeg](img-79.jpeg)

127

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

is also homotopy cocartesian, this implies that

$$C \coprod_{[a,1]} \tau_n^i([a,1]) \to \tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1])$$

is an acyclic cofibration. Suppose now that there exists a family of morphisms $(x_k : [a_k, 1])_{k \le m} \to C$ such that $x_0 = x$, $x_m = y$ and for any $k$, $x_k$ and $x_{k+1}$ fulfill one of the three cases of definition 3.2.4.5. We then have two homotopy cocartesian squares:

$$\begin{array}{ccc} C \coprod_{[a',1]} \tau_n^i[a',1] & \longleftrightarrow & [a,1] \longrightarrow C \\ \downarrow & & \downarrow \\ C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1] & \longleftrightarrow & \tau_n^i[a,1] \longrightarrow C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1] \end{array}$$

As before, this implies that

$$C \coprod_{[a,1]} \tau_n^i([a,1]) \to C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1]$$

and

$$\tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1]) \to C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1]$$

are acyclic cofibrations. By two out of three, this implies the result.

One can show similarly:

**Proposition 3.2.4.8.** Let $C$ be a stratified Segal $A$-precategory, and $x : [a,1] \to C$, $y : [a',1] \to C$ and $z : [a'',1] \to C$ three morphisms such that $(x,y) \ge_n z$. The morphism

$$\tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1]) \to \tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1]) \coprod_{[a'',1]} \tau_n^i([a'',1])$$

is an acyclic cofibration.

**Lemma 3.2.4.9.** Let $n$ be a non null integer and $a$ an element such that $\tau_n^i(a) = a$. The object $[2]^2 \otimes a$ is $n$-relying on $d^1 \bar{\otimes} a : e \star a \to [2]^2 \bar{\otimes} a$.

*Proof.* As the morphism $d^1 \bar{\otimes} a : e \star a \to [2]^2 \bar{\otimes} a$ is a weak equivalence, so are the horizontal morphisms of the following diagram:

$$\begin{array}{ccc} [k] \star e \star a & \xrightarrow{\sim} & [k] \star ([2]^2 \bar{\otimes} a) \\ \downarrow & & \downarrow \\ \tau_{n+k+1}^i([k] \star e \star a) & \xrightarrow{\sim} & \tau_{n+k+1}^i([k] \star ([2]^2 \bar{\otimes} a)) \end{array}$$

As the vertical morphisms are cofibrations, this implies that this square is homotopy cocartesian.

**Lemma 3.2.4.10.** Let $n$ be a non null integer and $a$ an element such that $\tau_n^i(a) = a$. The object $[2] \bar{\otimes} a$ is $n$-relying on $d^0 \otimes a : [1] \otimes a \to [2] \bar{\otimes} a$ and $d^2 \otimes a : e \star a \to [2] \otimes a$. Moreover, $[2] \bar{\otimes} a \coprod_{d^0 \otimes a} \tau_n^i([1] \otimes a)$ (resp. $[2] \bar{\otimes} a \coprod_{d^2 \bar{\otimes} a} \tau_n^i(e \star a)$) is $n$-relying on $d^2 \otimes a$ (resp. $d^0 \bar{\otimes} a$).

128

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Proof. Consider the following diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star (\Lambda^ {1} [ 2 ] \otimes a) \xrightarrow {\sim} [ k ] \star ([ 2 ] \otimes a) \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star (\Lambda^ {1} [ 2 ] \otimes a)) \xrightarrow {\sim} \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \end{array}$$

The left square is cocartesian and so homotopy cocartesian. Horizontal morphisms of the right square are weak equivalences, so this square is also homotopy cocartesian. The outer square is then homotopy cocartesian and this implies that $[ [2] \otimes a, 1 ]$ is $n$-relying on $d^0 \otimes a$ and $d^2 \otimes a$. We then have a diagram:

$$\begin{array}{c} [ k ] \star ([ 1 ] \otimes a) \amalg [ k ] \star ([ 1 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \otimes a) \xrightarrow {} [ k ] \star ([ 2 ] \bar {\otimes} a) \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \amalg \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 1 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \otimes a)) \to \tau_ {n + k + 1} ^ {i} ([ k ] \star ([ 2 ] \bar {\otimes} a)) \end{array}$$

where the two squares are homotopy cocartesian and so is the outer one. This implies the first assertion and the two others follow easily.

Lemma 3.2.4.11. Let $n$ be an integer strictly superior to 1 and $a$ such that $\tau_n^i(a) = a$. We consider the projection $\pi : [a, 2] \to [a, 1] \vee [\tau_{n-1}^i(a), 1]$ and $\pi' : [a, 2] \to [\tau_{n-1}^i(a), 1] \vee [a, 1]$. We then have inequalities

$$e \star \pi \circ \epsilon_ {a} \circ [ d ^ {0} \otimes a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ]$$

and

$$e \star \pi^ {\prime} \circ \epsilon_ {a} \circ [ d ^ {2} \bar {\otimes} a, 1 ] \geq_ {n + 1} e \star \pi \circ \epsilon_ {a} \circ [ d ^ {1} \bar {\otimes} a, 1 ].$$

Proof. Using the diagram (6).3.2.4.2 we get a diagram

$$\begin{array}{c} [ e \star a, 1 ] \xrightarrow {[ d ^ {2} \bar {\otimes} a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ \tau_ {n} ^ {i} (e \star a), 1 ] \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {0} ] ]{} e \star [ a, 2 ] \\ e \star [ \tau_ {n - 1} ^ {i} (a), 1 ] \longrightarrow e \star ([ a, 1 ] \vee [ \tau_ {n - 1} ^ {i} (a), 1 ]) \end{array}$$

The morphism $r_{e\star([a,1]\vee[\tau_{n-1}^i(a),1])}\circ e\star\pi\circ\epsilon_a$ then factors through $[ [2]\bar{\otimes}a\coprod_{d^2\bar{\otimes}a}\tau_n^i(e\star a),1]$. According to lemma 3.2.4.10, we then get the first inequalities.

For the second inequality, using the diagrams (3).3.2.4.2 and (5).3.2.4.2, we have a diagram:

$$\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \xrightarrow {[ d ^ {0} \otimes a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ [ [ 1 ] \otimes a, d ^ {1} ] \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \vee [ a, 1 ] \xrightarrow {\delta_ {a}} e \star [ a, 2 ] \\ [ e \star a, d ^ {2} ] \xrightarrow {\alpha_ {a}} e \star [ a, 1 ] \xrightarrow {e \star [ a , d ^ {2} ]} e \star ([ \tau_ {n - 1} ^ {i} (a), 1 ] \vee [ a, 1 ]) \\ [ \tau_ {n} ^ {i} (e \star a), 1 ] \xrightarrow [ \alpha_ {\tau_ {n - 1} ^ {i} (a)} ]{} e \star [ \tau_ {n - 1} ^ {i} (a), 1 ] \end{array}$$

129

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

This implies that \( r_{e\star([\tau_{n-1}^i(a),1]\vee [a,1])}\circ e\star \pi' \circ e\star [a,d^2]\circ \alpha_a \) factors through \( [\tau_n^i (e\star a),1] \). The morphism \( r_{e\star ([\tau_{n-1}^i(a),1]\vee [a,1])}\circ e\star \pi \circ \epsilon_a \) then factors through \( [[2]\otimes a\coprod_{d^0\otimes a}\tau_n^i ([1]\otimes a),1] \). According to lemma 3.2.4.10, we then get the second inequality.

Lemma 3.2.4.12. Let \( n \) be an integer strictly superior to 1 and \( a \) such that \( \tau_n^i(a) = a \). We then have \( \delta_a \circ [e \star a, d^2] \geq_{n+1} \delta_a \circ [[1] \otimes a, d^1] \).

Proof. There is a diagram:

\[
\begin{array}{c} [ e \star a, 1 ] \xrightarrow {i d} [ e \star a, 1 ] \xleftarrow {} [ [ 1 ] \otimes a, 1 ] \\ \Big \downarrow [ e \star a, d ^ {2} ] \qquad \qquad \qquad \Big \downarrow [ [ 1 ] \otimes a, d ^ {2} ] \\ e \star [ a, 2 ] \xleftarrow [ \delta_ {a} ] {\delta_ {a}} [ e \star a, 1 ] \vee [ a, 1 ] \xleftarrow {} [ [ 1 ] \otimes a, 1 ] \vee [ a, 1 ] \\ \Big \uparrow [ [ 1 ] \otimes a, d ^ {1} ] \qquad \qquad \qquad \Big \uparrow [ [ 1 ] \otimes a, d ^ {1} ] \\ [ [ 1 ] \otimes a, 1 ] \xleftarrow [ i d ] {i d} [ [ 1 ] \otimes a, 1 ] \end{array}
\]

As the morphism \([ [1] \otimes a, 1] \vee [a, 1] \to [e \star a, 1] \vee [a, 1]\) factors through \([ [1] \otimes a, 1] \vee [\tau_n^i ([1] \otimes a), 1]\), we get the desired inequality.

Proposition 3.2.4.13. Let \( a \) be an object such that \( \tau_n^i(a) = a \). Let \( x: [a,1] \to C, y: [a',1] \to C \) be two morphisms, such that \( x \geq_n y \), then if we denote by \( \bar{x} := e \star x \circ \alpha_a \) and \( \bar{y} := e \star y \circ \alpha_{a'} \), we have \( \bar{x} \geq_{n+1} \bar{y} \).

Proof. First, we suppose that we are in the first case of the definition 3.2.4.5. We can then suppose without loss of generality that \( C = [a,1] \vee [\tau_{n-1}^i(a),1] \). We denote by \( \pi \) the projection of \( [a,2] \) on \( [a,1] \vee [\tau_{n-1}^i(a),1] \). Using the diagrams (3).3.2.4.2, (4).3.2.4.2 and (5).3.2.4.2, we have a diagram:

\[
\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \xrightarrow {[ d ^ {0} \otimes a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \xleftarrow {[ d ^ {1} \bar {\otimes} a , 1 ]} [ e \star a, 1 ] \\ [ [ 1 ] \otimes a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \Big \downarrow \epsilon_ {a} \qquad \qquad \qquad \Big \downarrow \alpha_ {a} \\ [ e \star a, 1 ] \vee [ a, 1 ] \xrightarrow {\delta_ {a}} e \star [ a, 2 ] \xleftarrow {e \star [ a , d ^ {1} ]} e \star [ a, 1 ] \\ [ e \star a, d ^ {2} ] \Big \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \xrightarrow {\alpha_ {a}} e \star [ a, 1 ] \qquad \qquad \qquad e \star ([ a, 1 ] \vee [ \tau_ {n - 1} ^ {i} (a), 1 ]) \end{array}
\]

Thanks to lemmas 3.2.4.11 and 3.2.4.12, this implies the result.

If we are in the second case of 3.2.4.5, we can suppose that \( C = [\tau_{n-1}^i(a), 1] \vee [a, 1] \), and we note by \( \pi' \) the projection from \( [a, 2] \to [\tau_{n-1}^i(a), 1] \vee [a, 1] \). Using the diagrams (4).3.2.4.2 and (6).3.2.4.2, we have a diagram:

\[
\begin{array}{c} [ e \star a, 1 ] \xrightarrow {[ d ^ {2} \bar {\otimes} a , 1 ]} [ [ 2 ] \bar {\otimes} a, 1 ] \xleftarrow {[ d ^ {1} \bar {\otimes} a , 1 ]} [ e \star a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {0} ] ]{} e \star [ a, 2 ] \xleftarrow [ e \star [ a , d ^ {1} ] ]{} e \star [ a, 1 ] \\ \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star ([ \tau_ {n - 1} ^ {i} (a), 1 ] \vee [ a, 1 ]) \end{array}
\]

Thanks to lemmas 3.2.4.11, this implies the result.

If we are in the third case, it is a direct consequence of the naturality of \(\alpha\), of the definition of \(n\)-reliability and of the fact that \((e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}}\) as remarked in 3.2.3.1.

130

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Proposition 3.2.4.14. Let $x : [a, 1] \to C$, $y : [a', 1] \to C$ and $z : [a'', 1]$ be three morphisms, such that $(x, y) \geq_n z$, then if we denote by $\bar{x} := e \star x \circ \alpha_a$, $\bar{y} := e \star y \circ \alpha_{a'}$ and $\bar{z} := e \star z \circ \alpha_{a''}$, we have $(\bar{x}, \bar{y}) \geq_{n+1} \bar{z}$.

Proof. Suppose first that we are in the first case of the definition 3.2.4.6. We can then suppose without loss of generality that $C = [a, 2]$. We define $\tilde{x} := \epsilon_a \circ [d^0 \otimes a, 1]$. Diagram (6).3.2.4.2 and lemma 3.2.4.11 imply that $(\tilde{x}, \tilde{y}) \geq_{n+1} \tilde{z}$. Eventually, diagrams (3).3.2.4.2 and (5).3.2.4.2 induce a diagram:

$$\begin{array}{c} [e \star a, 1] \xrightarrow{[e \star a, d^2]} [e \star a, 1] \vee [a, 1] \xleftarrow{[[1] \otimes a, d^1]} [[1] \otimes a, 1] \\ \alpha_a \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [a, 1] \xrightarrow[e \star [a, d^2]] \quad e \star [a, 2] \xleftarrow{\epsilon_a} \quad [[2] \bar{\otimes} a, 1] \end{array}$$

which implies that $\bar{x} \geq_{n+1} \tilde{x}$.

If we are in the second case of the definition, it is a direct consequence of the naturality of $\alpha$, of the definition of $n$-reliability and of the fact that $(e \star C)_{\mathrm{mk}} \cong (e \star C_{\mathrm{mk}})_{\mathrm{mk}}$ as remarked in definition 3.2.3.1. $\square$

Lemma 3.2.4.15. For any $a$ such that $\tau_n^i a = a$ and $x : [a, 1] \to C$, if we denote by $\bar{x} := e \star x \circ d^0 \star [a, 1]$ and $\tilde{x} := e \star x \circ \alpha_a \circ [d^0 \star a, 1]$, then $\bar{x} \geq_{n+1} \tilde{x}$.

Proof. Using the diagrams (1).3.2.4.2 and (2).3.2.4.2, we have a diagram:

$$\begin{array}{c} [a, 1] \xrightarrow{[d^0 \star a, 1]} [e \star a, 1] \\ [a, d^1] \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1] \vee [a, 1] \xrightarrow{\beta_a} e \star [a, 1] \xrightarrow{e \star x} C \\ [a, d^0] \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [a, 1] \end{array}$$

which implies the desired inequality. $\square$

We now use these results to show that the thinness extensions are weak equivalences.

Definition 3.2.4.16. We define by induction on $n \geq 2$ the morphism $\iota_n : [[n-1], 1] \to [n]$ where $\iota_2 := \alpha_{[0]}$ and $\iota_{n+1} := e \star \iota_n \circ \alpha_{[n-1]}$.

We can easily show by induction that $[n]$ is a colimit of terms which are all invariant under $\tau_{n-1}^i$ except the one corresponding to $\iota_n$. For any $n$ we then have a pushout square:

$$\begin{array}{c} [[n-1], 1] \xrightarrow{\iota_n} [n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [[n-1]_t, 1] \xrightarrow{r} [n]_t \end{array}$$

Lemma 3.2.4.17. For any $n$ and for any $k < n$, such that $k \neq n-2$, we have inequalities $d^k \circ \iota_{n-1} \geq_{n-1} \iota_n \circ [d^k, 1]$ and $(d^n \circ \iota_{n-1}, d^{n-2} \circ \iota_{n-1}) \geq_{n-1} \iota_n \circ [d^{n-2}, 1]$

131

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. We start by showing the first inequality by induction on \( n \). If \( n = 2 \), the only case is \( k = 1 \), and the two morphisms are equal.

Suppose now the result true at the stage \( n \). If \( k > 0 \), we have

\[
\begin{array}{l} d ^ {k} \circ \iota_ {n} = e \star d ^ {k - 1} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]} \\ \geq_ {n} e \star \iota_ {n} \circ e \star [ d ^ {k - 1}, 1 ] \circ \alpha_ {[ n - 2 ]} \quad (\text { induction   hypothesis   and   3.2.4.13 }) \\ = e \star \iota_ {n} \circ \alpha_ {[ n - 1 ]} \circ [ e \star d ^ {k - 1}, 1 ] \\ = \iota_ {n + 1} \circ \alpha_ {[ n - 1 ]} \circ [ d ^ {k}, 1 ] \\ \end{array}
\]

We still have to deal with the case \( k = 0 \). As \( d^0: [n] \to [n + 1] \) (resp \( [d^0, 1]: [[n - 1], 1] \to [[n], 1] \)) is equal to \( d^0 \star [n] \) (resp. \( [d^0 \star [n - 1], 1] \)), this is exactly the content of lemma 3.2.4.15.

For the second inequality, we proceed again by induction. We remark that this is true for \( n = 2 \). Suppose now the result true at the stage \( n \). We have

\[
\begin{array}{l} \left(d ^ {n + 1} \circ \iota_ {n}, d ^ {n - 1} \iota_ {n}\right) = \left(e \star d ^ {n} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]}, e \star d ^ {n - 2} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]}\right) \\ \geq_ {n - 1} e \star \iota_ {n} \circ e \star [ d ^ {n - 2}, 1 ] \circ \alpha_ {[ n - 2 ]} \quad (\text { induction   hypothesis   and   3.2.4.14 }) \\ = e \star \iota_ {n} \circ e \star \alpha_ {[ n - 1 ]} \circ [ e \star d ^ {n - 2}, 1 ] \\ = \iota_ {n + 1} \circ [ d ^ {n - 1}, 1 ] \\ \end{array}
\]

Lemma 3.2.4.18. Let \(0 < k < n\) be two integers. We denote by \(\tau^k\) the projection \([n] \to [n]^k\). We then have

\[
\tau^ {k} \circ \iota_ {n} \circ [ d ^ {k}, 1 ] \geq_ {n - 1} \tau^ {k} \circ d ^ {k} \circ \iota_ {n - 1}.
\]

Proof. We demonstrate the result by induction on \( n \). For the initialization, the only case is \( n = 2 \) and \( k = 1 \), and is obvious. Suppose now the result true at the stage \( n \), and let \( k > 1 \). We have inequalities:

\[
\begin{array}{l} \tau^ {k} \circ \iota_ {n + 1} \circ [ d ^ {k}, 1 ] = e \star \tau^ {k} \circ e \star \iota_ {n} \circ \alpha_ {[ n - 1 ]} \circ [ d ^ {k}, 1 ] \\ = e \star \tau^ {k} \circ e \star \iota_ {n} \circ e \star [ d ^ {k - 1}, 1 ] \circ \alpha_ {[ n - 2 ]} \\ \geq_ {n} e \star \tau_ {k} \circ e \star d ^ {k - 1} \circ e \star \iota_ {n - 1} \circ \alpha_ {[ n - 2 ]} \quad (\text { induction   hypothesis   and   3.2.4.13 }) \\ = \tau_ {k} \circ d ^ {k} \circ \iota_ {n} \\ \end{array}
\]

We still have to deal with the case \( k = 1 \). Using diagrams (1), (2), (4) and (5), of construction 3.2.4.2, we get a diagram:

\[
\begin{array}{l} [ [ n - 1 ], 1 ] \xrightarrow {\alpha_ {[ n - 2 ]}} e \star [ [ n - 2 ], 1 ] \xrightarrow {e \star \iota_ {n - 1}} [ n ] \\ [ d ^ {2} \otimes [ n - 2 ], 1 ] \Bigg \downarrow \qquad \qquad \qquad \Bigg \downarrow e \star [ [ n - 1 ], d ^ {0} ] \qquad \qquad \Bigg \downarrow d ^ {1} \\ [ [ 2 ] \bar {\otimes} [ n - 2 ], 1 ] \xrightarrow {e \star \pi \circ e _ {[ n - 2 ]}} e \star ([ e, 1 ] \vee [ [ n - 2 ], 1 ]) \xrightarrow {e \star \beta_ {[ n - 1 ]}} [ n + 1 ] \xrightarrow {\tau^ {1}} [ n + 1 ] ^ {1} \\ [ d ^ {1} \bar {\otimes} [ n - 2 ], 1 ] \uparrow \qquad \qquad \qquad \uparrow e \star [ [ n - 1 ], d ^ {1} ] \qquad \qquad \uparrow e \star \iota_ {n} \\ [ [ n - 1 ], 1 ] \xrightarrow {\alpha_ {[ n - 2 ]}} e \star [ [ n - 2 ], 1 ] \xrightarrow [ e \star [ d ^ {0} , 1 ] ]{} e \star [ [ n - 1 ], 1 ] \\ \end{array}
\]

where \(\pi\) is the projection \([n - 2], 2] \to [e, 1] \vee [n - 2], 1\). However, according to the diagrams (5) and (3)

132

3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

of 3.2.4.2, there is a diagram:

$$\begin{array}{c} [[1] \otimes [n-2], 1] \xrightarrow{[1] \otimes [n-2], d^1} [e \star [n-2], 1] \vee [[n-2], 1] \xrightarrow{e \star [n-2], d^2} [e \star [n-2], 1] \\ [d^0 \otimes [n-2], 1] \downarrow \qquad \qquad \qquad \downarrow \delta_{[n-2]} \qquad \qquad \qquad \downarrow \alpha_{[n-2]} \\ [[2] \bar{\otimes} [n-2], 1] \xrightarrow{\epsilon_{[n-2]}} [[n-2], 2] \xleftarrow{} e \star [[n-2], 1] \\ \qquad \qquad \qquad \qquad \qquad \downarrow e \star \pi \qquad \qquad \qquad \downarrow \\ e \star ([e, 1] \vee [[n-2], 1]) \xleftarrow{} e \star [e, 1] \\ \tau_1 \circ e \star \beta_{[n-1]} \downarrow \qquad \qquad \qquad \downarrow \\ [n+1]^1 \xleftarrow{d^3 \circ \dots \circ d^{n+1}} [2]_t \end{array}$$

This implies that $[[2] \bar{\otimes} [n-2], 1] \to [n+1]^k \to ([n+1]^k)_{\mathrm{mk}}$ factors through $[[2] \bar{\otimes} [n-2] \coprod_{d^0 \otimes a} \tau_{n-1}^i ([1] \otimes [n-2]), 1]$. We can then apply lemma 3.2.4.10.

Lemma 3.2.4.19. Let $0 < k < n-1$ be two integers. We denote by $\tau^k$ the projection $[n] \to [n]^k$. We then have

$$(\tau^k \circ \iota_n \circ [d^{k-1}, 1], \tau^k \circ \iota_n \circ [d^{k+1}, 1]) \ge_{n-1} \tau^k \circ \iota_n \circ [d^k, 1]$$

and

$$\tau^{n-1} \circ \iota_n \circ [d^{n-2}, 1] \ge_{n-1} \tau^k \circ \iota_n \circ [d^{n-1}, 1].$$

Proof. By construction, for any $a$, the morphism $[[2] \star a, 1] \to [2] \star [a, 1] \to [2]_t \star [a, 1]$ factors through $[[2]_t \star a, 1]$. By induction, this implies that the composite morphism $[[n-1], 1] \xrightarrow{\iota_n} [n] \to [n]^k$ factors through $[[n-1]^k, 1]$ for any $k < n-1$. This implies the first assertion.

For the second one, note that $[[1], e] \to [2] \to [2]_t$ factors through $[[1]_t, e]$. By induction, this implies that the composite morphism $[[n-1], 1] \xrightarrow{\iota_n} [n] \to [n]^{n-1}$ factors through $[[n-1]^{n-2}, 1]$ which gives the second one.

Proposition 3.2.4.20. For any $0 \le k \le n$, the morphism $([n]^k)' \to ([n]^k)''$ is a weak equivalence.

Proof. The case $k=0$ and $k=n$ are demonstrated in lemma 3.2.4.1. For the case $0 < k < n$, lemmas 3.2.4.17, 3.2.4.18 and 3.2.4.19 imply that if we denote by $\tau_k$ the projection $[n] \to [n]^k$, we have an inequality: $(\tau_k \circ d^{k-1} \circ \iota_{n-1}, \tau_k \circ d^{k+1} \circ \iota_{n-1}) \ge_{n-1} \tau_k \circ d^k \circ \iota_{n-1}$. Together with the proposition 3.2.4.8, this implies that the following square is homotopy cartesian:

$$\begin{array}{c} [n-1] \cup [n-1] \xrightarrow{d^{k+1} \cup d^{k-1}} [n]^k \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ [n-1]_t \cup [n-1]_t \longrightarrow ([n]^k)'' \end{array}$$

The morphism $([n]^k)' \to ([n]^k)''$ is then a weak equivalence.

### 3.2.5 Saturation extensions

Proposition 3.2.5.1. For any $n \ge -1$, the morphism $[n] \star [3]^{eq} \to [n] \star [3]^\sharp$ is an acyclic cofibration.

133

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proof. Let \(\Lambda[3]^{eq} \to [3]^{eq}\) be the entire inclusion generated by \(Im(d^3) \cup Im(d^0) \subset [3]\). This inclusion fits in the following sequence:

![img-80.jpeg](img-80.jpeg)

This inclusion is then a weak equivalence according to propositions 3.2.3.17 and 3.2.4.20. Now, note that we have a pushout:

![img-81.jpeg](img-81.jpeg)

As the left vertical morphism is a weak equivalence, so is the right one. Let \(\Lambda[3]^{\sharp} \to [3]^{\sharp}\) be the entire inclusion generated by \(Im(d^3) \cup Im(d^0) \subset [3]\). Using the same reasoning, we show that this cofibration is acyclic and that there is a weak equivalence \(\Lambda[3]^{\sharp} \to [e, [3]^{\sharp}]\). We then have a commutative square:

![img-82.jpeg](img-82.jpeg)

where all arrows labelled by \(\sim\) are weak equivalences. By two out of three, this implies that \([3]^{eq} \to [3]^{\sharp}\) is a weak equivalence. Combined with the proposition 3.2.2.5, this concludes the proof.

#### 3.2.6 Conclusion

Proposition 3.2.6.1. The stratified cosimplicial object constructed in 3.2.2.1 induces a Quillen adjunction \(\mathrm{tPsh}(\Delta)^{\omega}\to \mathrm{tSeg}(A)\).

Proof. It is a direct consequence of theorem 2.2.1.8 and propositions 3.2.3.17, 3.2.4.20, and 3.2.5.1. \(\square\)

Theorem 3.2.6.2. Let \( A \) be a complicial Gray module. The Gray module structure on \( \mathrm{tSeg}(A) \) given by theorem 3.1.4.8 is complicial.

Proof. The constructions 3.1.5.1 and 3.2.1.1 provide two functors \(\mathrm{tPsh}(\Delta) \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)\). Moreover, the proposition 3.2.1.3 implies that they are weakly equivalent. By propositions 3.2.3.16 and 3.2.6.1, the functor of construction 3.2.1.1 fulfills all the conditions of the definition 3.1.5.4, and so does the one of construction 3.1.5.1.

### 3.3 Complicial sets as of model of  \( (\infty, n) \) -categories

#### 3.3.1 The case \(n < \omega\)

Construction 3.3.1.1. Let \( n \in \mathbb{N} \cup \{\omega\} \). We recall that \( \mathrm{tPsh}(\Delta)^n \) is the category of stratified simplicial sets endowed with the model structure for \( n \)-complicial sets given in theorem 2.2.1.8. As remarked in

134

3.3. COMPLICIAL SETS AS OF MODEL OF \((\infty, n)\)-CATEGORIES

example 3.1.5.7, \(\mathrm{tPsh}(\Delta)^{\omega}\) is a complicial Gray module, and according to proposition 3.2.6.1, it is endowed with a left Quillen functor

\[
i ^ {\omega}: \mathrm{tPsh} (\Delta) ^ {\omega} \to \mathrm{tSeg} (\mathrm{tPsh} (\Delta)) ^ {\omega}
\]

It was noted in definition 3.2.4.16 that for \( k > 0 \), \( [k] \to [k]_t \) fits in the following cocartesian square:

![img-83.jpeg](img-83.jpeg)

The functor \( i^{\omega} \) then induces for any integer \( n < \omega \), a left Quillen functor

\[
i ^ {n + 1}: \mathrm{tPsh} (\Delta) ^ {n + 1} \rightarrow \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {n}) \tag {3.3.1.2}
\]

Definition 3.3.1.3. Let \( k \) be an integer. The \( k \)-globe of \( \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \) is [0] if \( k = 0 \) and \( [\mathbf{D}_{k-1}, 1] \) if \( k > 0 \) where \( \mathbf{D}_k \) is the stratified simplicial set constructed in definition 2.4.1.1. This assignment extends to a functor \( G \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \).

Construction 3.3.1.4. In the category of stratified simplicial sets, we define \(\tilde{\mathbf{D}}_0 := [0]\), and for all integer \(k > 0\), \(\tilde{\mathbf{D}}_k := (\Sigma \mathbf{D}_{k-1}^{op})^{op}\). This assignation lifts to a functor \(\mathrm{G} \to \mathrm{tPsh}(\Delta)\) that sends \(i_0^\epsilon\) on \(i_0^\epsilon : [0] \to \Sigma[0]\), and \(i_k^\epsilon\) to \((\Sigma i_{k-1}^{-\epsilon})^{op} : (\Sigma \mathbf{D}_{k-1}^{op})^{op} \to (\Sigma \mathbf{D}_k^{op})^{op}\) for \(k > 0\) and \(\epsilon \in \{-, +\}\).

Lemma 3.3.1.5. There exists a natural zigzag of weak equivalences of \(\mathrm{tSeg}(\mathrm{Psh}(\Delta)^{\omega})\)

\[
\mathbf {D} _ {k} \rightsquigarrow \tilde {\mathbf {D}} _ {k}.
\]

Proof. As the functor \(\mathrm{R}:\mathrm{tPsh}(\Delta)\to (0,\omega)\)-cat preserves suspension and the op duality, we have \(\mathrm{R}(\mathbf{D}_k)\cong\) \(\mathrm{R}(\tilde{\mathbf{D}}_k)\). We then have two natural transformations

\[
\mathbf {D} _ {-} \rightarrow \mathrm{N} (\mathbf {D} _ {-}) \leftarrow \tilde {\mathbf {D}} _ {-}
\]

which are weak equivalences according to theorem 2.2.3.3.

Lemma 3.3.1.6. Let \( K, L \) be two stratified simplicial sets, and \( i^{\omega}(L) \rightsquigarrow [K,1] \) a zigzag of weak equivalence of \( \mathrm{tPsh}(\Delta)^{\omega} \). This induces a zigzag \( i^{n+1}((\Sigma L^{op})^{op})) \rightsquigarrow [(\Sigma K^{op})^{op},1] \) of weak equivalences.

Proof. We recall that \(\Sigma^{\star}:\mathrm{tPsh}(\Delta)^{\omega}\to \mathrm{tPsh}(\Delta)^{\omega}\) is the functor defined in construction 2.2.2.15 that sends \(X\) to \([0]\coprod_X X\star [0]\) and that we have a weak equivalence \(\Sigma X\to \Sigma^{\star}X\) natural in \(X\) defined in (2.2.2.16). This induces a weak equivalence \((\Sigma X^{op})^{op}\to (\Sigma^{\star}X^{op})^{op}\) natural in \(X\).

By proposition 2.2.2.11, applying the duality \((\_)^{op}\) to the cocartesian square of stratified simplicial sets

![img-84.jpeg](img-84.jpeg)

we get a cocartesian square

![img-85.jpeg](img-85.jpeg)

135

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

We denote by \(\Sigma': \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^\omega) \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^\omega)\) the functor sending \(C\) to \([0] \star C \coprod_X [0]\). Remark that by construction, we have a cocartesian square

![img-86.jpeg](img-86.jpeg)

and then a natural isomorphism \( i^{\omega}((\Sigma^{*}(L^{op}))^{op}) \cong \Sigma' i^{\omega}(L) \).

By proposition 3.2.1.6, for any stratified simplicial sets \(K\), \(\Sigma'([K,1])\) is the colimit of the diagram:

\[
[ [ 0 ] \diamond K, 1 ] \xleftarrow {[ d ^ {0} * K , 1 ]} [ K, 1 ] \xrightarrow {[ e , d ^ {1} ]} [ [ 0 ], 1 ] \vee [ K, 1 ] \xleftarrow {[ e , d ^ {0} ]} [ K, 1 ] \longrightarrow [ 0 ]
\]

Combined with the previous cocartesian square of stratified simplicial sets, we get a cocartesian square

![img-87.jpeg](img-87.jpeg)

and as the left vertical morphism is a weak equivalence, so is the right vertical one. We then have constructed a natural transformation

\[
\Sigma^ {\prime} [ K, 1 ] \rightarrow [ (\Sigma K ^ {o p}) ^ {o p}, 1 ]
\]

that is pointwise a weak equivalence.

Let \( K, L \) be two stratified simplicial sets, and \( i^{\omega}(L) \rightsquigarrow [K, 1] \) a zigzag of weak equivalence. We then have natural weak equivalences

\[
\begin{array}{l} i ^ {\omega} ((\Sigma L ^ {o p}) ^ {o p})) \rightarrow i ^ {\omega} ((\Sigma^ {*} L ^ {o p}) ^ {o p}) \\ \cong \Sigma^ {\prime} (i ^ {\omega} (L)) \\ \leftrightarrow \Sigma^ {\prime} [ K, 1 ] \\ \rightarrow [ (\Sigma K ^ {o p}) ^ {o p}, 1 ] \\ \end{array}
\]

Proposition 3.3.1.7. For all \( n \in \mathbb{N} \cup \{\omega\} \), the functor \( i^{n+1} \) preserves globes up to zigzag of weak equivalence.

Proof. It is sufficient to demonstrate the result when \( n = \omega \). We construct by induction on \( k \) a zigzag of weak equivalence \( i^{\omega}(\mathbf{D}_k) \rightsquigarrow \mathbf{D}_k \). The initialization is obvious as we have \( i^{\omega}(\mathbf{D}_0) \cong \mathbf{D}_0 \) and \( i^{\omega}(\mathbf{D}_1) \cong \mathbf{D}_1 \). Suppose then the zigzag constructed at the stage \( k \). Using Lemmas 3.3.1.5 and 3.3.1.6, we have a zigzag of weak equivalences

\[
i ^ {n + 1} (\mathbf {D} _ {k}) \leftrightarrow i ^ {n + 1} (\tilde {\mathbf {D}} _ {k}) \leftrightarrow [ \mathbf {D} _ {k - 1} ^ {\sim}, 1 ] \leftrightarrow [ \mathbf {D} _ {k - 1}, 1 ]
\]

Construction 3.3.1.8. We define the colimit-preserving functor

\[
j ^ {\omega}: \mathrm{tSeg} (\mathrm{tPsh} (\Delta) ^ {\omega}) \rightarrow \mathrm{tPsh} (\Delta) ^ {\omega} \tag {3.3.1.9}
\]

136

3.3. COMPLICIAL SETS AS OF MODEL OF \((\infty, n)\)-CATEGORIES

sending $[K, n]$ to the pushout:

$$\begin{array}{c} \coprod_{i \leq n} K \boxtimes \{i\} \longrightarrow K \boxtimes [n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{i \leq n} [0] \longrightarrow j([K, n]) \end{array}$$

and $[[0], 1]_t$ to $[1]_t$. As $\_ \boxtimes \_$ is a left Quillen bifunctor, and as $\tilde{j}([[0], 1]_t \to [0]) = [1]_t \to [0]$ and $\tilde{j}([[0], E^{eq}] \to [0]) = E^{eq} \to [0]$ are weak equivalences, the theorem 3.1.2.13 implies that the functor $j^\omega$ is a left Quillen functor. By definition of the Gray pre-tensor product, we remark that $\tilde{j}([[k], n] \to [[k]_t, n])$ is a pushout of a disjoint union of $[k + 1] \to [k + 1]_t$, and $j^\omega$ then induces for any $n < \omega$, a left Quillen functor

$$j^{n+1} : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \to \mathrm{tPsh}(\Delta)^{n+1}.$$

**Proposition 3.3.1.10.** *For any $n \in \mathbb{N} \cup \{\omega\}$, the functor*

$$j^{n+1} : \mathrm{tPsh}(\Delta)^{n+1} \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$$

*preserves globes up to isomorphisms.*

*Proof.* This is a direct consequence of the isomorphism $j^{n+1}[K, 1] \cong \Sigma K$ natural in $K$. $\square$

**Theorem 3.3.1.11.** *For all integers $n$, the model structure $\mathrm{tPsh}(\Delta)^n$ for $n$-complicial sets is a model of $(\infty, n)$-categories.*

*Proof.* We will proceed by induction. For the initialization, remark that we have two functors

$$\begin{array}{c c c c c c} i^0 : \mathrm{Psh}(\Delta) & \to & \mathrm{tPsh}(\Delta)^0 & j^0 : \mathrm{tPsh}(\Delta)^0 & \to & \mathrm{Psh}(\Delta) \\ [n] & \mapsto & \tau_0^i[n] & [n], [n]_t & \mapsto & [n] \end{array}$$

which are obviously left Quillen. As we have $j^0 i^0 \cong \mathrm{id}$ and a weakly invertible natural transformation $\mathrm{id} \to i^0 j^0$, these two functors are Quillen equivalences, and $\mathrm{tPsh}(\Delta)^0$ is then a model of $(\infty, 0)$-categories.

Suppose now that $\mathrm{tPsh}(\Delta)^n$ is a model of $(\infty, n)$-categories. Theorem 3.1.3.5 then implies that $\mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$ is a model of $(\infty, n + 1)$-categories.

The propositions 3.3.1.7 and 3.3.1.10 state that the left Quillen functor

$$i^\omega j^\omega : \mathrm{tPsh}(\Delta)^\omega \to \mathrm{tPsh}(\Delta)^\omega$$

preserves globes, and the corollary 2.4.4.14 then implies that $i^\omega j^\omega$ is equivalent up to homotopy to the identity. As a consequence, the left Quillen functor

$$i^{n+1} j^{n+1} : \mathrm{tPsh}(\Delta)^{n+1} \to \mathrm{tPsh}(\Delta)^{n+1}$$

is also equivalent up to homotopy to the identity. The proposition 3.3.1.7 and 3.3.1.10 also implies that the composite functor

$$j^{n+1} i^{n+1} : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$$

preserves globes. According to the proposition 3.1.3.4, $j^{n+1} i^{n+1}$ is equivalent up to homotopy to the identity. The two functors $i^{n+1}$ and $j^{n+1}$ are then homotopy inverse, and are then both Quillen equivalence. Being equivalent to $\mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$, the model category $\mathrm{tPsh}(\Delta)^{n+1}$ is then a model of $(\infty, n + 1)$-categories. $\square$

137

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Corollary 3.3.1.12. Let \( n \in \mathbb{N} \). The adjunction between \( \mathrm{Psh}(\Theta_n \times \Delta) \) and \( \mathrm{tPsh}(\Delta)^n \) constructed in [OR22] is a Quillen equivalence.

Proof. A direct induction using [OR22, theorem 3.22] implies that the left adjoint preserves globes. The results then follow from the fact that these two categories are models of \((\infty, n)\)-categories and from proposition 3.1.3.4.

#### 3.3.2 The case \(n = \omega\)

Construction 3.3.2.1. We define by induction the functor

\[
q: \Theta \to \mathrm{tPsh} (\Delta)
\]

by the formula

\[
q ([ 0 ]) := [ 0 ], \quad q ([ \mathbf {a}, n ]) := \underset {[ b, m ] \to [ \mathbf {a}, n ]} {\operatorname{colim}} q (b) \otimes [ n ].
\]

This induces an adjunction:

\[
i: \mathrm{Psh} (\Theta \times \Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta): N _ {i}
\]

where the left adjoint is the left Kan extension of the functor  \( (a,n)\mapsto q(a)\times[n]^{\sharp} \) .

We denote  \( i_{\omega} := i \) ,  \( N_{i_{\omega}} := N_{i} \) , and for an integer n,

\[
i _ {n}: \mathrm{Psh} (\Theta_ {n} \times \Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta): N _ {i _ {n}}
\]

the restriction of this adjunction.

Proposition 3.3.2.2. For any \(n \in \mathbb{N} \cup \{\omega\}\), the adjunction constructed in 3.3.2.1

\[
i _ {n}: \mathrm{Psh} (\Theta_ {n} \times \Delta) \xrightarrow [ \leftarrow ]{\perp} \mathrm{tPsh} (\Delta) ^ {n}: N _ {i _ {n}}
\]

is a Quillen pair, where \(\mathrm{Psh}(\Theta_n\times \Delta)\) is endowed with the model structure described in construction 3.1.3.2.

Proof. We first prove by induction on \( n \) that the restricted functor \( (q_n)_! : \mathrm{Psh}(\Theta_n) \to \mathrm{tPsh}(\Delta)^n \) sends \( W_n \) onto weak equivalences. The initialization is trivial. The case \( n = 1 \) is a consequence of proposition 2.2.1.10 applied to the identity functor \( id : \mathrm{tPsh}(\Delta)_1 \to \mathrm{tPsh}(\Delta)_1 \).

Suppose the result true at the stage  \( n \geq 1 \) . We recall that the Gray tensor product on stratified simplicial sets is a Quillen bifunctor. The induction hypothesis and the proposition 2.1.1.8 then imply that the functor

\[
(q _ {n + 1} ^ {\prime}) _ {!}: \mathrm{Psh} (\Delta [ \Theta_ {n} ]) \to \mathrm{tPsh} (\Delta) ^ {n + 1}
\]

defined by \( q_{n+1}'[a, n] := a \otimes [n] \), sends \( \overline{\mathbf{W}_n} \otimes \overline{\mathbf{W}_1} \) to weak equivalences. As \( M_{n+1} \) is included in this set of morphisms, it is send by \( q_{n+1}' \) to weak equivalences. As \( q_{n+1}' \) preserves monomorphisms and colimits, the proposition 2.1.1.8 implies that this functor sends \( \overline{M_{n+1}} \) to weak equivalences. Now remark that \( (q_{n+1})_! \) is the composite

\[
\mathrm{Psh} (\Theta_ {n + 1}) \xrightarrow {i ^ {*}} \mathrm{Psh} (\Delta [ \Theta_ {n} ]) \xrightarrow {(q _ {n + 1} ^ {\prime}) !} \mathrm{tPsh} (\Delta) ^ {n + 1}
\]

and the proposition 1.1.3.17 then implies that \((q_{n + 1})_!\) sends \(\mathrm{W}_{n + 1}\) to weak equivalences.

As \( \mathrm{W} := \cup_{n} \mathrm{W}_{n} \), the functor \( q_{!} : \mathrm{Psh}(\Theta) \to \mathrm{tPsh}(\Delta)^{\omega} \) sends \( \mathrm{W} \) to weak equivalences. By definition of the model structure on \( \mathrm{Psh}(\Theta_{n} \times \Delta) \), this concludes the proof.

138

3.3. COMPLICIAL SETS AS OF MODEL OF \((\infty, n)\)-CATEGORIES

Corollary 3.3.2.3. For any $n \in \mathbb{N}$, the adjunction constructed in 3.3.2.1

$$i_n : \mathrm{Psh}(\Theta_n \times \Delta) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)^n : N_{i_n}$$

is a Quillen equivalence.

Proof. Note that $i_n$ preserves globes by construction. According to theorem 3.3.1.11, $\mathrm{tPsh}(\Delta)^n$ is a model of $(\infty, n)$-categories, and the proposition 3.1.3.4 concludes the proof. □

Construction 3.3.2.4. For any integer $n$, we have an Quillen adjunction

$$\mathrm{Psh}(\Theta_n \times \Delta) \xrightarrow[\leftarrow \tau_n]{\perp} \mathrm{Psh}(\Theta \times \Delta)$$

where the left adjoint is the left Kan extension of the canonical inclusion $\Theta_n \times \Delta \to \Theta \times \Delta$. The image of an object $X$ of $\mathrm{Psh}(\Theta_n \times \Delta)$ by $\iota$ will be simply denoted by $X$.

Theorem 3.3.2.5. For any $n \in \mathbb{N} \cup \{\omega\}$, the adjunction constructed in 3.3.2.1

$$i : \mathrm{Psh}(\Theta \times \Delta) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)^\omega : N_i$$

is a Quillen equivalence. The model category $\mathrm{tPsh}(\Delta)^\omega$ is then a model of $(\infty, \omega)$-categories.

Proof. As the functor $i$ preserves globes, the theorem 2.4.2.9 implies that $N_i$ detects weak equivalences. To conclude the proof, it then remains to show that $i$ is homotopically fully faithfull.

Let $X$ be an element of $\mathrm{Psh}(\Theta \times \Delta)$. We have to show that the canonical morphism $X \to N_i \mathbf{F}iX$ is a weak equivalence where $\mathbf{F}$ is a fibrant replacement. The object $X$ is the colimit of the sequence

$$\tau_0 X \to \tau_1 X \to \tau_2 X \to \cdots$$

As the generating anodyne extension has finite codomain, the colimit of the sequence

$$\mathbf{F}i\tau_0 X \to \mathbf{F}i\tau_1 X \to \mathbf{F}i\tau_2 X \to \cdots$$

is a fibrant replacement of $iX$. As $N_i$ preserves directed colimits, and as $\tau_n N_i \cong N_{i_n}$, the object $N_i \mathbf{F}iX$ is the colimit of the sequence

$$N_{i_0} \mathbf{F}i_0\tau_0 X \to N_{i_1} \mathbf{F}i_1\tau_1 X \to N_{i_2} \mathbf{F}i_2\tau_2 X \to \cdots$$

As weak equivalences are stable by directed colimits, the corollary 3.3.2.3 implies that $X \to N_i \mathbf{F}iX$ is a weak equivalence, which concludes the proof. □

Finally, it may be useful to know the connection between the Quillen equivalences of Corollary 3.3.2.3 and Theorem 3.3.2.5 with the Street nerve defined in 2.2.3.1.

Construction 3.3.2.6. We denote by $\pi_0 : \mathrm{Psh}(\Theta_n \times \Delta) \to \mathrm{Psh}(\Theta_n)$ the left Kan extention of the functor sending $(a, [n])$ onto $a$. As $\pi_0$ sends W to isomorphisms, it induces an adjoint pair:

$$\pi_0 : \mathrm{Psh}(\Theta_n \times \Delta) \xrightarrow{\perp} (0, \omega)\text{-cat} : N_{\pi_0}$$

139

CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proposition 3.3.2.7. Let \( n \in \mathbb{N} \cup \{\omega\} \). There exist unique invertible natural transformations

\[
\begin{array}{c} \operatorname{Psh} (\Theta_ {n} \times \Delta) \xrightarrow {\pi_ {0}} (\infty , n) \text {-cat} \\ i _ {n} \Big \downarrow \qquad \cong \qquad \uparrow \tau_ {n} ^ {i} \\ \operatorname{tPsh} (\Delta) ^ {n} \xrightarrow [ \mathrm{R} ]{} (0, \omega) \text {-cat} \end{array}
\]

\[
\begin{array}{c} \operatorname{Psh} (\Theta_ {n} \times \Delta) \xrightarrow {\pi_ {0}} (\infty , n) \text {-cat} \\ N _ {i _ {n}} \Big \uparrow \qquad \cong \qquad \uparrow \tau_ {n} ^ {i} \\ \operatorname{tPsh} (\Delta) ^ {n} \xrightarrow [ \mathrm{R} ]{} (0, \omega) \text {-cat} \end{array}
\]

where \(\mathbf{R}\) is the functor defined in 2.2.3.1 and the functor \(\tau_n^i\) is defined in 1.1.1.12.

There exist a unique invertible natural transformation and a weekly unique weekly invertible natural transformation

\[
\begin{array}{c} (\infty , n) \text {-cat} \xrightarrow {N _ {\pi_ {0}}} \operatorname{Psh} (\Theta_ {n} \times \Delta) \\ \Big \downarrow \qquad \cong \qquad \uparrow N _ {i _ {n}} \\ (0, \omega) \text {-cat} \xrightarrow [ N ]{} \operatorname{tPsh} (\Delta) ^ {n} \end{array}
\]

\[
\begin{array}{c} (\infty , n) \text {-cat} \xrightarrow {N _ {\pi_ {0}}} \operatorname{Psh} (\Theta_ {n} \times \Delta) \\ \Big \downarrow \qquad \sim \qquad \Big \downarrow i _ {n} \\ (0, \omega) \text {-cat} \xrightarrow [ N ]{} \operatorname{tPsh} (\Delta) ^ {n} \end{array}
\]

where the functor \(\mathbf{N}\) is defined in 2.2.3.1.

Proof. As \((\infty, n)\)-cat \(\to (0, \omega)\)-cat is fully faithful and as \(\mathrm{tPsh}(\Delta)^n \to \mathrm{tPsh}(\Delta)^\omega\) is homotopically fully faithful, we can restrict to the case \(n = \omega\).

Remark that the two functors

\[
\Theta \times \Delta \xrightarrow {i} \mathrm{tPsh} (\Delta) ^ {\omega} \xrightarrow {\mathrm{R}} (0, \omega) \text {-cat}
\]

\[
\Theta \times \Delta \longrightarrow \operatorname{Psh} (\Theta_ {n} \times \Delta) \xrightarrow {\pi_ {0}} (0, \omega) \text {-cat}
\]

factor through \(\Theta\) as \(\pi_0\) and R sends weak equivalences to isomorphisms, and preserve globes by construction. The theorem 1.2.4.15 then implies that they are both isomorphic to the canonical inclusion \(\Theta \to (\infty, \omega)\)-cat. This implies the existence of the invertible natural transformation appearing in the first square of the first assertion. The unicity follows from the lemma 1.2.4.19 that states that globular sums have no non-trivial automorphisms. As R and \(\pi_0\) sends weak equivalences on isomorphisms, and as \((i, N_i)\) is a Quillen equivalence, this induces the existence and the unicity of the invertible natural transformation appearing in the second square of the first assertion.

Eventually, the second assertion follows by adjunction and from the fact that \((i,N_i)\) is a Quillen equivalence.

140

# Index of symbols

|  $(0, n)$-cat | 15  |
| --- | --- |
|  $(0, \omega)$-cat | 15  |
|  $(0, \omega)$-cat_{B} | 29  |
|  $(\_)^2$ |   |
|  *for stratified Segal A-precategories* | 105  |
|  $(\_)^{co}$ | 14  |
|  $(\_)^{op}$ | 14  |
|  $(\_)^\circ$ | 14  |
|  $(\_)_{mk}$ | 67  |
|  $\otimes$ |   |
|  *for $(0, \omega)$-categories* | 47  |
|  *for marked simplicial sets* | 73  |
|  *for stratified simplicial sets* | 72  |
|  $\diamond$ | 74  |
|  $\star$ | 76  |
|  $\_ \otimes [1]$ |   |
|  *for $(0, \omega)$-categories* | 47  |
|  *for augmented directed complexes* | 41  |
|  *for marked simplicial sets* | 77  |
|  $[1] \otimes \_$ |   |
|  *for $(0, \omega)$-categories* | 47  |
|  *for stratified Segal A-precategories* | 114  |
|  $\_ \star 1$ |   |
|  *for $(0, \omega)$-categories* | 48  |
|  *for augmented directed complexes* | 42  |
|  *for marked simplicial sets* | 77  |
|  $1 \star$ |   |
|  *for $(0, \omega)$-categories* | 48  |
|  *for marked simplicial sets* | 77  |
|  $1 \star \_$ |   |
|  *for $(0, \omega)$-categories* | 48  |
|  $[\_, 1]$ |   |
|  *for $(0, \omega)$-categories* | 14  |
|  *for augmented directed complexes* | 44  |
|  $[a, n]$ | 16  |
|  $[a, n]$ |   |
|  *for A-Segal precategories* | 102  |
|  *for $(0, \omega)$-categories* | 16  |
|  $[a_0, n_0] \vee [a_1, n_1] \vee \dots \vee [a_k, n_k]$ |   |
|  *for $\Theta$* | 16  |
|  *for Segal A-precategories* | 103  |
|  $[e, 1]_t$ | 105  |
|  $[e, 1]_t \vee [a, n]$ | 108  |
|  $[n]_t$ | 69  |
|  $[n]^k$ | 69  |
|  $([n]^k)'$ | 69  |
|  $([n]^k)''$ | 69  |
|  $([3]^{eq}$) | 69  |
|  $[n]^2$ | 69  |
|  $\ge n$ | 126  |
|  $\hat{\square}$ | 64  |
|  ADC | 25  |
|  ADC_{B} | 28  |
|  $C(a, b)$ | 74  |
|  $C_{/c}$ | 77  |
|  $C_{c/}$ | 77  |
|  **D_{n}** |   |
|  *for $(0, \omega)$-categories* | 13  |
|  *for marked simplicial sets* | 84  |
|  $\Delta[\Theta]$ | 18  |
|  $\Delta[\Theta_n]$ | 19  |
|  $E^{eq}$ | 18  |
|  $i_{str}$ | 78  |
|  $\lambda : \omega$-cat $\rightarrow$ ADC | 25  |
|  M | 18  |
|  mPsh_{M}(_) | 67  |
|  mPsh($\Delta$) | 71  |
|  M_{Sat} | 18  |
|  M_{Seg} | 18  |
|  mSeg(A) | 119  |

141

INDEX OF SYMBOLS

N : (0, ω)-cat → mPsh(Δ) ... 78

ν : ADC → ω-cat ... 26

∂ₙ⁺(_) ... 27

∂ₙ⁻(_) ... 27

R : mPsh(Δ) → (0, ω)-cat ... 78

r_C : C → C_mk ... 119

Seg(A) ... 102

Σ_ ... 73

Σⁿ

for (∞, ω)-categories ... 18

for (0, ω)-categories ... 14

Σ*_ ... 75

[1] ∀ΣX ... 76

ΣX ∀ [1] ... 76

Spₐ ... 18

S̅ ... 20

τₙ

for (0, ω)-categories ... 15

for marked simplicial sets ... 72

τₙⁱ

for (0, ω)-categories ... 15

for marked simplicial sets ... 71

for stratified Segal A-precategories ... 109

Θ ... 16

Θₙ ... 16

tPsh_M(B) ... 66

tPsh(Δ) ... 68

tPsh(Δ)ⁿ ... 70

tSeg(A) ... 105

W ... 18

W_Sat ... 18

W_Seg ... 18

142

# Index of notions

A

algebraic morphism of $\Theta$ ... 17
array ... 26
atomic basis ... 29

B

basis
    for $(\infty, \omega)$-categories ... 28
    for augmented directed complexes ... 27

C

$\omega$-category ... 13
$(0, \omega)$-category ... 15
$(0, n)$-category ... 15
$n$-cell
    for $(0, \omega)$-categories ... 13
    for marked simplicial sets ... 84
co-join ... 76
coherent array ... 26
completeness extensions ... 104
complicial Gray module ... 113
complicial horn inclusions ... 69
complicial set ... 70
complicial sets ... 70
complicial thinness extensions ... 69

D

degenerate morphism of $\Theta$ ... 17
degeneration partition operator ... 72
D-equivalence ... 87
diamond product ... 74
dimension of a globular sum ... 16
discrete objects ... 102
D-trivial fibration ... 87
dualities ... 14

E

elegant Reedy category ... 17

elementary anodyne extension

    for Segal A-precategory ... 104
    for stratified simplicial sets ... 69
entire morphism ... 66, 69
equivalence ... 15
equivalence of marked Segal A-categories ... 105
equivalence of Segal A-categories ... 104
equivalent $n$-cells ... 85
even duality ... 14

F

face partition operator ... 72
full duality ... 14

G

generated by composition ... 28
generating Reedy cofibrations ... 104
$n$-globe
    for $(0, \omega)$-categories ... 13
    for marked simplicial sets ... 84
globular morphism ... 17
globular object ... 109
globular set ... 13
globular sum ... 16
Gray o-cone
    for $(0, \omega)$-categories ... 48
    for marked simplicial sets ... 77
Gray o-cylinder
    for $(0, \omega)$-categories ... 47
    for stratified Segal A-precategories ... 114
Gray cone
    for $(0, \omega)$-categories ... 48
    for augmented directed complexes ... 42
    for marked simplicial sets ... 77
Gray cylinder
    for $(0, \omega)$-categories ... 47
    for augmented directed complexes ... 41

143

INDEX OF NOTIONS

|  *for marked simplicial sets* ... 77 | **R**  |
| --- | --- |
|  Gray module ... 109 | Reedy category ... 16  |
|  Gray op-cone | Reedy cofibrant functor ... 20  |
|  *for (0,ω)-categories* ... 48 | regular morphism ... 69  |
|  Gray tensor product | *n*-relying on *x* ... 126  |
|  *for augmented directed complexes* ... 40 | *n*-relying on *x* and *x'* ... 126  |
|  *for marked simplicial sets* ... 73 |   |
|  *for stratified simplicial sets* ... 72 | **S**  |
|  **I** | saturation extensions ... 69  |
|  intelligent *n*-truncation | Segal *A*-category ... 104  |
|  *for (0,ω)-categories* ... 15 | Segal *A*-precatagory ... 102  |
|  *for marked simplicial sets* ... 71 | Segal extensions ... 104  |
|  *for stratified Segal A-precategories* ... 109 | slice over ... 77  |
|  isomorphism for an arrow *x* : [*e*, 1] → *C* ... 104 | slice under ... 77  |
|  **L** | *S*-local ... 19  |
|  left cancellation ... 20 | stratified morphism ... 66  |
|  loop free basis | stratified presheaf on *B* ... 65  |
|  *for (0,ω)-categories* ... 29 | stratified Segal *A*-precatagory ... 105  |
|  *for augmented directed complexes* ... 28 | stratified simplicial set ... 68  |
|  **M** | Street endofunctor ... 78  |
|  marked presheaf on *B* ... 67 | suspension  |
|  marked Segal *A*-category ... 105 | *for (0,ω)-categories* ... 14  |
|  marked Segal *A*-precategory ... 119 | *for augmented directed complexes* ... 44  |
|  marked simplicial set ... 71 | *for marked simplicial sets* ... 73  |
|  model of (∞, *n*)-categories ... 109 |   |
|  morphism of ω-categories ... 13 | **T**  |
|  **N** | thin simplex ... 68  |
|  nice model structure ... 64 | *n*-truncation  |
|  non trivial *n*-cell ... 13 | *for (0,ω)-categories* ... 15  |
|  **O** | *for marked simplicial sets* ... 72  |
|  odd duality ... 14 |   |
|  oriental ... 77 | **U**  |
|  **P** | unitary basis ... 28  |
|  polygraph ... 14 |   |
|  precocomplete set of arrows ... 20 | **W**  |
|  **Q** | wedge of acyclic cofibration ... 65  |
|  quasi-rigid morphism ... 29 |   |

144

# Bibliography

[AGOR23] Dimitri Ara, Andrea Gagna, Viktoriya Ozornova, and Martina Rovelli. A categorical characterization of strong steiner  $\omega$ -categories. *Journal of Pure and Applied Algebra*, 227(7):107313, 2023.[AM20] Dimitri Ara and Georges Maltsiniotis. *Joint et tranches pour les  $\infty$ -catégories strictes*. Société Mathématique de France, 2020.[Ara10] Dimitri Ara. *Sur les  $\infty$ -groupoïdes de Grothendieck et une variante  $\infty$ -catégorique*. PhD thesis, Université Paris 7, 2010.[BD95] John C Baez and James Dolan. Higher-dimensional algebra and topological quantum field theory. *Journal of mathematical physics*, 36(11):6073–6105, 1995.[Ber02] Clemens Berger. A cellular nerve for higher categories. *Advances in Mathematics*, 169(1):118–175, 2002.[Bou77] A.K. Bousfield. Constructions of factorization systems in categories. *Journal of Pure and Applied Algebra*, 9(2):207–220, 1977.[BR13] Julia E Bergner and Charles Rezk. Reedy categories and the  $\Theta$ -construction. *Mathematische Zeitschrift*, 274(1-2):499–514, 2013.[BSP21] Clark Barwick and Christopher Schommer-Pries. On the unicity of the theory of higher categories. *Journal of the American Mathematical Society*, 34(4):1011–1058, 2021.[Cam23a] Timothy Campion. The gray tensor product of  $(\infty, n)$ -categories. *arXiv preprint arXiv:2311.00205*, 2023.[Cam23b] Timothy Campion. An  $(\infty, n)$ -categorical pasting theorem. *arXiv preprint arXiv:2311.00200*, 2023.[Cis06] Denis-Charles Cisinski. *Les préfaïseaux comme modèles des types d'homotopie*. Société mathématique de France, 2006.[Cis19] Denis-Charles Cisinski. *Higher categories and homotopical algebra*, volume 180. Cambridge University Press, 2019.[CS19] Damien Calaque and Claudia Scheimbauer. A note on the  $(\infty, n)$ -category of cobordisms. *Algebraic & Geometric Topology*, 19(2):533–655, 2019.

145

BIBLIOGRAPHY

[Dug01] Daniel Dugger. Replacing model categories with simplicial ones. Transactions of the American Mathematical society, 353(12):5003–5027, 2001.

[GHL22] Andrea Gagna, Yonatan Harpaz, and Edoardo Lanari. On the equivalence of all models for (∞, 2)-categories. Journal of the London Mathematical Society, 106(3):1920–1982, 2022.

[GOR21] Andrea Gagna, Viktoriya Ozornova, and Martina Rovelli. Nerves and cones of free loop-free ω-categories. arXiv preprint arXiv:2103.01066, 2021.

[GP21] Daniel Grady and Dmitri Pavlov. The geometric cobordism hypothesis. arXiv preprint arXiv:2111.01095, 2021.

[GR19] Dennis Gaitsgory and Nick Rozenblyum. A study in derived algebraic geometry: Volume I: correspondences and duality, volume 221. American Mathematical Society, 2019.

[Hir03] Philip S Hirschhorn. Model categories and their localizations. Number 99. American Mathematical Soc., 2003.

[Joy02] André Joyal. Quasi-categories and Kan complexes. Journal of Pure and Applied Algebra, 175(1-3):207–222, 2002.

[Lou23] Félix Loubaton. Conditions de Kan sur les nerfs des ω-catégories. Bulletin de la société mathématique de France, 151:331–406, 2023.

[Lur08] Jacob Lurie. On the classification of topological field theories. Current developments in mathematics, 2008(1):129–280, 2008.

[Lur09] Jacob Lurie. Higher topos theory. Princeton University Press, 2009.

[Mae23] Yuki Maehara. Orientals as free weak ω-categories. Journal of Pure and Applied Algebra, 227(3):107230, 2023.

[OR20a] Viktoriya Ozornova and Martina Rovelli. Fundamental pushouts of n-complicial sets. arXiv preprint arXiv:2005.05844, 2020.

[OR20b] Viktoriya Ozornova and Martina Rovelli. Model structures for (∞, n)-categories on (pre) stratified simplicial sets and prestratified simplicial spaces. Algebraic & Geometric Topology, 20(3):1543–1600, 2020.

[OR22] Viktoriya Ozornova and Martina Rovelli. A quillen adjunction between globular and complicial approaches to (∞, n)-categories. arXiv preprint arXiv:2206.02689, 2022.

[ORV20] Viktoriya Ozornova, Martina Rovelli, and Dominic Verity. Gray tensor product and saturated n-complicial sets. arXiv preprint arXiv:2007.01235, 2020.

[Rez10] Charles Rezk. A cartesian presentation of weak n-categories. Geometry & Topology, 14(1):521–571, 2010.

[RV22] Emily Riehl and Dominic Verity. Elements of ∞-Category Theory, volume 194. Cambridge University Press, 2022.

146

BIBLIOGRAPHY

[Sim11] Carlos Simpson. *Homotopy Theory of Higher Categories: From Segal Categories to n-Categories and Beyond*, volume 19. Cambridge University Press, 2011.

[Ste04] Richard Steiner. $\omega$-categories and chain complexes. *Homology, Homotopy and Applications*, 6(1):175 – 200, 2004.

[Str87] Ross Street. The algebra of oriented simplexes. *Journal of Pure and Applied Algebra*, 49(3):283 – 335, 1987.

[Ver06] Dominic Verity. Weak complicial sets, a simplicial weak omega-category theory. part II: nerves of complicial gray-categories. *arXiv preprint math/0604416*, 2006.

[Ver08a] Dominic Verity. Complicial sets. *Memoirs of the AMS*, 193(905), 2008.

[Ver08b] Dominic Verity. *Complicial Sets Characterising the Simplicial Nerves of Strict $\omega$-Categories*, volume 193. American Mathematical Soc., 2008.

[Ver08c] Dominic Verity. Weak complicial sets I. basic homotopy theory. *Advances in Mathematics*, 219(4):1081–1149, 2008.

[Ver17] Dominic Verity. A complicial compendium. www.cirm-math.fr/ProgWeebly/Renc1773/Verity.pdf, 2017.

147