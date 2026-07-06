arXiv:2301.11424v2 [math.CT] 8 Jan 2025

# An inductive model structure for strict \(\infty\)-categories

Simon Henry* and Félix Loubaton†

## Abstract

We construct a left semi-model category of “marked strict  \( \infty \) -categories” for which the fibrant objects are those whose marked arrows satisfy natural closure properties and are invertible up to higher marked arrows. The canonical model structure on strict  \( \infty \) -categories can be recovered as a left Bousfield localization of this model structure. We show that an appropriate extension of the Street nerve to the marked setting produces a Quillen adjunction between our model category and the Verity model structure for complicial sets, generalizing previous results by the second named author. Finally, we use this model structure to study, in the setting of strict  \( \infty \) -categories, the idea that, because they are two different “truncation functors” taking an  \( (\infty,n) \)  to an  \( (\infty,n-1) \) -category, there are two non-equivalent definitions for the  \( (\infty,1) \) -category of  \( (\infty,\infty) \) -categories as a limit of the  \( (\infty,1) \) -categories of  \( (\infty,n) \) -categories. We show that in fact there seem to be at least three non-equivalent ways of constructing an  \( (\infty,1) \) -category of  \( (\infty,\infty) \) -categories.

## Contents

1 Introduction 2

1.1 The Street Nerve as a Right Quillen Functor 2
1.2 The Two (?) Notions of \((\infty, \infty)\)-Categories 3
1.3 Overview of the Paper 6

2 ∞-Categories and Marked ∞-Categories 8

2.1 ∞-Categories 8
2.2 Marked \(\infty\) -Categories 12
2.3 Tensor Product of \(m\)-Marked \(\infty\)-Categories 13
2.4 The Inductive Left Semi-Model Structure 16

3 Equations and Saturations in an m-Marked ∞-Category. 22

3.1 Definitions of Equations and Saturations ... 22
3.2 Characterization of Fibrant Objects of The Inductive Left Semi-Model Structure 26

*Simon Henry has received research support from Natural Sciences and Engineering Research Council of Canada, RGPIN-2020-06779.

\( ^{\dagger} \) Félix Loubaton has received support from the Agence Nationale de la Recherche program 3ia Côte d'Azur ANR-19-P3IA-0002, and the European Research Council Horizons 2020 grant 670624

1

3.3 Isofibrations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 30
3.4 Equivalences . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 33
3.5 The Saturated Inductive Localization. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 34

## 4 Comparison with Other Model Structures . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 36

4.1 Truncation Functors . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 36
4.2 Coinductive Localization and Comparison with $\infty$-Cat$_{\text{Can}}$ . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 43
4.3 The Canonical Model Structure vs the Limit of the $\pi$-Tower . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 47
4.4 Complicial Sets and Stratified Street Nerve . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 52

## A Left Semi-model categories . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 58

# 1 Introduction

In the present paper, we introduce (in Section 2.2) a category $\infty$-Cat$^{+m}$ of “$m$-marked (strict) $\infty$-categories” for $m \in \mathbb{N} \cup \{\infty\}$. Marked $\infty$-categories are $\infty$-categories with the additional data of a collection of arrows that are meant to be invertible. This is similar to relative categories or stratified simplicial sets. $m$-marked means that all arrows of dimension $> m$ are marked, and the marked arrows are required to be closed under composition, and all identity arrows are marked.

This category $\infty$-Cat$^{+m}$ is equipped with two monoidal closed structures denoted $\ominus$ and $\ominus$ that are both the Gray-Crans tensor product on the underlying strict $\infty$-categories but act differently on markings. These two monoidal structures are meant to respectively be models for the “lax-Gray tensor product” and the “pseudo-Gray tensor product”.

Our main result is the construction of various left semi-model$^1$ structures on $\infty$-Cat$^{+m}$, that are in the same spirit as the canonical (or “folk”) model structure $\infty$-Cat$_{\text{Can}}$ on strict $\infty$-categories from [30], the main one being the saturated inductive model $\infty$-Cat$^{+m}_{\text{Sat-Ind}}$ which is meant to model the homotopy theory of strict $\infty$-categories and serves as toy models for the homotopy theory of weak $(\infty, m)$-categories and $(\infty, \infty)$-categories.

The motivations for this work come from two different places that we will now explain before presenting in more detail the content of this work:

## 1.1 The Street Nerve as a Right Quillen Functor

Complicial sets are a model for weak $(\infty, n)$-categories introduced by Verity in [43]. Concretely, a complicial set is a “stratified simplicial set”, which means that it is a simplicial set where some arrows are marked as being “thin”, which moreover satisfies some filling conditions that refine those for Kan complexes and quasicategories. One essentially recovers Kan complexes when $n = 0$ and quasicategories when $n = 1$. We denote by Strat$^{+m}$ the category of $m$-stratified simplicial sets, i.e., stratified simplicial sets where all simplices of dimension $> m$ are thin. It is equipped with a model structure Strat$^{+m}_{\text{V}}$, which we refer to as the Verity model structure, whose fibrant objects are the complicial sets. More precisely, we will use the “saturated” version of this model structure constructed in [38], which we review in Section 4.4.

$^1$See Appendix A for a quick review of the theory of left semi-model structures.

2

In [32], the second named author has shown that the Street nerve of a strict $\infty$-category can be made into a complicial set by defining the “thin” simplices as those whose top-dimensional arrows are “coinductively” invertible, i.e., admit inverses up to arrows of dimension $(n+1)$ that are themselves invertible up to arrows of dimension $(n+2)$, and so on up to infinity.

From there, it is natural to ask whether this stratified version of the Street nerve also preserves fibrations, and hence is a morphism of categories of fibrant objects (and this will be shown in the present paper as Proposition 4.58).

In fact, more generally, one could ask if it is possible to make this version of the Street nerve into a right Quillen functor (for the Verity model structure on complicial sets from [43]). This is not directly possible simply because this stratified Street nerve is not a right adjoint functor. The solution to this problem is to work with markings on both sides: The usual Street nerve from strict $\infty$-categories to simplicial sets is a right adjoint functor, and one can extend it to a right adjoint functor from marked $\infty$-categories to “marked” simplicial sets (or rather *stratified* simplicial sets to follow the terminology of [43]). In Section 4.4, we show that this functor is indeed a right Quillen functor from the Verity model structure on complicial sets to the saturated inductive semi-model structure on marked $\infty$-categories.

This right Quillen functor from marked $\infty$-categories to stratified simplicial sets is meant to be a model for the forgetful functor from strict $\infty$-categories to weak $(\infty, \infty)$-categories. In particular, the corresponding left Quillen functor from stratified simplicial sets to marked $\infty$-categories is a model for the more mysterious “strictification functor”, sending weak $(\infty, \infty)$-categories to strict $\infty$-categories.

At the level of $\infty$-groupoids, this strictification functor corresponds essentially to (non-abelian) homology, through the equivalence between strict $\infty$-groupoids and crossed chain complexes ([13]) which is well-known to be a conservative functor by Whitehead’s theorem for homology. The first named author has conjectured [28] that more generally this strictification functor should be conservative on weak $(\infty, m)$-categories for all $m$. This allows us to state a concrete version of this conjecture here:

**1.1 Conjecture.** *The left Quillen functor $\downarrow: \mathbf{Strat}_V^{+m} \rightarrow \infty\text{-Cat}_{Sat-Ind}^{+m}$ from Section 4.4 reflects weak equivalences between cofibrant objects.*

## 1.2 The Two (?) Notions of $(\infty, \infty)$-Categories

C. Schommer-Pries and C. Rezk have independently argued ([27]) that there should be more than one notion of weak $(\infty, \infty)$-categories. More precisely, they both arrive at the conclusion that even if one accepts (which seems to be a clear consensus nowadays) that there is only one notion of weak $(\infty, n)$-categories for finite $n$, there are at least two different ways to build a notion of $(\infty, \infty)$-categories out of it.

Before we go into further details, we should say that the following discussion is mostly informal and speculative, and most of it has not been formalized in any models—in fact, one motivation for the present paper is to formalize some of it in the context of strict $\infty$-categories.

First, let us go over the argument put forward by Rezk and Schommer-Pries, or at least how we understand it.

3

Assuming we agree on what the $(\infty, 1)$-category of $(\infty, n)$-categories is for each $n$, the forgetful (or inclusion) functor from $(\infty, n)$-categories to $(\infty, n+1)$-categories is supposed to have both a left adjoint $\pi_n$, which freely adds inverses to all $(n+1)$-arrows, and a right adjoint $\tau_n$ which removes all non-invertible $(n+1)$-arrows. This allows us to produce two different towers of $(\infty, 1)$-categories:

$$(\infty, 0)\text{-Cat} \stackrel{\pi_0}{\leftarrow} (\infty, 1)\text{-Cat} \stackrel{\pi_1}{\leftarrow} (\infty, 2)\text{-Cat} \stackrel{\pi_2}{\leftarrow} \dots \stackrel{\pi_{n-1}}{\leftarrow} (\infty, n)\text{-Cat} \stackrel{\pi_n}{\leftarrow} \dots$$

$$(\infty, 0)\text{-Cat} \stackrel{\tau_0}{\leftarrow} (\infty, 1)\text{-Cat} \stackrel{\tau_1}{\leftarrow} (\infty, 2)\text{-Cat} \stackrel{\tau_2}{\leftarrow} \dots \stackrel{\tau_{n-1}}{\leftarrow} (\infty, n)\text{-Cat} \stackrel{\tau_n}{\leftarrow} \dots$$

and one can take the projective limit of either of these two towers to give a definition of what an $(\infty, \infty)$-category is.

The difference between these two definitions can be seen in the notion of invertibility.

A $k$-arrow of an $(\infty, n)$-category is 'invertible' if it is invertible up to $(k+1)$-arrows, which are themselves invertible up to $(k+2)$-arrows, and so on up to arrows of dimension larger than $n+1$, which are all assumed to be invertible. Therefore, proving that an arrow $c$ is invertible amounts to producing a tower $T_c$ of inverses, witnesses of invertibility, inverses of these witnesses, and so forth, up to arrows of dimension $n+1$. But when $n$ goes to $\infty$, there might be more than one way to define what it means for a cell to be invertible.

We say that an arrow $c$ is *coinductively invertible* when there is such a tower $T_c$ of inverses, witnesses of invertibility, inverses of these witnesses, and so forth, but that never ends. This is, for example, how invertibility is defined in the context of strict $\infty$-categories in [30], or how it is used in [15].

Suppose first that we take the limit of the $\tau$-tower as our definition of an $\infty$-category, that is, an $(\infty, \infty)$-category $X$ corresponds to a collection of $(\infty, n)$-categories $X_n$ such that $X_n \simeq \tau_n X_{n+1}$. Note that, in particular, $X_n$ and $X_{n+1}$ have the same $k$-arrow for $k \leq n$, so we can talk about the set (or space) of $k$-arrows of $X$ for any $k$: it just means the set of $k$-arrows of $X_n$ for any $n \geq k$. In particular, there is another notion of 'invertibility' that is present by definition: an $n$-arrow is said to be invertible if it belongs to $X_{n-1}$. In this case, we say that the arrow is 'inductively invertible.' Note that an arrow that has an inverse up to inductively invertible arrows is itself inductively invertible, but given a coinductively invertible arrow $c$, if none of the arrows of the tower $T_c$ are inductively invertible, the arrow $c$ might not be inductively invertible.

If one takes the definition of the $\pi$-tower as our definition of an $(\infty, \infty)$-category, however, it is quite different: an $(\infty, \infty)$-category in this sense corresponds to a collection of $(\infty, n)$-categories $X_n$ such that $X_n \simeq \pi_n X_{n+1}$. In this definition, if an arrow $c$ is coinductively invertible in the previous sense, with a tower of inverses and witnesses $T_c$, then for each integer $n$, $\pi_n(T_c)$ is a tower of invertibility for the arrow $\pi_n(c)$, which is therefore invertible in $X_n$ for all $n$. Hence, the arrow should be considered invertible in $X$.

To show more precisely that the two limits should really be different, one can for example consider the $(\infty, \infty)$-category of cobordisms (see for example [7]). In the limit of the $\tau$-tower, one can define it by taking $X_n$ to be the $(\infty, n)$-categories of cobordisms—which do satisfy $\tau_n(X_{n+1}) \simeq X_n$ and hence form a well-defined element of the limit of that $\tau$-tower. By definition, this $(\infty, \infty)$-category $X$ is such that $\tau_m(X) = X_m$, so informally, one recovers the $(\infty, m)$-category of cobordisms by dropping the non-invertible arrows of dimension $> m$.

4

But this $(\infty, \infty)$-category of cobordisms also has the property that every arrow in every dimension has a dual, because in the $(\infty, m)$-category of cobordisms, every arrow of dimension strictly inferior to $m - 1$ has a dual. There is a result by E. Cheng (see [15]) that says that (in at least one model) if every arrow has a dual, then every arrow is coinductively invertible. In particular, if one tries to construct a $\pi_m(X)$, i.e., forces all the arrows of $X$ of dimension $> m$ to be invertible, then we will actually make all the arrows of $X$ of all dimensions invertible, so that $\pi_m(X)$ is in fact an $\infty$-groupoid and does not depend on $m$. It follows that any attempt at constructing something like the $(\infty, \infty)$-category of cobordisms, with properties similar to those we can construct in the limit of the $\tau$-tower, will, in the limit of the $\pi$-tower, result in a constant family of $\infty$-groupoids which will not remember the subtle structure of the $(\infty, m)$-category of cobordisms for finite $m$.

Using the saturated inductive left semi-model structures on marked strict $\infty$-categories we construct in this paper, we will make the construction of the $\pi$-tower and of the $\tau$-tower formal in the context of strict $\infty$-categories. See the next subsection for a more detailed account. This is of course only meant to be a toy model for the case of weak $(\infty, \infty)$-categories, but it is already interesting, and it will show that the picture above, while correct, needs to be refined a little.

First, we will show in Section 4.1 that the saturated inductive left semi-model structure $\infty$-Cat$^{+\infty}$ corresponds to the (putative) homotopy limit of the saturated inductive left semi-model structure on $\infty$-Cat$^{+m}$ for $m < \infty$ using the $\tau_n$ functor as transition functors.

Here there is a small gap we should disclaim: The notion of homotopy limit of a tower of model structures from which we have taken inspiration was introduced in [11]. However, they only developed the theory of such limits for Quillen model categories and not left semi-model categories, and we will apply their construction to our left semi-model categories directly.

In order for our argument to be complete despite this, we will prove that the construction from [11] does yield a left semi-model category, but we will not reprove that it corresponds to a homotopy limit as in [11, Theorem 5.1]. For this reason, we will call this construction the *putative limit* of the $\tau$-tower. However, it should be noted that in practice, the argument of [11] seems to carry over to our setting with almost no changes, so this gap is not really a concern.

In Section 4.2, we will show that the canonical model structure is equivalent to a left Bousfield localization $\infty$-Cat$^{+\infty}_{\text{Coind}}$ of $\infty$-Cat$^{+\infty}_{\text{Sat-Ind}}$ which corresponds to turning all coinductively invertible arrows into equivalences.

However, we will also show in Section 4.3 that the canonical model structure is not equivalent to the limit of the $\pi$-tower. More precisely, the natural functor from the canonical model structure to this limit is not an equivalence. It is unclear if the limit of the tower of $\pi_n$ corresponds to a further localization of our model structure, or if it is something entirely different. Nevertheless, we find that the argument we will give in Section 4.3 to distinguish between the canonical model structure and the limit of the $\pi$-tower shows that this limit exhibits behaviors that are not really expected from a notion of $(\infty, \infty)$-categories, or at least are not typical of any known model of $\infty$-categories.

Returning to the world of weak $(\infty, \infty)$-categories, this suggests that the two most interesting notions of weak $(\infty, \infty)$-categories should be the limit

5

of the $\tau_n$ tower, which corresponds to an “inductive” notion of equivalences, and its localization that turns the coinductive equivalences into equivalences$^2$. However, this localization should be different from the limit of the $\pi_n$-tower, which might not be an interesting notion of $(\infty, \infty)$-categories. What we mean here is that we are not aware of any attempt to give a concrete definition of $(\infty, \infty)$-categories that seems to produce something that could be equivalent to this limit.

### 1.3 Overview of the Paper

Finally, we give a short presentation of the contents of the paper, the various model structures, and Quillen functors we will construct. We will assume some familiarity with the theory of left semi-model categories—the necessary material is recalled in Appendix A.

In Section 2.1, we briefly recall the basics of the theory of strict $\infty$-categories, mostly in order to fix our notations. The category $\infty$-Cat$^{+m}$ of $m$-marked $\infty$-categories is introduced in Section 2.2, and in Section 2.3 we introduce the two monoidal structures $\ominus$ and $\ominus$ on $\infty$-Cat$^{+m}$, which both correspond to the Gray-Crans tensor products at the level of the underlying strict $\infty$-categories but behave differently on the markings. $\ominus$ is meant to correspond to the Lax Gray-Crans tensor product, while $\ominus$ corresponds to the pseudo Gray-Crans tensor product.

Next, in Section 2.4, exploiting these monoidal structures, we set up the first left semi-model structure on $\infty$-Cat$^{+m}$, which we call the *inductive* model structure, whose properties are summarized in:

**1.2 Theorem.** *For any $m \in \mathbb{N} \cup \{\infty\}$, there is a combinatorial left semi-model structure on the category $\infty$-Cat$^{+m}$ of $m$-marked $\infty$-categories, called the inductive or unsaturated inductive model structure and denoted $\infty$-Cat$^{+m}_{ind}$, such that:*

- *This model structure is monoidal for both tensor products $\ominus$ and $\ominus$ (from Section 2.3).*
- *The cofibrations are the maps that are cofibrations of the canonical model structure between the underlying $\infty$-categories. (Proposition 2.34)*
- *The fibrant objects are the marked $\infty$-categories in which all marked arrows admit marked inverses up to higher marked arrows, and in which if there is a marked arrow $a \rightarrow b$, then $a$ is marked if and only if $b$ is marked.*
- *Fibrations between fibrant objects are the “isofibrations” (as defined in Section 3.3).*
- *Weak equivalences between fibrant objects are “equivalences of marked $\infty$-categories” (as defined in Section 3.4).*

The existence of this model structure is established in Section 2.4, but some of its properties, in particular, the characterization of fibrant objects and fibrations between fibrant objects, will only be established in Section 3.

This model structure is intended as a model for “strict $(\infty, m)$-categories”, i.e., strict $\infty$-categories whose arrows of dimension strictly superior to $m$ are

$^2$Provided that we can define the notion of coinductively invertible arrow in a “model independent” way, which is not investigated in this article.

6

invertible in a weak sense. In this interpretation, marked arrows should correspond to weakly invertible arrows. When $m = \infty$, it still retains an 'inductive' notion of invertibility, like what is expected of the limit of the $\tau$-tower as mentioned in Section 1.2.

However, it is not quite the case yet due to a small defect: Given $X$ a fibrant object, there might be arrows in $X$ that are invertible up to higher marked arrows without being marked themselves. Hence, the fibrant objects are carrying an additional piece of data compared to what $(\infty, n)$-categories should be: some of their invertible arrows are marked and others are not.

To solve this problem, in Section 3.5 we consider a left Bousfield localization $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$, called the *saturated inductive model structure*, in which the fibrant objects are the marked $\infty$-categories in which an arrow is marked if and only if it is invertible up to higher-dimensional marked arrows. These are really our intended model for strict $(\infty, n)$-categories. So we have a first (identity) left Quillen functor:

$$\infty\text{-Cat}_{\text{Ind}}^{+m} \rightarrow \infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$$

We consider the saturated inductive model structure $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$ to be the most interesting one, as it actually models strict $(\infty, m)$-categories. The only reason we use $\infty\text{-Cat}_{\text{Ind}}^{+m}$ is because it is the one that naturally arises from our construction in Section 2.4. It is not completely clear to us what $\infty\text{-Cat}_{\text{Ind}}^{+m}$ actually models at a homotopy theoretic level.

In Section 4.1, we study how these model structures relate when $m$ varies. We show that for $m < p \leqslant \infty$, the obvious inclusion functor $\iota_p: \infty\text{-Cat}^{+m} \subset \infty\text{-Cat}^{+p}$ has both a left adjoint $\pi_m$ and a right adjoint $\tau_m: \infty\text{-Cat}^{+p} \rightarrow \infty\text{-Cat}^{+m}$. We show that these form two Quillen adjunctions $(\pi_m \dashv \iota_p)$ and $(\iota_p \dashv \tau_m)$ between the saturated inductive model structures.

We also investigate how the saturated inductive model structure $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$ can be understood as a certain limit of the tower of right Quillen functors

$$\infty\text{-Cat}_{\text{Sat-Ind}}^{+0} \stackrel{\tau_n}{\leftarrow} \infty\text{-Cat}_{\text{Sat-Ind}}^{+1} \stackrel{\tau_1}{\leftarrow} \infty\text{-Cat}_{\text{Sat-Ind}}^{+2} \stackrel{\tau_2}{\leftarrow} \dots \stackrel{\tau_{\ell-1}}{\leftarrow} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n} \stackrel{\tau_n}{\leftarrow} \dots$$

as explained previously.

Next, in Section 4.2, in the case where $m = +\infty$, we can take a further left Bousfield localization, which we study in Section 4.2, called the coinductive model structure, denoted $\infty\text{-Cat}_{\text{Coind}}^{+\infty}$, whose fibrant objects are marked $\infty$-categories where the marked arrows are exactly the 'coinductively invertible arrows' (see Definition 4.16):

$$\infty\text{-Cat}_{\text{Ind}}^{+\infty} \rightarrow \infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty} \rightarrow \infty\text{-Cat}_{\text{Coind}}^{+\infty}$$

Of course, we can also try to define $\infty\text{-Cat}_{\text{Coind}}^{+m}$ for finite $m$, but this is the same as $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$.

This second localization $\infty\text{-Cat}_{\text{Coind}}^{+\infty}$ is in fact equivalent to the canonical model structure on $\infty$-categories $\infty\text{-Cat}_{\text{Can}}$ from [30], in a fairly strong sense: the functor

$$\begin{array}{ccc} \infty\text{-Cat}_{\text{Can}} & \rightarrow & \infty\text{-Cat}_{\text{Coind}}^{+\infty} \\ C & \mapsto & C^\circ \end{array}$$

where $C^\circ$ is the minimal marking (i.e., only the identity arrows are marked) defined in Example 2.16, is a left Quillen equivalence. Its right adjoint (the

7

forgetful functor $\infty\text{-Cat}^{+\infty} \rightarrow \infty\text{-Cat}$) induces an equivalence of categories between the categories of fibrant objects that preserves and detects weak equivalences and fibrations (between fibrant objects). Thus, their categories of fibrant objects are literally the same, with the same fibrations and weak equivalences.

Finally, in Section 4.4, we study a marked version of the Street nerve. The usual Street Nerve is the right adjoint functor $N_{\mathcal{O}}: \infty\text{-Cat} \rightarrow \mathbf{sSet}$, defined using Street's Orientals $\mathcal{O}: \Delta \rightarrow \infty\text{-Cat}$, where $N_{\mathcal{O}}(X)_n = \text{Hom}(\mathcal{O}[n], X)$. We extend it to a Nerve/realization Quillen adjunction:

$$|-|: \mathbf{Strat}_{\text{V}}^{+m} \leftrightarrows \infty\text{-Cat}_{\text{Sat-Ind}}^{+m}: N$$

where $\mathbf{Strat}_{\text{V}}^{+m}$ is the category of $m$-marked simplicial sets equipped with the (saturated) Verity model structure from [43] and [38], which we review in Section 4.4. As explained above, this generalizes the results of the second named author from [32].

## 2 $\infty$-Categories and Marked $\infty$-Categories

### 2.1 $\infty$-Categories

A globular set is a presheaf on the globular category $\mathbb{G}$:

$$\mathbb{D}_0 \xrightarrow[i_0]{i_0^+} \mathbb{D}_1 \xrightarrow[i_1]{i_1^+} \mathbb{D}_2 \xrightarrow[i_2]{i_2^+} \mathbb{D}_3 \xrightarrow[i_3]{i_3^+} \mathbb{D}_4 \dots$$

with the relations $i_n^+ i_{n-1}^\epsilon = i_n^- i_{n-1}^\epsilon$ for any $n > 0$ and $\epsilon \in \{+, -\}$. For any $n > k$ and $\epsilon \in \{+, -\}$, we also denote by $i_k^\epsilon$ the composite $\mathbb{D}_k \xrightarrow{i_k^\epsilon} \mathbb{D}_{k+1} \xrightarrow{f} \mathbb{D}_n$ where $f$ is any map. These and the identity arrows are the only maps in the category $\mathbb{G}$.

**2.1 Notation.** If $X$ is a globular set, one denotes by $X_n$ the set $X(\mathbb{D}_n)$. The map $X_n \rightarrow X_k$ induced by $i_k^\epsilon: \mathbb{D}_k \rightarrow \mathbb{D}_n$ is denoted by $\pi_k^\epsilon$.

**2.2 Definition.** Let $X$ be a globular set and $n$ a positive integer. A $n$-arrow of $X$ is an element of $X_n$.

A *arrow of $X$* is an element of $\prod_{k \geq 0} X_k$. If $a$ is an arrow of $X$, its *dimension* is the integer $n$ such that $a$ belongs to $X_n$.

If $a$ is an $n$-arrow of $X$ and $k$ an integer strictly less than $n$, the $k$-*source of $a$* is the $k$-arrow $\pi_k^-(a)$ and the $k$-*target of $a$* is the $k$-arrow $\pi_k^+(a)$.

**2.3 Definition.** An $\infty$-*category* is a globular set $X$ together with operations of *compositions*

$$X_n \times_{X_k} X_n \rightarrow X_n \quad (0 \leq k < n)$$

which associates to two $n$-arrows $(x, y)$ verifying $\pi_k^+(x) = \pi_k^-(y)$, one $n$-arrow $x \#_k y$, as well as *identities*

$$X_n \rightarrow X_{n+1}$$

associating to an $n$-arrow $x$, an $(n+1)$-arrow $\mathbb{I}_x$, and satisfying the following axioms:

8

(1) $\forall x \in X_n, \pi_n^e(\mathbb{I}_x) = x$.

(2) $\pi_k^-(x\#_ky) = \pi_k^-(x)$ and $\pi_k^+(x\#_ky) = \pi_k^+(y)$ whenever the composition is defined and $k \leqslant n$.

(3) $\pi_k^e(x\#_ky) = \pi_k^e(x)\#_k\pi_k^e(y)$ whenever the composition is defined and $k > n$.

(4) $x\#_k\mathbb{I}_{\pi_k^+x} = x$ and $\mathbb{I}_{\pi_k^-x}\#_kx = x$.

(5) $(x\#_ky)\#_kz = x\#_k(y\#_kz)$ as soon as one of these is defined.

(6) If $k < n$

$$(x\#_ky)\#_k(z\#_kw) = (x\#_kz)\#_k(y\#_kw)$$

when the left-hand side is defined.

A morphism of $\infty$-categories is a map of globular sets commuting with both operations. The category of $\infty$-categories is denoted $\infty$-Cat.

**2.4 Definition.** An $(n+1)$-arrow $c$ in an $\infty$-category is said to be *trivial*, or an *identity arrow*, if there exists an $n$-arrow $d$ such that $c = \mathbb{I}_d$.

**2.5 Example.** By abuse of notation, we also denote $\mathbb{D}_n$ as the $\infty$-category that admits for any $k < n$ only two non-trivial $k$-arrows, denoted $e_k^-$ and $e_k^+$, and a single non-trivial $n$-arrow, denoted $e_n$, satisfying:

$$\begin{array}{l} \pi_l^-(e_k^e) = e_l^- \quad \pi_l^+(e_k^e) = e_l^+ \quad \text{for } l \le k < n \\ \pi_l^-(e_n) = e_l^- \quad \pi_l^+(e_n) = e_l^+ \quad \text{for } l \le n \end{array}$$

The $\infty$-category $\partial\mathbb{D}_n$ is obtained from $\mathbb{D}_n$ by removing the $n$-arrow $e_n$. We thus have a morphism

$$i_n: \partial\mathbb{D}_n \to \mathbb{D}_n.$$

Note that $\partial\mathbb{D}_0 = \emptyset$.

**2.6 Definition.** If $X$ is an $\infty$-category, we define the globular set $\Sigma X$, called the *suspension of $X$*, by the formula

$$(\Sigma X)_0 = \{a, b\}, \quad (\Sigma X)_{n+1} := X_n \cup \{\mathbb{I}^n a, \mathbb{I}^n b\},$$

where $\mathbb{I}_a^n$ (resp. $\mathbb{I}_b^n$) is the $n$-times iterated identity of $a$ (resp. of $b$). Moreover, $\Sigma X$ inherits from $X$ a structure of an $\infty$-category.

Eventually, for an integer $n$, we define the $\infty$-category $\Sigma^n X$, called the *n-suspension of $X$*, as the $n$-times iterated suspension of $X$.

Next, we define the notion of polygraphs, first introduced under the name "computads" by R. Street in [41] for 2-categories, with the general notion being hinted at in [42]. As far as we know, the first formal introduction of polygraphs in the literature is in [37] and independently in [14], where the name "polygraphs" was introduced. Here we will exploit that the category of polygraphs identifies with a (non-full) subcategory of $\infty$-Cat to give a shorter definition. We refer to the references above for a more complete introduction.

9

## 2.7 Definition.

- We say that an $\infty$-category $X$ is a polygraph if it can be constructed from the empty $\infty$-category by freely adding arrows with specified source and target. That is, $X$ can be obtained as a transfinite composition $\emptyset = X_0 \to X_1 \to \cdots \to X_i \to \operatorname{Colim} X_i = X$, where for each $i$, the map $X_i \to X_{i+1}$ is a pushout of $\coprod_S \partial \mathbb{D}_n \to \coprod_S \mathbb{D}_{n+1}$.
- An arrow of a polygraph is said to be a *generator* if it is one of the arrows that has been freely added at some stage.
- A morphism of $\infty$-categories between two polygraphs is said to be a *morphism of polygraphs* or a *polygraphic morphism* if it sends each generator to a generator.
- An $n$-polygraph is a polygraph whose generators are all of dimension less than or equal to $n$.

**2.8 Remark.** Generators of a polygraph can be shown to be exactly the arrows that cannot be written as a composite in a non-trivial way$^3$, see 16.6.1 and 16.6.2 in [4].

So, the notion of generator does not depend on the choice of the presentation of $X$, and any isomorphism between polygraphs is automatically polygraphic, see 16.6.3 in [4].

**2.9 Example.** The only $n$-polygraph for $n < 0$ is the empty $\infty$-category. The category of 0-polygraphs is equivalent to the category of sets and corresponds to discrete $\infty$-categories. The category of 1-polygraphs (and polygraphic morphisms between them) is equivalent to the category of directed graphs, and they correspond to categories that are free on a graph.

We will sometimes distinguish between a polygraph seen as an object of the category of polygraphs and polygraphic morphisms, and the corresponding $\infty$-category, which we call the free $\infty$-category on the polygraph.

**2.10 Remark.** Each arrow in a polygraph can be written as an iterated composite of the generators (not necessarily in a unique way). For an $n$-arrow $f$, the set of generators of dimension $n$ that appear in such an expression, and even the number of times they appear, is the same for all such expressions, see section 4.3 of [35]. We will say that an $n$-generator *appears* in an $n$-arrow if it appears in any such expression.

**2.11 Construction.** The category $\infty$-Cat admits a closed monoidal structure, called the Gray tensor product or Crans-Gray tensor product, which we denote as

$$\begin{array}{c c c} \infty\text{-Cat} \times \infty\text{-Cat} & \to & \infty\text{-Cat} \\ X, Y & \mapsto & X \otimes Y \end{array}$$

Its explicit construction is very involved, and we will assume the reader is already familiar with it. It was first introduced by S. Crans in his Ph.D. thesis [16]. We refer to [1] for an introduction to this tensor product close to its original definition, and to [40] for a more modern account. The proof of the existence of this monoidal structure in [40] contains some gaps that have been fixed in Appendix A of [6].

$^3$The trivial ones being decompositions involving units, such as the decompositions $u = u\#_i \mathbb{I}_{u_i^+ u}^k = \mathbb{I}_{u_i^- u}^k \#_i u$.

10

It is easy to see from either of these definitions that $\mathbb{D}_n \otimes \mathbb{D}_m$ has a unique non-trivial arrow of dimension $n + m$. If $f$ and $g$ are respectively an $n$-arrow of $X$ and an $m$-arrow of $Y$, which correspond to morphisms $f: \mathbb{D}_n \to X$ and $g: \mathbb{D}_m \to Y$, we denote by $f \otimes g$ the $(m + n)$-arrow of $X \otimes Y$ obtained as the image of this non-trivial $(n + m)$-arrow by the functor $f \otimes g: \mathbb{D}_n \otimes \mathbb{D}_m \to X \otimes Y$.

**2.12 Example.** The following description of $\mathbb{D}_1 \otimes \mathbb{D}_n$ comes from Appendix B.1 of [6] (see Proposition B.1.4): As a polygraph, the generating arrows of $\mathbb{D}_1 \otimes \mathbb{D}_n$ are:

$$a_0^- \otimes e_k^\epsilon \quad a_0^+ \otimes e_k^+ \quad a \otimes e_k^\epsilon$$

where the arrows of $\mathbb{D}_1$ have been denoted “$a$” instead of “$e$” to distinguish them, and $\epsilon$ is either $+$ or $-$, $k \leqslant n$, and $e_n^+ = e_n^-$. Their source and target are given as follows:

$$\begin{aligned} \pi^-(a_0^- \otimes e_k^\epsilon) &= a_0^- \otimes e_{k-1}^- & \pi^+(a_0^- \otimes e_k^\epsilon) &= a_0^- \otimes e_{k-1}^+ \\ \pi^-(a_0^+ \otimes e_k^\epsilon) &= a_0^+ \otimes e_{k-1}^- & \pi^+(a_0^+ \otimes e_k^\epsilon) &= a_0^+ \otimes e_{k-1}^+ \\ \pi^-(a \otimes e_k^\epsilon) &= (a_0^- \otimes e_k^\epsilon)\#_0(a \otimes e_0^+)\#_1 \dots \#_{k-1}(a \otimes e_{k-1}^+) \\ \pi^+(a \otimes e_k^\epsilon) &= (a \otimes e_{k-1}^-)\#_{k-1} \dots \#_1(a \otimes e_0^-)\#_0(a_0^+ \otimes e_k^\epsilon) \end{aligned}$$

We did not put parentheses in the expressions above to keep them shorter; the default convention is to perform the composition $\#_i$ in order of increasing values of $i$. The last two equations are given by Proposition B.1.4 of [6], though note that this reference uses a different convention than ours regarding the composition order.

We recall from Theorem 1.35 of [19] or from [5]:

**2.13 Proposition.** *If $X$ and $Y$ are polygraphs, then $X \otimes Y$ is also a polygraph. The $n$-generators of $X \otimes Y$ are the arrows of the form $x \otimes y$, where $x$ and $y$ are respectively a $(n - k)$-generator of $X$ and a $k$-generator of $Y$, with $k \leq n$.*

**2.14 Lemma.** *Let $X$ and $Y$ be $\infty$-categories. The $\infty$-category $X \otimes Y$ is generated by composition of $n$-arrows of the shape $x \otimes y$, where $x$ and $y$ are respectively an $(n - k)$-arrow of $X$ and a $k$-arrow of $Y$, with $k \leq n$.*

*Proof.* Remark first that given a diagram $F: I \to \infty$-Cat such that, for any $i \in I$, $F(i)$ is generated by composition from a set $M_i$, then the $\infty$-category $\text{Colim}_{i \in I} F_i$ is generated by composition from the set $\cup_{i \in I} f_i(M_i)$ where $f_i$ is the canonical map $f(i): F(i) \to \text{Colim}_{i \in I} F_i$.

Secondly, Theorem 1.12 of [10] states that a certain subcategory of $\infty$-Cat, denoted by $\Theta$ and whose objects are polygraphs, is dense. As the Gray tensor product preserves colimits, the previous remark implies that we can reduce to the case where $X$ and $Y$ are elements of $\Theta$, and so in particular polygraphs. The result then follows from Proposition 2.13. $\square$

Finally, we recall from [30] that $\infty$-Cat carries a model structure, called the canonical model structure, in which every object is fibrant and where the generating cofibrations are the maps $\partial \mathbb{D}_n \to \mathbb{D}_n$. Its weak equivalences are a natural class of equivalence of $\infty$-categories that generalizes the equivalences of ordinary categories. It was shown in [35] that the cofibrant objects are exactly the polygraphs, and it also follows from this that the cofibrations between cofibrant objects are the polygraphic inclusions. It was shown in [5] that this model structure is a monoidal model structure for the Gray tensor product.

11

## 2.2 Marked $\infty$-Categories

For the rest of the article, we fix an $m \in \mathbb{N} \cup \{\infty\}$.

**2.15 Definition.** An $m$-marked $\infty$-category is an $\infty$-category $X$, together with a set $M \subset \prod_{k>0} X(k)$ of arrows of positive dimension called *marked* arrows such that:

- All identity arrows $\mathbb{I}_x$ are marked.
- All arrows of dimension strictly greater than $m$ are marked.
- If $x$ and $y$ are marked $n$-arrows and $x\#_k y$ is defined, then $x\#_k y$ is marked.

A morphism of $m$-marked $\infty$-categories is a morphism between the underlying $\infty$-categories that sends marked arrows to marked arrows. The category of $m$-marked $\infty$-categories is denoted $\infty$-Cat$^{+m}$.

Note that if $m = \infty$, then the second condition of the definition simply disappears; this is the main case we are interested in.

**2.16 Example.** If $X$ is an $\infty$-category, we denote by $X^\#$ the $m$-marked $\infty$-category $(X, X_{>0})$ where all arrows of positive dimension are marked. We denote by $X^\flat$ the $m$-marked $\infty$-category where only identity arrows and $k$-arrows for $k > m$ are marked.

**2.17 Notation.** To simplify notation and when there is no confusion, the marked $\infty$-category $X^\flat$ will simply be denoted as $X$.

**2.18 Construction.** If $X$ is an $\infty$-category and $M \subset \prod_{k>0} X_k$ is a set of arrows of $X$, we denote by $\overline{M}$ the smallest set of arrows such that $M \subset \overline{M}$ and $(X, \overline{M})$ is an $m$-marked $\infty$-category. That is, $\overline{M}$ is the union of the set of arrows of dimension strictly greater than $m$ and the set of all $n$-arrows that can be written as iterated composites of $n$-arrows in $M$ and arrows of the form $\mathbb{I}_x$ for $x$ an $(n-1)$-arrow. For example, $X^\flat = (X, \emptyset)$.

**2.19 Construction.** The category of $m$-marked $\infty$-categories has all colimits, and they are easily described in terms of colimits of $\infty$-categories and of Construction 2.18: if $(X_i, M_i)_{i \in I}$ is a diagram of $m$-marked $\infty$-categories indexed by a category $I$, then:

$$\operatorname{Colim}_{i \in I}(X_i, M_i) = \left( \operatorname{Colim}_{i \in I} X_i, \overline{\cup_i f_i(M_i)} \right)$$

where $f_i$ denotes the canonical map $f_i: X_i \rightarrow \operatorname{Colim}_{i \in I} X_i$ and $f_i(M_i)$ is simply the set of arrows of the form $f_i(x)$ for $x \in M_i$.

This is easily shown by checking that the right-hand side has the universal property of the colimit.

**2.20 Remark.** Theorem 1.12 of [10] identifies a small full subcategory of $\infty$-Cat, denoted $\Theta$, which is dense. We denote by $\Theta^{+m}$ the full subcategory of $\infty$-Cat$^{+m}$ whose objects are of the form $(C, M)$ with $C$ in $\Theta$. From the description of colimits of $m$-marked $\infty$-categories given in Construction 2.19, it follows that $\Theta^{+m}$ is dense in $\infty$-Cat$^{+m}$. Moreover, as objects of $\Theta^{+m}$ have a finite number of non trivial cells, they are $\omega$-small. It follows that $\infty$-Cat$^{+m}$ is locally finitely presentable.

12

## 2.3 Tensor Product of $m$-Marked $\infty$-Categories

In this section, we construct two monoidal closed structures on the category of $m$-marked $\infty$-categories, respectively called the *pseudo-Gray* tensor product $\ominus$ and the *lax-Gray* tensor product $\ominus$. Both are obtained by putting different markings on the Gray tensor product from Construction 2.11. For example, the lax-Gray tensor product $\mathbb{D}_1 \ominus \mathbb{D}_1$ is $C_1^*$,

$$C_1 = \begin{pmatrix} \bullet & \longrightarrow & \bullet \\ \downarrow & \swarrow & \downarrow \\ \bullet & \longrightarrow & \bullet \end{pmatrix}$$

while $\mathbb{D}_1 \ominus \mathbb{D}_1$ is the $m$-marked polygraph $(C_1, \overline{D})$, where $D$ only contains the unique 2-dimensional generator of $C_1$. So, unless $m = 0$ or $m = 1$, the two tensor products are distinct. At the derived or homotopy-theoretic level, the pseudo-Gray tensor product should correspond to the Cartesian product.

The formal definition is as follows:

**2.21 Construction.** Given two $m$-marked $\infty$-categories $(X, M)$ and $(Y, N)$, we define two sets of arrows in $X \otimes Y$:

- $M \ominus N$ is the set of arrows of the form $x \otimes y \in X \otimes Y$ where either $x \in M$ or $y \in N$.
- $M \ominus N$ contains all arrows in $M \ominus N$ together with all arrows of the form $x \otimes y$ with $x$ and $y$ both of dimension strictly greater than 0.

Note that $M \ominus N$ and $M \ominus N$ are not markings on $X \otimes Y$: they are not stable under composition. So we define:

$$(X, M) \ominus (Y, N) = (X \otimes Y, \overline{M \ominus N})$$

$$(X, M) \ominus (Y, N) = (X \otimes Y, \overline{M \ominus N})$$

We will show in Lemma 2.42 that both make the category of $m$-marked $\infty$-categories into a monoidal closed category.

In order to show this, it is convenient to introduce the following notations:

**2.22 Notation.** For $A$ and $B$ subsets of arrows in $\infty$-categories, we denote by $A \otimes B$ the set of arrows of the form $a \otimes b \in X \otimes Y$ for $a \in A$ and $b \in B$. For an $\infty$-category $X$, we denote by $X_{\geq 0}$ the set of all arrows of $X$ and by $X_{>0}$ the set of all arrows of dimension strictly greater than 0. We can hence, for $(X, M)$ and $(Y, N)$ two $m$-marked $\infty$-categories, rewrite the definitions above as:

$$\begin{aligned} M \ominus N &= (M \otimes Y_{\geq 0}) \cup (X_{\geq 0} \otimes N) \\ M \ominus N &= (M \ominus N) \cup (X_{>0} \otimes Y_{>0}) \\ &= (M \otimes Y_{\geq 0}) \cup (X_{\geq 0} \otimes N) \cup (X_{>0} \otimes Y_{>0}) \end{aligned}$$

By definition of the Gray tensor product, we have the following result:

**2.23 Lemma.** *Let $X$ and $Y$ be two $\infty$-categories. Then:*

$$\begin{aligned} \overline{X_{\geq 0} \otimes Y_{\geq 0}} &= (X \otimes Y)_{\geq 0} \\ \overline{X_{>0} \otimes Y_{\geq 0} \cup X_{\geq 0} \otimes Y_{>0}} &= (X \otimes Y)_{>0}. \end{aligned}$$

13

*Proof.* The first equality corresponds to the fact that $X \otimes Y$ is generated under composition by arrows of the form $x \otimes y$, as proven in Lemma 2.14. The second equality corresponds to the fact that arrows of dimension strictly greater than 0 in $X \otimes Y$ are generated under composition by arrows of the form $x \otimes y$ where either $x$ or $y$ has dimension strictly greater than 0, which directly follows from the previous claim, and from the fact that $x \otimes y$ is of dimension strictly greater than 0 if at least one of $x$ or $y$ is. $\square$

**2.24 Lemma.** *Let $X$ be an $\infty$-category and $M, N$ be two subsets of arrows of $X$. Then:*

$$\overline{M \cup N} = \overline{\overline{M} \cup N} = \overline{M \cup \overline{N}} = \overline{\overline{M} \cup \overline{N}}$$

*Proof.* This is straightforward. $\square$

**2.25 Lemma.** *Let $X$ and $Y$ be two $\infty$-categories and $M \subset X_{\geq 0}$ and $N \subset Y_{\geq 0}$. Then:*

$$\overline{M \otimes N} = \overline{\overline{M} \otimes N} = \overline{M \otimes \overline{N}} = \overline{\overline{M} \otimes \overline{N}}$$

*Proof.* We will only show the equality $\overline{M \otimes N} = \overline{\overline{M} \otimes \overline{N}}$. The equality $\overline{M \otimes N} = \overline{\overline{M} \otimes \overline{N}}$ can be proved in the same way, and the last equality follows immediately by applying the result to $M$ and $\overline{N}$.

We will also only prove the results for $m = \infty$; the case of a general $m$ follows immediately as it marks all arrows of dimension strictly greater than $m$ on each side of these equalities.

The evident inclusion $M \subset \overline{M}$ implies $\overline{M \otimes N} \subset \overline{\overline{M} \otimes \overline{N}}$, so it is enough to show that $\overline{M} \otimes N \subset \overline{\overline{M} \otimes \overline{N}}$.

Let $K$ be the set of arrows $k$ in $X$ such that $k \otimes n \in \overline{M \otimes N}$ for all $n \in N$. We need to show that $K$ is closed under identity and composition to finish the proof.

If $k = \mathbb{I}_x$, then $k \otimes n = \mathbb{I}_{x \otimes n} \in \overline{M \otimes N}$. Let now $k, k' \in K$ of dimension $n$ such that $k \#_i k'$ is defined. They are encoded by a map $\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n \to X$, and let $y \in N$ be an arrow of dimension $m$ in $Y$, encoded by a map $\mathbb{D}_m \to Y$.

Together these induce a map $e: (\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n) \otimes \mathbb{D}_m \to X \otimes Y$. $(\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n) \otimes \mathbb{D}_m$ is a polygraph of dimension $m + n$ with only two generating arrows of maximal dimensions that are sent to $k \otimes y$ and $k' \otimes y$, which are by hypothesis in $\overline{M \otimes N}$.

Now the arrow corresponding to $(k \#_i k') \otimes y$ in $(\mathbb{D}_n \coprod_{\mathbb{D}_n} \mathbb{D}_n) \otimes \mathbb{D}_m$ is in $\overline{M \otimes N}$ as all the top-dimensional generators that appear in it are in $\overline{M \otimes N}$. We have proved that $k \#_i k' \otimes y \in \overline{M \otimes N}$ for all $y \in N$, hence $k \#_i k' \in K$ and this concludes the proof. $\square$

**2.26 Lemma.** *Let $X, Y$ be two $\infty$-categories, $M \subset X_{\geq 0}$ and $N \subset Y_{\geq 0}$. Then we have*

$$\begin{array}{rcl} \overline{M \ominus N} & = & \overline{\overline{M} \ominus \overline{N}} \\ \overline{M \ominus N} & = & \overline{\overline{M} \ominus \overline{N}}. \end{array}$$

*Proof.* Given the formula for $M \ominus N$ and $M \ominus N$ from Notation 2.22, this is a direct consequence of Lemma 2.24 and Lemma 2.25. $\square$

14

**2.27 Lemma.** Let $X, Y, Z$ be three $\infty$-categories, $M \subset X_{>0}$, $N \subset Y_{>0}$ and $P \subset Z_{>0}$. Then we have

$$\begin{array}{rcl} \overline{(M \ominus N) \ominus P} & = & \overline{M \ominus (N \ominus P)} \\ \overline{(M \ominus N) \ominus P} & = & \overline{M \ominus (N \ominus P)} \end{array}$$

*Proof.* We begin with the first equality. Let

$$E := (M \otimes Y_{\geqslant 0} \otimes Z_{\geqslant 0}) \cup (X_{\geqslant 0} \otimes N \otimes Z_{\geqslant 0}) \cup (X_{\geqslant 0} \otimes Y_{\geqslant 0} \otimes P).$$

The lemmas 2.23, 2.24, and 2.25 imply the following equalities:

$$\begin{aligned} \overline{E} & = \overline{M \otimes Y_{\geqslant 0} \otimes Z_{\geqslant 0}} \cup X_{\geqslant 0} \otimes (N \otimes Z_{\geqslant 0} \cup Y_{\geqslant 0} \otimes P) \\ & = \overline{M \otimes (Y \otimes Z)_{\geqslant 0}} \cup X_{\geqslant 0} \otimes (N \ominus P) \\ & = \overline{M \ominus (N \ominus P)} \end{aligned}$$

A very similar computation also shows that $\overline{E} = \overline{(M \ominus N) \ominus P}$, which concludes the proof of the first equality.

For the second equality, we define

$$F := (X_{\geqslant 0} \otimes Y_{>0} \otimes Z_{>0}) \cup (X_{>0} \otimes Y_{\geqslant 0} \otimes Z_{>0}) \cup (X_{>0} \otimes Y_{>0} \otimes Z_{\geqslant 0})$$

The second equality of Lemma 2.23 implies that:

$$\overline{F} = \overline{X_{\geqslant 0} \otimes Y_{>0} \otimes Z_{>0} \cup X_{>0} \otimes (Y \otimes Z)_{>0}}$$

and then that

$$\begin{aligned} \overline{E \cup F} & = \overline{M \otimes (Y \otimes Z)_{\geqslant 0}} \cup X_{\geqslant 0} \otimes (N \ominus P) \cup X_{>0} \otimes (Y \otimes Z)_{>0} \\ & = \overline{M \ominus (N \ominus P)} \end{aligned}$$

and here again, a similar computation shows $\overline{E \cup F} = \overline{(M \ominus N) \ominus P}$, which concludes the proof. $\square$

**2.28 Lemma.** Let $X$ be an $\infty$-category, $M \subset X_{>0}$. Then the empty set, considered as a subset of the $\infty$-category $\mathbb{D}_0$, satisfies (up to the identifications $\mathbb{D}_0 \otimes X \simeq X \otimes \mathbb{D}_0 \simeq X$):

$$\begin{array}{l} \emptyset \ominus M = M \ominus \emptyset = M \\ \overline{\emptyset \ominus M} = \overline{M \ominus \emptyset} = \overline{M} \end{array}$$

*Proof.* The first equality is a straightforward application of the definition of $\ominus$. For the second case, we also use the fact that all arrows of $(\mathbb{D}_0)_{>0} \otimes X_{>0}$ are identities and so all belong to $\overline{M}$. $\square$

**2.29 Proposition.** Both the *lax-Gray tensor product* $\ominus$ and the *pseudo-Gray tensor product* $\ominus$, as defined above, are monoidal structures on the category of $m$-marked $\infty$-categories. In both cases, the forgetful functor to $\infty$-categories is monoidal, and their unit is $\mathbb{D}_0^{\flat} = \mathbb{D}_0^{\#}$.

*Proof.* Note that $\mathbb{D}_0^{\flat} = \mathbb{D}_0^{\#} = (\mathbb{D}_0, \overline{\emptyset})$ as all arrows of $\mathbb{D}_0$ of dimension strictly superior to 0 are identities.

15

The proposition states that the structural maps (associativity and unit isomorphisms) of the Gray tensor product of $\infty$-categories preserve the marking we specified on the tensor product.

For the unit, let $(X, M)$ be an $m$-marked $\infty$-category. The Lemmas 2.25 and 2.28 imply that

$$\begin{aligned} (X, M) \ominus (\mathbb{D}_0, \overline{\emptyset}) &= (X \otimes \mathbb{D}_0, \overline{M \ominus \emptyset}) &= (X, M) \\ (X, M) \ominus (\mathbb{D}_0, \overline{\emptyset}) &= (X \otimes \mathbb{D}_0, \overline{M \ominus \emptyset}) &= (X, M) \end{aligned}$$

and

$$\begin{aligned} (\mathbb{D}_0, \overline{\emptyset}) \ominus (X, M) &= (\mathbb{D}_0 \otimes X, \overline{\emptyset \ominus M}) &= (X, M) \\ (\mathbb{D}_0, \overline{\emptyset}) \ominus (X, M) &= (\mathbb{D}_0 \otimes X, \overline{\emptyset \ominus M}) &= (X, M) \end{aligned}$$

For the associativity isomorphism, let $(X, M)$, $(Y, N)$, and $(Z, P)$ be three marked $\infty$-categories. Lemma 2.25 implies that

$$\begin{aligned} \big((X, M) \ominus (Y, N)\big) \ominus (Z, P) &= (X \otimes Y \otimes Z, \overline{(M \ominus N) \ominus P}) \\ \big((X, M) \ominus (Y, N)\big) \ominus (Z, P) &= (X \otimes Y \otimes Z, \overline{(M \ominus N) \ominus P}) \end{aligned}$$

and

$$\begin{aligned} (X, M) \ominus \big((Y, N) \ominus (Z, P)\big) &= (X \otimes Y \otimes Z, \overline{M \ominus (N \ominus P)}) \\ (X, M) \ominus \big((Y, N) \ominus (Z, P)\big) &= (X \otimes Y \otimes Z, \overline{M \ominus (N \ominus P)}) \end{aligned}$$

Lemma 2.27 shows that these two markings on $X \otimes Y \otimes Z$, in the lax and pseudo cases, coincide. $\square$

**2.30 Proposition.** *The pseudo and lax-Gray tensor products $\ominus$ and $\ominus$ preserve colimits in each variable.*

*Proof.* It follows from the fact that the Gray tensor product $\otimes$ preserves colimits in each variable, the description of colimits of $m$-marked $\infty$-categories given in Construction 2.19, and Lemma 2.25. $\square$

**2.31 Remark.** Remark 2.20 states that $\infty$-Cat$^{+m}$ is locally presentable. Consequently, the preceding proposition implies that the functors $C \ominus -$, $-\ominus C$, $C \ominus -$, and $-\ominus C$ admit right adjoints. In particular, this immediately implies that both tensor products are closed monoidal structures.

## 2.4 The Inductive Left Semi-Model Structure

In this section, we will construct a left semi-model structure on the category $\infty$-Cat$^{+m}$. The definitions and results on left semi-model structures that we will use here are recalled in Appendix A.

**2.32 Definition.** We define the set $I = I^\partial \cup I^{+m}$ to be our *set of generating cofibrations* in $\infty$-Cat$^{+m}$ where:

$$\begin{aligned} I^\partial &= \{i_n : \partial \mathbb{D}_n^b \to \mathbb{D}_n^b \mid n \geqslant 0\} \\ I^{+m} &= \{\mathbb{D}_n^b \to (\mathbb{D}_n, \overline{\{e_n\}}) \mid n \geqslant 0\} \end{aligned}$$

An arrow in $\infty$-Cat$^{+m}$ is said to be an *acyclic fibration* if it has the right lifting property against all arrows in $I$. An arrow in $\infty$-Cat$^{+m}$ is said to be a *cofibration* if it has the left lifting property against all acyclic fibrations.

16

**2.33 Remark.** It immediately follows from the small object argument that every morphism can be factored into a cofibration followed by an acyclic fibration, and that all cofibrations are retracts of transfinite compositions of pushouts of morphisms in $I$.

**2.34 Proposition.** A morphism $(K, M) \rightarrow (L, N)$ is a cofibration in $\infty$-$\mathbf{Cat}^{+m}$ if and only if the induced functor $K \rightarrow L$ is a cofibration in the canonical model structure $\infty$-$\mathbf{Cat}_{Can}$ recalled in Theorem 4.23.

In particular, the cofibrant objects of $\infty$-$\mathbf{Cat}^{+m}$ are exactly the $m$-marked $\infty$-categories whose underlying $\infty$-category is free on a polygraph, with any possible marking on them.

*Proof.* As recalled in Theorem 4.23, the set of generating cofibrations of the canonical model structure is given by $\{i_n: \partial\mathbb{D}_n \rightarrow \mathbb{D}_n \mid n \geq 0\}$. Note that the trivial marking functor $(-)^b: \infty$-$\mathbf{Cat} \rightarrow \infty$-$\mathbf{Cat}^{+m}$ and the forgetful functor $U: \infty$-$\mathbf{Cat}^{+m} \rightarrow \infty$-$\mathbf{Cat}$ preserve colimits. We can directly deduce that both of these functors preserve cofibrations.

In particular, a cofibration $(K, M) \rightarrow (L, N)$ induces a cofibration $K \rightarrow L$ in $\infty$-$\mathbf{Cat}_{Can}$.

Conversely, suppose we are given a morphism $(K, M) \rightarrow (L, N)$ such that the induced morphism $K \rightarrow L$ is a cofibration in $\infty$-$\mathbf{Cat}_{Can}$. We have a canonical square:

$$\begin{array}{ccc} K^b & \longrightarrow & (K, M) \\ \downarrow & & \downarrow \\ L^b & \longrightarrow & (L, N) \end{array}$$

where the left-hand vertical morphism is a cofibration. The canonical morphism $L^b \coprod_{K^b} (K, M) \rightarrow (L, N)$ is the identity on the underlying category and is thus an iterated pushout of morphisms in $I^{+m}$. In particular, it is a cofibration, and by stability under pushouts and compositions, so is $(K, M) \rightarrow (L, N)$.

Finally, the last claim follows from [35, Theorem 7.4], which asserts that cofibrant objects of $\infty$-$\mathbf{Cat}_{Can}$ correspond to $\infty$-categories that are free on a polygraph. $\square$

**2.35 Remark.** A morphism $\pi: X \rightarrow Y$ has the right lifting property against all morphisms in $I^\partial$ if its image by the forgetful functor to $\infty$-$\mathbf{Cat}$ is an acyclic fibration; that is, if for every pair of parallel $n$-arrows $u, v$ in $X$, the map $\operatorname{Hom}_X(u, v) \rightarrow \operatorname{Hom}_Y(\pi(u), \pi(v))$ is surjective.

$\pi$ has the right lifting property against all morphisms in $I^{+m}$ if and only if for every arrow $f \in X$ such that $\pi(f)$ is marked in $Y$, $f$ is marked in $X$. An acyclic fibration is a map that has both these properties.

The pushout-product, or corner-product (sometimes also called the Leibniz product) $f \bar{\ominus} g$ and $f \bar{\ominus} g$ is defined as usual: if $f: X \rightarrow Y$ and $g: A \rightarrow B$ are two morphisms in $\infty$-$\mathbf{Cat}^{+m}$, then $f \bar{\ominus} g$ is the canonical morphism:

$$X \ominus B \coprod_{X \ominus A} Y \ominus A \rightarrow Y \ominus B$$

17

and $f \hat{\ominus} g$ is the canonical morphism

$$X \ominus B \coprod_{X \ominus A} Y \ominus A \rightarrow Y \ominus B$$

We refer to the appendix of [29] for the general theory of pushout products and their formal properties.

**2.36 Proposition.** *If $f$ and $g$ are two cofibrations in $\infty$-Cat$^{+m}$, then $f \hat{\ominus} g$ and $f \hat{\ominus} g$ are both cofibrations.*

*Proof.* By the usual properties of the corner-product, it is enough to check this when $f$ and $g$ are generating cofibrations. If $f$ and $g$ are both in $I^\partial$, then $f \ominus g$ has no marked arrows in either its domain or codomain and coincides with the corner-product $f \hat{\otimes} g$ in $\infty$-Cat, which is a cofibration by [5, theorem 3.9]. $f \ominus g$ is the same except that some arrows are marked, but we can always add these markings by taking additional pushouts by morphisms in $I^{+m}$, so it is again a cofibration.

The forgetful functor $\infty$-Cat$^{+m}$ $\rightarrow \infty$-Cat is monoidal for both tensor products and preserves colimits, so it preserves the corner-product. In particular, if either $f$ or $g$ is in $I^{+m}$, then it is sent to isomorphisms by this forgetful functor, and hence $f \hat{\ominus} g$ and $f \hat{\ominus} g$ induce isomorphisms between their underlying $\infty$-categories. Now, if $f: (X, N) \rightarrow (X, M)$ is a morphism in $\infty$-Cat$^{+m}$ that induces an isomorphism on underlying $\infty$-categories, then it is a pushout of morphisms in $I^{+m}$: one simply needs to take such pushouts to make all arrows in $M$ marked. □

**2.37 Construction.** We define $I := \mathbb{D}_1^2 = (\mathbb{D}_1, \{e_1\})$. It is the $\infty$-category with two objects, $e_0^-$ and $e_0^+$, and a marked arrow $e_1: e_0^- \rightarrow e_0^+$. We denote by $j_-$ and $j_+$ the two maps $\mathbb{D}_0 \rightarrow I$ corresponding, respectively, to the two objects $e_0^-$ and $e_0^+$. This gives a diagram:

$$\mathbb{D}_0 \coprod \mathbb{D}_0 \mapsto I \rightarrow \mathbb{D}_0$$

which will play the role of the interval object for our left semi-model structure on $\infty$-Cat$^{+m}$.

We will take as a set of “generating anodyne cofibrations” (also called a “pseudo-generating set of acyclic cofibrations”) the set of maps of the form $j_+ \hat{\ominus} i$ where $i$ is a generating cofibration, more precisely:

**2.38 Definition.**

- We say that a morphism is a *generating anodyne cofibration* if it is of the form $j_+ \hat{\ominus} i$ with $i$ a generating cofibration.
- We say that a morphism in $\infty$-Cat$^{+m}$ is a *naive fibration* if it has the right lifting property against all morphisms of the form $j_+ \hat{\ominus} i$, where $j_+: \mathbb{D}_0 \rightarrow I$ is as in Construction 2.37, and $i$ is one of the generating cofibrations as in Definition 2.32.
- We say that an $m$-marked $\infty$-category $C$ is *fibrant* if the morphism $C \rightarrow 1$ is a naive fibration.
- We say that a morphism in $\infty$-Cat$^{+m}$ is an *anodyne cofibration* if it has the right lifting property against all naive fibrations.

18

- We say that a cofibration in $\infty$-Cat$^{+m}$ is acyclic if it has the lifting property against all naive fibrations between fibrant objects.
- We say that a map in $\infty$-Cat$^{+m}$ is a fibration if it has the right lifting property against all acyclic cofibrations.

As before, it immediately follows from the small object argument that every morphism factors as an anodyne cofibration followed by a naive fibration, and all anodyne cofibrations are retracts of transfinite compositions of pushouts of the generating anodyne cofibrations.

2.39 Remark. It immediately follows from Proposition 2.36 that, as $j_+$ is a cofibration, all maps of the form $j_+ \hat{\odot} i$ are cofibrations. In particular, all acyclic fibrations are also naive fibrations and all anodyne cofibrations are cofibrations.

2.40 Proposition. Acyclic cofibrations and fibrations form a cofibrantly generated weak factorization system on $\infty$-Cat$^{+m}$. A morphism with fibrant target is a fibration if and only if it is a naive fibration.

Proof. This is a direct application of the results of Section 4 of [24]. Starting from the premodel (see Definition A.1) structure on $\infty$-Cat$^{+m}$ whose weak factorization systems are (cofibrations, acyclic fibrations) and (anodyne cofibrations, naive fibrations), we obtain the one with (cofibrations, acyclic fibrations) and (acyclic cofibrations, fibrations) as its "left saturation" L($\infty$-Cat$^{+m}$) in the sense of Theorem 4.1 of [24]. All the claims in the proposition follow from this Theorem 4.1.

2.41 Remark. Note that replacing $\hat{\odot}$ by $\hat{\odot}$ in Definition 2.38 would not change the definition. Indeed, if $X = Y^2$ is an $m$-marked $\infty$-category whose arrows of dimension strictly greater than 0 are all marked, then for any $m$-marked $\infty$-category $Z$ one has $X \odot Z = X \ominus Z$. As this applies to both the domain and the co-domain of $j_+$, it follows that $j_+ \hat{\odot} i = j_+ \hat{\odot} i$.

Also, the reader should not be worried about the use of $j_+$ in Definition 2.38 rather than $j_-$ or both $j_-$ and $j_+$. While using $j_-$ or both $j_-$ and $j_+$ instead of $j_+$ would change the definition of naive fibrations and anodyne cofibrations, this does not affect the definition of (naive) fibrations between fibrant objects; hence, the acyclic cofibrations and fibrations would not be changed. Indeed, once the existence of a (monoidal) model structure is established, it follows that $j_-$ is acyclic by 2-out-of-3, and hence all the maps $j_- \hat{\odot} i = j_- \hat{\odot} i$ are also acyclic cofibrations.

2.42 Lemma. If $f$ is an anodyne (resp. acyclic) cofibration and $g$ is a cofibration, then $f \hat{\odot} g$ and $f \hat{\odot} g$ are anodyne (resp. acyclic).

Proof. To get the result for "anodyne cofibrations," it is enough to prove it for the generating anodyne cofibrations. Let $i$ be one of the generating cofibrations and $f = j_+ \hat{\odot} i'$ be one of the generating anodyne cofibrations. We have $f \hat{\odot} i = j_+ \hat{\odot} (i \hat{\odot} i')$. As $i' \hat{\odot} i$ is a pushout of generating cofibrations $i_1, \ldots, i_k$ by Proposition 2.36, it follows that $j_+ \hat{\odot} (i \hat{\odot} i')$ is a pushout of the $j_+ \hat{\odot} i_k$ and hence is an anodyne cofibration.

The result for acyclic cofibrations follows from the formal properties of the pushout product: it follows that if $i$ is a cofibration and $p$ is a naive fibration,

19

then the (right) pullback exponential $\langle p/i \rangle$ is a naive fibration. If $p$ is a (naive) fibration between fibrant objects, then $\langle p/i \rangle$ is a naive fibration between fibrant objects, hence a fibration. It follows that if $i$ is an acyclic cofibration and $j$ is a cofibration, then $i \in j$ is an acyclic cofibration as it is a cofibration by Definition 2.32, and if $p$ is a fibration between fibrant objects, then $i \in j$ has the right lifting property against $p$ because $j$ has the left lifting property against $\langle p/i \rangle$.

The case of $\ominus$ works exactly the same considering the first half of Remark 2.41. $\square$

**2.43 Theorem.** *The category $\infty$-Cat$^{+m}$ of $m$-marked $\infty$-categories admits a $\omega$-combinatorial left semi-model structure (Definition A.5), called the inductive model structure and denoted by $\infty$-Cat$^{+m}_{\text{Ind}}$, in which the cofibrations and acyclic fibrations are as in Definition 2.32 and the fibrations are as in Definition 2.38. Moreover, this left semi-model structure is monoidal (Definition A.5) for both tensor products $\ominus$ and $\ominus$ (from Section 2.3).*

*Proof.* The existence of the left semi-model structure immediately follows from Theorem 6.12 of [24]. Because of Proposition 2.36 and Lemma 2.42, tensoring by the interval object $I$ of Construction 2.37 is a “strong Quillen functor” in the sense of Section 6 of [24]. Note that to apply Theorem 6.12, one needs to observe that $\infty$-Cat$^{+m}$, with the (cofibrations, acyclic fibrations) and (acyclic cofibrations, fibrations) weak factorization systems, is both “right saturated” and “left saturated”, that is, that a fibration that has the right lifting property against all cofibrations between cofibrant objects is an acyclic fibration, and that a cofibration that has the left lifting property against all fibrations between fibrant objects is an acyclic cofibration. The first one holds because the generating cofibrations are cofibrations between cofibrant objects, and the second because that is how we defined acyclic fibrations.

As $\infty$-Cat$^{+m}$ is finitely locally presentable, and as the codomains of the generating cofibrations and generating anodyne cofibrations are $\omega$-small, Theorem 4.1 of [24] implies that $\infty$-Cat$^{+m}_{\text{Ind}}$ is $\omega$-combinatorial.

The fact that this left semi-model structure is monoidal directly follows from Proposition 2.36 and Lemma 2.42. $\square$

**2.44 Remark.** The proof of Theorem 2.43 above also shows that $\infty$-Cat$^{+m}$ also admits a right semi-model category structure whose fibrations and acyclic cofibrations are the fibrations and acyclic cofibrations of Definition 2.38 and whose cofibrations are as in Definition 2.32.

This, however, does not clearly make $\infty$-Cat$^{+m}$ into a Quillen model structure but rather into a “two-sided model category” as in Section 5 of [24]. We refer to Section 5 of [24] for what this means more precisely, but in short, the problem is that the left and right left semi-model categories have different classes of weak equivalences. The two classes of equivalence, however, coincide for morphisms that are between fibrant or cofibrant objects. Another way to talk about this difference is that the left and right left semi-model categories are Quillen equivalent and have the same homotopy category but define different functors $\infty$-Cat$^{+m} \rightarrow \text{Ho}(\infty\text{-Cat}^{+m})$. The two functors agree on objects that are either fibrant or cofibrant but differ on general objects: one sends an object $X$ to its cofibrant replacement while the other sends it to a fibrant replacement, and we

20

do not know if these are always homotopy equivalent when $X$ is neither fibrant nor cofibrant itself.

**2.45 Remark.** We do not know if $\infty\text{-Cat}^{+m}$ is actually a Quillen model category or not. In the unmarked case, this follows from the fact that all objects are fibrant. But that is no longer the case in this situation. In terms of the “two-sided model structure” mentioned in the previous remark, the question is whether $\infty\text{-Cat}^{+m}$ satisfies one of the equivalent conditions of Proposition 5.3 of [24].

We conclude this section with the following lemma that will be useful later:

**2.46 Lemma.** *The map*

$$i_n^+ : \mathbb{D}_n^\flat \to (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$$

where $e_{n+1}$ is the unique non-identity arrow of $\mathbb{D}_{n+1}$, is an anodyne cofibration.

*Proof.* We will show it is a retract of the map $j_+ \hat{\odot} i_n$ where $i_n$ is the map $\partial \mathbb{D}_n \to \mathbb{D}_n$. We then have to construct two morphisms $i, p$ fitting in a diagram of the form

$$(\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}) \xrightarrow{i} I \ominus \mathbb{D}_n^\flat$$
$$\downarrow p$$
$$(\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$$

and such that $p$ and $i$ send the domain of $i_n^+$ and of $j_+ \hat{\odot} i_n$ to each other.

In order to achieve this, we will use the explicit description of $\mathbb{D}_1 \otimes \mathbb{D}_n$ given in Example 2.12. The object we are interested in is $I \ominus \mathbb{D}_n^\flat$ which is the same polygraph endowed with the marking where all the arrows $a \otimes e_k^\iota$ are marked. We call $i: (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}) \to I \ominus \mathbb{D}_n^\flat$ the unique morphism sending $e_{n+1}$ to $a \otimes e_n$. This is well defined because $a \otimes e_n$ is a marked arrow. Next, we define a map $p: I \ominus \mathbb{D}_n^\flat \to (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$ by:

$$p(a_0^\iota \otimes e_k^\mu) = e_k^\mu \text{ if } k < n.$$

$$p(a_0^\iota \otimes e_n) = e_n^\iota$$

$$p(a \otimes e_k^\iota) = \mathbb{I}_{e_k^\iota} \text{ if } k < n.$$

$$p(a \otimes e_n) = e_{n+1}$$

In order to check that this is well defined, we first need to check that this definition is compatible with the source and target given above, which follows from an immediate calculation. Then we need to show that this is compatible with the marking, which is the case as both $\mathbb{I}_{e_k^\iota}$ and $e_{n+1}$ are marked.

Finally, the composite $p \circ i$ sends the arrow $e_{n+1}$ to $p(a \otimes e_n) = e_{n+1}$ and hence is the identity of $\mathbb{D}_{n+1}$.

To conclude the proof, we just have to observe that the maps $p$ and $i$ defined above send the domain of $i_n^+$ and of $j_+ \hat{\odot} i_n$ to each other.

The domain of $j_+ \hat{\odot} i_n$ is the sub-polygraph of $I \ominus \mathbb{D}_n^\flat$ which contains all the generators except $a_0^- \otimes e_n$ and $a \otimes e_n$, while the domain of $i_n^+$ contains all generators of $\mathbb{D}_{n+1}$ except $e_{n+1}$ and $e_n^-$.

21

In order to check that the map $i$ is compatible with these sub-polygraphs, it is enough to check that $i(e_n^+)$ is in the domain of $j_+ \hat{\odot} i_n$. To see this, we compute:

$$i(e_n^+) = \pi^+ i(e_{n+1}) = \pi^+(a \otimes e_n) = (a \otimes e_{n-1}^-)\#_{n-1} \dots \#_1 (a \otimes e_0^-)\#_0 (a_0^+ \otimes e_n)$$

and we observe that this expression involves neither $a_0^- \otimes e_n$ nor $a \otimes e_n$, hence it does belong to the domain of $j_+ \hat{\odot} i_n$.

In order to check that the map $p$ is compatible with these sub-polygraphs, we need to check the image by $p$ of all the generators of $I \ominus \mathbb{D}_n^\times$ except $a_0^- \otimes e_n$ and $a \otimes e_n$. These are given by the formulas $p(a_0^e \otimes e_k^p) = e_k^p$ if $k < n$, $p(a_0^+ \otimes e_n) = e_n^+$ and $p(a \otimes e_k^e) = \mathbb{I}_{e_k^e}$, which all indeed belong to the image of $i_n^+$.

### 3 Equations and Saturations in an $m$-Marked $\infty$-Category.

The general goal of this section is to arrive at a better description of the fibrant objects and fibrations between fibrant objects of the model structure of Theorem 2.43. This is achieved using the notion of *equations* in an $\infty$-category introduced by the second named author in [32]. We will recall the basic theory of equations, in a slightly different language, and introduce an analog of equations to deal with the markings, which we call *saturations*.

#### 3.1 Definitions of Equations and Saturations

**3.1 Definition.** A morphism of $m$-marked polygraphs $\Lambda P \rightarrow P$ is a *left equation* if there exists an integer $n$, and two generators $x, y$ of $P$ of dimension respectively $n$ and $n+1$, such that

1. $\Lambda P$ is the $m$-marked sub-polygraph of $P$ that contains all generators except $x$ and $y$,
2. $y$ is a marked arrow,
3. if $n \leq m$, $x$ is an unmarked arrow of $P$,
4. the source of $y$ admits a decomposition:

$$\pi_n^- y = l_n \#_{n-1} (l_{n-1} \#_{n-2} \dots \#_1 (l_1 \#_0 x \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n$$

where for each $i$, $l_i$ and $r_i$ are marked $i$-arrows in $P$, with $l_n$ and $r_n$ not containing $x$. In particular, $x$ appears only once in $\pi_n^- y$,

1. $x$ does not appear in the target of $y$.

*Right equations* are defined in the exact same way except the source and target of $y$ are exchanged in the last two conditions.

We say that $\Lambda P \rightarrow P$ is an *equation* to mean that it is either a left or right equation.

**3.2 Remark.** Note that the integer $n$ and the arrows $x$ and $y$ in the previous definition are uniquely determined by the inclusion $\Lambda P \rightarrow P$.

22

**3.3 Remark.** The name “equation” comes from the idea that we are looking for an element $x$ such that a certain composite of $x$ with other arrows is isomorphic to another given arrow. From this point of view, a map $\Lambda P \rightarrow X$ corresponds to such an equation in $X$, and an extension $P \rightarrow X$ corresponds to a solution of the equation, or rather the image of $x$ is the solution and $y$ represents the isomorphism witnessing that $x$ is a solution.

**3.4 Definition.** A morphism of $m$-marked polygraphs $\Omega P \rightarrow P$ is a *left saturation* if it is an isomorphism on the underlying polygraphs, and if there exists an integer $n$, and two marked generators $x, y$ of $P$ of dimension respectively $n$ and $n+1$, such that

1. (1) any marked generator of $P$ that is different from $x$ is marked in $\Omega P$,
2. (2) $x$ and $y$ are marked in $P$,
3. (3) the target of $y$ is marked,
4. (4) the arrows $x$ and $y$ satisfy the conditions (5) and (6) of Definition 3.1.

*Right saturations* are defined in the exact same way except the source and target of $y$ are exchanged in the last two conditions.

We say that $\Omega P \rightarrow P$ is an *saturation* to mean that it is either a left or right saturation.

**3.5 Construction.** Let $n$ be a non-negative integer. The morphism

$$j_+ \hat{\odot} i_n := I \odot \partial \mathbb{D}_n \coprod \{1\} \odot \mathbb{D}_n \rightarrow I \odot \mathbb{D}_n$$

is a left equation. Indeed, let $y$ be the top-dimensional generator of $I \odot \mathbb{D}_n$. If we denote by $x$ the top-dimensional arrow of $\{0\} \odot \mathbb{D}_n$, and for $0 < k \leq n$, by $a_k$ the image of the top-dimensional $k$-generator of $I \odot \mathbb{D}_{k-1}$ by the morphism

$$I \odot \delta_{k-1}^- : I \odot \mathbb{D}_{k-1} \rightarrow I \odot \mathbb{D}_n,$$

we recall that we gave an explicit description of $\mathbb{D}_1 \otimes \mathbb{D}_n$ in Example 2.12. The object we are interested in is $I \odot \mathbb{D}_n^\times$, which is the same polygraph endowed with the marking where all the arrows $a \otimes e_k^\times$ are marked. Using this description, we see that if we name $y = a \otimes e_n$ and $x = a_0^- \otimes e_n$ the two arrows of $I \odot \mathbb{D}_n$ that are not in the image of $j_+ \hat{\odot} i_n$, then we have a decomposition of the source of $y$ of the form:

$$(((x\#_0 a_0)\#_1 a_2) \dots)\#_{n-1} a_n$$

and all the $a_k$ are marked. We denote it

$$\mathbf{e}\mathbf{q}_n^\square : \Lambda \mathbf{E}\mathbf{q}_n^\square \rightarrow \mathbf{E}\mathbf{q}_n^\square.$$

**3.6 Example.** The underlying $\infty$-category of $\mathbf{E}\mathbf{q}_1^\square$ is

![img-0.jpeg](img-0.jpeg)

23

and the underlying $\infty$-category of $\mathbf{Eq}_2^{\sqsupset}$ is

![img-1.jpeg](img-1.jpeg)

3.7 Construction. Similarly, the morphism

$$j_+ \hat{\ominus} s_n \colon I \ominus \mathbb{D}_n \coprod \{1\} \ominus (\mathbb{D}_n, \overline{\{e_n\}}) \to I \ominus (\mathbb{D}_n, \overline{\{e_n\}})$$

where $s_n$ is the "identity" map $\mathbb{D}_n \to (\mathbb{D}_n, \overline{\{e_n\}})$ is a left saturation, which we denote

$$\mathbf{sat}_n^{\sqsupset} \colon \Omega \mathbf{Sat}_n^{\sqsupset} \to \mathbf{Sat}_n^{\sqsupset}.$$

3.8 Proposition. Generating anodyne cofibrations are either equations or saturations.

Proof. By Definition 2.38, the generating anodyne cofibrations are of the form $j_+ \hat{\ominus} i$ with $i$ being either $\partial \mathbb{D}_n \to \mathbb{D}_n$ or $\mathbb{D}_n \to (\mathbb{D}_n, \overline{\{e_n\}})$ for an integer $n$. By Constructions 3.5 and 3.7, these morphisms are either equations or saturations.

3.9 Definition. We define some left equations which play an important role. In each case, $k$ and $n$ are integers with $0 < k \leqslant n$.

- $\mathbf{eq}_{k,n}^{\sqsupset \diamond} \colon \Lambda \mathbf{Eq}_{k,n}^{\sqsupset \diamond} \to \mathbf{Eq}_{k,n}^{\sqsupset \diamond}$, whose codomain is generated by

- a \(n\)-arrow \(x\), a marked \(k\)-arrow \(a\) such that \(\pi_{k-1}^{+}(a) = \pi_{k-1}^{-}(x)\),
- a \(n\)-arrow \(b\) of source \(a\#_{k-1}\pi_{n-1}^{-}(y)\) (resp. \(\pi_{n-1}^{-}(a)\)) and of target \(a\#_{k-1}\pi_{n-1}^{+}(y)\) (resp. \(\pi_{n-1}^{+}(x)\)) if \(k < n\) (resp. if \(k = n\)),
- a marked \((n + 1)\)-arrow \(y\) of source \(a\#_{k - 1}x\) and of target \(b\),

and whose domain is obtained by removing $x$ and $y$.

- $\mathbf{eq}_{k,n}^{\diamond -} \colon \Lambda \mathbf{Eq}_{k,n}^{\diamond -} \to \mathbf{Eq}_{k,n}^{\diamond -}$, whose codomain is generated by

- a \(n\)-arrow \(x\), a marked \(k\)-arrow \(a\) such that \(\pi_{k - 1}^{+}(x) = \pi_{k - 1}^{-}(a)\),
- a \(n\)-arrow \(b\) of source \(\pi_{n - 1}^{-}(y)\#_{k - 1}a\) (resp. \(\pi_{n - 1}^{-}(x)\)) and of target \(\pi_{n - 1}^{+}(y)\#_{k - 1}a\) (resp. \(\pi_{n - 1}^{+}(a)\)) if \(k < n\) (resp. if \(k = n\)),
- a marked \((n + 1)\)-arrow \(y\) of source \(y\#_{k - 1}x\) and of target \(b\).

and whose domain is obtained by removing $x$ and $y$.

3.10 Example. The underlying $\infty$-category of $\mathbf{Eq}_{1,1}^{\sqsupset \diamond}$ is generated by the diagram

![img-2.jpeg](img-2.jpeg)

24

and the underlying $\infty$-category of $\mathbf{Eq}_{1,2}^{\circ}$ is generated by the diagram

![img-3.jpeg](img-3.jpeg)

**3.11 Definition.** Let $\Lambda P \rightarrow P$ be a left equation, and $n, x, y$ the integer and the two generators of Definition 3.1. We denote $(x_0, y_0)$ and $(x_1, y_1)$ the images of the couple $(x, y) \in P$ by the two inclusions $P \rightarrow P \coprod_{\Lambda P} P$. The $m$-marked polygraph $\mathrm{Uni}_{\Lambda P}(P)$ is obtained from $P \coprod_{\Lambda P} P$ by adding an unmarked $(n+1)$-generator $z$ of $n$-source $x_0$ and $n$-target $x_1$.

A map $f: P \coprod_{\Lambda P} P \rightarrow X$ corresponds to a map $\Lambda P \rightarrow X$, which is an equation in $X$, together with two solutions $P \rightarrow X$, given by pairs $(x_0, y_0)$ and $(x_1, y_1)$. The morphism $f$ lifts to $\mathrm{Uni}_{\Lambda P}(P)$ if there exists a marked arrow $z: x_0 \rightarrow x_1$. Formally, this expresses that the two solutions are equivalent.

**3.12 Example.** The underlying $\infty$-category of $\mathrm{Uni}_{\Lambda \mathbf{Eq}_{1,1}^{\circ}} (\mathbf{Eq}_{1,1}^{\circ})$ is

![img-4.jpeg](img-4.jpeg)

**3.13 Definition.** Let $C$ be an $m$-marked $\infty$-category and $\Lambda P \rightarrow P$ a left equation (resp. right equation).

The equation $\Lambda P \rightarrow P$ has solutions in $C$ if for all morphisms $\Lambda P \rightarrow C$, there exists a lifting $(x, y): P \rightarrow C$ such that $x$ is sent to a marked arrow whenever the target of $y$ is (resp. the source of $y$ is).

Solutions to an equation $\Lambda P \rightarrow P$ in $C$ are weakly unique if $C$ has the right lifting property against $P \coprod_{\Lambda P} P \rightarrow \mathrm{Uni}_{\Lambda P}(P)$.

The equation $\Lambda P \rightarrow P$ has weakly unique solutions in $C$ if the equation $\Lambda P \rightarrow P$ has solutions in $C$ and they are weakly unique.

It will be useful to have a “coherent” version of $\mathrm{Uni}_{\Lambda P}(P)$.

**3.14 Definition.** Let $\Lambda P \rightarrow P$ be a left equation, and $n, x, y$ the integer and the two generators of Definition 3.1. Suppose given a decomposition

$$\pi_n^- y = l_n \#_{n-1}(l_{n-1} \#_{n-2} \dots \#_1(l_1 \#_0 x \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n$$

of the $n$-source of $y$. We denote $(x_0, y_0)$ and $(x_1, y_1)$ the images of the couple $(x, y) \in P$ by the two inclusions $P \rightarrow P \coprod_{\Lambda P} P$. The $m$-marked polygraph $\mathrm{Uni}_{\Lambda P}^{coh}(P)$ is obtained from $P \coprod_{\Lambda P} P$ by

1. (1) adding an unmarked $(n+1)$-generator $z$ of $n$-source $x_0$ and $n$-target $x_1$,
2. (2) adding a marked $(n+2)$-generator $w$ of $(n+1)$-source

$$l_n \#_{n-1}(l_{n-1} \#_{n-2} \dots \#_1(l_1 \#_0 z \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n \#_n y_1$$

and of $(n+1)$-target $y_0$.

25

By construction, the morphism $P \coprod_{\Lambda P} P \rightarrow \operatorname{Uni}_{\Lambda P}^{coh}(P)$ is a left equation.

Let $\Lambda P \rightarrow P$ be a right equation, and $n, x, y$ the integer and the two generators of Definition 3.1. Suppose given a decomposition

$$\pi_n^+ y = l_n \#_{n-1}(l_{n-1} \#_{n-2} \dots \#_1(l_1 \#_0 x \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n$$

of the $n$-target of $y$. We denote $(x_0, y_0)$ and $(x_1, y_1)$ the images of the couple $(x, y) \in P$ by the two inclusions $P \rightarrow P \coprod_{\Lambda P} P$. The $m$-marked polygraph $\operatorname{Uni}_{\Lambda P}(P)$ is obtained from $P \coprod_{\Lambda P} P$ by

(1) adding an unmarked $(n+1)$-generator $z$ of $n$-source $x_0$ and $n$-target $x_1$,
(2) adding a marked $(n+2)$-generator $w$ of $(n+1)$-source

$$y_0 \#_n l_n \#_{n-1}(l_{n-1} \#_{n-2} \dots \#_1(l_1 \#_0 z \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n \rightarrow y_1$$

and of $(n+1)$-target $y_0$.

By construction, the morphism $P \coprod_{\Lambda P} P \rightarrow \operatorname{Uni}_{\Lambda P}^{coh}(P)$ is a right equation.

**3.15 Remark.** Let $\Lambda P \rightarrow P$ be an equation and $X$ a $m$-marked $\infty$-category. A map $f: P \coprod_{\Lambda P} P \rightarrow X$ corresponds to a map $\Lambda P \rightarrow X$, together with two solutions $P \rightarrow X$ given by pairs $(x_0, y_0)$ and $(x_1, y_1)$. If the equation $P \coprod_{\Lambda P} P \rightarrow \operatorname{Uni}_{\Lambda P}^{coh}(P)$ has a solution in $C$, it implies that given any pair of solutions $(x_0, y_0)$ and $(x_1, y_1)$ of $\Lambda P \rightarrow P$, there exists a marked arrow $z: x_0 \rightarrow x_1$, which informally expresses that the two solutions are equivalent, together with marked arrows

$$l_n \#_{n-1}(l_{n-1} \#_{n-2} \dots \#_1(l_1 \#_0 z \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n \#_n y_1 \rightarrow y_0$$

(resp.

$$y_0 \#_n l_n \#_{n-1}(l_{n-1} \#_{n-2} \dots \#_1(l_1 \#_0 z \#_0 r_1) \#_1 \dots \#_{n-2} r_{n-1}) \#_{n-1} r_n \rightarrow y_1$$

which express a compatibility between $z, y_0$, and $y_1$.

In particular, this implies that the equation $\Lambda P \rightarrow P$ has weakly unique solutions in $C$.

**3.16 Example.** The underlying $\infty$-category of $\operatorname{Uni}_{\Lambda \mathbf{Eq}_{1,1}}^{coh}(\mathbf{Eq}_{1,1}^{\circ})$ is

![img-5.jpeg](img-5.jpeg)

## 3.2 Characterization of Fibrant Objects of The Inductive Left Semi-Model Structure

In this section, we will give a simple characterization of the fibrant objects of the left semi-model structure introduced in Theorem 2.43. We will temporarily call the objects satisfying this characterization “prefibrant” (Definition 3.18) and then show in Proposition 3.25 that these are exactly the fibrant objects.

26

**3.17 Definition.** Let $a$ be an $(n+1)$-arrow in a $m$-marked $\infty$-category $C$. An *inverse* for $a$ is an arrow $a^{-1}$ such that there exist two marked arrows:

$$\epsilon: a\#_n a^{-1} \rightarrow \mathbb{I} \quad \nu: a^{-1}\#_n a \rightarrow \mathbb{I}.$$

An arrow is *invertible* if it has an inverse.

**3.18 Definition.** An $m$-marked $\infty$-category $C$ is *prefibrant* if

(1) marked arrows of $C$ are invertible and their inverses are marked,
(2) whenever $a$ and $c: a \rightarrow b$ are marked in $C$, so is $b$.

This directly implies that if $b$ and $c: a \rightarrow b$ are marked, so is $b$.

This notion is purely temporary: we will show in Proposition 3.25 that an object is fibrant for the left semi-model structure of Theorem 2.43 if and only if it is prefibrant.

**3.19 Proposition.** Let $0 < k \leq n$ be two integers. If $C$ is *prefibrant*, then equations $\mathbf{eq}_{k,n}^{\circ \circ \circ}$ and $\mathbf{eq}_{k,n}^{\circ \circ \circ}$ have weakly unique solutions in $C$.

*Proof.* We show the result by decreasing induction on $k \leq n$. The initialization corresponds to $k = n$. In this case, the data of a morphism $\mathbf{A}\mathbf{E}\mathbf{q}_{n,n}^{\circ \circ \circ} \rightarrow C$ corresponds to two $n$-arrows $a$ and $b$ sharing the same source and such that $a$ is marked. Let $\nu: a^{-1}\#_n a \rightarrow \mathbb{I}$. If we define $x: = a^{-1}\#_n b$ and $y: \psi\#_n b: a\#_n x \rightarrow b$, the couple $(x, y)$ is a solution of $\mathbf{eq}_{n,n}^{\circ \circ}$. If $b$ is marked, so is $x$. We now show the weak uniqueness of the solution. Let $(\bar{x}, \bar{y})$ be another solution. We then have a marked arrow:

$$z: \bar{x} \xrightarrow{\nu^{-1}} a^{-1}\#_n a\#_n \bar{x} \xrightarrow{\bar{y}} a^{-1}\#_n b.$$

The assertion for $\mathbf{eq}_{n,n}^{\circ \circ \circ}$ is similar.

Suppose now the result is true for $k+1$. We start by showing that solutions of $\mathbf{eq}_{k,n}^{\circ \circ}$ and $\mathbf{eq}_{k,n}^{\circ \circ \circ}$ are weakly unique in $C$. The data of a morphism $\mathbf{A}\mathbf{E}\mathbf{q}_{k,n}^{\circ \circ} \rightarrow C$ corresponds to an $n$-arrow $x: s \rightarrow t$, a $k$-invertible arrow $a$ such that $\pi_k^+ a = \pi_k^- x$, and an arrow $b: a\#_{k-1} s \rightarrow a\#_k t$. Let $(x, y: a\#_{k-1} x \rightarrow b)$ be a solution of this equation. Let $\nu: a^{-1}\#_{k-1} a \rightarrow \mathbb{I}_{\pi_k^+ a}$ be a marked $(k+1)$-arrow. We recall that the interchange rule implies that

$$\begin{aligned} (\nu\#_{k-1} s)\#_k x &= (\nu\#_{k-1} \mathbb{I}_s) \#_k (\mathbb{I}_{\pi_k^+ a} \#_k x) \\ &= (\nu\#_k \mathbb{I}_{\pi_k^+ a}) \#_{k-1} (\mathbb{I}_s \#_k x) \\ &= \nu\#_{k-1} x \\ &= (\mathbb{I}_{a^{-1}\#_{k-1} a} \#_k \nu) \#_{k-1} (x \#_k \mathbb{I}_t) \\ &= (\mathbb{I}_{a^{-1}\#_{k-1} a} \#_k - 1) \#_k (\mathbb{I}_t \#_k - 1) \nu) \\ &= (a^{-1}\#_{k-1} a\#_{k-1} x) \#_k (\nu\#_{k-1} t) \end{aligned}$$

The arrow $x$ is then also a solution of $\mathbf{eq}_{k+1,n}^{\circ \circ}$:

$$(\nu\#_{k-1} s)\#_k x = (a^{-1}\#_{k-1} a\#_{k-1} x) \#_k (\nu\#_{k-1} t)^{\frac{(a^{-1}\#_{k-1} y)\#_k (\nu\#_{k-1} t)}{2}} (a^{-1}\#_{k-1} b) \#_k (\nu\#_{k-1} t)$$

27

and so is weakly unique. The uniqueness of solutions of $\mathbf{eq}_{k,n}^{\circ -}$ is proved similarly.

We show now that $\mathbf{eq}_{k,n}^{\circ -}$ and $\mathbf{eq}_{k,n}^{\circ -}$ have solutions in $C$. Let $(x, y)$ be a solution of the equation

$$y: (\nu\#_0s)\#_k x \rightarrow (a^{-1}\#_{k-1}b)\#_k(\nu\#_{k-1}t)$$

Moreover, we can find such $x$ marked whenever $b$ is. We then have

$$(\nu\#_0s)\#_k x = (a^{-1}\#_{k-1}a\#_{k-1}x)\#_k(\nu\#_{k-1}t).$$

By weak uniqueness of solutions of $\mathbf{eq}_{k+1,n}^{\circ -}$, we then have a marked arrow

$$z: a^{-1}\#_{k-1}a\#_{k-1}x \rightarrow a^{-1}\#_{k-1}b.$$

But $a\#_{k-1}x$ and $b$ are solutions of an equation $\mathbf{eq}_{k,n}^{\circ -}$, and so there exists a marked arrow

$$\bar{y}: a\#_{k-1}x \rightarrow b.$$

If $b$ is marked, the arrow $x$ that we produce is also marked. The existence of a solution of $\mathbf{eq}_{k,n}^{\circ -}$ is proved similarly. $\square$

**3.20 Lemma.** *If the equations $\mathbf{eq}_{k,n}^{\circ -}$ and $\mathbf{eq}_{k,n}^{\circ -}$ have solutions in $C$ for any integers $0 < k \leq n$, then all equations have solutions in $C$.*

*Proof.* Let $\Lambda P \rightarrow P$ be a left equation. There is a decomposition of the source of $y$ of the shape

$$\pi_n^- y = l_n\#_{n-1}(l_{n-1}\#_{n-2}\dots\#_1(l_1\#_0x\#_0r_1)\#_1\dots\#_{n-2}r_{n-1})\#_{n-1}r_n$$

where for each $i$, $l_i$ and $r_i$ are marked $i$-arrows in $P$. We can then use the existence of solutions to $\mathbf{eq}_{k,n}^{\circ -}$ and $\mathbf{eq}_{k,n}^{\circ -}$ to get two sequences of arrows $(x_k)_{0<k<2n}$ and $(y_k)_{0<k<2n}$ such that:

- (1) $y_{2n-1}: x_{2n-1}\#_{n-1}r_n \rightarrow \pi_n^+ y$;
- (2) $y_{2k-1}: x_{2k-1}\#_{k-1}r_k \rightarrow x_{2k}$;
- (3) $y_{2k-2}: l_k\#_{k-1}x_{2k-2} \rightarrow x_{2k-1}$.

Moreover, arrows $x_k$ are marked whenever $\pi_n^+ y$ is. The couple $(x_0, \bar{y})$ is then a solution to $P$ where $\bar{y}$ is the composite:

$$\begin{aligned} \bar{y} := & \quad (l_n\#_{n-1}(l_{n-1}\#_{n-2}\dots\#_1((y_0\#_0r_1)\#_n y_1)\#_1\dots\#_{n-2}r_{n-1})\#_{n-1}r_n) \\ \#_n & \quad (l_n\#_{n-1}(l_{n-1}\#_{n-2}\dots\#_2((y_2\#_1r_2)\#_n y_3)\#_2\dots\#_{n-2}r_{n-1})\#_{n-1}r_n) \\ \#_n & \quad \dots \\ \#_n & \quad (y_{2n-2}\#_{n-1}r_n)\#_n y_{2n-1} \end{aligned}$$

If $\Lambda P \rightarrow P$ is a right equation, we define $\Lambda P \rightarrow P^{op}$ to be the left equation obtained by inverting the direction of the arrow of maximum dimension. A solution of $\Lambda P \rightarrow P$ is given by $(x, y^{-1})$ where $(x, y)$ is a solution of $\Lambda P \rightarrow P^{op}$. Moreover, one can find an arrow $x$ marked whenever the source of $y^{-1}$ is. $\square$

28

**3.21 Lemma.** *Let $C$ be an $m$-marked $\infty$-category such that all equations have solutions in $C$ and whenever $a$ and $c: a \rightarrow b$ are marked, so is $b$. Then $C$ has the right lifting property against all equations and saturations.*

*Proof.* By definition, $C$ has the right lifting property against all equations. Let $\Omega Q \rightarrow Q$ be a saturation, and let $n$, $x$, and $y$ be the integer and the two generators of Definition 3.4. We denote by $P$ the $m$-marked polygraph obtained from $Q$ by unmarking $x$ and all the $n$-arrows appearing in the $n$-target of $y$. We also denote by $\Lambda P$ the $m$-marked sub-polygraph of $P$ that contains all generators except $x$ and $y$. The morphism $\Lambda P \rightarrow P$ is then an equation.

Suppose now that we have a morphism $f: \Omega Q \rightarrow C$. This corresponds to a solution $(x, y)$ of the equation $\Lambda P \rightarrow P$. We then know that there exists another solution $(\bar{x}, \bar{y})$ of the equation where $\bar{x}$ is marked. Furthermore, as $P \prod_{\Lambda P} P \rightarrow \text{Uni}_{\Lambda P}^{\text{coh}}(P)$ is an equation, it has solutions in $C$, and there exists a marked arrow $z': \bar{x} \rightarrow x$. By assumption, this implies that $x$ is marked. This shows that we can lift the morphism $f$ to $Q$. $\square$

**3.22 Lemma.** *Fibrant objects have the right lifting property against the equations $\mathbf{eq}_{n,n}^{\diamond \cdots}$ and saturations $\mathbf{sat}_{n,n}^{\diamond \cdots}$.*

*Proof.* Consider a lifting problem of $\mathbf{eq}_{n,n}^{\diamond \cdots}$ against $C$. This means that we have in $C$ an $n$-arrow $b$ and a marked $n$-arrow $a$ that share the same source.

Since $C$ is fibrant, it has, by definition, the right lifting property against $\mathbf{eq}_n^{\square}$ as in Construction 3.5. Using the same notations as in 3.5 for the generators of $\Lambda \mathbf{Eq}_n^{\square}$, we choose the image of $a_l$ in $C$ to be an identity for all $l < n$, and $a_n = a$. This gives us a span:

$$\begin{array}{c} \Lambda \mathbf{Eq}_n^{\square} \longrightarrow C \\ \mathbf{eq}_n^{\square} \downarrow \\ \mathbf{Eq}_n^{\square} \end{array}$$

which has a dotted diagonal filling $(x, y)$. But this pair verifies $y: x \#_{k-1} a \rightarrow b$, and is thus a solution to the lifting problem above.

The proof for the saturation $\mathbf{sat}_{n,n}^{\diamond \cdots}$ is similar. $\square$

**3.23 Lemma.** *In a fibrant $m$-marked $\infty$-category, all marked arrows are invertible. Moreover, their inverses are marked.*

*Proof.* Lemma 3.22 states that $C$ has the right lifting property against $\mathbf{eq}_{n,n}^{\diamond \cdots}$ and $\mathbf{sat}_{n,n}^{\diamond \cdots}$.

First, the right lifting property against $\mathbf{eq}_{n,n}^{\diamond \cdots}$ shows that for any marked arrow $a$, there exists a pair $(a^{-1}, \nu)$ where $\nu$ is marked and

$$\nu: a^{-1} \#_n a \rightarrow \mathbb{I}.$$

The fact that $a^{-1}$ is marked follows from the right lifting property against $\mathbf{sat}_{n,n}^{\diamond \cdots}$.

29

Using again the right lifting property against $\mathbf{eq}_{n,n}^{\circ\cdots}$, we deduce that there are two marked arrows $(a^{-1})^{-1}$ and $\beta$ such that:

$$\beta: (a^{-1})^{-1} \#_n a^{-1} \rightarrow \mathbb{I}.$$

Finally, in the same way, we obtain a marked arrow:

$$\beta^{-1}: \mathbb{I} \rightarrow (a^{-1})^{-1} \#_n a^{-1}.$$

We then define $\epsilon: a \#_n a^{-1} \rightarrow \mathbb{I}$ as the composite:

$$\begin{array}{ccc} a \#_n a^{-1} & & \mathbb{I} \\ \beta^{-1} \#_n a \#_n a^{-1} \downarrow & & \uparrow \beta \\ (a^{-1})^{-1} \#_n a^{-1} \#_n a \#_n a^{-1} & \xrightarrow{(a^{-1})^{-1} \#_n \nu \#_n a^{-1}} & (a^{-1})^{-1} \#_n a^{-1} \end{array}$$

As it is a composite of marked arrows, $\epsilon$ is also marked. This then shows that $a^{-1}$ is an inverse of $a$. $\square$

### 3.24 Lemma. *Fibrant objects are prefibrant.*

*Proof.* Lemma 3.23 implies the first condition. For the second one, let $y: x \rightarrow b$ be a marked arrow where $b$ is marked. The right lifting property against $\mathbf{sat}_{n,n}^{\circ\cdots}$, choosing $a$ to be an identity, implies that $x$ is marked. Now suppose given a marked arrow $y: b \rightarrow x$ where $x$ is marked. We have a marked arrow $y^{-1}: x \rightarrow b$, and thus $b$ is also marked. $\square$

### 3.25 Proposition. *For an $m$-marked $\infty$-category $C$, the following assertions are equivalent:*

1. (1) $C$ is prefibrant in the sense of Definition 3.18.
2. (2) All equations have solutions in $C$, and whenever $a$ and $c: a \rightarrow b$ are marked, so is $b$.
3. (3) $C$ has the right lifting property against all equations and saturations.
4. (4) $C$ is fibrant for the left semi-model structure of Theorem 2.43.

*Proof.* The implication $(1) \Rightarrow (2)$ is a consequence of Proposition 3.19 and Lemma 3.20. Lemma 3.21 states $(2) \Rightarrow (3)$. By Proposition 3.8, generating anodyne cofibrations are either equations or saturations, and thus $(3) \Rightarrow (4)$. Eventually, the implication $(4) \Rightarrow (1)$ is the content of Lemma 3.24. $\square$

## 3.3 Isofibrations

In this section, we provide a simpler characterization of fibrations between fibrant objects as the “isofibrations” in the following sense:

### 3.26 Definition. A morphism between $m$-marked $\infty$-categories is said to be an *isofibration* if it has the lifting property against the maps:

$$i_n^+: \mathbb{D}_n^b \rightarrow (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$$

where $e_{n+1}$ is the unique non-identity arrow of $\mathbb{D}_{n+1}$.

30

**3.27 Notation.** Suppose given an equation $\Lambda P \rightarrow P$ and a lifting problem of the form:

![img-6.jpeg](img-6.jpeg)

Given $a$ a generator of $P$, we will denote its image in $D$ also by $a$. If $a \in \Lambda P$, we denote by $\bar{a}$ its image in $C$. So in general $p(\bar{a}) = a$. If the dotted diagonal lift exists, or if we are in the process of constructing such a lift, the image of $x, y \in P$ in $C$ is also denoted $\bar{x}$ and $\bar{y}$, and we hence also have $p(\bar{x}) = x$ and $p(\bar{y}) = y$.

Explicitly, a morphism $\pi: X \rightarrow Y$ between fibrant $m$-marked $\infty$-categories is an isofibration if for every $n$-dimensional arrow $f: a \rightarrow b$ in $X$, such that in $Y$ there is a parallel arrow $g: \pi(a) \rightarrow \pi(b)$ with a marked arrow $h: g \rightarrow \pi(f)$, then $g$ and $h$ can be lifted to arrows $\bar{g}: a \rightarrow b$ and $\bar{h}: \bar{g} \rightarrow f$ in $X$, with $\bar{h}$ marked, such that $\pi(\bar{g}) = g$ and $\pi(\bar{h}) = h$.

Note that it follows from Lemma 2.46 that fibrations are isofibrations. We insist on the fact that we will only consider the notion of isofibration between *fibrant* $m$-marked $\infty$-categories. We do not expect the definition given above to be very interesting outside this context.

**3.28 Lemma.** *Any isofibration between fibrant $m$-marked $\infty$-categories also has the lifting property against*

$$i_n^\sim: \mathbb{D}_n^b \rightarrow (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}).$$

*Proof.* Let $\pi: X \rightarrow Y$ be an isofibration between fibrant $m$-marked $\infty$-categories, $f: a \rightarrow b$ an $n$-arrow in $X$, with $g: \pi(a) \rightarrow \pi(b)$ and $h: \pi(f) \rightarrow g$ two arrows in $Y$, where $h$ is marked.

As $Y$ is fibrant, according to Lemma 3.23, the arrow $h$ admits an inverse, i.e., there is a marked arrow $h^{-1}: g \rightarrow \pi(f)$ and another marked arrow $t: h^{-1} \#_n h \rightarrow \mathbb{I}_g$ witnessing the inverse relation. One can then apply the isofibration property to lift $g$ and $h^{-1}$ to two arrows $\bar{g}: a \rightarrow b$ and $\bar{h}^{-1}: \bar{g} \rightarrow f$.

As $X$ is also fibrant, one can then consider an inverse $\bar{h}$ of $\bar{h}^{-1}$ in $X$, whose image by $\pi$ will be a second inverse of $h^{-1}$ in $Y$, and again because $Y$ is fibrant, one can hence construct a marked arrow $h \rightarrow \pi(\bar{h})$. Applying the isofibration property one more time then gives us a lift of $h$ and concludes the proof. $\square$

**3.29 Lemma.** *An isofibration between fibrant $m$-marked $\infty$-categories has the right lifting property against all equations and saturations.*

*Proof.* We will show that such a morphism has the lifting property against all left equations; the exact same argument shows that it also has the lifting property against all right equations.

Consider an isofibration $\pi: X \rightarrow Y$ between two fibrant $m$-marked $\infty$-categories and a lifting problem of $\pi$ against $\Lambda P \rightarrow P$:

![img-7.jpeg](img-7.jpeg)

31

We want to show that $x$ and $y$ can be lifted to $X$.

One first remarks that as $X$ is fibrant, the equation $\Lambda P \rightarrow P$ has solutions in $X$ according to Proposition 3.25. This implies that one can find a lift $(x', y'): P \rightarrow X$ that makes the upper triangle commutative.

Now, in $Y$, we have two solutions of the equation $\Lambda P \rightarrow P$, given by $(\pi(x'), \pi(y'))$ and $(x, y)$. As $Y$ is fibrant, $P \coprod_{\Lambda P} P \rightarrow \text{Uni}_{\Lambda P}^{coh}(P)$ has solutions in $Y$, and there exist marked arrows:

$$z: x \rightarrow \pi(x')$$

$$w: s\#_n \pi(y') \rightarrow y$$

where $s$ is by construction a composite of $z$ with arrows in the source of $\pi(y')$.

By the isofibration property, there exists an arrow

$$\overline{z}: \overline{x} \rightarrow x'$$

over $z$. This arrow induces an arrow $\overline{s}$ over $s$. By the dual isofibration property from Lemma 3.28, there exists an arrow

$$\overline{w}: s\#_n y' \rightarrow \overline{y}$$

over $w$. The pair $(\overline{x}, \overline{y})$ then induces the desired lift $P \rightarrow X$.

Now, to show that isofibrations have the right lifting property against saturations, one simply remarks that lifts against saturations are unique when they exist (saturations are epimorphisms), so as fibrant objects have the right lifting property against these maps, any map between fibrant objects also has the lifting property against all saturations. $\square$

### 3.30 Proposition. *A morphism between fibrant $m$-marked $\infty$-categories is a fibration if and only if it is an isofibration.*

*Proof.* According to Lemma 2.46, the morphism $i_n^+$ is an anodyne cofibration, so all fibrations (between fibrant objects) are isofibrations.

For the converse, as a morphism between fibrant objects is a fibration if and only if it has the right lifting property against generating anodyne cofibrations, which are either equations or saturations, Lemma 3.29 implies that isofibrations between fibrant objects are fibrations. $\square$

As a consequence, we have:

### 3.31 Corollary. *Equations and saturations are acyclic cofibrations.*

*Proof.* The Lemma 3.29 and the Lemma 3.29 implies that equations and saturations have the lifting property against fibration between fibrants. By definition, this implies that these maps are acyclic cofibrations. $\square$

32

### 3.4 Equivalences

We now turn to the characterization of weak equivalences between fibrant objects.

**3.32 Definition.** A morphism $p: X \rightarrow Y$ between fibrant $m$-marked $\infty$-categories is an *equivalence of $m$-marked $\infty$-categories* if:

1. (1) For any arrow $x \in X$, if $p(x)$ is marked in $Y$, then $x$ is marked in $X$.
2. (2) For any object $c \in Y$, there exists an object $\tilde{c} \in X$ and a marked arrow $e: p(\tilde{c}) \rightarrow c$.
3. (3) For any pair of parallel arrows $(a, b)$ in $X$, and any arrow $c: p(a) \rightarrow p(b)$ in $Y$, there exists an arrow $\tilde{c}: a \rightarrow b$ in $X$ and a marked arrow $e: p(\tilde{c}) \rightarrow c$ in $X$.

So informally, a functor is an equivalence if it is conservative, essentially surjective, and “essentially surjective on each Hom $\infty$-category”.

**3.33 Proposition.** A morphism $f: X \rightarrow Y$ between fibrant objects in $\infty$-Cat$^{+m}$ is a weak equivalence in the left semi-model structure of Theorem 2.43 if and only if it is an equivalence in the sense of Definition 3.32.

*Proof.* We will use the characterization of weak equivalences between fibrant objects given in Proposition A.7. We recall that in our left semi-model structure, the generating cofibrations are given by

$$I^\partial = \{i_n: \partial \mathbb{D}_n \rightarrow \mathbb{D}_n \mid n \geqslant 0\} \quad I^{+m} = \{\mathbb{D}_n \rightarrow (\mathbb{D}_n, \overline{\{e_n\}}) \mid n \geqslant 0\}$$

To express the homotopy right lifting property, we need a relative cylinder object for each of these cofibrations.

For a map of the form $\mathbb{D}_n \rightarrow (\mathbb{D}_n, \overline{\{e_n\}})$, we have that the canonical map

$$(\mathbb{D}_n, \overline{\{e_n\}}) \prod_{\mathbb{D}_n} (\mathbb{D}_n, \overline{\{e_n\}}) \rightarrow (\mathbb{D}_n, \overline{\{e_n\}})$$

is an isomorphism, so $(\mathbb{D}_n, \overline{\{e_n\}})$ is already a cylinder object. In particular, the weak left lifting property against these maps is exactly the same as the ordinary left lifting property and it corresponds exactly to the first condition of Definition 3.32.

For the map $i_n: \partial \mathbb{D}_n \rightarrow \mathbb{D}_n$, one obtains a relative cylinder object by considering the factorization:

$$\mathbb{D}_n \prod_{\partial \mathbb{D}_n} \mathbb{D}_n \mapsto (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}) \rightarrow \mathbb{D}_n$$

The first map freely adds a (marked) $(n+1)$-arrow between the two non-trivial arrows of the domain, so it is a cofibration. And one of the two maps $\mathbb{D}_n \rightarrow (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$ was shown to be an anodyne cofibration in Lemma 2.46, hence proving that this is a relative cylinder object for this cofibration. Using this cylinder to express the weak lifting property against $i_n$, one obtains exactly the second condition (for $n = 0$) and the third condition (for $n > 0$) of

33

Definition 3.32. Indeed, suppose given a weak lifting diagram:

![img-8.jpeg](img-8.jpeg)

The solid part of the diagram corresponds to a pair of parallel $(n-1)$-arrows $(a, b)$ in $X$, together with an $n$-arrow $c: p(a) \rightarrow p(b)$ in $Y$. The top dotted morphism gives us an arrow $\tilde{c}: a \rightarrow b$, while the bottom dotted morphism corresponds to a marked $(n+1)$-arrow $e: p(\tilde{c}) \rightarrow c$. So this lifting condition corresponds exactly to the third point of Definition 3.32 (with the second point corresponding to the case $n=0$).

### 3.5 The Saturated Inductive Localization.

Proposition 3.25 produces a characterization of fibrant objects of the left semi-model structure of Theorem 2.43: a marked $\infty$-category is fibrant if the marked arrows have inverses and if an arrow isomorphic to a marked arrow is marked.

A careful reader might have noticed, however, that this is not sufficient to show that the marked arrows are exactly the arrows that have inverses in the sense of Definition 3.17.

**3.34 Example.** Let $C$ be a category, seen as an $\infty$-category with no non-identity arrows of dimension strictly superior to 1. We endow $C$ with the marking $C^\flat$, where only the identity arrows are marked.

With this marking, $C$ is fibrant; indeed, it satisfies all the conditions of Proposition 3.25. But if the category $C$ has non-identity invertible arrows, these would be arrows that have inverses in the sense of Definition 3.17 without being marked.

In this section, we “fix” this problem by introducing a Bousfield localization in which the fibrant objects have these properties.

**3.35 Definition.** A marked $\infty$-category $C$ is said to satisfy the 2-out-of-6 property if given three composable $n$-arrows $f$, $g$, and $h$ such that $f\#_{n-1}g$ and $g\#_{n-1}h$ are marked, then $f$, $g$, and $h$ are marked.

**3.36 Remark.** If $C$ is a fibrant $m$-marked $\infty$-category, then the relation $f \sim g$ defined by $\exists c: f \rightarrow g$ a marked $(n+1)$-arrow, is an equivalence relation on $n$-arrows. Indeed, it is reflexive and transitive as identities are marked and composites of marked arrows are marked, and it is symmetric as marked arrows have inverses.

This equivalence relation is moreover compatible with all composition operations, so that one can define a “homotopy $n$-category” $h_n C$, which is an

34

$n$-category whose $k$-(arrows for $k < n$ are those of $C$ and its $n$-arrows are equivalence classes for this relation. We will use in particular that given two parallel $(n-2)$-arrows $u, v$ in $C$ we have a category $h_n C(u, v)$ whose objects are $(n-1)$-arrows $u \rightarrow v$ and whose morphisms are equivalence classes of $n$-arrows between them.

**3.37 Lemma.** *For an $m$-marked $\infty$-category $C$, the following conditions are equivalent:*

(1) *An arrow in $C$ is marked if and only if it has an inverse in the sense of Definition 3.17.*
(2) *$C$ is fibrant in the inductive left semi-model structure $\infty$-$\mathbf{Cat}_{Ind}^{+m}$ of Theorem 2.43 and satisfies the 2-out-of-6 property.*

*Proof.* We first consider $C$ an $m$-marked $\infty$-category which satisfies (1), and we check it fulfills the conditions of Definition 3.18. By Proposition 3.25, this will imply that $C$ is fibrant. The first condition of Definition 3.18 is immediate; we check the second condition. Let $b$ and $c: a \rightarrow b$ be two marked arrows. By assumption, $b$ is invertible, and there exists then an arrow $b^{-1}$ and two marked arrows $c: b^{-1}\#_n b \rightarrow \mathbb{I}$ and $v: b\#_n b^{-1} \rightarrow \mathbb{I}$. We then have marked arrows:

$$b^{-1}\#_n a \stackrel{b^{-1}\#_n c}{\rightarrow} b^{-1}\#_n b \stackrel{c}{\rightarrow} \mathbb{I}$$

$$a\#_n b^{-1} \stackrel{c\#_n b^{-1}}{\rightarrow} b\#_n b^{-1} \stackrel{c}{\rightarrow} \mathbb{I}$$

This shows that $b^{-1}$ is also an inverse for $a$, and hence if all arrows with an inverse are marked, $a$ is marked as well. Note that if it is $a$ which is marked in the first place, then one can consider an inverse $c^{-1}: b \rightarrow a$ and apply the same argument.

Next, we show that $C$ satisfies 2-out-of-6. For this, we can rely on Remark 3.36. An $n$-arrow has an inverse in the sense of Definition 3.17 if and only if it is an isomorphism in the category $h_n C(u, v)$ where $u$ and $v$ are its $(n-2)$-dimensional source and target. Our assumption is then that an $n$-arrow is marked if and only if its equivalence class is invertible in the category $h_n C(u, v)$. The fact that marked arrows satisfy 2-out-of-6 then follows from the fact that isomorphisms in a category satisfy the 2-out-of-6 condition.

Conversely, assuming that $C$ satisfies condition (2), we have that marked arrows have inverses because $C$ is fibrant and Proposition 3.25. If an arrow $a$ has an inverse $a^{-1}$, then both $a\#_{n-1} a^{-1}$ and $a^{-1}\#_{n-1} a$ are marked because they are equivalent to identities, and it follows from the 2-out-of-6 condition that $a$ (and $a^{-1}$) is marked. $\square$

**3.38 Theorem.** *The inductive semi-model structure $\infty$-$\mathbf{Cat}_{Ind}^{+m}$ of Theorem 2.43 admits a Bousfield localization (as a left semi-model structure) in which the fibrant objects are the marked $\infty$-categories that satisfy the equivalent conditions of Lemma 3.37.*

*We call this left semi-model structure the saturated inductive left semi-model structure and denote it by $\infty$-$\mathbf{Cat}_{Sat-Ind}^{+m}$.*

As a Bousfield localization, this left semi-model structure has the same cofibrations and the same fibrations between fibrant objects as the left semi-model structure from Theorem 2.43.

35

*Proof.* The key point here is that the 2-out-of-6 condition for a marked $\infty$-category corresponds to the lifting property against certain cofibrations.

For each $n$, we consider the polygraphs $X_n$ generated by three composable $n$-arrows

$$\mathbb{D}_n \prod_{\mathbb{D}_{n-1}} \mathbb{D}_n \prod_{\mathbb{D}_{n-1}} \mathbb{D}_n$$

where each pushout uses the target maps on the left and the source map on the right. We call $f$, $g$, and $h$ the three $n$-dimensional generators of $X_n$. We consider the map $s_n$:

$$s_n: \left( X_n, \overline{\{f\#_{n-1}g, g\#_{n-1}h\}} \right) \rightarrow \left( X_n, \overline{\{f, g, h\}} \right)$$

which is the identity of $X_n$ (with two different markings). $s_n$ is a cofibration, and a marked $m$-category has the right lifting property against all the $s_n$ if and only if it satisfies the 2-out-of-6 property.

Using Theorem A.8, we define $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+m}$ as the left Bousfield localization of $\infty$-$\mathbf{Cat}_{\text{Ind}}^{+m}$ at the set $\{s_n\}_{n \in \mathbb{N}}$.

Lemma A.9 characterizes the fibrant objects of $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+m}$ as the fibrant objects of $\infty$-$\mathbf{Cat}_{\text{Ind}}^{+m}$ that have the right lifting property against the $s_n$ and their higher homotopy codiagonal maps $\nabla^k(s_n)$. However, as $s_n$ is a cofibration $A \rightarrow B$ that only adds some marking, its codiagonal $B \coprod_A B \rightarrow B$ is an isomorphism, and so the $\nabla^k s_n$ can all be taken to be isomorphisms; we only need to check the right lifting property with respect to the maps $s_n$ themselves. Thus, fibrant objects of $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+m}$ correspond to the marked $\infty$-categories that satisfy the equivalent conditions of Lemma 3.37. This concludes the proof. $\square$

## 4 Comparison with Other Model Structures

### 4.1 Truncation Functors

**4.1 Definition.** Let $m < p \leq \infty$. There is a functor:

$$\begin{array}{rcl} \pi_m: & \infty\text{-}\mathbf{Cat}^{+p} & \rightarrow \infty\text{-}\mathbf{Cat}^{+m} \\ & (X, M) & \mapsto (X, \overline{M}). \end{array}$$

that marks every arrow of dimension $m+1$, an obvious inclusion functor:

$$\begin{array}{rcl} \iota_p: & \infty\text{-}\mathbf{Cat}^{+m} & \rightarrow \infty\text{-}\mathbf{Cat}^{+p} \\ & (X, M) & \mapsto (X, M) \end{array}$$

and eventually, a functor:

$$\begin{array}{rcl} \tau_m: & \infty\text{-}\mathbf{Cat}^{+p} & \rightarrow \infty\text{-}\mathbf{Cat}^{+m} \\ & (X, M) & \mapsto (X \cap M_{>m}, M) \end{array}$$

where $X \cap M_{>m}$ is the sub $\infty$-category of $X$ whose arrows of dimension strictly superior to $m$ are the ones in $M$. As $M$ is assumed to be closed under composition and contains the identities, $X \cap M_{>m}$ is indeed an $\infty$-category.

These functors fit into the following adjunctions:

$$\pi_m \dashv \iota_p \dashv \tau_m.$$

36

**4.2 Notation.** Because $\iota_p$ is the inclusion of a full subcategory, we will often identify $X$ and $\iota_p X$ in our notation. In the same way, for a morphism $f \in \operatorname{Hom}(X, \tau_m(Y))$, the corresponding morphism in $\operatorname{Hom}(\iota_p X, Y)$ will also be denoted $f$.

**4.3 Proposition.** *For $m < p$, the adjoint pairs $(\pi_m \dashv \iota_p)$ and $(\iota_p \dashv \tau_m)$ are Quillen pairs (definition Definition A.5) both between $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$ and $\infty\text{-Cat}_{\text{Sat-Ind}}^{+p}$ and between $\infty\text{-Cat}_{\text{Ind}}^{+m}$ and $\infty\text{-Cat}_{\text{Ind}}^{+p}$.*

*Proof.* The left adjoint functors $\pi_m$ and $\iota_p$ obviously preserve cofibrations. Their respective right adjoint functors $\iota_p$ and $\tau_m$ obviously preserve the isofibrations of Section 3.3, and fibrant objects for either the inductive (characterized by Definition 3.18 and Proposition 3.25) or saturated inductive model structures (whose characterization is given in Lemma 3.37). This implies that the right adjoint functors preserve fibrations between fibrant objects. The left adjoint then also preserves acyclic cofibrations as well, and this concludes the proof. $\square$

**4.4 Proposition.** *For any $m < p \leq \infty$, a morphism $f$ in $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$ is a cofibration (resp. acyclic cofibration, resp. fibration, resp. acyclic fibration, resp. weak equivalence) if and only if $\iota_p(f)$ is in $\infty\text{-Cat}_{\text{Sat-Ind}}^{+p}$.*

*Proof.* This directly follows from Proposition 4.3 and from the fact that $\iota_p$ is the inclusion of a full subcategory. $\square$

As mentioned in the introduction, we can consider the two towers of left semi-model structures:

$$\begin{aligned} &\infty\text{-Cat}_{\text{Sat-Ind}}^{+0} \xleftarrow{\tau_n} \infty\text{-Cat}_{\text{Sat-Ind}}^{+1} \xleftarrow{\tau_1} \infty\text{-Cat}_{\text{Sat-Ind}}^{+2} \xleftarrow{\tau_2} \dots \xleftarrow{\tau_{n-1}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n} \xleftarrow{\tau_n} \dots \\ &\infty\text{-Cat}_{\text{Sat-Ind}}^{+0} \xleftarrow{\tau_n} \infty\text{-Cat}_{\text{Sat-Ind}}^{+1} \xleftarrow{\tau_1} \infty\text{-Cat}_{\text{Sat-Ind}}^{+2} \xleftarrow{\tau_2} \dots \xleftarrow{\tau_{n-1}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n} \xleftarrow{\tau_n} \dots \end{aligned}$$

and take the projective limit of either tower to get a definition of 'strict $(\infty, \infty)$-categories'.

Our goal in this section is to show that the left semi-model structure $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$ is equivalent to the limit of the second tower (with $\tau$ functors). Here, by projective limit, we mean a homotopy theoretic limit of these towers, that is, a homotopy limit of the corresponding tower of $(\infty, 1)$-categories. Such projective limits of model structures have been studied in [11] and [20], and we will use the construction from these papers.

**4.5 Remark.** It should be noted that the results from [11] and [20] are only proved for Quillen model structures, so they do not immediately apply to the left semi-model structures that we are using here. The proof from these two papers easily adapts to the setting of left semi-model structures with very few modifications, so it should be safe to assume these results can be applied here as well. Though to avoid relying on this, we will give an independent proof that the left semi-model structure we use as a model of these projective limits exists and state our main theorem as an equivalence with this left semi-model structure. The only aspect that still relies on applying the results of [11] or [20] to left semi-model structures is in order to interpret our results as saying something about homotopy limits of towers.

37

**4.6 Definition.** We define the category $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$, the *putative lax limit* of $\propto \text{-Cat}^{+m}$, whose objects are sequences $X_{\bullet} = \{(X_n, f_n)\}_{n \in \mathbb{N}}$ where $X_n \in \propto \text{-Cat}^{+n}$ and $f_n: X_n \to \tau_n X_{n+1}$. By adjunction, objects are in bijection with sequences

$$X_0 \xrightarrow{f_0} X_1 \xrightarrow{f_1} \dots \xrightarrow{f_{n-1}} X_n \xrightarrow{f_n} \dots$$

where each $X_n \in \propto \text{-Cat}^{+n}$.

**4.7 Proposition.** *There exists a left semi-model structure on $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$, called the putative lax-limit left semi-model structure and denoted by $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}_{\text{Sat-Ind}}^{+n}$, where fibrations and weak equivalences are pointwise fibrations and weak equivalences of the saturated inductive left semi-model structure, and cofibrations are morphisms $h: X_{\bullet} \to Y_{\bullet}$ such that $h_0: X_0 \to Y_0$ is a cofibration in $\propto \text{-Cat}^{+0}$, and for all $n$, the dotted morphism in the following diagrams is a cofibration in $\propto \text{-Cat}^{+i+1}$:*

![img-9.jpeg](img-9.jpeg)

*Proof.* First, let us notice that $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$ can be identified with the full subcategory of functors $X: \mathbb{N} \to \propto \text{-Cat}^{+\infty}$ such that $X_n \in \propto \text{-Cat}^{+n}$.

There is a left semi-model structure on such functors, where fibrations and weak equivalences are pointwise: the Reedy (or projective) model structure as presented at the end of Appendix A. The cofibrations of this model structure are as described in the proposition, and we claim that this model structure “restricts” to $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$.

By this last assertion, we mean that given two sequences $X_{\bullet}, Y_{\bullet} \in \text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$ and a map $X \to Y$, the factorizations of $f$ as (cofibration, acyclic fibration) or (acyclic cofibration, fibration) in the Reedy left semi-model structure can be done within $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$, which shows that one can deduce all the properties in the definition of semi-model structures from the fact that they are satisfied by the Reedy model structure.

We will prove the claim for the (acyclic cofibration, fibration) factorization system, the proof for the other one being identical. We can construct by induction on $n$ a functorial factorization $X_n \to E_n \to Y_n$ of $p_n$ such that $X_0 \to E_0 \to Y_0$, and $X_n \coprod_{X_{n-1}} E_{n-1} \to E_n \to Y_n$ for $n > 0$, is an acyclic cofibration followed by a fibration of $\propto \text{-Cat}_{\text{Sat-Ind}}^{+n}$. As the functor $\iota_{\infty}: \propto \text{-Cat}^{+m} n_{\text{Sat-Ind}} \to \propto \text{-Cat}_{\text{Sat-Ind}}^{+m}$ is both a left and right Quillen functor, it preserves acyclic cofibrations and fibrations, and the resulting factorization $X \to E \to Y$ is an acyclic cofibration followed by a fibration of the Reedy left semi-model structure.

We can then deduce that the Reedy left semi-model structure “restricts” to $\text{pLimLax}_{n \in \mathbb{N}} \propto \text{-Cat}^{+n}$, which concludes the proof. $\square$

38

### 4.8 Definition. We have an adjunction

![img-10.jpeg](img-10.jpeg)

where the left adjoint sends a sequence $X_{\bullet}$ to its colimit:

$$c(X_{\bullet}) := \underset{n \in \mathbb{N}}{\operatorname{Colim}} X_n,$$

and the right adjoint sends an $\infty$-marked $\infty$-category $X$ on the sequence

$$\tau_0(X) \to \cdots \to \tau_n(X) \to \ldots$$

**4.9 Proposition.** *This adjunction induces a Quillen adjunction between $p\text{LimLax}_{n \in \mathbb{N}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n}$ and $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$ where the left adjoint preserves weak equivalences and fibrant objects.*

*Proof.* The functor $c$ preserves cofibrations and acyclic cofibrations because of Lemma A.11, and hence is a left Quillen functor.

Secondly, because the left semi-model structure on $\infty\text{-Cat}^{+\infty}$ is $\omega$-combinatorial, its weak equivalences are closed under $\omega$-filtered colimits (this is shown for Quillen model structures as Proposition 7.3 of [17], and for left semi-model structures as Proposition 7.7 of [22]). This implies that the functor $c$ also preserves weak equivalences: if $f: X_{\bullet} \to Y_{\bullet}$ is an equivalence in $\text{pLimLax}_{n \in \mathbb{N}} \infty\text{-Cat}^{+n}$, then the map

$$c(f): \underset{n \in \mathbb{N}}{\operatorname{Colim}} X_n \to \underset{n \in \mathbb{N}}{\operatorname{Colim}} Y_n$$

is a filtered colimit of weak equivalences, and so is a weak equivalence. This implies that $c$ also preserves acyclic cofibrations, which concludes the proof.

**4.10 Proposition.** *There is a left Bousfield localization of $p\text{LimLax}_{n \in \mathbb{N}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n}$, called the putative limit structure and denoted by $p\text{Lim}_{n \in \mathbb{N}} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n}$, where $X_{\bullet}$ is fibrant if and only if it is fibrant in the putative lax-limit left semi-model model structure and if for all integers $n$, $f_n: X_n \to \tau_n X_{n+1}$ is a weak equivalence. Moreover, weak equivalences between fibrant objects are pointwise equivalences.*

**4.11 Remark.** According to our (unproven) claim (see Remark 4.5) that the results of [11] or [20] can be applied to left semi-model structures, the $\infty$-category obtained as the localization of this Bousfield localization would be equivalent to the limit of the $\infty$-categories obtained as the localization of the $\infty\text{-Cat}^{+n}$ (with the $\tau_n$ functors as transitions).

We need to introduce certain constructions before proving the proposition:

**4.12 Construction.** Let $k$ be any positive integer. We define

$$\underset{i \in \{k, k+1\}}{\text{pLimLax}}(\infty\text{-Cat}^{+i}, \tau_i)$$

39

to be the category whose objects are triples $(X, X', f: X \to \tau_k(X'))$ where $X$ and $X'$ are respectively $k$-marked and $(k+1)$-marked $\infty$-categories. By adjunction, these objects are in bijection with sequences:

$$X \xrightarrow{f} X'$$

where $X$ and $X'$ are respectively $k$-marked and $(k+1)$-marked $\infty$-categories. There is an adjunction

$$\text{pLimLax}_{i \in \{k, k+1\}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i) \xrightarrow[\substack{\perp \\ \beta_k]{\alpha_k} \text{pLimLax}_{i \in \mathbb{N}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$$

where the left adjoint $\alpha_k$ sends $X \to Y$ to the sequence

$$\emptyset \to \cdots \to \emptyset \to X \xrightarrow{f} Y \to Y \to \cdots \to Y \to \cdots$$

while the right adjoint $\beta_k$ sends $X_\bullet$ to

$$X_k \xrightarrow{f} X_{k+1}.$$

**4.13 Lemma.** Let $i: A \mapsto B$ be a cofibration between cofibrant objects in $\infty\text{-}\mathbf{Cat}^{+k}$ and $I_A B$ a relative cylinder object for $i$ (as in Proposition A.7). Let $\phi$ be the morphism in $\text{pLimLax}_{i \in \{k, k+1\}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$ given by the square:

$$\begin{array}{c} A \longrightarrow B \\ \downarrow \qquad \qquad \downarrow \\ B \longrightarrow I_A B \end{array}$$

There exists a morphism $\psi$ in $\text{pLimLax}_{i \in \{k, k+1\}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$ corresponding to a square

$$\begin{array}{c} B \coprod_A B \longrightarrow I_A B \coprod_B I_A B \\ \downarrow \qquad \qquad \qquad \downarrow \\ I_A B \coprod_B I_A B \longrightarrow W \end{array} \tag{1}$$

where $W$ is a relative cylinder object for $B \coprod_A B \to I_A B$, and such that $\alpha_k(\psi)$ is a relative cylinder for $\alpha_k(\phi)$.

Proof. One can first observe that the horizontal map $B \coprod_A B \mapsto I_A B \coprod_B I_A B$ is already a relative cylinder object for $A \mapsto B$. By definition of the putative lax-limit left semi-model structure, we then have to construct a square of shape (1), with $W$ a relative cylinder object for $B \coprod_A B \to I_A B$, and such that the canonical map

$$(I_A B \coprod_B I_A B) \coprod_{(B \coprod_A B)} (I_A B \coprod_B I_A B) \to W$$

is a weak equivalence.

40

We will proceed in three steps. We first factorize the leftmost map:

![img-11.jpeg](img-11.jpeg)

We then forms the pushout $P$:

![img-12.jpeg](img-12.jpeg)

Eventually, we factor the map $P \rightarrow I_A B$ can into a cofibration followed by a weak equivalence.

![img-13.jpeg](img-13.jpeg)

Which gives a relative cylinder object, and hence a homotopy codiagonal for $\phi$ of the form:

![img-14.jpeg](img-14.jpeg)

But one can see that the object $W$ we constructed above is itself a relative cylinder object for the map $B \coprod_A B \rightarrow I_A B \coprod_B I_A B$, which concludes the proof.

*Proof of Proposition 4.10.* Let $I_k$ be the set of cofibrations of $\text{pLimLax}_{i \in \mathbb{N}}(\infty\text{-}\mathbf{Cat}^{+i}, \tau_i)$ of the form

$$\{\alpha_k(A \rightarrow B) \rightarrow \alpha_k(B \rightarrow I_A B)\}$$

where $i: A \rightarrow B$ is a generating cofibration of $\infty\text{-}\mathbf{Cat}^{+k}$ and $I_A B$ is a relative cylinder object for $i$.

41

We then define the putative limit left semi-model structure as the left Bousfield localization of the lax-putative limit left semi-model structure by all sets $I_k$ (for all values of $k$). The existence of this localization is asserted by Theorem 7.3 of [24]. By Lemma A.9, fibrant objects correspond to morphisms having the right lifting property against iterated homotopy codiagonals of maps in $I_k$. Since weak equivalences between fibrant objects of the localized left semi-model structure correspond to weak equivalences in the unlocalized left semi-model structure, they also correspond to pointwise weak equivalences.

To show that the adjunction given in Definition 4.8 induces an adjunction between the putative limit left semi-model structure and the inductive left semi-model structure, one has to demonstrate that for any integer $k$, and $\phi \in I_k$, $c(\phi)$ is a weak equivalence of the inductive left semi-model structure. Let $i: A \mapsto B$ be the generating cofibration of $\infty$-$\mathbf{Cat}^{+k}$ such that $\phi$ is

$$\alpha_k(A \to B) \to \alpha_k(B \to I_A B).$$

The morphism $c(\phi)$ then corresponds to $B \to I_A B$, which is a weak equivalence by the definition of a relative cylinder object.

To conclude the characterization of fibrant objects of this left semi-model structure, we will show that for any fibrant object $(X_i, f_i)$ of the unlocalized left semi-model structure, the following conditions are equivalent:

1. $(X_i, f_i)$ has the right lifting property against all maps in $I_k$.
2. For any $k$, $f_k: X_k \to \tau_k X_{k+1}$ is a weak equivalence.
3. $(X_i, f_i)$ has the right lifting property against all maps of the form $\{\alpha_k(A \to B) \to \alpha_k(B \to I_A B)\}$ where $A \to B$ is an arbitrary cofibration in $\infty$-$\mathbf{Cat}^{+k}$.
4. $(X_i, f_i)$ has the right lifting property against iterated homotopy codiagonals of maps in $I_k$.

The implications $(1) \Rightarrow (2)$ and $(2) \Rightarrow (3)$ are a reformulation of Proposition A.7. The implication $(3) \Rightarrow (4)$ is Lemma 4.13. Finally, the implication $(4) \Rightarrow (1)$ is straightforward. $\square$

**4.14 Theorem.** *The Quillen adjunction between the putative limit left semi-model structure of Proposition 4.10 and the inductive left semi-model structure is a Quillen equivalence.*

$$\underset{n \in \mathbb{N}}{p \text{Lim}} \infty\text{-}\mathbf{Cat}_{\text{Sat-Ind}}^{+n} \simeq \infty\text{-}\mathbf{Cat}_{\text{Sat-Ind}}^{+\infty}$$

*Proof.* As the left adjoint preserves weak equivalence and fibrant objects of the unsaturated left semi-model structure by Proposition 4.9, one has to show that for every fibrant $\infty$-marked $\infty$-category $X$, and for every cofibrant and fibrant sequence $X_\bullet$ of the putative limit left semi-model structure, we have two weak equivalences:

$$c\tau X \to X \quad \text{and} \quad X_\bullet \to \tau c X_\bullet.$$

The first one is immediate because

$$X \cong \underset{n \in \mathbb{N}}{\text{Colim}} \tau_n X.$$

42

Let $X_{\bullet}$ be a cofibrant and fibrant object of the putative limit left semi-model structure. Because $X_{\bullet}$ and $\tau \in X_{\bullet}$ are fibrant, the second comparison morphism is a weak equivalence if and only if for all $k$, $X_k \rightarrow \text{Colim}_{n \in \mathbb{N}} \tau_k(X_n)$ is a weak equivalence. In order to show this, consider the diagram:

![img-15.jpeg](img-15.jpeg)

where, by two out of three, all the vertical morphisms are weak equivalences. The previous diagram corresponds to a weak equivalence in the unlocalized left semi-model structure on $\text{pLimLax}_{n \in \mathbb{N}} \infty\text{-Cat}^{+n}$ between $X_{\min(\bullet,k)}$ and $(\tau_k(X_{\bullet}))$. Because the left adjoint $c$ preserves weak equivalences of the unlocalized left semi-model structure by proposition Proposition 4.9, this induces a weak equivalence:

$$X_k \cong \text{Colim}_{n \in \mathbb{N}} X_{\min(n,k)} \rightarrow \text{Colim}_{n \in \mathbb{N}} \tau_k(X_n)$$

## 4.2 Coinductive Localization and Comparison with $\infty\text{-Cat}_{\text{Can}}$

Following [30, Definition 4.2], we can also give a coinductive notion of invertible arrows in an $\infty$-category. In short, an $n$-arrow $a: \pi_{n-1}^- a \rightarrow \pi_{n-1}^+ a$ is said to be coinductively invertible if there is an $n$-arrow $\bar{a}: \pi_{n-1}^+ a \rightarrow \pi_{n-1}^- a$ and two coinductively invertible $(n+1)$-arrows

$$c: \bar{a} \#_{n-1} a \rightarrow \mathbb{I}_{\pi_{n-1}^-} a$$

$$c': a \#_{n-1} \bar{a} \rightarrow \mathbb{I}_{\pi_{n-1}^+} a$$

The notion is called “weakly invertible” in [30]. Note that this is a coinductive definition, that is an arrow is coinductively invertible if there are two such arrows $c$ and $c'$, which themselves have such “weak inverses” $\bar{c}$ and $\bar{c}'$ with four witness $n+2$ arrows, which are themselves coinductively invertible, i.e., have weak inverses and there are eight $(n+3)$-arrows witnessing this, and so on... We can make this definition more formal as follows:

**4.15 Definition.** Let $D$ be an $\infty$-category. An *invertibility set* in $D$ is a set $E = \prod_{n>0} E_n$ with $E_n \subset D_n$ such that, for all $n > 0$ and $a \in E_n$, there exists $\bar{a} \in E_n$ of the form $\bar{a}: \pi_{n-1}^+ a \rightarrow \pi_{n-1}^- a$ and $c, c' \in E_{n+1}$ of the form

$$c: \bar{a} \#_{n-1} a \rightarrow \mathbb{I}_{\pi_{n-1}^-} a \quad \text{and} \quad c': a \#_{n-1} \bar{a} \rightarrow \mathbb{I}_{\pi_{n-1}^+} a.$$

**4.16 Definition.** Let $D$ be an $\infty$-category and $n > 0$. Given $a \in D_n$, the $n$-arrow $a$ is *coinductively invertible* if there exists an invertibility set $E$ such that $a \in E$.

**4.17 Proposition.** Let $D$ be an $\infty$-category and $n > 0$. An $n$-arrow $a$ is *coinductively invertible* if and only if there exists an $n$-arrow $\bar{a}$ of the form $\bar{a}: \pi_{n-1}^+ a \rightarrow \pi_{n-1}^- a$ and two coinductively invertible $(n+1)$-arrows $c, c'$ of the form

$$c: \bar{a} \#_{n-1} a \rightarrow \mathbb{I}_{\pi_{n-1}^-} a \quad \text{and} \quad c': a \#_{n-1} \bar{a} \rightarrow \mathbb{I}_{\pi_{n-1}^+} a.$$

43

*Proof.* This is [32, Lemme 1.1.8].

**4.18 Lemma.** *Let $X$ be an $\infty$-category, and $M$ the set of coinductively invertible arrows. The set $M$ satisfies the two following properties:*

(2) *For all $c: a \rightarrow b$ in $M$, $a \in M \Leftrightarrow b \in M$.*

*Proof.* The first point is the third and the fourth point of example 1.1.9 of [32], and the second one is a consequence of proposition 1.1.10 of *loc. cit.*

**4.19 Proposition.** *If $X$ is a fibrant $m$-marked $\infty$-category, all marked arrows in $X$ are coinductively invertible in the underlying $\infty$-category.*

*Proof.* The Lemma 3.23 directly implies that the set of all marked arrows is an invertibility set. By definition, all marked arrows are then coinductively invertible.

**4.20 Proposition.** *Let $X$ be an $\infty$-category and $M$ the set of coinductively invertible arrows. The marked $\infty$-category $(X, M)$ is then fibrant in the saturated inductive semi-model structure.*

*Proof.* Proposition 4.17 shows that $(X, M)$ satisfies point (1) of Lemma 3.37, which is a characterization of the fibrant objects in the saturated inductive semi-model structure (see Theorem 3.38).

Next we remark that coinductively invertible arrows can be characterized using a lifting property:

**4.21 Definition.** Let $G_1$ be the $\infty$-category obtained from the factorization of $\mathbb{D}_1 \rightarrow \mathbb{D}_0$ as a cofibration $k_1: \mathbb{D}_1 \rightarrow G_1$ followed by an acyclic fibration $t_1: G_1 \rightarrow \mathbb{D}_1$. We then define $G_n := \Sigma^{n-1} G_1$ and $k_n := \Sigma^{n-1} k_1: \mathbb{D}_n \rightarrow G_n$, $t_n := \Sigma^{n-1} t_1: G_n \rightarrow \mathbb{D}_{n-1}$. Let us recall that the definition of the functor $\Sigma^{n-1}$ is given in Definition 2.6. As the suspension preserves acyclic fibrations and cofibrations, the pair $(k_n, t_n)$ is a factorization of $\mathbb{D}_n \rightarrow \mathbb{D}_{n-1}$ into a cofibration followed by an acyclic fibration.

**4.22 Proposition.** *Let $X$ be an $\infty$-category, and $f$ an $n$-arrow of $X$. There exists a lifting in the following diagram:*

![img-16.jpeg](img-16.jpeg)

*if and only if $f$ is coinductively invertible.*

*Proof.* This is a reformulation of lemma 4.36 of [30].

We recall now the model structure on $\infty$-Cat constructed in [30].

**4.23 Theorem.** *There exists a model structure on $\infty$-Cat, called the canonical model structure and denoted by $\infty$-Cat$_{Can}$ such that*

44

(1) *cofibrant $\infty$-categories are polygraphs.*
(2) *Acyclic fibrations are the morphisms having the left lifting property with respect to the set of morphisms $\{\partial\mathbb{D}_n \to \mathbb{D}_n, n \in \mathbb{N}\}$.*
(3) *Fibrations are the morphisms having the left lifting property with respect to the set of morphisms $\{\mathbb{D}_n \xrightarrow{i_n^*} \mathbb{D}_{n+1} \xrightarrow{k_{n+1}} G_{n+1}, n \in \mathbb{N}\}$.*
(4) *Cofibrations and acyclic cofibrations are morphisms having the right lifting property against, respectively, acyclic fibrations and fibrations..*

*Proof.* This is Theorem 4.39 and 5.3 of [30]. The first point is the main result of [35]. □

**4.24 Definition.** The *coinductive left semi-model structure* on $\infty$-Cat$^{+\infty}$, denoted by $\infty$-Cat$^{+\infty}_{\text{Coind}}$, is the left Bousfield localization of the left semi-model structure on $\infty$-Cat$^{+\infty}_{\text{Sat-Ind}}$ by the set of morphisms:

$$\{(G_n, \vec{\emptyset}) \rightarrow \mathbb{D}_{n-1}^b, n \in \mathbb{N}^*\}$$

**4.25 Remark.** Remark that if we define $\tilde{G}_n := \pi_{n-1}(G_n, \vec{\emptyset})$, the sequence

$$(G_n, \vec{\emptyset}) \xrightarrow{p_n} \tilde{G}_n \xrightarrow{k_n} \mathbb{D}_{n-1}^b$$

is a factorization as a cofibration followed by an acyclic fibration in the inductive left semi-model structure. Using the terminology of [24], we will say that the cofibration $p_n$ represents the morphism $(G_n, \vec{\emptyset}) \rightarrow \mathbb{D}_{n-1}^b$. As we can see in the construction of the left Bousfield localization provided in the proof of Theorem 7.3 of *op cit*, a marked $\infty$-category $X$ is fibrant in the coinductive left semi-model structure if and only if $X$ is fibrant in the inductive left semi-model structure and has the right lifting property against morphisms $k_n$ and iterated homotopy codiagonals of $k_n$ for all $n > 0$.

**4.26 Proposition.** *Let $X$ be a fibrant $\infty$-marked $\infty$-category in the inductive left semi-model structure. Then $X$ is fibrant in the coinductive left semi-model structure if and only if marked arrows are exactly the coinductively invertible arrows of the underlying $\infty$-category.*

*Proof.* Suppose first that $X$ is fibrant in the coinductive left semi-model structure and let $f$ be a coinductively invertible arrow of the underlying $\infty$-category. By Proposition 4.22, this corresponds to a morphism $f: (G_n, \vec{\emptyset}) \rightarrow X$. As remarked in Remark 4.25, $X$ has the right lifting property against $k_n$, which implies that $f$ can be lifted to $\pi_{n-1}(G_n)$. That shows that $f$ is marked. Moreover, Lemma 3.23 states that all marked arrows are coinductively invertible. This shows that marked arrows exactly correspond to coinductively invertible ones.

For the other direction, suppose that $X$ is a marked $\infty$-category, fibrant in the inductive left semi-model structure, whose marked arrows are the coinductively invertible ones. We want to show that $X$ is fibrant in the coinductive left semi-model structure. According to Proposition 4.20, $X$ is fibrant in the nonlocalized left semi-model structure. We then have to show that for all integers $n > 0$, $X$ has the left lifting property against $k_n$ and iterated homotopy

45

codiagonals of $k_n$. Remark now that, as $\vec{G}_n \coprod_{(G_n, \vec{\mathbb{S}})} \vec{G}_n = \vec{G}_n$, all the iterated homotopy codiagonals are identities. To conclude, it is enough to show that $X$ has the left lifting property against morphisms $k_n$ for $n > 0$, which is obvious by assumption and by the Proposition 4.22. $\square$

**4.27 Lemma.** *Let $X$ be an $\infty$-category, and let $M$ be the set of coinductive invertible arrows. The canonical morphism $X^\flat \rightarrow (X, M)$ is an anodyne cofibration of the coinductive left semi-model structure.*

*Proof.* We denote by $(X, M')$ the marked $\infty$-category obtained as the pushout of the following span:

$$\coprod_{\operatorname{Hom}(G_n, X)} \vec{G}_n \xleftarrow{\coprod_{P_n}} \coprod_{\operatorname{Hom}(G_n, X)} G_n^\flat \longrightarrow X^\flat$$

By stability by coproducts and pushouts, the canonical morphism $X^\flat \rightarrow (X, M')$ is an anodyne cofibration of the coinductive left semi-model structure.

Moreover, Lemma 4.9 of [30] applied to the acyclic fibration $G_n \rightarrow \mathbb{D}_{n-1}$ implies that any arrow of $G_n$ of dimension higher or equal to $n$ is coinductively invertible. In particular, every marked arrow of $\vec{G}_n$ is coinductively invertible. We then have $M' \subset M$, and 4.22 implies that $M \subset M'$. Furthermore, Proposition 4.26 implies that $(X, M)$ is a fibrant object of the coinductive left semi-model structure. $\square$

**4.28 Theorem.** *The adjunction*

$$(-)^\flat : \infty\text{-}\mathbf{Cat} \xrightarrow{\quad} \infty\text{-}\mathbf{Cat}^{+\infty} : U$$

*induces a Quillen equivalence between $\infty\text{-}\mathbf{Cat}_{Can}$ and $\infty\text{-}\mathbf{Cat}_{Coind}^{+\infty}$.*

*Proof.* We first show that this adjunction is a Quillen adjunction.

Remark that the left adjoint obviously preserves generating cofibrations. Furthermore, for any integer $n$, the morphism

$$\mathbb{D}_n^\flat \xrightarrow{i_n^-} \mathbb{D}_{n+1}^\flat \xrightarrow{k_{n+1}} G_{n+1}^\flat$$

admits a retract given by the weak equivalence $G_{n+1}^\flat \rightarrow \mathbb{D}_n^\flat$, and so it is a acyclic cofibration of $\infty\text{-}\mathbf{Cat}_{Can}^{+m}$. The left adjoint then preserves cofibration and acyclic cofibration, which implies that the adjunction is a Quillen adjunction.

We now show that this adjunction is a Quillen equivalence. Let $X$ be a cofibrant $\infty$-category and let $M$ be the set of coinductive invertible arrows of $X$. The lemma Proposition 4.26 and Lemma 4.27 imply that $(X, M)$ is the fibrant replacement of $X^\flat$. The derived unit then corresponds to the isomorphism $U(X^\flat)_{fib} \cong U(X, M) \cong X$.

Remark now that the right adjoint preserves colimits and cofibrations. It is then sufficient to compute the derived counit on cofibrant and fibrant objects of $\infty\text{-}\mathbf{Cat}_{Coind}^{+\infty}$. Given such an object $(X, M)$, we then have $((U(X, M))_{cof})^\flat \cong X^\flat$. As Proposition 4.26 states that $M$ is the set of coinductive invertible arrows of $X$, Lemma 4.27 implies that the derived counit $X^\flat \rightarrow (X, M)$ is a weak equivalence. $\square$

46

**4.29 Theorem.** *The full subcategory of fibrant objects of $\infty$-Cat$^{+\infty}_{\text{Coind}}$ is isomorphic $\infty$-Cat. Moreover, a morphism between fibrant objects of $\infty$-Cat$^{+\infty}_{\text{Coind}}$ is a weak equivalence (resp. fibration, resp. acyclic fibration) if and only if the underlying morphism in $\infty$-Cat$_{\text{Can}}$ is a weak equivalence (resp. fibration, resp. acyclic fibration).*

*Proof.* The first claim directly follows from Proposition 4.26 and from the fact that any functor between $\infty$-categories preserves coinductively invertible arrows.

For the second claim, suppose we are given a morphism $p: (X, M) \to (Y, N)$ between fibrant objects of $\infty$-Cat$^{+\infty}_{\text{Coind}}$. If $U(p)$ is a weak equivalence, so is $p$ by Theorem 4.28

Suppose now that $U(p)$ is an acyclic fibration in $\infty$-Cat$_{\text{Can}}$. The morphism $p$ then as the right lifting property against the set $I^\partial$ (defined in Definition 2.32). To demonstrate that $p$ is an acyclic fibration, it remains to show that an arrow is marked in $X$ if and only if its image in $Y$ is. Since $M$ and $N$ correspond respectively to the set of coinductively invertible arrows of $X$ and $Y$, this follows from Lemma 4.9 of [30].

Finally, suppose that $U(p)$ is a fibration in $\infty$-Cat$_{\text{Can}}$. As $(X, M)$ and $(Y, N)$ are, by definition, fibrant in $\infty$-Cat$^{+\infty}_{\text{Coind}}$, we need to show that $p$ is an isofibration. Applying Lemma 4.9 of [30] to $G_n \to \mathbb{D}_{n-1}$, we find that the marked arrows of $\hat{G}_n$ correspond to coinductively invertible arrows of $G_n$. This marked $\infty$-category is, in particular, fibrant in $\infty$-Cat$^{+\infty}_{\text{Coind}}$. Since $\mathbb{D}_{n-1}^b$ is also fibrant, and since $U$ induces an equivalence between the subcategories of fibrant objects, $p$ has the right lifting property against $\mathbb{D}_{n-1}^b \xrightarrow{t_n^+} (\mathbb{D}_{n-1}, \overline{e_n}) \to \hat{G}_n$. Finally, since $(Y, N)$ has by definition the right lifting property against $(\mathbb{D}_{n-1}, \overline{e_n}) \to \hat{G}_n$, $p$ has the right lifting property against $\mathbb{D}_{n-1}^b \xrightarrow{t_n^+} (\mathbb{D}_{n-1}, \overline{e_n})$ and is thus an isofibration. $\square$

Note that if $m < \infty$, then every $m$-marked $\infty$-category which is fibrant for the saturated inductive left semi-model structure is also fibrant for the coinductive left semi-model structure. Hence, when restricting the previous theorem to $m$-marked objects for $m < \infty$, we no longer need to move to the coinductive left semi-model structure and we directly obtain the following:

**4.30 Corollary.** *If $m < \infty$, the full subcategory of fibrant objects of $\infty$-Cat$^{+m}_{\text{Sat-Ind}}$ is isomorphic to the subcategory of $\infty$-Cat composed of $\infty$-categories whose arrows of dimension strictly superior to $m$ are coinductively invertible. Moreover, a morphism between fibrant $m$-marked $\infty$-categories is a weak equivalence (resp. fibration, resp. acyclic fibration) in $\infty$-Cat$^{+m}_{\text{Sat-Ind}}$ if and only if the underlying morphism in $\infty$-Cat is a weak equivalence (resp. fibration, resp. acyclic fibration) in $\infty$-Cat$_{\text{Can}}$.*

### 4.3 The Canonical Model Structure vs the Limit of the $\pi$-Tower

In this section, we will compare the canonical model structure with the limits of the tower of $\pi$ functors as considered in Section 4.1.

Given a strict $\infty$-category $C$, it is possible to define an $(\infty, m)$ localization $\pi_m X$, and this defines an object of the limit of the tower of $\pi$ functors. But this

47

construction does not produce an equivalence between this limit and the canonical model structure, contrary to what seemed to have been believed previously. Here we are using “limit” as “the (homotopy) limit of the corresponding tower of associated $(\infty, 1)$-categories,” without referring to any specific model.

We will show this by building a morphism $C_\infty \rightarrow D_\infty$ that is not an equivalence of the coinductive model structure, but becomes invertible in the limit of the $\pi$-tower. Though we believe this is not the case, this still leaves open the possibility that the limit of the $\pi$-tower is equivalent to a further localization of the coinductive left semi-model structure, where this morphism (and probably others) would become invertible. If this were the case, then the limit of the $\pi$-tower would be equivalent to a localization $\infty$-Cat$_{\text{Can}}$.

More precisely, we will show:

**4.31 Proposition.** *There exists a morphism $f: C_\infty \rightarrow D_\infty$ between cofibrant $\infty$-marked $\infty$-categories such that*

(1) $f$ is not a weak equivalence in the coinductive left semi-model structure on $\infty$-marked $\infty$-categories defined in Definition 4.16,
(2) for all integers $n$, $\pi_n f$ is a weak equivalence in the saturated inductive left semi-model structure on $n$-marked $\infty$-categories defined in Theorem 3.38.

As an immediate consequence, we get:

**4.32 Corollary.** *The $(\infty, 1)$-functor from the $(\infty, 1)$-category associated to $\infty$-Cat$_{\text{Can}}$ to the limit of the diagram of $(\infty, 1)$-categories associated to $(\infty$-Cat$^{+n}_{\text{Sat-Ind}}, \pi_n)$ induced by the diagram*

![img-17.jpeg](img-17.jpeg)

*is not an equivalence.*

**4.33 Construction.** Let $E_1$ denote the following 2-polygraph:

![img-18.jpeg](img-18.jpeg)

and $E_n := \Sigma^{n-1} E_1$. Let us recall that the definition of the functor $\Sigma^{n-1}$ is given in Definition 2.6. When writing $\mathbb{D}_n \rightarrow E_n$, we will always consider the morphism representing the $n$-arrow $\Sigma^{n-1} f$. We define by induction a sequence of polygraphs $(P_n)_{n \in \mathbb{N}}$. We set $P_0 := \mathbb{D}_1$ and $P_n$ as the pushout:

![img-19.jpeg](img-19.jpeg)

48

where $(P_n)_{n+1}$ is the set of $(n+1)$-arrows of $P_n$.

Informally, taking a pushout along $\mathbb{D}_{n+1} \rightarrow E_n$ means freely adding a left and a right inverse to an arrow $f$ (except there is no marking yet) and so $P_{n+1}$ is constructed by freely adding left and right inverses to all $(n+1)$-arrows of $P_n$.

When writing $\mathbb{D}_1 \rightarrow P_n$, we will always consider the morphism representing the 1-arrow $P_0 \rightarrow P_n$. Finally, for $n \in \mathbb{N} \cup \{\infty\}$ we define $C_n$ and $D_n$ as the following pushouts:

![img-20.jpeg](img-20.jpeg)

The morphism $C_\infty \rightarrow D_\infty$ will be the map $f$ of Proposition 4.31. The informal idea is that in $C_\infty$ the 1-arrow corresponding to the vertical map $\mathbb{D}_1 \rightarrow C_\infty$ has “coinductive inverse up to height $n$” for all $n$, but is not coinductively invertible. So when $C_\infty$ is seen as an object of the canonical (or coinductive) model structure this 1-arrow is not invertible, but as soon as we localize to make all the $n$-arrows invertible for some integer $n$, then this 1-arrow will become invertible. In contrast in $D_\infty$ this arrow becomes an identity, so it is invertible from the start. In the rest of the section, we will justify this rigorously.

We begin by showing the first point of Proposition 4.31, namely that $C_\infty \rightarrow D_\infty$ is not a weak equivalence in the coinductive left semi-model structure.

**4.34 Lemma.** *Let $P$ be a polygraph and $f$ a coinductively invertible $k$-arrow in $P$. For every $k$-generator $g$ appearing in the decomposition of $f$, there exists a sequence of generating arrows $(g_n)_{n \in \mathbb{N}}$ such that*

1. (1) for $n > 0$, $g_n$ is a $(n+k)$-generator and $g_0 = g$,
2. (2) for $n > 0$, $g_n$ appears in the decomposition of the source of $g_{n+1}$.

*Proof.* We show this result by coinduction on $k$. Suppose the result is true for all $(k+1)$-arrows, and let $f: a \rightarrow b$ be a coinductively invertible $k$-arrow, and $g$ a $k$-generator appearing in the decomposition of $f$. There exists a $k$-arrow $f': b \rightarrow a$ and a coinductively invertible $(n+1)$-arrow $\alpha: f\#_{k-1}f' \rightarrow \mathbb{I}_a$. As $g$ is a $k$-generator appearing in the decomposition of $f\#_{k-1}f'$ (which is the source of $\alpha$), we can find a $(k+1)$-generator $\beta$ appearing in the decomposition of $\alpha$ and such that $g$ is in the decomposition of the source of $\beta$. As $\alpha$ is coinductively invertible, one can continue this process coinductively starting from $\beta$ to build a sequence of generators $(\beta_n)_{n \in \mathbb{N}}$ satisfying the desired property. We then set $g_0 := g$, and $g_n := \beta_{n-1}$. This sequence also satisfies the desired property. $\square$

**4.35 Corollary.** *The $\infty$-categories $C_\infty$ and $D_\infty$ have no coinductively invertible arrows except identities.*

*Proof.* We will show this assertion for $C_\infty$; the proof for $D_\infty$ is essentially the same. We proceed by contradiction: let $f$ be a non-identity coinductively invertible $k$-arrow of $C_\infty$. As $f$ is not an identity, there must be at least one $k$-generator $g$ appearing in its decomposition. Since $C_\infty$ is a polygraph, one can

49

apply Lemma 4.34 to obtain a sequence $(g_m)_{m \in \mathbb{N}}$ of generators of $C_\infty$. Eventually shifting the sequence, one can freely assume that $g_0$ is of dimension strictly greater than 1. The generators of $C_\infty$ are obtained by gluing the generators of $P_n$ for all $n$ at the unique generator of $\mathbb{D}_1$, so this $g_0$ must be in one of the $P_n$. It then follows by induction that all the $g_m$ are in the same $P_n$, but this leads to a contradiction as the dimension of the generators of $P_n$ is bounded above. $\square$

**4.36 Corollary.** *The marked $\infty$-categories $C_\infty^0$ and $D_\infty^0$ are fibrant in the coinductive left semi-model structure.*

*Proof.* It is immediate that $C_\infty^0$ and $D_\infty^0$ fulfills the conditions of Definition 3.18 and hence they are fibrant in the inductive left semi-model structure by Proposition 3.25. Hence, by Proposition 4.26, we only need to check that all their coinductively invertible arrows are marked. By the previous corollary, only their identity arrows are coinductively invertible, which concludes the proof. $\square$

**4.37 Lemma.** *The morphism $C_\infty \rightarrow D_\infty$ is not a weak equivalence in $\infty\text{-Cat}_{\text{Coind}}^{+\infty}$.*

*Proof.* As both $C_\infty$ and $D_\infty$ are fibrant in the coinductive left semi-model structure, which is a Bousfield localization of the inductive left semi-model structure, this map is a coinductive equivalence if and only if it is an inductive equivalence. Hence, one can test whether it is an equivalence using Definition 3.32 and Proposition 3.33, but this map fails to satisfy condition (1) of Definition 3.32, as the 1-arrow of $C_\infty$ corresponding to the vertical map $\mathbb{D}_1 \rightarrow C_\infty$ is not marked and maps to an identity arrow (hence marked) in $D_\infty$. $\square$

Let us now show the second point, namely that for any integer $n$, $\pi_n C_\infty \rightarrow \pi_n D_\infty$ is a weak equivalence of $\infty\text{-Cat}_{\text{Sat-Ind}}^{+n}$.

**4.38 Lemma.** *For any $n > 0$, the map $(\mathbb{D}_n, \overline{\{e_n\}}) \rightarrow \pi_{n-1} E_n$ is an acyclic cofibration of $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$.*

*Proof.* This map is the composition of pushouts along the equations $(\mathbf{eq}_{n,n}^{-\circ})^{d_{n+1}}$, $(\mathbf{eq}_{n,n}^{-\circ})^{d_{n+1}^*}$ and the saturations $(\mathbf{sat}_{n,n}^{-\circ})^{d_{n+1}}$, $(\mathbf{sat}_{n,n}^{-\circ})^{d_{n+1}^*}$, where $(-)^{d_n}$ is the duality that inverts the direction of $(n+1)$-arrows, and $(-)^{d_{n+1}^*}$ is the duality that inverts the direction of both $n$-arrows and $(n+1)$-arrows. By Corollary 3.31, this concludes the proof. $\square$

**4.39 Lemma.** *For any $n > 0$, the map $\pi_{n+1} E_{n+1} \rightarrow \pi_n E_{n+1}$ is an acyclic cofibration in $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$.*

*Proof.* One should first note that this map is an isomorphism of the underlying $\infty$-categories and corresponds to marking all the $n$-arrows. In particular, it is a cofibration. Moreover, $\pi_{n+1} E_{n+1}$ is cofibrant as its underlying $\infty$-category is a polygraph. Using the characterization of fibrant objects in the saturated inductive left semi-model structure (see Lemma 3.37 and Theorem 3.38), one easily sees that fibrant objects have the unique left lifting property against $\pi_{n+1} E_{n+1} \rightarrow \pi_n E_{n+1}$.

The class of morphisms having the unique left lifting property against this map then contains every morphism $C \rightarrow 1$ where $C$ is fibrant. As this class is closed under left cancellation, it includes any map between fibrant objects,

50

and so in particular, any fibration between fibrant objects. It follows that $\pi_{n+1}E_{n+1} \to \pi_n E_{n+1}$ is an acyclic cofibration. $\square$

**4.40 Lemma.** *For all $n$, $\pi_n P_n \to \mathbb{D}_0$ is a weak equivalence in $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+\infty}$.*

*Proof.* We will proceed by induction. The case $n = 0$ is obvious. Suppose proven that $\pi_n P_n \to \mathbb{D}_0$ is a weak equivalence. We define $\tilde{P}_{n+1}$ as the pushouts:

$$\begin{array}{c} \coprod_{(P_n)_{n+1}} \mathbb{D}_{n+1} \longrightarrow P_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_n E_{n+1} \longrightarrow \tilde{P}_{n+1} \end{array}$$

By [23, Corollary 2.4.4], and Lemmas 4.39 and 4.38, all morphisms labeled by $\sim$ in the following diagrams are acyclic cofibrations, and hence weak equivalences:

$$\begin{array}{c} \coprod_{(P_n)_{n+1}} \mathbb{D}_{n+1} \longrightarrow P_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_{n+1} E_{n+1} \longrightarrow \pi_{n+1} P_{n+1} \\ \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_n E_{n+1} \longrightarrow \tilde{P}_{n+1} \end{array}$$

$$\begin{array}{c} \coprod_{(P_n)_{n+1}} \mathbb{D}_{n+1} \longrightarrow P_{n+1} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} (\mathbb{D}_{n+1}, \overline{\{e_n\}}) \longrightarrow \pi_n P_n \\ \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(P_n)_{n+1}} \pi_n E_{n+1} \longrightarrow \tilde{P}_{n+1} \end{array}$$

By two out of three, and using the assumption that $\pi_n P_n \to \mathbb{D}_0$ is a weak equivalence, the map $\tilde{P}_{n+1} \to \mathbb{D}_0$ is a weak equivalence, and by stability by composition, so is the map $\pi_{n+1} P_{n+1} \to \mathbb{D}_0$. $\square$

**4.41 Lemma.** *For all $n$, the induced morphism $\pi_n C_\infty \to \pi_n D_\infty$ is a weak equivalence in $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+n}$*

*Proof.* By Proposition 4.4, it is sufficient to show that $\pi_n C_\infty \to \pi_n D_\infty$ is a weak equivalence in $\infty$-$\mathbf{Cat}_{\text{Sat-Ind}}^{+\infty}$.

Using Lemma 4.40 and since weak equivalences between cofibrant objects are stable by pushout, we have a diagram where all morphisms labeled by $\sim$ are weak equivalences:

$$\begin{array}{c} \coprod_{k \in \mathbb{N}} \pi_n \mathbb{D}_1 \longrightarrow \coprod_{k \in \mathbb{N}} \pi_n P_k \xrightarrow{\sim} (\coprod_{k < n} P_k) \coprod (\coprod_{k \geq n} \mathbb{D}_0) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \pi_n \mathbb{D}_1 \xrightarrow{\sim} \pi_n C_\infty \xrightarrow{\sim} D_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{D}_0 \xrightarrow{\sim} \pi_n D_\infty \xrightarrow{\sim} D_n \end{array}$$

By two out of three, this shows the result. $\square$

*Proof of Proposition 4.31.* We choose $f$ to be the morphism $C_\infty^b \to D_\infty^b$. The first point follows from Lemma 4.37 and the second from Lemma 4.41. $\square$

51

## 4.4 Complicial Sets and Stratified Street Nerve

In this section, we show that the Street nerve can be made into a right Quillen functor from the saturated inductive left semi-model structure on $\infty$-Cat$^{+\infty}$ to the Ozornova-Rovelli-Verity model structure for complicial sets. We refer to [43] and [38] for a detailed introduction to complicial sets; we will simply recall the important definitions below.

**4.42 Definition.** A *stratified simplicial set* is a simplicial set $X$, together with a set $M \subset \prod_{k>0} X_n$ of simplices of positive dimension called *thin simplices* that includes all degenerate simplices.

A morphism of stratified simplicial sets is a morphism between the underlying simplicial sets that sends thin simplices to thin simplices. The category of stratified simplicial sets is denoted **Strat**.

The *join* is an important operation for simplicial sets, which is defined on representables by the formula

$$\Delta[n] \star \Delta[m] := \Delta[n + m + 1].$$

We can extend it to any pair of simplicial sets by setting

$$X \star Y := \operatorname{Colim}_{\Delta^\dagger_X \times \Delta^\dagger_Y} \Delta[n] \star \Delta[m]$$

where $\Delta^\dagger$ is the augmented simplex category whose objects are possibly empty finite ordered sets and where we set the convention

$$\Delta[n] \star \Delta[-1] := \Delta[n] =: \Delta[n-1] \star \Delta[n].$$

The set of $n$-simplices of $X \star Y$ is then in bijection with the set

$$\{x \star y, (x, y) \in \prod_{k<n} X_k \times Y_{n-k-1}\} \cup \{x \star \emptyset, x \in X_n\} \cup \{\emptyset \star y, y \in Y_n\}$$

See, for example, [34, Definition 1.2.8.1] and below. We now define it for stratified simplicial sets as follows:

**4.43 Definition.** If $(X, M)$ and $(Y, N)$ are two stratified simplicial sets, we define $M \star N$ as the set of simplices of $X \star Y$ of the form $x \star y$ where either $x$ or $y$ is thin, with the convention that $\emptyset$ is not thin. We then define

$$(X, M) \star (Y, N) := (X \star Y, M \star N),$$

**4.44 Definition.** We define several marked simplicial sets whose underlying simplicial set is $\Delta[n]$:

1. $\Delta[n]$, where degenerate simplices are thin.
2. $\Delta[n]$$_t$, where the top $n$-simplex is thin.
3. $\Delta^k[n]$, where all simplices that include $\{k-1, k, k+1\} \cap [n]$ and degenerate simplices are thin.

52

(4) $(\Delta^k[n])'$, where all simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face and the $(k+1)$-face, and all the degenerate simplices are thin.
(5) $(\Delta^k[n])''$, where all simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face, the $k$-face, and the $(k+1)$-face are thin and all the degenerate simplices are thin.
(6) $\Delta[3]^{eq}$, where simplices of dimension strictly higher than 2, together with $[0, 2]$ and $[1, 3]$, and all degenerate simplices are thin.
(7) $\Delta[n]^\sharp$, where all simplices are thin.

Eventually, we will consider $\Lambda^k[n]$ endowed with the following marking: a simplex is marked in $\Lambda^k[n]$ if and only if it is marked in $\Delta^k[n]$.

**4.45 Definition** ([36, Definition 1.19]). An *elementary anodyne extension* is one of the following:

(1) The *complicial horn inclusions*:

$$\Lambda^k[n] \to \Delta^k[n], \quad n \ge 1, \quad n \ge k \ge 0.$$

(2) The *complicial thinness extensions*:

$$(\Delta^k[n])' \to (\Delta^k[n])'', \quad n \ge 2, \quad n \ge k \ge 0.$$

(3) The *saturation extensions*:

$$\Delta[n] \star \Delta[3]^{eq} \to \Delta[n] \star \Delta[3]^\sharp, \quad n \ge -1.$$

(4) The *m-triviality extensions*:

$$\Delta[n] \to \Delta[n]_t, \quad n > m.$$

**4.46 Remark.** In the case where $m = \infty$, there is no $m$-triviality extension.

**4.47 Definition.** An $m$-*complicial set* is a marked simplicial set having the right lifting property against all elementary anodyne extensions.

**4.48 Remark.** In the definition of complicial sets, we have included the "saturation extension" as part of our elementary anodyne extensions. These are not always included and play a role similar to the saturated localization of the inductive left semi-model structure considered in Section 3.5. See also [38] for a more general discussion of saturation for complicial sets.

As demonstrated in [33], $m$-complicial sets are a model for $(\infty, m)$-categories. For example, 0-complicial sets and 1-complicial sets are essentially the same as Kan complexes and quasicategories, respectively.

**4.49 Theorem** (Verity [43], Riehl [38], Ozornova-Rovelli [36]). *There is a model structure on **Strat**, which we will call the Verity model structure, where the cofibrations are all monomorphisms, and the acyclic cofibrations are generated by elementary anodyne extensions. Fibrant objects of this model structure are the $m$-complicial sets. We denote **Strat**$^\dagger^m$ the category **Strat** endowed with this model structure.*

53

We will use the join to define the adjunction between stratified simplicial sets and marked $\infty$-categories.

**4.50 Definition.** Let $(C, M)$ and $(D, N)$ be two marked $\infty$-categories. The *join* of $(C, M)$ and $(D, N)$, denoted $(C, M) \star (D, N)$, is the colimit of the following diagram:

$$\begin{array}{ccc} C \ominus \{0\} \ominus D & \coprod C \ominus \{1\} \ominus D & \longrightarrow & C \ominus \mathbb{D}_1 \ominus D \\ \downarrow & & \downarrow \\ C \coprod B & & \longrightarrow & C \star B \end{array}$$

As noted in Proposition 3.3.11 of [3] at the level of $\infty$-categories, this is the usual join of $\infty$-categories, as defined in Paragraph 6.30 of [6]. By the definition of the operation $\ominus$, we then have $(C, M) \star (D, N) \cong (C \star D, \overline{M \star N})$, where

$$M \star N := \{x \star y \mid x \in M, y \in N\} \cup \{x \star \emptyset \mid x \in M\} \cup \{\emptyset \star y \mid y \in N\}.$$

**4.51 Proposition.** Let $X \rightarrow Y$ be a *cofibration* and $K \rightarrow L$ an *acyclic cofibration* of $\infty$-Cat$^{+\infty}_{Sat-Ind}$. The morphisms

$$K \star Y \coprod_{X \star K} L \star X \rightarrow L \star Y \quad \text{and} \quad Y \star K \coprod_{K \star X} X \star L \rightarrow Y \star L$$

are *acyclic cofibrations* of $\infty$-Cat$^{+\infty}_{Sat-Ind}$.

*Proof.* By construction, we have a cocartesian square

$$\begin{array}{ccc} K \ominus \mathbb{D}_1 \ominus Y \cup L \ominus \partial \mathbb{D}_1 \ominus Y \cup L \ominus \mathbb{D}_1 \ominus X & \longrightarrow & K \star Y \coprod_{X \star K} L \star X \\ \downarrow & & \downarrow \\ L \ominus \mathbb{D}_1 \ominus Y & & \longmapsto & L \star Y \end{array}$$

By Lemma 2.42, the left-hand vertical morphism is an acyclic cofibration, and so is the right one. We proceed analogously for the second morphism. $\square$

**4.52 Definition.** The terminal category 1 has a monoid structure for this join operation. The multiplication $1 \star 1 \rightarrow 1$ is the unique morphism to the terminal $\infty$-category.

By the universal property of the category $\Delta$, this induces a cosimplicial object $|-|: \Delta \rightarrow \infty$-Cat$^{+\infty}$ where

$$|\Delta[n]| := 1 \star 1 \star \dots \star 1.$$

The $\omega$-category $|\Delta[n]|$ is traditionally called the $n^{th}$ oriental. We denote $|-|: \mathbf{Sset} \rightarrow \infty$-Cat$^{+\infty}$ the extension by colimits of this cosimplicial object.

For all $n$, $|\Delta[n]|$ is an $n$-polygraph that admits only one $n$-generator. If $M$ is a marking for $K$, we denote $|M|$ the set of arrows obtained as composition:

$$\mathbb{D}_n \rightarrow \Delta[n] \xrightarrow{|v|} K$$

54

where the left morphism corresponds to the top arrow of the $n^{th}$ orientals, and the right morphism is in $M$. We can now extend the strictification functor to stratified simplicial sets:

$$\begin{array}{rcl} |-|: & \mathbf{Strat} & \rightarrow & \infty\text{-}\mathbf{Cat}^{+m} \\ & (K, M) & \mapsto & (|K|, \overline{|M|}) \end{array}$$

This functor is cocontinuous and induces an adjunction:

$$\mathbf{Strat} \xleftarrow[\downarrow]{\perp} \infty\text{-}\mathbf{Cat}^{+m}$$

The right adjoint is called the *stratified Street nerve*.

**4.53 Remark.** In the case $m = \infty$, this adjunction models the forgetful functor from strict $\infty$-categories to weak $(\infty, \infty)$-categories (given by the stratified Street nerve $N$). The left adjoint corresponds to the “strictification functor” that sends a weak $(\infty, \infty)$-category to a strict $\infty$-category in a universal way.

**4.54 Proposition.** *The stratified Street nerve sends fibrant objects of $\infty\text{-}\mathbf{Cat}_{Sat\text{-}Ind}^{+m}$ to fibrant objects of $\mathbf{Strat}_V^{+m}$.*

*Proof.* Suppose first that $m < \infty$ and let $(X, M)$ be a fibrant $m$-marked $\infty$-category for the saturated inductive left semi-model structure. According to Corollary 4.30, $M$ consists of coinductively invertible arrows of $X$, and $N((X, M))$ is equal to the stratified simplicial set associated with the Street nerve of $X$ defined in [32, Définition 5.2.1]. Theorem 5.2.12 of *op. cit.* then implies that the stratified Street nerve sends fibrant objects of the saturated inductive left semi-model structure on $\infty\text{-}\mathbf{Cat}^{+m}$ to $m$-complicial sets.

Now, let $C$ be a fibrant $\infty$-marked $\infty$-category for the saturated inductive left semi-model structure. As the stratified Street nerve preserves directed colimits, there is an isomorphism

$$N(C) \cong \operatorname{Colim}_{n \in \mathbb{N}} N(\tau_n C)$$

For all $n$, $\tau_n C$ is fibrant for the saturated inductive left semi-model structure for $n$-marked $\infty$-categories, and $N(\tau_n C)$ is then a fibrant object of the model structure for $n$-complicial sets. As the model structure for $\infty$-complicial sets is $\omega$-combinatorial, fibrant objects are stable under directed colimits, and $N(C)$ is fibrant. $\square$

**4.55 Lemma.** *Let $(K, M)$ be a stratified simplicial set and $L$ a simplicial set. We denote $N$ the set of degenerate simplices of $L$. There exists an isomorphism*

$$|(K, M) \star (L, N)| \cong |(K, M)| \star |(L, N)|$$

*natural in $K$ and $L$.*

*Proof.* Proposition 7.13 of [6] provides a natural isomorphism $|K \star L| \cong |K| \star |L|$. Moreover, Lemma 2.24 implies that $\overline{|M| \star |N|} = \overline{|M| \star |N|}$. Since we have $|(K, M) \star (L, N)| \cong (|K \star L|, \overline{|M \star N|})$ and $(|K| \star |L|, \overline{|M| \star |N|})$, this concludes the proof. $\square$

55

**4.56 Lemma.** *The strictification functor sends complicial horn inclusions to acyclic cofibrations of the saturated inductive left semi-model structure for m-marked ∞-categories.*

*Proof.* The morphism |Λ¹[2]| → |Δ[2]¹| corresponds to the following inclusion of marked ∞-categories:

![img-21.jpeg](img-21.jpeg)

which is obviously an equation. The two morphisms |Λ⁰[2]| → |Δ⁰[2]| and |Λ²[2]| → |Δ²[2]| are respectively equal to eq¹·¹ and eq¹·¹. Furthermore, we can see that for all 0 < k < n, we have:

$$\Delta^k[n] = \Delta[k-2] \star \Delta^1[2] \star \Delta[n-k-2]$$

and Λᵏ[n] is the sub-object:

$$\begin{array}{l} \partial\Delta[k-2] \star \Delta^1[2] \star \Delta[n-k-2] \\ \cup \quad \Delta[k-2] \star \Lambda^1[2] \star \Delta[n-k-2] \\ \cup \quad \Delta[k-2] \star \Delta^1[2] \star \partial\Delta[n-k-2]. \end{array}$$

By Lemma 4.55, the strictification functor commutes with the join. Proposition 4.51 then implies that |Λᵏ[n]| → |Δᵏ[n]| is an acyclic cofibration. We proceed analogously for the cases k = 0 and k = n.

**4.57 Theorem.** *The strictification functor and the stratified Street nerve form a Quillen adjunction between the model structure for m-complicial sets and the saturated inductive left semi-model structure on ∞-Cat⁺ᵐ.*

*Proof.* Because of Lemma 4.56, it remains to show that complicial thinness extensions, saturation extensions, and m-triviality extensions are sent to acyclic cofibrations. Let i be such a morphism. According to Proposition 4.54, any fibrant object of the saturated inductive left semi-model structure has the right lifting property against |i|. As |i| is an identity on the underlying ∞-category, lifts against it are unique if they exist. This implies that any morphism between fibrant objects has the right lifting property against |i|, and this morphism is then an acyclic cofibration. This concludes the proof.

We can use this to generalize the results from [32]: The stratified Street nerve:

$$\mathcal{N}: \infty\text{-Cat} \to \mathbf{Strat}^{+m}$$

introduced in [32], is exactly the stratified Street nerve N of the present paper combined with the fully faithful inclusion ∞-Cat ⊂ ∞-Cat⁺ᵐ constructed in Section 4.2, which makes all coinductively invertible arrows marked. Hence:

**4.58 Proposition.** *Let f: X → Y be a fibration (resp. an acyclic fibration, resp. a weak equivalence) of the canonical model structure ∞-CatCan, then its stratified Street nerve N(f): N(X) → N(Y) is a fibration (resp. an acyclic fibration, resp. a weak equivalence) in the Verity model structure Stratᵥ⁺ᵐ.*

56

The main result of [32] corresponds to the special case of preservation of fibrant objects.

Note that, in particular, the proposition shows that the stratified Street nerve from [32], while not being a right Quillen functor, is still a morphism of Brown categories of fibrant objects ([12]), and so it does define a limit-preserving functor on the corresponding associated $(\infty, 1)$-categories.

*Proof.* As the stratified Street nerve $N: \infty\text{-Cat}_{\text{Sat-Ind}}^{+m} \rightarrow \text{Strat}_V^{+m}$ is a right Quillen functor, it preserves fibrations and acyclic fibrations, as well as weak equivalences between fibrant objects. Moreover, we have shown in Theorem 4.29 that the functor sending a strict $\infty$-category to the marked one where the marked arrows are the coinductively invertible ones, preserves fibrations, acyclic fibrations, and weak equivalences. $\square$

Finally, we want to clarify that this “forgetful” functor from strict $\infty$-categories to weak $\infty$-categories is not an “inclusion” in the sense that it is not fully faithful in any reasonable homotopy-theoretic sense. That is, this functor is not just an inclusion of strict $(\infty, m)$-categories into weak $\infty$-categories, but exhibits strict $\infty$-categories as objects with more structure than weak $\infty$-categories, even though the exact nature of this additional structure is not quite clear, beyond some special cases. Below we reproduce an example, mostly due to Dimitri Ara in [2], and just slightly adjusted to our setting, showing that this functor is not fully faithful on the homotopy category:

**4.59 Example.** For $M$ a commutative monoid, we write $B^n M$ for the strict $\infty$-category with only one cell in dimension $k < n$, the monoid $M$ of cell in dimension $n$ and only identity arrows in dimension $k > n$. All composition operations are given by the operation of $M$. We then claim that

$$[B^2\mathbb{N}, B^4\mathbb{Z}]_{\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}} \simeq \{0\} \quad [N(B^2\mathbb{N}), N(B^4\mathbb{Z})]_{\text{Strat}_V} \simeq \mathbb{Z}$$

Where $[\_\_]$ denote the set of homotopy class of maps (i.e. morphism in the homotopy category). We have not specified the marking, but these results do not depend on markings as long as the nerve $N$ is applied to a fibrant replacement (as it is a right Quillen functor).

First, we need to notice that $B^2\mathbb{N}$ is the $\infty$-category freely generated by one object $*$ and a 2-cell whose source and target are the identity of $*$. In particular it is a polygraph, and hence is a cofibrant object.

On the other hand $B^4\mathbb{Z}$ is a strict $\infty$-groupoid (every cell is strictly invertible) so, whatever marking we start from on $B^4\mathbb{Z}$, a fibrant replacement will just be $B^4(\mathbb{Z})^\sharp$ as marking cells that are invertible is an acyclic cofibration and once every cell is marked it is a fibrant object by (Lemma 3.37 and Theorem 3.38). So, the set of maps $[B^2\mathbb{N}, B^4\mathbb{Z}]_{\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}}$ in the homotopy category can be computed as homotopy class of maps from $B^2\mathbb{N}$ to $B^4\mathbb{Z}^\sharp$, but as there is no non-trivial 2-cell in $B^4\mathbb{Z}$ the only such maps in the constant maps equal to 0. Hence

$$[B^2\mathbb{N}, B^4\mathbb{Z}]_{\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}} \simeq \{0\}.$$

We now move to the computation of the hom set in complicial sets. In order to apply the Street nerve in a homotopy relevant way, we need to take fibrant

57

replacement of both object. For $B^4\mathbb{Z}$ we discuss this above and it corresponds to take $B^4\mathbb{Z}^\sharp$. For $B^2\mathbb{N}$, as it has no non-identity invertible cells, $B^2\mathbb{N}^\flat$ is already fibrant. In particular $N(B^4\mathbb{Z})$ is a complicial set whose cells are all thin (marked). Hence the marking we put in $N(B^2\mathbb{N})$ actually do not matter in the computation and

$$[(B^2\mathbb{N})^\flat, (B^4\mathbb{Z})^\sharp]_{\mathbf{Strat}_V^{\perp m}} = [(B^2\mathbb{N})^\sharp, (B^4\mathbb{Z})^\sharp]_{\mathbf{Strat}_V^{\perp m}}$$

Hence we need to compute a set of homotopy class of maps between two complicial sets where every cell is marked - so this boils down to computing a set of homotopy class of maps in the Kan-Quillen model structure on simplicial set, using the unmarked Street nerve. We can now rely on two results from [2] to show arrive at our result:

Theorem 4.7 of [2] shows that for any group $G$, $N(B^n G)$ is an Eilenberg MacLane space $K(\pi, n)$. Theorem 4.9 (and especially example 4.10) shows that $N(B^2\mathbb{N})$ is homotopically equivalent to $N(B^2\mathbb{Z})$ and hence is also an Eilenberg MacLane $K(2, \mathbb{Z})$, so using the well known equivalence between simplicial sets and spaces, we can write

$$[N(B^2\mathbb{N}), N(B^4\mathbb{Z})]_{\mathbf{Strat}_V} \simeq [K(2, \mathbb{Z}), K(4, \mathbb{Z})]_{\mathrm{Space}}$$

and for this final hon set we can use methods from topology: $K(2, \mathbb{Z})$ can be realized as $\mathbf{CP}^\infty$ and hence

$$[K(2, \mathbb{Z}), K(4, \mathbb{Z})]_{\mathrm{Space}} = H^4(\mathbf{CP}^\infty) = \mathbb{Z}$$

where these last claim can be found in many algebraic topology textbook, for example [21].

## A Left Semi-model categories

Semi-model categories were first introduced by Spitzweck in [39], following a remark by Hovey in [25] that given a combinatorial symmetric monoidal model category $\mathcal{V}$, the category of monoids in $\mathcal{V}$ carries such a structure without assuming that $\mathcal{V}$ satisfies the "monoid axiom." This observation is sufficient for studying the homotopy theory of monoids in $\mathcal{V}$. A more general (but not equivalent) notion of semi-model structure was later introduced by Fresse in Section 12 of [18].

Contrary to what the name might suggest, a left semi-model category is not "half of a model category." It is a minor weakening of the definition of a Quillen model category that allows for nearly all standard homotopical constructions but is somewhat easier to define. This minor weakening often eliminates technical or unnatural assumptions in certain theorems, such as the monoid axiom mentioned above or the requirement of properness when constructing localizations (see Theorem A.8 below).

In brief, a left semi-model category is similar to a model category, but certain axioms, such as the lifting property and the existence of factorizations, are only required to hold for morphisms with cofibrant domains. Since any map can be replaced by an equivalent one with a cofibrant domain, and only maps between cofibrant and fibrant objects contribute directly to the homotopy theory, this

58

restriction does not significantly alter the theory. The primary drawback of using left semi-model structures is practical: most of the literature focuses on Quillen model structures, so results must be re-proven for semi-model structures. A substantial body of work (see below) has been completed on this topic, and no serious difficulties have arisen so far.

In this paper, all Quillen model structures and left semi-model structures we encounter are "combinatorial" (in the sense of Definition A.5 below). In particular, they have fully formed weak factorization systems, rather than the weakened version assumed in [39], [18], or [23]. Assuming the existence of full factorization systems simplifies the definition, which we will adopt here. In [24], these are referred to as "factorization left semi-model categories," which is not the most general definition found in the literature.

**A.1 Definition.** A *premodel category* is a complete and cocomplete category $\mathcal{C}$ equipped with two weak factorization systems: (*anodyne cofibrations*, *fibrations*) and (*cofibrations*, *anodyne fibrations*), where the anodyne cofibrations are also cofibrations, or equivalently, the anodyne fibrations are fibrations.

**A.2 Definition.** An object $C$ is *fibrant* if the map $C \rightarrow 1$ is a fibration. An object is *cofibrant* if the map $\emptyset \rightarrow C$ is a cofibration.

**A.3 Definition.** A (*Spitzweck factorization*) *left semi-model category* is a pre-model category with a class $\mathcal{W}$ of morphisms, called weak equivalences, satisfying the following conditions:

(1) The class $\mathcal{W}$ contains all isomorphisms and satisfies the 2-out-of-3 property.
(2) A fibration is anodyne if and only if it is in $\mathcal{W}$.
(3) A cofibration with a cofibrant domain is anodyne if and only if it is in $\mathcal{W}$.

Note that if we remove the restriction "with cofibrant domain" in the third axiom, we recover the definition of a Quillen model structure. In the remainder of the paper, we will simply refer to these structures as left semi-model categories.

**A.4 Remark.** We should clarify the terminology here compared to what we used, for instance, in Definition 2.38. Often, as in the present paper, we begin with a premodel category with two weak factorization systems (anodyne cofibrations, fibrations) and (cofibrations, anodyne fibrations) that does not itself form a left semi-model category. However, we use a "saturation" construction described in Section 4 of [24], which adjusts the weak factorization systems without altering the underlying category, the cofibrations with cofibrant domains, or the fibrations with fibrant domains. The resulting premodel category is a left semi-model category. These new factorization systems are typically called "trivial" or "acyclic" instead of "anodyne." See Sections 3 and 4 of [24] for more details on this process.

In this paper, this distinction means that, contrary to what Definition A.3 might suggest, Theorem 2.43 does not imply that a cofibration (with a cofibrant domain) that is an equivalence is an anodyne cofibration as defined in Definition 2.38. Instead, the premodel structure that Theorem 2.43 asserts to be a left semi-model category involves weak factorization systems for (acyclic

59

cofibrations, fibrations) and (cofibrations, acyclic fibrations). Therefore, a cofibration with a cofibrant domain is an equivalence if and only if it is an acyclic cofibration.

In particular, the full subcategory of $\mathcal{C}$ consisting of cofibrant objects forms a model category, except that it may not be closed under limits and colimits—hence the need to consider the non-cofibrant objects of $\mathcal{C}$ as well.

The basic theory of left semi-model categories operates similarly to Quillen model categories: the homotopy category can be defined by formally inverting the maps in $\mathcal{W}$ or by defining a homotopy relation between bifibrant objects. See [39] or [23]$^4$. The $\infty$-categorical localization is also considered in the appendices of [31] (under the assumption that the factorization systems are functorial, which will always be the case in this paper), and it functions similarly to the corresponding localization in Quillen model categories.

### A.5 Definition.

- A premodel category is said to be combinatorial if its underlying category is locally presentable and both factorization systems are cofibrantly generated. It is said to be \(\omega\)-combinatorial if furthermore the underlying category is locally \(\omega\)-presentable and the codomains of the generating cofibrations and acyclic cofibrations are \(\omega\)-small.
- A Quillen adjunction between premodel categories is an adjunction \( L: \mathcal{C} \leftrightarrows \mathcal{D}: R \) such that \( L \) sends cofibrations and anodyne cofibrations to cofibrations and anodyne cofibrations, or equivalently, such that \( R \) sends fibrations and anodyne fibrations to fibrations and anodyne fibrations.
- A monoidal premodel category is a premodel category \(\mathcal{C}\), endowed with a monoidal closed structure, such that the monoidal unit is cofibrant, and for each pair of cofibrations \(i: A \to B\) and \(j: C \to D\), the map

$$ i \widehat{\otimes} j : B \otimes C \coprod_{A \otimes C} A \otimes D \to B \otimes D $$

is also a cofibration. Moreover, if $i$ or $j$ is anodyne, then $i \widehat{\otimes} j$ is also anodyne.

A left semi-model category is said to be *combinatorial* or *monoidal* if its underlying category is, and an adjunction between left semi-model categories is said to be a *Quillen adjunction* if it is a Quillen adjunction of the underlying premodel categories.

There are more general notions of monoidal structures or Quillen adjunctions for left semi-model structures that only involve the cofibrations between cofibrant objects, such as the "weak Quillen functors" discussed in [23]. However, we do not need these generalizations in the present paper.

Similarly to what happens with Quillen model categories, Quillen adjunctions between left semi-model categories induce adjunctions between their homotopy categories and even between their $\infty$-categorical localizations (see, for example, [23]).

### A.6 Definition.

A Quillen adjunction $F: C \leftrightarrows D: R$ is a *Quillen equivalence* if the induced adjunction between their homotopy categories is an equivalence of categories.

$^4$Semi-model categories are particular cases of weak model structures as defined in [23], so the results from this work can be applied.

60

Various equivalent characterizations of Quillen equivalences can be found in Proposition 2.4.5 of [23].

The following result will be used to characterize weak equivalences, or at least the weak equivalences between fibrant objects, in various left semi-model structures:

**A.7 Proposition.** Let $\mathcal{C}$ be a left semi-model category, and let $f: X \to Y$ be a morphism between two fibrant objects. Then $f$ is a weak equivalence if and only if $f$ has the so-called "homotopy right lifting property" against all cofibrations between cofibrant objects. That is, for each cofibration $i: A \mapsto B$ with cofibrant domain in $\mathcal{C}$ and any commutative square:

![img-22.jpeg](img-22.jpeg)

there exist dotted morphisms making the following diagram commute:

![img-23.jpeg](img-23.jpeg)

where $I_A B$ is a relative cylinder object for $i$, that is, a middle object of some (cofibration, anodyne fibration) factorization of the codiagonal map of $i$:

$$B \coprod_A B \mapsto I_A B \stackrel{\sim}{\twoheadrightarrow} B$$

Moreover, if $I$ is a generating set of cofibrations, then it is sufficient to check this for $i \in I$.

This is well known for Quillen model categories and proved in the more general setting of weak model categories in Appendix A of [23] (see Remark A.2.7).

We will occasionally need to take left Bousfield localizations of left semi-model categories. This is actually easier than Bousfield localization of Quillen model categories as it no longer requires any properness assumptions. It was shown in [9] that left Bousfield localization of combinatorial left semi-model categories at a set of maps yields another left semi-model category. This result was later reproved and generalized in [24] to include both left and right Bousfield localizations of combinatorial and accessible left semi-model categories, but we will only need the version from [9] here:

61

**A.8 Theorem.** *Let $\mathcal{C}$ be a combinatorial left semi-model category, and let $S$ be a set of morphisms between cofibrant objects in $\mathcal{C}$. Then there is another left semi-model category $\mathcal{C}_S$, called the left Bousfield localization of $\mathcal{C}$ at $S$, with the same underlying category as $\mathcal{C}$, such that:*

- • $\mathcal{C}_S$ has the same cofibrations as $\mathcal{C}$, and the identity functor $\mathcal{C} \to \mathcal{C}_S$ is a left Quillen functor.
- • *A left Quillen functor $\mathcal{C} \to \mathcal{D}$ to any other left semi-model structure is a left Quillen functor $\mathcal{C}_S \to \mathcal{D}$ if and only if it sends the morphisms in $S$ to weak equivalences.*

The fibrant objects of $\mathcal{C}_S$ are the objects that are fibrant in $\mathcal{C}$ and are "S-local". However, in order to define $S$-local objects, one needs to define mapping spaces. To avoid this, we provide the following characterization:

**A.9 Lemma.** *Let $\mathcal{C}_S$ be a left Bousfield localization of $\mathcal{C}$. Assume that all morphisms in $S$ are cofibrations between cofibrant objects (or have been replaced by equivalent cofibrations). For each cofibration $i: A \to B \in S$, let $\nabla i$ be a cofibration between cofibrant objects homotopy equivalent to the map $B \coprod_A B \to B$, for example a factorization*

$$B \coprod_A B \stackrel{\nabla i}{\rightsquigarrow} I_A B \stackrel{\sim}{\to} B$$

*and let $\nabla^k i$ be a series of cofibrations obtained by iterating this process, that is, $\nabla^k i = \nabla(\nabla^{k-1} i)$. Then an object is fibrant in $\mathcal{C}_S$ if and only if it is fibrant in $\mathcal{C}$ and has the right lifting property against $\nabla^k i$ for all $k$ and all $i \in S$.*

Finally, we can form Reedy model structures in this context as well. This is very similar to the treatment of classical Reedy model structures (see, for example, Chapter 5.2 in [26]).

Given a Reedy category $R$ and $\mathcal{C}$ a premodel category, the category of functors $\mathcal{C}^R$ has a premodel structure whose (anodyne) fibrations and (anodyne) cofibrations are the Reedy (anodyne) fibrations and cofibrations. That is, a natural transformation $f_r: X(r) \to Y(r)$ in $\mathcal{C}^R$ is an (anodyne) cofibration if and only if for each $r \in R$ the natural map

$$X(r) \coprod_{L_r X} L_r Y \to Y(r)$$

where

$$L_r X = \underset{\substack{r' \to r \in R^+ \\ r' \neq r}}{\text{Colim}} X(r')$$

is an (anodyne) cofibration. Dually, this natural transformation is an (anodyne) fibration if the natural map

$$X(r) \to Y(r) \times_{M_r Y} M_r X$$

where

$$M_r X = \underset{\substack{r \to r' \in R^- \\ r' \neq r}}{\text{Lim}} X(r')$$

is an (anodyne) fibration. We have:

62

**A.10 Theorem.** *If $\mathcal{C}$ is a premodel category and $R$ is a Reedy category, then $\mathcal{C}^R$ is a premodel category with the class of maps described above.*

*Furthermore, if $\mathcal{C}$ is a left semi-model category, then $\mathcal{C}^R$ is a left semi-model category with the weak equivalences being the levelwise weak equivalences.*

A more detailed treatment of Reedy model structures in the context of weak model categories, with more detailed proofs, can be found in Appendix C.2 of [8]. Though most of it is devoted to dealing with weakened assumptions regarding the existence of limits and colimits, which are not relevant in the present context.

*Proof.* The proof carries over essentially unchanged from the case of Quillen model structures. The proof that these form weak factorization systems on $\mathcal{C}^R$ as in Theorem 5.2.5 of [26] relies on the fact that we have weak factorization systems on $\mathcal{C}$ and hence carries over to the case of premodel categories. The other key argument can be found in the proof of Theorem 5.1.3 of [26] and shows that, because of the 2-out-of-3 property for weak equivalences, a Reedy fibration is a Reedy anodyne fibration if and only if it is a weak equivalence, and by the exact same argument, a Reedy cofibration with cofibrant domain is a Reedy anodyne cofibration if and only if it is a levelwise equivalence. □

A lemma that plays a significant role in this proof and that we will use at some points is:

**A.11 Lemma.** *If $R$ is a direct category (that is, a Reedy category with $R = R^+$) and $A \rightarrow B$ is a Reedy (anodyne) cofibration in $\mathcal{C}^R$, then the comparison map*

$$\operatorname{Colim}_{r \in R} A(r) \rightarrow \operatorname{Colim}_{r \in R} B(r)$$

*is an (anodyne) cofibration.*

*Proof.* This is essentially Corollary 5.1.5 of [26]. The simplest way to prove it is to observe that the colimit functor is the left adjoint to the 'constant' functor, and the constant functor clearly sends the fibrations and anodyne fibrations of $\mathcal{C}$ to Reedy fibrations and anodyne Reedy fibrations in $\mathcal{C}^R$, as Reedy fibrations for a direct category are just levelwise fibrations. □

## References

- [1] Fahd Ali Al-Agl, Ronald Brown, and Richard Steiner. Multiple categories: The equivalence of a globular and a cubical approach. *Advances in Mathematics*, 170:71–118, 2002.
- [2] Dimitri Ara. A Quillen theorem B for strict $\infty$-categories. *Journal of the London Mathematical Society*, 100(2):470–497, 2019.
- [3] Dimitri Ara. Habilitation à diriger des recherche: Théorie de l'homotopie des $\infty$-catégories strictes. 2022.
- [4] Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer, and Samuel Mimram. Polygraphs: from rewriting to higher categories. *arXiv preprint arXiv:2312.00429*, 2023.

63

[5] Dimitri Ara and Maxime Lucas. The folk model category structure on strict ω-categories is monoidal. Theory and Applications of Categories, 35(21):745–808, 2020.

[6] Dimitri Ara and Georges Maltsiniotis. Join and slices for strict ∞-categories. ArXiv:1607.00668, 2016.

[7] John C Baez and James Dolan. Higher-dimensional algebra and topological quantum field theory. Journal of mathematical physics, 36(11):6073–6105, 1995.

[8] César Bardomiano-Martinez and Simon Henry. Homotopy languages. to appear, 2024.

[9] Michael Batanin and David White. Left bousfield localization without left properness. Journal of Pure and Applied Algebra, 228(6):107570, 2024.

[10] Clemens Berger. A cellular nerve for higher categories. Advances in Mathematics, 169(1):118–175, 2002.

[11] Julia E Bergner. Homotopy limits of model categories and more general homotopy theories. Bulletin of the London Mathematical Society, 44(2):311–322, 2012.

[12] Kenneth S Brown. Abstract homotopy theory and generalized sheaf cohomology. Transactions of the American Mathematical Society, 186:419–458, 1973.

[13] Ronald Brown and Philip J Higgins. The equivalence of ∞-groupoids and crossed complexes. Cahiers de topologie et géométrie différentielle catégoriques, 22(4):371–386, 1981.

[14] Albert Burroni. Higher-dimensional word problems with applications to equational logic. Theoretical computer science, 115(1):43–62, 1993.

[15] Eugenia Cheng. An ω-category with all duals is an ω-groupoid. Applied Categorical Structures, 15(4):439–453, 2007.

[16] Sjoerd Erik Crans. On combinatorial models for higher dimensional homotopies. Universiteit Utrecht, Faculteit Wiskunde en Informatica, 1995.

[17] Daniel Dugger. Combinatorial model categories have presentations. Advances in Mathematics, 164(1):177–201, 2001.

[18] Benoit Fresse. Modules over operads and functors, volume 169 of Lecture Notes in Mathematics. Springer-Verlag, Berlin, 2009.

[19] Amar Hadzihasanovic. The algebra of entanglement and the geometry of composition. arXiv preprint arXiv:1709.08086, 2017.

[20] Yonatan Harpaz. Lax limits of model categories. Theory and Applications of Categories, 35(25):959–978, 2020.

[21] Allen Hatcher. Algebraic Topology. Cambridge University Press, 2002.

[22] Simon Henry. Minimal model structures. Preprint ArXiv:2011.13408, 2020.

64

[23] Simon Henry. Weak model categories in classical and constructive mathematics. *Theory and Applications of Categories*, 35(24):875–958, 2020.
[24] Simon Henry. Combinatorial and accessible weak model categories. *Journal of Pure and Applied Algebra*, 227(2):107191, 2023.
[25] Mark Hovey. Monoidal model categories. *Preprint arXiv:math/9803002*, 1998.
[26] Mark Hovey. *Model categories*, volume 63 of *Mathematical Surveys and Monographs*. American Mathematical Society, Providence, RI, 1999.
[27] Chris Schommer-Pries (https://mathoverflow.net/users/184/chris-schommer_pries). Is there an accepted definition of $(\infty, \infty)$ category? MathOverflow. URL:https://mathoverflow.net/q/134099 (version: 2017-12-15).
[28] Simon Henry (https://mathoverflow.net/users/22131/simon_henry). Testing for equivalences of $\infty$-categories on strictifications? MathOverflow. URL:https://mathoverflow.net/q/313748 (version: 2018-10-25).
[29] André Joyal and Myles Tierney. Quasi-categories vs segal spaces. *Contemporary Mathematics*, 431(277-326):10, 2007.
[30] Yves Lafont, François Métayer, and Krzysztof Worytkiewicz. A folk model structure on omega-cat. *Advances in Mathematics*, 224(3):1183–1231, 2010.
[31] Giulio Lo Monaco. Large cardinals and oo-categories. 2022.
[32] Félix Loubaton. Conditions de kan sur les nerfs des $\omega$-catégories. *ArXiv:2102.04281*, 2021.
[33] Félix Loubaton. $n$-complicial sets as a model of $(\infty, n)$-categories. *arXiv preprint arXiv:2207.08504*, 2022.
[34] Jacob Lurie. *Higher topos theory*. Princeton University Press, 2009.
[35] François Métayer. Cofibrant objects among higher-dimensional categories. *Homology, Homotopy and Applications*, 10(1):181–203, 2008.
[36] Viktoriya Ozornova and Martina Rovelli. Model structures for $(\infty, n)$-categories on (pre) stratified simplicial sets and prestratified simplicial spaces. *Algebraic & Geometric Topology*, 20(3):1543–1600, 2020.
[37] A John Power. An n-categorical pasting theorem. In *Category theory*, pages 326–358. Springer, 1991.
[38] Emily Riehl. Complicial sets, an overture. In *2016 MATRIX Annals*, pages 49–76. Springer, 2018.
[39] Markus Spitzweck. *Operads, algebras and modules in model categories and motives*. PhD thesis, Ph. D. thesis (Universität Bonn), 2001.
[40] Richard Steiner. Omega-categories and chain complexes. *Homology, Homotopy and Applications*, 6(1):175–200, 2004.

65

[41] Ross Street. Limits indexed by category-valued 2-functors. *Journal of Pure and Applied Algebra*, 8(2):149–181, 1976.
[42] Ross Street. The algebra of oriented simplexes. *Journal of Pure and Applied Algebra*, 49(3):283–335, 1987.
[43] Dominic RB Verity. Weak complicial sets i. basic homotopy theory. *Advances in Mathematics*, 219(4):1081–1149, 2008.

66