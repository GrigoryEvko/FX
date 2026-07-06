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