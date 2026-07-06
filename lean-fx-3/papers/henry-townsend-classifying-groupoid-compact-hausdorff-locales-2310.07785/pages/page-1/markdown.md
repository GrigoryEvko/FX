arXiv:2310.07785v1 [math.CT] 11 Oct 2023

# A classifying groupoid for compact Hausdorff locales

Simon Henry, Christopher Townsend

October 13, 2023

## Abstract

We construct a localic groupoid $\mathbb{G}_{KH}$ such that for any locale $X$ the category of compact Hausdorff locales in the topos of sheaves over $X$ is equivalent to a category whose objects are principal $\mathbb{G}_{KH}$-bundles over $X$ and whose morphisms are $\mathbb{S}$-homotopies (where $\mathbb{S}$ is the Sierpiński locale).

This result can be intuitively viewed as the compact Hausdorff dual of the well known result from topos theory that there is an object classifier.

## 1 Introduction

The paper [B90] proves that for any étale-complete localic groupoid $\mathbb{G}$, if we consider the topos $B(\mathbb{G})$ of $\mathbb{G}$-equivariant sheaves, then geometric morphisms $Sh(X) \longrightarrow B(\mathbb{G})$ are in bijection with principal $\mathbb{G}$-bundles over $X$. By the famous Joyal and Tierney result ([JT84]) we know that every bounded topos is of the form $B(\mathbb{G})$ for some étale-complete localic groupoid $\mathbb{G}$ and so since there is an object classifier this means we can find a localic groupoid $\mathbb{G}$ and a bijection between principal $\mathbb{G}$-bundles over $X$ and $Sh(X)$ for any locale $X$. Recalling that $Sh(X)$ can be identified with discrete locales internal to $Sh(X)$ we can therefore identify discrete locales with principal $\mathbb{G}$-bundles for some localic groupoid $\mathbb{G}$. The purpose of this paper is to prove a compact Hausdorff dual for this observation. Specifically, we construct a localic groupoid $\mathbb{G}_{KH}$ and identify, for any locale $X$, principal $\mathbb{G}_{KH}$-bundles over $X$ with compact Hausdorff locales internal to $Sh(X)$.

In outline the proof proceeds as follows. Firstly, by showing (Proposition 3.6) that proper maps of locales descend along effective descent morphism and that compact Hausdorff locales can be characterised as those locales that have proper diagonals, we see that $X \mapsto \mathbf{KHaus}_X$ is a stack. Then we recall two conditions that are sufficient to show that a stack on the category of locales is geometric; that is, equivalent to $X \mapsto \text{Prin}_{\mathbb{G}}(X)$ for some localic groupoid $\mathbb{G}$. The two conditions are similar to the familiar ones appearing in the definition of Artin stacks or Deligne-Munford stacks from algebraic geometry. The first condition is that there is a locale $G_0$ and a canonical object at stage $G_0$ such that every other object is covered by the canonical object via an effective descent

1