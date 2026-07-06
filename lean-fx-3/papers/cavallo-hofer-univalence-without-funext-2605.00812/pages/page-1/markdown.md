MFPS 2026 Preliminary Proceedings

arXiv:2605.00812v1 [cs.LO] 1 May 2026

# Univalence without function extensionality*

Evan Cavallo$^{a,1,3}$ Jonas Höfer$^{a,2}$

$^a$ Department of Computer Science and Engineering
University of Gothenburg and Chalmers University of Technology
Gothenburg, Sweden

# Abstract

It is a well-known theorem of homotopy type theory, originally due to Voevodsky, that function extensionality holds inside any univalent universe. We consider a weaker variant of the univalence axiom, asserting that the wild category formed by the universe is univalent, which we call categorical univalence. We show that categorical univalence does not imply function extensionality by an analysis of Von Glehn's polynomial model construction, which produces models of Martin-Löf type theory that always refute function extensionality. We find in particular that when the base model has a univalent universe, its polynomial model has a universe that is categorically univalent but lacks function extensionality.

Keywords: univalence, function extensionality, homotopy type theory, type theory, polynomial functor

# 1 Introduction

In 2010, Voevodsky [47,48] discovered that any universe of intensional Martin-Löf type theory (ITT) satisfying his univalence axiom also satisfies function extensionality: (dependent) functions between types in the universe are equal as soon as they are homotopic. This result became a foundational pillar of Homotopy Type Theory / Univalent Foundations. For constructivists, it was an additional motivation to justify univalence constructively—noted for example by Bezem, Coquand, and Huber [7]—given the historical difficulty of integrating function extensionality with constructive type theory.

At the same time, the connection between univalence and function extensionality has always seemed contingent. It is unclear whether univalence implies extensionality principles for other negative type formers, such as coinductive [49] or modal [24, Conjecture 11.2.2] types, which suggests functions might be privileged simply because they appear in the statement of univalence. Furthermore, minor variations on the univalence axiom are not known to imply function extensionality.

In a post on MathOverflow in 2013 [18], François G. Dorais proposed$^4$ one such variation. To contextualize Dorais' axiom, let us first review the standard definitions. For functions $f, g: \prod_{a:A} B(a)$, we write $f \sim g := \prod_{a:A} fa =_{B(a)} ga$ for the type of homotopies from $f$ to $g$. The type $A \simeq B$ of (homotopy)

* We thank Lorenzo Perticone for first (inadvertently) calling our attention to this question, and we thank the Gothenburg Logic and Types unit for many lunchtime discussions on the topic. We also thank András Kovács for his Agda formalization of the polynomial model, which was of great help to us in understanding the construction.

$^1$ Email: evan.cavallo@gu.se

$^2$ Email: hoferj@chalmers.se

$^3$ Supported by the Knut and Alice Wallenberg Foundation (KAW), Grant No. 2019.0116

$^4$ With some input from Mike Shulman.

MFPS 2026 Proceedings will appear in Electronic Notes in Theoretical Informatics and Computer Science