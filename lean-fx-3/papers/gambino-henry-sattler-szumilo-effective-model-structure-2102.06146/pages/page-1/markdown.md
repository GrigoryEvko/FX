arXiv:2102.06146v3 [math.CT] 9 Nov 2022

# The effective model structure and $\infty$-groupoid objects

Nicola Gambino

Simon Henry

Christian Sattler

Karol Szumiło

November 11, 2022*

## Abstract

For a category $\mathcal{E}$ with finite limits and well-behaved countable coproducts, we construct a model structure, called the effective model structure, on the category of simplicial objects in $\mathcal{E}$, generalising the Kan–Quillen model structure on simplicial sets. We then prove that the effective model structure is left and right proper and satisfies descent in the sense of Rezk. As a consequence, we obtain that the associated $\infty$-category has finite limits, colimits satisfying descent, and is locally Cartesian closed when $\mathcal{E}$ is, but is not a higher topos in general. We also characterise the $\infty$-category presented by the effective model structure, showing that it is the full sub-category of presheaves on $\mathcal{E}$ spanned by Kan complexes in $\mathcal{E}$, a result that suggests a close analogy with the theory of exact completions.

## Introduction

**Context and motivation.** Over the past two decades, there has been an explosion of interest in the connections between model categories and higher categories [Cis20, GK17, JT07, Lur09, Rez01, Szu17]. This line of research led to the reformulation of significant parts of modern homotopy theory in terms of higher category theory, the development of higher topos theory [TV05, Lur09] and is of great importance for Homotopy Type Theory and the Univalent Foundations programme [AW09, BM18b, GK17, KL12, Shu19]. Central to these developments are model structures on categories of simplicial objects, i.e., functor categories of the form $\mathfrak{s}\mathcal{E} = [\Delta^{\mathrm{op}}, \mathcal{E}]$, where $\mathcal{E}$ is a category, as considered in [Qui67, Section II.4], [GJ99, Chapter II], [CH02, Theorem 6.3] and [Hör21]. In particular, the category of simplicial sets equipped with the Kan–Quillen model structure [Qui67] can be understood as a presentation of the $\infty$-category of spaces, while categories of simplicial presheaves and sheaves (i.e., simplicial objects in a Grothendieck topos) equipped with the Rezk model structure [Rez10] and the Joyal–Jardine model structure [Bro73, Joy84, Jar96] can be seen as presentations of $\infty$-toposes and their hypercompletions, respectively [DHI04, Lur09].

The main contribution of this paper is to construct a new model structure, which we call the *effective model structure*, on categories of simplicial objects $\mathfrak{s}\mathcal{E}$, assuming that $\mathcal{E}$ is merely a countably lextensive category, i.e., a category with finite limits and countable coproducts, where the latter are required to be van Kampen colimits [CLW93, Rez10]. The effective model structure is

*This version of the paper reflects the one published in *Forum of Mathematics, Sigma* (2022), Vol. 10:e34 1–59, submitted 9 March 2021, revised 19 January 2022, accepted 7 February 2022, available here. Two additional minor topos have been fixed.

2020 Mathematics Subject Classification: 18N40 (primary), 18N60, 55U10.

1