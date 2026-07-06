2

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

|  5 | Relating internal formulations of realignment | 33  |
| --- | --- | --- |
|  5.1 | Internal realignment à la Orton and Pitts . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 33  |
|  5.2 | Realignment and recollement . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 35  |
|  6 | Applications of realignment | 38  |
|  6.1 | Independence results for Martin-Löf type theory . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 38  |
|  6.2 | Semantics of the univalent universes . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 39  |
|  6.3 | Artin gluing and synthetic Tait computability . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 44  |
|  7 | Conclusions and future work | 47  |
|  7.1 | Prospects for a constructive version . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . | 48  |

## 1. Introduction

Grothendieck introduced the language of *universes* to control the size issues that plague a naïve categorical development of algebraic geometry [AGV72]. In a somewhat different line of research, Martin-Löf introduced universes into dependent type theory as a *reflection principle* [Mar71; Mar75; Mar79; Mar84]. In either case a universe parameterizes a class of maps that are closed under enough operations to do mathematics, including dependent product/sum, quotients, *etc.*

Grothendieck's use of universes was located in the ambient set theory; each universe $\mathcal{U}$ determines a category of $\mathcal{U}$-small sets and functions that serves as a base for both enrichment and internalization, generalizing the notions of locally small and small category respectively. The past three decades have however seen an increased interest in the adaptation of universes to categories other than **Set**:

1. Universes play a central role in the *algebraic set theory* of Joyal and Moerdijk [JM95], which explores the relationship between sets and classes from a categorical viewpoint.
2. Voevodsky's elucidation of the univalence principle [Voe06], foreshadowed by Hofmann and Streicher [HS98], has reinvigorated the study of universes in topoi. Closely related to Voevodsky's univalent universes are the *object classifiers* of $\infty$-topos theory in the Joyal–Lurie–Rezk tradition [Lur09; Rez10].
3. It is of practical interest to employ Martin-Löf type theory (MLTT) as an internal language for a variety of categories. In addition to the standard applications of internal methods to mathematics, the existence of topos models of MLTT is a critical ingredient for a number of recent results in type theory and programming languages, including the generalized abstraction theorem of Sterling and Harper [SH21] and the proofs of normalization for cubical type theory and multi-modal dependent type theory [Gra22; SA21].

Unfortunately some doubt has proliferated in the type theoretic literature (*e.g.* Coquand, Manna, and Ruch [CMR17], Xu [Xu15], and Xu and Escardó [XE16]) as to when sufficiently well-adapted universes exist in a topos. It is a well-known result of Hofmann