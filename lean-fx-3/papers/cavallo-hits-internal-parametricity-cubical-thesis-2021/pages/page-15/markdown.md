3

## Contributions

This dissertation is divided into four parts. Each part begins with an introduction; the introductions are meant to be more accessible than the thesis as a whole, and can be read in sequence for a more extended overview of its objectives and contributions.

Part I is a review first of dependent type theory and then cubical type theory, roughly as presented by Angiuli [Ang19]. These are the prerequisites on which the rest of the dissertation depends; each subsequent part presents an extension to the cubical type theory framework.

Part II presents our schema for higher inductive types as an extension to cubical type theory. We develop a language for specifying such types and show that each specification can be realized in type theory with a computational interpretation.

Part III extends cubical type theory with internal parametricity, which endows every construction in the theory with an action on relations. We examine the consequences of such an action, and apply it in particular to mechanically check theorems which are prohibitively difficult to prove in ordinary cubical type theory. Our motivating example uses higher inductive types, but we do not depend on the entirety of Part II; the introduction of that part is sufficient background for an intuitive understanding. We also present a formalism for the type theory and a presheaf model of that formalism.

Part IV builds on Part III, extending parametric cubical type theory with a system of cohesive modalities that allow the interaction of parametric and non-parametric constructions. This is essential for the results we prove in the previous part to be used in ordinary cubical type theory.

**Publications** The results of Part II and Part III have been published in the following papers.

- Evan Cavallo and Robert Harper. “Higher inductive types in cubical computational type theory”. In: *PACMPL* 3.POPL (2019), 1:1–1:27. DOI: 10.1145/3290314
- Evan Cavallo and Robert Harper. “Internal Parametricity for Cubical Type Theory”. In: *28th EACSL Annual Conference on Computer Science Logic, CSL 2020, January 13-16, 2020, Barcelona, Spain*. 2020, 13:1–13:17. DOI: 10.4230/LIPICS.CSL.2020.13

The contents of Part II have been generalized from their form in the first paper to admit dependency and path types in recursive arguments.