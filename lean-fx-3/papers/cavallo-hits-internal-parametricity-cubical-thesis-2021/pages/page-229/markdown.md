# Chapter 12

### 12.1 Related work

*Internal parametricity* The concept of parametricity originates with Reynolds [Rey83], who gave a relational interpretation of simply-typed $\lambda$-calculus with type variables in order to show that polymorphic functions treat their type arguments parametrically. His vision of parametricity is external and semantic: the results that follow from parametricity are theorems about the denotation of terms in a set-theoretic model. This kind of parametricity has been extended in every which direction—mostly notably for our purposes, to dependent type theory, by Atkey, Ghani, and Johann [AGJ14].

Mairson [Mai91], as well as Abadi, Cardellin, Curien, and Lévy [ACC93] and Plotkin and Abadi [PA93], developed early *syntactic* accounts of parametricity. In these systems, one has a logic on top of a type-theoretic formalism (typically the impredicative polymorphic $\lambda$-calculus) in which parametricity properties can be derived. The relational logic can then be interpreted in some setting such as Reynolds' (modulo issues of impredicativity).

Bernardy and Lasson [BL11] observed more generally that, given a pure type system (PTS) [Bar91], one can find a new, possibly stronger PTS in which the relational interpretation of the former system can be defined. Bernardy, Jansson, and Paterson [BJP10] show that in a sufficiently expressive, so-called *reflective* PTS, such as a dependent type theory, the relational interpretation can be defined in the same PTS. This is a step towards fully internal parametricity: the inputs and outputs of the parametricity translation belong to the same theory, but the translation function itself is metatheoretical. Keller and Lasson [KL12b] proved a similar result, constructing—and implementing as a tactic in the **Coq** proof assistant [Coq]—a parametricity translation from types to elements of an impredicative universe of propositions.

Krishnaswami and Dreyer [KD13], meanwhile, define a relational realizability semantics of a formalism for extensional dependent type theory that validates parametricity

217