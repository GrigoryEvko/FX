16:4

A. NUYTS AND D. DEVRIESE

Vol. 20:2

**Directed:** Weaver and Licata [WL20] use a bicubical set model to show that directed HoTT [RS17] can be soundly extended with a directed univalence *axiom*.

**Guarded:** In guarded type theory [BM20], one axiomatizes Löb induction and clock-irrelevance.

**Nominal:** One version of nominal type theory [PMD15] provides the locally fresh name abstraction $\nu(i : \mathbb{I})$ which can be used anywhere (i.e. the goal type remains the same after we abstract over a fresh name). The operation introduces a name but requires a body that is fresh for the name (i.e. we do not get to use it). This would be rather useless, were it not that we are allowed to *capture* the fresh name (see Section 10).

*Internalizing fibrancy proofs.* Another motivation to internalize aspects of presheaf categories, is for building parts of the model inside the type theory, thus abstracting away certain categorical details such as the very definition of presheaves, and for some type systems enabling automatic verification of these constructions. Given the common pattern in models described in the previous section, it is particularly attractive to try and define fibrancy and prove results about it internally.

In the context of HoTT, Orton and Pitts [Ort18, OP18] study CCHM-Kan-fibrancy [CCHM17] in a type theory extended with a set of axioms, of which all but one serve to characterize the interval and the notion of cofibration. One axiom, *strictness*, provides a type former Strict for strictifying partial isomorphisms, which exists in every presheaf category. In order to construct a universe of fibrant types, Licata et al. postulate an “amazing right adjoint” $\mathbb{I} \setminus \sqcup$ to the non-dependent path functor $\mathbb{I} \to \sqcup$ [LOPS18, Ort18], which indeed exists in presheaves over cartesian base categories if $\mathbb{I}$ is representable. Since $\mathbb{I} \setminus \sqcup$ and its related axioms are global operations (only applicable to closed terms, unless you want to open Pandora’s box as we do in the current paper), they keep everything sound by introducing a judgemental comonadic *global* modality $\flat$.

Orton et al.’s formalization [LOPS18, Ort18, OP18] is only what we call *meta-internal*: the argument is internalized to *some* type theory which still only serves as a metatheory of the type system of interest. Ideally, we would also be able to define and prove fibrancy of types *within* the type theory of interest, which we call *auto-internal*. This has several advantages:

- A general approach to auto-internalization of notions of fibrancy saves us from a proliferation of type systems, each with axiomatic internal fibrancy operations with hard-coded computational behaviour that proceeds by case analysis on the construction of the type. Proving fibrancy auto-internally will in general be more typesafe than hard-coding it in a language implementation that is often written in a simply-typed language such as Haskell and OCaml.
- Given an auto-internal implementation, we can still pretend that we have a meta-internal situation by restricting ourselves to a subset of the language. But we automatically get a two-level type theory [Voe13, ACKS23], where we have access to non-fibrant types from within. (This does not prove conservativity of two-level type theory over the object system.)
- In directed type theory, there are various relevant notions of fibrancy, many of which are not well preserved by basic type formers, so access to non-fibrant types may be a necessity to get any work done at all.