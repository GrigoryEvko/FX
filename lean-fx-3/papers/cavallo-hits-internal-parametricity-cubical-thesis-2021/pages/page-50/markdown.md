38 Martin-Löf's type theory

The equality reflection rule presents difficulties from the perspective of formalism design; a formalism that includes equality reflection (such as Nuprl [Con+86]) necessarily has an undecidable equality judgment, which precludes techniques for automatically checking the truth of judgments. This motivates the restriction to the J rule in formalisms, possibly supported by the uniqueness of identity proofs principle (UIP). As a side effect, the fact that the J rule is compatible with non-unique identity proofs motivated early work in higher-dimensional type theory and models thereof, as we will see below.

### 2.1.5.5 The unit and empty types

We have included also a type with one element, Unit, and a type with no elements, Void. These are somewhat degenerate: the unit type needs no elimination rule, because its single element carries no interesting information, while the empty type needs no introduction rule, because there is nothing to introduce. The empty type is useful in particular for expressing falsehoods: we can inhabit $A \rightarrow$ Void if $A$ is empty, i.e., if $A$ regarded as a theorem is false. The elimination rule for Void says that we can construct an element of any type if we have an element of Void.

Rules 2.1.46 (Unit type).

FORMATION

⊨ Unit type

INTRODUCTION

⊨ ★ ∈ Unit

Rules 2.1.47 (Empty type).

FORMATION

⊨ Void type

ELIMINATION

⊨ A type ⊨ M ∈ Void

⊨ abort ∈ A

### 2.1.5.6 Universe

Finally, our type theory $\tau_1$ includes a universe of (so-called “small”) types. The typical rules for a universe are fairly simple: any element of the universe is a type, and the universe is closed under the same operators as $\tau_0$.

Rules 2.1.48 (Universes).

⊨ U type

⊨ A = A' ∈ U
⊨ A = A' type

⊨ A = A' ∈ U    a : A ≫ B = B' ∈ U
⊨ (a : A) → B = (a : A') → B' ∈ U

...