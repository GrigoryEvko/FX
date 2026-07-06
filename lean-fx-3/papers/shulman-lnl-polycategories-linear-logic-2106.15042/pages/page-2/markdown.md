1:2

M. SHULMAN

Vol. 19:2

## 1. INTRODUCTION

When presenting logics and type theories, it is generally useful to separate the *structural* rules, such as exchange, weakening, contraction, identity, and cut, from the *logical* rules governing particular connectives. This separation of concerns can be reflected in categorical semantics by starting with a kind of *multicategory* [Lam69, Her00, Lei04] or *polycategory* [Sza75] encapsulating the structural rules, in which we can formulate universal properties of objects that correspond to the connectives.

A multicategory is like a category, but allows the domain of a morphism to be a finite list of objects; a polycategory allows both the domain and codomain to be such a list. Such morphisms correspond respectively to intuitionistic sequents $A_1, \dots, A_m \vdash B$ and classical sequents $A_1, \dots, A_m \vdash B_1, \dots, B_n$. One can then formulate universal properties for “tensor products” as representing objects for such morphisms, generalizing the classical characterization of the tensor product of vector spaces as a representing object for multilinear maps.

The choice of structural rules in a logic is reflected by an action on the morphisms of a multi- or polycategory that modifies the elements in the domain or codomain lists. For instance, the exchange rule is reflected by an operation taking any morphism $(\Gamma, A, B, \Delta) \rightarrow C$ to a morphism $(\Gamma, B, A, \Delta) \rightarrow C$. This leads to different kinds of multi- and polycategory, such as the following.

- Cartesian multicategories (a.k.a. abstract clones) correspond to intuitionistic nonlinear logic, with all structural rules. A cartesian multicategory with enough representing objects is equivalent to a cartesian monoidal category or a cartesian closed category.
- Symmetric multicategories correspond to intuitionistic multiplicative-additive linear logic, with exchange but no weakening or contraction. A symmetric multicategory with enough representing objects is equivalent to a symmetric monoidal category, possibly closed.
- Symmetric polycategories correspond to classical multiplicative-additive linear logic. A symmetric polycategory with enough representing objects is equivalent to a linearly distributive category or a *-autonomous category.

Multicategories and polycategories also have advantages from a purely category-theoretic standpoint. They can simplify coherence problems, since operations defined by universal properties generally do not require explicit coherence axioms. They can also enable the unification of different-looking structures in a larger context; for instance, monoidal categories and closed categories can both be represented as multicategories [Her00, Man12], and the Chu and Dialectica constructions are both instances of one polycategorical operation [Shu20].

It seems, however, that no polycategorical structure exists in the literature to correspond to *classical* linear logic *with exponentials*. Structured categories with exponential modalities have certainly been studied, such as LNL adjunctions [Ben95] and linearly distributive categories with storage [BCS96]. And a multicategorical version, corresponding to *intuitionistic* linear logic with exponentials, is suggested in [HT21]. But the polycategorical case appears to be missing.

In this paper we fill this gap by defining *LNL polycategories*. An LNL polycategory has two classes of objects, called *linear* and *nonlinear*. The linear objects form a symmetric polycategory, while the nonlinear objects form a cartesian multicategory, and there are additional morphisms relating the two classes of objects, enabling a description of the modalities ! and ? by universal properties. This can be regarded as a semantic counterpart of