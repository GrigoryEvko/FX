property of 2-categories or bicategories that does not use equality between objects or between 1-arrows will also be invariant under biequivalences. One can also expect it can be generalized to other sorts of higher structures, for example a result about multicategories not using equality between objects should also have similar invariance properties.

The main goal of this paper is, informally, to establish a version of this result for essentially any kind of higher structure independently of the type of structure or the “categoricity level”. The only requirement is that the sort of higher structure we are considering must be organized as the fibrant objects of a model category (or semi-model category, or weak model category).

That is, we will attach to every (semi/weak) model category a “first-order language”, whose formulas are statements about objects of the category (possibly with parameters) such that

- Replacing the value of the parameters by homotopically equivalent parameters does not change the validity of a formula.
- Two weakly equivalent fibrant objects satisfy the same formulas.

We call these two results respectively the 1st and 2nd invariance theorem, and their precise statement is given as theorem 2.38. We will now go into a little more detail about how this language is defined, and explain the role of the different sections of the paper.

As mentioned above, our language is based first on dependent types. More precisely, we use the formalism of “Generalised algebraic theory” in the sense of Cartmell ([Car78]) as our basis, which are algebraic theories with dependent types. If we compare our approach to traditional model theory, our choice of a generalized algebraic theory T plays a role similar to the choice of a signature. However, contrary to traditional model theory, it is crucial for us that the theory T (i.e., our signature) can be any generalized algebraic theory, in particular the theory T can include equality axioms. This is in part because the first-order logic we will introduce on top of it will not have equality, so algebraic equations cannot be treated as axioms like any other.

## Overview

Starting from a generalized algebraic theory T, we build in section 2.1 the first-order language L^T, as well as its quotient L^T where “provably equivalent formulas” (for a relatively weak notion of proof) are identified.

4