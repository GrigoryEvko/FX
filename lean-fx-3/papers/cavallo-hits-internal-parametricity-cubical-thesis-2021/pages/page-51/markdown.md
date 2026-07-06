Formalisms 39

The benefit of having a universe is that we can write definitions and prove theorems that quantify over types within the theory. For example, we can define composition of functions between arbitrary types:

$$\lambda A, B, C, g, f, a, g (f a) \in (A, B, C : U) \rightarrow (B \rightarrow C) \rightarrow (A \rightarrow B) \rightarrow (A \rightarrow C)$$

(For concision, we group iterated abstractions, such as $(A : U) \rightarrow (B : U) \rightarrow \cdots$ and $\lambda A, \lambda B, \cdots$ in the above, as comma-separated lists.)

## 2.2 Formalisms

If a type theory is a definition of truth, a formalism is a *window onto truth*; in computer science terms, an interface. The concerns of formalism design are much the same as those of interface design. On the one hand, there is *usability*: is the formalism expressive enough to prove the kind of results we want to prove, and is it structured to make them easy to prove? On the other hand, there is *range of applicability*: is the interface generic enough to be used as a window on a wide variety of notions of truth (*i.e.*, implementations)? Formalisms are particularly relevant to type theories because they can form the basis of proof assistants, programs that help a user develop proofs and check their correctness.

**Algebraic theories** Our type theories are built on top of an untyped programming language, the terms of which are the subjects of the typing judgments. This is sensible if we want to ground our truth in computation, but for an interface we would like to abstract away those details; this way we can realize the interface with implementations that compute differently, do not compute, or are not syntactic at all (such as set-theoretic interpretations).

Various techniques therefore exist to ensure that a formalism does not make reference to so-called “raw terms”. For example, the substitution operation $\sim [M/a]$ we have used in our computational type theories is an operator on raw terms; in our formalisms, we avoid it by using *explicit substitutions* [ACCL91], term formers that are internal to the type theory (of the same status as, say, $\text{suc}(\sim)$) rather than external operations.

These techniques have the additional useful effect of making our formalisms instances of the class of *generalized algebraic theories* (GATs) [Car86]. All GATs satisfy certain generic results; for example, the collection of interpretations of a given GAT can be organized into a category (the *category of models*) with an initial object given by the so-called *syntactic model*. These results are tremendously useful for establishing key properties of the formalism such as normalization, as is well-demonstrated by a recent explosion of research (*e.g.*, [Shu15; Coq19; CHS19; KHS19; SAG19; SA21]). Proving any such properties is beyond the scope of this thesis, but we aim with our novel formalism in Part III to create a setting amenable to such approaches.