86

Introduction

$f(0)$ and to define $f(n+1)$ in terms of $f(n)$; to show that a property $P$ holds of all elements of Nat, it suffices to show that $P(0)$ holds and that $P(n)$ implies $P(n+1)$.

An inductive type might be defined relative to some collection of parameters; for example, given parameter types $A, B \in \mathrm{U}$, we can form their coproduct (i.e., disjoint union, or sum), whose elements are tagged elements of either $A$ or $B$.

$$
\begin{array}{l} A: \mathrm{U}, B: \mathrm{U} \gg \textbf{inductive } A + B \textbf{ where} \\ | \operatorname{inl}(a: A) \in A + B \\ | \operatorname{inr}(b: B) \in A + B \end{array}
$$

The eliminator for the coproduct expresses that we can construct a function $(c: A + B) \to D$ given functions $(a: A) \to D[\operatorname{inl}(a)/c]$ and $(b: B) \to D[\operatorname{inr}(b)/c]$; from the logical perspective, we can prove a property of elements of $A + B$ by showing that it holds of all elements of the form $\operatorname{inl}(a)$ and all elements of the form $\operatorname{inr}(b)$.

A bit more generally, an inductive type might also take one or more indices [CP88; Dyb94], as in the following inductive type of vectors of elements of $A$ of length $n$. Here $A$ is a parameter, while $n$ is an index.

$$
\begin{array}{l} A: \mathrm{U} \gg \textbf{inductive } \operatorname{Vec}(A, n: \mathrm{Nat}) \textbf{ where} \\ | \operatorname{nil} \in \operatorname{Vec}(A, \text{zero}) \\ | \operatorname{cons}(n: \mathrm{Nat}, a: A, v: \operatorname{Vec}(A, n)) \in \operatorname{Vec}(A, \operatorname{suc}(n)) \end{array}
$$

An index is distinguished from a parameter in that the constructors may introduce elements at different indices. In this case, nil constructs the empty vector, which has length zero, while $\operatorname{cons}(n, a, v)$ takes a vector $v$ of length $n$ as input and constructs a vector of length $\operatorname{suc}(n)$ by appending a new element $a$. By contrast, the parameter $A$ is uniform across all constructors. We call inductive types with indices indexed inductive types; they are also known as inductive families.

The concept of (indexed) inductive type admits various further generalizations, in particular to inductive-inductive types [NS10] and inductive-recursive types [Dyb00], which permit the interleaving of multiple inductive and recursive definitions in a certain way. Our objective in this thesis is to generalize in a different direction, to higher inductive types, by adding the ability to declare path constructors. We take the class of indexed inductive types as our starting point for this generalization for two reasons. First, some ingenuity is required to give a computational interpretation for inductive types with indices in cubical type theory, in particular to interpret coercion in these types. By contrast, our—admittedly untested—expectation is that the implementation of coercion in indexed inductive types generalizes straightforwardly to inductive-inductive and inductive-recursive types. Second, Martin-Löf's identity type is an indexed inductive type. By interpreting indexed inductive types, we are therefore able to interpret Martin-Löf's intensional type theory (Section 2.2) en passant; because cubical type theory also validates the univalence axiom, this makes cubical type theory a constructive interpretation of HoTT.