222

Conclusions

not equivalent to the classical model in spaces. It is unclear whether one can in some way get “the best of both worlds”: a relational setting that contains a relativistic universe but becomes equivalent to a classical setting when restricted to  \( (\infty,1) \) -categories or  \( (\infty,1) \) -groupoids.

Substructural cubes Our parametric type theory, following Bernardy et al., adopts the affine cubical structure used in Bezem, Coquand and Huber's cubical model of ITT with the univalence axiom. This model has been largely abandoned in favor of structural cubical type theories, in part because of the comparative intuitive simplicity of structural variables, but also due to the difficulty of interpreting higher inductive types in this model.

To get an intuitive sense of the problem, consider the following “interval” higher inductive type, consisting of two points with a path between them.

inductive lval where

| zero ∈ lval
| one ∈ lval
| seg(x : I) ∈ lval [x ≡ 0 ↔ zero, x ≡ 0 ↔ one]

We would expect an eliminator for this type validating the following rule.

\[
\begin{array}{c c c} & i: \text {Ival} \gg A \text {type} & M \in \text {Ival} \\ Z \in A [ \text {zero / i} ] & O \in A [ \text {one / i} ] & x: \mathbf {I} \gg S \in A [ \text {seg (x) / i} ] \\ \hline \text {elim(i.A;M;Z,O,x.S)} \in A [ M / i ] \end{array}
\]

When we attempt to devise an operational semantics for this eliminator, however, we get stuck: how should  \( \text{elim}(i.A;\text{seg}(y);Z,O,x.S) \)  reduce? Following Part II, we would like to reduce to  \( S[y/x] \) , but the typing rule does not guarantee that S is apart from y, so this substitution is not permitted for affine interval variables. On a more conceptual level, the elimination principle sets up an isomorphism between structural functions  \( f: lval \to A \)  and bridges of type  \( \text{Bridge}(A,f\text{ zero},f\text{ one}) \) ; higher inductive types are in a way inherently structural.

By leveraging the Kan operations to simulate structural substitution, it is possible to model an interval higher inductive type in affine cubical sets that contains an eliminator with the above type. In the non-dependent case, to give an idea, we can define the reduction for the path constructor as follows.

\[
\operatorname{elim} (\dots A; \operatorname{seg} (y); Z, O, x. S) \longmapsto \operatorname{hcom} _ {A} ^ {0 \rightarrow y} (S [ 0 / x ]; x = 0 \hookrightarrow S [ 0 / x ], x = 1 \hookrightarrow z. S [ z / x ])
\]

Given \( Z, O, x.S \) with types as in the rule above, we can construct a path in \( \text{Path}(A, Z, O) \) from \( \lambda^{\sharp}y \). \( \text{elim}(\ldots A; \text{seg}(y); Z, O, x.S) \) to \( \lambda^{\sharp}x.S \), although we do not obtain it as an exact equality.