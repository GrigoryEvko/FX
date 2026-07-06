Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:21

definition:

\[
\begin{array}{c} \text {syn} \times A \longrightarrow A \\ \Big \downarrow \quad \Big \downarrow \\ \text {syn} \longrightarrow \bullet A \end{array} \tag {4.1}
\]

Intuitively, \(\bullet A\) is the portion of \(A\) with a trivial \(\mathcal{E}\) component. This is even clearer if one calculates the behavior of \(\bullet\) on a closed type \(A = (E,F,f)\) as \(\bullet A = (\mathbf{1},F,!\). Just as hypothesizing syn i.e., working under \(\bigcirc\), recovers \(\mathcal{E}\) internally to \(\mathbf{Gl}(\rho)\), working under \(\bullet\) recovers \(\mathcal{F}\). Phrased in topos-theoretic terms, \(\mathcal{F}\) is a closed subtopos of \(\mathbf{Gl}(\rho)\).

The final ingredient we must add to our type theory is the realignment axiom [OP18, BBC \( ^{+} \) 19, SH21], stating that the following canonical map has an inverse re for any B : U:

\[
\left(\sum_ {A: \mathrm{U}} [ A \cong B ]\right)\rightarrow \left(\sum_ {A: \text {syn} \rightarrow \mathrm{U}} \prod_ {z: \text {syn}} A (z) \cong B\right) \tag {4.2}
\]

Unfolding these conditions yields the following:

Definition 4.6. Fix \(B: \mathsf{U}\), \(A: \circ \mathsf{U}\), and \(\alpha: \prod_{z:\mathbf{syn}} A(z) \cong B\). The realignment \(\mathsf{re}(B, A, \alpha)\) of \(B\) along \(\alpha\) is a term of type \(\sum_{A^*: \mathsf{U}} A^* \cong B\) satisfying the following condition:

\[
\prod_ {z: \mathbf {s y n}} \mathsf {r e} (B, A, \alpha) = (A (z), \alpha (z))
\]

More intuitively, realignment states that a predicate lying over an object in E can be shifted to lie over an isomorphic object. A proper motivation of realignment is deferred to its use in Section 5, but broadly realignment will be used to satisfy the strict equalities demanded by Definition 3.8 where a priori two constants might agree only up to isomorphism.

Theorem 8.4 of Orton and Pitts [OP18] shows that a Hofmann–Streicher universe satisfies realignment for levelwise decidable propositions. Using the presentation of  \( \mathbf{Gl}(\rho) \)  as a presheaf topos [CJ95], syn is clearly levelwise decidable and so realignment at syn is constructively valid. Indeed, for this proposition realignment has a simple and intuitive meaning. To a first approximation, it allows us to take an object in a gluing topos  \( X \longrightarrow \rho(Y) \)  along with an isomorphism  \( Y \cong Y' \)  and perturb the first object to  \( X \longrightarrow \rho(Y') \) . Making this precise (e.g., allowing re to act in an arbitrary context) is only marginally more complex.

Definition 4.7. The language of synthetic Tait computability is extensional type theory with a cumulative hierarchy of universes and a universe of propositions equipped with a distinguished proposition syn : Ω such that each universe satisfies the realignment axiom for syn.

This subsection is summarized by the following result, which might be termed the ‘fundamental lemma’ of STC:

Theorem 4.8. \(\mathbf{Gl}(\rho)\) is a model of STC.

4.2. Gluing together cosmoi. While a model in  \( \mathbf{Gl}(\rho) \)  for a carefully chosen E, F, and  \( \rho \)  is sufficient to prove many results of MLTT [Coq19] the situation for MTT is more complex. Rather than gluing along a single functor, it is necessary to glue along an entire 2-natural transformation of continuous functors between 2-functors of presheaf topoi. We begin by