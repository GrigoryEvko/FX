Proof. The claim is that the canonical square on the right below admits a section

$$\begin{array}{c} P X \xrightarrow {c} P R \xrightarrow {P s} P X \\ \delta_ {X} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \xrightarrow [ (\epsilon_ {X} , r) ]{} P X \times_ {X} R \xrightarrow [ s \pi ]{} X. \end{array}$$

The notion of a $\delta$-contractor is such that the indicated maps constitute just such a section. $\square$

Lemma 3.6.6. Let $R \rightrightarrows X$ be a reflexive relation such that the Leibniz pullback applications of $\delta$ to $(s, t) \colon R \to X \times X$ and $t \colon R \to X$ are both trivial fibrations. Then $\delta_X \colon PX \to X$ is also a trivial fibration.

Proof. Note that $\delta_X \colon PX \to X$ is the Leibniz pullback application of $\delta$ to $!_X \colon X \to 1$. By Lemmas 3.6.4 and 3.6.5, $\delta \hat{\circ}!_X$ is a retract of $(Pt, \delta_R) = \delta \hat{\circ} t$ and thus a trivial fibration. $\square$

When the fibrations are created from the trivial fibrations in a particular way, Lemma 3.6.6 can be used to establish the fibrancy of an object $X$ admitting a suitable reflexive relation. For later use, we introduce the following general definitions.

Definition 3.6.7. Let $\mathsf{E}$ be a (locally) cartesian closed category with a class of trivial fibrations.

- (i) Relative to an interval object $\delta_0, \delta_1 \colon 1 \to I$ in $\mathsf{E}$, the biased fibrations are those maps whose Leibniz exponentials by $\delta_0$ and $\delta_1$ are trivial fibrations.
- (ii) Relative to an object $I \in \mathsf{E}$, the unbiased fibrations are those maps for which the Leibniz exponential of their pullback to the slice over $I$ by the diagonal $\delta \colon I \to I \times I$ is a trivial fibration in the slice.

Proposition 3.6.8. Let $\mathsf{E}$ be a cartesian closed category with a premodel structure in which its fibrations are the biased fibrations defined relative to an interval object. Then an object $X$ is fibrant if it has a reflexive relation $s, t \colon R \rightrightarrows X$ such that both $(s, t) \colon R \to X \times X$ and $t \colon R \to X$ are fibrations.

Proof. As in Example 3.6.1, exponentiation by the interval defines an endofunctor $(-)^I$ equipped with a natural retraction $\epsilon \colon \mathrm{id} \Rightarrow (-)^I$ and $\delta_0, \delta_1 \colon (-)^I \Rightarrow \mathrm{id}$. Applying Lemma 3.6.6 separately with $\delta_0$ and $\delta_1$, we see that both $(\delta_0)_X = \delta_0 \hat{\circ}!_X$ and $(\delta_1)_X = \delta_1 \hat{\circ}!_X$ are trivial fibrations, proving that $X$ is fibrant. $\square$

Proposition 3.6.9. Let $\mathsf{E}$ be a cartesian closed category with a premodel structure in which the fibrations are the unbiased fibrations defined relative to an object $I$. Then an object $X$ is fibrant if it has a reflexive relation $s, t \colon R \rightrightarrows X$ such that $(s, t) \colon R \to X \times X$ and $t \colon R \to X$ are both fibrations.

Proof. By Example 3.6.1 the standing hypotheses of this section are satisfied in the slice over $I$. The fibrations $(s, t) \colon R \twoheadrightarrow X \times X$ and $t \colon R \twoheadrightarrow X$ pullback to fibrations in the sliced premodel structure over $I$. Lemma 3.6.6 applies, and $\delta \hat{\circ}!_{X \times I}$ is therefore a trivial fibration, proving that $X$ is fibrant. $\square$

We now combine these observations with the construction of the previous section to prove that the universe is a fibrant object under the combined hypotheses of these sections.

Proposition 3.6.10. Suppose $\mathsf{E}$ is a presheaf topos with a cylindrical premodel structure satisfying the Frobenius condition in which the cofibrations are the monomorphisms. If the fibrations are characterized as in Proposition 3.6.8 or 3.6.9 and have universes, then the bases of the universal fibrations $\pi \colon \hat{U} \twoheadrightarrow U$ are fibrant objects.

39