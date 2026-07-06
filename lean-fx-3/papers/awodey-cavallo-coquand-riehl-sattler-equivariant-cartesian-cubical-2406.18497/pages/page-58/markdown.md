**Corollary 5.2.7.** *For any $k \geq 1$, the inclusions $\vec{0}, \vec{1}: 1 \to I^k$ of the initial or final vertices into the $k$-cube each define trivial cofibrations.* $\square$

We now verify that the equivariant premodel structure is cartesian monoidal.

**Proposition 5.2.8.** *Pushout products of cofibrations are cofibrations, while the pushout product of a cofibration and a trivial cofibration is a trivial cofibration.*

*Proof.* As the cofibrations are the monomorphisms in a topos, the first property is again immediate. The second statement is equivalent to the assertion that the Leibniz exponential $\widehat{\{c, f\}}$ of a uniform fibration $f: Y \to X$ and a monomorphism $c: C \mapsto Z$ is a uniform fibration. But uniform fibrations and monomorphisms are created by the functor $\Delta: \mathsf{cSet} \to \mathsf{cSet}^{\mathbb{Z}}$ from the corresponding classes of cubical species, by definition and Lemma 5.1.4, respectively, and in virtue of Corollary 5.1.3 the functor $\Delta$ also preserves Leibniz exponentials. So the result follows from Proposition 4.3.18. $\square$

We now observe that our premodel structure is cylindrical. Although the equivariant fibrations are not defined using a particular interval object, we will show that the naive interval object

$$1 \xrightarrow[1]{0} I \xrightarrow{!} 1$$

satisfies the axioms of Definition 3.1.8, using the adjunction $(-) \times I \dashv (-)^I$ to define our adjoint functorial cylinder.

**Lemma 5.2.9.** *The equivariant premodel structure on cubical sets is cylindrical.*

*Proof.* Since the endpoints 0 and 1 of our interval $I$ are disjoint, the map $\partial: 1 + 1 \mapsto I$ is a monomorphism and thus a cofibration. By Corollary 5.2.7, the single endpoint inclusions $\partial_0, \partial_1: 1 \xrightarrow{\sim} I$ are trivial cofibrations. Now the result follows from Proposition 5.2.8. $\square$

**5.3. The equivariant cubical sets model of homotopy type theory.** In this section, we establish the type-theoretic properties of the cylindrical premodel structure on cubical sets needed to infer that it defines a Quillen model structure with the extra features required of a model of homotopy type theory.

The cofibrations in the equivariant premodel structure are exactly the monomorphisms, which are closed under pushout products in all slices by Remark 2.2.2. Together with Lemma 5.2.9, this verifies the hypotheses of Theorem 3.3.3, and therefore:

**Proposition 5.3.1.** *The equivariant premodel structure on cubical sets satisfies the equivalence extension property.* $\square$

Unlike in the case of the interval premodel structure on cubical species, we cannot use the results of §3.4 to establish the Frobenius condition, as the equivariant fibrations are not the naive unbiased fibrations. Instead, it follows for the equivariant premodel structure on cubical sets by comparison with cubical species.

**Proposition 5.3.2.** *The equivariant fibrations satisfy the Frobenius condition.*

*Proof.* We must show that the pushforward of an equivariant fibration $g$ along an equivariant fibration $f$ defines an equivariant fibration, which is the case just when its image under the constant diagram functor is a fibration of cubical species. But since Corollary 5.1.3 tells us that this functor preserves pushforwards, this map is the pushforward of $\Delta g$ along $\Delta f$. Since the equivariant fibrations are pulled back along $\Delta$ from the fibrations, the result follows from Frobenius for the latter, Proposition 4.4.2. $\square$

58