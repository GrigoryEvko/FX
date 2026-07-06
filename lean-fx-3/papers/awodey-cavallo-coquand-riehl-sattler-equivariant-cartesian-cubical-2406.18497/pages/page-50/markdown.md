trivial cofibrations. Picking the appropriate trivial cofibration in each component and forming their coproduct in cubical species yields the point inclusion $\vec{v}: 1 \rightarrow \mathbb{I}$ in $\mathsf{cSet}^{\mathbb{Z}}$.

We have defined (cofibration, trivial fibration) and (trivial cofibration, fibration) algebraic weak factorization systems, each with an explicit category of generators. The trivial fibrations lift naturally against the generating category for the (trivial cofibration, fibration) awfs by Proposition 2.2.11, so trivial fibrations are fibrations and trivial cofibrations are cofibrations. The underlying weak factorization systems thus equip the category of cubical species with a premodel structure to be called the **interval premodel structure**. As in §3.1, we define the **weak equivalences** of cubical species to be those maps that factor as trivial cofibrations followed by trivial fibrations.

*Remark 4.3.17.* We would have a similar result if we had included the identity automorphism of the 0-cube in our definition of $\mathbb{Z}$, adding a $k = 0$ component to our cubical species. Had we done so, then note that in the $k = 0$ component, all maps would be fibrations, since the components of the exterior squares of (4.3.13) are both pullbacks. Consequently, in the $k = 0$ component, the only trivial cofibrations would be the isomorphisms, which means that the class of weak equivalences would coincide with the class of trivial fibrations, defined as in the other components to be those maps that lift against monomorphisms. But this class evidently fails to satisfy the 2-of-3 property, failing to be closed under left cancellation, so had we included a $k = 0$ component our premodel structure would have no chance of defining a model structure. However, the premodel structure would still suffice to define the model structure on equivariant cubical sets in Section 5.1.

We next verify that the interval premodel structure is cartesian monoidal. We expect that this property can be made structural: that the cartesian closed structure on the category of cubical species defines two variable adjunctions of algebraic weak factorization systems [Rie13], but as we have no application for that result, we decline to pursue it here.

**Proposition 4.3.18.** *Pushout products of cofibrations are cofibrations, while the pushout product of a cofibration and a trivial cofibration is a trivial cofibration.*

*Proof.* As the cofibrations are the monomorphisms in a presheaf category, the first property holds by Remark 2.2.2.

The remaining statement is equivalent to the assertion that the Leibniz exponential $\{c, f\}$ of a fibration $f: \mathbb{Y} \rightarrow \mathbb{X}$ and a monomorphism $c: \mathbb{C} \rightarrow \mathbb{Z}$ is a fibration. By Theorem 4.3.14, this is equivalent to the assertion that the Leibniz exponential in the slice over $\mathbb{I}$ of $\delta: \mathbb{I} \rightarrow \mathbb{I} \times \mathbb{I}$ and $\{c, f\} \times \mathbb{I}$ is a trivial fibration, lifting against all monomorphisms $u: \mathbb{J} \rightarrow \mathbb{K}$ in the slice over $\mathbb{I}$. Since the pullback of $\{c, f\}$ to the slice over $\mathbb{I}$ is isomorphic to the Leibniz exponential in the slice over $\mathbb{I}$ of the pullbacks $c \times \mathbb{I}$ and $f \times \mathbb{I}$, we are equivalently looking to solve lifting problems in the slice over $\mathbb{I}$ between the Leibniz product of $c \times \mathbb{I}$ and $u$ in the slice over $\mathbb{I}$ and the Leibniz exponential

$$\operatorname{ev} \hat{\circ} f := \{\widehat{\delta, f \times \mathbb{I}}\}_{\mathbb{I}}.$$

As we are working under the hypothesis that $f$ is a fibration, $\operatorname{ev} \hat{\circ} f$ is a trivial fibration so it suffices to verify that the pushout product of the monomorphisms $c \times \mathbb{I}$ and $u$ over $\mathbb{I}$ is a monomorphism. This again holds by Remark 2.2.2.

Finally, we observe that the interval premodel structure is cylindrical, satisfying the axioms of Definition 3.1.8, using the adjunction $(-) \times \mathbb{I} \dashv (-)^{\mathbb{I}}$ to define an adjoint functorial cylinder.

**Lemma 4.3.19.** *The interval premodel structure on cubical species is cylindrical.*

*Proof.* Since the endpoints $\vec{0}$ and $\vec{1}$ of the interval $\mathbb{I}$ are disjoint, the copairing $[\delta_0, \delta_1]: \mathbb{I} \to \mathbb{I} \mapsto \mathbb{I}$ is a monomorphism and thus a cofibration. By Lemma 4.3.15, the single endpoint inclusions $\delta_0, \delta_1: \mathbb{I} \not\to \mathbb{I}$ are trivial cofibrations. Now the result follows from Proposition 4.3.18.

50