CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

is a right Gray deformation retract, and that the corresponding Gray deformation retract structure is functorial in $i : I$. As $j$ and $ji_n^\alpha$ are marked globular, they are discrete Conduché functors, and so exponentiable according to proposition 5.1.1.29. The following canonical morphism

$$\underset{I}{\operatorname{colim}} f(i) \to f$$

is then an equivalence. As right Gray deformation retract structures are stable by colimits, this concludes the proof.

**Lemma 5.2.3.2.** *Let $A$ be an $(\infty, \omega)$-category and $F : I \to (\infty, \omega)\text{-cat}_{\mathrm{m}/A^\sharp}$ be a diagram that is pointwise a left cartesian fibration. Let $i : a^\sharp \to b^\sharp$ be a morphism between globular sums and $i : b^\sharp \to A^\sharp$ any morphism. The canonical comparison*

$$\underset{I}{\operatorname{colim}}(ji)^* F \to i^* \underset{I}{\operatorname{colim}} j^* F$$

*is an equivalence.*

*Proof.* Lemma 5.2.3.1 implies that the two morphisms are left cartesian fibrations. As equivalences between these morphisms are detected on fibers, we can suppose that $a$ is [0]. In this case, the morphism $i$ is a discrete Conduché functor, and is then exponentiable according to proposition 5.1.1.29. This directly concludes the proof.

**Theorem 5.2.3.3.** *Let $A$ be an $(\infty, \omega)$-category and $F : I \to (\infty, \omega)\text{-cat}_{\mathrm{m}/A^\sharp}$ be a diagram that is pointwise a left cartesian fibration. The induced morphism $\operatorname{colim}_I F$ is a left cartesian fibration over $A^\sharp$.*

*Proof.* Consider the functor $\psi : \Theta_{/A} \to \operatorname{Arr}((\infty, \omega)\text{-cat}_\mathrm{m})$ whose value on $j : b \to A$ is $\operatorname{colim}_I j^* F$. As $F$ is pointwise a left cartesian fibration, the corollary 5.2.2.13 induces equivalences

$$\underset{\Theta_{/A}}{\operatorname{colim}} \psi := \underset{j:b \to A}{\operatorname{colim}} \underset{I}{\operatorname{colim}} j^* F \sim \underset{I}{\operatorname{colim}} \underset{j:b \to A}{\operatorname{colim}} j^* F \sim \underset{I}{\operatorname{colim}} F$$

The functor $\psi$ is cartesian according to lemma 5.2.3.2, and as $\operatorname{codom} \psi$ as a special colimit (given by $A^\sharp$), so has $\psi$ according to proposition 5.1.1.33. In particular, this implies that for any $j : b \to A$, the following canonical morphism

$$\underset{I}{\operatorname{colim}} j^* F =: \psi(j) \to j^* \underset{\Theta_{/A}}{\operatorname{colim}} \psi \sim j^* \underset{I}{\operatorname{colim}} F$$

is an equivalence. As the left object is a left cartesian fibration according to lemma 5.2.3.1, so is the right one. As this is true for any $j : b \to A$, the corollary 5.2.1.28 implies that $\operatorname{colim}_I F$ is a left cartesian fibration.

278