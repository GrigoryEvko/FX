CHAPTER 5. THE $$(\infty, 1)$$-CATEGORY OF MARKED $$(\infty, \omega)$$-CATEGORIES

**Proposition 5.2.2.2.** Let $$F : I \to (\infty, \omega)$$-$$\text{cat}_{\text{m}/b^{\sharp}}$$ be a functor which is pointwise $$b$$-exponentiable. The morphism $$\text{colim}_I F$$ is $$b$$-exponentiable

*Proof.* Remark that all morphisms $$\mathbf{D}_n^{\sharp} \to b^{\sharp}$$ in $$\text{Sp}_b^{\sharp}$$ are globular, and so are discrete Conduché functors. We then have a sequence of equivalences

$$\underset{i:\text{Sp}_b^{\sharp}}{\text{colim}} i^* \underset{I}{\text{colim}} F \sim \underset{I}{\text{colim}} \underset{i:\text{Sp}_b^{\sharp}}{\text{colim}} i^* F \sim \underset{I}{\text{colim}} F.$$

□

**Proposition 5.2.2.3.** Let $$a$$ be a globular sum, and $$f : X \to a^{\sharp}$$ be a morphism. The induced morphism $$\text{colim}_{i:\text{Sp}_a^{\sharp}} i^* f$$ is $$a$$-exponentiable.

*Proof.* As marked globular morphisms are marked discrete Conduché functors, for any $$j : \mathbf{D}_n^{\sharp} \to a^{\sharp} \in \text{Sp}_a$$, $$j^* \text{colim}_{i:\text{Sp}_a^{\sharp}} i^* f$$ is equivalent to $$j^* f$$. We then have a sequence of equivalences

$$\underset{j:\text{Sp}_a^{\sharp}}{\text{colim}} j^* \underset{i:\text{Sp}_a^{\sharp}}{\text{colim}} i^* f \sim \underset{j:\text{Sp}_a^{\sharp}}{\text{colim}} j^* f.$$

□

**Proposition 5.2.2.4.** Let $$f : X \to b^{\sharp}$$ be exponentiable in $$b$$ and $$j : a^{\sharp} \to b^{\sharp}$$ a globular morphism. The morphism $$j^* f : X \to a^{\sharp}$$ is exponentiable in $$a$$.

*Proof.* The morphism $$j : a^{\sharp} \to b^{\sharp}$$ is a marked discrete Conduché functor, so $$j^*$$ preserves colimits according to proposition 5.1.1.29. We then have a sequence of equivalences

$$j^* f \sim j^* \underset{i:\text{Sp}_b}{\text{colim}} i^* f \sim \underset{i:\text{Sp}_b}{\text{colim}} (ji)^* f \sim \underset{k:\text{Sp}_a}{\text{colim}} k^* f.$$

□

**Lemma 5.2.2.5.** Let $$i : c \to d$$ be in $$\text{F}_g$$, $$b$$ a globular sum, and $$f : d \to b^{\sharp}$$ any morphism. Then, there exists a commutative square

$$\begin{array}{c} c' \xrightarrow{i'} d' \longrightarrow b^{\sharp} \\ h \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ c \xrightarrow{i} d \end{array}$$

- (1) $$d \to d'$$ is a finite composition of pushouts of morphism of shape $$i_n^{\alpha} : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$$ with $$n$$ an integer and $$\alpha := +$$ if $$n$$ is even, and $$-$$ if not.
- (2) $$d' \to b^{\sharp}$$ is globular.
- (3) $$h \to g$$ is a right Gray deformation retract.

272