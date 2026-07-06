The excluded middle 201

## 10.4 The excluded middle

The bridge-discreteness of Bool implies a cute result concerning the law of the excluded middle in parametric type theory.

**Definition 10.4.1.** Write $\neg A := (A \rightarrow \text{Void})$ for intuitionistic negation. We define three varieties of excluded middle.

$$\text{LEM}_{\infty} := (A : \text{U}) \rightarrow (b : \text{Bool}) \times \text{elim}_{\text{Bool}}(\dots \text{U}; b; A, \neg A)$$

$$\text{LEM}_{-1} := (A : \text{U}) \rightarrow \text{IsProp}(A) \rightarrow (b : \text{Bool}) \times \text{elim}_{\text{Bool}}(\dots \text{U}; b; A, \neg A)$$

$$\text{LEM}_{\neg} := (A : \text{U}) \rightarrow (b : \text{Bool}) \times \text{elim}_{\text{Bool}}(\dots \text{U}; b; \neg A, \neg \neg A)$$

We call $\text{LEM}_{\infty}$ the *unrestricted excluded middle*, $\text{LEM}_{-1}$ the *excluded middle for propositions*, and $\text{LEM}_{\neg}$ the *weak excluded middle*.

Clearly $\text{LEM}_{\infty}$ implies $\text{LEM}_{-1}$. Moreover, $\text{LEM}_{-1}$ implies $\text{LEM}_{\neg}$, as every negated type is a proposition—this is a consequence of function extensionality and the fact that the empty type is a proposition.

The unrestricted excluded middle is independent of ITT, but is contradictory to the univalence axiom. We refer to [Uni13, Corollary 4.2.7] for a full proof, but the basic intuition is as follows. An element $d : \text{LEM}_{\infty}$ picks out a distinguished element of every inhabited type; in particular, some distinguished element $M$ of Bool. At the same time, univalence implies that $d$ has an action on isomorphisms. By examining the action of $d$ on the automorphism not $\in \text{Bool} \simeq \text{Bool}$ that swaps the two booleans, we can derive a path from (not $M$) to $M$, a clear contradiction.

The excluded middle for propositions, on the other hand, is perfectly consistent with homotopy type theory and is validated in the simplicial model thereof [KL20]; propositions have at most one element up to path equality, so there is no problem choosing elements uniformly with respect to isomorphisms. By contrast, even the weak law of the excluded middle is refuted in parametric type theory.

**Lemma 10.4.2.** If $A$ type is bridge-discrete, then any function $f : \text{U} \rightarrow A$ is constant.

*Proof.* For any pair of types $B_0, B_1 : \text{U}$, we have an abundance of bridges between them; to choose one, we have a bridge $\lambda^1 x \cdot \text{Gel}_x(B_0, B_1, \dots \text{Void}) \in \text{Bridge}(\text{U}, B_0, B_1)$ given by the empty relation. By applying $f$ pointwise, we obtain a bridge $\lambda^1 x \cdot f(\text{Gel}_x(B_0, B_1, \dots \text{Void}))$ from $f B_0$ to $f B_1$. As $A$ is bridge-discrete, this bridge induces a path between the same. $\square$

**Theorem 10.4.3.** The weak excluded middle is refuted.