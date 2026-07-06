Strengthening canonicity 149

Angiuli, Favonia, and Harper therefore solve the original problem by different route, introducing a *validity restriction* that prevents the formation of frivolous composites in the first place [AFH18, Definition 12]. In brief, composite tubes are restricted to certain forms that can never become frivolous by substitution.

**Definition 6.5.1 (Validity).** A collection $\Psi \Vdash \xi_1, \dots, \xi_n \in \mathbb{F}$ is *valid* when there exist $\Psi \Vdash r \in \mathbb{I}$ and $1 \leq i, j \leq n$ such that $\Psi, r \equiv 0 \Vdash \xi_i$ satisfied and $\Psi, r \equiv 1 \Vdash \xi_j$ satisfied.

This condition has the following two important properties.

**Proposition 6.5.2.** If $\Psi \Vdash \vec{\xi}_i \in \mathbb{F}$ is valid, then $\Psi' \Vdash \vec{\xi}_i \psi \in \mathbb{F}$ is valid for any $\Psi' \Vdash \psi \in \Psi$.

**Proposition 6.5.3.** If $\cdot \Vdash \vec{\xi}_i \in \mathbb{F}$ is valid, then there is some $i$ such that $\cdot \Vdash \xi_i$ satisfied.

The first of these simply checks that validity is stable under interval substitution; this is essential if it is to be a sensible condition to impose. The second implies that any composite with a valid tube in an empty interval context can be simplified.

The solution, then, is to require only that composites exist when the shape of the tube is valid; that is, we add validity as a prerequisite in Definition 3.1.27. Valid composites are sufficient for motivating use of composites, namely coercion in path types. In any case, non-valid composites can be recovered using iterated valid composites [Ang19, Theorem 4.34].

If we add the reduction rule for reducing frivolous formal coercions, impose the validity condition on homogeneous compositions, and add only valid formal composites to inductive types, we can obtain the following improved canonicity theorem for non-indexed HITs in an empty interval context.

**Theorem 6.5.4.** Assume the above adjustments have been made. Let $\cdot \Vdash \cdot \blacktriangleright \mathcal{K}$ spec and $\cdot \Vdash M \in \text{Ind}_{\mathcal{K}}^{(\cdot)}(\cdot)$ be given. Then $M$ evaluates to an intro term.

Thus we can run a closed integer modulo 2 and expect to obtain an actual integer as a result. Even simpler, we can define the type of natural numbers as a (particularly degenerate) higher inductive type and have our computations produce actual natural numbers.

Note that we absolutely cannot expect such a strong result for indexed inductive types. In these case, we can still exclude fhcom values with the validity restriction, but there is nothing to be done about formal coercions. The paradigmatic example is the identity type: an element $\cdot \Vdash P \in \text{Id}(A, M, N)$ cannot be guaranteed to evaluate to a refl value, because $\text{Id}(A, M, N)$ is inhabited as soon as there is a *path* from $M$ to $N$ in $A$.