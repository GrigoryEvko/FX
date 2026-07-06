Gel types and relativity 187

*Proof.* We are in one of two cases. If $r$ is a constant $\varepsilon \in \{0, 1\}$, then these equations follow from the corresponding conditions in $A_\varepsilon$ by coherent head expansion. If $r$ is a variable $x$, then we apply Lemma 9.4.8 to see that the composition is equal to $\text{gel}_x(M_0^t, M_1^t, P)$ as defined in that lemma. We then prove the two rules as follows.

For the first rule, if $s = t$, then the rule for trivial compositions in $A_0, A_1$, and $R$ provide that $\Psi \Vdash M_\varepsilon^t = Q[\varepsilon/x] \in A_\varepsilon$ for $\varepsilon \in \{0, 1\}$ and $\Psi \Vdash P = \text{ungel}(x, Q) \in R[M_0^t/a_0, M_1^t/a_1]$, so that the combined term is equal to $Q$ by uniqueness for Gel types.

For the second rule, suppose $\Psi \Vdash \xi_j$ satisfied for some $j$. By the rule for the boundary of composition in $A_0$ and $A_1$, we have that $\Psi \Vdash M_\varepsilon^t = Q_j[\varepsilon/x] \in A_\varepsilon$ for $\varepsilon \in \{0, 1\}$. Moreover, we know that $\xi_j$ does not refer to $x$. If it did, it would have to be of the form $x \equiv 0$ or $x \equiv 1$, which would contradict our assumption that $\Psi \Vdash \xi_j$ satisfied. Thus we have an entry in the composition defining $P$ corresponding to $\xi_j$, and the composition boundary rule for $R$ then implies that $\Psi \Vdash P \in \text{ungel}(x, Q_j)R[M_0^t/a_0, M_1^t/a_1]$. Again, we conclude by uniqueness that the combined term is equal to $Q_i$. $\square$

#### Theorem 9.4.10 (Type formation).

$$\begin{array}{l} \frac{\Psi \Vdash r \in I \quad (\forall \varepsilon) \Psi \setminus r \Vdash A_\varepsilon = A'_\varepsilon \text{ type} \quad \Psi \setminus r, a_0 : A_0, a_1 : A_1 \gg R = R' \text{ type}}{\Psi \Vdash \text{Gel}_r(A_0, A_1, a_0, a_1, R) = \text{Gel}_r(A'_0, A'_1, a_0, a_1, R') \text{ type}} \\ \frac{\varepsilon \in \{0, 1\} \quad \Psi \Vdash A_\varepsilon \text{ type}}{\Psi \Vdash \text{Gel}_\varepsilon(A_0, A_1, a_0, a_1, R) = A_\varepsilon \text{ type}} \end{array}$$

*Proof.* For the first, we must show the coercion and composition are well-typed and equal in the two Gel types and that the satisfy the necessary coherence conditions. The former follows from Lemmas 9.4.6 and 9.4.8—we reduce the operations and see that the reducts are well-typed and equal—and the coherence conditions hold by Corollaries 9.4.7 and 9.4.9.

The second equation requires, beyond the equality of pretypes, that coe and hcom are defined in equal ways at $\text{Gel}_\varepsilon(A_0, A_1, a_0, a_1, R)$ and $A_\varepsilon$. This is immediate, as coercion and composition in the former reduce to their equivalents in the latter. $\square$