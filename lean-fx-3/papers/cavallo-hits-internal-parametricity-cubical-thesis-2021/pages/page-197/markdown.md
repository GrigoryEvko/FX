Gel types and relativity

185

equation. Such an equation is rather onerous to satisfy in semantics. In particular, it requires Bernardy et al. to divert from a standard presheaf model to a model in what they call refined presheaves. By contrast, our own presheaf model (Section 11.1) does not require any such refinement.

Finally, we must check that Gel supports coercion and composition. In typical fashion, we prove reduction rules for the two operations first, then conclude they are well-typed and preserve equality. The reader familiar with the intricacies of cubical type theory will notice that the reduction for coercion is much simpler than its equivalent for V types (see, e.g., [Ang19, §4.4.9]). This is a reflection of the fact that the principal direction of a coercion—the interval variable abstracted in the type line—is always a path variable. For V types, one must consider both the cases $\text{coe}_{x,V_x(A,B,I)}$ and $\text{coe}_{x,V_r(A,B,I)}$ where $r \neq x$, the former of which is the more involved. With Gel, on the other hand, the directions of the coercion is always orthogonal to the direction of the type itself.

### Lemma 9.4.6 (Coercion reduction in Gel types).

$$\begin{array}{c c c} \Psi \Vdash s, t \in \mathbb{I} & \Psi \Vdash r \in \mathbf{I} & (\forall \varepsilon) \Psi \setminus r, y : \mathbb{I} \Vdash A_\varepsilon \text{ type} \\ \Psi \setminus r, y : \mathbb{I}, a_0 : A_0, a_1 : A_1 \gg R \text{ type} & \Psi \setminus r, x : \mathbf{I} \Vdash Q \in \text{Gel}_x(A_0, A_1, a_0, a_1, R)[s/y] \\ (\forall \varepsilon) M_\varepsilon^y := \text{coe}_{y,A_\varepsilon}^{s \to y}(Q[\varepsilon/x]) & P := \text{coe}_{y,R[M_0^y/a_0,M_1^y/a_1]}^{s \to t}(\text{ungel}(x,Q)) \\ \hline \Psi \Vdash \text{coe}_{y,\text{Gel}_r(A_0,A_1,a_0,a_1,R)}^{s \to t}(Q[r/x]) = \text{gel}_x(M_0^t, M_1^t, P) \in \text{Gel}_r(A_0, A_1, a_0, a_1, R)[t/y] \end{array}$$

Proof. By coherent expansion. Let $\Psi' \Vdash \psi \in \Psi$ be given. We are in one of two cases.

- $r\psi = \varepsilon \in \{0, 1\}$. Then we have $\text{coe}_{y,\text{Gel}_r(A_0,A_1,a_0,a_1,R)}^{s \to t}(Q[r/x])\psi \longmapsto \text{coe}_{y,A_\varepsilon}^{s \to t}(Q[r/x])\psi$, and we know $\Psi' \Vdash \text{coe}_{y,A_\varepsilon}^{s \to t}(Q[r/x])\psi = \text{gel}_x(M_0^t, M_1^t, P)\psi \in A_\varepsilon[t/y]\psi$ by the boundary rule for gel and definition of $M_\varepsilon^t$.

- $r\psi = z$ for some variable $z$. Then the left hand side steps to the right hand side, which is well-typed by coercion for $A_0$, $A_1$, and $R$. As with extent, this relies on the affinity of bridge substitutions, in this case the fact that $\text{ungel}(z,Q\psi[z/x]) = \text{ungel}(x,Q)\psi$. $\square$

### Corollary 9.4.7 (Trivial coercion in Gel types).

$$\begin{array}{c c c} \Psi \Vdash s \in \mathbb{I} & \Psi \Vdash r \in \mathbf{I} & (\forall \varepsilon) \Psi \setminus r, y : \mathbb{I} \Vdash A_\varepsilon \text{ type} \\ \Psi \setminus r, y : \mathbb{I}, a_0 : A_0, a_1 : A_1 \gg R \text{ type} & \Psi \Vdash Q \in \text{Gel}_x(A_0, A_1, a_0, a_1, R)[s/y] \\ \hline \Psi \Vdash \text{coe}_{x,\text{Gel}_r(A_0,A_1,a_0,a_1,R)}^{s \to s}(Q) = Q \in \text{Gel}_r(A_0, A_1, a_0, a_1, R)[s/y] \end{array}$$

Proof. We are in one of two cases.