186

Parametric cubical type theory

If $r$ is a constant $\varepsilon \in \{0, 1\}$, then we have by coherent head expansion that $\Psi \Vdash \text{coe}_{x.\text{Gel}_r(A_0, A_1, a_0, a_1, R)}^{s \to s}(Q) = \text{coe}_{x.A_\varepsilon}^{s \to s}(Q) \in \text{Gel}_r(A_0, A_1, a_0, a_1, R)[s/y]$, in which case the result follows from the conditions on coercion in $A_\varepsilon$.

If $r$ is a variable $x$, then we apply Lemma 9.4.6 to find that the coercion is equal to $\text{gel}_x(M_0^s, M_1^s, P)$ as defined in that rule. The reduction of trivial coercions in $A_0, A_1$, and $R$ shows that this term is equal to $\text{gel}_x(Q[0/x], Q[1/x], \text{ungel}(x, Q))$, thus to $Q$ by uniqueness for Gel types.

### Lemma 9.4.8 (Composition reduction in Gel types).

$$\begin{array}{l} \Psi \Vdash s, t \in \mathbb{I} \quad \Psi \Vdash r \in \mathbf{I} \quad (\forall \varepsilon) \Psi \setminus r \Vdash A_\varepsilon \text{ type} \quad \Psi \setminus r, a_0 : A_0, a_1 : A_1 \gg R \text{ type} \\ G := \text{Gel}_x(A_0, A_1, a_0, a_1, R) \quad \Psi \setminus r, x : \mathbf{I} \Vdash Q \in G \quad (\forall i) \Psi \setminus r, x : \mathbf{I} \Vdash \xi_i \in \mathbb{F} \\ (\forall i, j) \Psi \setminus r, x : \mathbf{I}, x : \mathbb{I}, \xi_i, \xi_j \Vdash Q_i = Q_j \in G \quad (\forall i) \Psi \setminus r, x : \mathbf{I}, \xi_i \Vdash Q = Q_i[s/x] \in G \\ M_\varepsilon^y := \text{hcom}_{A_\varepsilon}^{s \to y}(Q[\varepsilon/x]; \overline{\xi_i[\varepsilon/x] \hookrightarrow y.Q_i[\varepsilon/x]}) \\ P := \text{com}_{y.R[M_0^y/a_0, M_1^y/a_1]}^{s \to t}(\text{ungel}(x, Q); (\overline{\xi_i \hookrightarrow y. \text{ungel}(x, Q_i)})_{x \notin \xi_i}) \\ \hline \Psi \Vdash \text{hcom}_G^{s \to t}(Q[r/x]; \overline{\xi_i[r/x] \hookrightarrow y.Q_i[r/x]}) = \text{gel}_x(M_0^t, M_1^t, P) \in G[r/x] \end{array}$$

Proof. By coherent expansion. Let $\Psi' \Vdash \psi \in \Psi$ be given. We are in one of two cases.

- $r\psi = \varepsilon \in \{0, 1\}$. Then the composition at $G\psi$ steps to the same composition $A_\varepsilon\psi$, which is $M_\varepsilon^t\psi$. We know $\Psi' \Vdash M_\varepsilon^t\psi = \text{gel}_x(M_0^t, M_1^t, P) \in A_\varepsilon[t/y]\psi$ by the boundary rule for gel.
- $r\psi = z$ for some variable $z$. Then the left hand side steps to the right hand side, which is well-typed by composition for $A_0, A_1$, and $R$. We use affinity to ensure that $\text{ungel}(z.Q\psi[z/x]) = \text{ungel}(x.Q)\psi$ and $\text{ungel}(z.Q_i\psi[z/x]) = \text{ungel}(x.Q_i)\psi$.

Corollary 9.4.9 (Boundary of composition in Gel types). Let $\Psi \Vdash r \in \mathbf{I}$, $\Psi \setminus r \Vdash A_\varepsilon$ type for each $\varepsilon \in \{0, 1\}$, and $\Psi \setminus r, a_0 : A_0, a_1 : A_1 \gg R$ type be given, and set $G := \text{Gel}_r(A_0, A_1, a_0, a_1, R)$. Then the following rules are validated.

$$\begin{array}{c} \Psi \Vdash s = t \in \mathbb{I} \\ (\forall i) \Psi \Vdash \xi_i \in \mathbb{F} \quad (\forall i, j) \Psi, x : \mathbb{I}, \xi_i, \xi_j \Vdash Q_i = Q_j \in G \quad (\forall i) \Psi, \xi_i \Vdash Q = Q_i[s/x] \in G \\ \hline \Psi \Vdash \text{hcom}_G^{s \to t}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = Q \in G \end{array}$$

$$\Psi \Vdash s, t \in \mathbb{I} \quad (\forall i) \Psi \Vdash \xi_i \in \mathbb{F} \quad (\forall i, j) \Psi, x : \mathbb{I}, \xi_i, \xi_j \Vdash Q_i = Q_j \in G$$

$$(\forall i) \Psi, \xi_i \Vdash Q = Q_i[s/x] \in G \quad \Psi \Vdash \xi_j \text{ satisfied}$$

$$\Psi \Vdash \text{hcom}_G^{s \to s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = Q_j[t/x] \in G$$