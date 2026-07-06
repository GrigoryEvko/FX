5.2. CARTESIAN FIBRATIONS

By the universal property of cartesian product, this directly implies that if a square of shape (5.2.5.3) exists, it has to be unique, and that the morphism $\phi$ will be an equivalence. It then remains to show the existence.

Let $\psi'$ be an inverse of $\psi$. We denote $\tilde{\psi}: X \times [a, 1]^b \to Y$ and $\tilde{\psi}': Y \times [a, 1]^b \to X$ the morphisms induce by the adjunction from $\psi$ and $\psi'$. For $\epsilon \in \{0, 1\}$, we denote by $\psi_\epsilon: X \times \{\epsilon\} \to Y$ and $\psi'_\epsilon: Y \times \{\epsilon\} \to X$ the induced morphisms. In particular $\psi_\epsilon$ and $\psi'_\epsilon$ are inverse one of the other.

By construction, we have a commutative diagram

$$\begin{array}{c} X \times [a, 1]^b \times [a, 1]^b \xrightarrow{\tilde{\psi} \times [a, 1]^b} Y \times [a, 1]^b \\ X \times \nabla \Bigg\uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ X \times [a, 1]^b \xrightarrow[\pi]{\quad} X \end{array}$$

where $\nabla$ is the diagonal and $\psi$ the canonical projection. This corresponds to a commutative diagram in the $(\infty, 1)$-category $[n] \mapsto \operatorname{Hom}(X \times [a, n]^b, X)$:

$$\begin{array}{c} i d_X \xrightarrow{\psi'_0 * \tilde{\psi}} i d_X \\ \tilde{\psi}' * \psi_0 \Big\downarrow \quad \searrow i d_{i d_X} \quad \Big\downarrow \tilde{\psi}' * \psi_1 \\ i d_X \xrightarrow{\psi'_1 * \tilde{\psi}} i d_X \end{array}$$

Remark that in the $(\infty, 1)$-category $[n] \mapsto \operatorname{Hom}(X \times [a, n]^b, Y)$, we have equivalences

$$\tilde{\psi} \sim \psi'_0 * \psi_0 * \psi \quad \text{and} \quad \tilde{\psi} \sim \psi'_1 * \psi_1 * \psi$$

and the previous diagram then induces two commutative triangles

$$\begin{array}{c} \psi_1 \\ \psi_1 * \tilde{\psi}' * \psi_0 \Big\downarrow \quad \searrow i d_{\psi_1} \\ \psi_0 \xrightarrow{\tilde{\psi}} \psi_1 \end{array}$$

$$\begin{array}{c} \psi_0 \xrightarrow{\tilde{\psi}} \psi_1 \\ \searrow i d_{\psi_0} \quad \Big\downarrow \psi_0 * \tilde{\psi}' * \psi_1 \\ \psi_0 \end{array}$$

View as a 1-cell of $[n] \mapsto \operatorname{Hom}(X \times [a, n]^b, Y)$, $\tilde{\psi}$ is then an equivalence. This implies the existence of a lifts in the following diagram

$$\begin{array}{c} [a, 1]^b \xrightarrow{\tilde{\psi}} \underline{\operatorname{Hom}}(X, Y) \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ 1 \end{array}$$

291