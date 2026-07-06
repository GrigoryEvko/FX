Remark 3.20. Using the adjunction $S^n \dashv Z_n$, for any chain complex $X$, a map $S^n \to X$ is simply a map $R \to Z_n X$ of $R$-modules. And from $D^n \dashv E v_n$, a map $D^n \to X$ corresponds to $y \in X_n$. Therefore, a commutative square

$$\begin{array}{c} S^{n-1} \xrightarrow{x} X \\ i_n \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ D^n \xrightarrow{Y} Y \end{array}$$

means that $x \in Z_{n-1}X \subseteq X_{n-1}$ i.e., $d_{n-1}x = 0$ and that $fx = y \in Y_n$. Therefore, taking a pushout simply means we freely add $(n-1)$-cycles to $X_{n-1}$ with a specified boundary.

The first element i.e., $n = 0$, of the set $I$ is the cofibration

$$\begin{array}{c c c c c c c c} 0 & & 0 \longleftarrow & 0 \longleftarrow & 0 \longleftarrow & \dots \\ i_0 \downarrow & & \downarrow & \downarrow & \downarrow & \\ D^0 & & 0 \longleftarrow & R \longleftarrow & 0 \longleftarrow & \dots \end{array}$$

For any $n \ge 1$ we have cofibrations $i_n$

$$\begin{array}{c c c c c c c c c} S^{n-1} & & 0 \longleftarrow & \dots \longleftarrow & R \longleftarrow & 0 \longleftarrow & 0 \longleftarrow & \dots \\ i_n \downarrow & & \downarrow & & 1_R & \downarrow & \downarrow & \\ D^n & & 0 \longleftarrow & \dots \longleftarrow & R \longleftarrow 1_R - R \longleftarrow & 0 \longleftarrow & \dots \end{array}$$

We then see immediately that $I$ has a natural, well-founded, order, where we can set $i_0$ to be the minimal element of the set.

From theorem 3.20, we get cycles $y \in X_n$ and for each $x \in X_{n-1}$ such that $dx = 0$ and $\mathsf{C}_n(x) := \{y \in X_n | dy = x\}$, this is for each generating cofibration $i_n : S^{n-1} \to D^n$. This tells us that the $\omega$-generalized algebraic theory has types $\mathsf{C}_n(x)$ for $n \ge 1$. We sum up the discussion in the following table:

$$i_0 : 0 \to D^0 \qquad \mapsto \qquad \vdash \mathsf{C}_0 \text{ Type}$$

$$i_n : S^{n-1} \to D^n \qquad \mapsto \qquad x : \mathsf{C}_{n-1}(0) \vdash \mathsf{C}_n(x) \text{ Type}$$

for $n \ge 1$. Note that the differential is already included in the information that defines the types $\mathsf{C}_n(x)$. We should also add, not included in the table, “+” operations on each type $\mathsf{C}_n(x)$, and axioms, that ensure is an abelian group:

$$a : \mathsf{C}_n(x), b : \mathsf{C}_n(y) \vdash a + b : \mathsf{C}_n(x+y).$$

40