5.2. CARTESIAN FIBRATIONS

(5) $p$ as the unique right lifting property against $\{0\} \to [1]^{\sharp}$, marked 1-cells are left cancellable, and for any pair of objects $(x, y)$ of $X$, $\hom_X(x, y) \to \hom_Y(px, py)$ is a right cartesian fibration.

Conversely, the following are equivalent:

(1)' The morphism $p$ is a right cartesian fibration.
(2)' $p$ has the unique right lifting property against marked trivialization and for any diagram of shape (5.2.1.27), if $i$ is a left Gray deformation retract, so is $p'' \to p'$.
(3)' $p$ has the unique right lifting property against marked trivialization, and for any diagram of shape (5.2.1.27), if $i$ is in $\mathrm{I}_g$, the square $p'' \to p'$ is a left Gray deformation retract.
(4)' For any even integer $n$, $p$ has the unique right lifting property against $i_n^- : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ and marked $n$-cells are left cancellable; for any odd integer $p$ has the unique right lifting property against $i_n^+ : \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ and marked $n$-cells are right cancellable.
(5)' $p$ as the unique right lifting property against $\{1\} \to [1]^{\sharp}$, marked 1-cells are right cancellable, and for any pair of objects $(x, y)$ of $X$, $\hom_X(x, y) \to \hom_Y(px, py)$ is a left cartesian fibration.

Proof. The implication from (1) to (2) and (1)' to (2)' is the content of proposition 5.2.1.13.

The implication from (2) to (3) and (2)' to (3)' comes from the fact that $\mathrm{I}_g$ (resp. $\mathrm{F}_g$) consists of right (resp. left) Gray deformation retracts.

Suppose now that $p$ fulfills condition (3). Lemma 5.2.1.25 implies that if $i$ is of shape $[a, 1] \hookrightarrow [1]^{\sharp} \vee [a, 1]$ for $a : t\Theta$, $p'' \to p'$ is a right deformation retract. Lemma 5.2.1.22 and 5.2.1.21 then imply that $p$ has the unique right lifting property against $\{0\} \to [1]^{\sharp}$ and marked 1-cells are left cancellable.

We are now willing to show that for any pair of objects $(x, y)$, $\hom_X(x, y) \to \hom_Y(px, py)$ fulfills condition (3)', and an obvious induction will complete the proof of (3) $\Rightarrow$ (4). We then consider $x, y$ two objects of $X$, $i : b \to a$ in $\mathrm{I}_g$ and any morphism $a \to \hom_Y(px, py)$. The previous data induces a pullback square

$$\begin{array}{c} X'' \longrightarrow X' \longrightarrow X \\ p'' \downarrow \quad \downarrow \quad p' \downarrow \quad \downarrow \quad p \downarrow \\ [b, 1] \xrightarrow{[i, 1]} [a, 1] \longrightarrow Y \end{array}$$

where the bottom right morphism sends $\{0\}$ to $px$ and $\{1\}$ to $py$. By construction, $[i, 1]$ is in $\mathrm{F}_g$, and so by assumption, the morphism $p' \to p''$ is a right Gray deformation retract.

269