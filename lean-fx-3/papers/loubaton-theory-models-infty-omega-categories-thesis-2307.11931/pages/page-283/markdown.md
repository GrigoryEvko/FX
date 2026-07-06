5.2. CARTESIAN FIBRATIONS

Proof. We obtain $(d')^{\natural}$ by factorizing $f^{\natural}$ into an algebraic morphism $g^{\natural}$ followed by a globular morphism. The marking $d'$ is the smaller one that makes $g$ a morphism of marked $(0, \omega)$-categories. By construction, $c \to d$ fits in a cocartesian square

$$\begin{array}{c} \mathbf{D}_{n}^{\flat} \longrightarrow c \\ i_{0}^{\alpha} \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (\mathbf{D}_{n+1})_{t} \longrightarrow d \end{array}$$

where all morphisms are globular, and where $\alpha$ is $+$ if $n$ is even, and $-$ if not. As the procedure is similar for any $n$, we will suppose that $n = 0$, and $d$ is then equivalent to $[1]^{\sharp} \vee [a, 1]$ for $a \in t\Theta$. The fact that $g$ is algebraic implies that there exists a marked globular sum $c'$ and an integer $k$, such that $d'$ is of shape $[k]^{\sharp} \vee c'$ and such that $gi$ factors through $c'$. These data verify the desired condition.

**Proposition 5.2.2.6.** Let $p: X \to b^{\sharp}$ be a morphism exponentiable in $b$. Consider also the following shape of diagram

$$\begin{array}{c} X'' \longrightarrow X' \longrightarrow X \\ p'' \Big\downarrow \quad \quad \quad p' \Big\downarrow \quad \quad \quad p \Big\downarrow \\ C \xrightarrow[i]{} C' \xrightarrow[j]{} b^{\sharp} \end{array} \tag{5.2.2.7}$$

The following are equivalent.

(1) For any globular morphism $i: [a, 1]^{\sharp} \to b^{\sharp}$, $i^*p$ is a left cartesian fibration.
(2) For any diagram of shape (5.2.2.7), if $i$ is $i_n^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ with $n$ an integer and $\alpha := +$ if $n$ is even and $-$ if not, and $j$ is globular, then $p'' \to p'$ is a right Gray deformation retract.
(3) For any diagram of shape (5.2.2.7), if $i$ is a finite composition of pushouts of morphism of shape $i_n^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t$ with $n$ an integer and $\alpha := +$ if $n$ is even and $-$ if not, and $j$ is globular, then $p'' \to p'$ is a right Gray deformation retract.
(4) For any diagram of shape (5.2.2.7), if $i$ is in $\mathrm{F}_g$, then $p'' \to p'$ is a right Gray deformation retract.
(5) The morphism $p$ is a left cartesian fibration.

Proof. The implication $(1) \Rightarrow (2)$ comes from theorem 5.2.1.26 as morphisms of shape $i_n^{\alpha}$ are right Gray deformation retracts according to proposition 5.1.4.11, and as every globular morphism $\mathbf{D}_{n+1} \to b$ factors through a globular morphism $[a, 1] \to b$.

273