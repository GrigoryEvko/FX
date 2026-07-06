and so is weakly unique. The uniqueness of solutions of $\mathbf{eq}_{k,n}^{\circ -}$ is proved similarly.

We show now that $\mathbf{eq}_{k,n}^{\circ -}$ and $\mathbf{eq}_{k,n}^{\circ -}$ have solutions in $C$. Let $(x, y)$ be a solution of the equation

$$y: (\nu\#_0s)\#_k x \rightarrow (a^{-1}\#_{k-1}b)\#_k(\nu\#_{k-1}t)$$

Moreover, we can find such $x$ marked whenever $b$ is. We then have

$$(\nu\#_0s)\#_k x = (a^{-1}\#_{k-1}a\#_{k-1}x)\#_k(\nu\#_{k-1}t).$$

By weak uniqueness of solutions of $\mathbf{eq}_{k+1,n}^{\circ -}$, we then have a marked arrow

$$z: a^{-1}\#_{k-1}a\#_{k-1}x \rightarrow a^{-1}\#_{k-1}b.$$

But $a\#_{k-1}x$ and $b$ are solutions of an equation $\mathbf{eq}_{k,n}^{\circ -}$, and so there exists a marked arrow

$$\bar{y}: a\#_{k-1}x \rightarrow b.$$

If $b$ is marked, the arrow $x$ that we produce is also marked. The existence of a solution of $\mathbf{eq}_{k,n}^{\circ -}$ is proved similarly. $\square$

**3.20 Lemma.** *If the equations $\mathbf{eq}_{k,n}^{\circ -}$ and $\mathbf{eq}_{k,n}^{\circ -}$ have solutions in $C$ for any integers $0 < k \leq n$, then all equations have solutions in $C$.*

*Proof.* Let $\Lambda P \rightarrow P$ be a left equation. There is a decomposition of the source of $y$ of the shape

$$\pi_n^- y = l_n\#_{n-1}(l_{n-1}\#_{n-2}\dots\#_1(l_1\#_0x\#_0r_1)\#_1\dots\#_{n-2}r_{n-1})\#_{n-1}r_n$$

where for each $i$, $l_i$ and $r_i$ are marked $i$-arrows in $P$. We can then use the existence of solutions to $\mathbf{eq}_{k,n}^{\circ -}$ and $\mathbf{eq}_{k,n}^{\circ -}$ to get two sequences of arrows $(x_k)_{0<k<2n}$ and $(y_k)_{0<k<2n}$ such that:

- (1) $y_{2n-1}: x_{2n-1}\#_{n-1}r_n \rightarrow \pi_n^+ y$;
- (2) $y_{2k-1}: x_{2k-1}\#_{k-1}r_k \rightarrow x_{2k}$;
- (3) $y_{2k-2}: l_k\#_{k-1}x_{2k-2} \rightarrow x_{2k-1}$.

Moreover, arrows $x_k$ are marked whenever $\pi_n^+ y$ is. The couple $(x_0, \bar{y})$ is then a solution to $P$ where $\bar{y}$ is the composite:

$$\begin{aligned} \bar{y} := & \quad (l_n\#_{n-1}(l_{n-1}\#_{n-2}\dots\#_1((y_0\#_0r_1)\#_n y_1)\#_1\dots\#_{n-2}r_{n-1})\#_{n-1}r_n) \\ \#_n & \quad (l_n\#_{n-1}(l_{n-1}\#_{n-2}\dots\#_2((y_2\#_1r_2)\#_n y_3)\#_2\dots\#_{n-2}r_{n-1})\#_{n-1}r_n) \\ \#_n & \quad \dots \\ \#_n & \quad (y_{2n-2}\#_{n-1}r_n)\#_n y_{2n-1} \end{aligned}$$

If $\Lambda P \rightarrow P$ is a right equation, we define $\Lambda P \rightarrow P^{op}$ to be the left equation obtained by inverting the direction of the arrow of maximum dimension. A solution of $\Lambda P \rightarrow P$ is given by $(x, y^{-1})$ where $(x, y)$ is a solution of $\Lambda P \rightarrow P^{op}$. Moreover, one can find an arrow $x$ marked whenever the source of $y^{-1}$ is. $\square$

28