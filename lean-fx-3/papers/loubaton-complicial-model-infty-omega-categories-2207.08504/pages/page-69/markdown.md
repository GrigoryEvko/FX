2.2. THE COMPLICIAL MODEL

**Remark 2.2.1.2.** Given a functor $i : I \mapsto (F(i), tF(i))$ with value in stratified simplicial sets, its colimit is given by $(\operatorname{colim} F(i), M)$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \operatorname{colim} F(i)$ for any $i : I$.

**Definition 2.2.1.3 (Verity).** We can extend the join to stratified simplicial sets as follows: If $(X, tX)$ and $(Y, tY)$ are two stratified simplicial sets, we define $tX \star tY$ as the set of simplices of $X \star Y$ of shape $x \star y$ where either $x$ or $y$ are thin. We then define

$$(X, tX) \star (Y, tY) := (X \star Y, tX \star tY).$$

**Definition 2.2.1.4.** A stratified monomorphism $f : X \to Y$ is

(1) *entire* if it is an identity on underlying simplicial sets.
(2) *regular* if for every $n \geq 1$ the following diagram is a pullback:

$$\begin{array}{ccc} tX_n & \longrightarrow & X_n \\ \downarrow & \downarrow & \downarrow \\ tY_n & \longrightarrow & Y_n. \end{array}$$

**Definition 2.2.1.5 (Verity).** We define several stratified structures on $[n]$.

(1) $[n]_t$. The top $n$-simplex is thin. All degeneracies are thin.
(2) $[n]^k$. All simplices that include $\{k-1, k, k+1\} \cap [n]$ are thin. All degeneracies are thin.
(3) $([n]^k)'$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(4) $([n]^k)''$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face, the $k$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(5) $[3]^{eq}$. All simplices of dimension strictly higher than 2, together with $[0, 2]$ and $[1, 3]$ are thin. All degeneracies are thin.
(6) $[n]^2$. All simplices are thin.

**Definition 2.2.1.6.** An *elementary anodyne extension* is one of the following:

(1) The *complicial horn inclusions* are the regular extensions:

$$\Lambda^k[n] \to [n]^k, \ n \geq 1, \ n \geq k \geq 0.$$

(2) The *complicial thinness extensions*:

$$([n]^k)' \to ([n]^k)'', \ n \geq 2, \ n \geq k \geq 0.$$

(3) The *saturation extensions*:

$$[n] \star [3]^{eq} \star [m] \to [n] \star [3]^2 \star [m], \ n, m \geq -1.$$

The set of complicial horn inclusions is $\Lambda$ and the reunion of *complicial thinness extensions* and of *saturation extensions* is $S$.

69