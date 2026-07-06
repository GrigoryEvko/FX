CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

**2.2.1.1.** A *stratified simplicial set* is a pair $(X, tX)$ where $X$ is a simplicial set and $tX := \cup_{n>0} tX_n$ a graded set such that for any $n \geq 1$, $tX_n$ is a subset of $X_n$ that includes all degenerate simplices. A simplex in $tX$ is called *thin*.

A *stratified morphism* $f : (X, tX) \to (Y, tY)$ is the data of a morphism on the underlying simplicial set such that $f(tX_n) \subset tY_n$. The category of stratified simplicial sets is denoted by $\text{tPsh}(\Delta)$.

Given a functor $i : I \mapsto (F(i), tF(i))$ with value in stratified simplicial sets, its colimit is given by $(\text{colim } F(i), M)$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \text{colim } F(i)$ for any $i : I$.

We can extend the join to stratified simplicial sets as follows: If $(X, tX)$ and $(Y, tY)$ are two stratified simplicial sets, we define $tX \star tY$ as the set of simplices of $X \star Y$ of shape $x \star y$ where either $x$ or $y$ are thin. We then define

$$(X, tX) \star (Y, tY) := (X \star Y, tX \star tY).$$

**Definition 2.2.1.2.** A stratified monomorphism $f : X \to Y$ is

(1) *entire* if it is an identity on underlying simplicial sets.
(2) *regular* if for every $n \geq 1$ the following diagram is a pullback:

$$\begin{array}{ccc} tX_n & \longrightarrow & X_n \\ \downarrow & \downarrow & \downarrow \\ tY_n & \longrightarrow & Y_n. \end{array}$$

**Definition 2.2.1.3.** We define several stratified structures on $[n]$.

(1) $[n]_t$. The top $n$-simplex is thin. All degeneracies are thin.
(2) $[n]^k$. All simplices that include $\{k-1, k, k+1\} \cap [n]$ are thin. All degeneracies are thin.
(3) $([n]^k)'$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(4) $([n]^k)''$. All simplices that include $\{k-1, k, k+1\} \cap [n]$, together with the $(k-1)$-face, the $k$-face and the $(k+1)$ face are thin. All degeneracies are thin.
(5) $[3]^{eq}$. All simplices of dimension strictly higher than 2, together with $[0, 2]$ and $[1, 3]$ are thin. All degeneracies are thin.
(6) $[n]^2$. All simplices are thin.

**Definition 2.2.1.4.** An *elementary anodyne extension* is one of the following:

74