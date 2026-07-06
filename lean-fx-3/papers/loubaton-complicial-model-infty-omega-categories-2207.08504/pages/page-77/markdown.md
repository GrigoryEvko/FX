2.2. THE COMPLICIAL MODEL

the morphism induced by the inclusion $X \otimes [1, 2] \subset X \otimes [2]_t$. We define similarly the left Quillen functor

$$[1] \vee \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[1]\amalg[0]}/$$

and the morphisms

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \Sigma X \hookrightarrow [1] \vee \Sigma X.$$

**Proposition 2.2.2.19.** *Morphisms*

$$\Sigma X \coprod_{[0]} [1] \to \Sigma X \vee [1] \quad \text{and} \quad [1] \coprod_{[0]} \Sigma X \to [1] \vee \Sigma X$$

*are acyclic cofibrations.*

*Proof.* We have cartesian squares:

$$\begin{array}{c} X \otimes ([0] \coprod [1, 2]) \longrightarrow X \otimes \Lambda^1[2] \longrightarrow X \otimes [2]_t \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [0] \coprod [1] \longrightarrow \Sigma X \coprod_{[0]} [1] \longrightarrow \Sigma X \vee [1]. \end{array}$$

The upper right horizontal morphism is an acyclic cofibration, and so is the downer right horizontal one. We proceed similarly for the other morphism. $\square$

**Definition 2.2.2.20.** The Gray tensor product induced a left Quillen functor

$$\_ \otimes [1] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$$

called the *Gray cylinder*. The join and the co-join also induce two left Quillen functors

$$\_ \star [0] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0]}/ \qquad [0] \stackrel{\circ}{\star} \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0]}/$$

called the *Gray cone* and the *Gray $\circ$-cone*. We denote by

$$\begin{array}{c c c c c} \mathrm{mPsh}(\Delta). & \to & \mathrm{mPsh}(\Delta) & \mathrm{mPsh}(\Delta). & \to & \mathrm{mPsh}(\Delta) \\ (X, x) & \mapsto & X_{/x} & (X, x) & \mapsto & X_{x/} \end{array}$$

respectively called the *slice of $X$ over $x$* and the *slice of $X$ under $x$*, the right adjoints of the Gray cone and the Gray $\circ$-cone.

Remark furthermore that we have canonical natural transformation $X_{x/} \to X$ and $X_{/x} \to X$, induced by the natural transformation $X \to X \star [0]$ and $X \to [0] \stackrel{\circ}{\star} X$.

### 2.2.3 Street nerve

We recall that $(0, \omega)$-categories are defined in section 1.1.1. The Gray operations on $(0, \omega)$-categories - $\_ \otimes [1]$, $\_ \star 1$, $1 \stackrel{\circ}{\star} \_ -$ are defined in section 1.2.4.

**Construction 2.2.3.1.** In [Str87], Street defines a cosimplicial object in $(0, \omega)$-cat, that associates to $n$, the $n^{th}$ *oriental* $O_n$. The original construction of this object is complicated, but Ara and Maltsiniotis have shown that it can be easily defined using Gray operations. Indeed, in [AM20, Corollaire 7.10], these authors construct an isomorphism

$$O_n \cong \overbrace{1 \star \dots \star 1}^{n+1}$$

77