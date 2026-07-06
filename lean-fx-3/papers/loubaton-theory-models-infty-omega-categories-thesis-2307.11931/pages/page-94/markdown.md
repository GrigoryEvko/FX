CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

**Proposition 2.2.2.20.** *Morphisms*

$$\Sigma X \coprod_{[0]} [1] \rightarrow \Sigma X \vee [1] \quad \text{and} \quad [1] \coprod_{[0]} \Sigma X \rightarrow [1] \vee \Sigma X$$

*are acyclic cofibrations.*

*Proof.* We have cartesian squares:

$$\begin{array}{ccc} X \otimes ([0] \coprod [1, 2]) & \longrightarrow & X \otimes \Lambda^1[2] \longrightarrow X \otimes [2]_t \\ \downarrow & & \downarrow \\ [0] \coprod [1] & \longrightarrow & \Sigma X \coprod_{[0]} [1] \longrightarrow \Sigma X \vee [1]. \end{array}$$

The upper right horizontal morphism is an acyclic cofibration, and so is the downer right horizontal one. We proceed similarly for the other morphism. □

### 2.2.3 Gray cylinder, Gray cone and Gray o-cone

#### 2.2.3.1. The Gray tensor product induced a left Quillen functor

$$\_ \otimes [1] : \text{mPsh}(\Delta) \rightarrow \text{mPsh}(\Delta)$$

called the *Gray cylinder*. The join and the co-join also induce two left Quillen functors

$$\_ \star [0] : \text{mPsh}(\Delta) \rightarrow \text{mPsh}(\Delta)_{[0]}/ \quad [0] \stackrel{co}{\star} \_ : \text{mPsh}(\Delta) \rightarrow \text{mPsh}(\Delta)_{[0]}/$$

called the *Gray cone* and the *Gray o-cone*. We denote by

$$\begin{array}{ccc} \text{mPsh}(\Delta). & \rightarrow & \text{mPsh}(\Delta) \\ (X, x) & \mapsto & X_{/x} \end{array} \qquad \begin{array}{ccc} \text{mPsh}(\Delta). & \rightarrow & \text{mPsh}(\Delta) \\ (X, x) & \mapsto & X_{x/} \end{array}$$

respectively called the *slice of X over x* and the *slice of X under x*, the right adjoints of the Gray cone and the Gray o-cone.

Remark furthermore that we have canonical natural transformation $X_{x/} \rightarrow X$ and $X_{/x} \rightarrow X$, induced by the natural transformation $X \rightarrow X \star [0]$ and $X \rightarrow [0] \stackrel{co}{\star} X$.

**2.2.3.2.** The category of endomorphisms of marked simplicial sets has a monoidal structure given by the composition. The endomorphism $[0] \stackrel{co}{\star} \_ $ admits a monoid structure, where the multiplication is the natural transformation: $[0] \stackrel{co}{\star} ([0] \stackrel{co}{\star} X) \rightarrow [0] \stackrel{co}{\star} X$, induced by the pairing:

$$\begin{array}{ccc} X \otimes [1] \otimes [1] & \rightarrow & X \otimes [1] \\ (x, i, j) & \mapsto & (x, i \wedge j). \end{array}$$

84