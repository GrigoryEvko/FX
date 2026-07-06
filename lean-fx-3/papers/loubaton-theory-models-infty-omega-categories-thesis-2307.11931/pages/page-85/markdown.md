2.2. THE COMPLICIAL MODEL

(1) The *complicial horn inclusions* are the regular extensions:

$$\Lambda^k[n] \to [n]^k, \ n \ge 1, \ n \ge k \ge 0.$$

(2) The *complicial thinness extensions*:

$$([n]^k)' \to ([n]^k)'', \ n \ge 2, \ n \ge k \ge 0.$$

(3) The *saturation extensions*:

$$[n] \star [3]^{eq} \star [m] \to [n] \star [3]^\sharp \star [m], \ n, m \ge -1.$$

The set of complicial horn inclusions is $\Lambda$ and the reunion of *complicial thinness extensions* and of *saturation extensions* is $S$.

**Definition 2.2.1.5.** Let $n \in \mathbb{N} \cup \{\omega\}$. A $n$-*complicial set* is a stratified set having the right lifting property against all elementary anodyne extensions and against all morphisms $[k] \to [k]_t$ for $k > n$.

**Theorem 2.2.1.6** (Ozornova, Rovelli, Verity). *Let $n \in \mathbb{N} \cup \{\omega\}$. There exists a nice model structure on stratified simplicial sets, denoted by $\mathrm{tPsh}(\Delta)^n$, whose fibrant objects are $n$-complicial sets.*

*A left adjoint $F : \mathrm{tPsh}(\Delta) \to D$ to a model category is a left Quillen functor if it preserves cofibrations and sends all elementary anodyne extensions and morphisms $[k] \to [k]_t$, for $k > n$, to weak equivalences.*

*Proof.* This is [OR20b, theorem 1.25].

During this chapter, we will only be interested in the model structure for $\omega$-complicial sets, and we will therefore drop the index $\omega$. The $\omega$-complicial sets will then just be called *complicial sets* and we will denote by $\mathrm{tPsh}(\Delta)$ the model category $\mathrm{tPsh}(\Delta)^\omega$.

**2.2.1.7.** A *marked simplicial set* is a stratified simplicial set that has the right lifting property against entire acyclic cofibrations. In particular, all complicial sets are marked. The category of marked simplicial sets is denoted by $\mathrm{mPsh}(\Delta)$. There is an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow[\downarrow]{\perp} \mathrm{mPsh}(\Delta) : \iota \tag{2.2.1.8}$$

The left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified simplicial set $(X, tX)$ to the marked simplicial set $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$

75