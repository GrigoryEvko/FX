The the above introduction rules equivalently then say that A and t in sm are defined by the data of each of the simplex levels $A_{n+1}$ and $t_{n+1}$. At this point, every single construction in $\text{sm}^n$ performed above extends to sm levelwise, since it is preserved strictly by all the finite truncation functors. In lieu of listing all of them, we will only give the case of display, which is slightly modified in the absence of truncation:

$$\frac{\gamma : \Gamma \vdash_{\text{sm}} A \gamma \text{ type}_\ell}{\gamma^+ : \Gamma^D, a : A^{pr} \gamma^+ \vdash_{\text{sm}} A^d \gamma^+ a \text{ type}_\ell}$$

$$\frac{\gamma : \Gamma \vdash_{\text{sm}} t \gamma : A \gamma}{\gamma^+ : \Gamma^D \vdash_{\text{sm}} t^d \gamma^+ : A^d \gamma^+ t^{pr}}$$

The computation rules for display on variables, $\Pi$-types, universes, and $\omega$-limits similarly hold in sm when modified to exclude $\pi$.

### 4.3 MODALITIES

We now relate the discrete (dm) and simplicial (sm) models by way of modalities, and introduce modal variants of the structural operations of a CwF.

The interesting facet of our approach is our treatment of $(\Gamma, \bullet_\Delta)$ and $(\gamma : \Gamma, a :^\Delta A \gamma)$. These examples concern the passage from dm to sm. Both examples construct a context in sm, but where (part of) the starting data is discrete — $\Gamma$ in the first example and A in the second example. One naive approach to this construction would be to convert the discrete data to simplicial data (fibrantly so in the second case) — in the first example we would set values of the presheaf at $m + 2$ to be zeros, and in the second example we would set the simplex types at levels $m + 2$ to be units. However, this would require us to assume that the starting CwF has, respectively, an initial object and unit types. The approach that we take avoids these assumptions, and also ensures that all computation laws have definitionally strict interpretations.

#### 4.3.1 Pieces of the triangle modality

We begin by dealing with $\triangle$. The modality $\triangle$ is supposed to construct a constant (augmented semi-)simplicial diagram, while its left adjoint $\bullet_\triangle$ picks out the object of (-1)-simplices. Both of these operations are determined levelwise by their behavior on truncated diagrams, which is where most of the work is. Recalling that we will not be modeling the modality $\triangle$ on types itself, since it would require assuming the existence of unit types in dm, in this section we describe the other aspects of $\triangle$ in the models $\text{sm}^{n+1}$ and how they fit together on sm.

We begin by defining a functor $\left(-, \bullet_{\triangle_{n+1}}\right) : \mathcal{C}^{\triangle_{n+1}^+} \to \mathcal{C}$ via:

$$\begin{array}{l} \left(\gamma : \Gamma, \bullet_{\triangle_{n+1}}\right) \equiv \Gamma_{-1} \\ \left[\sigma, \bullet_{\triangle_{n+1}}\right] \equiv \sigma_{-1} \end{array}$$

Then we construct modal extension for $\triangle_{n+1}$ in $\text{sm}^{n+1}$:

$$\frac{\begin{array}{c} \Gamma \text{ ob}_{\text{sm}^{n+1}} \quad \gamma : \Gamma, \bullet_{\triangle_{n+1}} \vdash_{\text{dm}} A \gamma \text{ type}_\ell \\ \hline \left(\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma\right) \text{ ob}_{\text{sm}^{n+1}} \end{array}}{\frac{\sigma : \Delta \to_{\text{sm}^{n+1}} \Gamma \quad \gamma : \Gamma, \bullet_{\triangle_{n+1}} \vdash_{\text{dm}} t \gamma : A \gamma}{\left[\sigma, t\right]_{\triangle_{n+1}} : \Delta \to_{\text{sm}^{n+1}} \left(\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma\right)}}$$

63