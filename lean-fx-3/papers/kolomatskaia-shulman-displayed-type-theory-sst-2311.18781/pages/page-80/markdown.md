Weakening and substituting to the needed context $\Gamma$, $\phi : \Phi^D$, $u : \lim \bar{Y}$, we have

$$\Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} (Y^{\partial n})^d \phi (\text{res}^{\partial n} u) \text{ tel}$$

$$\Gamma, \phi : \Phi^D, u : \lim \bar{Y}, \partial v : (Y^{\partial n})^d \phi (\text{res}^{\partial n} u) \vdash_{sm} (Y^n)^d \phi \langle \text{res}^{\partial n} u, \partial v \rangle (\text{res}^n u) \text{ type}$$

such that

$$\begin{aligned} (Y^{\partial(n+1)})^d \phi (\text{res}^{\partial(n+1)} u) &\equiv \left( \partial v : \bar{Y}^{\partial n}, v : \bar{Y}^n \partial v \right)^d \phi [\text{res}^{\partial n} u, \text{res}^n u] \\ &\equiv \left( \partial v : (\bar{Y}^{\partial n})^d \phi (\text{res}^{\partial n} u), v : (\bar{Y}^n)^d \phi \langle \text{res}^{\partial n} u, \partial v \rangle (\text{res}^n u) \right). \end{aligned}$$

Thus, these data form another infinite telescope, which we denote

$$\begin{aligned} \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} \bar{Y}^d \phi u \text{ stel}^\infty \\ (Y^d)^{\partial n} \phi u &\equiv (Y^{\partial n})^d \phi (\text{res}^{\partial n} u) \\ (Y^d)^n \phi u \partial v &\equiv (Y^n)^d \phi \langle \text{res}^{\partial n} u, \partial v \rangle (\text{res}^n u) \end{aligned}$$

We say that display respects $\omega$-limits if

$$\begin{aligned} \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} \lim \bar{Y}^d \phi u &\equiv \lim(\bar{Y}^d \phi u) \\ \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} (\text{res}^{\partial n})^d \phi u &\equiv \text{res}^{\partial n} \phi u \\ \Gamma, \phi : \Phi^D, u : \lim \bar{Y} \vdash_{sm} (\text{res}^n)^d \phi u &\equiv \text{res}^n \phi u. \end{aligned}$$

where in the last two equations, the left-hand side is a restriction relative to $\bar{Y}$, and on the right-hand side it is relative to $\bar{Y}^d$.

**Theorem 4.41.** *Display respects $\omega$-limits in the simplicial model.*

*Proof.* This holds essentially by construction of $\omega$-limits therein, plus passing across the translation between different forms of display from theorem 4.40. $\square \triangleleft$

### 4.5 SEMANTICS OF SEMI-SIMPLICIAL TYPES

Finally, we construct semantics for the displayed coinductive types of section 3.3, in particular including SST. As with most kinds of coinductive definitions, they are terminal coalgebras of some sort, but in this case they are terminal coalgebras for a *copointed* endofunctor. We will construct such a terminal coalgebra by a sequential limit construction, assuming that the base (discrete) model admits such limits.

#### 4.5.1 Terminal coalgebras for copointed endofunctors

**Definition 4.42.** A **copointed endofunctor** of a category $\mathcal{C}$ is a functor $F : \mathcal{C} \to \mathcal{C}$ together with a natural transformation $\epsilon : F \to 1_{\mathcal{C}}$. A **coalgebra** for a copointed endofunctor is an object $X$ with a morphism $x : X \to FX$ such that the composite $X \xrightarrow{x} FX \xrightarrow{\epsilon_x} X$ is the identity. A **terminal coalgebra** is a terminal object of the category of coalgebras.

80