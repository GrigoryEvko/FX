Such that the $\beta$ and $\eta$ laws hold:

$$\frac{\gamma : \Gamma, a : A \gamma \vdash t \gamma a : B \gamma a \quad \gamma : \Gamma \vdash s \gamma : A \gamma}{\gamma : \Gamma \vdash (\text{app } (\lambda t) s) \gamma \equiv t^{[1_r, s]} \gamma : B^{[1_r, s]} \gamma}$$

$$\frac{\gamma : \Gamma \vdash f \gamma : (a : A \gamma) \rightarrow B \gamma a}{\gamma : \Gamma \vdash (\lambda (\text{app } f^{\text{pt}} z v)) \gamma \equiv f \gamma : (\Pi A B) \gamma}$$

Or, in indexed notation:

$$\gamma : \Gamma \vdash \text{app } \gamma (\lambda a . t \gamma a) (s \gamma) \equiv t \gamma (s \gamma) : B \gamma (s \gamma)$$

$$\gamma : \Gamma \vdash \lambda a . \text{app } [\gamma, a] (f \gamma) a \equiv f \gamma : (a : A \gamma) \rightarrow B \gamma a$$

And such that the above constructs are stable under substitution, i.e. for $\sigma : \Delta \rightarrow \Gamma$:

$$(\Pi A B)^\sigma \equiv \Pi A^\sigma B^{W_2^\Delta \sigma}$$

$$(\lambda t)^\sigma \equiv \lambda t^{W_2^\Delta \sigma}$$

$$(\text{app } f s)^\sigma \equiv \text{app } f^\sigma s^\sigma$$

### 4.1.4 Universes

A $\mathcal{U}$-structure on a CwF with levels consists of the following structure and properties:

$$\frac{\ell \text{ level}}{\gamma : \Gamma \vdash \text{Type}_\ell \gamma \text{ type}_{\text{lsuc } \ell}}$$

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_\ell}{\gamma : \Gamma \vdash \text{Code } A \gamma : \text{Type}_\ell \gamma}$$

$$\frac{\gamma : \Gamma \vdash A \gamma : \text{Type}_\ell \gamma}{\gamma : \Gamma \vdash \text{EI } A \gamma \text{ type}_\ell}$$

Such that Code and EI are mutual inverses:

$$\frac{\gamma : \Gamma \vdash A \gamma \text{ type}_\ell}{\gamma : \Gamma \vdash \text{EI } (\text{Code } A) \gamma \equiv A \gamma}$$

$$\frac{\gamma : \Gamma \vdash A \gamma : \text{Type}_\ell \gamma}{\gamma : \Gamma \vdash \text{Code } (\text{EI } A) \gamma \equiv A \gamma : \text{Type}_\ell \gamma}$$

And such that the above constructs are stable under substitution, i.e. for $\sigma : \Delta \rightarrow \Gamma$:

$$\text{Type}_\ell^\sigma \equiv \text{Type}_\ell$$

$$(\text{Code } A)^\sigma \equiv \text{Code } A^\sigma$$

$$(\text{EI } A)^\sigma \equiv \text{EI } A^\sigma$$

### 4.1.5 Natural models

We recall from [Awo18] that a CwF can equivalently be described as a natural model: a category $\mathcal{C}$ together with an (algebraically) representable natural transformation $\text{pr} : \text{Tm} \rightarrow \text{Ty}$ of presheaves on $\mathcal{C}$. This amounts to representing the dependency of terms on types in 'fibered' rather than 'indexed' style, which is different from the usual type-theoretic notation, but it has the advantage that various operations can cleanly be described in terms of pr. Similarly, of course, a CwF with levels can be described by a family of representable transformations $\text{pr}_\ell : \text{Tm}_\ell \rightarrow \text{Ty}_\ell$.

In particular, like any morphism in a locally cartesian closed category, any such pr induces a polynomial endofunctor $P_{\text{pr}}$ of the presheaf category, where for any presheaf

44