We allow ourselves to write this alternatively by taking the formal variables $\gamma, \delta$ more seriously and 'applying' $\sigma$ to them:

$$\delta : \Delta \vdash A \ (\sigma \ \delta) \ \text{type}_\ell \qquad \delta : \Delta \vdash t \ (\sigma \ \delta) : A \ (\sigma \ \delta)$$

Formally, this is justified by interpretation in the internal type theory of the presheaf category $\text{Set}^{\text{CW}}$. By virtue of functoriality, for $\sigma : \Delta \to \Gamma$ and $\tau : \Omega \to \Delta$ we have that

$$A \ (\sigma \ (\tau \ \omega)) \equiv A \ ((\sigma \circ \tau) \ \omega) \qquad t \ (\sigma \ (\tau \ \omega)) \equiv t \ ((\sigma \circ \tau) \ \omega)$$

Now let us consider the representation hypothesis. In categorical notation, for $\Gamma : \text{ob}_\mathcal{C}$ and $A : \text{Ty}_\ell$ we have a representing object $\Gamma \cdot A : \text{ob}_\mathcal{C}$ called the context extension. In type-theoretic notation, we denote the context extension by

$$\frac{\Gamma \text{ ob} \qquad \gamma : \Gamma \vdash A \ \gamma \ \text{type}_\ell}{(\gamma : \Gamma, \ a : A \ \gamma) \ \text{ob}}$$

Note that this is an operation that takes an element of one set (the absolute judgment $\Gamma$ ob) and an element of one presheaf (the hypothetical judgment $\gamma : \Gamma \vdash A \ \gamma \ \text{type}_\ell$) and produces an element of a set (the absolute judgment $(\gamma : \Gamma, \ a : A \ \gamma)$ ob). As before, at the moment the 'variables' $\gamma$ and $a$ are just a convention of notation.

We then have a family of bijections, natural in $\Delta$:

$$(\Delta \to (\gamma : \Gamma, \ a : A \ \gamma)) \simeq ((\sigma : \Delta \to \Gamma) \times (\delta : \Delta \vdash t \ \delta : A \ (\sigma \ \delta)))$$

Note that this says that a substitution into an extended context $(\gamma : \Gamma, \ a : A \ \gamma)$ is precisely a substitution $\sigma$ into $\Gamma$, along with some term $t$ of type $A^\sigma$. By the Yoneda lemma, the left-to-right part of this bijection is determined by setting $\Delta$ to $(\gamma : \Gamma, \ a : A \ \gamma)$ and evaluating at the identity $1_{(\gamma : \Gamma, \ a : A \ \gamma)}$. The first component gives us a substitution $\text{pt}^A : (\gamma : \Gamma, \ a : A \ \gamma) \to \Gamma$, which we call a fundamental context projection or parent map$^7$ and denote by:

$$\text{pt}^A : (\gamma : \Gamma, \ a : A \ \gamma) \to \Gamma$$

The second component then gives us a term that we call the zero variable and denote by $\text{zv}^A : \text{Tm}((\gamma : \Gamma, \ a : A \ \gamma), A^{\text{pt}^A})$, or:

$$\delta : (\gamma : \Gamma, \ a : A \ \gamma) \vdash \text{zv}^A \ \delta : A \ (\text{pt}^A \ \delta)$$

Note that the forward direction of the bijection sends a substitution $\tau : \Delta \to (\gamma : \Gamma, \ a : A \ \gamma)$ to the pair $(\text{pt}^A \circ \tau, \ (\text{zv}^A)^\top)$. That this map is a bijection is witnessed by the existence of a substitution extension operation:

$$\frac{\sigma : \Delta \to \Gamma \qquad \delta : \Delta \vdash t \ \delta : A \ (\sigma \ \delta)}{[\sigma, \ t] : \Delta \to (\gamma : \Gamma, \ a : A \ \gamma)}$$

such that for $\sigma : \Delta \to \Gamma$ and $\delta : \Delta \vdash t \ \delta : A \ (\sigma \ \delta)$, we have:

$$\text{pt}^A \circ [\sigma, \ t] \equiv \sigma \tag{4.2}$$

$$(\text{zv}^A)^{[\sigma, \ t]} \equiv t \tag{4.3}$$

$^7$From the perspective of type theoretic fibration categories, an alternative approach to semantics from that of CwFs, the role of fundamental context projections is instead played by fibrations.

42