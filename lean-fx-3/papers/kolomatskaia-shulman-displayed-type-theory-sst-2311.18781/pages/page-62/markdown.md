We then inductively define:

$$\pi(\lim_{\mathfrak{m}^{n+2}} \bar{Y}) \equiv \lim_{\mathfrak{m}^{n+1}} \pi \bar{Y}$$

$$(\lim_{\mathfrak{m}^{n+2}} \bar{Y})_{n+2} \equiv (\lim_{\mathfrak{m}^{n}} \bar{Y}^d)_{n+1}$$

$$\pi(\lim_{\mathfrak{m}^{n+2}} \bar{v}) \equiv \lim_{\mathfrak{m}^{n+1}} \pi \bar{v}$$

$$(\lim_{\mathfrak{m}^{n+2}} \bar{v})_{n+2} \equiv (\lim_{\mathfrak{m}^{n}} \bar{v}^d)_{n+1}$$

$$\pi(\text{res}_{\mathfrak{m}^{n+2}}^{\partial m} u) \equiv \text{res}_{\mathfrak{m}^{n+1}}^{\partial m} \pi u$$

$$(\text{res}_{\mathfrak{m}^{n+2}}^{\partial m} u)_{n+2} \equiv (\text{res}_{\mathfrak{m}^{n}}^d u^d)_{n+1}$$

$$\pi(\text{res}_{\mathfrak{m}^{n+2}}^m u) \equiv \text{res}_{\mathfrak{m}^{n+1}}^m \pi u$$

$$(\text{res}_{\mathfrak{m}^{n+2}}^m u)_{n+2} \equiv (\text{res}_{\mathfrak{m}^{n}}^m u^d)_{n+1}.$$

As always, this says that the constructions are performed level-wise. From this, theorems eqs. (4.25) to (4.28) then follow inductively, since the hypothesised display formulas were used to define each successive level. The correctness of these definitions will follow from verifying laws in appendix A.4.

### 4.2.9 The Simplicial Model

Having constructed the truncated simplicial models $\mathfrak{sm}^n$, we obtain the *simplicial model* fairly directly by taking a limit. In order to state this, we first define a *tail-cutting truncation functor* and extend *décalage* to an endofunctor:

$$\pi_n : \mathcal{C}^{\Delta^+} \to \mathcal{C}^{\Delta_n^+} \quad (-)^D : \mathcal{C}^{\Delta^+} \to \mathcal{C}^{\Delta^+}$$

$$(\pi_n \Gamma)_{m+1} \equiv \Gamma_{m+1} \quad (\Gamma^D)_{m+1} \equiv \Gamma_{m+2}$$

$$(\pi_n \Gamma)^b \equiv \Gamma^b \quad (\Gamma^D)^b \equiv \Gamma^{\ddagger b}$$

$$(\pi_n \sigma)_{m+1} \equiv \sigma_{m+1} \quad (\sigma^D)_{m+1} \equiv \sigma_{m+2}$$

Since décalage is now an endofunctor, $\rho$ no longer involves truncation:

$$\rho : (-)^D \Rightarrow 1_{\mathcal{C}^{\Delta^+}}$$

$$(\rho_\Gamma)_{m+1} \equiv \Gamma^{\Theta_1(m+1)}$$

Now we define the types and terms in $\mathfrak{sm}$ to be compatible towers of types and terms in the truncated models $\mathfrak{sm}^n$. In syntax this can be expressed by the following infinitary bidirectional rules:

$$\frac{(\gamma : \pi_n \Gamma \vdash_{\mathfrak{sm}_n} \pi_n A \gamma \text{ type}_\ell)_{n \geqslant -2} \quad (\pi(\pi_{n+1} A) \equiv \pi_n A)_{n \geqslant -2}}{\gamma : \Gamma \vdash_{\mathfrak{sm}} A \gamma \text{ type}_\ell}$$

$$\frac{(\gamma : \pi_n \Gamma \vdash_{\mathfrak{sm}_n} \pi_n t \gamma : \pi_n A \gamma)_{n \geqslant -2} \quad (\pi(\pi_{n+1} t) \equiv \pi_n t)_{n \geqslant -2}}{\gamma : \Gamma \vdash_{\mathfrak{sm}} t \gamma : A \gamma}$$

We also define:

$$\frac{\gamma : \Gamma \vdash_{\mathfrak{sm}} A \gamma \text{ type}_\ell}{A_{n+1} \equiv (\pi_{n+1} A)_{n+1}} \quad \frac{\gamma : \Gamma \vdash_{\mathfrak{sm}} t \gamma : A \gamma}{t_{n+1} \equiv (\pi_{n+1} t)_{n+1}}.$$

62