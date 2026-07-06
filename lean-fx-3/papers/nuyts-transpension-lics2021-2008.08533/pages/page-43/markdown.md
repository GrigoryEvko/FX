Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:43

amazing right adjoint. Let us write $1 \Leftarrow \Sigma u \circ \lrcorner[u] : \text{spdrop}_u \rrcorner \text{spconst}_u : 1 \Rightarrow \forall u \circ \Omega[u]$ and $\text{spunmer}_u : \Pi u \circ \Diamond[u] \Rightarrow 1$ for the 2-cells built by partial transposition from either $\text{hide}_u \rrcorner \text{spoil}_u$ or $\text{cospoil}_u$ (Theorem 6.31), which are each other's transposite. The following are isomorphisms:

$$\kappa := \text{spconst}_u \star 1_b : b \cong \forall u \circ \Omega[u] \circ b,$$

$$\zeta := 1_b \star \text{spunmer}_u : b \circ \Pi u \circ \Diamond[u] \cong b.$$

For $\kappa$, this is intuitively clear from the fact that we are considering $\mathbb{U}$-cells in a discrete presheaf produced by $b$. For $\zeta$, this is similarly clear after taking the left adjoints:

$$\text{spconst}_u \star 1_{\int} : \int \cong \forall u \circ \Omega[u] \circ \int$$

where $\int$, the left name of $b$, is semantically the connected components functor which also produces discrete presheaves. Write $\int \Leftarrow 1 : \eta \rrcorner \varepsilon : b \Rightarrow 1$ for the co-unit of the comonad $b$. We can define

$$\mathbb{U} \surd \sqcup : (b \mid \mathsf{U}) \to \mathsf{U}$$

$$\mathbb{U} \multimap \sqcup : \mathsf{U} \to \mathsf{U}$$

$$\mathbb{U} \surd A = \left\langle \Pi u \circ \Diamond[u] \mid A[\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$\mathbb{U} \multimap A = \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\text{spconst}_u}^{\text{spdrop}_u}] \right\rangle.$$

Let two global types $\cdot \mid \Gamma, \mathbf{a}_{\zeta} \vdash A, B$ type be given. Applying the non-dependent version of Proposition 3.4 to the adjunction $\forall u \circ \Omega[u] \dashv \surd_{\mathbb{U}} = \Pi u \circ \Diamond[u]$ with unit $(1_{\Pi u} \star \text{reidx}_u \star 1_{\Omega[u]}) \circ \text{const}_u : 1 \Rightarrow \Pi u \circ \Diamond[u] \circ \forall u \circ \Omega[u]$ yields:

$$(A[\mathbf{a}_{\zeta}^{\eta}] \to \mathbb{U} \surd B)$$

$$\cong \left\langle \surd_{\mathbb{U}} \mid \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\zeta}^{\eta}][\mathbf{a}_{\text{const}_u}^{\text{drop}_u}][\mathbf{a}_{\Pi u}^{\Omega[u]}, \mathbf{a}_{\text{reidx}_u}^{\text{app}_u}, \mathbf{a}_{\Omega[u]}^{\Sigma u}] \right\rangle \to B[\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$= \left\langle \surd_{\mathbb{U}} \mid \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\text{spconst}_u}^{\text{spdrop}_u}] \right\rangle [\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \to B[\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$= \left\langle \surd_{\mathbb{U}} \mid \left( \left\langle \forall u \circ \Omega[u] \mid A[\mathbf{a}_{\text{spconst}_u}^{\text{spdrop}_u}] \right\rangle \to B \right) [\mathbf{a}_{\zeta^{-1}}][\mathbf{a}_{\zeta}^{\eta}, \mathbf{a}_{\Pi u \circ \Diamond[u]}^{\forall u \circ \Omega[u]}] \right\rangle$$

$$= \mathbb{U} \surd ((\mathbb{U} \multimap A) \to B).$$

Equality of the substitutions applied to $A$ is proven by transposing $\forall u \circ \Omega[u]$ to the left as $\Pi u \circ \Diamond[u]$. Then the unit $\text{const}_u \circ (1_{\Pi u} \star \text{reidx}_u \star 1_{\Omega[u]}) : 1 \Rightarrow \Pi u \circ \Diamond[u] \circ \forall u \circ \Omega[u]$ becomes $1_{\Pi u \circ \Diamond[u]}$, leaving just $\varepsilon : b \Rightarrow 1$, whereas $\text{spconst}_u : 1 \Rightarrow \forall u \circ \Omega[u]$ becomes $\text{spunmer}_u : \Pi u \circ \Diamond[u] \Rightarrow 1$ and cancels against $\zeta^{-1}$, again leaving just $\varepsilon$.

Applying the $b$ modality to both sides of the isomorphism and using $\zeta$ to get rid of the amazing right adjoint on the right, yields transposition functions as given by Licata et al. [LOPS18].

We refer back to Section 6.7 for the opposite construction: a transpension type for a cartesian multiplier can be constructed from an amazing right adjoint [Yet87].

10.2. The $\Phi$-combinator. In Fig. 10, we state BCM's $\Phi$-rule [BCM15, Mou16], also known as extent [CH21]; both a slight reformulation adapted to FFTraS and the rule PHI adapted to MTraS.

In the binary version of the BCM system, or in FFTraS with an interval shape as in cubical type theory, the $\Phi$-combinator allows us to define functions of type $\forall i.(y : B i) \to C i y$ from an action $c_\epsilon$ at every endpoint $\epsilon$ and a compatible action $c_\forall$ on sections $\forall i.B i$. When the resulting function $\Phi c_0 c_1 c_\forall$ is applied to an endpoint $\epsilon : \mathbb{I}$ it just reduces to the corresponding action $\lambda y.c_\epsilon$. When it is applied to an interval variable $i : \mathbb{I}$ and expression $b$ that depends