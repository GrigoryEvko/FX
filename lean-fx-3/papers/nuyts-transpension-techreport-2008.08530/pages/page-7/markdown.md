$\widehat{\mathcal{W}}/\Gamma$ We need a natural isomorphism $\varepsilon : \forall(\Delta, \sigma).(\Gamma.\sigma^{-1}, \pi) \cong (\Delta, \sigma)$. Given $(\gamma, \delta) : W \Rightarrow \Gamma.\sigma^{-1}$ (i.e. we know $\sigma \circ \delta = \gamma$), we define $\varepsilon \circ (\gamma, \delta) = \delta : W \Rightarrow \Delta$. Then

$$\sigma \circ \varepsilon \circ (\gamma, \delta) = \sigma \circ \delta = \gamma = \pi \circ (\gamma, \delta), \tag{6}$$

so indeed we have a morphism in the slice category. It is inverted by sending $\delta : W \Rightarrow \Delta$ to $(\sigma \circ \delta, \delta) : W \Rightarrow \Gamma.\sigma^{-1}$. $\square$

**Corollary 2.3.7.** We have $\widehat{\mathcal{W}/U} \cong \widehat{\mathcal{W}/\mathbf{y}}U \simeq \widehat{\mathcal{W}}/\mathbf{y}U$. $\square$

### 2.3.5 Substitution and its adjoints

**Definition 2.3.8.** Given $U \in \mathcal{W}$, we write

- $\Sigma_U : \mathcal{W}/U \to \mathcal{W} : (W, \psi) \mapsto W$,
- $\Omega_U : \mathcal{W} \to \mathcal{W}/U : W \to (W \times U, \pi_2)$ (if $\mathcal{W}$ has cartesian products with $U$).

**Proposition 2.3.9.** If $\Omega_U$ exists, then $\Sigma_U \dashv \Omega_U$. We denote the unit as $\text{copy}_U : \text{Id} \to \Omega_U \Sigma_U$ and the co-unit as $\text{drop}_U : \Sigma_U \Omega_U \to \text{Id}$. $\square$

**Proposition 2.3.10.** 1. If $U \to \top$ is split epi, then the functor $\Omega_U$ is faithful.

2. (Not used). If $U \to \top$ is mono, then $\Sigma_U$ is full.$^5$

*Proof.* 1. We have some $v : \top \to U$, so that the action of $\Omega_U$ on morphisms sending $\varphi \mapsto \varphi \times U$ can be inverted: $\varphi = \pi_1 \circ (\varphi \times U) \circ (\text{id}, v)$.

2. Take slice objects $(W_1, \psi_1)$ and $(W_2, \psi_2)$ and a morphism $\varphi : W_1 \to W_2$. The fact that $U \to \top$ is mono just means that morphisms to $U$ are unique if existent. Then $\varphi$ is also a morphism between the slice objects. $\square$

**Definition 2.3.11.** Given $\chi : W'_0 \to W_0$ in $\mathcal{W}$, we write

- $\Sigma/\chi : \mathcal{W}/W'_0 \to \mathcal{W}/W_0 : (W', \psi') \mapsto (W', \chi \circ \psi')$,
- $\Omega/\chi : \mathcal{W}/W_0 \to \mathcal{W}/W'_0$ for the functor that maps $(W, \psi)$ to its pullback along $\chi$ (if $\mathcal{W}$ has pullbacks along $\chi$).

If $\chi = \pi_1 : W_0 \times U \to W_0$, we also write $\Sigma_U/\chi : \mathcal{W}/(W_0 \times U) \to \mathcal{W}/W_0$ and $\Omega_U/\chi : \mathcal{W}/W_0 \to \mathcal{W}/(W_0 \times U)$.

**Proposition 2.3.12.** If $\Omega/\chi$ exists, then $\Sigma/\chi \dashv \Omega/\chi$. We denote the unit as $\text{copy}/\chi : \text{Id} \to \Omega/\chi \Sigma/\chi$ and the co-unit as $\text{drop}/\chi : \Sigma/\chi \Omega/\chi \to \text{Id}$. $\square$

**Proposition 2.3.13** (Ultimately not used). 1. If $\chi$ is split epi, then $\Omega/\chi$ is faithful.

2. If $\chi$ is mono, then $\Sigma/\chi$ is full.$^6$

*Proof.* 1. We have some $v : W_0 \to W'_0$ such that $\chi \circ v = \text{id}$. Then the action of $\Omega/\chi$ on morphisms sending $\varphi \mapsto \varphi \times_{W_0} W'_0$ can be inverted: given $\varphi : (W_1, \psi_1) \to (W_2, \psi_2) \in \mathcal{W}/W_0$, we have

$$\varphi : W_1 \xrightarrow{(\text{id}, v \circ \psi_1)} W_1 \times_{W_0} W'_0 \xrightarrow{\varphi \times_{W_0} W'_0} W_2 \times_{W_0} W'_0 \xrightarrow{\pi_1} W_2. \tag{7}$$

2. Take a morphism $\varphi : (W_1, \chi \circ \psi_1) \to (W_2, \chi \circ \psi_2)$. Then $\chi \circ \psi_2 \circ \varphi = \chi \circ \psi_1$. Because $\chi$ is mono, this implies that $\psi_2 \circ \varphi = \psi_1$, i.e. $\varphi : (W_1, \psi_1) \to (W_2, \psi_2)$. $\square$

$^5$An earlier version asserted fullness of $\Omega_U$ instead, but proved the current theorem.
$^6$An earlier version asserted fullness of $\Omega/\chi$ instead, but proved the current theorem.

7