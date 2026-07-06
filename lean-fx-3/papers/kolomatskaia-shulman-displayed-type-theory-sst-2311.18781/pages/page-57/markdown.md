and the context in which $A_{n+2}$ lives expands to this by the definition of matching telescopes:

$$\gamma_{n+2} : \Gamma_{n+2}, \ \partial a : \pi A_{\partial(n+2)} \ \gamma_{n+2} \vdash_{dm} A_{n+2} \ \gamma_{n+2} \ \partial a \ \text{type}_\ell.$$

We can now check (4.9) at the level of $n + 1$ simplices:

$$\begin{aligned} & \left( (\gamma : \Gamma, \ a : A \ \gamma)^D \right)_{n+1} \\ & \quad \equiv (\gamma : \Gamma, \ a : A \ \gamma)_{n+2} \\ & \quad \equiv (\gamma_{n+2} : \Gamma_{n+2}, \ \partial a : \pi A_{\partial(n+2)} \ \gamma_{n+2}, \ a : A_{n+2} \ \gamma_{n+2} \ \partial a) \\ & \quad \equiv (\gamma_{n+2} : \Gamma_{n+2}, \ \partial a : (\pi \pi A^{p_{\pi\Gamma}})_{\partial(n+1)} \ \gamma_{n+2}, \ a : (\pi A^{p_\Gamma})_{n+1} \ \gamma_{n+2} \ \partial a, \\ & \qquad \qquad \partial a' : (\pi A^d)_{\partial(n+1)} \ [ \gamma_{n+2}, \ \partial a, \ a \ ], \ a' : (A^d)_{n+1} \ [ \gamma_{n+2}, \ \partial a, \ a \ ] \ \partial a') \\ & \quad \equiv (\gamma^+ : \Gamma^D, \ a : \pi A^{p_\Gamma} \ \gamma^+, \ a' : A^d \ \gamma^+ \ a)_{n+1}, \end{aligned}$$

where (4.10) follows similarly. Stability under substitutions follows inductively:

$$\begin{aligned} \pi \Big( (A^\sigma)^d \Big)_{n+1} & \equiv (\pi A^{\pi\sigma})^d \\ & \equiv (\pi A^d)^{W_2^{\pi A^p \pi \Gamma} \pi \sigma^D} \\ & \equiv (\pi A^d)^{\pi W_2^{\pi A^p \Gamma} \sigma^D} \\ & \equiv \pi \Big( (A^d)^{W_2^{\pi A^p \Gamma} \sigma^D} \Big) \\ \Big( (A^\sigma)^d \Big)_{n+1} & \equiv (A^\sigma)_{n+2} \\ & \equiv A_{n+2}^{W_2^{\pi A_{\partial(n+2)}} \sigma_{n+2}} \\ & \equiv A_{n+2}^{W_2^{(\pi A^d)_{\partial(n+1)}} W_2^{(\pi A^p \Gamma)_{n+1}} W_2^{(\pi \pi A^p \pi \Gamma)_{\partial(n+1)}} \sigma_{n+2}} \\ & \equiv \Big( (A^d)_{n+1} \Big)^{W_2^{(\pi A^d)_{\partial(n+1)}} \left( W_2^{\pi A^p \Gamma} \sigma^D \right)_{n+1}} \\ & \equiv \Big( (A^d)^{W_2^{\pi A^p \Gamma} \sigma^D} \Big)_{n+1}. \end{aligned}$$

Lastly, we define the components of the functorial action on presheaves as follows:

$$\text{act}_{\partial(\mathbb{0}b)}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \equiv \text{act}_{\partial b}^{\pi A^{p_{\pi\Gamma}}} \ \gamma_{n+2} \ \partial a$$

$$\text{act}_{\mathbb{0}b}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \ a' \equiv \text{act}_b^{\pi A^{p_\Gamma}} \ \gamma_{n+2} \ \partial a \ a$$

$$\text{act}_{\partial(\mathbb{1}b)}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \equiv$$

$$[ \text{act}_{\partial b}^{\pi A^{p_{\pi\Gamma}}} \ \gamma_{n+2} \ \partial a, \ \text{act}_b^{A^{p_\Gamma}} \ \gamma_{n+2} \ \partial a \ a, \ \text{act}_{\partial b}^{A^d} \ [ \gamma_{n+2}, \ \partial a, \ a \ ] \ \partial a' ]$$

$$\text{act}_{\mathbb{1}b}^A \ \gamma_{n+2} \ [ \partial a, \ a, \ \partial a' ] \ a' \equiv \text{act}_b^{A^d} \ [ \gamma_{n+2}, \ \partial a, \ a \ ] \ \partial a' \ a',$$

57