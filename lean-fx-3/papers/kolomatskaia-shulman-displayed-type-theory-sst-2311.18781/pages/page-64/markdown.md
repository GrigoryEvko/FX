These are defined such that:

$$\left( \gamma : \Gamma, a :^{\triangle_{n+2}} A \gamma \right)^D \equiv \left( \gamma^+ : \Gamma^D, a :^{\triangle_{n+1}} A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]} \gamma^+ \right)$$

$$\left( [\sigma, t]_{\triangle_{n+2}} \right)^D \equiv [\sigma^D, t^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}]_{\triangle_{n+1}}$$

For dimension $-1$, we define:

$$\left( \gamma : \Gamma, a :^{\triangle_{-1}} A \gamma \right)_{-1} \equiv \left( \gamma_{-1} : \Gamma_{-1}, a : A \gamma_{-1} \right)$$

$$\left( [\sigma, t]_{\triangle_{-1}} \right)_{-1} \equiv [\sigma_{-1}, t]$$

Then we inductively define:

$$\left( \gamma : \Gamma, a :^{\triangle_{n+2}} A \gamma \right)_{m+1} \equiv \left( \gamma^- : \pi \Gamma, a :^{\triangle_{n+1}} A \gamma^- \right)_{m+1} \quad \text{for} \quad m \leqslant n$$

$$\left( \gamma : \Gamma, a :^{\triangle_{n+2}} A \gamma \right)_{n+2} \equiv \left( \gamma^+ : \Gamma^D, a :^{\triangle_{n+1}} A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]} \gamma^+ \right)_{n+1}$$

$$\left( [\sigma, t]_{\triangle_{n+2}} \right)_{m+1} \equiv \left( [\pi \sigma, t]_{\triangle_{n+1}} \right)_{m+1} \quad \text{for} \quad m \leqslant n$$

$$\left( [\sigma, t]_{\triangle_{n+2}} \right)_{n+2} \equiv \left( [\sigma^D, t^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}]_{\triangle_{n+1}} \right)_{n+1}$$

We next have fundamental context projections and zero variables:

$$\frac{\gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}} \vdash_{dm} A \gamma \text{ type}_\ell}{\text{pt}_{\triangle_{n+1}}^A : \left( \gamma : \Gamma, a :^{\triangle_{n+1}} A \right) \rightarrow_{sm^{n+1}} \Gamma}$$

$$\frac{\gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}} \vdash_{dm} A \gamma \text{ type}_\ell}{\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}} \vdash_{dm} zv_{\triangle_{n+1}}^A \gamma a : A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]} \gamma a}$$

These are defined such that:

$$\left( \text{pt}_{\triangle_{n+2}}^A \right)^D \equiv \text{pt}_{\triangle_{n+1}}^{A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}}$$

For dimension $-1$, we define:

$$\left( \text{pt}_{\triangle_{-1}}^A \right)_{-1} \equiv \text{pt}_{dm}^A$$

$$zv_{\triangle_{-1}}^A \equiv zv_{dm}^A$$

Then we inductively define:

$$\pi \left( \text{pt}_{\triangle_{n+2}}^A \right) \equiv \text{pt}_{\triangle_{n+1}}^A$$

$$\left( \text{pt}_{\triangle_{n+2}}^A \right)_{n+2} \equiv \left( \text{pt}_{\triangle_{n+1}}^{A^{[p_\Gamma, \widehat{\mathbf{a}}_{\triangle_{n+1}}]}} \right)_{n+1}$$

$$zv_{\triangle_{n+2}}^A \equiv zv_{\triangle_{n+1}}^A$$

Finally, we construct modal $\Pi$-types:

$$\frac{\gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle} \vdash_{dm} A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma \vdash_{sm^{n+1}} B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash_{sm^{n+1}} \Pi_{\triangle}^{sm^{n+1}} A B \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma, a :^{\triangle_{n+1}} A \gamma \vdash_{sm^n} t \gamma a : B \gamma a}{\gamma : \Gamma \vdash_{sm} \lambda_{\triangle}^{sm^{n+1}} t \gamma : \Pi_{\triangle}^{sm^{n+1}} A B \gamma}$$

$$\frac{\gamma : \Gamma \vdash_{sm^n} f \gamma : \Pi_{\triangle}^{sm^n} A B \gamma \quad \gamma : \Gamma, \widehat{\mathbf{a}}_{\triangle} \vdash_{dm} s \gamma : A \gamma}{\gamma : \Gamma \vdash_{sm} \text{app}_{\triangle}^{sm^n} f s \gamma : B^{[1_\Gamma, s]_{\triangle}} \gamma}$$

64