where the last definition is well typed because $\left(A^{d}\right)_{n+1} \equiv A_{n+2}$. We check functoriality:

$$\begin{array}{l} \operatorname{act}_{\partial b_{0}}^{\pi^{(n+1)-m}A}\left(\Gamma^{\otimes b_{1}} \gamma_{n+2}\right)\left(\operatorname{act}_{\partial\left(\emptyset b_{1}\right)}^{A} \gamma_{n+2}\left[\partial a, a, \partial a^{\prime}\right]\right) \\ \quad \equiv \operatorname{act}_{\partial b_{0}}^{\pi^{n-m} \pi A}\left(\left(\rho_{\Gamma}\right)_{m+1}\left(\left(\Gamma^{D}\right)^{b_{1}} \gamma_{n+2}\right)\right)\left(\operatorname{act}_{\partial\left(\emptyset b_{1}\right)}^{A} \gamma_{n+2} \partial a\right) \\ \quad \equiv \operatorname{act}_{\partial b_{0}}^{\pi^{n-m} \pi A^{\rho_{\pi \Gamma}}}\left(\left(\Gamma^{D}\right)^{b_{1}} \gamma_{n+2}\right)\left(\operatorname{act}_{\partial b_{1}}^{\pi A^{\rho_{\pi \Gamma}}} \gamma_{n+2} \partial a\right) \\ \quad \equiv \operatorname{act}_{\partial\left(b_{1} \circ b_{0}\right)}^{\pi A^{\rho_{\pi \Gamma}}} \gamma_{n+2} \partial a \\ \quad \equiv \operatorname{act}_{\partial\left(\emptyset b_{1} \circ b_{0}\right)}^{A} \gamma_{n+2}\left[\partial a, a, \partial a^{\prime}\right] \end{array}$$

and stability under substitutions:

$$\begin{array}{l} \operatorname{act}_{\partial\left(\emptyset b\right)}^{A^{\pi \sigma}} \delta_{n+2}\left[\partial a, a, \partial a^{\prime}\right] \equiv \operatorname{act}_{\partial b}^{\pi A^{\pi \pi \sigma \circ \rho_{\pi A}}} \delta_{n+2} \partial a \\ \quad \equiv \operatorname{act}_{\partial b}^{\pi A^{\rho_{\pi \Gamma} \circ \pi \sigma^{D}}} \delta_{n+2} \partial a \\ \quad \equiv \operatorname{act}_{\partial b}^{\pi A^{\rho_{\pi \Gamma}}}\left(\sigma_{n+1}^{D} \delta_{n+2}\right) \partial a \\ \quad \equiv \operatorname{act}_{\partial\left(\emptyset b\right)}^{A}\left(\sigma_{n+2} \delta_{n+2}\right)\left[\partial a, a, \partial a^{\prime}\right]. \end{array}$$

All omitted verifications are similar to the cases presented. This completes the construction of the type and term presheaves and their context extension function, plus display, for the truncated simplicial models $\mathbf{sm}^{n}$.

### 4.2.5 Variables

To make the models $\mathbf{sm}^{n}$ into CwFs, what is missing from the above construction are the fundamental context projections and variables. In this section we will now define these:

$$\frac{\gamma : \Gamma \vdash_{\mathbf{sm}^{n}} A \gamma \operatorname{type}_{\ell}}{\operatorname{pt}_{\mathbf{sm}^{n}}^{A} : (\gamma : \Gamma, a : A \gamma) \rightarrow \Gamma} \quad \frac{\gamma : \Gamma \vdash_{\mathbf{sm}^{n}} A \gamma \operatorname{type}_{\ell}}{\gamma : \Gamma, a : A \gamma \vdash_{\mathbf{sm}^{n}} z v_{\mathbf{sm}^{n}}^{A} \gamma a : A^{\operatorname{pt}} \gamma a}.$$

We now construct variables and parent maps in $\mathbf{sm}^{n}$ inductively, with all of the hypothesise eqs. (4.2) to (4.4) outlined before assumed at all prior levels. This construction will be performed such that the following theorems hold inductively:

$$\left(\operatorname{pt}_{\mathbf{sm}^{n+1}}^{A}\right)^{D} \equiv \operatorname{pt}_{\mathbf{sm}^{n}}^{\pi A^{\rho_{\Gamma}}} \circ \operatorname{pt}_{\mathbf{sm}^{n}}^{A^{d}} \tag{4.16}$$

$$\left(z v_{\mathbf{sm}^{n+1}}^{A}\right)^{d} \equiv z v_{\mathbf{sm}^{n}}^{A^{d}} \tag{4.17}$$

$$\left(z v_{\mathbf{sm}^{n}}^{\pi A}\right)^{\rho_{\left(\Gamma, A\right)}} \equiv \left(z v_{\mathbf{sm}^{n}}^{\pi A^{\rho_{\Gamma}}}\right)^{\operatorname{pt}_{\mathbf{sm}^{n}}^{A^{d}}}. \tag{4.18}$$

Note that the above equations are well typed by way of the formulas for décalage given in the fibrant construction above. Now for $\mathbf{sm}^{-1}$, we define:

$$\left(\operatorname{pt}_{\mathbf{sm}^{-1}}^{A}\right)_{-1} \equiv \operatorname{pt}_{\mathbf{dm}}^{A-1}$$

$$\left(z v_{\mathbf{sm}^{-1}}^{A}\right)_{-1} \equiv z v_{\mathbf{dm}}^{A-1}.$$

58