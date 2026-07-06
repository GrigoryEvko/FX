Proof. We have the axiom

$$\{x_\alpha : \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{f^* B_\mu}(x_\alpha)_{\alpha<\lambda} \equiv \overline{B_\mu}(\overline{p_\beta \circ f}(x_\alpha)_{\alpha<\lambda})_{\beta<\mu}$$

for $U(\mathcal{C})$ and the derivation rule for $\kappa$-GAT

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad t : A_1}{\Gamma \vdash t : A_2}.$$

These put together give us the result.

Lemma B.19. Let $\mathcal{C}$ a $\kappa$-contextual category, objects $\{A_\alpha\}_{\alpha<\lambda}$, $\{B_\beta\}_{\beta<\mu+1}$, $\{C_\gamma\}_{\gamma<\varepsilon}$ and a commutative diagram

$$\begin{array}{c} C_\varepsilon \xrightarrow{\ell} B_{\mu+1} \\ k \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A_\lambda \xrightarrow{\quad f\quad} B_\mu. \end{array}$$

If $h : C_\varepsilon \to f^* B_{\mu+1}$ is the unique map given by the pullback, then the rule

$$\{x_\gamma : \overline{C_\gamma}(x_\delta)_{\delta<\gamma}\}_{\gamma<\varepsilon} \vdash \overline{h}(x_\gamma)_{\gamma<\varepsilon} \equiv \overline{(fk)^* B_{\mu+1}(x_\gamma)_{\gamma<\varepsilon}} \, \overline{l}(x_\gamma)_{\gamma<\varepsilon}$$

is a derived rule of $U(\mathcal{C})$.

Proof. The proof is the same as [Car78, Lemma 2 pp. 2.32] using theorem B.18.

Lemma B.20. Let $\mathcal{C}$ a $\kappa$-contextual category, objects $\{A_\alpha\}_{\alpha<\lambda}$, $\{B_\beta\}_{\beta<\mu}$, $\{C_\gamma\}_{\gamma<\varepsilon}$ and for $0 < \nu < \mu$ a commutative diagram

$$\begin{array}{c} C_\varepsilon \xrightarrow{\iota_\nu} B_\mu \\ k_\nu \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A_\lambda \xrightarrow{\quad f\quad} B_\nu. \end{array}$$

If $h_\nu : C_\varepsilon \to f^* B_\mu$ is the unique map given by the pullback, then the rule

$$\{x_\gamma : \overline{C_\gamma}(x_\delta)_{\delta<\gamma}\}_{\gamma<\varepsilon} \vdash \overline{h_\nu}(x_\gamma)_{\gamma<\varepsilon} \equiv \overline{(fk_\nu)^* B_\mu(x_\gamma)_{\gamma<\varepsilon}} \, \overline{l_\nu}(x_\gamma)_{\gamma<\varepsilon}$$

is a derived rule of $U(\mathcal{C})$.

121