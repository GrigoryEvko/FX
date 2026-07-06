This construction follows the pattern of the non-modal truncated case and is performed level-wise. We will inductively assert the following formulas for display:

$$\left( \Pi_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{A} \mathrm{B} \right)^{\mathrm{d}} \equiv \Pi_{\triangle}^{\mathrm{sm}^{n+1}} \left( \mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]} \right)^{\mathrm{pt}} \left( \mathrm{B}^{\mathrm{d}} \right)^{\left[ \mathrm{W}_{2}^{\mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]}} \mathrm{pt}, \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{zv}^{\mathrm{stop}} \mathrm{zv}_{\triangle}^{\mathrm{pt}} \right]}$$

$$\left( \lambda_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{t} \right)^{\mathrm{d}} \equiv \lambda_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{t}^{\mathrm{d}}$$

$$\left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{f} \mathrm{s} \right)^{\mathrm{d}} \equiv \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{f}^{\mathrm{d}} \mathrm{s}.$$

In dimension -1 we set:

$$\left( \Pi_{\triangle}^{\mathrm{sm}^{-1}} \mathrm{A} \mathrm{B} \right)_{-1} \equiv \Pi^{\mathrm{dm}} \mathrm{A} \mathrm{B}_{-1}$$

$$\left( \lambda_{\triangle}^{\mathrm{sm}^{-1}} \mathrm{t} \right)_{-1} \equiv \lambda^{\mathrm{dm}} \mathrm{t}_{-1}$$

$$\left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{-1}} \mathrm{f} \mathrm{s} \right)_{-1} \equiv \mathrm{app}^{\mathrm{dm}} \mathrm{f}_{-1} \mathrm{s}.$$

Then we inductively define:

$$\pi \left( \Pi_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{A} \mathrm{B} \right) \equiv \Pi_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{A} \pi \mathrm{B}$$

$$\left( \Pi_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{A} \mathrm{B} \right)_{n+2} \equiv \left( \Pi_{\triangle}^{\mathrm{sm}^{n+1}} \left( \mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]} \right)^{\mathrm{pt}} \left( \mathrm{B}^{\mathrm{d}} \right)^{\left[ \mathrm{W}_{2}^{\mathrm{A}^{\left[ \rho_{\Gamma}, \mathbf{\Theta}_{\triangle} \right]}} \mathrm{pt}, \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{zv}^{\mathrm{stop}} \mathrm{zv}_{\triangle}^{\mathrm{pt}} \right]} \right)_{n+1}$$

$$\pi \left( \lambda_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{t} \right) \equiv \lambda_{\triangle}^{\mathrm{sm}^{n+1}} \pi \mathrm{t}$$

$$\left( \lambda_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{t} \right)_{n+2} \equiv \lambda_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{t}^{\mathrm{d}}$$

$$\pi \left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{f} \mathrm{s} \right) \equiv \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \pi \mathrm{f} \mathrm{s}$$

$$\left( \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+2}} \mathrm{f} \mathrm{s} \right)_{n+2} \equiv \mathrm{app}_{\triangle}^{\mathrm{sm}^{n+1}} \mathrm{f}^{\mathrm{d}} \mathrm{s}.$$

The verification of many identities has been omitted.

Finally, we check that $\pi$ preserves all the operations defined above. Therefore, we can define the untruncated operations $\triangle$ and $\mathbf{\Theta}_{\triangle}$ on sm, with modal context extension $x :^{\triangle} \mathrm{A}$ and modal $\Pi$-types, simply by acting levelwise on each $\mathrm{sm}^{n+1}$.

### 4.3.2 Pieces of the Box Modality

The box modality is more subtle because it is not determined levelwise by operations on truncated diagrams. However, we can still construct it in terms of truncated data. We start with a truncated lock functor $\{-, \mathbf{\Theta}_{\square_n}\} : \mathcal{C} \to \mathcal{C}^{\Delta_n^*$ that constructs a constant simplicial diagram:

$$\left( \gamma : \Gamma, \mathbf{\Theta}_{\square_{n+1}} \right)_{m+1} \equiv \Gamma$$

$$\left( \gamma : \Gamma, \mathbf{\Theta}_{\square_{n+1}} \right)^{\mathrm{b}} \equiv 1_{\Gamma}$$

$$[\sigma, \mathbf{\Theta}_{\square_{n+1}}]_{m+1} \equiv \sigma.$$

We define the following four new pieces of syntax. The operation $\mathrm{A}_{\square(n+1)}$ is like a truncated version of $\square$, in that it takes the limit of a truncated diagram, but yielding a finite

65