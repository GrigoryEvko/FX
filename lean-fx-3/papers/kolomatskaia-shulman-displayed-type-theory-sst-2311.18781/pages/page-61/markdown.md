used to define each successive level. The correctness of these definitions will follow from verifying that Code and El are mutual inverses in appendix A.3.

### 4.2.8 ω-Limits

If ω-limits are defined in smⁿ, then given an infinite telescope γ : Γ ⊢ₛₘⁿ⁺¹ Ϡ γ stelℓ∞ or infinite partial substitution γ : Γ ⊢ₛₘⁿ⁺¹ ϋ γ : Ϡ γ in smⁿ, we can meaningfully give a type declaration of its display through use of limits:

$$\frac{\gamma : \Gamma \vdash_{\text{sm}^{n+1}} \bar{\Upsilon} \gamma \text{stel}_{\ell}^{\infty}}{\gamma^{+} : \Gamma^{\text{D}}, u : \lim_{\text{sm}^{n}} \pi \bar{\Upsilon}^{\text{pr}} \gamma^{+} \vdash_{\text{sm}^{n}} \bar{\Upsilon}^{\text{d}} \gamma^{+} u \text{stel}_{\ell}^{\infty}}$$

$$\frac{\gamma : \Gamma \vdash_{\text{sm}^{n+1}} \bar{\upsilon} \gamma : \bar{\Upsilon} \gamma \text{stel}_{\ell}^{\infty}}{\gamma^{+} : \Gamma^{\text{D}} \vdash_{\text{sm}^{n}} \bar{\upsilon}^{\text{d}} \gamma^{+} : \bar{\Upsilon}^{\text{d}} \gamma^{+} \left( \lim_{\text{sm}^{n}} \pi \bar{\upsilon}^{\text{pr}} \right)}$$

We then define these by:

$$\begin{array}{l} \left(\bar{\Upsilon}^{\text{d}} \gamma^{+} u\right)^{\partial m} \equiv \left(\bar{\Upsilon}^{\partial m}\right)^{\text{d}} \gamma^{+} \left(\text{res}_{\text{sm}^{n}}^{\partial m} \gamma^{+} u\right) \\ \left(\bar{\Upsilon}^{\text{d}} \gamma^{+} u\right)^{m} \equiv \left(\bar{\Upsilon}^{m}\right)^{\text{d}} \gamma^{+} \left(\text{res}_{\text{sm}^{n}}^{m} \gamma^{+} u\right) \\ \left(\bar{\upsilon}^{\text{d}}\right)^{\partial m} \equiv \left(\bar{\upsilon}^{\partial m}\right)^{\text{d}} \\ \left(\bar{\upsilon}^{\text{d}}\right)^{m} \equiv \left(\bar{\upsilon}^{m}\right)^{\text{d}}. \end{array}$$

The third declaration, for example, is well typed because its expected type is:

$$\begin{array}{l} \left(\bar{\Upsilon}^{\text{d}} \gamma^{+} \left(\lim_{\text{sm}^{n}} \pi \bar{\upsilon}^{\text{pr}}\right)\right)^{\partial m} \\ \equiv \left(\bar{\Upsilon}^{\partial m}\right)^{\text{d}} \gamma^{+} \left(\text{res}_{\text{sm}^{n}}^{\partial m} \gamma^{+} \left(\lim_{\text{sm}^{n}} \pi \bar{\upsilon}^{\text{pr}}\right)\right) \\ \equiv \left(\bar{\Upsilon}^{\partial m}\right)^{\text{d}} \gamma^{+} \left(\pi \left(\bar{\upsilon}^{\partial m}\right)^{\text{pr}}\right). \end{array}$$

We now construct ω-limits in smⁿ inductively, with all of the assumptions of a ω-structure outlined before assumed at all prior levels. This construction will be performed such that the following theorems hold inductively:

$$\begin{array}{l} \left(\lim_{\text{sm}^{n+1}} \bar{\Upsilon}\right)^{\text{d}} \equiv \lim_{\text{sm}^{n}} \bar{\Upsilon}^{\text{d}} \quad (4.25) \\ \left(\lim_{\text{sm}^{n+1}} \bar{\upsilon}\right)^{\text{d}} \equiv \lim_{\text{sm}^{n}} \bar{\upsilon}^{\text{d}} \quad (4.26) \\ \left(\text{res}_{\text{sm}^{n+1}}^{\partial m} u\right)^{\text{d}} \equiv \text{res}_{\text{sm}^{n}}^{\partial m} u^{\text{d}} \quad (4.27) \\ \left(\text{res}_{\text{sm}^{n+1}}^{m} u\right)^{\text{d}} \equiv \text{res}_{\text{sm}^{n}}^{m} u^{\text{d}}. \quad (4.28) \end{array}$$

For sm⁻¹, we define:

$$\begin{array}{l} \left(\lim_{\text{sm}^{-1}} \bar{\Upsilon}\right)_{-1} \equiv \lim_{\text{dm}} \bar{\Upsilon}_{-1} \\ \left(\lim_{\text{sm}^{-1}} \bar{\upsilon}\right)_{-1} \equiv \lim_{\text{dm}} \bar{\upsilon}_{-1} \\ \left(\text{res}_{\text{sm}^{-1}}^{\partial m} u\right)_{-1} \equiv \text{res}_{\text{dm}}^{\partial m} u_{-1} \\ \left(\text{res}_{\text{sm}^{-1}}^{m} u\right)_{-1} \equiv \text{res}_{\text{dm}}^{m} u_{-1}. \end{array}$$

61