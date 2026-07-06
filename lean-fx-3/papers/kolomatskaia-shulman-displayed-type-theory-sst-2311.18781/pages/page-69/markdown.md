Note that in the last case, if we have $\text{in}_{\text{fl}} \sigma : \text{in}_{\text{dm}} \Delta \to \text{in}_{\text{sm}} \Gamma$ then $\sigma : \Delta \to \Gamma_{-1}$. In order to form the extension $[\text{in}_{\text{fl}} \sigma, s] : \text{in}_{\text{dm}} \Delta \to \text{in}_{\text{sm}} (\gamma : \Gamma, a : A \gamma)$, we must give $\delta : \text{in}_{\text{dm}} \Delta \vdash_{\text{sm}_+} s \delta : (\text{in}_{\text{sm}} A)^{\text{in}_{\text{fl}} \sigma} \delta$. We see then that such an $s$ has type $\text{in}_{\text{dm}} (A_{-1})^\sigma$ and must be of the form $\text{in}_{\text{dm}} t$.

4.3.3.3 $\Pi$-Types and Universes. We define (non-modal) $\Pi$-types and universes in $\text{sm}_+$ by reducing to the respective constructs in $\text{dm}$ and $\text{sm}$, depending on whether or not the context is flat:

$$\begin{array}{l} \Pi^{\text{sm}_+} (\text{in}_{\text{dm}} A) (\text{in}_{\text{dm}} B) \equiv \text{in}_{\text{dm}} (\Pi^{\text{dm}} A B) \\ \Pi^{\text{sm}_+} (\text{in}_{\text{sm}} A) (\text{in}_{\text{sm}} B) \equiv \text{in}_{\text{sm}} (\Pi^{\text{sm}} A B) \\ \text{Type}_{\ell}^{\text{sm}_+} \equiv \begin{cases} \text{in}_{\text{dm}} \text{Disc}_{\ell} & \text{for} \quad \text{in}_{\text{dm}} \Gamma \\ \text{in}_{\text{sm}} \text{Type}_{\ell}^{\text{sm}} & \text{for} \quad \text{in}_{\text{sm}} \Gamma. \end{cases} \end{array}$$

The definitions of $\lambda^{\text{sm}_+}$, $\text{app}^{\text{sm}_+}$, $\text{Code}^{\text{sm}_+}$, and $\text{EI}^{\text{sm}_+}$ are similar.

Note that stability under substitution is a more general property in $\text{sm}_+$ since we have to additionally consider flat substitutions; if $\text{in}_{\text{fl}} \sigma : \text{in}_{\text{dm}} \Delta \to \text{in}_{\text{sm}} \Gamma$, then we have:

$$\begin{array}{l} \left(\Pi^{\text{sm}_+} (\text{in}_{\text{sm}} A) (\text{in}_{\text{sm}} B)\right)^{\text{in}_{\text{fl}} \sigma} \\ \equiv \left(\text{in}_{\text{sm}} (\Pi^{\text{sm}} A B)\right)^{\text{in}_{\text{fl}} \sigma} \\ \equiv \text{in}_{\text{dm}} \left((\Pi^{\text{sm}} A B)_{-1}\right)^\sigma \\ \equiv \text{in}_{\text{dm}} \left(\Pi^{\text{dm}} A_{-1} B_{-1}\right)^\sigma \\ \equiv \text{in}_{\text{dm}} \left(\Pi^{\text{dm}} (A_{-1})^\sigma (B_{-1})^{W_2^{A_{-1}} \sigma}\right) \\ \equiv \Pi^{\text{sm}_+} (\text{in}_{\text{dm}} (A_{-1})^\sigma) (\text{in}_{\text{dm}} (B_{-1})^{W_2^{A_{-1}} \sigma}) \\ \equiv \Pi^{\text{sm}_+} (\text{in}_{\text{sm}} A)^{\text{in}_{\text{fl}} \sigma} (\text{in}_{\text{sm}} B)^{W_2^A (\text{in}_{\text{fl}} \sigma)} \end{array}$$

Similarly for universes:

$$\begin{array}{l} \left(\text{Type}_{\ell}^{\text{sm}_+}\right)^{\text{in}_{\text{fl}} \sigma} \equiv \left(\text{in}_{\text{sm}} \text{Type}_{\ell}^{\text{sm}}\right)^{\text{in}_{\text{fl}} \sigma} \\ \equiv \text{in}_{\text{dm}} \left((\text{Type}_{\ell}^{\text{sm}})_{-1}\right)^\sigma \\ \equiv \text{in}_{\text{dm}} \text{Disc}_{\ell}^\sigma \\ \equiv \text{in}_{\text{dm}} \text{Disc}_{\ell} \\ \equiv \text{Type}_{\ell}^{\text{sm}_+} \end{array}$$

What makes these calculations work is the relevant constructs have been defined to agree with their discrete counterparts in dimension -1. In the rest of this section, we show how $\text{dm}$ and $\text{sm}^+$ can be made into a model of all of dTT (except for the type-former $\triangle$).

69