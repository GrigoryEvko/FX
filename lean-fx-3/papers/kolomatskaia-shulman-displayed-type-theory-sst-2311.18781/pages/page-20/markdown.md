types (the primed variables in the above example). (The corresponding 'odds' substitution must wait until we introduce telescope display in section 2.6.3.)

$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \Upsilon \text{ tel}_\ell}{\Gamma \vdash_{sm} \Upsilon^D \text{ tel}_\ell} \quad \frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \Upsilon \text{ tel}_\ell \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \sigma : \Upsilon}{\Gamma \vdash_{sm} \sigma^D : \Upsilon^D}$$
$$\frac{\Gamma \vdash_{sm} \sigma^+ : \Upsilon^D}{\Gamma \vdash_{sm} \sigma^{+ev} : \Upsilon [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ]} \quad \sigma^{D \text{ ev}} \equiv \sigma [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ]$$

Notationally, we put a superscript '+' on variables and metavariables belonging to décalaged telescopes, and a prime on variables belonging to displayed types and telescopes. These symbols are part of the variable name, e.g. $\sigma^+$ above is a single variable that just happens to be named mnemonically.

At this point we can assert that décalage preserves empty telescopes.

$$()_{sm}^D \equiv ()_{sm} \quad [ ]_{sm}^D \equiv [ ]_{sm} \quad [ ]_{sm}^{ev} \equiv [ ]_{sm}$$

Décalage will also compute on telescopes extended by a type, but we wait to give these rules in section 2.4.4, since they require more structure.

### 2.4.3 Display for meta-abstractions

The more general version of display alluded to above can informally be thought of as having the following rule:

$$\mathcal{L} \quad \frac{\Gamma, \text{ \textpermil}_{\Delta\square} | \Upsilon \vdash_{sm} A \text{ type}_\ell}{\Gamma | \Upsilon^D, a : A \vdash_{sm} A^d a \text{ type}_\ell} \quad ?$$

However, this is not a well-behaved rule because the context of the conclusion is not fully general. There are multiple ways to solve this problem; we will solve it by saying that general display acts on a meta-abstracted type.

$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon}{\Gamma \vdash_{sm} A^d \text{ type}_{\ell_1} / v^+ : \Upsilon^D, a : A [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ] v^{+ev}}$$
$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} t : A}{\Gamma \vdash_{sm} t^d : \left( \left( A^d v^+ (t v^{+ev}) \right) \right)_{v^+ : \Upsilon^D}}$$

In general, this does not reduce to ordinary display, but it does when applied to a décalaged partial substitution.

$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \sigma : \Upsilon \quad \Gamma \vdash t : (A \sigma) [ \text{ \textpermil}_{\text{ev}}^{\Delta\square \leqslant 1_{sm}} ]}{\Gamma \vdash A^d \sigma^D t \equiv (A \sigma)^d t}$$
$$\frac{\Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} A \text{ type}_{\ell_1} / v : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} \sigma : \Upsilon \quad \Gamma, \text{ \textpermil}_{\Delta\square} \vdash_{sm} t : A}{\Gamma \vdash t^d \sigma^D \equiv (t \sigma)^d}$$

In particular, when $\Upsilon \equiv ()_{sm}$ these rules say that display for trivial meta-abstractions is equivalent to ordinary display.

20