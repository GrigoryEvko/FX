This comes with the following computation rules:

$$\text{head } (\phi \upsilon) \left( \text{corec}_{[\Phi, A, \mathcal{B}, \sigma]} [\Upsilon, \phi, \bar{h}, \bar{\tau}] \upsilon \right) \equiv \bar{h} \upsilon$$

$$\text{tail } (\phi \upsilon) \left( \text{corec}_{[\Phi, A, \mathcal{B}, \sigma]} [\Upsilon, \phi, \bar{h}, \bar{\tau}] \upsilon \right) \mathfrak{b} \equiv \left( \text{corec}_{[\Phi, A, \mathcal{B}, \sigma]} [\Upsilon, \phi, \bar{h}, \bar{\tau}] \right)^d \langle \upsilon, \bar{\tau} \upsilon \mathfrak{b} \rangle$$

Now we can define SST as a particular instance of an indexed displayed coinductive type (which happens to have trivial indexing). In fact, it is in some sense the universal such instance, where the family $\mathcal{B}$ indexed by $A$ is the universal family $\mathcal{EI}$ indexed by $\text{Type}_\ell$. This may be compared with the fact that the $W$-type of $\mathcal{EI}$ is the type of 'presentations of well-founded sets' [Acz78], while its $M$-type is the type of 'presentations of ill-founded sets' [Lin89].

$$\text{SST}_\ell \equiv \text{dCoind} \left[ ()_{\text{sm}}, ((\text{Type}_\ell))_{\varphi:()_{\text{sm}}}, ((\text{EI X}))_{X:\text{Type}_\ell}, [\![\!]_{\text{sm}}]\!]_{X:\text{Type}_\ell, x:\text{EI X}} \right]$$

This is the end of all the primitive rules and definitions we have to give. From here, we can deduce the rules for $\text{SST}_\ell$, defining $Z \equiv \text{head}$ and $S \equiv \text{tail}$ and $R \equiv \text{corec}$:

$$\overline{\Gamma \vdash_{\text{sm}} Z : ((\text{Type}_\ell))_{X:\text{SST}_\ell}} \quad \overline{\Gamma \vdash_{\text{sm}} S : ((\text{SST}_\ell^d X))_{X:\text{SST}_\ell, x:\text{EI}(Z X)}}$$

$$\frac{\Gamma, \widehat{\bullet}_{\Delta\square} \vdash_{\text{sm}} \Upsilon \text{tel}_{\ell'}}{\Gamma, \widehat{\bullet}_{\Delta\square} \vdash_{\text{sm}} \bar{Z} : ((\text{Type}_\ell))_{\upsilon:\Upsilon} \quad \Gamma, \widehat{\bullet}_{\Delta\square} \vdash_{\text{sm}} \bar{S} : ((\Upsilon^d \upsilon))_{\upsilon:\Upsilon, x:\text{EI}(\bar{Z}\upsilon)}}{\Gamma \vdash_{\text{sm}} R_\Upsilon \bar{Z} \bar{S} : ((\text{SST}_\ell))_{\upsilon:\Upsilon}}$$

The problem of giving a corecursion rule for $\text{SST}^d$ carries over to the general case in the following way. Just as $^d$ of a $\Pi$-type is another $\Pi$-type and so on for records and ordinary coinductive types, We'd like to compute $^d$ of a dCoind to be another dCoind, with something like the following:

$$\begin{array}{l} \text{dCoind}_{[\Phi, A, \mathcal{B}, \sigma]^d} \equiv \text{dCoind} \left[ (\varphi^+: \Phi^D, c: \text{dCoind}_{[\Phi, A, \mathcal{B}, \sigma]} \varphi^{+\text{ev}}), \right. \\ \left. \left( (A^d \varphi^+ (\text{head } c))_{\varphi^+, c}, ((\mathcal{B}^D \varphi^+ (\text{head } c) a'))_{\varphi^+, x, a'}, \right. \right. \\ \left. \left[ \sigma^D \varphi^+ [\text{head } c, a'] \mathfrak{b}^+, \text{tail } c \mathfrak{b}^{+\text{ev}} \right]_{\varphi^+, c, a', \mathfrak{b}^+} \right] \end{array}$$

To see whether this is well-typed, observe that we have

$$\begin{array}{l} \varphi: \Phi, a: A \varphi, \mathfrak{b}: \mathcal{B} \varphi a \vdash_{\text{sm}} \sigma \varphi a \mathfrak{b}: \Phi^d \varphi \\ \varphi^+: \Phi^D, a: A, a': A^d a, \mathfrak{b}^+: \mathcal{B}^D \varphi^+ [a, a'] \vdash_{\text{sm}} \sigma^D \varphi^+ [a, a'] \mathfrak{b}^+: \Phi^{dD} \varphi^+ \end{array}$$

whereas the $\sigma$ of the resulting dCoind must lie in $(\varphi^+: \Phi^D, c: \text{dCoind}_{[\Phi, A, \mathcal{B}, \sigma]} \varphi^{+\text{ev}})^d$. Thus, in particular, we need to compare $\Phi^{dD} \varphi^+$ to $\Phi^{Dd} \varphi^+$, where $\varphi^+: \Phi^D$. In the case of a one-type telescope $\Phi = (a: A)$, this becomes

$$\begin{array}{l} \Phi^D \equiv (a: A, a': A^d a) \\ \Phi^d a \equiv (a': A^d a) \\ \Phi^{dD} [a, a'] \equiv (a'': A^d a, a''': A^{dd} a a' a'') \\ \Phi^{Dd} [a, a'] \equiv (a'': A^d a, a''': A^{dd} a a'' a') \end{array}$$

37