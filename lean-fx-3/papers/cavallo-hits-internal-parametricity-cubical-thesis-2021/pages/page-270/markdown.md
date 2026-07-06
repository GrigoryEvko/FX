258

Cohesive parametric type theory

Example 14.4.3 (Small type system). We define an operator Mo on candidate type systems as follows: given $\tau$, $Mo(\tau)$ is the union of the following clauses.

- $Mo(\tau) \models \Psi \Vdash \langle \mu \mid A \rangle \approx \langle \mu \mid A' \rangle \downarrow R @ n$ for $\mu : m \to n$ with $\mu \in \{\text{dsc}, \text{glo}\}$ whenever

- $A \approx A' \in \Downarrow \tau[S]$ for some $\Psi.\mu$-PER $S$,
- $R = Mod_{\mu}(S)$.

- $Mo(\tau) \models \Psi \Vdash \langle \text{cc} \mid A \rangle \approx \langle \text{cc} \mid A' \rangle \downarrow R @ \text{par}$ whenever

- $A \approx A' \in \Downarrow \tau[S]$ for some $\Psi.\text{cc}$-PER $S$,
- $R$ is the least fixed-point of the operator $R \mapsto Mod_{\text{cc}}(R) \cup Fhcom(R)$.

We define the candidate type system $\tau_0^{Mo}$ to be the least fixed point of the following operator, where $F, H, IP$ are as defined in Examples 3.1.32, 6.2.22 and 9.1.13 respectively.

$$\tau \mapsto \left( \bigcup_{m \in \{\text{pt}, \text{par}\}} F(\tau_m) \right) \cup \left( \bigcup_{m \in \{\text{pt}, \text{par}\}} H(\tau_m) \right) \cup IP(\tau_{\text{par}}) \cup Mo(\tau)$$

That is, we include the basic cubical ($F$) and higher inductive ($H$) type formers in both the pointwise and parametric modes, but restrict the Bridge and Gel types ($IP$) to the parametric mode.

We can construct a larger type system $\tau_1^{Mo}$ closed under these type formers and containing $\tau_0^{Mo}$ as a universe in the usual fashion. We henceforth assume we are working in such a type system.

For the first couple of rules—pretype formation and mod introduction—we can treat the three modal types uniformly.

Rule 14.4.4 (Pretype formation). The following rule is validated for $\mu \in \{\text{cc}, \text{dsc}, \text{glo}\}$ with $\mu : m \to n$.

$$\frac{\Psi.\mu \gg A = A' \text{ type } @ m}{\Psi \Vdash \langle \mu \mid A \rangle = \langle \mu \mid A' \rangle \text{ pretype } @ n}$$

Proof. Immediate by coherent value introduction. We use the action of $\mu$ on substitutions: for any $\Psi' \Vdash \psi \in \Psi @ n$, we have $\Psi'.\mu \gg (\psi : \Psi) \otimes \mu \in \Psi @ m$, thus $\Psi'.\mu \gg A\psi = A'\psi$ type $@ m$ and therefore $\tau_0^{Mo} \models \Psi' \Vdash \langle \mu \mid A\psi \rangle \approx \langle \mu \mid A'\psi \rangle \downarrow R @ n$ for the appropriate $R$. $\square$

Rule 14.4.5 (Introduction). The following rule is validated for $\mu \in \{\text{cc}, \text{dsc}, \text{glo}\}$ with $\mu : m \to n$.

$$\frac{\Psi.\mu \gg M = M' \in A @ m}{\Psi \Vdash \text{mod}(M) = \text{mod}(M') \in \langle \mu \mid A \rangle @ n}$$