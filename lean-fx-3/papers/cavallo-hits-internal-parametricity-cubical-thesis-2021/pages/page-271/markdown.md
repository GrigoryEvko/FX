Modal types

259

Proof. By coherent value introduction, following the proof of pretype formation.

□

For the remainder of the rules—elimination, reduction and uniqueness equations, and the Kan operations—we must handle $\langle \mu \mid A \rangle$ for $\mu = \mathrm{dsc}$ separately from the two right adjoints dsc and glo.

### 14.4.1 Right adjoint modalities

The type formers Glo and Codisc do not only have left adjoint context operators; those left adjoints are themselves right adjoints, to cc and dsc respectively. This enables a negative treatment of Glo and Codisc, that is, one characterized by a projection operator and uniqueness principle rather than an induction principle. An analogous situation appears in Shulman's cohesive type theory: his $\sharp$ operator, which corresponds to the composite Codisc(Glo(−)), is axiomatized negatively. We treat the two type formers uniformly by introducing the following shorthand.

Definition 14.4.6. Given $\mu \in \{\mathrm{dsc}, \mathrm{glo}\}$, define ${}^4\mu$ as follows.

$${}^4\mathrm{dsc} := \mathrm{cc}$$

$${}^4\mathrm{glo} := \mathrm{dsc}$$

Note that ${}^4\mu = \mathrm{id} \div \mu$, where division is as specified in Definition 14.3.4.

In the following, it may be useful to notice the similarity to bridge types: if we think of the context operator $-.\mu$ as analogous to $x:\mathbf{I}$, then $-.{}^4\mu$ corresponds to interval restriction. Modulo the absence of endpoint constraints in the type and the binding of an interval variable, the projection rules for bridge and negative modal types then match exactly.

Rules 14.4.7 (Projection). The following rules are validated for any $\mu \in \{\mathrm{dsc}, \mathrm{glo}\}$ with $\mu : m \to n$.

$$\frac{\Psi.{}^4\mu.\mu \gg A \text{ type } @ m \quad \Psi.{}^4\mu \gg P = P' \in \langle \mu \mid A \rangle @ n}{\Psi \Vdash \operatorname{unmod}(P) = \operatorname{unmod}(P') \in A @ m}$$

$$\frac{\Psi.{}^4\mu.\mu \gg A \text{ type } @ m \quad \Psi.{}^4\mu.\mu \gg M \in A @ m}{\Psi \Vdash \operatorname{unmod}(\operatorname{mod}(M)) = M \in A @ m}$$

$$\frac{\Psi.\mu \gg A \text{ type } @ m \quad \Psi \Vdash P \in \langle \mu \mid A \rangle @ n}{\Psi \Vdash P = \operatorname{mod}(\operatorname{unmod}(P)) \in \langle \mu \mid A \rangle @ n}$$