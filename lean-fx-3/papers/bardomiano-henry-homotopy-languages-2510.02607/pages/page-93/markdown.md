2. The judgment

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type}$$

is a *well-formed judgment* of $T$ if and only if $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a context.

3. The judgment

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta$$

is *well-formed* if and only if

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type}$$

is a *derived judgment* of $T$.

**Definition A.4.** Let $T$ be a $\kappa$-pretheory. The set of *derived judgments* of $T$ are the ones that can be derived from the following list of rules:

1.

$$\frac{\Gamma \vdash A \text{ Type}}{\Gamma \vdash A \equiv A}$$

2.

$$\frac{\Gamma \vdash t : A}{\Gamma \vdash t \equiv_A t}$$

3.

$$\frac{\Gamma \vdash A_1 \equiv A_2}{\Gamma \vdash A_2 \equiv A_1}$$

4.

$$\frac{\Gamma \vdash t_1 \equiv_A t_2}{\Gamma \vdash t_2 \equiv_A t_1}$$

5.

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad \Gamma \vdash A_2 \equiv A_3}{\Gamma \vdash A_1 \equiv A_3}$$

6.

$$\frac{\Gamma \vdash t_1 \equiv_A t_2 \quad \Gamma \vdash t_2 \equiv_A t_3}{\Gamma \vdash t_1 \equiv_A t_3}$$

93