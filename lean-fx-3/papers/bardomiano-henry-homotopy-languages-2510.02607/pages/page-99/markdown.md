**Definition A.17.** We say that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta \approx \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash s : \Omega$$

if and only if $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type} \approx \{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega \text{ Type}$ and $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv s$.

*Remark A.18.* Let $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ and $\{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be two contexts. Assume further that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x_\beta : \Omega_\beta\}_{\beta < \mu}.$$

Then for all derived rules

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega,$$

the rule

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Omega$$

is also a derived rule.

Regardless of its simplicity, this remark is useful in the next:

**Corollary A.19.** *The relation $\approx$ is an equivalence relation on judgments of the form $\{x_\beta : \Delta_\beta\}_{\beta < \mu} \vdash t : \Delta$.*

*Proof.* Reflexivity is a consequence of 2 from theorem A.4. Assume that $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta \approx \{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash s : \Omega$. Hence, the contexts satisfy $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda}$. Applying the symmetry of the relation $\approx$ to contexts, and using theorem A.18, we see that $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash t \equiv s$. Then we must have $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash s : \Delta$ and $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash \Omega \equiv \Delta$. We can apply 4 from theorem A.4 to conclude that $\{x_\alpha : \Omega_\alpha\}_{\alpha < \lambda} \vdash s \equiv t$, thus proving symmetry. Transitivity is a straightforward application of theorem A.18. $\square$

**Definition A.20.** A *morphism* between contexts

$$\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \rightarrow \{x_\beta : \Omega_\beta\}_{\beta < \mu}$$

is $\mu$-sequence of terms $\{t_\beta\}_{\beta < \mu}$ such that for all $\beta < \mu$ we have

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\beta : \Omega_\beta [t_\gamma | x_\gamma]_{\gamma < \beta}.$$

99