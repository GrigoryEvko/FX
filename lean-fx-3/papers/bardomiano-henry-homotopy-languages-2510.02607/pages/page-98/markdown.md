### A.3 Equivalence relation on judgments

Throughout this section we work in a generalized $\kappa$-algebraic theory. We first introduce a relation that allows us to identify contexts which express the same meaning, but differ on the variables that are used in them [Car78, 1.13].

There is a relation defined on the judgments of the generalized $\kappa$-algebraic theory $T$.

**Definition A.14.** Let $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \vdash \Delta_\lambda \text{ Type}$ and $\{x_\beta : \Omega_\beta\}_{\beta<\mu} \vdash \Omega_\mu \text{ Type}$ be two type judgments of $T$. We say that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \vdash \Delta_\lambda \text{ Type} \approx \{x_\beta : \Omega_\beta\}_{\beta<\mu} \vdash \Omega_\mu \text{ Type}$$

if either:

1. Both ordinals are successor such that $\lambda = \mu = \nu + 1$ and for all $\alpha \leq \nu$ we have

$$\{x_\delta : \Delta_\delta\}_{\delta<\alpha} \vdash \Delta_\alpha \equiv \Omega_\alpha$$

is a derived rule of $T$.

2. Both ordinals are limit ordinals with $\lambda = \mu$ and for any successor ordinal $\nu + 1 < \lambda$ we have

$$\{x_\alpha : \Delta_\alpha\}_{\alpha<\nu} \vdash \Delta_\nu \text{ Type} \approx \{x_\beta : \Omega_\beta\}_{\beta<\nu} \vdash \Omega_\nu \text{ Type}.$$

**Lemma A.15.** *The relation $\approx$ is an equivalence relation on type judgments of the theory $T$.*

*Proof.* This is an immediate result since we have assumed canonical names for variables. Otherwise, we could repeat the argument as in [Car78, 1.13].

$\square$

**Definition A.16.** Let $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}$ and $\{x_\beta : \Omega_\beta\}_{\beta<\mu}$ be two contexts. We say that

$$\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \approx \{x_\beta : \Omega_\beta\}_{\beta<\mu}$$

if and only if $\lambda = \mu$ and for all $\alpha < \lambda$

$$\{x_\delta : \Delta_\delta\}_{\delta<\alpha} \vdash \Delta_\alpha \text{ Type} \approx \{x_\gamma : \Omega_\gamma\}_{\gamma<\alpha} \vdash \Omega_\alpha \text{ Type}$$

It follows that this induces an equivalence relation on contexts.

98