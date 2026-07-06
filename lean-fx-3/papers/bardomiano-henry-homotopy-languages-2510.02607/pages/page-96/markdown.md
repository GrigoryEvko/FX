## A.2 Substitution property

Let $T$ be a generalized $\kappa$-algebraic theory. Recall that given $\Delta$, $\{t_\alpha\}_{\alpha < \lambda}$ expressions and $\{x_\alpha\}_{\alpha < \lambda}$ variables, then the new expression $\Delta[e_\alpha|x_\alpha]_{\alpha < \lambda}$ denotes the substitution of variables by the expressions.

**Definition A.8.** Let $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ be a derived judgment of $T$. We say that this judgment has the *substitution property* if for every $\vdash \Gamma$ Ctxt and expressions $\{t_\alpha\}_{\alpha < \lambda}$, such that for all $\alpha < \lambda$

$$\Gamma, \{t_\beta : \Delta_\beta[t_\gamma|x_\gamma]_{\gamma < \beta}\}_{\beta < \alpha} \vdash t_\alpha : \Delta_\alpha[t_\beta|x_\beta]_{\beta < \alpha}$$

are derived rules, then

$$\Gamma \vdash \Delta[t_\alpha|x_\alpha]_{\alpha < \lambda}$$

is a derived rule of $T$.

In [Car78] it is proven that all derived judgment of a generalized algebraic theory satisfy the substitution property. This is done through a series of results that can be generalized to our setting. The proofs are omitted since they are the same as in the original reference.

**Lemma A.9.** If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ is a derived judgment of $T$, then the variables that appear in $\Delta$ is a subset of $\{x_\alpha\}_{\alpha < \lambda}$

*Proof.* See [Car78, Lemma 1, Section 1.7]. $\square$

**Lemma A.10.** 1. *The premise of a derived judgment is a context.*

2. If $\vdash \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ Ctxt then for $\alpha < \lambda$, we have

$$\{x_\beta : \Delta_\beta\}_{\beta < \alpha} \vdash \Delta_\alpha \text{ Type}$$

*Proof.* See [Car78, Lemma 2, Section 1.7]. $\square$

**Theorem A.11.** *Every derived judgment of a generalized $\kappa$-algebraic theory has the substitution property.*

*Proof.* The same proof as in [Car78, 1.7] applies. This goes by proving that each judgment has the substitution property. For the last two judgments in theorem A.1, this is a consequence of rules (11) and (12) in theorem A.4. While for the first two it is done by induction on the derivations. It is shown that each derivation rule of theorem A.4 preserve the substitution property. $\square$

96