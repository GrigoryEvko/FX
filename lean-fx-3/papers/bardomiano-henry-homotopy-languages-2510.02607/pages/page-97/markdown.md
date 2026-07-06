This result has similar consequences of those in [Car78]. The proofs are analogous or the same. For us, it is only relevant to know that our generalized $\kappa$-algebraic theories are well-defined. That is:

**Proposition A.12.** *The derived judgments of a generalized $\kappa$-algebraic theory are well-formed.*

*Proof.* Again, by induction on the derivations [Car78, pp. 1.33]. $\square$

Both the statement and proof of the next lemma are the same as The Derivation Lemma [Car78, pp. 1.34]. The proof does not rely on the context size.

**Lemma A.13.** 1. *Every derived type judgment of $T$ is of the form*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash A(t_\alpha)_{\alpha < \lambda}$$

*for some type symbol $A$ with introductory rule*

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash A(x_\alpha)_{\alpha < \lambda} \text{ Type}$$

*and $\{t_\alpha\}_{\alpha < \lambda}$ are expressions such that for all $\alpha < \lambda$ the rule*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \Delta_\alpha[t_\delta \mid x_\delta]_{\delta < \alpha}.$$

2. *Every term element judgment of $T$ is of the form*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash x_\beta : \Omega$$

*for some $x_\beta$ and such that $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega_\beta \equiv \Omega$, or is of the form*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash f(t_\alpha)_{\alpha < \lambda} : \Omega$$

*for some operator symbol $f$ of $T$ with introductory judgment of the form*

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash f(x_\alpha)_{\alpha < \lambda} : \Delta$$

*such that for each $\alpha < \lambda$ the rules*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\alpha : \Delta_\alpha[t_\delta \mid x_\delta]_{\delta < \alpha}$$

*and*

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Delta[t_\alpha \mid x_\alpha]_{\alpha < \lambda} \equiv \Omega$$

*are derived rules of $T$.*

*Proof.* This follows from theorem A.4 (10) and (11). $\square$

97