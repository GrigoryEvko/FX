**Proposition A.6.4** (Frobenius, `type-former.pi.IIFibStr`). Given a family of types $A$ over $\Gamma$ and $B$ over $\Gamma.A$, we have an operation

$$\text{Transp } \Gamma \ A \to \text{Fill } (\Gamma.A) \ B \to \text{Fill } \Gamma \ (\Pi_A B).$$

*Proof.* Let us write $T$ for $\Pi_A B$. Given $t_A$ in $\text{Transp } \Gamma \ A$ and $c_B$ in $\text{Fill } (\Gamma.A) \ B$, we define $c_T$ in $\text{Fill } \Gamma \ T$ by

$$c_T^n \ \gamma \ r_0 \ f_0 \ (\psi, f) \ r_1 \ a_1 := c_B^n \ \langle \gamma, \tilde{a} \rangle \ r_0 \ b_0 \ (\psi, b) \ r_1 \tag{A.6.5}$$

where

$$\begin{array}{rcl} \tilde{a} & := & t_A^n \ \gamma \ r_1 \ a_1 \quad \text{in} \quad \Pi_{r:S} A \ (\gamma \ r) \\ \langle \gamma, \tilde{a} \rangle \ r & := & (\gamma \ r, \tilde{a} \ r) \quad \text{in} \quad (\Gamma.A)^S \\ b \ x \ r & := & f \ x \ r \ (\tilde{a} \ r) \quad \text{in} \quad (\Pi_{r:S} B (\gamma \ r, \tilde{a} \ r))^{[\psi]} \\ b_0 & := & f_0 \ (\tilde{a} \ r_0) \quad \text{in} \quad B \ (\gamma \ r_0, \tilde{a} \ r_0). \end{array}$$

So far this is only a slight generalization of [ABCHFL21], having replaced $\mathsf{I}$ by $S = \mathsf{I}^n$.

It remains to check the equivariance equation (A.5.4) for the operation $c_T$, assuming that the operations $t_A$ and $c_B$ are equivariant. Let $\sigma$ be an element of $\Sigma_n$. Write $\tilde{a}, b, b_0$ for the auxiliary definitions associated to $c_T^n \ \gamma \ (\sigma \ r_0) \ t_0 \ (\psi, t) \ (\sigma \ r_1)$ and $\tilde{a}', b', b'_0$ for those associated to $c_T^n \ \gamma \sigma \ r_0 \ f_0 \ (\psi, f) \sigma \ r_1$. Then we have

$$c_T^n \ \gamma \ (\sigma \ r_0) \ t_0 \ (\psi, t) \ (\sigma \ r_1) \ a_1 := c_B^n \ \langle \gamma, \tilde{a} \rangle \ (\sigma \ r_0) \ b_0 \ (\psi, b) \ (\sigma \ r_1)$$

$$(\text{equivariance of } c_B) = c_B^n \ \langle \gamma, \tilde{a} \rangle \sigma \ r_0 \ b_0 \ (\psi, b) \sigma \ r_1$$

$$(\text{equivariance of } t_A) = c_B^n \ \langle \gamma \sigma, \tilde{a}' \rangle \ r_0 \ b'_0 \ (\psi, b') \ r_1$$

$$=: c_T^n \ \gamma \sigma \ r_0 \ f_0 \ (\psi, f) \sigma \ r_1 \ a_1$$

where we use equivariance of $t_A$ to see that $\tilde{a} \ (\sigma \ r) = t_A \ \gamma \ (\sigma \ r_1) \ a_1 \ (\sigma \ r) = t_A \ \gamma \sigma \ r_1 \ a_1 \ r = \tilde{a}' \ r. \quad \square$

The core of the argument for Frobenius in this type-theoretic setting is thus the defining equation (A.6.5).

*Remark A.6.6.* To interpret the law $(\Pi_A B)[\rho] = \Pi_{A[\rho]} B[\rho.A]$ for computing a substitution applied to a $\Pi$-type, it is also necessary to check that the operation defined in Proposition A.6.4 commutes with reindexing along any $\rho : \Delta \to \Gamma$; see `type-former.pi.reindexIIFibStr` in the formalization.

**A.7. Other type formers.** We can follow the pattern of the proof of Proposition A.6.4 to lift the other type-theoretic operations to filling structures: take the corresponding definition of Angiuli et al. [ABCHFL21], replace $\mathsf{I}$ by $S = \mathsf{I}^n$, and check the equivariance equation.

For instance (`type-former.sigma`), we define the $\Sigma$-type $\Sigma_A B$ of families $A$ over $\Gamma$ and $B$ over $\Gamma.A$ by $(\Sigma_A B)\gamma = \Sigma_{a:A\gamma} B(\gamma, a)$ and build an element of type

$$\text{Fill } \Gamma \ A \to \text{Fill } (\Gamma.A) \ B \to \text{Fill } \Gamma \ (\Sigma_A B).$$

This corresponds to the closure of fibrations under composition in the external development.

To interpret identity types, we first define path types (`type-former.path`) as an instance of extension types (`type-former.extension`) à la Riehl and Shulman [RS17]. Extension types correspond externally to the closure of fibrations under Leibniz exponentiation by cofibrations (Proposition 5.2.8). Path types suffice to interpret identity types with a propositional computational rule for the eliminator. To interpret identity types with a judgmental computation rule, we can apply a modification due to Swan to path types [CCHM15, §9.1] (`type-former.swan-identity`).

We establish fibrancy and univalence of universes using the Glue types introduced in [CCHM15, §6] and adapted to cartesian cubical type theory in [ABCHFL21, §2.11] (`type-former.glue`). Preliminary WeakGlue types correspond to the equivalence extension property for the equivariant premodel structure proven in Proposition 5.3.1. The Glue types and associated properties (`universe.univalence`) correspond to univalence of the universe of equivariantly fibrant types

80