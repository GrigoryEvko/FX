16:10

A. NUYTS AND D. DEVRIESE

Vol. 20:2

To see (2), we need telescope application.

The transpension type and the meridian constructor respect substitution (FF:TRANSP:NAT, FF:TRANSP:INTRO:NAT), and this can only be stated thanks to functoriality (FF:CTX-FORALL:FMAP).

2.1.6. *Telescope application.* In Section 2.1.3 above, we noted that the formation and introduction rules of the transpension type are in line with those of the modal type in MTT (Fig. 4) and act by dependent transposition. In fact, the same is true for the formation and introduction rules of the linear/affine function type, which is a dependent right adjoint to shape variable extension of contexts (FF:CTX-SHP). In order for the types to be adjoints internally – which requires that we can define unit and co-unit functions and that the adjunction laws are statable and satisfied – we need their left adjoint operations to be adjoints, i.e. for any context $\Psi$ and any context $\Theta = (\Gamma, u : \mathbb{U}, \Delta)$, we need substitutions $\Psi \rightarrow [\forall u]\Theta = (\Gamma, \forall u.(\delta : \Delta))$ to be equivalent to substitutions $(\Psi, u : \mathbb{U}) \rightarrow \Theta = (\Gamma, u : \mathbb{U}, \delta : \Delta)$ respecting $u$.

One way to ensure this is by providing natural unit and co-unit substitutions. For the unit, we need substitutions $\Psi \rightarrow \forall u = (\Psi, \forall u.()) = \Psi$, so we can take the identity. In other words, the unit is given by FF:CTX-FORALL:NIL, with naturality given by FF:CTX-FORALL:FMAP:NIL.

For the co-unit, we need substitutions $(\Gamma, \forall u.(\delta : \Delta), v : \mathbb{U}) \rightarrow (\Gamma, u : \mathbb{U}, \Delta)$, which are given by FF:CTX-APP and made natural by FF:CTX-APP:NAT. Again, from the syntactic viewpoint it would be cleaner to write $\mathsf{app}_{\Theta} : ([\forall u]\Theta, v : \mathbb{U}) \rightarrow \Theta$. However, intuitively, semantically and in the admissibility proof, what it does is applying the 'function' $\lambda u.\delta : \forall u.\Delta$ to $v : \mathbb{U}$, which inspires the notation in the typing rule.

Since the unit is the identity, the adjunction laws simply require that whiskering the co-unit with either adjoint also yields the identity. The fact that $\mathsf{app}_{(\Gamma, u:\mathbb{U})} = 1_{(\Gamma, u:\mathbb{U})}$ is exactly what is asserted by FF:CTX-APP:NIL. The fact that $[\forall (v/u)]\mathsf{app}_{(\Gamma, u:\mathbb{U}, \delta:\Delta)} = 1_{(\Gamma, \forall u.(\delta:\Delta))}$ is exactly what is asserted by FF:CTX-FORALL:FMAP:CTX-APP.

With the unit and co-unit for the adjunction $(-, u : \mathbb{U}) \dashv [\forall u]$ on contexts in place, we can now state the $\beta$- and $\eta$-rules of the transpension type (FF:TRANSP:BETA, FF:TRANSP:ETA) parallel to those for the modal type in MTT (Proposition 3.3).

We now show (2) from above, i.e. assuming $\Delta$ lists a variable $y : B$, we seek to derive a term $\Gamma, \forall u.(\delta : \Delta) \vdash t : \forall v.B[\sigma]$. This can be done using FF:CTX-APP as follows:

$$\frac{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash y : B}{\Gamma, \forall u.(\delta : \Delta), v : \mathbb{U} \vdash y[v/u, (\lambda u.\delta) v/\delta] : B[v/u, (\lambda u.\delta) v/\delta]}\frac{\Gamma, \forall u.(\delta : \Delta) \vdash \lambda v.(y[v/u, (\lambda u.\delta) v/\delta]) : \forall v.(B[v/u, (\lambda u.\delta) v/\delta])}.$$

**Definition 2.1.** For any variable $y : B$ in telescope $\Delta$, we define $\Gamma, \forall u.(\delta : \Delta) \vdash \lambda u.y := \lambda v.(y[v/u, (\lambda u.\delta) v/\delta]) : \forall v.(B[v/u, (\lambda u.\delta) v/\delta])$.

**Proposition 2.2.** *For any variable $y : B$ in telescope $\Delta$ and any substitution $(1_\Gamma, u/u, \tau/\delta) : (\Gamma, u : \mathbb{U}, \delta' : \Delta') \rightarrow (\Gamma, u : \mathbb{U}, \delta : \Delta)$, we have*

$$\Gamma \vdash (\lambda u.y)[\lambda u.\tau/\lambda u.\delta] = \lambda u.(\tau_y[u/u, (\lambda u.\delta') u/\delta']) : \forall u.B[\tau/\delta],$$

*where $\tau_y = y[\tau/\delta]$ is the component of the vector $\tau$ for variable $y$.*