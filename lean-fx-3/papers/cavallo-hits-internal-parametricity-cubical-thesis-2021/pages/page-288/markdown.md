276

Programming in cohesive parametric type theory

That is, we first apply the parametric comm at the discrete embeddings of $A_*$ and $B_*$, then adjust by $\wedge$-disc to obtain the following dashed composite function.

$$\begin{array}{c} \operatorname{Disc}_*(A_*) \wedge_* \operatorname{Disc}_*(B_*) \xrightarrow[\wedge\text{-disc}]{\simeq} \operatorname{Disc}_*(A_* \wedge_* B_*) \\ \operatorname{unmod}(\operatorname{comm}) \triangleleft A_* \triangleleft B_* \Bigg\downarrow \\ \operatorname{Disc}_*(B_*) \wedge_* \operatorname{Disc}_*(A_*) \xrightarrow[\wedge\text{-disc}]{\simeq} \operatorname{Disc}_*(B_* \wedge_* A_*) \end{array}$$

Applying $\blacklozenge_*(\operatorname{mod}(-))$ then yields a map $A_* \wedge_* B_* \to B_* \wedge_* A_*$.

We show that $\operatorname{comm}_{\mathrm{pt}} A_* B_*$ is an isomorphism by checking that $\operatorname{comm}_{\mathrm{pt}} B_* A_*$ is its inverse, i.e., that $\operatorname{comm}_{\mathrm{pt}} B_* A_* \circ_* \operatorname{comm}_{\mathrm{pt}} A_* B_*$ for any $A_*$ and $B_*$. The aim is to reduce this condition to the corresponding condition on the parametric commutator. To do so, we need to know how $\blacklozenge_*$ interacts with function identity and composition.

**Proposition 15.4.8 (Functoriality of $\blacklozenge_*$).** Given $A_*, B_*, C_* : \cup_*$ and a pair of functions $u : \operatorname{Glo}(\operatorname{Disc}_*(A_*) \to \operatorname{Disc}_*(B_*))$ and $v : \operatorname{Glo}(\operatorname{Disc}_*(B_*) \to \operatorname{Disc}_*(A_*))$, we have paths of the following types.

$$\begin{array}{l} \operatorname{id}_*(A_*) \rightsquigarrow \blacklozenge_*(\operatorname{mod}(\operatorname{id}_*(\operatorname{Disc}_*(A_*)))) \in A_* \to A_* \\ \blacklozenge_*v \circ_* \blacklozenge_*u \rightsquigarrow \blacklozenge_*(\operatorname{mod}(\operatorname{unmod}(v) \circ_* \operatorname{unmod}(u))) \in A_* \to C_* \end{array}$$

*Proof (sketch).* The first of these two paths holds up to exact equality. The second takes more work to establish; its proof involves undisc-uniq and, to relate the basepoint preservation paths, the fact that mod (as a constructor for Disc) commutes with hcom. $\square$

This work can be avoided by instead *defining* composition in the pointwise mode as the shadow of parametric composition.

$$g_* \circ_*^{\mathrm{pt}} f_* := \blacklozenge_*(\operatorname{mod}(\operatorname{unmod}(\diamond_* g_*) \circ_* \operatorname{unmod}(\diamond_* f_*)))$$

The path $\blacklozenge_*v \circ_*^{\mathrm{pt}} \blacklozenge_*u \rightsquigarrow \blacklozenge_*(\operatorname{mod}(\operatorname{unmod}(v) \circ_* \operatorname{unmod}(u)))$ then follows as a corollary of the inverse conditions of the $\diamond_*\text{-}\blacklozenge_*$ isomorphism.

**Theorem 15.4.9.** $\operatorname{comm}_{\mathrm{pt}}$ is a family of isomorphisms.

*Proof.* It suffices to show that for any $A_*, B_* : \cup_*$, we have a path in $A_* \wedge_* B_* \to B_* \wedge_* A_*$ as follows.

$$\operatorname{comm}_{\mathrm{pt}} B_* A_* \circ_* \operatorname{comm}_{\mathrm{pt}} A_* B_* \rightsquigarrow \operatorname{id}_*(A_* \wedge_* B_*)$$