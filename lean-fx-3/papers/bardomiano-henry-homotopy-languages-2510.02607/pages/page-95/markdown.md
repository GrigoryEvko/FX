14. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta'$ is an axiom then

$$\frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \text{ Type} \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta' \text{ Type},}{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta'}$$

15. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t'$ is an axiom then

$$\frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t' : \Delta}{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t'}$$

We are now ready for the following:

**Definition A.5.** A $\kappa$-pretheory $T$ is *well-formed* if all its rules are well-formed. A *generalized $\kappa$-algebraic theory* is a well-formed $\kappa$-pretheory.

*Remark A.6.* Observe that a generalized algebraic theory as defined by Cartmell [Car78] is the same as an $\omega$-generalized algebraic theory in our sense.

We introduce an important example of $\kappa$-algebraic theories.

**Example A.7.** Let *Cat* denote the $\omega$-algebraic theory defined in the following way:

1. Type of objects: $\vdash$ **Ob Type**.
2. Type of morphisms: $x : \mathbf{Ob}, y : \mathbf{Ob} \vdash \mathbf{Hom}(x, y)$ **Type**.
3. Composition operation: $x : \mathbf{Ob}, y : \mathbf{Ob}, z : \mathbf{Ob}, f : \mathbf{Hom}(x, y), g : \mathbf{Hom}(y, z) \vdash g \circ f : \mathbf{Hom}(x, z)$.
4. Identity operator: $x : \mathbf{Ob} \vdash \mathsf{id}_x : \mathbf{Hom}(x, x)$.

Subject to the following axioms:

$$\frac{x : \mathbf{Ob}, y : \mathbf{Ob}, f : \mathbf{Hom}(x, y)}{\mathsf{id}_y \circ f \equiv f} \quad \frac{x : \mathbf{Ob}, y : \mathbf{Ob}, f : \mathbf{Hom}(x, y)}{f \circ \mathsf{id}_x \equiv f}$$
$$\frac{x : \mathbf{Ob}, y :: \mathbf{Ob}, z : \mathbf{Ob}, w : \mathbf{Ob}, f : \mathbf{Hom}(x, y), g : \mathbf{Hom}(y, z), h : \mathbf{Hom}(z, w)}{(h \circ g) \circ f \equiv h \circ (g \circ f)}$$

95