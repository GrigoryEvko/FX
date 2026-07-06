## 2.4 DÉCALAGE AND DISPLAYED TYPES

Semantically, the fundamental operation is shifting the dimensions of a simplicial type. In classical simplicial homotopy theory, this is called décalage:

$$\left(A^{D}\right)_{n}=A_{n+1}$$

The simplicial structure maps of $A^{D}$ are a subset of those of $A$, while the unused ones assemble into a simplicial map $A^{D} \to A$. When $A$ is a type at mode sm, we will regard $A^{D}$ as the projection from a type $A^{d}$ dependent on $A$; thus we have

$$A^{D}=(x:A, x':A^{d}x)$$

(Semantically, this is validated by the fact that if $A$ is Reedy fibrant, then the map $A^{D} \to A$ is a Reedy fibration.) These dependent types $A^{d}$, which we call display, are our version of the 'logical relations' assigned to every type by an internal parametricity theory.

### 2.4.1 Display for types

In contrast to fully internal parametricity theories, because we don't have degeneracies in our cube category, décalage and display can only be applied in restricted contexts. In external parametricity, the logical relations apply only to types in the empty context; but our modalities allow us to say more generally that they apply to any 'boxed' type. Here by 'box' we mean not $\square$ but the corresponding endofunctor of the simplicial mode, namely $\triangle\square$. Thus, informally display should have the type $d: (A:\triangle\square \text{Type}_{\ell}) \to A \to \text{Type}_{\ell}$, with computability witnesses being assigned by a function $d: (A:\triangle\square \text{Type}_{\ell})(x:\triangle\square A) \to A^{d}x$. If we reformulate these without referring to $\Pi$-types, we obtain the following rules for our basic notion of displayed type:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle\square} \vdash_{sm} A \text{ type}_{\ell} \quad \Gamma \vdash_{sm} t: A \left[ \mathbf{a}_{\ell}^{\triangle\square \leqslant 1_{sm}} \right]}{\Gamma \vdash_{sm} A^{d} \text{ type}_{\ell}} \quad \frac{\Gamma, \widehat{\mathbf{a}}_{\triangle\square} \vdash_{sm} t: A}{\Gamma \vdash t^{d}: A^{d} \left( t \left[ \mathbf{a}_{\ell}^{\triangle\square \leqslant 1_{sm}} \right] \right)}$$

However, in order to compute with this, we need a version of it that incorporates dependence on a telescope to the right of the lock. The corresponding action on that telescope is called décalage.

### 2.4.2 Telescope décalage

As noted above, with display $A^{d}$ defined as dependent on $A$, décalage $A^{D}$ is naturally not a single type but a telescope. It is therefore natural to generalise its input to be a telescope also. This yields an operation that doubles the variables and groups each type with its displayed version, e.g.

$$(x:A, y:B)^{D} \equiv (x:A, x':A^{d}x, y:B, y':B^{d}y).$$

The classical projection from décalage to the identity, composed of the leftover face maps, becomes an 'evens' substitution $\Upsilon^{D} \to \Upsilon$ that throws away the elements of the displayed

19