Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:11

Proof. We have

$$\begin{array}{l} (\lambda u.y)[u/u, \tau/\delta] = (\lambda u.y[u/u, (\lambda u.\delta) u/\delta])[\lambda u.\tau/\lambda u.\delta] \quad \text{(Definition 2.1)} \\ = \lambda u.(y[u/u, (\lambda u.\delta) u/\delta][\lambda u.\tau/\lambda u.\delta, u/u]) \\ = \lambda u.(y[u/u, \tau/\delta][u/u, (\lambda u.\delta') u/\delta']) \quad \text{(FF:CTX-APP:NAT)} \\ = \lambda u.(\tau_y[u/u, (\lambda u.\delta') u/\delta']). \end{array}$$

Corollary 2.3. For any variable $y : B$ in telescope $\Delta$ and any substitution $(1_\Gamma, u/u, \tau/\delta) : (\Gamma, u : \mathbb{U}) \to (\Gamma, u : \mathbb{U}, \delta : \Delta)$, we have $\Gamma \vdash (\lambda u.y)[\lambda u.\tau/\lambda u.\delta] = \lambda u.\tau_y : \forall u.B[\tau/\delta]$, where $\tau_y = y[\tau/\delta]$ is the component of the vector $\tau$ for variable $y$.

Proof. This follows from FF:CTX-APP:NIL.

2.1.7. Discussion. The type system presented above is less general than the paper's main system MTraS. In Section 2.1.6, we saw that the unit of the adjunction on contexts is invertible. This is equivalent to the left adjoint $(-, u : \mathbb{U}) : \text{Ctx} \to \text{Ctx}/(u : \mathbb{U})$ being fully faithful [nLa23a], and the requirement on presheaf models to support the typing rules in the current section (with FF:CTX-FORALL:NIL an isomorphism) is exactly that: the multiplier functor interpreting $(-, u : \mathbb{U})$ has to be fully faithful w.r.t. the slice category over $(u : \mathbb{U})$.

By uniqueness of the adjoint, we can also conclude that the co-unit of the adjunction $\forall u \dashv \mathfrak{g}[u]$ is invertible,⁵ which is equivalent to the right adjoint $\mathfrak{g}[u]$ being fully faithful [nLa23c], whence the section title.

However, the current typing rules become unusable in a more general setting, as well as in more specific settings where we may start adding operations that we need in important applications. First, we have no story for substitutions which exist in cubical type systems such as endpoints $(0/i) : \Gamma \to (\Gamma, i : \mathbb{I})$ [BCM15, BCH14, CCHM17] or connections $(j \wedge k/i) : (\Gamma, j, k : \mathbb{I}) \to (\Gamma, i : \mathbb{I})$ [CCHM17], as there is no formation rule for $\mathfrak{g}[0]A$ or $\mathfrak{g}[j \wedge k]A$. Secondly, in non-fully-faithful generalizations featuring the contraction rule for shape variables, the transpension is not stable under substitution of the shape variables preceding $u$, so in those settings the way we internalized the transpension type here was too naïve.⁶ In order to obtain a type system that does not fail in the presence of endpoints, connections or shape variable contraction, in the rest of the paper we will rely on MTT, which we briefly summarize in Section 3.

2.2. Poles. We can still try to get a grasp on $\mathfrak{g}[0]A$ in cubical type systems, however. In general we have $T[0/i] \cong (\forall i.(i \equiv_{\mathbb{I}} 0) \to T)$. Assuming $T = \mathfrak{g}[i]A$ and onelsNotZero : $(1 \equiv_{\mathbb{I}} 0) \to \text{Empty}$, the latter type is inhabited by

$$\text{pole}_0 := \lambda i.\lambda e.\text{mer}[i] \text{ (case (onelsNotZero $((\lambda i.e) 1)$) of \{\})} : \forall i.(i \equiv_{\mathbb{I}} 0) \to \mathfrak{g}[i]A$$

where $\lambda i.e$ has type $\forall i.(i \equiv_{\mathbb{I}} 0)$. Moreover, using the $\eta$-rules for functions and the transpension type and a (provable propositional) $\eta$-rule for Empty, we can show that this is the only

⁵In fact, this is exactly what the $\beta$- and $\eta$-rules of the transpension type say (when $\Delta$ is empty).

⁶Indeed, write $\Omega[u]$ for the operation of cartesian weakening over a shape variable $u : \mathbb{U}$, which is an example of a substitution involving shape variables. If in general $\Omega[u] \circ \mathfrak{g}[v] \cong \mathfrak{g}[v] \circ \Omega[u]$, then by uniqueness of the left adjoint we would find that $\Pi v \circ \Sigma u \cong \Sigma u \circ \Pi v$. This is clearly false for cartesian shapes such as the interval $\mathbb{I}$ in HoTT. For more information on how the transpension type commutes with other operations, see the technical report [Nuy20b].