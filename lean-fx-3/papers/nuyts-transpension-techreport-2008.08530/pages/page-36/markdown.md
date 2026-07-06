Instantiating this with $\sigma = () : \Psi \to \top$ and applying both hands to $\bot$, which is preserved by the substitution functor, we find $\Omega^{() \ltimes yU} \ldot{\lvert}_{yU} \bot \to \ldot{\lvert}_{yU}^{\Psi} \bot$, i.e. the indirect boundary predicate implies the direct boundary predicate.

Since the transpension type is stable under substitution for $\top$-slice (or equivalently presheafwise) fully faithful multipliers, we can conclude that for those multipliers, both notions of boundary coincide. In fact, we already proved this for $\top$-slice full multipliers (proposition 4.1.8).

**Theorem 4.4.7** (Transpension elimination). Let $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ be $\top$-slice (or equivalently presheafwise) fully faithful and shard-free. Then we have$^{16}$

$$
\begin{aligned}
\Psi \ltimes \mathbf{y}U \mid \Gamma \vdash \text{Ctx} \\
\Psi \mid \forall_{\mathbf{y}U}^{\Psi} \mid \Gamma \vdash A \text{ type} \\
\Psi \ltimes \mathbf{y}U \mid \Gamma \cdot \left\langle \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \mid A \right\rangle \vdash B \text{ type} \\
\Psi \ltimes \partial U \mid \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \mid \Gamma \vdash b_\partial : \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \mid B \right) [(\text{id}, \bot)] \\
\Psi \mid \left( \forall_{\mathbf{y}U}^{\Psi} \mid \Gamma \right) \cdot A \vdash \dot{b} : \left( \forall_{\mathbf{y}U}^{\Psi} \mid B \right) \left[ \left( \pi, \left( \text{unmerid}_{\mathbf{y}U}^{\Psi} \right)^{-1} (\xi) \right) \right] \\
\Psi \ltimes \partial U \mid \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \left( \left( \forall_{\mathbf{y}U}^{\Psi} \mid \Gamma \right) \cdot A \right) \vdash^{\Omega_{(\in \partial U)}^{\Psi \ltimes \partial U}} \left( \text{app}_{\mathbf{y}U}^{\Psi} \left( \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \dot{b} \right) \right) = b_\partial \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \left( \text{app}_{\mathbf{y}U}^{\Psi} \circ \pi \right) \right] \\
: \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \mid B \right) [(\text{id}, \bot)] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \left( \text{app}_{\mathbf{y}U}^{\Psi} \circ \pi \right) \right] \\
\hline
\end{aligned}
$$

and $b$ reduces to $b_\partial$ and $\dot{b}$ if we apply to it the same functors and substitutions that have been applied to $B$ in the types of $b_\partial$ and $\dot{b}$.

(If the multiplier is not $\top$-slice (or equivalently presheafwise) right adjoint, then $\lleftarrow_{\mathbf{y}U}^{\Psi}$ may not be a CwF morphism, but the term $\text{app}_{\mathbf{y}U}^{\Psi} \left( \lleftarrow_{\mathbf{y}U}^{\Psi} \dot{b} \right)$ is essentially a dependent transposition for the adjunction $\lleftarrow_{\mathbf{y}U}^{\Psi} \dashv \forall_{\mathbf{y}U}^{\Psi}$ which even exists if only the right adjoint is a CwF morphism [Nuy18]).

In words: if we want to eliminate an element of the transpension type, then we can do so by induction. We distinguish two cases and a coherence condition:

- In the first case ($b_\partial$), we are on the boundary of $U$ and the transpension type trivializes.
- In the second case, we are defining an action on cells that live over all of $\mathbf{y}U$. In the transpension type, such cells are in 1-1 correspondence with cells of type $A$ under the isomorphism $\text{unmerid}_{\mathbf{y}U}^{\Psi} : \forall_{\mathbf{y}U}^{\Psi} \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \cong \text{Id}$.
- The boundary of the image of cells in the second case, must always be $b_\partial$.

Note that right adjoint weak CwF morphisms such as $\ldot{\lvert}_{\mathbf{y}U}^{\Psi}$ give rise to a DRA by applying the CwF morphism and then substituting with the unit of the adjunction. As such, the transpension type is modelled by the DRA sending $A$ to $\left\langle \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \mid A \right\rangle = \left( \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \mid A \right) \left[ \text{reid}_{\mathbf{y}U}^{\Psi} \right]$.

*Proof.* **Well-formedness.** We first show that the theorem is well-formed.

- The rule for $\Gamma$ just assumes that $\Gamma$ is a presheaf over $\mathcal{V}/(\Psi \ltimes \mathbf{y}U)$.
- Then $\forall_{\mathbf{y}U}^{\Psi} \mid \Gamma$ is a presheaf over $\mathcal{W}/\Psi$ and we assume that $A$ is a type in that context, i.e. a presheaf over the category of elements of $\forall_{\mathbf{y}U}^{\Psi} \mid \Gamma$.
- Then the DRA of $\ldot{\lvert}_{\mathbf{y}U}^{\Psi}$ applied to $A$ is a type in context $\Gamma$. We assume that $B$ is a type over the extended context.

$^{16}$regardless of the notion of boundary, as these coincide for $\top$-slice full multipliers (proposition 4.1.8); we do not even have to distinguish cases in the proof as we will simply apply the appropriate version of the quotient theorem 4.1.12.

36