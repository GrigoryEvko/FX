The following theorem shows that dimensionally split morphisms are an interesting concept:

**Theorem 4.4.5** (Boundary theorem). 1. (Obsolete.) Using the indirect boundary, we have

$$\top \ltimes \mathbf{y} U \mid (\in \partial U) \cong \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot \vdash \mathsf{Ctx}$$

and more generally

$$\Psi \ltimes \mathbf{y} U \mid (\in \partial U) \cong \Omega^{( ) \ltimes \mathbf{y} U \mid} \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot \vdash \mathsf{Ctx}.$$

2. Using the direct boundary, we have

$$\Psi \ltimes \mathbf{y} U \mid (\in \partial U) \cong \mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot \vdash \mathsf{Ctx}.$$

*Proof.* 1. We prove the first statement by characterizing the right hand side of the isomorphism. We have

$$\begin{aligned} & (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot \\ & = \forall_{\mathbf{y} U}^{\top \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U}) \rightarrow \bot \\ & = \forall (W, ()^{W \Rightarrow \top}). ((W, ()) \Rightarrow \forall_{\mathbf{y} U}^{\top \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow ((W, ()) \Rightarrow \bot) \\ & = \forall (W, ()^{W \Rightarrow \top}). ((W, ()) \Rightarrow \forall_{\mathbf{y} U}^{\top \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, ()^{W \Rightarrow \top}). (\exists_{U}^{\top} (W, ()) \rightarrow (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, ()^{W \Rightarrow \top}). ((W \ltimes U, () \ltimes U) \rightarrow (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & \cong \forall W. ((W \ltimes U, \pi_2) \rightarrow (V, \pi_2 \circ \varphi)) \rightarrow \varnothing \\ & \cong (\exists W. (W \ltimes U, \pi_2) \rightarrow (V, \pi_2 \circ \varphi)) \rightarrow \varnothing. \end{aligned}$$

Clearly, the left hand side of the last line is inhabited if and only if $\pi_2 \circ \varphi$ is dimensionally split. Hence, there is a unique cell $(V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot$ if and only if $\pi_2 \circ \varphi$ is *not* dimensionally split, showing that $\mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot$ is indeed isomorphic to $(\in \partial U)$.

The second statement follows from applying $\Omega^{( ) \ltimes \mathbf{y} U \mid}$ to both sides of the first statement and observing that, being defined by pullback, the indirect boundary predicate is preserved by the substitution functor.

2. We prove this by characterizing the right hand side of the isomorphism. We have

$$\begin{aligned} & (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot \\ & = \forall_{\mathbf{y} U}^{\Psi \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \rightarrow \bot \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). ((W, \psi) \Rightarrow \forall_{\mathbf{y} U}^{\Psi \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow ((W, \psi) \Rightarrow \bot) \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). ((W, \psi) \Rightarrow \forall_{\mathbf{y} U}^{\Psi \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). (\exists_{U}^{\top} (W, \psi) \rightarrow (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). ((W \ltimes U, \psi \ltimes U) \rightarrow (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & \cong (\exists (W, \psi^{W \Rightarrow \Psi}). (W \ltimes U, \psi \ltimes U) \rightarrow (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing. \end{aligned}$$

Clearly, the left hand side of the last line is inhabited if and only if $\varphi$ is directly dimensionally split. Hence, there is a unique cell $(V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot$ if and only if $\varphi$ is *not* directly dimensionally split, showing that $\mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot$ is indeed isomorphic to $(\in \partial U)$. $\square$

**Remark 4.4.6.** In section 6.3 (theorem 6.3.1), we will see that unless the multiplier is $\top$-slice (or equivalently presheafwise) fully faithful, the transpension type may not be stable under substitution. Instead, for $\sigma : \Psi_1 \to \Psi_2$, we only have $\Omega^{\sigma \ltimes \mathbf{y} U \mid} \circ \mathbb{Q}_{\mathbf{y} U}^{\Psi_2 \mid} \to \mathbb{Q}_{\mathbf{y} U}^{\Psi_1 \mid} \circ \Omega^{\sigma \mid}$.

35