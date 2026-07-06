180

Parametric cubical type theory

Note that $r$ must itself be a variable in this case. We have $M[r/x]\psi = M\psi[y/x]$, so the above term is equal to the following.

$$\overline{N}\psi[M\psi[0/x]/a_0, M\psi[1/x]/a_1, \lambda^1\mathbf{y}.M\psi[\mathbf{y}/x]/\overline{a}]\mathbf{y}$$

Finally, we know that $r$ does not occur in $M$ by typing assumption. As $\psi$ is affine, it can send no variables but $r$ to $\mathbf{y}$, so $\mathbf{y}$ does not occur in $M\psi$. It follows that $\lambda^1\mathbf{y}.M\psi[\mathbf{y}/x] = \lambda^1\mathbf{x}.M\psi$. The term above is therefore syntactically equal to $O\psi$.

(1) By cases on $\Psi \Vdash r \in \mathbf{I}$. If $r$ is a constant, then this follows from the constant reduction rule. If $r$ is a variable, then it follows from the variable reduction rule. $\square$

In the proof above we see the crucial role of affinity in the well-behavedness of extent: it delivers the equation $\lambda^1\mathbf{y}.M\psi[\mathbf{y}/x] = \lambda^1\mathbf{x}.M\psi$. Intuitively, interval abstraction is stable under affine substitution, but not all structural substitutions. Say, for example, that we have some two-dimensional path term $P$ applied to path interval variables $x$ and $y$. By interleaving abstraction by $x$ with the diagonal substitution $z:\mathbb{I} \Vdash (z/x, z/y) \in (x:\mathbb{I}, y:\mathbb{I})$ in different orders, we get different results.

$$\begin{array}{ccc} (x, Pxy) & \xmapsto{\lambda^1\mathbb{I} - \cdot -} & \lambda^1\mathbf{x}.Pxy \\ & \downarrow & \downarrow -[z/x, z/y] \\ -[z/x, z/y] & & \downarrow \\ & & \lambda^1\mathbf{x}.Pxz \\ & \downarrow & \updownarrow \\ (z, Pzz) & \xmapsto{\lambda^1\mathbb{I} - \cdot -} & \lambda^1\mathbf{z}.Pzz \end{array}$$

This instability is familiar to any programmer who has had to implement capture-avoiding substitution. With affine variables, on the other hand, this situation cannot occur.

**Theorem 9.3.2 (Bridges in function types).** Let $x:\mathbf{I} \gg A$ type and $x:\mathbf{I}, a:A \gg B$ type be given together with $F_0 \in ((a:A) \to B)[0/x]$ and $F_1 \in ((a:A) \to B)[1/x]$. Then we have an isomorphism of the following type.

$$\text{Bridge}(\mathbf{x}.(a:A) \to B, F_0, F_1)$$

$$\simeq$$

$$(a_0:A[0/x])(a_1:A[1/x])(p:\text{Bridge}(\mathbf{x}.A, a_0, a_1)) \to \text{Bridge}(\mathbf{x}.B[px/a], F_0a_0, F_1a_1)$$

That is, a bridge in a function type is a function from bridges in the domain to bridges in the codomain.