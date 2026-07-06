embeds in the category of coalgebras; thus, in particular, the colimit in $\mathsf{cSet}^2$ of any diagram of open box inclusions and pullback squares is a trivial cofibration.

With this definition, it is immediate that the 1-cube is contractible: the endpoint $0: 1 \mapsto I$ is the open box formed by the subobject $\emptyset \mapsto I^0$ and point $0: I^0 \to I^1$, thus a trivial cofibration. That the 2-cube is contractible is slightly less immediate: we can write $\vec{0}: 1 \to I^2$ as a composite of generating trivial cofibrations

$$1 \xrightarrow[0]{\sim} I^1 \xrightarrow[I^1 \times 0]{\sim} I^2$$

where the second map is the open box formed by $\emptyset \mapsto I^1$ and the constant map $0: I^1 \to I^1$. We can continue inductively to see that $\vec{0}: 1 \to I^n$ is a trivial cofibration for all $n$, the composite of $n$ generating trivial cofibrations. Observe, however, that this construction is inherently *asymmetric*: we collapse a 2-cube by collapsing first along one axis and then along the other. This prevents us, for example, from deriving a trivial cofibration coalgebra structure on $\vec{0}: 1 \to I^2_{/\Sigma_2}$ by taking a colimit: writing $\Sigma_2$ for the one-object groupoid corresponding to $\Sigma_2$, the diagram $\Sigma_2 \to \mathsf{cSet}^2$ sending the object to $\vec{0}: 1 \xrightarrow{\sim} I^2$ and $\sigma \in \Sigma_2$ to

$$\begin{array}{ccc} 1 & \longrightarrow & 1 \\ \vec{0} \downarrow & & \vec{0} \downarrow \\ I^2 & \xrightarrow{\sigma} & I^2 \end{array}$$

does *not* lift to a diagram of trivial cofibration coalgebras. In fact, one can show that if $A \xrightarrow{\sim} B$ is a trivial cofibration and $B$ contains a non-trivial (in an appropriate sense) copy of $I^2_{/\Sigma_2}$, then so does $A$ [Coq18, §4]: trivial cofibrations cannot collapse copies of $I^2_{/\Sigma_2}$. It follows that $I^2_{/\Sigma_2}$ is not contractible [Coq18, §5]; the same argument applies to quotients of higher cubes.

1.5.2. *The solution.* Our solution to this problem is to require a more general *equivariant* uniform box-filling structure on our fibrations. First, we generalize the open box inclusions, replacing generalized points $\xi: I^n \to I^1$ on the 1-cube with points $\xi: I^n \to I^k$ in arbitrary $k$-cubes, so that we ask for lifts

$$\begin{array}{ccc} I^n \cup_C C \times I^k & \longrightarrow & Y \\ \langle [\xi], c \times I^k \rangle \downarrow & & \downarrow f \\ I^n \times I^k & \longrightarrow & X. \end{array}$$

This generalization alone does not change the class of fibrations. The key is in our generalization of the uniformity condition: for every morphism of cubes $\alpha: I^m \to I^n$ and *automorphism* $\sigma: I^k \cong I^k$, the resulting triangle of lifts

$$\begin{array}{ccc} I^m \cup_D D \times I^k & \longrightarrow & I^n \cup_C C \times I^k \xrightarrow{\sim} Y \\ \downarrow & \downarrow & \downarrow \\ I^m \times I^k & \xrightarrow[\alpha \times \sigma]{} & I^n \times I^k \xrightarrow{\sim} X \end{array}$$

must commute.

With this definition, the vertex inclusion $\vec{0}: 1 \to I^n$ is immediately a trivial cofibration: it is the open box formed by $\emptyset \mapsto 1$ and the point $\vec{0}: 1 \to I^n$. Moreover, for any $H \subset \Sigma_n$, the diagram

6