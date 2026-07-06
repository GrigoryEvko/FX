Note that this collection automatically contains all identities, composites, and opposites. It is isomorphic to Pinyo and Kraus's category of twisted cubes, as can be seen from the ternary representation of said category [PK20, def. 34]. This category is objectwise pointable.

Again, we consider the functor $\sqcup \ltimes \mathbb{I} : \mathbb{M} \to \mathbb{M}$, which is well-defined by construction of $\mathbb{M}$ and an endomultiplier for $\mathbb{I}$. It corresponds to Pinyo and Kraus's twisted prism functor.

It is: not copointed and $\top$-slice fully faithful, objectwise pointable, shard-free and right adjoint.

The left adjoint to $\exists_1 : W \mapsto (W \ltimes \mathbb{I}, \pi_2)$ is now given by

$$\exists_1 : \left\{ \begin{array}{l l} (W, ((), 0)) & \mapsto W^{\mathrm{op}} \\ (W, ((), 1)) & \mapsto W \\ (W \ltimes \mathbb{I}, () \ltimes \mathbb{I}) & \mapsto W, \end{array} \right. \tag{16}$$

with the obvious action on morphisms.

Example 3.3.9 (Embargoes). In order to define contextual fibrancy [BT21] internally, we need to be able to somehow put a sign in the context $\Gamma \mathbf{\Omega} \Theta$ in order to be able to say: the type is fibrant over $\Theta$ in context $\Gamma$. We call this an embargo and say that $\Theta$ is embargoed whereas $\Gamma$ is not. If $\mathcal{C}$ is the category of contexts, then $\Gamma \mathbf{\Omega} \Theta$ can be seen as an object of the arrow category $\mathcal{C}^\uparrow$, namely the arrow $\Gamma \Theta \to \Gamma$.

If $\mathcal{C} = \widehat{\mathcal{W}}$ happens to be a presheaf category, then we have an isomorphism of categories $H : \widehat{\mathcal{W}}^\uparrow \cong \widehat{\mathcal{W} \times \uparrow}$ where $\uparrow = \{\bot \to \top\}$. Under this isomorphism, we have $\mathbf{y}(W, \top) \cong H(\mathbf{y}W \xrightarrow{\mathrm{id}} \mathbf{y}W)$ which we think of as $\mathbf{y}W \mathbf{\Omega} \top$ and $\mathbf{y}(W, \bot) \cong H(\bot \xrightarrow{\mathrm{id}} \mathbf{y}W)$ which we think of as $\mathbf{y}W \mathbf{\Omega} \bot \bot$. Thus, forgetting the second component of $(W, o)$ amounts to forgetting the embargoed part of the context. A $(W, \top)$-cell of $\Gamma \mathbf{\Omega} \Theta$ is a $W$-cell of $\Gamma \Theta$, i.e. a partly embargoed $W$-cell. We can extract the unembargoed information by restricting to $(W, \bot)$, as a $(W, \bot)$-cell of $\Gamma \mathbf{\Omega} \Theta$ is just a $W$-cell of $\Gamma$.

There are 3 adjoint functors $\bot \dashv () \dashv \top$ between $\uparrow$ and Point from which we obtain 3 adjoint functors $(\mathrm{Id}, \bot) \dashv \pi_1 \dashv (\mathrm{Id}, \top)$ between $\mathcal{W} \times \uparrow$ and $\mathcal{W}$. The rightmost functor $(\mathrm{Id}, \top) : \mathcal{W} \to \mathcal{W} \times \uparrow$ is a multiplier for the terminal object $\mathbf{\Omega} \colon := (\top, \top) \in \mathcal{W} \times \uparrow$, denoted $\sqcup \ltimes \mathbf{\Omega}$.

It is: not endo, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $\mathcal{W}$ is and in that case $\top$-slice shard-free, and $\top$-slice right adjoint.

In order to look at the left adjoint, note first that since $\mathbf{\Omega}$ is terminal, we have $(\mathcal{W} \times \uparrow)/\mathbf{\Omega} \cong \mathcal{W} \times \uparrow$ and clearly $\exists_1$ corresponds to $(\mathrm{Id}, \top)$ under this isomorphism. This functor is part of a chain of three adjoint functors $(\mathrm{Id}, \bot) \dashv \pi_1 \dashv (\mathrm{Id}, \top)$ so that the multiplier is not just $\top$-slice right adjoint but $\exists_1$ even has a further left adjoint!

If $\sqcup \ltimes U : \mathcal{V} \to \mathcal{W}$ is a multiplier, then we can lift it to a multiplier $\sqcup \ltimes (U \ltimes \mathbf{\Omega}) : \mathcal{V} \times \uparrow \to \mathcal{W} \times \uparrow$ by applying it to the first component, i.e. $(W, o) \ltimes (U \ltimes \mathbf{\Omega}) = (W \ltimes U, o)$. The resulting multiplier inherits all properties in definition 3.1.2 from $\sqcup \ltimes U$, except that it is never $\top$-slice objectwise pointable.

Example 3.3.10 (Enhanced embargoes). If $\sqcup \ltimes U$ is a copointed endomultiplier on $\mathcal{W}$, then we might want to apply it to an arrow $V \xrightarrow{\psi} W$ by sending it to $V \ltimes U \xrightarrow{\psi \circ \pi_1} W$. This operation is not definable on $\mathcal{W} \times \uparrow$, which only encodes arrows of the forms $W \to W$ (as $(W, \top)$) and $\bot \to W$ (as $(W, \bot)$). For this reason, we move to the comma category $\mathcal{W}_\mathbf{\Omega} := \mathcal{W}_\bot / \mathcal{W}$ where $\mathcal{W}_\bot$ is $\mathcal{W}$ with a freely added initial object. This comma category has as its objects arrows $V \xrightarrow{\psi} W$ where $V \in \mathcal{W}_\bot$ and $W \in \mathcal{W}$. Morphisms are simply commutative squares. A $(V \xrightarrow{\psi} W)$-cell is now a non-embargoed $W$-cell $\gamma$ with embargoed information about $\gamma \circ \psi$.

We still have three adjoint functors $(\bot \xrightarrow{\mathrm{id}} \sqcup) \dashv \mathrm{Cod} \dashv \Delta$ where $\Delta W = (W \xrightarrow{\mathrm{id}} W)$. Further right adjoints would be $\mathrm{Dom} \dashv (\sqcup \xrightarrow{\mathrm{id}} \top)$, but $\mathrm{Dom}$ is not definable as the domain might be $\bot$. We take $\Delta$ as a multiplier for $\mathbf{\Omega} \colon := (\top \to \top)$, denoted $\sqcup \ltimes \mathbf{\Omega} \colon := \Delta$.

The multiplier $\sqcup \ltimes \mathbf{\Omega}$ is: not endo, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $\mathcal{W}$ is objectwise pointable and in that case generally not $\top$-slice shard-free (as every non-identity arrow is a shard), and $\top$-slice right adjoint.

Now we can still lift any multiplier $\sqcup \ltimes U : \mathcal{V} \to \mathcal{W}$ to a multiplier $\sqcup \ltimes (U \ltimes \mathbf{\Omega}) : \mathcal{V}_\mathbf{\Omega} \to \mathcal{W}_\mathbf{\Omega}$ for $(U \ltimes \mathbf{\Omega}) = (U \xrightarrow{\mathrm{id}} U)$ by applying it to both domain and codomain, i.e. $(V \xrightarrow{\psi} W) \ltimes (U \ltimes \mathbf{\Omega}) :=$

13