2.4. GLOBULAR EQUIVALENCES

Restricted to $\Sigma^n[2]_t \times \{1\}$ this shows that $F$ commutes with compositions. We then have defined a functor

$$F : \pi_n(s, t, C) \to \pi_n(s', t', C).$$

Using exactly the same procedure, where we just invert 0 and 1, we define a functor:

$$G : \pi_n(s', t', C) \to \pi_n(s, t, C).$$

Now, we have a lift in the following diagram:

$$\begin{array}{c} \mathbf{D}_n \times \Lambda^2[2]^\sharp \cup \partial \mathbf{D}_n \times [2]^\sharp \xrightarrow{h_x \cup h_{F(x)} \cup \psi(id \times s^0)} C \\ \downarrow \\ \mathbf{D}_n \times [2]^\sharp \end{array}$$

The restriction of $k_x$ to $\mathbf{D}_n \times [0,1]_t$ provides a marked cell $x \to G(F(x))$, which corresponds to an isomorphism in $\pi_n(s, t, C)$ according to proposition 2.4.1.8. If $f : x \to y$ is a $(n+1)$-cell, there is a lifting in the following diagram:

$$\begin{array}{c} \mathbf{D}_{n+1} \times \Lambda^2[2]^\sharp \cup \partial \mathbf{D}_{n+1} \times [2]^\sharp \xrightarrow{h_f \cup h_{F(f)} \cup k_x \cup k_y} C \\ \downarrow \\ \mathbf{D}_{n+1} \times [2]^\sharp \end{array}$$

The restriction of $k_f$ to $\mathbf{D}_{n+1} \times [0,1]_t$ induces in $\pi_n(s, t, C)$ a commutative diagram:

$$\begin{array}{c} x \longrightarrow GFx \\ [f] \downarrow \qquad \downarrow [GFf] \\ y \longrightarrow GFy. \end{array}$$

We then have an invertible natural transformation $\psi : id \to GF$. Similarly we can construct an other natural transformation $id \to GF$, which shows the desired equivalence of categories.

**Definition 2.4.1.10.** Let $a$ be an element of $\mathrm{Hom}_{h\circ(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, C)$. We define

$$\pi_n(a, C) := \pi_n(s, t, C) \tag{2.4.1.11}$$

where $s, t$ is a pair of parallel arrows such that $s \cup t$ represents $a$. The previous proposition shows that this is well defined.

### 2.4.2 A criterion to be a weak equivalence

**Definition 2.4.2.1.** A morphism $p : C \to D$ between complicial sets is a **D**-equivalence if

$$\pi_0(C) \to \pi_0(D)$$

is an equivalence of categories, and for any $n > 0$ and pair of parallel arrow $s, t$, the induced functor

$$\pi_n(s, t, C) \to \pi_n(ps, pt, D)$$

is an equivalence of categories.

A **D**-trivial *fibration* is a fibration having the right lifting property against $\partial \mathbf{D}_n \to \mathbf{D}_n$ and $\mathbf{D}_n \to (\mathbf{D}_n)_t$.

87