The symbol $\otimes$ is only here to distinguish the underlying $\infty$-categories $\mathcal{M}$ and $\mathcal{X}$, which are the fiber over respectively [1] and ([0], 0), from the domain of these coCartesian fibrations.

*Remark 3.4.* If an $\infty$-category $\mathcal{M}$ has a monoid structure as a simplicial set, then it has a monoidal $\infty$-category. We call this a strict monoidal $\infty$-category. Indeed, one easily sees that such a “strict monoidal” $\infty$-category corresponds exactly to the functor $N(\Delta^{op}) \rightarrow \mathbf{Cat}_{\infty}$, which comes from the 1-categorical functor $\Delta^{op} \rightarrow \operatorname{Set}_{\Delta}$ that takes values in $\infty$-categories and satisfies the Segal condition up to isomorphism instead of just up to equivalence. Morphisms of simplicial monoids also induces monoidal functors.

Of course, the same can be said of a monoidal action. If $\mathcal{M}$ and $\mathcal{X}$ are two $\infty$-categories and $\mathcal{M}$ is a simplicial monoid acting on the simplicial set $\mathcal{X}$, then this produces a monoidal structure on $\mathcal{M}$ and a monoidal action of $\mathcal{M}$ on $\mathcal{X}$ in the sense above. The monoidal action can be encoded as functor $\Delta^{op} \times \Delta^1 \rightarrow \operatorname{Set}_{\Delta}$ that takes values in quasi-categories and satisfies the Segal conditions up to isomorphism.

Next we move to the definition of monoids and monoidal actions in monoidal $\infty$-categories. We first need to introduce the following terminology:

**Definition 3.5.** • An edge in $N(\Delta^{op})$ is said to be *inert* if the corresponding arrow in $\Delta$ is an interval inclusion, i.e. of the form $[k] \simeq \{i, i+1, \dots, i+k\} \subset [n]$ for $i+k \leqslant n$.
- • An inert edge in $N(\Delta^{op}) \times \Delta^1$ is a pair $(v, f)$ of an *inert* edge $v$ (in the above sense) in $N(\Delta^{op})$ and an arbitrary edge $f$ in $\Delta^1$, such that if $f$ is the identity edge of 0 then the map $v : [n] \rightarrow [m]$ satisfies $v(n) = m$.
- • If $X^{\otimes} \rightarrow N(\Delta^{op})$ is a monoidal $\infty$-category or a monoidal action, an arrow in $X^{\otimes}$ is said to be *inert* if it is coCartesian and its image in $N(\Delta^{op})$ is inert.
- • If $X^{\otimes} \rightarrow N(\Delta^{op}) \times \Delta^1$ is a monoidal action, an arrow in $X^{\otimes}$ is said to be *inert* if it is coCartesian and its image in $N(\Delta^{op}) \times \Delta^1$ is inert.

Intuitively, the inert edges are the arrows in $N(\Delta^{op})$ or $N(\Delta^{op}) \times \Delta^1$ such that, given a monoid object $N(\Delta^{op}) \rightarrow \mathcal{C}$ or a module object $N(\Delta^{op}) \times \Delta^1 \rightarrow \mathcal{C}$ corresponds to product projection. A general arrow encodes some operations from the monoid or module structure.

We can now give the definition of monoids, monoid actions and module objects in a general monoidal $\infty$-category.

14