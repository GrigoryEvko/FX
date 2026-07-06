1:16

M. SHULMAN

Vol. 19:2

F-universal morphism $(\mathsf{U}(A \otimes B) \mid) \to \mathsf{FU}(A \otimes B)$:

$$\begin{aligned} \mathcal{P}(\mid A, B; A \otimes B) &\to \mathcal{P}(\mathsf{U}A, \mathsf{U}B \mid; A \otimes B) \\ &\xrightarrow{\sim} \mathcal{P}(\mathsf{U}A, \mathsf{U}B; \mathsf{U}(A \otimes B)) \\ &\to \mathcal{P}(\mathsf{U}A, \mathsf{U}B \mid; \mathsf{FU}(A \otimes B)) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \mathsf{FU}A, \mathsf{FU}B; \mathsf{FU}(A \otimes B)) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \mathsf{FU}A \otimes \mathsf{FU}B; \mathsf{FU}(A \otimes B)). \end{aligned}$$

Similarly, to give the map $\mathsf{I}A \to \mathsf{I}A \otimes \mathsf{I}A$ we act on the $\otimes$-universal morphism $(\mathsf{I}A, \mathsf{I}A) \to \mathsf{I}A \otimes \mathsf{I}A$ as follows. The two noninvertible maps are composition with the F-universal morphism $(\mathsf{U}A \mid) \to \mathsf{FU}A = \mathsf{I}A$ and a structural map.

$$\begin{aligned} \mathcal{P}(\mid \mathsf{I}A, \mathsf{I}A; \mathsf{I}A \otimes \mathsf{I}A) &= \mathcal{P}(\mid \mathsf{FU}A, \mathsf{FU}A; \mathsf{I}A \otimes \mathsf{I}A) \\ &\to \mathcal{P}(\mathsf{U}A, \mathsf{U}A \mid; \mathsf{I}A \otimes \mathsf{I}A) \\ &\to \mathcal{P}(\mathsf{U}A \mid; \mathsf{I}A \otimes \mathsf{I}A) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \mathsf{FU}A; \mathsf{I}A \otimes \mathsf{I}A). \end{aligned}$$

The nullary cases are similar, and the axioms follow by universal properties.

This implication for LNL adjunctions was observed in [Ben95, §2.2.1]; LNL multicategories give a way to state and prove it even in the absence of $\times, 1$. Conversely:

**Proposition 3.4.** *The Eilenberg–Moore adjunction of any linear exponential comonad $\mathsf{I}$ determines an LNL multicategory with $\times, 1, \otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$, whose underlying linear exponential comonad recovers the given $\mathsf{I}$.*

*Proof.* Such an Eilenberg–Moore adjunction is an LNL adjunction (see [Ben95, §2.2.2] and [Mel09, §7]), hence an LNL multicategory with $\times, 1, \otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$.

Moreover, since *any subset of objects of a multicategory determines a sub-multicategory* (in stark contrast to the situation for monoidal categories), we still obtain an LNL multicategory with $\otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$ if we restrict to any subset of the $\mathsf{I}$-coalgebras containing the cofree ones. The smallest choice, of course, consists of exactly the cofree coalgebras, so we have:

**Corollary 3.5.** *The Kleisli adjunction of any linear exponential comonad $\mathsf{I}$ determines an LNL multicategory with $\otimes, \mathbb{1}, \mathsf{F}, \mathsf{U}$, whose underlying linear exponential comonad recovers the given $\mathsf{I}$.*

**Remark 3.6.** To include the Kleisli adjunction in the case when both categories are required to be monoidal, one has to assume that cofree coalgebras are closed under products. This follows for instance if the original monoidal category has products [Ben95, §2.2.3], in which case we recover the notion of **Seely comonad**, characterized by $\mathsf{I}A \otimes \mathsf{I}B \cong \mathsf{I}(A \& B)$. But LNL polycategories allow us to include the Kleisli case even when $\mathsf{I}$ doesn't exist.

There are also intermediate choices between the Eilenberg–Moore category (all coalgebras) and Kleisli category (cofree coalgebras), such as the category of finite products of cofree coalgebras (if $\mathcal{L}$ has finite products), or category of exponentiable coalgebras (if $\mathcal{L}$ is closed monoidal), as discussed in [Ben95, §2.2.2].

Here is another situation that LNL polycategories allow us to treat more generally.