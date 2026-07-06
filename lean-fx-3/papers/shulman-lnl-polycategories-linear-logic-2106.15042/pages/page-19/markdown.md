Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:19

in which the map $X \times TA \rightarrow T(X \times A)$ is the monad strength.

**Proposition 3.12.** *Any strong monad $T$ on a cartesian monoidal category $\mathcal{E}$ induces an LNL multicategory $\mathcal{P}$ with $\mathcal{P}^{\mathrm{NL}} = \mathcal{E}$, whose linear objects are the $T$-algebras, with*

$$\begin{aligned} \mathcal{P}(\Theta \mid ; A) &= \mathcal{E}(\Theta; A) \\ \mathcal{P}(\Theta \mid A; B) &= \{(\times \Theta)\text{-indexed families of algebra maps } A \rightarrow B\} \end{aligned}$$

*and all other linear homsets empty.*

(Here by $\times \Theta$ we mean the cartesian product of all the objects in $\Theta$, or the terminal object if $\Theta$ is empty.)

This LNL multicategory is **linearly subunary**, i.e. all its linear morphisms have linear codomain of length 1 (since it is an LNL multicategory) and linear domain of length $\leq 1$. It has $\times, 1, \cup$, and also an $\mathsf{F}$ with a weaker universal property:

$$\mathcal{P}(\Theta, X \mid ; B) \cong \mathcal{P}(\Theta \mid \mathsf{F}X; B). \tag{3.1}$$

This is similar to the restriction on $\top, 0$ in multicategories from Section 2. It implies there is a $\mathbb{1}$ (namely $\mathsf{F}1$) with a similarly restricted universal property. Conversely, from $\times$ and a restricted $\mathbb{1}$, we can construct a restricted $\mathsf{F}$ as $\mathsf{F}X = X \times \mathbb{1}$.

These LNL multicategories provide semantics for “call-by-push-value” [Lev03] and related theories. In this case, they are usually described as *enriched adjunctions*, analogously to the definition of LNL adjunctions as *monoidal* adjunctions. To explain this, recall that if $\mathcal{E}$ is cartesian monoidal, its Yoneda embedding $\mathcal{E} \hookrightarrow [\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$ is fully faithful and preserves products; thus any $\mathcal{E}$-enriched category can be regarded as an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched one. In addition, $\mathcal{E}$ itself is always $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched, with hom-presheaves $\underline{\mathcal{E}}(A, B)(X) = \mathcal{E}(X \times A, B)$.

**Proposition 3.13.** *A linearly subunary LNL multicategory with $\times, 1$ is uniquely determined by a **CBPV pre-structure** [Lev03]: a cartesian monoidal category $\mathcal{E}$, a category $\mathcal{L}$ enriched over $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$, and an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched functor $R : \mathcal{L} \rightarrow [\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$. Moreover:*

- (i) *The modality $\cup$ exists if and only if $R$ lands inside $\mathcal{E}$.*
- (ii) *If $\cup$ exists, then $\mathsf{F}$ exists with restricted universal property (3.1) if and only if $R : \mathcal{L} \rightarrow \mathcal{E}$ has an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched left adjoint.*
- (iii) *The hom-objects of $\mathcal{L}$ lie in $\mathcal{E}$ if and only if $\rightarrow$ exists.*
- (iv) *$\mathcal{L}$ has $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched powers by representables if and only if $\rightarrow$ exists.*
- (v) *$\mathcal{L}$ has $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched copowers by representables if and only if $\times$ exists.*
- (vi) *$\mathcal{L}$ has $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched finite products if and only if $\mathcal{&}, \top$ exist with a restricted universal property respecting the arity restrictions.*
- (vii) *$\mathcal{E}$ is distributive [CLW93] and the hom-presheaves of $\mathcal{L}$ preserve finite coproducts if and only if $+, \emptyset$ exist with a restricted universal property.*

*Proof.* Of course, $\mathcal{E}$ corresponds to $\mathcal{P}^{\mathrm{NL}}$, which is cartesian monoidal if and only if $\times, 1$ exist. The arity restrictions then ensure that the linear hom-sets are uniquely determined by those of the form $\mathcal{P}(X \mid A; B)$ and $\mathcal{P}(X \mid ; B)$. The former assemble into an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched category $\mathcal{L}$, and the latter into the functor $R$.

To say that $R$ lands in $\mathcal{E}$ is to say that each functor $X \mapsto \mathcal{P}(X \mid ; B)$ is representable, which is to say that $\cup$ exists. Given this, (3.1) says exactly that $\mathsf{F}$ is an $[\mathcal{E}^{\mathrm{op}}, \mathsf{Set}]$-enriched left adjoint of $\cup$. The other claims follow by similar comparisons of universal properties. $\square$