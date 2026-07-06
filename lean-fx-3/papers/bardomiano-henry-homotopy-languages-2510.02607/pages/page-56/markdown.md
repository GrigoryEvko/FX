such equality is salvaged in $\mathbb{L}^{Iso}$ thanks to the dependencies. On the other hand, a Street fibration is a formula in $\mathbb{L}^{Fun}$. We also know that the two Reedy model structures on the category $\mathbf{Cat}^{[1]}$ are Quillen equivalent. The above result can also be automatically obtained as an elementary application of $4^{th}$ invariance theorem, whose proof is the heart of the next section.

## 4 Language invariance under Quillen equivalences

### 4.1 The third and fourth invariance theorem

The main goal of this section is to show two more invariance properties of the first order language from section 2.4, that we can phrase informally$^4$ as:

1. $3^{rd}$ invariance theorem: If two cofibrant objects $X$ and $Y$ are equivalent, then any formula in context $X$ can be translated into a formula in context $Y$.
2. $4^{th}$ invariance theorem: If two (weak) model categories $\mathcal{M}$ and $\mathcal{N}$ are Quillen equivalent, then any formula in the language of $\mathcal{M}$ can be translated into a formula in the language of $\mathcal{N}$.

These “translations” are equivalent to the original formula in the sense that they are interpreted in the same way in any fibrant model, but they might not be equivalent in the more syntactic sense introduced in theorem 2.10. More precisely, we introduce the following equivalence relation on formulas:

**Definition 4.1.** Let $A$ be a cofibrant object of $\mathcal{M}$. Two formulas $\phi, \psi \in \mathbb{L}^M_\lambda(A)$ are said to be *semantically equivalent* if for all fibrant objects $X \in \mathcal{M}$ we have $|\phi|_X = |\psi|_X$. In this situation we write $\phi \approx \psi$.

We define $h\mathbb{L}^M_\lambda(A)$ to be the quotient of $\mathbb{L}^M_\lambda(A)$ by the relation $\approx$. We easily check that this is still a Boolean algebra.

By definition of $\approx$ we have that for $\phi, \psi \in \mathbb{L}^M_\lambda(\Gamma)$, $\phi \approx \psi$ if and only if all maps $v : \Gamma \to X$ with $X$ fibrant

$$\Gamma \vdash \phi(v) \Leftrightarrow \Gamma \vdash \psi(v).$$

We can now state our theorems.

### Theorem 4.2.

---$^4$The precise statement is just below as theorem 4.2.

56