Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:21

so that the universal property of $\mathsf{F}$ holds by definition. The rest is also similar to Proposition 3.1, using the result of [CS97] that a symmetric polycategory with $\otimes, \mathbb{1}, \mathfrak{A}, \bot$ is equivalently a symmetric linearly distributive category. The universal property of $\mathsf{F}$ relative to linear morphisms with arbitrary codomain ensures that it is uniquely determined by its action on underlying multicategories, while $\mathsf{U}$ knows nothing about the non-co-unary morphisms at all. $\square$

Note that since $\sqcup$ and $\cap$ can be defined in terms of $\mathsf{F}, \mathsf{U}, (\cdot)^*$ by $\sqcup X = (\mathsf{F}X)^*$ and $\cap A = \mathsf{U}(A^*)$, an LNL adjunction with $\mathcal{L}$ *-autonomous also has $\sqcup, \cap$. Thus, we have the following locally full sub-2-categories of LNLPoly:

- **Linearly distributive LNL adjunctions** and **-autonomous LNL adjunctions**, defined as in Proposition 3.15(iii).
- Linearly distributive LNL adjunctions with any desired limits and colimits in either category, subject to the restrictions that colimits must be preserved by the product or tensor product in each variable, and limits in the linearly distributive category must be preserved by the cotensor product in each variable.
- *-autonomous closed LNL adjunctions with any desired limits and colimits in either category.

On the other hand, if we add $\sqcup$ and $\cap$ *without* $(\cdot)^*$, the induced structure on $\mathcal{L}$ is also one that appears in the literature:

**Proposition 3.16.** *If $\mathcal{P}$ is an LNL polycategory with $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{F}, \mathsf{U}, \sqcup, \cap$, then $\mathcal{P}^{\mathsf{L}}$ is a (symmetric) linearly distributive category with storage [BCS96].*

*Proof.* Note that any LNL polycategory $\mathcal{P}$ has an underlying LNL multicategory $\text{LNLMULTI}^*(\mathcal{P})$ containing all the objects, all the nonlinear morphisms, but only the co-unary linear morphisms. It also has a **linear opposite** $\mathcal{P}^{\text{L-op}}$ in which the nonlinear morphisms are the same, but $\mathcal{P}^{\text{L-op}}(\Theta \mid \Gamma; \Delta) = \mathcal{P}(\Theta \mid \Delta; \Gamma)$.

Thus, applying Proposition 3.3 to $\text{LNLMULTI}^*(\mathcal{P})$ and $\text{LNLMULTI}^*(\mathcal{P}^{\text{L-op}})$, we obtain a linear exponential comonad $! = \mathsf{FU}$ and a linear exponential monad $? = \sqcup, \cap$, so it remains only to show that $?$ is a $!$-strong monad and dually. We obtain the morphism $?A \otimes !B \rightarrow ?(A \otimes !B)$ by acting on the $\cap$-universal morphism of $(\cap(A \otimes \mathsf{FUB}) \mid) \rightarrow A \otimes \mathsf{FUB}$ as follows.

$$\begin{aligned} \mathcal{P}(\cap(A \otimes \mathsf{FUB}) \mid A \otimes \mathsf{FUB};) &\xrightarrow{\sim} \mathcal{P}(\cap(A \otimes \mathsf{FUB}) \mid A, \mathsf{FUB};) \\ &\xrightarrow{\sim} \mathcal{P}(\cap(A \otimes \mathsf{FUB}), \mathsf{UB} \mid A;) \\ &\xrightarrow{\sim} \mathcal{P}(\cap(A \otimes \mathsf{FUB}), \mathsf{UB}; \cap A) \\ &\rightarrow \mathcal{P}(\cap(A \otimes \mathsf{FUB}), \mathsf{UB} \mid \sqcup A;) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \sqcup A, \mathsf{FUB}; \sqcup(A \otimes \mathsf{FUB})) \\ &\xrightarrow{\sim} \mathcal{P}(\mid \sqcup A \otimes \mathsf{FUB}; \sqcup(A \otimes \mathsf{FUB})) \\ &= \mathcal{P}(\mid ?A \otimes !B; ?(A \otimes !B)). \end{aligned}$$

The noninvertible map above is composition with the $\sqcup$-universal $(\cap A \mid \sqcup A) \rightarrow ()$. It is straightforward to check the axioms. (This is like the proof in [BCS96, §3.1] that proof nets with storage boxes form a linearly distributive category with storage.) $\square$

The converse of Proposition 3.16 is subtler. If $\mathcal{L}$ is a symmetric linearly distributive category with storage, it is in particular a symmetric monoidal category (under $\otimes, \mathbb{1}$) with a