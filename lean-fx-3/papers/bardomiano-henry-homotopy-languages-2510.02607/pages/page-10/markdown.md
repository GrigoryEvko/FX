The collection of all formulas $\{\mathcal{L}_{\lambda}^{T}(\Gamma)\}_{\Gamma \in T}$ is what we call *the language of $T$*. Often, we will simply refer to it by $\mathcal{L}_{\lambda}^{T}$.

*Remark 2.2.* The key point in theorem 2.1 is that we are not including atomic formulas other than $\top$ and $\bot$. In particular, the language *does not include any equality*. At this point it might be unclear how we get non-trivial formulae in this language as it seems that applying quantifiers, conjunction or disjunction to formulas that are either $\bot$ or $\top$ will never produce any formulas that are not immediately interpreted as $\bot$ or $\top$. Or even, on how we might obtain formulas with free variables. The central idea is that free variables appear thanks to the fact we quantify over dependent types, that is, types in which free variables can appear. The following examples will demonstrate these phenomena.

**Example 2.3.** Let $Cat$ be the generalized $\omega$-algebraic theory of categories as introduced in theorem A.7. Then, in the context $(x : \mathsf{Ob})$ we can write the formula

$$\phi(x) := (\forall y : \mathsf{Ob}, \exists f : \mathsf{Hom}(x, y), \top)$$

which expresses that for any object $y$ there is an arrow from $x$ to $y$. This simply means that $x$ is a weakly initial object. Indeed, $\top$ is a formula in context $(x : \mathsf{Ob}, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y))$, so that $\exists f : \mathsf{Hom}(x, y), \top$ is a formula in context $(x : \mathsf{Ob}, y : \mathsf{Ob})$, and $\forall y : \mathsf{Ob}, \exists f : \mathsf{Hom}(x, y), \top$ is a formula in context $(x : \mathsf{Ob})$.

The logic is still not strong enough to express many of the interesting category theoretic notions. For example, without any kind of equality predicate on morphisms there is no way to write down a formula for an initial object, or a limit. In the next example, we show how modifying the theory $Cat$ allows the recovery of equality on morphisms:

**Example 2.4.** We consider the theory $Cat_{\equiv}$ obtained by adding to the theory $Cat$ the following:

$$\begin{aligned} &x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y) \vdash \mathsf{Eq}(f, g) \text{Type} \\ &x, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash r_f : \mathsf{Eq}(f, f) \\ &x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash f \equiv g \\ &x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash a \equiv r_f \end{aligned}$$

One can easily see that a model of $Cat_{\equiv}$ is just a category, with the type $\mathsf{Eq}(f, g)$ being empty if $f \neq g$ and $\{r_f\}$ if $f = g$. In this new theory, we can

10