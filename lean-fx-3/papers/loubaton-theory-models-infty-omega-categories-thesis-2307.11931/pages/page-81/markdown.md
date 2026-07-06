2.1. PRELIMINARIES

**2.1.2.2.** If $b$ is an object of $M$, we denote by $b_t$ the stratified presheaf $(b, S)$, where $S$ is the smaller stratification that includes $id : b \rightarrow b$.

We then define $t_M B$ as the full subcategory of $\mathrm{tPsh}_M(B)$ spanned by the objects of shape $a$ or $b_t$ with $a \in B$ and $b \in M$. We then have equalities:

$$\begin{aligned} \mathrm{Hom}_{t_M B}(a, b) &:= \mathrm{Hom}_B(a, b), \\ \mathrm{Hom}_{t_M B}(a, b_t) &:= \mathrm{Hom}_B(a, b), \\ \mathrm{Hom}_{t_M B}(a_t, b) &:= \mathrm{Hom}_B(a, b) \cap B_- \setminus \{id_a\}, \\ \mathrm{Hom}_{t_M B}(a_t, b_t) &:= \mathrm{Hom}_B(a, b) \cap B_-. \end{aligned}$$

The canonical functor $B \rightarrow t_M B$ is then fully faithful and we will identify object of $B$ with their image through this functor.

**Proposition 2.1.2.3.** *The category $t_M B$ admits a structure of elegant Reedy category, that makes the inclusion $B \rightarrow t_M B$ a morphism of Reedy category. There is no non trivial negative morphism whose codomain is of shape $b_t$ for $b \in M$. There is no non trivial positive morphism whose domain is of shape $b_t$ for $b \in M$.*

*Proof.* We define the degree degree function $ob(t_M B) \rightarrow \mathbb{N}$ by the assignment

$$d'(b) := 2d(b) \qquad d'(b_t) := 2d(b) + 1$$

The category $(t_M B)_+$ is the smallest that includes $B_+$ and morphisms of shape $a \rightarrow a_t$. The category $(t_M B)_-$ is the smallest that includes $B_-$ and morphisms of shape $b_t \rightarrow a$.

To prove the axioms of Reedy category, we can replicate the strategy used in proposition C.2 of [OR20b] with obvious modification to this more general framework.

We still have to show that $tB$ is elegant. Let $X$ be a presheaf on $t_M B$, $a$ an element of $t_M B$, $f : a \rightarrow a'$ and $g : a \rightarrow a'$ two negative morphisms, an element $x$ of $X(a)$, two non degenerate elements $y \in X(a')$ and $z \in X(a'')$ such that $f^*y = x$, $g^*z = x$.

Suppose first that $a$ is in $B$. In this case, $f$ and $g$ are also in $B$, and as this Reedy category is elegant by assumption, this implies $f = g$ and $y = z$. Suppose now that $a$ is of shape $b_t$ for $b \in B$. We denote $\alpha$ the canonical morphism $\alpha : b \rightarrow b_t$. By definition of negative morphism, the codomain of $f$ and $g$ are in $B$. The morphisms $\alpha f$ and $\alpha g$ then are in $B$. Moreover, these two morphisms are negative, and we have $(\alpha f)^*y = \alpha^*x$, $(\alpha g)^*z = \alpha^*x$. As $B$ is elegant, $\alpha f = \alpha g$ and $y = z$. Eventually, remark that the first equality implies that $f$ is equal to $g$. $\square$

A cellular model for $t_M B$ is given by $C \cup \{b \rightarrow b_t, b \in M\}$ where $C$ is a cellular model for $B$.

71