2.2. THE COMPLICIAL MODEL

**Proposition 2.2.2.13.** *For any marked simplicial sets $X, Y$, the morphism $\gamma_{X,Y}$ is a weak equivalence.*

*Proof.* The functor

$$t\Delta_{/X} \times t\Delta_{/Y} \to \mathrm{mPsh}(\Delta) \times \mathrm{mPsh}(\Delta) \xrightarrow{\gamma} \mathrm{Arr}(\mathrm{mPsh}(\Delta))$$

is Reedy cofibrant (definition 1.1.3.1). It is then enough to show the result for any couples of representables.

Let's start by the case $(X, Y) = ([n], [m])$. Let $s: X \star Y \to X \diamond Y$ be the morphism defined on objects by the formula:

$$s(k \star \emptyset) := (k, 0, 0) \quad s(\emptyset \star l) := (n, 1, l)$$

We have

$$\gamma_{X,Y} s = id \quad s\gamma_{X,Y}(k, \epsilon, l) = (k + \epsilon(n - k), \epsilon, \epsilon l).$$

Let $\eta: [n] \diamond [m] \to [n] \diamond [m]$ be induced by the application

$$(k, \epsilon, l) \mapsto (k, \epsilon, \epsilon l).$$

We are now going to construct two morphisms

$$\epsilon_0: ([n] \diamond [m]) \times [1]_t \to [n] \diamond [m] \quad \text{and} \quad \epsilon_1: ([n] \diamond [m]) \times [1]_t \to [n] \diamond [m]$$

such that

$$\epsilon_0(\_, 0) = \eta \quad \epsilon_0(\_, 1) = s\gamma_{X,Y}$$

$$\epsilon_1(\_, 0) = \eta \quad \epsilon_1(\_, 1) = id$$

The first one is induced on the level of simplicial sets by

$$(k, \epsilon, l, \alpha) \mapsto (k + \alpha\epsilon(n - k), \epsilon, \epsilon l),$$

and the second one by

$$(k, \epsilon, l, \alpha) \mapsto (k, \epsilon, (\epsilon \vee \alpha)l),$$

where $\epsilon \vee \alpha := \epsilon + \alpha - \epsilon\alpha$. These two morphisms extend to marked simplicial sets.

We proceed in a similar way with cases $(X, Y) = ([n]_t, [m]), ([n], [m]_t)$ or $([n]_t, [m]_t)$. $\square$

**Remark 2.2.2.14.** As we already now that functors $\_ \diamond X$ and $X \diamond \_$ preserve weak equivalences, the previous proposition implies that for any marked simplicial sets $X$, functors $\_ \star X$ and $X \star \_$ preserves weak equivalences and are then left Quillen functors.

**Construction 2.2.2.15.** Let $X$ be a marked simplicial set. We now describe an variation on the suspension. We define $\Sigma^* X$, as the following pushout:

$$\begin{array}{c} X \longrightarrow X \star [0] \\ \downarrow \qquad \qquad \downarrow \\ 1 \longrightarrow \Sigma^* X \end{array}$$

This assignation defines a cocontinuous functor $\Sigma^*: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{\partial[1]}$. Using proposition 2.2.2.13, all the vertical morphisms of the following diagram are weak equivalences:

$$\begin{array}{c} 1 \longleftarrow X \longrightarrow X \diamond 1 \\ \downarrow \qquad \downarrow \qquad \downarrow \\ 1 \longleftarrow X \longrightarrow X \star 1 \end{array}$$

75