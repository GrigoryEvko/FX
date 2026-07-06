#### A.4 The category of generalized $\kappa$-algebraic theories

We construct a category where the objects are generalized $\kappa$-algebraic theories with maps *interpretations*. This is analogous to the category that Cartmell constructs in [Car78, 1.11], all the results can be copied from there to our setting. Since we work with different theories, the alphabets, expressions and rules are marked accordingly. If $T$ is a theory then these sets are denoted $Alp(T)$, $Exp(T)$, $Rul(T)$ respectively.

Let $T$ and $T'$ two generalized $\kappa$-algebraic theories. Let $I: Alp(T) \rightarrow Exp(T')$ be a function. Using this function, we can define a *preinterpretation* $\bar{I}: Exp(T) \rightarrow Exp(T')$ by induction on the construction of expressions:

1. If $x \in V$

$$\bar{I}(x) := x,$$

2. If $F \in Alp(T)$

$$\bar{I}(F) := I(F),$$

3. If $L \in Alp(T)$ is an alphabet symbol and $\{t_\alpha\}_{\alpha < \lambda}$ are expressions

$$\bar{I}(L(t_\alpha)_{\alpha < \lambda}) := I(L)(\bar{I}(t_\alpha))_{\alpha < \lambda}.$$

**Definition A.24.** Given a preinterpretation $\bar{I}$ we define a new function $\hat{I}: Rul(T) \rightarrow Rul(T')$.

1. $\hat{I}(\Gamma \vdash \Delta \text{ Type}) := \bar{I}(\Gamma) \vdash \bar{I}(\Delta) \text{ Type}$
2. $\hat{I}(\Delta \vdash t : \Delta) := \bar{I}(\Delta) \vdash \bar{I}(t) : \bar{I}(\Delta)$
3. $\hat{I}(\Delta, \Delta' \vdash \Delta \equiv \Delta') := \bar{I}(\Delta), \bar{I}(\Delta') \vdash \bar{I}(\Delta) \equiv \bar{I}(\Delta').$
4. $\hat{I}(\Delta, t, t' : \Delta \vdash t \equiv_\Delta t') := \bar{I}(\Delta), \bar{I}(t), \bar{I}(t') : \bar{I}(\Delta) \vdash \bar{I}(t) \equiv_{\bar{I}(\Delta)} \bar{I}(t').$

This function is an *interpretation* from $T$ into $T'$ if all introductory judgments and axioms of $T$ are sent to derived rules of $T'$, we will simply denote this as $I: T \rightarrow T'$.

Just as in [Car78] it is possible to prove that:

**Lemma A.25.** *If $I$ is an interpretation from $T$ to $T'$, then it preserves the derived judgments of the theory $T$.*

102