(3) For any arrow $f : U \rightarrow V$, if for all $c \in \mathcal{C}$, $\operatorname{Hom}(c, f) : \operatorname{Hom}(c, U) \rightarrow \operatorname{Hom}(c, V)$ is a bijection, then $f$ is an isomorphism.

Then, $\mathcal{A}$ is locally $\kappa$-presentable and up to equivalence, $\mathcal{C}$ is the category of $\kappa$-presentable objects of $\mathcal{A}$.

Proof. This is essentially the definition of a locally presentable categories, depending on the reference. We just briefly recall the argument: for any object $X \in \mathcal{A}$, we let

$$Y = \operatorname{Colim}_{\substack{c \rightarrow X \\ c \in \mathcal{C}}} c,$$

as $\mathcal{C}$ has all $\kappa$-small colimits, this is a $\kappa$-filtered colimit. As every object $d \in \mathcal{C}$ is $\kappa$-presentable we have that $\operatorname{Hom}(d, Y) = \operatorname{Colim}_{c \rightarrow X} \operatorname{Hom}(d, c) = \operatorname{Hom}(d, X)$, hence the last condition implies that the canonical map $Y \rightarrow X$ is an isomorphism. So, $\mathcal{C}$ is a dense subcategory of $\kappa$-presentable objects, hence $\mathcal{A}$ is locally $\kappa$-presentable. Finally, if $X$ is a $\kappa$-presentable object then as $X$ is a $\kappa$-directed colimits of objects of $\mathcal{C}$, then $X$ is a retract of an object in $\mathcal{C}$, and as $\mathcal{C}$ has all $\kappa$-small colimits, it is closed under retracts, so that $X$ is isomorphic to an object of $\mathcal{C}$. □

### 3 Proof of Theorem 1.3.

The equivalence between condition (A2) and condition (A3) of Theorem 1.3 follows immediately from Proposition 1.1 and the remarks right after its proof. The implication (A1) $\Rightarrow$ (A2) is tautological, so we only need to show (A2) $\Rightarrow$ (A4) and (A4) $\Rightarrow$ (A1). But before this, we need to discuss the notion of well-founded categories which appear in condition (A4).

#### 3.1 Well-founded categories

The class **Ord** of all ordinal is seen as a (large) category with a single arrow from $\beta \rightarrow \gamma$ if $\gamma \leqslant \beta$. Any ordinal $\alpha$ is seen as the small full subcategory $\alpha \subset \mathbf{Ord}$ of all ordinals $\beta < \alpha$.

We first need to introduce the following construction, which plays a central role both in the notion of well-founded categories and latter in the proof of Theorem 1.3.

**3.1 Construction.** Given $I$ a category and $\alpha$ either an ordinal or the large category **Ord** of all ordinal, we denote by $I^{(\alpha)}$ the non-full subcategory of $I \times \alpha$ which contains all the object of $I \times \alpha$ and in which the morphisms are:

1. (1) All arrows $(x, \beta) \rightarrow (y, \gamma)$ in $I \times \alpha$ if $\beta < \gamma$.
2. (2) Only the identity arrow $(x, \beta) \rightarrow (x, \beta)$.

The projection $I \times \alpha \rightarrow I$ restrict to a functor $I^{(\alpha)} \rightarrow I$ which we call the canonical functor.

It should be noted that the construction $I \mapsto I^{(\alpha)}$ is not functorial in the bicategorical sense, but only in a 1-categorical sense, as it explicitly involve the set of objects of $I$. This construction does not respect the “equivalence

8