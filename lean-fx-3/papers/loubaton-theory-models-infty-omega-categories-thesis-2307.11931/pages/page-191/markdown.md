4.1. PRELIMINARIES

is an equivalence. The previous square is then equivalent to the square

$$\begin{array}{c} \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}(C)_{L} \times_{C} \operatorname{Arr}_{R}(C) \times_{C} \operatorname{Arr}_{R}(C) \xrightarrow{\nabla \times_{C} \operatorname{Arr}_{R}(C) \times_{C} \operatorname{Arr}_{R}(C)} \operatorname{Arr}(C)_{L} \times_{C} \operatorname{Arr}_{R}(C) \times_{C} \operatorname{Arr}_{R}(C) \\ \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{L}(C) \times_{C} \nabla \Bigg\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{R}(C) \xrightarrow{\nabla \times_{C} \operatorname{Arr}_{R}(C)} \operatorname{Arr}_{L}(C) \times_{C} \operatorname{Arr}_{R}(C) \end{array}$$

which is obviously cartesian.

**Proposition 4.1.2.12.** *The $\infty$-groupoid $L$ is stable under colimit, retract, composition, and left cancellation. The $\infty$-groupoid $R$ is stable under limit, retract, composition, and right cancellation.*

*Proof.* Let $p : b \to d$ be a morphism of $R$ and $\{i_j : a_j \to c_j\}_{j:J}$ a family of morphisms of $L$ indexed by a functor $J \to \operatorname{Arr}_L(C)$, admitting a colimit $\bar{i} : \bar{a} \to \bar{c}$. Both functors $r \mapsto \operatorname{Sq}(r, p)$ and $c \mapsto \operatorname{Hom}(c, b)$ send colimits on limits. This implies that the morphism

$$\operatorname{Hom}(\bar{c}, b) \to \operatorname{Sq}(\bar{i}, p)$$

is the limit in $\operatorname{Arr}(\operatorname{Sp})$ of the family of morphisms

$$\operatorname{Hom}(c_j, b) \to \operatorname{Sq}(i_j, p).$$

Each of these morphisms is an equivalence by assumption, so that implies that $\operatorname{Hom}(\bar{c}, b) \to \operatorname{Sq}(\bar{i}, p)$ is an equivalence. As this is true for any $p$ in $R$, proposition 4.1.2.10 implies that $\bar{i}$ is in $L$.

Consider now a retract diagram:

$$\begin{array}{c} a \xrightarrow{id} a' \xrightarrow{} a \\ \downarrow i \qquad \qquad \downarrow i' \qquad \qquad \downarrow i \\ c \xrightarrow{id} c' \xrightarrow{} c \end{array}$$

such that $i'$ is in $L$. For any morphism $p : b \to d$ of $R$, this induces a retract diagram

$$\begin{array}{c} \operatorname{Hom}(c, b) \xrightarrow{id} \operatorname{Hom}(c', b) \xrightarrow{} \operatorname{Hom}(c, b) \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \\ \operatorname{Sq}(i, p) \xrightarrow{id} \operatorname{Sq}(i', p) \xrightarrow{} \operatorname{Sq}(i, p) \end{array}$$

As equivalences are stable under retract, $\operatorname{Hom}(c, b) \to \operatorname{Sq}(i, p)$ is an equivalence, and as it is true for any $p$ in $R$, $i$ is in $L$.

For the cloture under left cancellation, this is proposition 4.1.2.3.

We proceed similarly for the dual assertion.

181