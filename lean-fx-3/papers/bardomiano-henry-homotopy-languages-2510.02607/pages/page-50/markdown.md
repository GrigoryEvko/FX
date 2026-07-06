4. A map $f : X \to Y$ between Segal spaces is a fibration (weak equivalence) if and only if is a Reedy fibration (Reedy weak equivalence).

Recall that $\mathcal{J}$ denotes the category with two objects and two arrows that are mutually inverses. It is usual to denote by $E(1)$ to the Segal space which is obtained by considering the nerve $N\mathcal{J}$ as a discrete simplicial space. This produces a map $F(1) \to E(1)$.

**Theorem 3.34.** *The category admits a unique simplicial model category structure such that:*

1. The cofibrations are the monomorphisms.
2. Fibrant objects are Segal spaces $X$ such that the map

$$Map(E(1), X) \to Map(F(0), X)$$

is a Kan equivalence. The fibrant objects are called complete Segal spaces.

3. The weak equivalences are the maps $f : X \to Y \in \mathbf{ssSet}$ such that

$$Map(f, W) : Map(Y, W) \to Map(X, W)$$

is a Kan equivalence for every complete Segal space $W$.

4. A map $f : X \to Y$ between complete Segal spaces is a fibration (weak equivalence) if and only if is a Reedy fibration (Reedy weak equivalence).

These models are cofibrantly generated. The set of generating cofibrations can be described using the box product [JT07, Proposition 2.2]. This set is given by $\hat{I} := \{d_m \hat{\square} d_n | m, n \in \mathbb{N}\}$. Explicitly, a map in $\hat{I}$ is of the form

$$d_m \hat{\square} d_n : \partial \Delta[m] \square \Delta[n] \coprod_{\partial \Delta[m] \square \partial \Delta[n]} \Delta[m] \square \partial \Delta[n] \to \Delta[m] \square \Delta[n]$$

We can obtain the generalized algebraic theory for (complete) Segal space. The domains of these maps provide the context in which a new type is formed. To get a sense of the theory, consider the following picture of a

50