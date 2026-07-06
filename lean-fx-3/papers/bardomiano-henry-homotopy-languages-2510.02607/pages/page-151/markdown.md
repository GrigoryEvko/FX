**Corollary C.15.** *Let $I$ be a finite direct category, and let $X : I \to \mathcal{M}$ be a Reedy cofibrant diagram and $U \subset I$ be a sieve, then $\mathsf{Colim}_I X$ and $\mathsf{Colim}_U X$ exist, are cofibrant and the obvious comparison map $\mathsf{Colim}_U X \to \mathsf{Colim}_I X$ is a cofibration.*

*If furthermore the latching map $L_r X \to X(r)$ is a trivial cofibration for each $r \in I - U$, then the map $\mathsf{Colim}_U X \to \mathsf{Colim}_I X$ is a trivial cofibration.*

*Proof.* By theorem C.14 all the latching objects of $X$ are cofibrant, so we can simply apply theorem C.13 and conclude. $\square$

**Corollary C.16.** *Let $R$ be a locally finite Reedy category.*

- *Any core (trivial) Reedy cofibration $X \to Y$ in $\mathcal{M}^R$ is in particular a levelwise (trivial) cofibration. That is, the map $X(r) \to Y(r)$ are (trivial) cofibrations for any $r \in R$.*
- *A map $X \to Y$ in $\mathcal{M}^R$ which is both a core Reedy cofibration and a level-wise weak equivalence is a trivial Reedy cofibration.*

Dually, the same is true for fibrations and trivial fibrations.

*Proof.* As both statement only depends on the restriction to the subcategory $R^+$, we can freely assume that $R$ is a (locally finite) direct category. In both cases, we consider the natural transformation $X \to Y$ as a diagram $T : R \times \{0 < 1\} \to \mathcal{M}$. We then observe that the latching map of $T$ at an object $(r, 0)$ is just $L_r X \to X$, and the latching map of $T$ at $(r, 1)$ is

$$L_r Y \sqcup_{L_r X} X(r) \to Y(r)$$

Hence the assumption that $X \to Y$ is a core Reedy cofibration translates into the fact that $T$ is Reedy cofibrant. For any object $r \in R$, the composite $R \times \{0 < 1\}/(r, 1) \to R \times \{0 < 1\} \to \mathcal{M}$ is immediately seen to be Reedy cofibrant as well, and we can then apply theorem C.15 to the sieve $U = R/r \times \{0\}$ to conclude that $X(r) \to Y(r)$ is a cofibration.

If $X \to Y$ is further assumed to be trivial, then the latching map of $T$ at all objects of the form $(r, 1)$ are trivial, and hence using the “trivial” case of theorem C.15, we conclude that $X(r) \to Y(r)$ is trivial.

If instead we assume that $X(r) \to Y(r)$ is a weak equivalence for all $r$, then we proceed by strong induction on $\deg(r)$. Assume that we already know that at all $k$ such that $\deg(k) < \deg(r)$.

151