$R \times \{0 < 1 < 2\} / (r, 2) \to R^- \times \{0 < 1 < 2\} \to \mathcal{M}$ is a Reedy cofibrant diagram. Hence, applying theorem C.15, we can deduce that the map

$$\operatorname{Colim}_U T \to Z(r)$$

is a cofibration, where $U \subset R \times \{0 < 1 < 2\} / (r, 2)$ is the sieve containing all the objects except $(r, 1)$ and $(r, 2)$. But this map can be seen to be exactly

$$L_r Z \sqcup_{L_r X} X(r) \to Z(r)$$

by theorem C.12. This concludes the proof, as this can be applied to any object $r \in R$. $\square$

**Proposition C.19.** *Consider a cospan $Y \leftarrow X \to Z$ of diagram $R \to \mathcal{M}$, such that $X, Y, Z$ are all Reedy cofibrant and the arrow $X \to Y$ is a Reedy cofibration. Then the (level-wise) pushout $Y \sqcup_X Z$ exists in $\mathcal{M}^R$ and the natural transformation $Z \to Y \sqcup_X Z$ is a Reedy cofibration.*

*Proof.* It follows from theorem C.16 that for each $r \in R$ the three objects in the diagram $Y(r) \leftarrow X(r) \to Z(r)$ are cofibrant and the map $X(r) \to Y(r)$ is a cofibration, so the levelwise pushout $Y(r) \sqcup_{X(r)} Z(r)$ exists and by general category-theoretic results is functorial in $r$ and is a pushout in the category of diagrams $\mathcal{M}^R$. We only need to check that the map $Z(r) \to Y(r) \sqcup_{X(r)} Z(r)$ is a Reedy cofibration. For this observe that as colimits commute with colimits we have:

$$L_r(Y \sqcup_X Z) = \operatorname{Colim}_{r' \to r \in R^+} Y(r') \sqcup_{X(r')} Z(r') = L_r Y \sqcup_{L_r X} L_r Z$$

So that in the latching map

$$L_r(Y \sqcup_X Z) \sqcup_{L_r Z} Z \to Y \sqcup_X Z$$

the domain can be identified with

$$(L_r Y \sqcup_{L_r X} L_r Z) \sqcup_{L_r Z} Z = L_r Y \sqcup_{L_r X} Z = (L_r Y \sqcup_{L_r X} X) \sqcup_X Z$$

so the latching map is

$$(L_r Y \sqcup_{L_r X} X) \sqcup_X Z \to Y \sqcup_X Z$$

which is a pushout of the latching map $L_r Y \sqcup_{L_r X} X \to Y$. The latter map is itself a core cofibration since $X \to Y$ is a core Reedy cofibration. Hence, this concludes the proof. $\square$

153