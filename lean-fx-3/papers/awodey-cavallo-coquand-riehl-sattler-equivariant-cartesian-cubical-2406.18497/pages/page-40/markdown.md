*Proof.* By Lemma 3.5.1, the fibration $\pi: \dot{U} \to U$ gives rise to a reflexive relation $\operatorname{Eq}(\dot{U}) \rightrightarrows U$ for which the pairing $\operatorname{Eq}(\dot{U}) \to U \times U$ is a fibration. By Theorem 3.3.3, the equivalence extension property holds, so by Proposition 3.5.5 the map $t: \operatorname{Eq}(\dot{U}) \xrightarrow{\sim} U$ is a trivial fibration, and in particular a fibration. Now either Proposition 3.6.8 or 3.6.9 applies to conclude that $U$ is fibrant. $\square$

**3.7. Fibration extension property and 2-of-3.** Recall Definition 2.3.6, which introduces what it means for a premodel structure on a presheaf topos to have universes. We say that a premodel structure **has fibrant universes** if in addition the base of each of these universes for each sufficiently large inaccessible cardinal is fibrant.

The aim of this section will be to connect the fibrancy of the universes to a useful property of the premodel structure.

**Definition 3.7.1.** A premodel structure on a presheaf topos satisfies the **fibration extension property** just when, for each sufficiently large inaccessible cardinal $\kappa$, any $\kappa$-small fibration $p: X \to A$, and trivial cofibration $t: A \xrightarrow{\sim} B$, there exists a $\kappa$-small fibration over $B$ which pulls back to $p$ along $t$:

$$\begin{array}{ccc} X & \dashrightarrow & Y \\ p \downarrow & \downarrow^\perp & \downarrow^q \\ A & \xleftarrow[\text{t}]{} & B. \end{array}$$

There is a well-known connection between the fibration extension property and fibrancy of the universe [Shu15] that we spell out carefully because we are working with a somewhat different axiomatization here.

**Lemma 3.7.2.** *Any premodel structure on a presheaf topos with fibrant universes has the fibration extension property. Conversely, if a premodel structure with the fibration extension property has universes, then those universes have fibrant base objects.*

*Proof.* We first show that fibrant universes imply the fibration extension property. For any fibration $p: X \to A$, we have a classifying universe $\pi: \dot{U} \to U$ with fibrant base $U$. In particular, this choice defines a classifying map and thus a lifting problem

$$\begin{array}{ccc} A & \xrightarrow{\bar{p}} & U, \\ j \downarrow^\perp & \searrow^\pi & \\ B & & \end{array}$$

which admits a solution since $U$ is fibrant. The pullback of $\pi$ along this map, displayed below-right, defines a small fibration over $B$. The pullback square for $p$ factors through the one for $q$ defining the desired extension square:

$$\begin{array}{ccc} X & \xrightarrow{\quad} & Y \xrightarrow{\quad} & \tilde{U} \\ p \downarrow^\perp & \downarrow^\perp & q \downarrow^\perp & \downarrow^\pi \\ A & \xrightarrow{\quad} & B \xrightarrow{\bar{q}} & U. \\ & \xrightarrow{\bar{p}} & & \\ & & 40 \end{array}$$