16

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

Lemma 3.1.5, noting that $\operatorname{colim}_{d/\mathcal{D}} H = \operatorname{colim}_{\mathcal{D}} H$ for any diagram $H: \mathcal{D} \to \mathcal{E}$.

$$\begin{array}{ccc} G(d) & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} G \\ \downarrow & & \downarrow \\ F(d) & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} F \end{array} \tag{8}$$

We observe that any object is the colimit of the constant $d/\mathcal{D}$-diagram it determines as $d/\mathcal{D}$ is connected; therefore we may rewrite Diagram 8 as follows:

$$\begin{array}{ccc} \operatorname{colim}_{d/\mathcal{D}} \{G(d)\} & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} G \\ \downarrow & & \downarrow \\ \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} & \longrightarrow & \operatorname{colim}_{d/\mathcal{D}} F \end{array}$$

Recall that filtered colimits commute with finite limits, so it suffices to check that the following square below is cartesian for $d \to e$:

$$\begin{array}{ccc} G(d) & \longrightarrow & G(e) \\ \downarrow & & \downarrow \\ F(d) & \longrightarrow & F(e) \end{array} \tag{9}$$

But Diagram 9 is cartesian because we have assumed that $G \to F$ is cartesian. ■

We recall the notion of *ideal diagram* from Awodey and Forssell [AF05].

3.1.7. DEFINITION. *An ideal diagram in a category $\mathcal{E}$ is a functor $\mathcal{D} \to \mathcal{E}$ where $\mathcal{D}$ is a small filtered preorder and the image of each $d \leq e$ is a monomorphism in $\mathcal{E}$.*

3.1.8. LEMMA. *If $F: \mathcal{D} \to \mathcal{E}$ is an ideal diagram, then each edge $F(d) \to \operatorname{colim}_{\mathcal{D}} F$ in its colimit cocone is a monomorphism.*

PROOF. This follows for essentially the same reason as Lemma 3.1.6. Fixing $d \in \mathcal{D}$, to see that $F(d) \to \operatorname{colim}_{\mathcal{D}} F$ is a monomorphism it suffices to check that the following diagram is cartesian:

$$\begin{array}{ccc} F(d) & = & F(d) \\ \downarrow & & \downarrow \\ F(d) & \longrightarrow & \operatorname{colim}_{\mathcal{D}} F \end{array} \tag{10}$$