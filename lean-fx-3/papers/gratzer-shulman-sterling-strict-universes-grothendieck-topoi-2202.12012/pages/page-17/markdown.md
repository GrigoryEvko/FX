STRICT UNIVERSES FOR GROTHENDIECK TOPOI

17

Because $\mathcal{D}$ is filtered, by Lemma 3.1.5 we may replace Diagram 10 as follows:

$$\begin{array}{c} \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} \xleftarrow{\quad} \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \operatorname{colim}_{d/\mathcal{D}} \{F(d)\} \xrightarrow{\quad} \operatorname{colim}_{d/\mathcal{D}} F \end{array}$$

Because filtered colimits commute with finite limits, it suffices to check that each of the following squares is cartesian for $e \geq d$:

$$\begin{array}{c} F(d) \xleftarrow{\quad} F(d) \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ F(d) \longrightarrow F(e) \end{array}$$

But we have already assumed $F(d) \longrightarrow F(e)$ to be a monomorphism. ■

3.1.9. REMARK. For any regular cardinal $\kappa \geq \omega$, a $\kappa$-filtered diagram [AR94, Remark 1.21] is filtered. Accordingly, both Lemmas 3.1.6 and 3.1.8 hold for $\kappa$-filtered diagrams.

3.1.10. LEMMA. Let $F, G: \mathcal{D} \longrightarrow \mathcal{E}$ be two diagrams such that $G$ satisfies descent, and let $F \longmapsto G$ be a cartesian monomorphism. Then the induced map $\operatorname{colim}_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} G$ is a monomorphism.

PROOF. We need to check that the following square is cartesian:

$$\begin{array}{c} \operatorname{colim}_{\mathcal{D}} F \xleftarrow{\quad} \operatorname{colim}_{\mathcal{D}} F \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \operatorname{colim}_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} G \end{array}$$

We can cover $\operatorname{colim}_{\mathcal{D}} F$ by $\coprod_{\mathcal{D}} F$; by descent of cartesian squares along covers, it suffices to prove that the outer square below is cartesian:

$$\begin{array}{c} \coprod_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} F \xleftarrow{\quad} \operatorname{colim}_{\mathcal{D}} F \\ \Big\| \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \coprod_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} G \\ \searrow \searrow \searrow \searrow \searrow \searrow \searrow \\ \coprod_{\mathcal{D}} G \end{array} \tag{11}$$