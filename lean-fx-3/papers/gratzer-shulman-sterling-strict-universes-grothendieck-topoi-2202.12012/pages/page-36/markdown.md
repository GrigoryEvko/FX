36

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The Grothendieck school then develops both a *global* and a *local* recollement theory for the open-closed partition $(\mathcal{X}_{/J}, \mathcal{X}_{*J})$ of $\mathcal{X}$:

5.2.1. GLOBAL RECOLLEMENT [AGV72]. The topos $\mathcal{X}$ may be reconstructed from its open and closed subtopoi as the comma category $\mathcal{X}_{*J} \downarrow i^* j_*$, i.e. the Artin gluing of $i^* j_*$. In other words, the diagram below is pseudocartesian in the (very large) bicategory of all categories, in which the upper functor $q: \mathcal{X} \longrightarrow \mathcal{X}_{*J}$ sends an object $E$ to the morphism $i^*(\eta_E: E \longrightarrow j_* j^* E)$ in $\mathcal{X}_{*J}$.

$$\begin{array}{ccc} \mathcal{X} & \xrightarrow{q} & \mathcal{X}_{*J} \\ j^* & \downarrow & \downarrow \text{cod}_{\mathcal{X}_{*J}} \\ \mathcal{X}_{/J} & \xrightarrow{i^* j_*} & \mathcal{X}_{*J} \end{array} \blacksquare$$

From the global recollement of the topos $\mathcal{X}$ from its open and closed subtopoi, the Grothendieck school concludes a *local* recollement or *fracture theorem* that reconstructs an object of the topos from its components over the open and closed subtopoi.³

5.2.2. LOCAL RECOLLEMENT [AGV72]. Under the same assumptions, any object $E$ of $\mathcal{X}$ may be reconstructed from its restrictions $j^* E, i^* E$ to the open and closed subtopoi respectively. In particular, the following diagram is cartesian in $\mathcal{X}$:

$$\begin{array}{ccc} E & \xrightarrow{\eta_E} & i_* i^* E \\ \eta_E & \downarrow & \downarrow i_* i^* \eta_E = i_* q E \\ j_* j^* E & \xrightarrow{\eta_{j_* j^* E}} & i_* i^* j_* j^* E \end{array} \blacksquare$$

The above follows immediately from the global recollement (Section 5.2.1); conversely, if $O: \mathcal{X}_{/J}$ is an object of the open subtopos and $p: K \longrightarrow i^* O: \mathcal{X}_{*J}$ is a family of objects in the closed subtopos, then the pullback of the latter along $O \longrightarrow i_* j^* O$ in $\mathcal{X}$ is a morphism $E \longrightarrow j_* O$ that is *isomorphic* to the unit $E \longrightarrow j_* j^* E$:

$$\begin{array}{ccc} E & \longrightarrow & i_* K \\ \downarrow & \downarrow & \downarrow i_* p \\ j_* j^* E & \eta_{j_* O}^*(i_* p) & \downarrow \\ \downarrow & \downarrow & \downarrow i_* i^* j_* O \\ j_* O & \xrightarrow{\eta_{j_* O}} & \end{array} \tag{37}$$

³Such a fracture theorem is developed in much greater generality for left exact modalities by Rijke, Shulman, and Spitters [RSS20].