STRICT UNIVERSES FOR GROTHENDIECK TOPOI

43

PROOF. Unfolding definitions, we must show that $\delta_{E_{\mathcal{U}_0}} : U_{\mathcal{U}_0} \longrightarrow \mathsf{Eq}(E_{\mathcal{U}_0})$ is a trivial cofibration; as it is already a cofibration, it is enough to check that it is a weak equivalence. Consider Diagram 39 below exhibiting $\delta_{E_{\mathcal{U}_0}}$ as a section of the fibration $\partial_1 : \mathsf{Eq}(E_{\mathcal{U}_0}) \longrightarrow U_{\mathcal{U}_0}$:

$$\begin{array}{c} U_{\mathcal{U}_0} \xrightarrow{\delta_{E_{\mathcal{U}_0}}} \mathsf{Eq}(E_{\mathcal{U}_0}) \\ \Biggl\downarrow \quad \Biggl\downarrow \partial_1 \\ U_{\mathcal{U}_0} \end{array} \tag{39}$$

By the 2-out-of-3 property of weak equivalances, it therefore suffices to show that fibration $\partial_1 : \mathsf{Eq}(E_{\mathcal{U}_0}) \longrightarrow U_{\mathcal{U}_0}$ is a trivial fibration. To this end we fix a cofibration $A \longmapsto B$ to check the right lifting property for $\partial_1$:

$$\begin{array}{c} A \xrightarrow{(\beta, \alpha, w)} \mathsf{Eq}(E_{\mathcal{U}_0}) \\ \Biggl\downarrow \quad \Biggl\downarrow \partial_1 \\ B \xrightarrow{\bar{\alpha}} U_{\mathcal{U}_0} \end{array} \tag{40}$$

In Diagram 40 above, we have written $\beta, \alpha$ for the two codes $A \longrightarrow U_{\mathcal{U}_0}$ and $w : [\beta] \longrightarrow [\alpha]$ for the weak equivalence between the corresponding fibers of $\pi_{\mathcal{U}_0}$, writing $[\alpha]$ for the pullback of $\pi_{\mathcal{U}_0}$ along $\alpha$, etc.; then $\bar{\alpha}$ is an extension of the code $\alpha$ along the cofibration $A \longmapsto B$. Our goal is to provide similar extensions of $\beta, w$ to produce an equivalence between $B$-valued fibers of $\pi_{\mathcal{U}_0}$. Considering the fiber of $\pi_{\mathcal{U}_0}$ at $\bar{\alpha}$, we have a Kan fibration $[\bar{\alpha}] \longrightarrow B$ whose pullback along $A \longmapsto B$ is $[\alpha] \longrightarrow A$. We summarize the situation as follows:

$$\begin{array}{c} [\beta] \\ \searrow w \\ \searrow [\alpha] \\ \searrow g \\ \searrow \\ A \longmapsto B \end{array} \longrightarrow \begin{array}{c} [\bar{\alpha}] \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \seend{array} \tag{41}$$

Using Lemma 6.2.6, we can complete Diagram 41 as follows:

$$\begin{array}{c} [\beta] \xrightarrow{f} [\bar{\beta}] \\ \searrow w \\ \searrow [\alpha] \\ \searrow g \\ \searrow \\ A \longmapsto B \end{array} \longrightarrow \begin{array}{c} [\bar{\beta}] \\ \searrow \\ \bar{w} \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \searrow \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \sev \\ \end{array} \tag{42}$$