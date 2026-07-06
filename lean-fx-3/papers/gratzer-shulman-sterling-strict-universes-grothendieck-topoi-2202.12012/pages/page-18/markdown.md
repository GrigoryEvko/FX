18

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

We have factored the downstairs map of Diagram 11 using the universal property of the coproduct. Our strategy to show that Diagram 11 is cartesian is to exhibit it as the pasting of two cartesian squares, as hinted by our factorization. In particular, by pasting pullbacks it is enough to prove that the right-hand square below is cartesian:

$$\begin{array}{ccc} \coprod_{\mathcal{D}} F & \longrightarrow & \coprod_{\mathcal{D}} F \longrightarrow \operatorname{colim}_{\mathcal{D}} F \\ \updownarrow & & \downarrow \\ \coprod_{\mathcal{D}} F & \longmapsto & \coprod_{\mathcal{D}} G \longrightarrow \operatorname{colim}_{\mathcal{D}} G \end{array} \quad (12)$$

The left-hand square of Diagram 12 can be seen to be cartesian using our assumption that $F \longmapsto G$ is a monomorphism. To see that the right-hand square is cartesian, we will use our descent hypothesis for $G$. In particular, it suffices to check that each of the squares below is cartesian:

$$\begin{array}{ccc} F(d) & \longrightarrow & \operatorname{colim}_{\mathcal{D}} F \\ \updownarrow & & \updownarrow \\ G(d) & \longrightarrow & \operatorname{colim}_{\mathcal{D}} G \end{array}$$

But this is exactly the condition that $G: \mathcal{D} \longrightarrow \mathcal{E}$ have descent.

3.2. COMPACT OBJECTS AND RELATIVELY COMPACT MAPS. We recall some of the theory of compact objects. We refer the reader to Adámek and Rosický [AR94] for a detailed exposition of compact objects and locally presentable categories.

3.2.1. DEFINITION. An object $X \in \mathcal{E}$ is said to be $\kappa$-compact when the functor $\operatorname{Hom}_{\mathcal{E}}(X, -)$ preserves $\kappa$-filtered colimits. Following Lurie [Lur09], a morphism $X \longrightarrow Y$ is said to be relatively $\kappa$-compact if for each $\kappa$-compact object $Z$ and morphism $Z \longrightarrow Y$, the pullback $Z \times_Y X$ is $\kappa$-compact:

$$\begin{array}{ccc} Z \times_Y X & \longrightarrow & X \\ \updownarrow & & \updownarrow \\ Z & \longrightarrow & Y \end{array}$$

More tersely, the fibers of $X \longrightarrow Y$ over $\kappa$-compact objects are $\kappa$-compact.

3.2.2. REMARK. We note that the requirement that $X \longrightarrow \mathbf{1}$ be relatively $\kappa$-compact is a priori stronger than merely asking $X$ to be $\kappa$-compact. Their equivalence amounts to requiring $\kappa$-compact objects to be closed under products, which will hold in all cases of importance for us.

3.2.3. NOTATION. We will write $\mathcal{S}_\kappa$ for the class of relatively $\kappa$-compact maps in $\mathcal{E}$.