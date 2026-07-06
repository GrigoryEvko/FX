By the first part of Lemma 3.1.10, the dashed composite fibrations are both trivial fibrations, and now the fibration $g$ is the base of a commutative triangle of trivial fibrations with summit $E$, so $g$ is a trivial fibration by the second part of that lemma.

This proves that $g$ admits some $\mathcal{TF}$-algebra structure. By relative acyclicity, this structure may be aligned with that of $t^*g$ to make the square (3.4.5) into a $\mathcal{TF}$-morphism. This specification of a new $\mathcal{TF}$-algebra structure on $g$ finally solves the original lifting problem (3.4.4).

In the setting of Lemma 3.4.3, Voevodsky constructs an alternate contractible map classifier, which we briefly digress to describe.

Digression 3.4.6. In a locally cartesian closed category with a cylindrical premodel structure satisfying the Frobenius condition, for any fibration $f: Y \to X$, there is a fibration $\phi_f: \text{isContr}_X f \to X$ defined by pushing forward and then summing over its fibred path space fibration:

$$\begin{array}{c c c c c} P_X Y & \Pi_Y P_X Y & \Sigma_Y \Pi_Y P_X Y & =: & \text{isContr}_X(f) \\ \partial \Big\downarrow & \Big\downarrow (\pi_2)_* \partial & \Big\downarrow f \cdot (\pi_2)_* \partial & & \Big\downarrow \phi_f \\ Y \times_X Y & \xrightarrow{\pi_2} Y & \xrightarrow{f} X & =: & X. \end{array}$$

By construction, sections to $\phi_f: \text{isContr}_X(f) \to X$ correspond to sections $s: X \to Y$ to $f$ together with a fibred homotopy $s \cdot f \sim_X \text{id}_Y$.

As our notation suggests, there is a close relationship between the map $\phi_f: \text{isContr}_X(f) \to X$ and the map $\phi_f: \mathcal{TF}(f) \to X$ constructed in Lemma 2.2.10 in the setting of a premodel structure on an elementary topos in which the cofibrations are the monomorphisms. For a fibration $f: Y \to X$, these define “logically equivalent notions” of fibred structure witnessing that $f$ is a trivial fibration.

Indeed, if $\phi_f: \mathcal{TF}(f) \to X$ has a section, then $f$ is a trivial fibration, so admits a section $s: X \to Y$, since all objects are cofibrant. This data defines a lifting problem

$$\begin{array}{c} \emptyset \longrightarrow P_X Y \\ \Big\downarrow \quad \stackrel{h}{\longrightarrow} \quad \Big\downarrow \partial \\ Y \xrightarrow{(sf,id_Y)} Y \times_X Y, \end{array}$$

which admits a solution by the axiom 3.1.8(i) in the setting of Lemma 3.1.9, constructing a section $(s, h)$ of $\phi_f: \text{isContr}_X(f) \to X$.

Conversely, if $\phi_f: \text{isContr}_X(f) \to X$ has a section, then this data defines a retract diagram

$$\begin{array}{c} Y \xrightarrow{h} P_X Y \xrightarrow{\partial_1} Y \\ f \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

exhibiting $f$ as a retract of $\partial_0$, which is a trivial fibration in the setting of Lemma 3.1.9 by the axiom 3.1.8(ii). Thus, $\phi_f: \mathcal{TF}(f) \to X$ has a section.

3.5. Univalence. In a premodel structure that satisfies the Frobenius condition and for which the fibrations have universes in the sense of Definition 2.3.6, the equivalence extension property of Definition 3.3.1 is related to Voevodsky’s univalence axiom. To state this, we require the following construction. Following Notation 2.3.7, we write $\pi: \dot{U} \to U$ for a generic classifying universe and refer to this as the “universe of fibrations,” without explicitly designating a cardinal bound.

34