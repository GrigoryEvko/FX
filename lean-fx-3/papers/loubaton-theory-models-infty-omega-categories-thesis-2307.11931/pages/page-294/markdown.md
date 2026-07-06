CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

**5.2.4.4.** A morphism $f : C \rightarrow D$ is *smooth* if $f^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/D} \rightarrow (\infty, \omega)\text{-cat}_{\mathrm{m}/C}$ preserves colimits, and for every cartesian square of the form

$$\begin{array}{ccc} C'' & \xrightarrow{v'} & C' & \longrightarrow & C \\ \downarrow & \downarrow & \downarrow & \downarrow & \downarrow_f \\ D'' & \xrightarrow{v} & D' & \longrightarrow & D \end{array} \tag{5.2.4.5}$$

if $v$ is initial, so is $v'$. When $f$ is smooth, the functor $f^*$ admits a left adjoint

$$f^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/D} \xleftarrow{\perp} (\infty, \omega)\text{-cat}_{\mathrm{m}/C} : f_*$$

and as $f^*$ preserves initial morphisms, this induces a derived adjunction:

$$\mathbf{L}f^* : \mathrm{LCart}(D) \xleftarrow{\perp} \mathrm{LCart}(C) : \mathbf{R}f_*$$

where $\mathbf{R}f_*$ is just the restriction of $f_*$.

**Proposition 5.2.4.6.** *Let $I, J$ be two marked $(\infty, \omega)$-categories. The projection $I \times J \rightarrow I$ is smooth.*

*Proof.* This is a direct consequence of the fact that cartesian product preserves colimits and initial morphisms. $\square$

**Proposition 5.2.4.7.** *Classified right cartesian fibrations are smooth.*

*Proof.* The theorem 5.2.2.12 states that $f^*$ preserves colimits. Suppose given a diagram of shape (5.2.4.5). As initial morphisms are the smallest cocomplete class containing morphism $I$, and as $f^*$ preserves colimits, one can suppose that $v$ belongs to $I$, and then is a left Gray deformation retract. To conclude, one applies proposition 5.2.1.13. $\square$

**5.2.4.8.** A morphism $f : C \rightarrow D$ is *proper* if $f^* : (\infty, \omega)\text{-cat}_{\mathrm{m}/D} \rightarrow (\infty, \omega)\text{-cat}_{\mathrm{m}/C}$ preserves colimits and for every cartesian square of the form

$$\begin{array}{ccc} C'' & \xrightarrow{v'} & C' & \longrightarrow & C \\ \downarrow & \downarrow & \downarrow & \downarrow & \downarrow_f \\ D'' & \xrightarrow{v} & D' & \longrightarrow & D \end{array} \tag{5.2.4.9}$$

if $v$ is final, so is $v'$. A morphism $f$ is then proper if and only if $f^\circ$ is smooth. Propositions 5.2.4.6 and 5.2.4.7 then imply that projections and classified right cartesian fibrations are proper.

284