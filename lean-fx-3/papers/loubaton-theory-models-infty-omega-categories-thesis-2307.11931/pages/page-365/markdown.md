6.2. YONEDA LEMMA AND APPLICATIONS

Proof. We only show the first assertion as the second follows by duality. As equivalences are detected pointwise and as the lax colimit commutes with evaluation, one can suppose that $A := 1$, and so $\widehat{A} := \underline{\omega}$. We denote by $E$ (resp. $H$) the object of $\mathrm{LCart}(J)$ (resp. $\mathrm{LCart}(I)$) corresponding to $f$ (resp. $f \circ i$) and $X \to I$ (resp. $Y \to J$) the corresponding left cartesian fibration. We then have a cartesian square

$$
\begin{array}{c c c} Y & \xrightarrow {i ^ {\prime}} & X \\ E \Big \downarrow & & \Big \downarrow H \\ J & \xrightarrow [ i ] & I \end{array}
$$

As classified left cartesian fibrations are proper, $i'$ is final. We recall that we denote by $\perp : (\infty, \omega)$-$\mathrm{cat}_{\mathrm{m}} \to (\infty, \omega)$-cat the functor sending a marked $(\infty, \omega)$-category to its localization by marked cells, and that $\perp$ sends final morphism to equivalences. If we denote by $t$ the two morphisms $I \to 1$ and $J \to 1$, we then have a sequence of equivalences:

$$
\operatorname * {l a x c o l i m} _ {I} f \circ i \sim \mathbf {L} t _ {!} H \sim \bot Y \sim \bot X \sim \mathbf {L} t _ {!} E \sim \operatorname * {l a x c o l i m} _ {J} f
$$

Lemma 6.2.3.16. Let $F: I \to A^{\sharp}$ be a morphism between $\mathbf{U}$-small marked $(\infty, \omega)$-categories. There is an equivalence

$$
\hom_ {\underline {{\operatorname {H o m}}} _ {\ominus} (I, A)} (\operatorname {c s t} _ {a}, F) \sim \underset {I} {\operatorname {l a x l i m}} \hom_ {A} (a, F)
$$

natural in $F:\underline{\mathrm{Hom}}_{\ominus}(I,A)$ and $a:A^t$.

Proof. Remark that there is a commutative square:

$$
\begin{array}{c} A \xrightarrow {\text {c s t}} \underline {{\operatorname {H o m}}} _ {\ominus} (I, A) \\ y \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \widehat {A} \xrightarrow [ \text {c s t} ]{} \underline {{\operatorname {H o m}}} _ {\ominus} (I, \widehat {A}) \end{array}
$$

and that the right vertical morphism is fully faithful as $y$ is. We then have a sequence of equivalences

$$
\begin{array}{l} \hom_ {\underline {{\operatorname {H o m}}} _ {\ominus} (I, A)} (\operatorname {c s t} _ {a}, F) \sim \hom_ {\underline {{\operatorname {H o m}}} _ {\ominus} (I, \widehat {A})} (\operatorname {c s t} _ {y _ {a}}, \underline {{\operatorname {H o m}}} _ {\ominus} (I, y) (F)) \\ \sim \hom_ {\widehat {A}} (y _ {a}, \operatorname {l a x l i m} _ {I} \underline {{\operatorname {H o m}}} _ {\ominus} (I, y) (F))) \\ \sim \left(\operatorname {l a x l i m} _ {I} \underline {{\operatorname {H o m}}} _ {\ominus} (I, y) (F)\right) (a) \quad (\text {Y o n e d a l e m m a}) \\ \sim \operatorname {l a x l i m} _ {I} \hom_ {A} (a, F (i)) \\ \end{array}
$$

where the last one comes from the fact that evaluations commute with lax limits.

355