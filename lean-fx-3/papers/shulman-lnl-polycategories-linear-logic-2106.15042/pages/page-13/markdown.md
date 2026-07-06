Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:13

Similarly, a colimit of linear objects satisfies

$$\mathcal{P}(\Theta \mid \Gamma, \operatorname{colim}_i A_i; \Delta) \cong \lim_i \mathcal{P}(\Theta \mid \Gamma, A_i; \Delta) \quad (2.4)$$

which implies that it is preserved by $\otimes$ in each variable and sent by $\cap$ to a limit in $\mathcal{P}^{\mathrm{NL}}$, insofar as $\otimes, \cap$ exist. If all $\otimes, \mathfrak{A}, \bot, \mathsf{F}$ exist, then a colimit in the ordinary category $\mathcal{P}^{\mathrm{L}}$ is a colimit in $\mathcal{P}$ if and only if it is preserved by $\otimes$. Dually, a limit of linear objects satisfies

$$\mathcal{P}(\Theta \mid \Gamma; \Delta, \lim_i A_i) \cong \lim_i \mathcal{P}(\Theta \mid \Gamma; \Delta, A_i) \quad (2.5)$$

which implies that it is preserved by $\mathfrak{A}$ in each variable and sent by $\cup$ to a limit in $\mathcal{P}^{\mathrm{NL}}$, insofar as $\mathfrak{A}, \cup$ exist. And if all $\mathfrak{A}, \otimes, \mathbb{1}, \mathsf{F}$ exist, a colimit in $\mathcal{P}^{\mathrm{L}}$ is a colimit in $\mathcal{P}$ if and only if it is preserved by $\mathfrak{A}$. Note also that $\otimes$ preserves all colimits if $\multimap$ exists, $\mathsf{F}$ preserves all colimits if $\cup$ exists, and so on.

We will write $X+Y$ for the coproduct of nonlinear objects and $\varnothing$ for the initial nonlinear object, and we denote finite products and coproducts of linear objects with Girard's notation for the linear logic additive connectives: $A \& B$ for the product, $A \oplus B$ for the coproduct, $\top$ for the terminal object, and $0$ for the initial object. Thus the above preservation properties state that

$$\begin{array}{ll} X \times (Y+Z) \cong (X \times Y) + (X \times Z) & X \times \varnothing \cong \varnothing \\ \mathsf{F}(X+Y) \cong \mathsf{F}X \oplus \mathsf{F}Y & \mathsf{F}\varnothing \cong 0 \\ \exists(X+Y) \cong \exists X \& \exists Y & \exists\varnothing \cong \top \\ A \otimes (B \oplus C) \cong (A \otimes B) \oplus (A \otimes C) & A \otimes 0 \cong 0 \\ \cap(A \oplus B) \cong \cap A \times \cap B & \cap 0 \cong 1 \\ A\mathfrak{A}(B \& C) \cong (A\mathfrak{A}B) \& (A\mathfrak{A}C) & A\mathfrak{A}\top \cong \top \\ \cup(A \& B) \cong \cup A \times \cup B & \cup\top \cong 1 \end{array}$$

If we specialize the above universal properties to symmetric polycategories, symmetric multicategories, cartesian multicategories, or LNL multicategories, there are three possible results. Some universal properties make sense unmodified, such as $\otimes, \mathfrak{A}$ in polycategories or $\times, \rightarrow$ in cartesian multicategories. Others make no sense at all, such as $\mathfrak{A}, \bot$ in LNL multicategories or $\mathsf{F}, \cup$ in symmetric polycategories.

A third group can only have a restricted universal property. Specifically, limits and colimits in a symmetric multicategory or LNL multicategory can only induce bijections of hom-sets with unary codomain: instead of (2.3)–(2.5) we assert only

$$\begin{array}{ll} \mathcal{P}(\Theta, \operatorname{colim}_i X_i \mid \Gamma; B) & \cong \lim_i \mathcal{P}(\Theta, X_i \mid \Gamma; B) \\ \mathcal{P}(\Theta \mid \Gamma, \operatorname{colim}_i A_i; B) & \cong \lim_i \mathcal{P}(\Theta \mid \Gamma, A_i; B) \\ \mathcal{P}(\Theta \mid \Gamma; \lim_i A_i) & \cong \lim_i \mathcal{P}(\Theta \mid \Gamma; A_i). \end{array}$$

Since the left- and right-hand sides of (2.3)–(2.5) have the same codomain arity, these apparently-weaker universal properties are equivalent to (2.3)–(2.5) for limits and colimits over *nonempty* domain categories. But the limit of the empty diagram of copies of the empty set is no longer empty, so an initial or terminal object in an LNL multicategory $\mathcal{E}$ (in the above sense) need not be initial or terminal in $\mathcal{E}$ *qua* LNL polycategory.

In fact, an LNL multicategory *cannot* have a terminal linear object, or an initial linear or nonlinear object, in the LNL-polycategorical sense. For example, if $\top$ is a terminal linear object, we must have $\mathcal{P}(\Theta \mid \Gamma; \Delta, \top) = 1$ for *all* $\Delta$, whereas in an LNL multicategory we