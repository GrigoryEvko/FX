Remark 2.1.5. Recall that a pullback of $\mathfrak{F}$-algebras as in (ii) is an $\mathfrak{F}$-morphism just when the $\mathfrak{F}$-algebra structure on $g^*f$ is created from the $\mathfrak{F}$-algebra structure on $f$. The naturality condition in Definition 2.1.3 tells us that this is the case just when the square defined by the corresponding sections of the representing morphisms commute:

$$\begin{array}{c} \mathfrak{F}(g^*f) \xrightarrow{i_g} \mathfrak{F}(f) \\ \psi_{g^*f} \Big\downarrow \Big\downarrow^{r_s g^*f} \qquad s_f \Big\uparrow \Big\downarrow \psi_f \\ Z \xrightarrow{g} X. \end{array}$$

A large family of examples of locally representable notions of fibred structure are considered in [Shu19, §3]. We mention just one, which will be applied in the following section.

Example 2.1.6 ([Shu19, 3.7,3.14]). From a functorial factorization on $\mathsf{E}$ one obtains a notion of fibred structure $\mathfrak{F}$ whose $\mathfrak{F}$-algebras are maps with chosen solutions to the canonical lifting problem against their left factor:

$$\begin{array}{c} Y \xlongequal{\quad} Y \\ Lf \Big\downarrow \quad \Big\downarrow^{j_f} \quad \Big\downarrow^{r_s} \\ Ef \xrightarrow{Rf} X. \end{array}$$

If $\mathsf{E}$ is locally cartesian closed and the functorial factorization is cartesian, in the sense that the functors $L, R \colon \mathsf{E}^2 \to \mathsf{E}^2$ carry pullback squares to pullback squares, then this notion of fibred structure is locally representable. Explicitly, $j^f$ may be encoded as an element in the internal hom $[Rf, f]_X := (Rf)_*(Rf)^*f$ from $Rf$ to $f$ in $\mathsf{E}_{/X}$

$$\begin{array}{c} X \xrightarrow{j^f} \Pi_{Ef}(Ef \times_X Y) \\ \searrow \quad \swarrow \\ X \xleftarrow{[Rf,f]_X} \end{array}$$

which restricts along $Lf$ to the identity at $Y$. Thus, we define $\phi_f \colon \mathfrak{F}(f) \to X$ to be the pullback

$$\begin{array}{c} \mathfrak{F}(f) \xrightarrow{\quad} \Pi_{Ef}(Ef \times_X Y) \\ \phi_f \Big\downarrow \quad \Big\downarrow^{-\circ L_f} \\ X \xrightarrow{\text{id}_Y} \Pi_Y(Y \times_X Y) \end{array}$$

of this restriction map.$^7$

Definition 2.1.7 ([Shu19, 5.11]). A notion of fibred structure $\mathfrak{F}$ is relatively acyclic if for any pullback square

$$\begin{array}{c} Y' \xrightarrow{i'} Y \\ f' \Big\downarrow \quad \Big\downarrow^{J} \quad \Big\downarrow^{f} \\ X' \xrightarrow{i} X \end{array}$$

with $\mathfrak{F}$-algebra structures $x$ on $f$ and $x'$ on $f'$, there is an $\mathfrak{F}$-algebra structure $\overline{x}$ on $f$ making the square an $\mathfrak{F}$-morphism from $x'$ to $\overline{x}$.

$^7$The map $-\cdot L_f$ is the restriction between internal homs in the cartesian closed category $\mathsf{E}_{/X}$. A construction of this map in $\mathsf{E}$ may be found in [HR24, 3.9].

14