**Lemma 2.2.** *Let $F : \mathcal{C} \rightarrow \mathcal{D}$, $G : \mathcal{D} \rightarrow \mathcal{C}$ be functors of $\infty$-categories. Let $\eta : id \rightarrow GF$ and $\epsilon : FG \rightarrow id$ be natural transformations. If for each object $X \in \mathcal{C}$ and $Y \in \mathcal{D}$ the two composites:*

$$F(X) \stackrel{F(\eta_X)}{\rightarrow} FGF(X) \stackrel{\epsilon_{F(X)}}{\rightarrow} F(X) \quad \text{and} \quad G(Y) \stackrel{\eta_{G(Y)}}{\rightarrow} GFG(Y) \stackrel{G(\epsilon_Y)}{\rightarrow} G(Y)$$

*are equivalences, then $\eta$ is the unit of an adjunction $F \dashv G$.*

By duality it is also the case that $\epsilon$ is the counit of an adjunction, but without additional assumption (for example the fact that the two composite above are equivalent to the identity) these two claims might not be compatible ($\eta$ and $\epsilon$ might not be the unit and counit of the same adjunction, typically, one of the adjunctions can be twisted by an automorphism of $F$ or $G$.)

*Proof.* By the definition of unit of an adjunction [15, Proposition 5.2.2.7], we want to show that for each $x \in \mathcal{C}, y \in \mathcal{D}$ the map

$$U_{x,y} : \text{Map}_{\mathcal{D}}(Fx, y) \rightarrow \text{Map}_{\mathcal{C}}(GFx, Gy) \xrightarrow{(-)\circ\eta_x} \text{Map}_{\mathcal{C}}(x, Gy) \quad (1)$$

is an equivalence. We introduce the dual transformation

$$V_{x,y} : \text{Map}_{\mathcal{C}}(x, Gy) \rightarrow \text{Map}_{\mathcal{D}}(Fx, FGy) \xrightarrow{\epsilon_y \circ(-)} \text{Map}_{\mathcal{D}}(Fx, y)$$

Since the natural transformation $\epsilon$ and $\eta$ induces a natural tranformation on the level of enriched homotopy categories$^2$, we get a commutative square in the homotopy category of spaces:

$$\begin{array}{ccc} \text{Map}_{\mathcal{C}}(x, G(y)) & \xrightarrow[GF(-)]{} & \text{Map}_{\mathcal{C}}(GF(x), GFG(y)) \\ \scriptstyle{id} \downarrow & & \scriptstyle{\eta_x} \downarrow \\ \text{Map}_{\mathcal{C}}(x, G(y)) & \xrightarrow{\eta_{Gy} \circ(-)} & \text{Map}_{\mathcal{C}}(x, GFG(y)) \end{array}$$

In other words $GF(-) \circ \eta_x \simeq \eta_{G(y)} \circ (-)$. We have

$$U_{x,y} \circ V_{x,y} = G(\epsilon_y \circ F(-)) \circ \eta_x = G(\epsilon_y) \circ GF(-) \circ \eta_x \simeq G(\epsilon_y) \circ \eta_{Gy} \circ (-)$$

$^2$Here we see the homotopy category as enriched in the homotopy category of spaces as in [15, Definition 1.1.5.14].

8