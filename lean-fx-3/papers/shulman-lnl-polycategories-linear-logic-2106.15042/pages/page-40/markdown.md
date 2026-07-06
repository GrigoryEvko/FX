1:40

M. SHULMAN

Vol. 19:2

Similarly, a nonlinear coproduct $X + Y$ in a cartesian Freyd multicategory is the same as a *sum* in the sense of [SL13]. Finally, a cartesian Freyd multicategory has *function spaces* in the sense of [SL13, §6] if and only if it has our mixed homs $\rightarrow$. The latter means that for any nonlinear object $X$ and linear object $\mathsf{F}Y$, there is a nonlinear object $X \rightarrow \mathsf{F}Y$, with a universal linear morphism $\chi \in \mathcal{P}(X \rightarrow \mathsf{F}Y, X \mid ; \mathsf{F}Y)$ inducing a bijection

$$\mathcal{P}(\Theta, X \mid ; \mathsf{F}Y) \cong \mathcal{P}(\Theta; X \rightarrow \mathsf{F}Y)$$

between computations and values, as in [SL13, (4)].

Unlike $\mathbb{D}$-completeness, well-sortedness is a *coreflective* property.

**Proposition 6.11.** *For any sorted doctrine $\mathbb{D}$, the 2-category of well-sorted $\mathbb{D}$-sketches is coreflective in $\mathbb{D}$-Sketch, and the coreflector preserves $\mathbb{D}$-completeness.*

*Proof.* The coreflection of a $\mathbb{D}$-sketch $\mathcal{S}$ is its full sub-LNL-polycategory $\mathcal{S}'$ containing all objects of $\mathcal{S}$ that lie over primitive sorts, and precisely those objects lying over derived sorts that are the vertex of a proto-extremal lift of the sorting cone. Its proto-extremal cones are precisely those of $\mathcal{S}$ that land in this subcategory.

If $\mathcal{S}$ is $\mathbb{D}$-complete, $\mathcal{S}'$ is clearly still realized and saturated. To see that $\mathcal{S}'$ is also still precomplete, note that by construction it still has proto-universal lifts of the sorting cones. But by definition, any non-sorting $\mathbb{D}$-cone must have a *primitive* vertex, and therefore the proto-universal lifts of such cones in $\mathcal{S}$ still lie in $\mathcal{S}'$. $\square$

**Example 6.12.** Over a Kleisli sorted doctrine, the well-sorted coreflection of an LNL adjunction is the Kleisli adjunction of its comonad. Similarly, over the doctrine of linearly distributive categories with storage from Example 6.7, the well-sorted coreflection of a linearly distributive LNL adjunction (Proposition 3.15(iii)) is the double-Kleisli adjunction of its induced monad/comonad pair (Proposition 3.18).

Finally, we remark on what it takes for a doctrine map to preserve well-sortedness.

**Definition 6.13.** Let $\mathbb{D}_1$ and $\mathbb{D}_2$ be sorted doctrines. A doctrine map $\mathfrak{F} : \mathbb{D}_1 \rightarrow \mathbb{D}_2$ is **sorted** if it preserves primitive sorts, derived sorts, and sorting cones, and moreover for any derived sort $R$ of $\mathbb{D}_1$, any sorting $\mathbb{D}_2$-cone with vertex $F(R)$ is the image of some sorting $\mathbb{D}_1$-cone with vertex $R$.

**Proposition 6.14.** *If $\mathfrak{F} : \mathbb{D}_1 \rightarrow \mathbb{D}_2$ is a sorted doctrine map, then $\mathfrak{F}_*$ and $\mathfrak{F}^*$ from Proposition 5.8 preserve well-sortedness.*

*Proof.* For $\mathfrak{F}_*$, let $\pi : \mathcal{S} \rightarrow |\mathbb{D}_1|$ be a well-sorted $\mathbb{D}_1$-sketch, let $R$ be a derived $\mathbb{D}_2$-sort, and let $S \in (F\pi)^{-1}(R)$. Then $\pi(S)$ is a derived $\mathbb{D}_1$-sort. So since $\mathcal{S}$ is well-sorted, there is a proto-extremal lift of its sorting cone $G_R$ that maps the vertex to $S$. But by assumption, $FG_R$ is the sorting $\mathbb{D}_2$-cone of $F(R)$, while by definition this lift of it is also proto-extremal in $\mathfrak{F}_*(\mathcal{S})$. Thus, $\mathfrak{F}_*(\mathcal{S})$ is well-sorted.

For $\mathfrak{F}^*$, let $\pi : \mathcal{S} \rightarrow |\mathbb{D}_2|$ be a well-sorted $\mathbb{D}_2$-sketch and $R$ a derived $\mathbb{D}_1$-sort. An object of $\mathfrak{F}^*(\mathcal{S})$ over $R$ is an object $S \in \pi^{-1}(F(R))$. Since $F(R)$ is a derived $\mathbb{D}_2$-sort and $\mathcal{S}$ is well-sorted, there is a proto-extremal lift of its sorting cone $G_{F(R)}$ that maps the vertex to $S$. By assumption, $G_{F(R)}$ is the image of the sorting $\mathbb{D}_1$-cone $G_R$, and this proto-extremal lift of $G_{F(R)}$ induces a proto-extremal lift of $G_R$ to $\mathfrak{F}^*(\mathcal{S})$ mapping the vertex to $S$. Thus, $\mathfrak{F}^*(\mathcal{S})$ is well-sorted. $\square$