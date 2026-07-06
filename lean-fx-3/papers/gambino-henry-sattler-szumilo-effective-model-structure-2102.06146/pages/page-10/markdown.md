For example, an initial object 0 is always vacuously effective and it is universal if and only if it is strict, i.e., if there is a morphism $X \to 0$, then $X$ is initial itself. Instead, a coproduct $Y_\star = \coprod_d Y_d$ is van Kampen if and only if it is universal and disjoint, i.e., $Y_d \times_{Y_\star} Y_{d'}$ is initial for $d \neq d'$. This can be seen inspecting the proof of [CLW93, Proposition 2.14].

**Lemma 2.3.** Let $D$ be a small category. Let $Y_\bullet: C \to \mathcal{E}^D$ be a diagram such that $Y_\bullet(d)$ admits a van Kampen colimit in $\mathcal{E}$ for all $d \in D$. Then $Y_\bullet$ has a van Kampen colimit in $\mathcal{E}^D$.

Proof. If each $d \in D$, $\operatorname{colim}_{c \in C} Y_c(d)$ exists in $\mathcal{E}$, then it is functorial in $d$ and it is a colimit in $\mathcal{E}^D$. In particular, an object over $\operatorname{colim}_c Y_c$ is a $D$-indexed diagram $X(d) \to \operatorname{colim}_C Y_c(d)$, which as these colimits are all van Kampen is the same as a $(C \times D)$-indexed diagram $X_c(d) \to Y_c(d)$ which is Cartesian in the $C$-direction, which in turn is the same as a $C$-indexed diagram $X_\bullet \in \mathcal{E}^D$ which is Cartesian over $Y_\bullet$, hence proving the lemma. $\square$

We now recall the definition of various kinds of lextensive categories [CLW93].

**Definition 2.4.** Let $\mathcal{E}$ be a category with finite limits. For a regular cardinal $\alpha$, we say that $\mathcal{E}$ is $\alpha$-lextensive if $\alpha$-coproducts exist and are van Kampen colimits. Furthermore, we say that $\mathcal{E}$ is

- (i) lextensive if it is $\omega$-lextensive, i.e., finite coproducts exist and are van Kampen colimits,
- (ii) countably lextensive if it is $\omega_1$-lextensive, i.e., countable coproducts exist and are van Kampen colimits,
- (iii) completely lextensive if it is $\alpha$-lextensive for all $\alpha$, i.e., all small coproducts exist and are van Kampen colimits.

**Example 2.5.** There are numerous examples of lextensive categories.

- (i) Any presheaf category is completely lextensive. In particular, for any group $G$ the category of $G$-sets is countably lextensive.
- (ii) More generally, any Grothendieck topos is completely lextensive. In fact, Giraud's theorem characterises Grothendieck toposes as the locally presentable categories in which coproducts and (in an appropriate sense) quotients by equivalence relations are van Kampen colimits.
- (iii) The category of topological spaces is completely lextensive. The same is true for many of its subcategories such as categories of Hausdorff spaces, compactly generated spaces, weakly Hausdorff compactly generated spaces, etc.
- (iv) The category of affine schemes is lextensive, the category of schemes is completely lextensive.
- (v) The category of countable sets is countably lextensive.
- (vi) A category with finite limits $\mathcal{E}$ has the free coproduct completion which can be constructed as the category $\mathsf{Fam}\,\mathcal{E}$ of families of objects in $\mathcal{E}$. Explicitly, an object is pair $(S, (X_s)_{s \in S})$ where $S$ is a set and $(X_s)_{s \in S}$ is an $S$-indexed family of objects of $\mathcal{E}$. A morphism $(S, (X_s)) \to (S', (X'_{s'}))$ consists of a function $f: S \to S'$ and morphisms $X_s \to X'_{f(s)}$ for all $s \in S$. $\mathsf{Fam}\,\mathcal{E}$ is completely lextensive. The $\alpha$-coproduct completion, $\mathsf{Fam}_\alpha\,\mathcal{E}$, obtained by restricting to $\alpha$-small families, is an $\alpha$-lextensive category.

10