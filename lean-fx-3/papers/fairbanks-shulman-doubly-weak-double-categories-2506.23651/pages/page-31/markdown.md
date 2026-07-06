DOUBLY WEAK DOUBLE CATEGORIES

31

double-categorical case is similar. However, for reasons of space we will not treat these categories.

**Lemma 6.6.** *These 2-categories $\mathcal{I}$-2-$\mathcal{C}$at and $\mathcal{I}$DblCat are locally finitely presentable as 2-categories (that is, Cat-enriched categories).*

*Proof.* By [Kel82b, Proposition 7.5], a cocomplete 2-category $\mathcal{K}$ is locally finitely presentable if and only if its underlying ordinary category $\mathcal{K}_0$ is locally finitely presentable and whenever $X \in \mathcal{K}$ is finitely presentable in $\mathcal{K}_0$ (that is, $\mathcal{K}_0(X, -): \mathcal{K}_0 \to \mathbf{Set}$ preserves filtered colimits) then it is also **Cat**-finitely-presentable in $\mathcal{K}$ (that is, $\mathcal{K}(X, -): \mathcal{K} \to \mathbf{Cat}$ preserves filtered colimits). For this, in turn, it suffices to show that $\mathcal{K}_0$ has a strongly generating set of finitely presentable objects that are also finitely presentable in $\mathcal{K}$.

We consider $\mathcal{I}$DblCat; the case of $\mathcal{I}$-2-$\mathcal{C}$at is analogous. For cocompleteness, since the underlying 1-category **IDblCat** is cocomplete, it suffices by [Kel82a, §3.8] to show that $\mathcal{I}$DblCat has powers by small categories. As for other 2-categories of icons, these can be constructed “hom-wise”. The power $X^{\mathbb{J}}$ has the same objects as $X$, its vertical arrows from $x$ to $y$ are $\mathbb{J}$-shaped diagrams in the category of such vertical arrows of $X$, and similarly for horizontal arrows, while its 2-cells are families of 2-cells in $X$ indexed by the objects of $\mathbb{J}$ that are “natural” with respect to their boundaries.

Now an evident strongly generating set of objects in the 1-category **IDblCat** consists of the images of the representables $0$, $1^H$, $1^V$, and $2_{c,d}^{a,b}$, so it suffices to show that these are also finitely presentable in the 2-category, in other words that icons mapping out of them preserve filtered colimits. Now, there are no nontrivial icons with domain $0$, while icons with domain $1^H$ and $1^V$ are simply horizontally or vertically globular 2-cells, and icons with domain $2_{c,d}^{a,b}$ are commutative “cylinders” relating two 2-cells of shape $2_{c,d}^{a,b}$ by globular 2-cells on their boundaries. But all of these are finitary structures, and hence are preserved in filtered colimits. $\square$

Therefore, we can use the machinery sketched in Section 5 to present 2-monads on $\mathcal{I}$-2-$\mathcal{C}$at and $\mathcal{I}$DblCat. Moreover, since the finitary objects are the same whether we regard them as 1-categories or 2-categories, exactly the same presentation as before actually presents a 2-monad.

We immediately deduce that **W-2-Cat$_{st}$** and **WDblCat$_{st}$** can also be enhanced to 2-categories $\mathcal{W}$-2-$\mathcal{C}$at$_{st}$ and $\mathcal{W}$DblCat$_{st}$, namely the 2-categories of strict algebras and strict morphisms for these 2-monads. We also obtain immediately notions of pseudo, lax, and colax morphism between bicategories and doubly weak double categories. Moreover, the “endomorphism monad of a morphism” $\{f, f\}$ from [KL97, §2] (see also [Lac09, §5.1]) implies that the definitions of these more general morphisms can also be deduced algebraically from the presentation.

In general, suppose $FA$ is the free 2-monad on $A \in [\mathrm{ob}\mathcal{K}_f, \mathcal{K}]$, for some locally finitely presentable 2-category $\mathcal{K}$, so that an $FA$-algebra $X$ is determined by maps $\mathcal{K}(c, X) \to \mathcal{K}(Ac, X)$. Then a pseudo $FA$-morphism $f: X \to Y$ is determined by natural isomorphisms

$$\begin{array}{ccc} \mathcal{K}(c, X) & \longrightarrow & \mathcal{K}(Ac, X) \\ \downarrow & \cong & \downarrow \\ \mathcal{K}(c, Y) & \longrightarrow & \mathcal{K}(Ac, Y). \end{array}$$