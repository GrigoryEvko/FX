Relative Elegance and Cartesian Cubes with One Connection

11

This gives us a Reedy factorization $g f = (m'm'')(e''e)$. By uniqueness of factorizations, $m'm''$ must be an isomorphism; this implies $|t''| = |t'| = |r|$, so $m'$ and $m''$ are also isomorphisms. Thus $g \cong e'$ is a lowering map.

Corollary 2.15 Any split epimorphism in a Reedy category is a lowering map; dually, any split monomorphism is a raising map.

When studying Set-valued presheaves over a Reedy category, it is useful to consider the narrower class of elegant Reedy categories [BM11; BR13].

Definition 2.16 A Reedy structure on a category $\mathbf{R}$ is elegant when

- (a) any span $s \stackrel{e}{\leftarrow} r \stackrel{e'}{\rightarrow} s'$ consisting of lowering maps $e, e'$ has a pushout;
- (b) the Yoneda embedding $\mathfrak{K}: \mathbf{R} \to \mathrm{PSh}(\mathbf{R})$ preserves these pushouts.

We refer to spans consisting of lowering maps as lowering spans, likewise pushouts of such spans as lowering pushouts. Note that all the maps in a lowering pushout square are lowering maps, as the left class of any factorization system is closed under cobase change.

Intuitively, an elegant Reedy category is one where any pair of "degeneracies" $s \stackrel{\leftarrow}{\leftarrow} r \stackrel{\rightarrow}{\rightarrow} s'$ has a universal "combination" $r \stackrel{\rightarrow}{\rightarrow} s \sqcup_r s'$, namely the diagonal of their pushout. The condition on the Yoneda embedding asks that any $r$-cell in a presheaf is degenerate along (that is, factors through) both $r \stackrel{\rightarrow}{\rightarrow} s$ and $r \stackrel{\rightarrow}{\rightarrow} s'$ if and only if it is degenerate along their combination. Again, the simplex category is the prototypical elegant Reedy category [GZ67, §II.3.2].

Remark 2.17 This definition is one of a few equivalent formulations introduced by Bergner and Rezk [BR13, Definition 3.5, Proposition 3.8] for strict Reedy categories. For generalized Reedy categories, Berger and Moerdijk [BM11, Definition 6.7] define Eilenberg-Zilber (or EZ) categories, which additionally require that $\mathbf{R}^+$ and $\mathbf{R}^-$ are exactly the monomorphisms and split epimorphisms respectively. We make do without this restriction. It is always the case that the lowering maps in an elegant Reedy category are the split epis (see Remark 5.39 below), but the raising maps need not be monic. For example [Cam23, Example 4.3], any direct category (that is, any Reedy category with $\mathbf{R}^+ = \mathbf{R}^-$) is elegant, but a direct category can contain non-monic arrows.

A presheaf $X \in \mathrm{PSh}(\mathbf{R})$ over any Reedy category can be written as the sequential colimit of a sequence of $n$-skeleta containing non-degenerate cells of $X$ only up to degree $n$, with the maps between successive skeleta obtained as cobase changes of certain basic cell maps. When $\mathbf{R}$ is elegant, these cell maps are moreover monic. This property gives rise to a kind of induction principle: any property closed under certain colimits can be verified for all presheaves on an elegant Reedy category by checking that it holds on basic cells. This principle is conveniently encapsulated by the following definition.

Definition 2.18 (Cis19, Definition 1.3.9) Let a category $\mathbf{E}$ be given. We say a replete class of objects $\mathcal{P} \subseteq \mathbf{E}$ is saturated by monomorphisms when

2025/10/16 00:43