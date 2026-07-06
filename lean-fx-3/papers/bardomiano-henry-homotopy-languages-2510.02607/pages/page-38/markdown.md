Remark 3.16. If we now try to obtain the associated theory $2Cat_{=}$ using the generating cofibration of [Lac04], we see that the resulting theory has similar types and operations as the theory $Bicat_{=}$ of bicategories. The notable differences are that we do not need associators or unitors, but we need to include equations for the associativity and unitality of the composition of arrows and cells, and also the interchange law relating horizontal and vertical composition of cells. All these axioms are the appropriate ones to obtain 2-categories as the models of the theory $2Cat_{=}$.

Definition 3.17. Let $\mathcal{C}$ be a 2-category. An object $x \in \mathcal{C}$ is bi-terminal if for all $y \in \mathcal{C}$ there is an equivalence of categories $\mathcal{C}(y, x) \cong \mathbf{1}$.

Note that $f : a \to b$ being an equivalence can be written as

$$\exists h : \operatorname{Hom}(b, a), \exists \eta : \operatorname{Hom}(\mathrm{id}_a, h \circ f), \exists \varepsilon : \operatorname{Hom}(f \circ h, \mathrm{id}_b), \mathrm{islso}(\eta) \wedge \mathrm{islso}(\varepsilon), \top.$$

Observe that the statement $\mathrm{islso}(\eta)$, which says that $\eta : f \Rightarrow g$ is a natural isomorphism, only involves equality of natural transformations:

$$\mathrm{islso}(\eta)) := \exists \epsilon : \operatorname{Hom}(g, f), s : \mathsf{Eq}(\epsilon \circ \eta, \mathrm{id}_f) \wedge r : \mathsf{Eq}(\eta \circ \epsilon, \mathrm{id}_g), \top.$$

We can then conclude that the notion of bi-terminal object is invariant.

Remark 3.18. Other natural, but somewhat different, higher categories to consider in this progression are the double categories. Fortunately, this question has been described in Paula Verdugo's PhD thesis [Ver24], or [Ver25]. In particular, she builds a model structure on double categories where the fibrant objects are the equipments. The language for this model structure produces formulas that express properties of equipments. Therefore, we can use our invariance theorems for this "language of equipments". The details of this are exposed in Verdugo's PhD thesis cited above.

### 3.3 Bounded below chain complexes

In this section, we examine the language of the projective model structure on bounded below chain complexes $Ch(R)$ over a commutative ring $R$. We start by recalling some facts about this model structure. The detailed proofs can be found elsewhere, e.g. [Hov99].

Given an $R$-module $M$, for each $n \in \mathbb{Z}$ define $S^n(M) \in Ch(R)$ by

$$S^n(M)_k := \begin{cases} M, & k = n \\ 0, & k \neq n. \end{cases}$$

38