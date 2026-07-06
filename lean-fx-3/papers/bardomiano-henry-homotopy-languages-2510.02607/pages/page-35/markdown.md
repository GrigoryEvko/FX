5. Identity operator: $x : \mathsf{Ob} \vdash \mathsf{id}_x : \mathsf{Hom}(x, x)$.

Subject to the following axioms:

- $x : \mathsf{Ob}, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash \mathsf{id}_y \circ f \equiv f$.
- $x : \mathsf{Ob}, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash f \circ \mathsf{id}_x \equiv f$.
- $x : \mathsf{Ob}, y : \mathsf{Ob}, z : \mathsf{Ob}, w : \mathsf{Ob}, f : \mathsf{Hom}(x, y), g : \mathsf{Hom}(y, z), h : \mathsf{Hom}(z, w) \vdash (h \circ g) \circ f \equiv h \circ (g \circ f)$.
- $x, y : \mathsf{Ob}, f : \mathsf{Hom}(x, y) \vdash r_f : \mathsf{Eq}(f, f)$.
- $x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash f \equiv g$.
- $x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), a : \mathsf{Eq}(f, g) \vdash a \equiv r_f$.

*Remark 3.11.* In the example above, we have imposed additional axioms for terms of type Hom and Eq. The reason behind this is solely so that the models of the theory $Cat_{\equiv}$ are exactly the categories.

As pointed out in theorem 2.4 the language we obtain is the same as the one given by [Bla78] and [Fre76]. In the introduction we presented the formula for an object $x$ to be terminal:

$$\forall y \in \mathsf{Ob}, (\exists v \in \mathsf{Hom}(y, x) \wedge \forall u, w \in \mathsf{Hom}(y, x), \mathsf{Eq}(u, w)).$$

Such formula is written in the language of categories.

*Observation 3.12.* We verify the above differently to showcase the fact that we do not need to explicitly know the language (type theory) associated to a model category, we only need to know that it can be constructed out of cofibrations. The formula above is constructed by first quantifying universally over the cofibration $\mathbf{0} \rightarrow \mathbf{1}$ to give $\forall y \in \mathsf{Ob}$. Note that applying the existential quantifier to $\{0\} \sqcup \{1\} \rightarrow \mathbf{2}$ gives us $\exists v \in \mathsf{Hom}(y, x)$ and the universal quantifier on $\mathbf{1} \rightarrow \mathcal{J}$. In the end, the formula can be seen as a composition pushouts “in context $x$.” Building the context of a formula is not an easy task, however, it might be easier to describe a pushout.

*Remark 3.13.* We mentioned at the beginning of the section that the association we do from cofibrations to types is not extremely formal. Again, the reason is that the equivalence between $\kappa$-clans and generalized $\kappa$-algebraic theories, section B, is not explicit. The association we make, for categories and the other examples below, is the obvious one and ad-hoc to the expected theory. From the start, we know what our intended models are, so once we have the types we define the operations and impose the equations that our intended models satisfy. We stress that this is informal and not very precise.

35