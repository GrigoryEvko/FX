A *categorical pattern* in the sense of [5] is a category $\mathcal{O}$ endowed with a factorization system $(\mathcal{O}^{act}, \mathcal{O}^{in})$ whose left class is called the *active morphisms* and the right class is called the *inert morphisms*, and a full subcategory $\mathcal{O}^{el} \subset \mathcal{O}^{in}$ of objects called elementary objects.

Given a categorical pattern $(\mathcal{O}, \mathcal{O}^{act}, \mathcal{O}^{in}, \mathcal{O}^{el})$, a Segal $\mathcal{O}$-object is a presheaf $\mathcal{F}$ on $\mathcal{O}$ which satisfies the following equivalent conditions:

- For all $X \in \mathcal{O}$, the map

$$\mathcal{F}(X) \rightarrow \lim_{\substack{E \rightarrow X \in \mathcal{O}^{in} \\ E \in \mathcal{O}^{el}}} \mathcal{F}(E)$$

is an equivalence.

- The restriction of $\mathcal{F}$ to $\mathcal{O}^{in}$ is a right Kan extension of $\mathcal{F}$ restricted to $\mathcal{O}^{el}$. (See lemma 2.9 of [5]).

We can immediately see this as a special case of the notion of theory of the present paper as follows: Consider the functor $\mathcal{O}^{in} \rightarrow \Pr \mathcal{O}^{el}$ that is obtained by composing the Yoneda embedding with the restriction functor:

$$\mathcal{O}^{in} \rightarrow \Pr \mathcal{O}^{in} \rightarrow \Pr \mathcal{O}^{el}$$

The induced nerve functor $\Pr \mathcal{O}^{el} \rightarrow \Pr \mathcal{O}^{in}$ is equivalent to the fully faithful inclusion of the full subcategory of objects of $\Pr \mathcal{O}^{in}$ that satisfies the Segal condition mentioned above. By definition the $\infty$-category of Segal $\mathcal{O}$-objects, we have a pullback:

$$\begin{array}{ccc} Seg_{\mathcal{O}} & \longrightarrow & \Pr \mathcal{O} \\ \downarrow & \swarrow & \downarrow \\ \Pr \mathcal{O}^{el} & \longrightarrow & \Pr \mathcal{O}^{in} \end{array} \quad (7)$$

That is, $Seg_{\mathcal{O}}$ is the category of $\mathcal{O}$-models where $\mathcal{O}$ is seen as $\mathcal{O}^{in}$-theory for the canonical inclusion $\mathcal{O}^{in} \rightarrow \mathcal{O}$, and the dense functor $\mathcal{O}^{in} \rightarrow \Pr \mathcal{A}$.

The condition that the categorical pattern $\mathcal{O}$ is *extendable* (see Definition 8.5 of [5]) is equivalent, by Proposition 8.8 of [5] to the fact that the pullback diagram (7) satisfies a Beck-Chevalley condition. That is, that the

52