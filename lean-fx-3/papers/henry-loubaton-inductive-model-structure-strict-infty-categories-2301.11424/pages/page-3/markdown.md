In [32], the second named author has shown that the Street nerve of a strict $\infty$-category can be made into a complicial set by defining the “thin” simplices as those whose top-dimensional arrows are “coinductively” invertible, i.e., admit inverses up to arrows of dimension $(n+1)$ that are themselves invertible up to arrows of dimension $(n+2)$, and so on up to infinity.

From there, it is natural to ask whether this stratified version of the Street nerve also preserves fibrations, and hence is a morphism of categories of fibrant objects (and this will be shown in the present paper as Proposition 4.58).

In fact, more generally, one could ask if it is possible to make this version of the Street nerve into a right Quillen functor (for the Verity model structure on complicial sets from [43]). This is not directly possible simply because this stratified Street nerve is not a right adjoint functor. The solution to this problem is to work with markings on both sides: The usual Street nerve from strict $\infty$-categories to simplicial sets is a right adjoint functor, and one can extend it to a right adjoint functor from marked $\infty$-categories to “marked” simplicial sets (or rather *stratified* simplicial sets to follow the terminology of [43]). In Section 4.4, we show that this functor is indeed a right Quillen functor from the Verity model structure on complicial sets to the saturated inductive semi-model structure on marked $\infty$-categories.

This right Quillen functor from marked $\infty$-categories to stratified simplicial sets is meant to be a model for the forgetful functor from strict $\infty$-categories to weak $(\infty, \infty)$-categories. In particular, the corresponding left Quillen functor from stratified simplicial sets to marked $\infty$-categories is a model for the more mysterious “strictification functor”, sending weak $(\infty, \infty)$-categories to strict $\infty$-categories.

At the level of $\infty$-groupoids, this strictification functor corresponds essentially to (non-abelian) homology, through the equivalence between strict $\infty$-groupoids and crossed chain complexes ([13]) which is well-known to be a conservative functor by Whitehead’s theorem for homology. The first named author has conjectured [28] that more generally this strictification functor should be conservative on weak $(\infty, m)$-categories for all $m$. This allows us to state a concrete version of this conjecture here:

**1.1 Conjecture.** *The left Quillen functor $\downarrow: \mathbf{Strat}_V^{+m} \rightarrow \infty\text{-Cat}_{Sat-Ind}^{+m}$ from Section 4.4 reflects weak equivalences between cofibrant objects.*

## 1.2 The Two (?) Notions of $(\infty, \infty)$-Categories

C. Schommer-Pries and C. Rezk have independently argued ([27]) that there should be more than one notion of weak $(\infty, \infty)$-categories. More precisely, they both arrive at the conclusion that even if one accepts (which seems to be a clear consensus nowadays) that there is only one notion of weak $(\infty, n)$-categories for finite $n$, there are at least two different ways to build a notion of $(\infty, \infty)$-categories out of it.

Before we go into further details, we should say that the following discussion is mostly informal and speculative, and most of it has not been formalized in any models—in fact, one motivation for the present paper is to formalize some of it in the context of strict $\infty$-categories.

First, let us go over the argument put forward by Rezk and Schommer-Pries, or at least how we understand it.

3