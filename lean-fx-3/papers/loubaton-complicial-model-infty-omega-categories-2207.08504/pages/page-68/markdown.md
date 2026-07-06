CHAPTER 2. STUDY OF COMPLICIAL SETS

*Proof.* Let $\kappa$ be a regular cardinal such that $X$ is $\kappa$-small. Remark first the domain of a entire monomorphism is $\kappa$-small if and only if its codomain is.

Let $I$ be the set of entire acyclic cofibrations with $\kappa$-small codomains and domains. This set generates via the small object argument a weak factorization system, and we denote by $X \rightarrow X' \rightarrow 1$ the factorization of $X \rightarrow 1$. We are willing to show that $X'$ is $M$-marked. As $X \rightarrow X'$ is an entire acyclic cofibration by construction, this will directly imply that $X'$ is equal to $\iota(X_{\mathrm{mk}})$ and so demonstrate the desired result.

Suppose then given a diagram

![img-39.jpeg](img-39.jpeg)

with $i$ an entire acyclic cofibration. We have to show that it admits a lift. Remark that this square factors as:

![img-40.jpeg](img-40.jpeg)

The morphism $i'$ is an entire acyclic cofibration with $\kappa$-small codomain and domain and then belongs to $i$. The right square of the previous diagram then admits a lift. This induces a lift in the original square, and this concludes the proof. $\square$

**Proposition 2.1.2.12.** *Suppose given a nice model structure on $\mathrm{tPsh}_M(B)$. This induces a nice model structure on $\mathrm{mPsh}_M(B)$, making the adjunction (2.1.2.10) a Quillen equivalence. A morphism between two marked presheaves is a cofibration (resp. a fibration) (resp. a weak equivalence) if it is a cofibration (resp. a fibration) (resp. a weak equivalence) when seen as a morphism of $\mathrm{tPsh}_M(B)$.*

*Proof.* Let $f : X \rightarrow Y$ be a fibration between stratified presheaves. If $Y$ is marked, so is $X$. The two weak factorization systems on $\mathrm{mPsh}_M(B)$ are then induced by the one of $\mathrm{tPsh}_M(B)$. We leave it to the reader to check that this model structure is nice.

The unit is pointwise a weak equivalence according to proposition 2.1.2.11 and the counit is the identity. The adjunction (2.1.2.10) is then a Quillen equivalence. $\square$

## 2.2 The complicial model

### 2.2.1 Model structure on marked simplicial sets

The theory of complicial sets has been extensively developed by Verity ([Ver08c]). However, Verity uses a definition slightly different from complicial sets, as he does not require the marking to be *saturated*.

In [OR20b], Ozornova and Rovelli adapt the arguments of Verity to the saturated case. This section is a recollection of the principal results of this article.

**Definition 2.2.1.1.** A *stratified simplicial set* is a pair $(X, tX)$ where $X$ is a simplicial set and $tX := \cup_{n>0} tX_n$ a graded set such that for any $n \geq 1$, $tX_n$ is a subset of $X_n$ that includes all degenerate simplices. A simplex in $tX$ is called *thin*.

A *stratified morphism* $f : (X, tX) \rightarrow (Y, tY)$ is the data of a morphism on the underlying simplicial set such that $f(tX_n) \subset tY_n$. The category of stratified simplicial sets is denoted by $\mathrm{tPsh}(\Delta)$.

68