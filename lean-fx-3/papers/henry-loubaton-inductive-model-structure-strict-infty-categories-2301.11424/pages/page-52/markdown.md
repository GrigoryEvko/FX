## 4.4 Complicial Sets and Stratified Street Nerve

In this section, we show that the Street nerve can be made into a right Quillen functor from the saturated inductive left semi-model structure on $\infty$-Cat$^{+\infty}$ to the Ozornova-Rovelli-Verity model structure for complicial sets. We refer to [43] and [38] for a detailed introduction to complicial sets; we will simply recall the important definitions below.

**4.42 Definition.** A *stratified simplicial set* is a simplicial set $X$, together with a set $M \subset \prod_{k>0} X_n$ of simplices of positive dimension called *thin simplices* that includes all degenerate simplices.

A morphism of stratified simplicial sets is a morphism between the underlying simplicial sets that sends thin simplices to thin simplices. The category of stratified simplicial sets is denoted **Strat**.

The *join* is an important operation for simplicial sets, which is defined on representables by the formula

$$\Delta[n] \star \Delta[m] := \Delta[n + m + 1].$$

We can extend it to any pair of simplicial sets by setting

$$X \star Y := \operatorname{Colim}_{\Delta^\dagger_X \times \Delta^\dagger_Y} \Delta[n] \star \Delta[m]$$

where $\Delta^\dagger$ is the augmented simplex category whose objects are possibly empty finite ordered sets and where we set the convention

$$\Delta[n] \star \Delta[-1] := \Delta[n] =: \Delta[n-1] \star \Delta[n].$$

The set of $n$-simplices of $X \star Y$ is then in bijection with the set

$$\{x \star y, (x, y) \in \prod_{k<n} X_k \times Y_{n-k-1}\} \cup \{x \star \emptyset, x \in X_n\} \cup \{\emptyset \star y, y \in Y_n\}$$

See, for example, [34, Definition 1.2.8.1] and below. We now define it for stratified simplicial sets as follows:

**4.43 Definition.** If $(X, M)$ and $(Y, N)$ are two stratified simplicial sets, we define $M \star N$ as the set of simplices of $X \star Y$ of the form $x \star y$ where either $x$ or $y$ is thin, with the convention that $\emptyset$ is not thin. We then define

$$(X, M) \star (Y, N) := (X \star Y, M \star N),$$

**4.44 Definition.** We define several marked simplicial sets whose underlying simplicial set is $\Delta[n]$:

1. $\Delta[n]$, where degenerate simplices are thin.
2. $\Delta[n]$$_t$, where the top $n$-simplex is thin.
3. $\Delta^k[n]$, where all simplices that include $\{k-1, k, k+1\} \cap [n]$ and degenerate simplices are thin.

52