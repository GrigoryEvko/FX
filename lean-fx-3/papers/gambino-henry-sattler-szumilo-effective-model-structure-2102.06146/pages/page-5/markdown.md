In Definition 1.3 we introduce the notion of a fibration in $\mathfrak{s}\mathcal{E}$ with which we shall work throughout the paper. This notion is defined using the enrichment of $\mathfrak{s}\mathcal{E}$ in $\mathfrak{s}\text{Set}$ and generalises that of a Kan fibration in $\mathfrak{s}\text{Set}$. The main result of this section, Theorem 1.7, establishes a structure of a fibration category on the category of fibrant objects in $\mathfrak{s}\mathcal{E}$. For applications throughout the paper, we also establish a fiberwise version of this fibration category in Theorem 1.9. We also introduce the notion of a *pointwise weak equivalence* (Definition 1.6), which provides the weak equivalences of these fibration categories. In the subsequent sections we will extend these results to obtain the effective model structure on $\mathfrak{s}\mathcal{E}$, under the stronger assumption that $\mathcal{E}$ is countably lextensive. The weak equivalences of the effective model structure will not be the pointwise weak equivalences in general, although the two notions will coincide for maps between fibrant objects.

Let us recall how the category $\mathfrak{s}\mathcal{E}$ is enriched over $\mathfrak{s}\text{Set}$ with respect to the Cartesian monoidal structure. For a finite simplicial set $K$ and $X \in \mathfrak{s}\mathcal{E}$, we define $K \pitchfork X \in \mathfrak{s}\mathcal{E}$ via the end formula

$$(K \pitchfork X)_m =_{\text{def}} \int_{[n] \in \Delta} X_n^{(K \times \Delta[m])_n}. \quad (1.1)$$

For $X, Y \in \mathfrak{s}\mathcal{E}$, the simplicial hom-object is then defined by letting$^1$

$$\text{Hom}_{\mathfrak{s}\text{Set}}(X, Y)_m =_{\text{def}} \text{Hom}_{\text{Set}}(X, \Delta[m] \pitchfork Y). \quad (1.2)$$

This makes $\mathfrak{s}\mathcal{E}$ into a $\mathfrak{s}\text{Set}$-enriched category so that the formula in (1.1) gives the cotensor (over finite simplicial sets) with respect to the enrichment. Without further assumptions on $\mathcal{E}$, $\mathfrak{s}\mathcal{E}$ does not admit all cotensors or tensors over simplicial sets. We often identify an object $E \in \mathcal{E}$ with the constant simplicial object with value $E$. For example, for $E \in \mathcal{E}$ and $Y \in \mathfrak{s}\mathcal{E}$ we write $\text{Hom}_{\mathfrak{s}\text{Set}}(E, Y)$. Note that

$$\text{Hom}_{\mathfrak{s}\text{Set}}(E, Y)_m = \text{Hom}_{\text{Set}}(E, Y_m),$$

$$\text{Hom}_{\mathfrak{s}\text{Set}}(E, K \pitchfork Y) = K \pitchfork \text{Hom}_{\mathfrak{s}\text{Set}}(E, Y).$$

The $\mathfrak{s}\text{Set}$-enrichment allows us to define a notion of a homotopy between morphisms of $\mathfrak{s}\mathcal{E}$. Given maps $f_0, f_1: X \rightarrow Y$ in $\mathfrak{s}\mathcal{E}$ (or one of its slice categories), a *homotopy* $H$ from $f_0$ to $f_1$, written $H: f_0 \sim f_1$, is a map

$$H: X \rightarrow \Delta[1] \pitchfork Y \quad (1.3)$$

that restricts to $f_0$ on $\{0\} \rightarrow \Delta[1]$ and to $f_1$ on $\{1\} \rightarrow \Delta[1]$. It is *constant* if it factors through the canonical map $\Delta[0] \pitchfork Y \rightarrow \Delta[1] \pitchfork Y$, in which case $f_0 = f_1$. Note that we can regard $H$ as a map $\Delta[1] \rightarrow \text{Hom}_{\mathfrak{s}\text{Set}}(X, Y)$. This generalises the usual notion of homotopy in simplicial sets. For each $E \in \mathcal{E}$, the functor $\text{Hom}_{\mathfrak{s}\text{Set}}(E, -)$ preserves homotopies because it preserves the cotensor with $\Delta[1]$.

We need some definitions to introduce the notions of a Kan fibration and trivial Kan fibration in $\mathfrak{s}\mathcal{E}$. For a finite simplicial set $K$, we define the *evaluation functor* $\text{ev}_K: \mathfrak{s}\mathcal{E} \rightarrow \mathcal{E}$ via the end formula

$$\text{ev}_K(X) = X(K) =_{\text{def}} \int_{[n] \in \Delta} X_n^{K_n}. \quad (1.4)$$

We will usually write $X(K)$ rather than $\text{ev}_K(X)$ for brevity. However, in some situations the notation $\text{ev}_K(X)$ will be more convenient, see the definition of pullback evaluation below. The end above exists since, by the finiteness of $K$, it can be constructed from finite limits. For example, $X(\Delta[n]) = X_n$ and $X(\Lambda^k[2]) = X_1 \times_{X_0} X_1$. Also note that $X(K) = (K \pitchfork X)_0$ and $X(K \times \Delta[m]) = (K \pitchfork X)_m$.

$^1$Here and in the following we use subscripts to indicate to which category the hom-objects under consideration belong.

5