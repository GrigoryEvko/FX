CHAPTER 2. STUDY OF COMPLICIAL SETS

[1] $\coprod_{[0]} \Sigma X$ and $\Sigma X \coprod_{[0]} [1]$. They come along with morphisms that are analogue to whiskerings, and that we also note by $\nabla$:

$$\nabla : \Sigma X \to [1] \, \forall \, \Sigma X \quad \text{and} \quad \nabla : \Sigma X \to \Sigma X \, \forall \, [1].$$

We then show the following theorem:

**Theorem 2.3.1.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $(\Sigma X) \otimes [1]$ and the colimit of the following diagram:*

$$\Sigma X \, \forall \, [1] \xleftarrow{\nabla} \Sigma(X \otimes \{0\}) \hookrightarrow \Sigma(X \otimes [1]) \leftarrow \Sigma(X \otimes \{1\}) \xrightarrow{\nabla} [1] \, \forall \, \Sigma X.$$

We also provide similar formulas for the *Gray cone* and *Gray o-cone*:

**Theorem 2.3.2.1.** *There exists a zigzag of acyclic cofibrations, natural in $X$, between $\Sigma X \star [0]$ and the colimit of the following diagram:*

$$\Sigma X \, \forall \, [1] \leftarrow \Sigma X \to \Sigma([0] \stackrel{\infty}{\star} X).$$

*There exists a zigzag of acyclic cofibrations, natural in $X$, between $[0] \stackrel{\infty}{\star} \Sigma X$ and the colimit of the following diagram:*

$$\Sigma(X \star [0]) \leftarrow \Sigma X \to [1] \, \forall \, \Sigma X.$$

The third section uses this formula and the strictification result of Gagna, Ozornova and Rovelli ([GOR21]) to demonstrate a criterion for detecting autoequivalences of complicial sets by their behavior on globes. Indeed, in section 2.4, by iterating the suspension, we construct a globular object:

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

**Theorem 2.4.4.13.** *Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.*

Proposition 15.10 of [BSP21] provides a similar result for models of $(\infty, n)$-categories.

## 2.1 Preliminaries

### 2.1.1 Generalities on model categories

For this chapter, we fix a model category $C$ whose cofibrations are monomorphisms.

We give first some results on homotopy colimits. These results will be used freely throughout these text.

62