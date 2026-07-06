3.1. PRELIMINARIES

We will apply this theorem to the case where $A$ is the category of stratified simplicial sets endowed with the model structure for $\omega$-complicial sets, and after tedious work, we get

**Theorem 3.4.3.2.** *Let $n \in \mathbb{N}$. The model structure for $n$-complicial sets is a model of $(\infty, n)$-categories.*

As a corollary we have

**Theorem 3.4.3.14.** *The adjunction between the model structure for complete Segal $\Theta$-spaces and $\omega$-complicial set constructed in [OR22] is a Quillen equivalence.*

## 3.1 Preliminaries

### 3.1.1 Segal $A$-precategories

Let $A$ be a category of stratified presheaves on a elegant Reedy category (as defined in paragraph 1.1.2.5 and section 2.1.2), endowed with a nice model structure (as defined in paragraph 2.1.1.8). We suppose furthermore that the terminal element of $A$, denoted by $e$, is representable. We then have an adjunction

$$\iota : \text{Set} \xrightarrow{\perp} A : ob \tag{3.1.1.1}$$

where the left adjoint sends a set $S$ onto $\coprod_S e$ and the right adjoint is the evaluation at $e$. The objects lying in the image of $\iota$ are called *discrete objects*.

An object $C$ of $\text{Fun}(\Delta^{op}, A)$ is a *Segal $A$-precategory* if $C_0$ is discrete. We denote by $\text{Seg}(A)$ the full subcategory of $\text{Fun}(\Delta^{op}, A)$ spanned by the Segal $A$-precategories.

**3.1.1.2.** We consider the functor $A \times \Delta \to \text{Fun}(\Delta^{op}, A)$ defined by the assignation $a \times [n] \to |[a, n]|$ where $|[a, n]|([m]) := a \times \iota(\text{Hom}_\Delta([m], [n]))$. We define the Segal $A$-precategory $[a, n]$ as the pushout:

$$\bigcup_{k \le n} |[a, \{k\}]| \longrightarrow |[a, n]|$$
$$\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad |[e, 0]| \longrightarrow [a, n]$$

The object $[e, 0]$ is simply denoted by $[0]$. Remark that this object is the terminal Segal $A$-precategory.

115