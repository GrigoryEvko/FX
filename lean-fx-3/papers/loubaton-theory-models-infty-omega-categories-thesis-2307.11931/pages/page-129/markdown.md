3.1. PRELIMINARIES

and the set of morphism $\Delta[M]$ in paragraph 3.1.1.3. We set $t\Delta[M]$ as the reunion of $\Delta[M]$ and the singleton $\{[e, 1]_t\}$. We can easily check that the category $\text{tSeg}(A)$ is the category of $t\Delta[M]$-stratified presheaves on $\Delta[B]$. The set of generating cofibrations for $\text{tSeg}(A)$ then consists of morphisms of shape $[e, 1] \rightarrow [e, 1]_t$ or $[a, n] \cup [b, \partial n] \rightarrow [b, n]$ where $a \rightarrow b$ is a generating cofibration of $A$. For any stratified Segal $A$-precategory $C$, we then have an isomorphism

$$C \cong \operatorname{colim}_{t\Delta[tB]/C} \neg$$

where $t\Delta[tB]$ is the full subcategory of $\text{tSeg}(A)$ whose objects are of in $\Delta[B]$ or $t\Delta[M]$.

Following the definition of section 2.1.2, a morphism between stratified Segal precategories is *entire* if it is the identity on the underlying $\Delta[B]$-presheaves.

**3.1.2.4.** A *marked Segal $A$-category* is a pair $(C, C^{\cong})$ where $C$ is a Segal $A$-category and $C^{\cong}$ is the subset of $ob(C_1)$ consisting of all isomorphisms. A morphism $f : (C, C^{\cong}) \rightarrow (D, D^{\cong})$ between marked Segal $A$-categories is an *equivalence of marked Segal $A$-categories* if $C_1 \rightarrow D_1$ is a weak equivalence in $A$, and for any element $x \in ob(D)$, there exists $y \in ob(C)$ and $v : f(y) \rightarrow x \in D^{\cong}$.

**3.1.2.5.** We are now willing to endow $\text{tSeg}(A)$ with a nice model structure whose fibrant objects are marked Segal $A$-category and weak equivalences between fibrant objects are equivalences of marked Segal $A$-categories. We define the stratified Segal $A$-precategories $(E^{\cong})'$ as the following pushout:

$$\begin{array}{ccc} [e, 1] & \xrightarrow{d^0 d^3} & E^{\cong} \\ \downarrow & & \downarrow \\ [e, 1]_t & \longrightarrow & (E^{\cong})' \end{array}$$

We define the set of map $J$ as the reunion of the set of generating acyclic cofibration of $\text{Seg}(A)$ and of $\{[e, 1]_t \rightarrow (E^{\cong})'\}$ and $\{E^{\cong} \rightarrow (E^{\cong})'\}$. We suppose furthermore that $J$ includes the acyclic cofibrations $\{0\} \rightarrow E^{\cong}$ and $\{1\} \rightarrow E^{\cong}$.

**Lemma 3.1.2.6.** A morphism $f$ has the right lifting property against $J$ if and only if $f^{\cong}$ is a fibration and $f$ has the right lifting property against $[e, 1]_t \rightarrow (E^{\cong})'$ and $E^{\cong} \rightarrow (E^{\cong})'$. An object $X$ has the right lifting property against $J$ if and only if it is a marked Segal $A$-category.

*Proof.* Straightforward. $\square$

119