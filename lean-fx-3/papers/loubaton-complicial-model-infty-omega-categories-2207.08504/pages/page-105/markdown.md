3.1. PRELIMINARIES

### 3.1.2 Stratified Segal $A$-precategories

Definition 3.1.2.1. A stratified Segal $A$-precategory is a pair $(C, tC)$ where $tC$ is a subset of $ob(C_1)$ that factors $s^0 : C_0 \to ob(C_1)$. A morphism of stratified Segal $A$-precategory $(C, tC) \to (D, tD)$ is the data of a morphism $f : C \to D$ such that $f(tC) \subset tD$. The category of stratified Segal $A$-precategories is denoted by $\mathrm{tSeg}(A)$.

We have an adjunction

$$(\_)^b : \mathrm{Seg}(A) \xrightarrow{\quad} \mathrm{tSeg}(A) : (\_)^\natural \tag{3.1.2.2}$$

where the left adjoint is a fully faithful inclusion that sends $C$ to $C^b := (C, Im(s^0))$. The right adjoint is the obvious forgetful functor. We will identify Segal $A$-precategories with their images in stratified Segal $A$-precategories under the left adjoint.

Definition 3.1.2.3. We define $[e, 1]_t := ([e, 1], [e, 1]_1)$. The subcategory of objects of shape $[a, n]$ or $[e, 1]_t$ is then dense in $\mathrm{tSeg}(A)$.

Definition 3.1.2.4. Let $B$ be the Reedy category and $M$ the subset of objects of $B$ such that $A$ is the category of $M$-stratified presheaves on $B$. We recall that we defined the category $\Delta[B]$ and the set of morphism $\Delta[M]$ in definition 3.1.1.6. We set $t\Delta[M]$ as the reunion of $\Delta[M]$ and the singleton $\{[e, 1]_t\}$. We can easily check that the category $\mathrm{tSeg}(A)$ is the category of $t\Delta[M]$-stratified presheaves on $\Delta[B]$.

Remark 3.1.2.5. The set of generating cofibrations for $\mathrm{tSeg}(A)$ then consists of morphisms of shape $[e, 1] \to [e, 1]_t$ or $[a, n] \cup [b, \partial n] \to [b, n]$ where $a \to b$ is a generating cofibration of $A$. For any stratified Segal $A$-precategory $C$, we then have an isomorphism

$$C \cong \underset{t\Delta[tB]/C}{\mathrm{colim}}.$$

where $t\Delta[tB]$ is the full subcategory of $\mathrm{tSeg}(A)$ whose objects are of in $\Delta[B]$ or $t\Delta[M]$.

Definition 3.1.2.6. Following the definition of section 2.1.2, a morphism between stratified Segal precategories is entire if it is the identity on the underlying $\Delta[B]$-presheaves.

Definition 3.1.2.7. A marked Segal $A$-category is a pair $(C, C^\cong)$ where $C$ is a Segal $A$-category and $C^\cong$ is the subset of $ob(C_1)$ consisting of all isomorphisms. A morphism $f : (C, C^\cong) \to (D, D^\cong)$ between marked Segal $A$-categories is an equivalence of marked Segal $A$-categories if $C_1 \to D_1$ is a weak equivalence in $A$, and for any element $x \in ob(D)$, there exists $y \in ob(C)$ and $v : f(y) \to x \in D^\cong$.

We are now willing to endow $\mathrm{tSeg}(A)$ with a nice model structure whose fibrant objects are marked Segal $A$-categories and weak equivalences between fibrant objects are equivalences of marked Segal $A$-categories.

Definition 3.1.2.8. We define the stratified Segal $A$-precategory $[e, E^{eq}]^\sharp$ whose underlying Segal $A$-precategory is $[e, E^{eq}]$ and where every element of $ob([e, E^{eq}]_1)$ is marked.

We define the set of map $J$ as the reunion of the set of generating acyclic cofibration of $\mathrm{Seg}(A)$ and of $\{[e, 1]_t \to [e, E^{eq}]^\sharp\}$ and $\{[e, E^{eq}] \to [e, E^{eq}]^\sharp\}$. We suppose furthermore that $J$ includes the acyclic cofibrations $\{0\} \to [e, E^{eq}]$ and $\{1\} \to [e, E^{eq}]$.

105