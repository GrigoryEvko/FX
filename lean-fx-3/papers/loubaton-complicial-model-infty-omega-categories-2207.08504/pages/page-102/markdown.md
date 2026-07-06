CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

**Theorem 3.2.6.2.** *If A is a complicial Gray module, then the category of stratified Segal precategories enriched in A is also a complicial Gray module.*

We will apply this theorem to the case where A is the category of stratified simplicial sets endowed with the model structure for n-complicial sets. Bergner results imply that stratified Segal precategories enriched in a model of (∞, n)-categories form models of (∞, n + 1)-categories. By induction, we then prove the following theorem:

**Theorem 3.3.1.11.** *Let n ∈ ℕ. The model structure for n-complicial sets is a model of (∞, n)-categories.*

Finally, in 3.3.2.1, we construct a Quillen adjunction between Θ-spaces and ω-complicial sets and prove the following result:

**Theorem 3.3.2.5.** *The adjunction*

$$\mathrm{Psh}(\Theta \times \Delta) \xleftrightarrow{\perp} \mathrm{tPsh}(\Delta)$$

constructed in 3.3.2.1 is a Quillen equivalence. Hence, the model structure for ω-complicial sets is a model of (∞, ω)-categories.

## 3.1 Preliminaries

### 3.1.1 Segal A-precategories

We fix a category A of stratified presheaves on a elegant Reedy category (as defined in definition 1.1.2.8 and section 2.1.2), endowed with a nice model structure (as defined in definition 2.1.1.6). We suppose furthermore that the terminal element of A, denoted by e, is representable.

**Definition 3.1.1.1.** We have an adjunction

$$\iota : \text{Set} \xleftrightarrow{\perp} A : ob \tag{3.1.1.2}$$

where the left adjoint sends a set S onto Π_S e and the right adjoint is the evaluation at e. The objects lying in the image of ι are called discrete objects.

**Definition 3.1.1.3.** An object C of Fun(Δ^op, A) is a Segal A-precatagory if C₀ is discrete. We denote by Seg(A) the full subcategory of Fun(Δ^op, A) spanned by the Segal A-precategories.

**Construction 3.1.1.4.** Let a be an object of A and n an integer. We denote by |[a, n]| the object of Fun(Δ^op, A) whose value on m is a × ι(Hom_Δ([m], [n])). This assignation defines a functor

$$\begin{array}{l} A \times \Delta \rightarrow \text{Fun}(\Delta^{op}, A) \\ (a, [n]) \mapsto \quad |[a, n]| \end{array}$$

We define the Segal A-precategory [a, n] as the pushout:

$$\begin{array}{c} \bigcup_{k \leq n} |[a, \{k\}]| \longrightarrow |[a, n]| \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ |[e, 0]| \longrightarrow [a, n] \end{array}$$

102