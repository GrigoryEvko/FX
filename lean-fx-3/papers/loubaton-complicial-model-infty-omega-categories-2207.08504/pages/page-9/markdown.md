CONTENTS

**Theorem 2.4.4.13.** *Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.*

Proposition 15.10 of [BSP21] provides a similar result for models of $(\infty, n)$-categories.

**Chapter 3.** Results of Gagna, Harpaz et Lanari ([GHL22]) states that 2-complicial sets are a model of $(\infty, 2)$-categories The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

The heart of the proof corresponds to constructing a Quillen adjunction between complicial sets and Segal precategories enriched in a model category $A$. We begin with the study (stratified) $A$-Segal categories. We then introduce the concept of *complicial Gray module* (definition 3.1.5.4). In short, a model category $A$ is a complicial Gray module when it admits a *Gray $\circ$-cylinder* $C \mapsto I \otimes C$ and a *Gray op-cone* $C \mapsto e \star C$, and when the assignment $[n] \to e \star e \star \dots e \star \emptyset$ lifts to a Quillen adjunction with stratified simplicial sets endowed with the model structure for complicial sets.

We then prove the following stability result:

**Theorem 3.2.6.2.** *If $A$ is a complicial Gray module, then the category of stratified Segal precategories enriched in $A$ is also a complicial Gray module.*

We will apply this theorem to the case where $A$ is the category of stratified simplicial sets endowed with the model structure for $n$-complicial sets. Bergner results imply that stratified Segal precategories enriched in a model of $(\infty, n)$-categories form models of $(\infty, n + 1)$-categories. By induction, we then prove the following theorem:

**Theorem 3.3.1.11.** *Let $n \in \mathbb{N}$. The model structure for $n$-complicial sets is a model of $(\infty, n)$-categories.*

Finally, in 3.3.2.1, we construct a Quillen adjunction between $\Theta$-spaces and $\omega$-complicial sets and prove the following result:

**Theorem 3.3.2.5.** *The adjunction*

$$\mathrm{Psh}(\Theta \times \Delta) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)$$

*constructed in 3.3.2.1 is a Quillen equivalence. Hence, the model structure for $\omega$-complicial sets is a model of $(\infty, \omega)$-categories.*

9