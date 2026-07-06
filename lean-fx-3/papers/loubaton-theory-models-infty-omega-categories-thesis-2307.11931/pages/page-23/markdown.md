**Theorem 2.4.4.14.** *Let $i$ be a left Quillen endofunctor for the model category for complicial sets. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_{-}) \rightsquigarrow \mathbf{D}_{-}.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$.*

Proposition 15.10 of [BSP21] provides a similar result for models of $(\infty, n)$-categories.

**Chapter 3.** Results of Bergner, Gagna, Harpaz, Lanari, Lurie and Rezk ([BR13a],[BR20], [Rez10], [Lur09a],[Lur09b], [GHL22]) imply that 2-complicial sets are a model of $(\infty, 2)$-categories (see [GHL22] to understand how to use all this source to obtained the desired result and [BOR21] for a direct comparison between complete Segal $\Theta_2$-spaces and 2-complicial sets). The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

To this extend, we first address the more general problem of finding sufficient conditions on a model category $A$ to build a *Gray cylinder* $C \mapsto I \otimes C$ and a *Gray cone* $C \mapsto e \star C$ on Segal precategories enriched in $A$. These two operations should be linked by the following homotopy cocartesian square

$$\begin{array}{c} \{0\} \otimes C \longrightarrow I \otimes C \\ \downarrow \qquad \qquad \qquad \downarrow \\ e \longrightarrow e \star C \end{array}$$

where $e$ is the terminal object. The conditions that $A$ has to fulfill are encapsulated in the notion of *Gray module* (paragraph 3.1.3.3). Thanks to the Gray cylinder and cone, we can show the following theorem:

**Theorem 3.3.4.2.** *If $A$ is a Gray module, there is a Quillen adjunction between the Ozornova-Rovelli model structure for $\omega$-complicial sets on stratified simplicial sets and stratified Segal precategories enriched in $A$ where the left adjoint sends $[n]$ to $e \star e \star \dots \star e \star \emptyset$*

We will apply this theorem to the case where $A$ is the category of stratified simplicial sets endowed with the model structure for $\omega$-complicial sets, and after tedious work, we get

**Theorem 3.4.3.2.** *Let $n \in \mathbb{N}$. The model structure for $n$-complicial sets is a model of $(\infty, n)$-categories.*

As a corollary we have

**Theorem 3.4.3.14.** *The adjunction between the model structure for complete Segal $\Theta$-spaces and $\omega$-complicial set constructed in [OR22] is a Quillen equivalence.*

13