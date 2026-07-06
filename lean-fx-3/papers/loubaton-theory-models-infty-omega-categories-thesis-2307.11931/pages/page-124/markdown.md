CHAPTER 3. COMPLICIAL SETS AS A MODEL OF $(\infty, \omega)$-CATEGORIES

Let $n \in \mathbb{N} \cup \{\omega\}$. Following the terminology of Barwick and Schommer-Pries ([BSP21]), we call model of $(\infty, n)$-categories any model category whose corresponding $(\infty, 1)$-category is $(\infty, n)$-cat.

With the definition of $(\infty, n)$-categories given in the introduction, we have a natural model for the $(\infty, 1)$-category $(\infty, n)$-cat, given by Rezk's complete Segal $\Theta_n$-spaces, i.e. space valued presheaves on $\Theta_n$ satisfying the (homotopical) Segal conditions and (homotopical) completeness conditions. However, there are many other models, see for instance [Ara14], [BR13a], [BR20], [BR13b] (we refer to [BSP21] for a comprehensive presentation of these models and their equivalence). For example, one can mention $n$-fold Segal spaces and Simpson's and Tamsamani's Segal $n$-categories among others.

It was conjectured ([Str87], [Ver17], [BSP21]) that Verity's $n$-complicial sets were also a model of $(\infty, n)$-categories. This would imply that Campion-Kapulkin-Maehara's $n$-comical sets also are, as they are shown to be Quillen equivalent to $n$-complicial sets in [DKM21].

Results of Bergner, Gagna, Harpaz, Joyal, Lanari, Lurie, Rezk and Tierney ([BR13a],[BR20], [Rez10], [Lur09a],[Lur09b], [GHL22], [JT07]) imply that 2-complicial sets are a model of $(\infty, 2)$-categories (see [GHL22] to understand how to use all this source to obtained the desired result and [BOR21] for a direct comparison between complete Segal $\Theta_2$-spaces and 2-complicial sets). The purpose of this chapter is to generalize this result to any $n \in \mathbb{N} \cup \{\omega\}$.

To this extend, we first address the more general problem of finding sufficient conditions on a model category $A$ to build a Gray cylinder $C \mapsto I \otimes C$ and a Gray cone $C \mapsto e \star C$ on Segal precategories enriched in $A$. These two operations should be linked by the following homotopy cocartesian square

$$\begin{array}{c} \{0\} \otimes C \longrightarrow I \otimes C \\ \downarrow \qquad \qquad \qquad \downarrow \\ e \longrightarrow e \star C \end{array}$$

where $e$ is the terminal object. The conditions that $A$ has to fulfill are encapsulated in the notion of Gray module (paragraph 3.1.3.3). Thanks to the Gray cylinder and cone, we can show the following theorem:

**Theorem 3.3.4.2.** If $A$ is a Gray module, there is a Quillen adjunction between the Ozornova-Rovelli model structure for $\omega$-complicial sets on stratified simplicial sets and stratified Segal precategories enriched in $A$ where the left adjoint sends $[n]$ to $e \star e \star \ldots \star e \star \emptyset$

114