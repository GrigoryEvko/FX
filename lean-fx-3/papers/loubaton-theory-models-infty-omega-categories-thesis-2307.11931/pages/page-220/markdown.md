CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

and $[C, 1] \star 1$ and the colimit of the diagram

$$[1 \stackrel{\text{co}}{\star} C, 1] \longleftarrow [C, 1] \longrightarrow [C, 1] \vee [1] \quad (4.3.1.9)$$

In each of the three previous diagrams, morphisms $[C, 1] \rightarrow [1] \vee [C, 1]$ and $[C, 1] \rightarrow [C, 1] \vee [1]$ are the unique ones preserving extremal points.

**Remark 4.3.1.10.** It is worth noticing the great similarity of these equations with the one given in theorems 1.2.3.13 and 1.2.3.14

**4.3.1.11.** Let $C$ be an $(\infty, \omega)$-category and $K$ a $(\infty, 1)$-category. There is a canonical morphism $C \otimes K \rightarrow C \times K$. In a way, one can see $C \times K$ as an intelligent truncated version of the Gray tensor product $C \otimes K$. We will make this intuition precise by constructing a hierarchy of Gray tensor products with $(\infty, 1)$-categories. For $k \in \mathbb{N} \cup \{\omega\}$, we define the functor

$$\begin{array}{rcl} (\infty, \omega)\text{-cat} \times (\infty, 1)\text{-cat} & \rightarrow & (\infty, \omega)\text{-cat} \\ (C, K) & \mapsto & C \otimes_k K \end{array}$$

where $C \otimes_k K$ fits in the cocartesian square

$$\begin{array}{ccc} \text{colim}_{n \geq k}(\tau_n C) \otimes K & \longrightarrow & C \otimes K \\ \downarrow & & \downarrow \\ \text{colim}_{n \geq k} \tau_n^i((\tau_n C) \otimes K) & \longrightarrow & C \otimes_k K \end{array}$$

The induced functors $\_ \otimes_k [1] : (\infty, \omega)\text{-cat} \rightarrow (\infty, \omega)\text{-cat}$ are called the *k-Gray cylinder*. Formula (4.3.1.7) implies that for every $(\infty, \omega)$-category $C$, there is a natural identification between $[C, 1] \otimes_{k+1} [1]$ and the colimit of the following diagram

$$[1] \vee [C, 1] \longleftarrow [C \otimes_k \{0\}, 1] \longrightarrow [C \otimes_k [1], 1] \longleftarrow [C \otimes_k \{1\}, 1] \longrightarrow [C, 1] \vee [1] \quad (4.3.1.12)$$

Remark that the endofunctor $\_ \otimes_0 [1]$ is the identity, the first assertion of lemma 2.2.2.8 implies that the endofunctor $\_ \otimes_1 [1]$ is equivalent to $\_ \times [1]$, and the endofunctor $\otimes_\omega [1]$ is just the normal Gray cylinder.

**Proposition 4.3.1.13.** *For any integer $k > 0$, $\_ \otimes_k [1]$ preserves colimits.*

*Proof.* In order to simplify the notation, for a functor $F : (\infty, \omega)\text{-cat} \rightarrow (\infty, \omega)\text{-cat}$, the $\infty$-presheaves $\text{colim}_{\Theta/\Sigma^n E^{eq}} \iota F$, where $\iota$ in the inclusion $(\infty, \omega)\text{-cat} \rightarrow \text{Psh}^\infty(\Theta)$, will just be denoted by $F(\Sigma^n E^{eq})$.

As $\tau$ and $\tau^i$ preserves colimits in $\text{Psh}^\infty(\Theta)$ and $\widehat{\text{W}_{\text{Seg}}}$, and as $\_ \otimes [1]$ preserves colimits, we just have to show that for any $n$, $(\Sigma^n E^{eq}) \otimes_k [1] \rightarrow (\Sigma^n 1) \otimes_k [1]$ is in $\widehat{\text{W}}$.

210