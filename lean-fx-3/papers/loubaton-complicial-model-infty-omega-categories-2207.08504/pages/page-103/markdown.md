3.1. PRELIMINARIES

The object $[e, 0]$, which is the terminal Segal $A$-precategory, is simply denoted by $[0]$.

The assignation $(a, n) \mapsto [a, n]$ induces by left Kan extension a colimit preserving functor

$$[\_, \_]: A \times \operatorname{Psh}(\Delta) \to \operatorname{Seg}(A).$$

The image of this functor is dense in $\operatorname{Seg}(A)$.

**Construction 3.1.1.5.** For $\{n_i\}_{i \le k}$ and $\{a \to a_i\}_{i \le k}$ two finite sequences, we denote by $[a_0, n_0] \vee [a_1, n_1] \vee \dots \vee [a_k, n_k]$ the Segal $A$-precategory fitting in the following pushout:

$$\begin{array}{ccc} \amalg_{i \le k}[a, n_i] & \longrightarrow & [a, \Sigma_{i \le k} n_i] \\ \downarrow & & \downarrow \\ \amalg_{i \le k}[a_i, n_i] & \longrightarrow & [a_0, n_0] \vee [a_1, n_1] \vee \dots [a_k, n_k] \end{array}$$

The case we will use the most is the one of the Segal $A$-precategories $[e, 1] \vee [a, n]$ and $[a, n] \vee [e, 1]$ corresponding to the sequence $((1, n), (a \to e, a \to a))$ and $((n, 1), (a \to a, a \to e))$.

**Definition 3.1.1.6.** Let $B$ be the Reedy category and $M$ the subset of objects of $B$ such that $A$ is the category of $M$-stratified presheaves on $B$. We define the category $\Delta[B]$ as the fully faithful subcategory of $\operatorname{Seg}(A)$ whose objects are of shape $[b, n]$ for $b \in B$ and $n$ an integer. Eventually, we define $\Delta[M]$ as the set of objects of shape $[b, n]$ for $b \in M$ and $n > 0$. We can easily check that the category $\operatorname{Seg}(A)$ is the category of $\Delta[M]$-stratified presheaves on $\Delta[B]$.

A cellular model for $\operatorname{tSeg}(A)$ is given by the set of morphisms $[b, \partial n] \cup [a, n] \to [b, n]$ for $n$ an integer, and $a \to b$ a generating cofibration of $A$.

Eventually, for any Segal $A$-precategory $C$, we have an isomorphism

$$C \cong \underset{\Delta[tB]/C}{\operatorname{colim}} [b, n].$$

Following the definition of section 2.1.2, a morphism between Segal precategories is *entire* if it is the identity on the underlying $\Delta[B]$-presheaves.

**Proposition 3.1.1.7.** *The category $\Delta[B]$ as a structure of elegant Reedy category.*

*Proof.* Remark first that $\operatorname{Hom}_{\Delta[B]}([a, n], [b, m])$ fits in the following cocartesian square:

$$\begin{array}{ccc} \coprod_{k \le m} \operatorname{Hom}_B(a, b) \times \operatorname{Hom}_\Delta([n], \{k\}) & \longrightarrow & \operatorname{Hom}_B(a, b) \times \operatorname{Hom}_\Delta([n], [m]) \\ \downarrow & & \downarrow \\ \coprod_{k \le m} \operatorname{Hom}_\Delta([n], \{k\}) & \longrightarrow & \operatorname{Hom}_{\Delta[B]}([a, n], [b, m]) \end{array}$$

We then define the degree functor $ob(\Delta[B]) \to \mathbb{N}$ by the formula $d([b, n]) = d(b)d(n)$. The subcategory $(\Delta[B])_+$ is the image of $\Delta_+ \times B_+$, and the subcategory $(\Delta[B])_-$ is the image of $\Delta_- \times B_-$.

We recall that we suppose that the Reedy category $B$ is elegant. Let $X$ be a presheaf on $\Delta[B]$, $[a, n]$ an element of $\Delta[A]$, $[f, g]: [a, n] \to [a', n']$ and $[h, i]: [a, n] \to [a', n']$ two negative morphisms, an element $x$ of $X([a, n])$, two non degenerate elements $y \in X([a', n'])$ and $z \in X([a'', n''])$ such that $[f, g]^* y = x$, $[h, i]^* z = x$.

We suppose first that $n \neq 0$. We denote by $\pi: B \times \Delta \to \Delta[B]$ the canonical projection and

$$\pi^*: \operatorname{Psh}(\Delta[B]) \to \operatorname{Psh}(\Delta \times B)$$

103