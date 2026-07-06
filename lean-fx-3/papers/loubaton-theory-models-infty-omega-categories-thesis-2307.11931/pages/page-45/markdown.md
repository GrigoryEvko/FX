1.1. BASIC CONSTRUCTIONS

1.1.3.2. The aim of this subsection is to demonstrate the following proposition:

**Theorem 1.1.3.3.** *For any $a \in \Theta$ and $b \in \Delta[\Theta]$, morphisms $i_!i^*a \to a$ and $b \to i^*i_!b$ are respectively in $\overline{\mathrm{W}}$ and $\overline{\mathrm{M}}$.*

As a corollary, we directly have:

**Corollary 1.1.3.4.** *The adjunction*

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta])_\mathrm{M} \xleftarrow{\quad} \mathrm{Psh}(\Theta)_\mathrm{W} : \mathbf{R}i^*$$

*given in (1.1.2.18) is an adjoint equivalence. For any integer $n$, the adjunction*

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta]_n)_{\mathrm{M}_n} \xleftarrow{\quad} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_n} : \mathbf{R}i^*$$

*given in (1.1.2.19) is an adjoint equivalence.*

*Proof.* The first assertion is a consequence of theorem 1.1.3.3 and of the fact that $\overline{\mathrm{W}}$ (resp. $\overline{\mathrm{M}}$) is a included in the smallest class containing W (resp. M) and stable by two out of three and colimits. We prove the second assertion similarly. $\square$

1.1.3.5. We denote by

$$[\_, \_] : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$$

the extension by colimit of the functor $\Theta \times \Delta \to \mathrm{Psh}(\Delta[\Theta])$ sending $(a, n)$ onto $[a, n]$. For an integer $n$, we denote

$$[\_, n] : \mathrm{Psh}(\Theta)^n \to \mathrm{Psh}(\Theta)$$

the extension by colimit of the functor $\Theta^n \to \mathrm{Psh}(\Theta)$ sending $\mathbf{a} := \{a_1, \dots, a_n\}$ onto $[\mathbf{a}, n]$. Eventually, we define

$$[\_, d^0 \cup d^n] : \mathrm{Psh}(\Theta)^n \to \mathrm{Psh}(\Theta)$$

the extension by colimit of the functor $\Theta^n \to \mathrm{Psh}(\Theta)$ sending $\mathbf{a} := \{a_1, \dots, a_n\}$ onto the colimit of the span.

$$[\{a_0, \dots, a_{n-2}\}, n-1] \leftarrow [\{a_1, \dots, a_{n-2}\}, n-2] \to [\{a_1, \dots, a_{n-1}\}, n-1]$$

**Lemma 1.1.3.6.** *The image of $\overline{\mathrm{W}} \times \overline{\mathrm{W}_1}$ by the functor $[\_, \_] : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$ is included in $\overline{\mathrm{W}}$.*

*Proof.* As $[\_, \_]$ preserves colimits and monomorphisms, it is enough to show that for any pair $f, g \in \mathrm{W} \times \mathrm{W}_1$, $[f, g]$ is in W which is obvious. $\square$

35