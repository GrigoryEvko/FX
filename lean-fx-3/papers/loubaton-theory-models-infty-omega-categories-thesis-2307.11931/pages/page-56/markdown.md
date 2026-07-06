CHAPTER 1. THE CATEGORY OF $(0, \omega)$-CATEGORIES

induce isomorphisms:

$$[\langle B \rangle] \cong B \quad \text{and} \quad E \cong \langle [E] \rangle.$$

**1.2.1.24.** We define the *full duality*

$$(\_)^\circ : \mathrm{ADC} \to \mathrm{ADC}$$

that sends a augmented directed complex $((K, \partial), K^*, e)$ to $((K, -\partial), K^*, e)$. We left the reader to check that $K^\circ$ admits a loop free and atomic basis when this is the case for $K$. This functor then induces a functor:

$$(\_)^\circ : \mathrm{ADC}_\mathrm{B} \to \mathrm{ADC}_\mathrm{B}.$$

Moreover, we have a canonical equivalence:

$$\lambda(C^\circ) \cong (\lambda C)^\circ$$

natural in $C$.

**1.2.1.25.** Let $f : M \to N$ be a morphism between two augmented directed complexes admitting unitary and loop-free bases $B_M$ and $B_N$. The morphism $f$ is *quasi-rigid* if for any $n$, and any $b \in (B_M)_n$,

$$f_n(b) \neq 0 \ \Rightarrow \ f_n(b) \in B_N \text{ and } \nu(f)\langle b \rangle = \langle f_n(b) \rangle.$$

**Theorem 1.2.1.26.** *Suppose given a commutative square in $\mathrm{ADC}_\mathrm{B}$*

$$\begin{array}{ccc} K & \xrightarrow{k^0} & M_1 \\ k^0 \Big\downarrow & & \Big\downarrow l^1 \\ M_0 & \xrightarrow{l^0} & M \end{array}$$

*and such that all morphisms are quasi-rigid. Let $B_K$, $B_{M_0}$, $B_{M_1}$, $B_M$ be the bases of $K$, $M_0$, $M_1$, $M$.*

*Then, this square is cocartesian if and only if for any $n$, the induced diagram of sets*

$$\begin{array}{ccc} (B_K)_n \cup \{0\} & \xrightarrow{k_n^0} & (B_{M_1})_n \cup \{0\} \\ k_n^0 \Big\downarrow & & \Big\downarrow l_n^1 \\ (B_{M_0})_n \cup \{0\} & \xrightarrow{l_n^0} & (B_M)_n \cup \{0\} \end{array}$$

46