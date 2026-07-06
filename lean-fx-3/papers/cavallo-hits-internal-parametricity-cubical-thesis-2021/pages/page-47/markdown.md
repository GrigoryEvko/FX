A logic of programs 35

# **Rules 2.1.39 (Elimination for natural numbers).**

ELIMINATION

$$\begin{array}{c} n : \text{Nat} \gg B = B' \text{ type} \\ \nvdash N = N' \in \text{Nat} \quad \nvdash Z = Z' \in B[\text{zero}/n] \quad n : \text{Nat}, b : B \gg S = S' \in B[\text{suc}(n)/n] \\ \hline \nvdash \text{elim}_{\text{Nat}}(n.B; N; Z, n.b.S) = \text{elim}_{\text{Nat}}(n.B'; N'; Z', n.b.S') \in B[N/n] \end{array}$$

REDUCTION-ZERO

$$\begin{array}{c} \nvdash Z \in B[\text{zero}/n] \\ \hline \nvdash \text{elim}_{\text{Nat}}(n.B; \text{zero}; Z, n.b.S) = Z \in B[\text{zero}/n] \end{array}$$

REDUCTION-SUC

$$\begin{array}{c} n : \text{Nat} \gg B \text{ type} \\ \nvdash N \in \text{Nat} \quad \nvdash Z \in B[\text{zero}/n] \quad n : \text{Nat}, b : B \gg S \in B[\text{suc}(n)/n] \\ \hline \nvdash \text{elim}_{\text{Nat}}(n.B; \text{suc}(N); Z, n.b.S) = S[N/n, \text{elim}_{\text{Nat}}(n.B; N; Z, n.b.S)/b] \in B[\text{suc}(N)/n] \end{array}$$

Because of the recursive character of Nat, we need a bit of setup to prove the well-typedness of the eliminator. We begin by defining a value relation $E_{\text{Nat}}$ whose elements are the values on which the Nat eliminator is well-behaved.

**Definition 2.1.40.** We define $V \approx V' \in E_{\text{Nat}}$ to hold when $V \approx V' \in [\![\text{Nat}\!\!]]$ and for every $n : \text{Nat} \gg B = B'$ type, $Z = Z' \in B[\text{zero}/n]$, and $n : \text{Nat}, b : B \gg S = S' \in B[\text{suc}(n)/n]$, we have $\nvdash \text{elim}_{\text{Nat}}(n.B; V; Z, n.b.S) = \text{elim}_{\text{Nat}}(n.B'; V'; Z', n.b.S') \in B[V/n]$.

We will show that all values of Nat are contained in $E_{\text{Nat}}$ by exploiting the definition of the value relation for Nat as the least closed under zero and suc.

**Lemma 2.1.41.** $\text{zero} \in E_{\text{Nat}}$.

*Proof.* For any $B, B', Z, Z', S, S'$ as in the definition of $E_{\text{Nat}}$, the operational semantics tells us that $\text{elim}_{\text{Nat}}(n.B; \text{zero}; Z, n.b.S) \longmapsto Z$ and $\text{elim}_{\text{Nat}}(n.B'; \text{zero}; Z', n.b.S') \longmapsto Z'$. That $\nvdash \text{elim}_{\text{Nat}}(n.B; \text{zero}; Z, n.b.S) = \text{elim}_{\text{Nat}}(n.B'; \text{zero}; Z', n.b.S') \in B[\text{zero}/n]$ thus follows from the assumption $\nvdash Z = Z' \in B[\text{zero}/n]$ by head expansion on either side. $\square$