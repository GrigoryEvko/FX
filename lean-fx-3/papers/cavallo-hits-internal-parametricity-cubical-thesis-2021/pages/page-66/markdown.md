54

Cubical type theory

Definition 3.1.8 (Incoherent evaluation). We generalize the evaluation operator $\Downarrow$- from relations (Definition 2.1.8) to $\Psi$-relations pointwise: $M \approx M' \in (\Downarrow R)\langle\psi\rangle$ holds when $M \Downarrow V$ and $M' \Downarrow V'$ with $V \approx V' \in R\langle\psi\rangle$.

Definition 3.1.9 (Coherent evaluation). Given a $\Psi$-relation $R$, we define its coherent extension to terms $\Downarrow R$ as follows. Let $\Psi' \Vdash \psi \in \Psi$ be given. Then $M \approx M' \in (\Downarrow R)\langle\psi\rangle$ holds when for every subsequent pair of substitutions, $\Psi_1 \Vdash \psi_1 \in \Psi'$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, the following conditions are satisfied.

- $M\psi_1 \Downarrow V$ and $M'\psi_1 \Downarrow V'$ for some values $V$ and $V'$.
- $N \approx N' \in \Downarrow R\psi\psi_1\psi_2$ for $N \in \{M\psi_1\psi_2, V\psi_2\}$ and $N' \in \{M'\psi_1\psi_2, V'\psi_2\}$.

Proposition 3.1.10. If $R$ is a $\Psi$-PER, then $\Downarrow R$ is a $\Psi$-PER.

We will ultimately use $\Downarrow$- to define the typing judgments induced by a type system. The third condition imposes the “coherence”; it requires that the following square of substitutions and evaluations commutes up to the equality defined by $\Downarrow R$.

$$\begin{array}{c} M\psi_1 \Longrightarrow V \\ -\psi_2 \downarrow \qquad \qquad \qquad \downarrow -\psi_2 \\ M\psi_1\psi_2 \Longrightarrow \bullet \end{array}$$

The outer quantification over $\psi_1$ ensures that $\Downarrow R$ is always stable under interval substitution; if $M \approx M' \in \Downarrow R$, then $M\psi \approx M'\psi \in \Downarrow R\psi$ for any $\psi$. In order for a value $\Psi$-relation $R$ to be suitable as the interpretation of a type, it must satisfy an additional well-formedness condition called value-coherence, which asks that all values related by $R$ are in fact coherently related by $R$.

Definition 3.1.11. A $\Psi$-relation $R$ on values is value-coherent when $R \subseteq \Downarrow R$.

As with ordinary relations, the collection of $\Psi$-relations on a given field is a lattice, and so we can obtain fixed-points of monotone operators on $\Psi$-relations. To check that these fixed-points are PERs, we again use operators $Sym^+$ and $Trans^+$ defined in Definition 2.1.21, which we extend pointwise to $\Psi$-relations.

Lemma 3.1.12. Let $F$ be a monotone operator on $\Psi$-relations. If we have $F(Sym^+(\mu F)) \subseteq Sym^+(\mu F)$, then $\mu F$ is symmetric. If $F(Trans^+(\mu F)) \subseteq Trans^+(\mu F)$, then $\mu F$ is transitive.

Proposition 3.1.13. We have $\Downarrow Sym^+(R) \subseteq Sym^+(\Downarrow R)$ and $\Downarrow Trans^+(R) \subseteq Trans^+(\Downarrow R)$.