CHAPTER 4. THE $(\infty, 1)$-CATEGORY OF $(\infty, \omega)$-CATEGORIES

By construction, the functor $\_ \ominus \_$ commutes with colimits in both variables. We also have the identification $C \ominus [1] := C \otimes [1]$.

Eventually, formula (4.3.1.7) induces a natural identification between $[C, 1] \ominus [b, 1]$ and the colimit of the following diagram

$$[b, 1] \vee [C, 1] \leftarrow [C \otimes \{0\} \times b, 1] \rightarrow [(C \otimes [1]) \times b), 1] \leftarrow [C \otimes \{1\} \times b, 1] \rightarrow [C, 1] \vee [b, 1] \tag{4.3.1.15}$$

### 4.3.2 Gray deformation retract

4.3.2.1. A left $k$-Gray deformation retract structure for a morphism $i : C \to D$ is the data of a retract $r : D \to C$, a deformation $\psi : D \otimes_k [1] \to D$, and equivalences

$$ri \sim id_C \qquad \psi_{|D \otimes_k \{0\}} \sim ir \qquad \psi_{|D \otimes_k \{1\}} \sim id_D \qquad \psi_{|C \otimes_k [1]} \sim i \operatorname{cst}_C$$

A morphism $i : C \to D$ between $(\infty, \omega)$-categories is a left $k$-Gray deformation retract if it admits a left deformation retract structure. By abuse of language, such data will just be denoted by $(i, r, \psi)$.

We define dually the notion of right $k$-Gray deformation retract structure and of right $k$-Gray deformation retract in exchanging 0 and 1 in the previous definition.

4.3.2.2. A left $k$-Gray deformation retract structure for a morphism $i : f \to g$ in the $(\infty, 1)$-category of arrows of $(\infty, \omega)$-cat is the data of a retract $r : g \to f$, a deformation $\psi : g \otimes_k [1] \to g$ and equivalences

$$ri \sim id_f \qquad \psi_{|g \otimes_k \{0\}} \sim ir \qquad \psi_{|g \otimes_k \{1\}} \sim id_D \qquad \psi_{|f \otimes_k [1]} \sim i \operatorname{cst}_C$$

A morphism $i : C \to D$ between arrows of $(\infty, \omega)$-cat is a left $k$-Gray deformation retract if it admits a left deformation retract structure. By abuse of language, such data will just be denoted by $(i, r, \psi)$.

We define dually the notion of right $k$-Gray deformation retract structure and of right $k$-Gray deformation retract in exchanging 0 and 1 in the previous definition.

Example 4.3.2.3. Let $k \in \mathbb{N} \cup \{\omega\}$ and let $C$ be an $(\infty, k)$-category. We consider the morphism $i : C \otimes \{0\} \to C \otimes [1]$. We define $r : C \otimes [1] \xrightarrow{C \otimes 1} C \otimes \{0\}$. Eventually, we set

$$\psi : C \otimes [1] \otimes [1] \to C \otimes ([1] \times [1]) \xrightarrow{C \otimes \phi} C \otimes [1]$$

where $\phi : [1] \times [1]$ is the morphism sending $(i, j)$ on the minimum of $i$ and $j$.

212