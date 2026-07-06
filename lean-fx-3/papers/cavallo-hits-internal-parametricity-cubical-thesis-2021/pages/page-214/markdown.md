202

Programming with parametricity

Proof. Suppose we are given $d : \text{LEM}_{\neg}$. Then $\lambda A. \text{fst}(dA)$ is a function $U \to \text{Bool}$, so is constant by Lemma 10.4.2 and Theorem 10.3.7. But this implies that $\text{fst}(d\text{Unit})$ and $\text{fst}(d\text{Void})$ have the same value, from which we readily derive a contradiction. $\square$

Corollary 10.4.4. The excluded middle for propositions is refuted.

For further analysis of the relationship between classical principles and parametricity, we refer to Booij et al. [BELS16].

## 10.5 Iterated smash products

Finally, we return to our motivating example of an application of parametricity unique to higher-dimensional type theory: coherence laws for the smash product. Recall from Chapter 8 that the smash product of two pointed types $A_*, B_* \in U_* := (A : U) \times A$ is the following higher inductive type.

$$
\begin{array}{l}
A_* : U_*, B_* : U_* \gg \textbf{inductive } A_* \wedge B_* \textbf{ where} \\
| \langle \langle a : A, b : B \rangle \rangle \in A_* \wedge B_* \\
| \circledast^L \in A_* \wedge B_* \\
| \text{spoke}^L(b : B, x : \mathbb{I}) \in A_* \wedge B_* \quad [x \equiv 0 \hookrightarrow \circledast^L \mid x \equiv 1 \hookrightarrow \langle \langle a_0, b \rangle \rangle] \\
| \circledast^R \in A_* \wedge B_* \\
| \text{spoke}^R(a : A, x : \mathbb{I}) \in A_* \wedge B_* \quad [x \equiv 0 \hookrightarrow \circledast^R \mid x \equiv 1 \hookrightarrow \langle \langle a, b_0 \rangle \rangle]
\end{array}
$$

Notation 10.5.1 (Recollections from Chapter 8). We abbreviate $A := \text{fst}(A_*) \in U$ and $a_0 := \text{snd}(A_*) \in A$ for the underlying type and point of a given pointed type $A_* \in U_*$. Given $A_*, B_* \in U_*$, we have the type $(A_* \to B_*) := (f : A \to B) \times \text{Path}(B, f a_0, b_0) \in U$ of functions that send the basepoint of $A$ to that of $B$. For the pointed type of such functions, we write $(A_* \to_* B_*) := \langle A_* \to B_*, \langle \lambda_-, b_0, \lambda^\mathbb{I}_-, b_0 \rangle \rangle \in U_*$; we write $f_*$ for elements of this type and abbreviate $f := \text{fst}(f_*)$ and $f_0 := \text{snd}(f)$ as with types. A pointed isomorphism, written $A_* \simeq B_*$, is an isomorphism whose underlying function is pointed.

The elements of the smash product are pairs $\langle \langle a : A, b : B \rangle \rangle$ but with all elements of the form $\langle \langle a_0, b \rangle \rangle$ identified with a distinguished point $\circledast^L$ and all elements of the form $\langle \langle a, b_0 \rangle \rangle$ identified with $\circledast^R$. We write $A_* \wedge_* B_*$ for the pointed type $\langle A_* \wedge B_*, \langle \langle a_0, b_0 \rangle \rangle \rangle$.

In Chapter 8, we imagined that various coherence conditions expected of the commutator and associator—themselves feasible if tedious to construct—could be verified automatically by using parametricity. First, we note that it suffices to characterize the inhabitants of types of the following form, where the input and output smash products are both associated in the same (arbitrary) way.

$$
(A_{1*}, \dots, A_{n*} : U_*) \to (A_{1*} \wedge_* \dots \wedge_* A_{n*}) \to (A_{1*} \wedge_* \dots \wedge_* A_{n*}) \tag{*}
$$