5:26

E. CAVALLO AND R. HARPER

Vol. 17:4

Proof. By Lemma 1.3, it suffices to prove the theorem when $a_1$ is $a_0$ and $p$ is $\lambda^\mathbb{I} \dots a_0$. In that case it follows from Remark 3.3 and the assumption that $B$ is bridge-discrete. $\square$

**Theorem 3.12.** Given $A$ type and $a : A \gg B$ type, if $A$ is bridge-discrete and $B$ is bridge-discrete for all $a : A$, then $(a : A) \times B$ is bridge-discrete.

Proof. Given $t, t' : (a : A) \times B$, we can characterize paths between $t$ and $t'$ as pairs of paths between their components.

$$\mathsf{Path}_{(a:A) \times B}(t, t') \simeq (p : \mathsf{Path}_A(\mathsf{fst}(t), \mathsf{fst}(t'))) \times \mathsf{Path}_{x.B[p@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t'))$$

In the forward direction we have $\lambda p. \langle \lambda^\mathbb{I} x.\mathsf{fst}(p@x), \lambda^\mathbb{I} x.\mathsf{snd}(p@x) \rangle$, and in the reverse we have $\lambda \langle q_0, q_1 \rangle. \lambda^\mathbb{I} x. \langle q_0@x, q_1@x \rangle$; these are clearly inverses. We can repeat the proof to obtain an analogous characterization of bridges in $(a : A) \times B$.

$$\mathsf{Bridge}_{(a:A) \times B}(t, t') \simeq (p : \mathsf{Bridge}_A(\mathsf{fst}(t), \mathsf{fst}(t'))) \times \mathsf{Bridge}_{x.B[p@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t'))$$

By assumption, we know that $\mathsf{Path}_A(\mathsf{fst}(t), \mathsf{fst}(t'))$ and $\mathsf{Bridge}_A(\mathsf{fst}(t), \mathsf{fst}(t'))$ are isomorphic via $\mathsf{loosen}_A$. To show that the product types are isomorphic, it then suffices to show the second component types are isomorphic over $\mathsf{loosen}_A$, i.e., that the following holds for all $p : \mathsf{Path}_A(\mathsf{fst}(t), \mathsf{fst}(t'))$.

$$\mathsf{Path}_{x.B[p@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t')) \simeq \mathsf{Bridge}_{x.B[\mathsf{loosen}_A(p)@x/a]}(\mathsf{snd}(t), \mathsf{snd}(t'))$$

This is immediate by Lemma 3.11. $\square$

**Theorem 3.13.** Given $A$ type and $a : A \gg B$ type, if $A$ is bridge-discrete and $B$ is bridge-discrete for all $a : A$, then $(a:A) \to B$ is bridge-discrete.

Proof. Analogous to Theorem 3.12, using Lemmas 1.2 and 2.1. $\square$

**Theorem 3.14.** If $A$ type is bridge-discrete, then $\mathsf{Path}_A(a, b)$ is bridge-discrete for all $a, b : A$.

Proof. Given $p, q : \mathsf{Path}_A(a, b)$, We have the following chain of isomorphisms.

$$\begin{array}{l} \mathsf{Path}_{\mathsf{Path}_A(a,b)}(p, q) \simeq \mathsf{Path}_{x.\mathsf{Path}_A(p@x, q@x)}(\lambda^\mathbb{I} \dots a, \lambda^\mathbb{I} \dots b) \\ \simeq \mathsf{Path}_{x.\mathsf{Bridge}_A(p@x, q@x)}(\mathsf{loosen}_A(\lambda^\mathbb{I} \dots a), \mathsf{loosen}_A(\lambda^\mathbb{I} \dots b)) \\ \simeq \mathsf{Path}_{x.\mathsf{Bridge}_A(p@x, q@x)}(\lambda^\mathbb{I} \dots a, \lambda^\mathbb{I} \dots b) \\ \simeq \mathsf{Bridge}_{\mathsf{Path}_A(a,b)}(p, q) \end{array}$$

The first step is by reordering interval abstractions, the second by Remark 3.3, the third by assumption that $A$ is bridge-discrete, and the fourth by reordering abstractions again. $\square$

**Corollary 3.15.** If $A$ type is bridge-discrete, then $\mathsf{Bridge}_A(a, b)$ is bridge-discrete for all $a, b : A$.

**Theorem 3.16.** bool is bridge-discrete.

Proof. We must define a right inverse to $\mathsf{loosen}_{\mathsf{bool}} \in \mathsf{Path}_{\mathsf{bool}}(b, b') \to \mathsf{Bridge}_{\mathsf{bool}}(b, b')$ for every $b, b' : \mathsf{bool}$. For simplicity, we prove the case where $b = \mathsf{tt}$ and $b' = \mathsf{ff}$; the other cases follow by the same argument. In this case, we first need a function of the following type.

$$\mathsf{tighten} \in \mathsf{Bridge}_{\mathsf{bool}}(\mathsf{tt}, \mathsf{ff}) \to \mathsf{Path}_{\mathsf{bool}}(\mathsf{tt}, \mathsf{ff})$$