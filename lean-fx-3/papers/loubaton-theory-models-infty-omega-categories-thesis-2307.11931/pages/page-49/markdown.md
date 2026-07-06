1.1. BASIC CONSTRUCTIONS

fulfilling the desired condition. The bijection (1.1.3.9) directly implies that $j$ is equal to $i$, and the first assertion implies that $\tilde{f}$ is non degenerate.

We can then factor $\tilde{f}: b \to \tilde{b}$ in a degenerate morphism $b \to \tilde{b}$ followed by a monomorphism $\tilde{b} \to \tilde{b}$ which is not the identity. The lemma 1.1.3.11 then implies that $\{\tilde{b} \to \tilde{b} \to a_i\}_{i<n}$ is an element of $\Theta_{/\mathbf{a}}^{\rightarrow}$. The first assertion then implies that the two morphisms $[b, m] \to [b', n]$ and $[b, m] \to [\tilde{b}, n]$ are equals. As the monomorphism $[b', n] = [\tilde{b}, n] \to [\tilde{b}, n]$ is not the identity, this concludes the proof. $\square$

**Lemma 1.1.3.14.** *The morphism $i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n] \to i^*[\mathbf{a}, n]$ is in $\overline{\mathrm{M}}$, where $\partial^j \mathbf{a}$ corresponds to the sequence $\{a_1, .., \partial a_j, .., a_n\}$.*

*Proof.* For $k \in \mathbb{N} \cup \{\infty\}$, we define $x_k$ as the smallest sub object of $i^*[\mathbf{a}, n]$ such that for any element of height inferior or equal to $k$ of $\Theta_{/\mathbf{a}}^{\rightarrow}$, the corresponding morphism $[b, n] \to i^*[\mathbf{a}, n]$ factors through $x_k$. In particular we have $x_0 = i^*[\partial^0 \mathbf{a}, n] \cup i^*[\partial^{n-1} \mathbf{a}, n]$, and the lemma 1.1.3.10 implies that $x_\infty = i^*[\mathbf{a}, n]$.

Every morphism $[b, m] \to i^*[\mathbf{a}, n]$ that does not preserve extremal points then factors through $x_0$. The lemma 1.1.3.13 implies that for any integer $k$, the canonical square

$$\begin{array}{c} \coprod_{(\Theta_{/\mathbf{a}}^{\rightarrow})_{k+1}} [b, d^0 \cup d^n] \cup [\partial b, n] \longrightarrow x_k \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{(\Theta_{/\mathbf{a}}^{\rightarrow})_{k+1}} [b, n] \longrightarrow x_{k+1} \end{array} \tag{1.1.3.15}$$

is cocartesian. The lemma 1.1.3.7 and the stability under pushout of $\overline{\mathrm{M}}$ imply that $x_k \to x_{k+1}$ is in $\overline{\mathrm{M}}$. As $i^*[\mathbf{a}, n]$ is the transfinite composition of the sequence $x_0 \to x_1 \to \dots$, this implies that $x_0 \to i^*[\mathbf{a}, n]$ is in $\overline{\mathrm{M}}$ which conclude the proof. $\square$

**Lemma 1.1.3.16.** *The morphism $i^* \mathrm{Sp}_a \to i^* a$ is in $\overline{\mathrm{M}}$ for any globular sum $a$.*

*Proof.* Let $[\mathbf{a}, n] := a$. As $\overline{\mathrm{M}}$ is closed under pushouts and composition, lemma 1.1.3.14 implies that the morphism

$$i^*[\{a_0, \dots, a_{n-2}\}, n-1] \cup i^*[\{a_1, \dots, a_{n-1}\}, n-1] \to i^*[\mathbf{a}, n]$$

is in $\widehat{\mathrm{M}}$. An easy induction on $n$ shows that this is also the case for the morphism

$$[a_0, 1] \cup \dots \cup [a_{n-1}, 1] = i^*[a_0, 1] \cup \dots \cup i^*[a_{n-1}, 1] \to i^*[\mathbf{a}, n].$$

Now remark that $i^* \mathrm{Sp}_{[\mathbf{a}, n]}$ is equivalent to

$$[\mathrm{Sp}_{a_0}, 1] \cup \dots \cup [\mathrm{Sp}_{a_{n-1}}, 1].$$

As the morphisms $[\mathrm{Sp}_i, 1] \to [a_i, 1]$ are by definition in $\mathrm{M}$, this concludes the proof. $\square$

39