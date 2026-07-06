Iterated smash products 207

Next, observe that we can capture the behavior of $F$ on spoke$^{\text{L}}$ by the following term, which is a path in $(A_*, B_*: \cup_*) \rightarrow A \rightarrow B \rightarrow A_* \wedge_* B_*$ between $\lambda A_*, \lambda B_*, \lambda_-, \lambda_-, F A_* B_* \circledast^{\text{L}}$ and $\lambda A_*, \lambda B_*, \lambda_-, \lambda b. F A_* B_* \langle \langle a, b \rangle \rangle$.

$$\lambda^{\text{I}} y. \lambda A_*, \lambda B_*, \lambda_-, \lambda b. F A_* B_* \text{ (spoke}^{\text{L}}(b, y))$$

By Corollary 10.5.10, this path is path-equal to any other path in this type, in particular path-equal to whatever we need it to be to complete this proof. The same applies to $\circledast^{\text{R}}$. Finally, we can apply the same trick for the basepoint path, writing it as a path in the type from Corollary 10.5.10 as follows.

$$\lambda^{\text{I}} y. \lambda A_*, \lambda B_*, \lambda_-, \lambda_-, f_0 A_* B_* y \quad \square$$

Now we argue that this strategy can be used to prove the $n$-ary generalization in a uniform way. (The binary version is in fact not very useful on its own; the direct proof of commutativity for the smash product is uncharacteristically straightforward because the definition of $\wedge$ is completely symmetric.)

**Theorem 10.5.11.** Any function of the form $(\ast)$ is either the polymorphic identity or the polymorphic constant pointed function.

*Proof.* First, consider the case where we associate to the left everywhere in $(\ast)$. We show by induction on $i \leq n + 1$ that any

$$A_0 \rightarrow \cdots \rightarrow A_{n-i} \rightarrow (A_{(n-i+1)*} \wedge_* \cdots \wedge_* A_{n*}) \rightarrow (A_{0*} \wedge_* \cdots \wedge_* A_{n*})$$

polymorphic in $A_{0*}, \dots, A_{n*}: \cup_*$ is either given by iterated pairing or constant. For $i = 0$, it follows from a simple $n$-ary generalization of the workhorse lemma (instantiating each type argument with a graph and applying the binary Graph Lemma repeatedly). For $i > 0$, it follows from the induction hypothesis by the same argument as in the proof of Theorem 10.5.2.

The case where we associate to the right everywhere then follows from commutativity of the smash product. These two cases are sufficient to prove associativity, from which the theorem follows for all other associations. $\square$

The key here is that we are never involved in an iterated induction on smash products: for each $i$ in the proof of Theorem 10.5.11, we have an argument by induction on one occurrence of the smash product, but these arguments do not overlap.