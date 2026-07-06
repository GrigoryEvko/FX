Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:33

At $\boldsymbol{x} = \mathbf{0}$, this term is $F(\mathsf{bool}_{*})(\mathsf{bool}_{*})(\mathsf{ff})(\mathsf{ff})$, and at $\boldsymbol{x} = \mathbf{1}$ it is $FA_{*}B_{*}ab$. Now we apply the Graph Lemma to obtain a term in $\mathsf{Gr}_{x}(\mathsf{bool}_{*} \wedge \mathsf{bool}_{*}, A_{*} \wedge B_{*}, [a]_{*} \wedge [b]_{*})$ with the same boundary. Finally, we apply $\mathsf{ungel}$ to extract a path from $([a]_{*} \wedge [b]_{*})(F(\mathsf{bool}_{*})(\mathsf{bool}_{*})(\mathsf{ff})(\mathsf{ff}))$ to $FA_{*}B_{*}ab$. We therefore see that $F$ is the pairing function if $F(\mathsf{bool}_{*})(\mathsf{bool}_{*})(\mathsf{ff})(\mathsf{ff})$ is $\langle\langle\mathsf{ff}, \mathsf{ff}\rangle\rangle$ and the constant function if it is $\langle\langle\mathsf{tt}, \mathsf{tt}\rangle\rangle$; by Lemma 3.26, we are in one of these two cases.

**Corollary 3.28.** $(A_{*}, B_{*}\mathcal{U}_{\mathsf{pt}}) \to A \to B \to A_{*} \wedge B_{*}$ is a set: any pair of paths between two elements of the type are path-equal.

*Proof.* Lemma 3.27 shows that the type is isomorphic to $\mathsf{bool}$, which is a set.

This is everything we need to prove the final result.

*Proof of Theorem 3.20.* Let $F_{*} \in (A_{*}, B_{*}\mathcal{U}_{\mathsf{pt}}) \to A_{*} \wedge_{*} B_{*} \to A_{*} \wedge_{*} B_{*}$ be given. To characterize $F_{*}$, we need to characterize its behavior on each constructor of $A_{*} \wedge B_{*}$ as well as the proof that it preserves the basepoint of $A_{*} \wedge_{*} B_{*}$.

First, by Lemma 3.27, we know that $\lambda^{\sharp}a.\lambda^{\sharp}b.FA_{*}B_{*}(\langle\langle a,b\rangle\rangle)$ is either pairing or constant. The values of $FA_{*}B_{*}\circledast^{\mathsf{L}}$ and $FA_{*}B_{*}\circledast^{\mathsf{R}}$ must be path-equal to $\circledast^{\mathsf{L}}$ and $\circledast^{\mathsf{R}}$ respectively, as $F$ is basepoint-preserving and $\circledast^{\mathsf{L}}$ ($\circledast^{\mathsf{R}}$) is connected to the basepoint by $\mathsf{spoke}^{\mathsf{L}}(b_{0}, -)$ ($\mathsf{spoke}^{\mathsf{R}}(a_{0}, -)$).

Next, observe that we can capture the behavior of $F$ on $\mathsf{spoke}^{\mathsf{L}}$ by the following term, which is a path in $(A_{*}, B_{*}\mathcal{U}_{\mathsf{pt}}) \to A \to B \to A_{*} \wedge_{*} B_{*}$ between $\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda_{\dots}FA_{*}B_{*}\circledast^{\mathsf{L}}$ and $\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda b.FA_{*}B_{*}(\langle\langle a,b\rangle\rangle)$.

$$\lambda^{\sharp}y.\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda b.FA_{*}B_{*}(\mathsf{spoke}^{\mathsf{L}}(b, y))$$

By Corollary 3.28, this path is path-equal to any other path in this type, in particular path-equal to whatever we need it to be to complete this proof. The same applies to $\circledast^{\mathsf{R}}$. Finally, we can apply the same trick for the basepoint path, writing it as a path in the type from Corollary 3.28 as follows.

$$\lambda^{\sharp}y.\lambda A_{*}.\lambda B_{*}.\lambda_{\dots}\lambda_{\dots}f_{0}A_{*}B_{*}\circledast y$$

Now we argue that this strategy can be used to prove the $n$-ary generalization in a uniform way. (The binary version is in fact not very useful on its own; the direct proof of commutativity for the smash product is uncharacteristically straightforward, because the definition of $\wedge$ is completely symmetric.)

**Theorem 3.29.** Any function $(A_{*}^{0}, \dots, A_{*}^{n}\mathcal{U}_{\mathsf{pt}}) \to (A_{*}^{0} \wedge_{*} \dots \wedge_{*} A_{*}^{n}) \to (A_{*}^{0} \wedge_{*} \dots \wedge_{*} A_{*}^{n})$ (associating $\wedge_{*}$ to the right) is either the polymorphic identity or the polymorphic constant pointed function.

*Proof.* We show by induction on $i \leq n + 1$ that any

$$(A_{*}^{0}, \dots, A_{*}^{n}\mathcal{U}_{\mathsf{pt}}) \to A^{0} \to \dots \to A^{n-i} \to (A_{*}^{n-i+1} \wedge_{*} \dots \wedge_{*} A_{*}^{n}) \to (A_{*}^{0} \wedge_{*} \dots \wedge_{*} A_{*}^{n})$$

is either given by iterated pairing or constant. For $i = 0$, it follows from a simple $n$-ary generalization of the workhorse lemma (instantiating each type argument with a graph and applying the binary Graph Lemma repeatedly). For $i > 0$, it follows from the induction hypothesis by the same argument as in the proof of Theorem 3.20.