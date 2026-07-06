The proposition states that the structural maps (associativity and unit isomorphisms) of the Gray tensor product of $\infty$-categories preserve the marking we specified on the tensor product.

For the unit, let $(X, M)$ be an $m$-marked $\infty$-category. The Lemmas 2.25 and 2.28 imply that

$$\begin{aligned} (X, M) \ominus (\mathbb{D}_0, \overline{\emptyset}) &= (X \otimes \mathbb{D}_0, \overline{M \ominus \emptyset}) &= (X, M) \\ (X, M) \ominus (\mathbb{D}_0, \overline{\emptyset}) &= (X \otimes \mathbb{D}_0, \overline{M \ominus \emptyset}) &= (X, M) \end{aligned}$$

and

$$\begin{aligned} (\mathbb{D}_0, \overline{\emptyset}) \ominus (X, M) &= (\mathbb{D}_0 \otimes X, \overline{\emptyset \ominus M}) &= (X, M) \\ (\mathbb{D}_0, \overline{\emptyset}) \ominus (X, M) &= (\mathbb{D}_0 \otimes X, \overline{\emptyset \ominus M}) &= (X, M) \end{aligned}$$

For the associativity isomorphism, let $(X, M)$, $(Y, N)$, and $(Z, P)$ be three marked $\infty$-categories. Lemma 2.25 implies that

$$\begin{aligned} \big((X, M) \ominus (Y, N)\big) \ominus (Z, P) &= (X \otimes Y \otimes Z, \overline{(M \ominus N) \ominus P}) \\ \big((X, M) \ominus (Y, N)\big) \ominus (Z, P) &= (X \otimes Y \otimes Z, \overline{(M \ominus N) \ominus P}) \end{aligned}$$

and

$$\begin{aligned} (X, M) \ominus \big((Y, N) \ominus (Z, P)\big) &= (X \otimes Y \otimes Z, \overline{M \ominus (N \ominus P)}) \\ (X, M) \ominus \big((Y, N) \ominus (Z, P)\big) &= (X \otimes Y \otimes Z, \overline{M \ominus (N \ominus P)}) \end{aligned}$$

Lemma 2.27 shows that these two markings on $X \otimes Y \otimes Z$, in the lax and pseudo cases, coincide. $\square$

**2.30 Proposition.** *The pseudo and lax-Gray tensor products $\ominus$ and $\ominus$ preserve colimits in each variable.*

*Proof.* It follows from the fact that the Gray tensor product $\otimes$ preserves colimits in each variable, the description of colimits of $m$-marked $\infty$-categories given in Construction 2.19, and Lemma 2.25. $\square$

**2.31 Remark.** Remark 2.20 states that $\infty$-Cat$^{+m}$ is locally presentable. Consequently, the preceding proposition implies that the functors $C \ominus -$, $-\ominus C$, $C \ominus -$, and $-\ominus C$ admit right adjoints. In particular, this immediately implies that both tensor products are closed monoidal structures.

## 2.4 The Inductive Left Semi-Model Structure

In this section, we will construct a left semi-model structure on the category $\infty$-Cat$^{+m}$. The definitions and results on left semi-model structures that we will use here are recalled in Appendix A.

**2.32 Definition.** We define the set $I = I^\partial \cup I^{+m}$ to be our *set of generating cofibrations* in $\infty$-Cat$^{+m}$ where:

$$\begin{aligned} I^\partial &= \{i_n : \partial \mathbb{D}_n^b \to \mathbb{D}_n^b \mid n \geqslant 0\} \\ I^{+m} &= \{\mathbb{D}_n^b \to (\mathbb{D}_n, \overline{\{e_n\}}) \mid n \geqslant 0\} \end{aligned}$$

An arrow in $\infty$-Cat$^{+m}$ is said to be an *acyclic fibration* if it has the right lifting property against all arrows in $I$. An arrow in $\infty$-Cat$^{+m}$ is said to be a *cofibration* if it has the left lifting property against all acyclic fibrations.

16