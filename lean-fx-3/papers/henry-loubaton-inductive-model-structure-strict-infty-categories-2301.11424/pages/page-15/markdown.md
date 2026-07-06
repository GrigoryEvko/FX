**2.27 Lemma.** Let $X, Y, Z$ be three $\infty$-categories, $M \subset X_{>0}$, $N \subset Y_{>0}$ and $P \subset Z_{>0}$. Then we have

$$\begin{array}{rcl} \overline{(M \ominus N) \ominus P} & = & \overline{M \ominus (N \ominus P)} \\ \overline{(M \ominus N) \ominus P} & = & \overline{M \ominus (N \ominus P)} \end{array}$$

*Proof.* We begin with the first equality. Let

$$E := (M \otimes Y_{\geqslant 0} \otimes Z_{\geqslant 0}) \cup (X_{\geqslant 0} \otimes N \otimes Z_{\geqslant 0}) \cup (X_{\geqslant 0} \otimes Y_{\geqslant 0} \otimes P).$$

The lemmas 2.23, 2.24, and 2.25 imply the following equalities:

$$\begin{aligned} \overline{E} & = \overline{M \otimes Y_{\geqslant 0} \otimes Z_{\geqslant 0}} \cup X_{\geqslant 0} \otimes (N \otimes Z_{\geqslant 0} \cup Y_{\geqslant 0} \otimes P) \\ & = \overline{M \otimes (Y \otimes Z)_{\geqslant 0}} \cup X_{\geqslant 0} \otimes (N \ominus P) \\ & = \overline{M \ominus (N \ominus P)} \end{aligned}$$

A very similar computation also shows that $\overline{E} = \overline{(M \ominus N) \ominus P}$, which concludes the proof of the first equality.

For the second equality, we define

$$F := (X_{\geqslant 0} \otimes Y_{>0} \otimes Z_{>0}) \cup (X_{>0} \otimes Y_{\geqslant 0} \otimes Z_{>0}) \cup (X_{>0} \otimes Y_{>0} \otimes Z_{\geqslant 0})$$

The second equality of Lemma 2.23 implies that:

$$\overline{F} = \overline{X_{\geqslant 0} \otimes Y_{>0} \otimes Z_{>0} \cup X_{>0} \otimes (Y \otimes Z)_{>0}}$$

and then that

$$\begin{aligned} \overline{E \cup F} & = \overline{M \otimes (Y \otimes Z)_{\geqslant 0}} \cup X_{\geqslant 0} \otimes (N \ominus P) \cup X_{>0} \otimes (Y \otimes Z)_{>0} \\ & = \overline{M \ominus (N \ominus P)} \end{aligned}$$

and here again, a similar computation shows $\overline{E \cup F} = \overline{(M \ominus N) \ominus P}$, which concludes the proof. $\square$

**2.28 Lemma.** Let $X$ be an $\infty$-category, $M \subset X_{>0}$. Then the empty set, considered as a subset of the $\infty$-category $\mathbb{D}_0$, satisfies (up to the identifications $\mathbb{D}_0 \otimes X \simeq X \otimes \mathbb{D}_0 \simeq X$):

$$\begin{array}{l} \emptyset \ominus M = M \ominus \emptyset = M \\ \overline{\emptyset \ominus M} = \overline{M \ominus \emptyset} = \overline{M} \end{array}$$

*Proof.* The first equality is a straightforward application of the definition of $\ominus$. For the second case, we also use the fact that all arrows of $(\mathbb{D}_0)_{>0} \otimes X_{>0}$ are identities and so all belong to $\overline{M}$. $\square$

**2.29 Proposition.** Both the *lax-Gray tensor product* $\ominus$ and the *pseudo-Gray tensor product* $\ominus$, as defined above, are monoidal structures on the category of $m$-marked $\infty$-categories. In both cases, the forgetful functor to $\infty$-categories is monoidal, and their unit is $\mathbb{D}_0^{\flat} = \mathbb{D}_0^{\#}$.

*Proof.* Note that $\mathbb{D}_0^{\flat} = \mathbb{D}_0^{\#} = (\mathbb{D}_0, \overline{\emptyset})$ as all arrows of $\mathbb{D}_0$ of dimension strictly superior to 0 are identities.

15