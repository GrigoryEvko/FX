CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

Then, this square is cocartesian if and only if for any $$n$$, the induced diagram of sets

$$\begin{array}{c} (B_K)_n \cup \{0\} \xrightarrow{k_n^0} (B_{M_1})_n \cup \{0\} \\ k_n^0 \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (B_{M_0})_n \cup \{0\} \xrightarrow{l_n^0} (B_M)_n \cup \{0\} \end{array}$$

is cocartesian. Furthermore, the induced square in $$(0, \omega)$$-cat

$$\begin{array}{c} \nu K \xrightarrow{\nu k^0} \nu M_1 \\ \nu k^0 \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \nu M_0 \xrightarrow{\nu l^0} \nu M \end{array}$$

is cocartesian.

Proof. This is a combination of theorems 3.1.2 and 3.2.7 of [Lou23].

### 1.2.2 2-Polygraphs and presheaves on $$\Theta_2$$

The objective of this section is to prove the following theorem

**Theorem 1.2.2.1.** Let $$k \le 1$$ be an integer, and let $$C$$ and $$D$$ be two $$(0, 2)$$-categories admitting loop-free and atomic bases (definition 1.2.1.19). Suppose there is a cocartesian square in $$(0, \omega)$$-cat of shape:

$$\begin{array}{c} \partial[[k], 1] \xrightarrow{\partial x} C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [[k], 1] \xrightarrow{x} D \end{array}$$

Then, viewed as a morphism of $$\mathrm{Psh}(\Theta_2)$$, the morphism $$j: C \cup x \to D$$ is in $$\overline{\mathbf{W}_2}$$ which is the smallest precomplete class of morphism (definition 1.1.3.2) containing $$\mathbf{W}_2$$ (definition 1.1.2.15).

Informally, this theorem shows that the square appearing in the previous statement is homotopically cocartesian. This result is therefore a special case of the similar but much more general theorem proved by Campion in [Cam23b].

We fix a $$(0, 2)$$-category $$D$$ admitting a loop free and atomic basis until the end of this section.

**Definition 1.2.2.2.** Let $$v$$ be a 2-cell of $$D$$. The 2-support of $$v$$, denoted $$B_2^v$$, is the support of $$[v]_2$$ (definition 1.2.1.10). The 1-support of $$v$$, denoted $$B_1^v$$, is the union of the support of $$[\pi_1^+ v]_1$$ with $$(\partial_1^- B_2^v) \cup B_2^v$$.

For $$i = 1, 2$$, we define the relation $$<_i^v$$ as the smallest transitive relation on $$B_i^v$$ such that $$c <_i d$$ whenever

$$\langle c \rangle_i^- \wedge \langle d \rangle_i^+ \neq 0.$$

**Remark 1.2.2.3.** Remark that the two inclusions $$(B_0^v, <_0^v) \to (B, \odot)$$ and $$(B_1^v, <_1^v) \to (B, \odot)$$ are strictly increasing. As a consequence, $$<_0^v$$ and $$<_1^v$$ are (partial) orders.

30