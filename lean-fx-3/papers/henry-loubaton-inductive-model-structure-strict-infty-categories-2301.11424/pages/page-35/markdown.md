$n$-category whose $k$-(arrows for $k < n$ are those of $C$ and its $n$-arrows are equivalence classes for this relation. We will use in particular that given two parallel $(n-2)$-arrows $u, v$ in $C$ we have a category $h_n C(u, v)$ whose objects are $(n-1)$-arrows $u \rightarrow v$ and whose morphisms are equivalence classes of $n$-arrows between them.

**3.37 Lemma.** *For an $m$-marked $\infty$-category $C$, the following conditions are equivalent:*

(1) *An arrow in $C$ is marked if and only if it has an inverse in the sense of Definition 3.17.*
(2) *$C$ is fibrant in the inductive left semi-model structure $\infty$-$\mathbf{Cat}_{Ind}^{+m}$ of Theorem 2.43 and satisfies the 2-out-of-6 property.*

*Proof.* We first consider $C$ an $m$-marked $\infty$-category which satisfies (1), and we check it fulfills the conditions of Definition 3.18. By Proposition 3.25, this will imply that $C$ is fibrant. The first condition of Definition 3.18 is immediate; we check the second condition. Let $b$ and $c: a \rightarrow b$ be two marked arrows. By assumption, $b$ is invertible, and there exists then an arrow $b^{-1}$ and two marked arrows $c: b^{-1}\#_n b \rightarrow \mathbb{I}$ and $v: b\#_n b^{-1} \rightarrow \mathbb{I}$. We then have marked arrows:

$$b^{-1}\#_n a \stackrel{b^{-1}\#_n c}{\rightarrow} b^{-1}\#_n b \stackrel{c}{\rightarrow} \mathbb{I}$$

$$a\#_n b^{-1} \stackrel{c\#_n b^{-1}}{\rightarrow} b\#_n b^{-1} \stackrel{c}{\rightarrow} \mathbb{I}$$

This shows that $b^{-1}$ is also an inverse for $a$, and hence if all arrows with an inverse are marked, $a$ is marked as well. Note that if it is $a$ which is marked in the first place, then one can consider an inverse $c^{-1}: b \rightarrow a$ and apply the same argument.

Next, we show that $C$ satisfies 2-out-of-6. For this, we can rely on Remark 3.36. An $n$-arrow has an inverse in the sense of Definition 3.17 if and only if it is an isomorphism in the category $h_n C(u, v)$ where $u$ and $v$ are its $(n-2)$-dimensional source and target. Our assumption is then that an $n$-arrow is marked if and only if its equivalence class is invertible in the category $h_n C(u, v)$. The fact that marked arrows satisfy 2-out-of-6 then follows from the fact that isomorphisms in a category satisfy the 2-out-of-6 condition.

Conversely, assuming that $C$ satisfies condition (2), we have that marked arrows have inverses because $C$ is fibrant and Proposition 3.25. If an arrow $a$ has an inverse $a^{-1}$, then both $a\#_{n-1} a^{-1}$ and $a^{-1}\#_{n-1} a$ are marked because they are equivalent to identities, and it follows from the 2-out-of-6 condition that $a$ (and $a^{-1}$) is marked. $\square$

**3.38 Theorem.** *The inductive semi-model structure $\infty$-$\mathbf{Cat}_{Ind}^{+m}$ of Theorem 2.43 admits a Bousfield localization (as a left semi-model structure) in which the fibrant objects are the marked $\infty$-categories that satisfy the equivalent conditions of Lemma 3.37.*

*We call this left semi-model structure the saturated inductive left semi-model structure and denote it by $\infty$-$\mathbf{Cat}_{Sat-Ind}^{+m}$.*

As a Bousfield localization, this left semi-model structure has the same cofibrations and the same fibrations between fibrant objects as the left semi-model structure from Theorem 2.43.

35