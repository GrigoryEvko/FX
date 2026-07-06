**Definition 4.51.** An object $Y \in E$ is a **generalised F-coalgebra** if it is equipped with:

- For any $X \in \mathcal{C}$ and morphism $h: Y \to X$, a specified morphism $\overline{h}: Y \to FX$, such that
- $\epsilon_X \circ \overline{h} = h$.
- For any $g: X \to Z$ in $\mathcal{C}$, we have $Fg \circ \overline{h} = \overline{g \circ h}$.

In more abstract language, we can say that $F$ induces a copointed endofunctor $F^*$ of the functor category $\mathsf{Set}^{\mathcal{C}}$ by precomposition, and $Y$ is a generalised F-coalgebra if the functor $E(Y, -): \mathcal{C} \to \mathsf{Set}$ is an $F^*$-coalgebra. The following observation is then a consequence of the Yoneda lemma, but we write it out explicitly.

**Lemma 4.52.** If $Y \in \mathcal{C}$, then generalised F-coalgebra structures on $Y$ are bijective to ordinary F-coalgebra structures.

*Proof.* In one direction, if $y: Y \to FY$ is an F-coalgebra structure, then given $h: Y \to X$ define $\overline{h} = Fh \circ y$. Then we have

$$\epsilon_X \circ \overline{h} = \epsilon_X \circ Fh \circ y = h \circ \epsilon_Y \circ y = h$$

and

$$Fg \circ \overline{h} = Fg \circ Fh \circ y = F(g \circ h) \circ y = \overline{g \circ h}.$$

In the other direction, given a generalised F-coalgebra structure, let $y = \overline{1_Y}: Y \to FY$. Then $\epsilon_Y \circ y = 1_Y$ by assumption, so $y$ is an F-coalgebra structure. Moreover, the other axiom implies that for any $g: Y \to Z$ we have $\overline{g} = \overline{g \circ 1_Y} = Fg \circ \overline{1_Y} = Fg \circ y$. Thus one round-trip composite is the identity. The other round-trip composite simply sends $y: Y \to FY$ to $\overline{1_Y} = F(1_Y) \circ y = 1_{FY} \circ y = y$.

Of course, a **morphism of generalised F-coalgebras** is a morphism $f: Y \to Z$ such that for any $h: Z \to X \in \mathcal{C}$ we have $\overline{h} \circ f = \overline{h \circ f}$.

**Lemma 4.53.** If $Y \in E$ is a generalised F-coalgebra and $x: X \to FX$ is an F-coalgebra in $\mathcal{C}$, then a morphism $f: Y \to X$ is a generalised F-coalgebra morphism if and only if $\overline{f} = x \circ f$.

*Proof.* If it is a generalised F-coalgebra map, then taking $h = 1_X$ in $\overline{h} \circ f = \overline{h \circ f}$ we get $x \circ f = \overline{f}$. On the other hand, if $x \circ f = \overline{f}$ then for any $h: X \to X'$ in $\mathcal{C}$ we have $\overline{h} \circ f = x' \circ h \circ f = Fh \circ x \circ f = Fh \circ \overline{f} = \overline{h \circ f}$, as desired.

**Theorem 4.54.** *Let $\mathcal{C}$ and $F$ be as in theorem 4.45, and let $\mathcal{C}$ be a full subcategory of $E$ such that the embedding preserves the terminal object and the inverse limits of $\omega$-sequences of fibrations. Then the terminal F-coalgebra constructed in theorem 4.45 is also a terminal generalised F-coalgebra.*

*Proof.* Indeed, the proof of terminality in theorem 4.45 really only uses the generalised F-coalgebra structure, which we can see clearly by repeating it in that language. Let $Y \in E$ be a generalised F-coalgebra. We construct inductively maps $h_n: Y \to X_n$ such that $x_{n+1} \circ h_{n+1} = \overline{h_n}$ and $g_{n+1} \circ h_{n+1} = h_n$. We start with $h_0: Y \to X_0 = \mathbb{1}$ the unique

88