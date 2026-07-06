2

SIMON HENRY AND CHRISTOPHER TOWNSEND

mentioned above. Finally in section 5 we put everything together and prove the main theorem.

## 2. NORMAL DISTRIBUTIVE LATTICES

By a *distributive lattice*, we mean a poset with finite$^{1}$ joins and finite meets which satisfies the distributivity law $a \wedge (b \vee c) = (a \wedge b) \vee (a \wedge c)$, or equivalently the dual distributivity law $a \vee (b \wedge c) = (a \vee b) \wedge (a \vee c)$. Morphisms of distributive lattices are order preserving maps that preserves finite joins and finite meets (i.e. lattice homomorphisms).

In a poset $P$, if $I \subset P$, we write $\downarrow I = \{a \in P | \exists i \in I, a \leqslant i\}$, and $\downarrow a = \downarrow \{a\}$ if $a \in P$. If $f : X \rightarrow Y$ is a function we denote by $\exists_f$ the direct image function from the power set of $X$ to the power set of $Y$.

A subset $I \subseteq D$ of a distributive lattice $D$ is an *ideal* if and only if $a \leqslant b \in I \Rightarrow a \in I$ and $I$ is closed under finite joins. The set of all ideals, written $idl(D)$, is itself a distributive lattice.

**Definition 2.1.** *A distributive lattice $D$ is normal provided for any $a, b \in D$ if $a \vee b = 1$ then there exists $a', b' \in D$ such that*

$$a' \wedge b' = 0 \text{ and } a' \vee b = 1 = a \vee b'.$$

*We denote by **NDL** the full subcategory of distributive lattices defined by this condition.*

As usual, one defines the relation $a \triangleleft b$ by $\exists c$ such that $a \wedge c = 0$ and $b \vee c = 1$. An equivalent way to define normal is then $a \vee b = 1 \Rightarrow \exists a' \triangleleft a$ such that $a' \vee b = 1$. It also follows that the relation $\triangleleft$ is interpolative in a normal distributive lattice: say $a \triangleleft b$, witnessed by $c$, so that $b \vee c = 1$; then there exists $b' \triangleleft b$ and $b' \vee c = 1$ so that $c$ also witnesses $a \triangleleft b'$.

**Example 2.2.** A compact regular frame $\mathcal{O}X$ is normal. Regularity is the assertion that $b = \bigvee \{b' | b' \triangleleft b\}$ for every open $b$. But the join is directed so $a \vee b = 1$ implies there exists $b' \triangleleft b$ with $a \vee b' = 1$ by compactness, which as observed above implies that $\mathcal{O}X$ is normal. Frame homomorphisms are lattice homomorphism so there is a forgetful functor $u : \mathbf{KRegFrm} \rightarrow \mathbf{NDL}$.

We now have a couple of lattice theoretic propositions which show that compact regular frames can be seen as completions of normal distributive lattices.

**Proposition 2.3.** *Let $N$ be a normal distributive lattice. Define*

$$C(N) = \{I \subseteq N | I \text{ an ideal and } \forall a \in I \ \exists b \in I \text{ such that } a \triangleleft b\}.$$

*Then:*

1. $C(N)$ is a distributive lattice.
2. $\Downarrow : N \rightarrow C(N)$, defined by $\Downarrow a = \{b | b \triangleleft a\}$, is a well defined lattice homomorphism.
3. $C(N)$ is a normal distributive lattice.
4. By setting $C(f)(I) = \downarrow \exists_f(I)$ for any lattice homomorphism $f : N \rightarrow M$ we have defined an order enriched functor $C : \mathbf{NDL} \rightarrow \mathbf{NDL}$.

$^{1}$Including nullary