1.2. GRAY OPERATIONS

Remark 1.2.2.4. The theorem 1.2.1.23 implies that $B_1^v$ is also equal to the union of the support of $[\pi_1^- v]_1$ with $(\partial_1^+ B_2^v) \cup B_2^v$.

Lemma 1.2.2.5. Let $v$ be a 2-cell of $D$, and $b, b'$ be two elements of $B_1^v$. The assertion $b <_0^v b'$ holds if and only if there exists a well-defined 0-composite

$$b *_0 \dots *_0 b'.$$

Proof. Straightforward.

Definition 1.2.2.6. Given a finite set $E$ endowed with a strict order $<$, an ordering of $E$ is a bijective sequence $(x_i)_{i \le n}$ of elements of $E$ such that for every $i < j$, $\neg(x_j < x_i)$.

Theorem 1.2.2.7. Let $v$ be a 2-cell of $D$, and $(w_i)_{i \le n}$ an ordering of $B_2^v$. There exists a decomposition of $v$ as

$$v := v_0 *_1 \dots *_1 v_n$$

such that for every $i < n$, $v_i$ is a 0-composition of an element of $w_i$ with several 1-generators of $D$.

Moreover, for any decomposition of $v$ as

$$v := v'_0 *_1 \dots *_1 v'_n$$

such that $v'_i$ is a 0-composition of a unique element $w'_i$ of $B_2^v$ with several 1-generators of $D$, then the sequence $\{w_i\}_{i \le n}$ is an ordering of $B_2^v$.

Proof. The first assertion is a consequence of [Lou23, theorem 2.47].

To show the second assertion, suppose given such a decomposition. We will proceed by contradiction and then suppose that there exist $i < j$ such that $w'_j < w'_i$. We can suppose without loss of generality that $i = 0$ and $j = n$.

By a direct induction on $n$ using [Lou23, lemma 2.43], we have

$$\partial_1^+([v'_0]_2) \le \partial_1^+([v'_0 *_1 \dots *_1 v'_n]_2) = \partial_1^+([v]_2)$$

$$\partial_1^-([v'_n]_2) \le \partial_1^-([v'_0 *_1 \dots *_1 v'_n]_2) = \partial_1^-([v]_2)$$

Moreover, the inequality $w'_n < w'_0$ implies

$$\partial_1^+([v'_0]_2) \wedge \partial_1^-([v'_n]_2) \neq 0$$

and then

$$\partial_1^+([v]_2) \wedge \partial_1^-([v]_2) \neq 0$$

which is absurd as $\partial_1^+([v]_2)$ and $\partial_1^-([v]_2)$ are respectively defined as the positive part and the negative part of $\partial([v]_2)$.

Lemma 1.2.2.8. Let $D$ be a $(0, 2)$-category and $f : C \to D$ be a morphism. Let $v$ be a 2-cell of $C$ and $b, b'$ two elements in the 1-support of $v$.

(1) $b <_0^v b'$ implies that for all $c \in B_1^{f(b)}$ and $c' \in B_1^{f(b')}$, $c <_0^{f(v)} c'$.
(2) $b <_1^v b'$ implies that for all $c \in B_2^{f(b)}$ and $c' \in B_2^{f(b')}$, $\neg(c' <_1^{f(v)} c)$.

31