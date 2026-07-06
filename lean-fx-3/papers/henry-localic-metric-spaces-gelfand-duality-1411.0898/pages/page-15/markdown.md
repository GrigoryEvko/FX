2.6.1. **Definition :** *An open sublocale of the form given in (1) will be called a basic sublocale. A basic sublocale will be said to be admissible if it satisfies the following condition:*

$$\forall i \in 1, \dots, n, j \in 1, \dots, m, (u_i \leq v_j) \Rightarrow (\neg U_i) \vee (\neg V_j) = X.$$

We will show in 2.6.5 that a basic open is admissible if and only if it is positive, hence the property of being admissible is indeed a property of the open sublocale $B$, and not of its representation. But, while we have not proven this, we will assume that each time we consider a basic open $B$, it is given with a representation in the form of (1) and say that it is admissible if and only if its representation is.

2.6.2. The following lemma is in some sense a constructive form of Urysohn's lemma, asserting that compact regular locales are in fact completely regular.

**Lemma :** *Let $X$ be a compact regular locale, and let $U, V$ be two open sublocales of $X$ such that $U \ll V$. Then there exists a positive locally positive locale $\mathcal{L}$, such that in the logic of $\mathcal{L}$ there exists a continuous function from $X$ to $[0, 1]^6$ such that $f$ restricted to $U$ is zero and $f$ is constant equal to one on $\neg V$.*

# **Proof :**

The classical proof of the Urysohn lemma for locale (see for example [17, Chap. XIV]) goes as follows: In a compact regular locale the relation $U \prec V$ is equivalent to the relation $U \ll V$. The relation $\prec$ in general does not interpolate, but in a locally compact locale the relation $\ll$ always does, ie if $a \ll b$ then there exists $c$ such that $a \ll c \ll b$. In particular in a compact regular space the relation $\prec$ interpolates and (using the axiom of choice) one can construct a $\mathbb{Q}$-indexed family of open subspaces $U_q$ such that $U_0 = U$, $U_1 = V$ and if $q < q'$ then $U_q \prec V_{q'}$, and we define $U_q = \emptyset$ when $q < 0$ and $U_q = X$ when $q > 1$. This defines a 'scale' (see [17] XIV.5.2) which in turns defines a function from $X$ to $[0, 1]$ with the required property (see [17]XIV.5.2.2).

The only part of the previous proof which is not constructive is the application of the axiom of dependent choice to construct the sequence $U_q$. By applying 2.3.8 one can construct a locale $\mathcal{L}$ in which there exists such a sequence and then finish the proof in the logic of $\mathcal{L}$ by constructing the function we are looking for. The only thing we need to check is that if $x \prec y$ then their pull-back to $\mathcal{L}$ also satisfy this identity, but as it can equivalently be defined by ' $\exists c$ such that $x \wedge c = \emptyset$ and $c \vee y = \top$ ' this is immediate.

□

$^{6}$That is externally a function from $\mathcal{L} \times X$ to $[0, 1]$.

15