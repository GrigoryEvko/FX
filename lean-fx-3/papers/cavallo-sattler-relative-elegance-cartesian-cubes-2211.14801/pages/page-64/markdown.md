64

E. Cavallo and C. Sattler

It is straightforward to check that $\deg(gf) = \deg(g)\deg(f)$ for $\mathfrak{C}_m \xrightarrow{f} \mathfrak{C}_n \xrightarrow{g} \mathfrak{C}_p$, as we expect from a winding number. Because $\mathfrak{C}_m$ is "too short" to wrap around $\mathfrak{C}_n$ when $m < n$, we have the following:

Lemma A.10 If $m < n$, then $\deg(f) = 0$ for any $f: \mathfrak{C}_m \to \mathfrak{C}_n$.

Proof By induction, $|\dot{f}(i) - \dot{f}(0)| \leq i$ for every $i \in \mathbb{N}$, so $|\dot{f}(2m) - \dot{f}(0)| < 2n$.

Definition A.11 For $n \geq 3$, define an poset embedding $c_n: \mathfrak{C}_n \mapsto [1]^n$ by

$$c_n(i)_j = \begin{cases} 1 & \text{if } \lfloor \frac{i}{2} \rfloor \leq j \leq \lceil \frac{i}{2} \rceil \\ 0 & \text{otherwise} \end{cases}$$

Definition A.12 Given $m, n \geq 3$ and a monotone map $f: \mathfrak{C}_m \to \mathfrak{C}_n$, define an extension

$$\begin{array}{c} \mathfrak{C}_m \xrightarrow{f} \mathfrak{C}_n \\ c_m \searrow \quad \searrow c_n \\ [1]^m - \overline{f} \to [1]^n \end{array}$$

by setting

$$\overline{f}(v) := \begin{cases} c_n(f(i)) & \text{if } v = c_m(i), \\ \bot & \text{if } v = \bot, \\ \top & \text{otherwise.} \end{cases}$$

The mapping $f \mapsto \overline{f}$ is the functorial action of a semifunctor from the category of crown posets to $\square_{\mathcal{N}}$: compositions are preserved, but not identities.

Lemma A.13 The diagram in Definition A.12 is a pullback.

Proof The three cases in the definition of $\overline{f}$ have disjoint values.

Theorem A.14 There exists no Reedy category $\mathbf{R}$ with a fully faithful functor $i: \square_{\mathcal{N}} \to \mathbf{R}$ such that $\mathbf{R}$ is elegant relative to $i$.

Proof Suppose for sake of contradiction that we have some $i: \square_{\mathcal{N}} \to \mathbf{R}$ such that $\mathbf{R}$ is elegant relative to $i$. Choose any $n \geq 3$. For every $m \geq 2$ and $a \geq 1$, the identity function on $\mathfrak{F}$ induces a map $f_a: \mathfrak{C}_{am} \to \mathfrak{C}_m$ with winding number $a$. We then have the following diagram in Pos:

$$\begin{array}{c} \dots \xrightarrow{f_2} \mathfrak{C}_{8n} \xrightarrow{f_2} \mathfrak{C}_{4n} \xrightarrow{f_2} \mathfrak{C}_{2n} \\ \downarrow f_8 \quad \downarrow f_4 \quad \downarrow f_2 \\ \dots \xrightarrow{\text{id}} \mathfrak{C}_n \xrightarrow{\text{id}} \mathfrak{C}_n \xrightarrow{\text{id}} \mathfrak{C}_n. \end{array}$$

2025/10/16 00:43