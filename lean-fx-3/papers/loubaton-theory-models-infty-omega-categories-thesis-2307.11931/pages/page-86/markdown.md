CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

a marked simplicial set. Moreover, the proposition 2.1.2.9 implies that the canonical morphism $X \to \iota(X)_{\mathrm{mk}}$ is an entire acyclic cofibration.

Given a functor $i: I \mapsto (F(i), tF(i))$ with value in marked simplicial sets, its colimit is given by $(\operatorname{colim} F(i), \overline{M})$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \operatorname{colim} F(i)$ for any $i: I$.

**Proposition 2.2.1.9.** *The category $\mathrm{mPsh}(\Delta)$ admits a nice model structure that makes the adjunction 2.2.1.8 a Quillen equivalence.*

*Proof.* This is a direct consequence of proposition 2.1.2.10 and theorem 2.2.1.6.

**2.2.1.10.** Let $n$ be an integer, and $(X, tX)$ a marked simplicial set. We define $\tau_n^i(tX)$ as the reunion of $tX$ and all simplices of dimension strictly superior to $n$. This induces a functor, called the *intelligent $n$-truncation*:

$$\begin{array}{rcl} \tau_n^i: & \mathrm{mPsh}(\Delta) & \mapsto \mathrm{mPsh}(\Delta) \\ & (X, tX) & \mapsto (X, \overline{\tau_n^i(tX)}). \end{array}$$

This functor preserves cofibrations. Given the explicit description of colimits in marked simplicial sets, it is easy to see that $\tau_n^i$ preserves colimits. For every elementary anodyne extension $i: K \to L$, we have a pushout

$$\begin{array}{ccc} K & \longrightarrow & L \\ \downarrow & & \downarrow \\ \tau_n^i(K) & \longrightarrow & \tau_n^i(L). \end{array}$$

The intelligent $n$-truncation is then a left Quillen functor.

It's associated right adjoint is called the *$n$-truncation* and is denoted by

$$\tau_n: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta).$$

### 2.2.2 Gray tensor product

**Construction 2.2.2.1** ([Ver08c, Notation 5]). For any $n, p, q \ge 0$ such that $n = p + q$, we define:

- the *degeneration partition operator*:

$$\begin{array}{rcl} \Pi_{p,q}^1: & [n] & \to & [p] \\ & k & \mapsto & k \quad \text{if } k \le p \\ & k & \mapsto & p \quad \text{if } k > p \end{array} \qquad \qquad \begin{array}{rcl} \Pi_{p,q}^2: & [n] & \to & [q] \\ & k & \mapsto & 0 \quad \text{if } k \le p \\ & k & \mapsto & k - p \quad \text{if } k > p. \end{array}$$

76