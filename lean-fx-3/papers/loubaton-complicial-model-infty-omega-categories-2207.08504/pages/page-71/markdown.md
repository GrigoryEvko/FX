2.2. THE COMPLICIAL MODEL

The set $S$ is then closed under the Leibniz product $\_ \star (\partial[n] \to [n])$. We can show similarly that $S$ is closed under the Leibniz product $(\partial[n] \to [n]) \star \_$.

As for any pair of integers $0 < i < n$, $\Lambda^i[n] \to [n]$ is the Leibniz product

$$(\partial[i - 1] \to [i - 1]) \star (\mathrm{Sp}_2 \to [2]) \star (\partial[n - i - 1] \to [n - i - 1])$$

this morphism belongs to $S$, which concludes the proof.

The functor $F((\_)^\flat)$ then preserves inner anodyne extensions and sends $E^{eq} \to 1$ to a weak equivalence. It is then a left Quillen functor when $\mathrm{Psh}(\Delta)$ is endowed with the Joyal model structure. As we have a cocartesian square

$$\begin{array}{c} E^{eq} \longrightarrow (E^{eq})^\sharp \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \longrightarrow 1 \end{array}$$

the functor $F$ sends $(E^{eq})^\sharp \to 1$ to a weak equivalence, and by two out of three, also $[1]_t \to (E^{eq})^\sharp$. Combined with [RV22, proposition D.4.8], the right adjoint of $F$ preserves fibrations between fibrant objects, and $F$ is then a left adjoint according to corollary A.2 of [Dug01].

**Definition 2.2.1.11.** A *marked simplicial set* is a stratified simplicial set that has the right lifting property against entire acyclic cofibrations. In particular, all complicial sets are marked. The category of marked simplicial sets is denoted by $\mathrm{mPsh}(\Delta)$. There is an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow[\leftarrow]{\perp} \mathrm{mPsh}(\Delta) : \iota \tag{2.2.1.12}$$

The left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified simplicial set $(X, tX)$ to the marked simplicial set $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$ a marked simplicial set. Moreover, the proposition 2.1.2.11 implies that the canonical morphism $X \to \iota(X)_{\mathrm{mk}}$ is an entire acyclic cofibration.

**Remark 2.2.1.13.** Given a functor $i : I \mapsto (F(i), tF(i))$ with value in marked simplicial sets, its colimit is given by $(\operatorname{colim} F(i), \overline{M})$ where $M$ is the smaller stratification that includes the image of $tF(i) \to \operatorname{colim} F(i)$ for any $i : I$.

**Proposition 2.2.1.14.** *The category $\mathrm{mPsh}(\Delta)$ admits a nice model structure that makes the adjunction 2.2.1.12 a Quillen equivalence.*

*Proof.* This is a direct consequence of proposition 2.1.2.12 and theorem 2.2.1.8.

**Construction 2.2.1.15.** Let $n$ be an integer, and $(X, tX)$ a marked simplicial set. We define $\tau_n^i(tX)$ as the reunion of $tX$ and all simplices of dimension strictly superior to $n$. This induces a functor, called the *intelligent $n$-truncation*:

$$\begin{array}{rcl} \tau_n^i : & \mathrm{mPsh}(\Delta) & \mapsto & \mathrm{mPsh}(\Delta) \\ & (X, tX) & \mapsto & (X, \overline{\tau_n^i(tX)}) \end{array}$$

This functor preserves cofibrations. Given the explicit description of colimits in marked simplicial sets, it is easy to see that $\tau_n^i$ preserves colimits. For every elementary anodyne extension $i : K \to L$, we have a pushout

$$\begin{array}{c} K \longrightarrow L \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \tau_n^i(K) \longrightarrow \tau_n^i(L). \end{array}$$

71