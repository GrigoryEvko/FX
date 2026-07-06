CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

and such that $\tau_0^i[e,1]_t = [e,1]_t$. As the intelligent $k$-truncations on $A$ are left Quillen, the intelligent $k$-truncations on $\mathrm{tSeg}(A)$ preserve generating Reedy cofibrations and Segal extensions. It is straightforward that they also send $[e,1]_t \to [0]$ and $E^{\cong} \to (E^{\cong})'$ to weak equivalences. According to theorem 3.1.2.10, they are left Quillen functors.

3.3.1.7. The (inverted) composition $g, f \mapsto g \circ f$ is a monoidal structure on the category of endomorphisms of $\mathrm{tSeg}(A)$. Lemmas 3.3.1.4 and 3.3.1.5 show that $e \star \_ \$ is a monoid for this monoidal structure. This induces a cosimplicial object:

$$
\begin{array}{l}
\Delta \to \operatorname{End}(\mathrm{tSeg}(A)) \\
[n] \mapsto [n] \star \_ := \underbrace{e \star e \star \ldots \star e}_{n+1} \star \_
\end{array}
$$

We extend this functor to $\Delta_t$ in setting for a stratified Segal $A$-precategory $C$ and an integer $n > 0$:

$$
\begin{array}{ccc}
\coprod_{k \ge -1} & \coprod_{D, \tau_k^i(D)=D} & \coprod_{D \to C} [n] \star D & \longrightarrow & [n] \star C \\
& \downarrow & & \downarrow \\
\coprod_{k \ge -1} & \coprod_{D, \tau_k^i(D)=D} & \coprod_{D \to C} \tau_{n+k}^i([n] \star D) & \longrightarrow & [n]_t \star C
\end{array}
$$

where $\tau_{-1}^i$ is the constant functor with value $\emptyset$. Evaluated on the empty Segal $A$-category, and by extension under colimits, this gives a functor

$$
\mathrm{tPsh}(\Delta) \to \mathrm{tSeg}(A). \tag{3.3.1.8}
$$

The image of $[n]$ (resp. $[n]_t$) is also noted by $[n]$ (resp. $[n]_t$).

By construction, for $K, L$ two stratified sets and $D$ a stratified Segal $A$-precategory, we have $K \star (L \star C) \cong (K \star L) \star C$.

Lemma 3.3.1.9. Let $K$ be a stratified simplicial set. The morphism $K \star \_ \$$ is a left Quillen functor. Moreover, if $i$ is a cofibration of stratified simplicial sets and $g$ an acyclic cofibration of stratified Segal $A$-precategories, the morphism $i \star g$ is an acyclic cofibration.

Proof. As every simplicial set is a homotopy colimit of representables and as $\star$ preserves monomorphisms, it is enough to show the first assertion for $K = [n]$. In this case, this is a repeated application of the corollary 3.2.4.11. By diagram chasing and the use of two out of three, this implies the second assertion. □

142