CHAPTER 2. STUDY OF COMPLICIAL SETS

Remark 2.4.4.6 implies that for one of these objects (resp. a morphism between them) to belong to $C$, it is sufficient to show that it is linked by a zigzag of acyclic cofibrations to the colimit, computed in $\mathrm{mPsh}(\Delta)$, of a diagram with value in $C$ (resp. in the arrow category of $C$).

As $\Sigma[0]_{\circ} = [1]$, the case $(k - 1, k - 1)$ implies that the morphism

$$\Sigma^{m}(\{0\} \star [k - 1]) \to \Sigma^{m}([1] \star [k - 1])$$

is in $C$. Combined with the case $(k - 1, n - 1)$, this implies that the diagram

$$\begin{array}{c} \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \longrightarrow \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \\ \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \uparrow \\ \Sigma^{m}([0] \star [k - 2]) \xrightarrow{id} \Sigma^{m}([0] \star [k - 2]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \Sigma^{m}([0] \star [k - 2]) \longrightarrow \Sigma^{m}([1] \star [k - 2]) \end{array}$$

is in $C$, and so is it's vertical colimits. As the codomain is weakly equivalent to $\Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2])$, this implies that $C$ includes the canonical morphism

$$\Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \hookrightarrow \Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]). \tag{2.4.4.8}$$

We can show similarly that the canonical morphism

$$\Sigma^{m}([1] \star [k - 2]) \hookrightarrow \Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]). \tag{2.4.4.9}$$

is in $C$.

The image by R of the canonical morphism

$$\Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]) \to \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2])$$

induced by the retraction $\Sigma[n - k]_{\circ} \vee [1] \to \Sigma[n - k]_{\circ}$ fulfills the condition of lemma 2.4.4.4 and then belongs to $C$. The lemma 2.4.4.3 then implies that the morphism

$$\Sigma^{m}(\nabla \star [k - 2]) : \Sigma^{m}((\Sigma[n - k]_{\circ}) \star [k - 2]) \to \Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]) \tag{2.4.4.10}$$

is in $C$. We will use freely in the rest of the proof that morphisms (2.4.4.8), (2.4.4.9) and (2.4.4.10) are in $C$.

Theorem 2.3.2.1 implies that the object $\Sigma^{m}(\Sigma[n - k]_{\circ} \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the colimit of

$$\Sigma^{m}((\Sigma[n - k]_{\circ} \vee [1]) \star [k - 2]) \leftarrow \Sigma^{m}(\Sigma[n - k]_{\circ} \star [k - 2]) \to \Sigma^{m}(\Sigma[n - k + 1]_{\circ} \star [k - 2])$$

and the induction hypothesis implies that it belongs to $C$. We proceed similarly to show that $\Sigma^{m}([k - 1]_{\circ} \stackrel{\infty}{\star} \Sigma[n - k])$ belongs to $C$.

Let $0 \leq l \leq k - 1$ and $-1 \leq p \leq n - k$ be two integers, and $f : [l] \to [k - 1]$ and $g : [p] \to [n - k]$ be two monomorphisms. Suppose first that $f$ is of shape $[0] \star f'$ for $f' : [l - 1] \to [k - 2]$. In this case,

96