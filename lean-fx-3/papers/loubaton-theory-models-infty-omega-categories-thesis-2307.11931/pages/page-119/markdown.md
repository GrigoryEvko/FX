2.4. GLOBULAR EQUIVALENCES

colimit of the diagram

$$\begin{array}{c} \Sigma^{m}(\{1\} \star [k-1]) \cong \Sigma^{m}([1] \star [k-2]) \longmapsto \Sigma^{m}((\Sigma[n-k]_{\circ} \vee [1]) \star [k-2]) \\ \uparrow \\ \Sigma^{m}(\Sigma[n-k]_{\circ} \star [k-2]) \\ \downarrow \\ \Sigma^{m}(\Sigma[n-k+1]_{\circ} \star [k-2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that for any $\epsilon \in \{0, 1\}$,

$$\Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \{\epsilon\}) \to \Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \Sigma[n-k])$$

belongs to $C$.

Eventually, the morphism $\Sigma^{m}(\emptyset \star [k-1]) \to \Sigma^{m}(\Sigma[n-k]_{\circ} \star [k-1])$ is is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^{m}(\{1\} \star [k-2]) \longrightarrow \Sigma^{m}([1] \star [k-2]) \longmapsto \Sigma^{m}((\Sigma[n-k]_{\circ} \vee [1]) \star [k-2]) \\ \uparrow \\ \Sigma^{m}(\Sigma[n-k]_{\circ} \star [k-2]) \\ \downarrow \\ \Sigma^{m}(\Sigma[n-k+1]_{\circ} \star [k-2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \emptyset) \to \Sigma^{m}([k-1]_{\circ} \stackrel{co}{\star} \Sigma[n-k])$$

belongs to $C$.

We have then proven the case $(k, n)$, and this concludes the proof.

**Lemma 2.4.4.12.** Let $F : \Delta \to (0, \omega)$-cat be a functor and $\phi : F \to \mathbb{R}$ be a invertible transformation such that for any monomorphism $i : [k] \to [n]$, the induced square

$$\begin{array}{c} F([k]) \xrightarrow{\phi_{[k]}} \mathbb{R}([k]) \\ F(i) \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow R(i) \\ F([n]) \xrightarrow{\phi_{[n]}} \mathbb{R}([n]) \end{array}$$

commutes. Then $\phi$ is an invertible natural transformation between $F$ and $\mathbb{R}$.

Proof. We can suppose without loss of generality that for all integer $n$, $F([n]) = \mathbb{R}([n])$. The hypotheses implies that for any monomorphism $i : [n] \to [m]$, $F(i) = \mathbb{R}(i)$ and it then remains to show that for any degeneracy $p : [n] \to [m]$, $F(p) = \mathbb{R}(p)$.

109