2.4. GLOBULAR EQUIVALENCES

$\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m((\Sigma[p]_\circ \lor [1]) \star [l - 1]) \longrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \uparrow \\ \Sigma^m(\Sigma[p]_\circ \star [l - 1]) \longrightarrow \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \Sigma^m(\Sigma[p + 1]_\circ \star [l - 1]) \longrightarrow \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. Suppose now that $f$ avoids the initial object of $[k - 1]$. In this case, the morphism $\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m(\Sigma[p]_\circ \star [l]) \longrightarrow \Sigma^m((\Sigma[n - k]_\circ) \star [k - 2]) \hookrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^m([l]_\circ \stackrel{co}{\star} \Sigma[p]) \to \Sigma^m([k - 1]_\circ \stackrel{co}{\star} \Sigma[n - k])$$

belongs to $C$.

The morphism $\Sigma^m(\{0\} \star [k - 1]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\{0\} \star [k - 1]) \cong \Sigma^m((\Sigma\{n - k + 1\}) \star [k - 2]) \longrightarrow \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. The morphism $\Sigma^m(\{1\} \star [k - 1]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m(\{1\} \star [k - 1]) \cong \Sigma^m([1] \star [k - 2]) \hookrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that for any $\epsilon \in \{0, 1\}$,

$$\Sigma^m([k - 1]_\circ \stackrel{co}{\star} \{\epsilon\}) \to \Sigma^m([k - 1]_\circ \stackrel{co}{\star} \Sigma[n - k])$$

97