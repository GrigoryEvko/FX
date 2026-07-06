CHAPTER 2. STUDY OF COMPLICIAL SETS

belongs to $C$.

Eventually, the morphism $\Sigma^m(\emptyset \star [k - 1]) \to \Sigma^m(\Sigma[n - k]_\circ \star [k - 1])$ is linked by a zigzag of acyclic cofibrations to the vertical colimit of the diagram

$$\begin{array}{c} \Sigma^m(\{1\} \star [k - 2]) \longrightarrow \Sigma^m([1] \star [k - 2]) \hookrightarrow \Sigma^m((\Sigma[n - k]_\circ \lor [1]) \star [k - 2]) \\ \uparrow \\ \Sigma^m(\Sigma[n - k]_\circ \star [k - 2]) \\ \downarrow \\ \Sigma^m(\Sigma[n - k + 1]_\circ \star [k - 2]) \end{array}$$

and the induction hypothesis implies that it belongs to $C$. We prove similarly that

$$\Sigma^m([k - 1]_\circ \stackrel{cp}{\star} \emptyset) \to \Sigma^m([k - 1]_\circ \stackrel{cp}{\star} \Sigma[n - k])$$

belongs to $C$.

We have then proven the case $(k, n)$, and this concludes the proof.

Lemma 2.4.4.11. Let $F : \Delta \to (0, \omega)$-cat be a functor and $\phi : F \to \mathbb{R}$ be a invertible transformation such that for any monomorphism $i : [k] \to [n]$, the induced square

$$\begin{array}{c} F([k]) \xrightarrow{\phi_{[k]}} \mathbb{R}([k]) \\ F(i) \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F([n]) \xrightarrow{\phi_{[n]}} \mathbb{R}([n]) \end{array}$$

commutes. Then $\phi$ is an invertible natural transformation between $F$ and $\mathbb{R}$.

Proof. We can suppose without loss of generality that for all integer $n$, $F([n]) = \mathbb{R}([n])$. The hypotheses implies that for any monomorphism $i : [n] \to [m]$, $F(i) = \mathbb{R}(i)$ and it then remains to show that for any degeneracy $p : [n] \to [m]$, $F(p) = \mathbb{R}(p)$.

We proceed by induction and we then suppose that for any $0 < k \le n$ and any degeneracy $s : [k] \to [k - 1]$, $F(s) = \mathbb{R}(s)$. As any morphism of $\Delta$ factors as a degeneracy followed by a monomorphism, the induction hypothesis implies that for any $f : [k] \to [n]$ with $k \le n$, $F(f) = \mathbb{R}(f)$.

Let $s : [n + 1] \to [n]$ be a degeneracy. We have a a priori non commutative diagram:

$$\begin{array}{c} \operatorname{colim}_{[k] \xrightarrow{\varphi_{id}} [n+1]} \mathbb{R}([k]) \xlongequal{\text{colim}}_{[k] \xrightarrow{\varphi_{id}} [n+1]} \mathbb{R}([k]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{R}([n+1]) \xlongequal{\text{ }} \mathbb{R}([n+1]) \\ F(s) \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbb{R}([n]) \xlongequal{\text{ }} \mathbb{R}([n]) \end{array}$$

The induction hypothesis implies that the outer and the upper square commute. As $R$ commutes with colimits, $\operatorname{colim}_{[k] \to \partial[n]} \mathbb{R}([k])$ is equivalent to $\mathbb{R}(\partial[n])$. Moreover, the inclusion $\mathbb{R}(\partial[n]) \to \mathbb{R}([n])$ induces an isomorphisms on cells of dimension lower or equal to $n$. For the lower square to commutes, we then only have to check that the top cell of $\mathbb{R}([n+1])$ is sent on the same element on $\mathbb{R}([n])$. That is the case because the two paths send it to an unity as there is no non trivial $(n+1)$-cells in $\mathbb{R}([n])$.

We then have $F(s) = \mathbb{R}(s)$, which concludes the induction and then the proof.

98