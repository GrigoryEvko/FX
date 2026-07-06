CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

(1) $\Sigma^m(\Sigma[n-k]_\circ \star [k-1])$ and $\Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$ are in $C$.
(2) For any $-1 \le l \le k-1$ and $0 \le p \le n-k$, and any monomorphisms $[l] \to [k-1]$ and $[p] \to [n-k]$, the morphisms

$$\Sigma^m(\Sigma[p]_\circ \star [l]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([l]_\circ \overset{co}{\star} \Sigma[p]) \to \Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$$

are in $C$.

(3) For any $\epsilon \in \{0, 1\}$, the morphisms

$$\Sigma^m(\{\epsilon\} \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([k-1]_\circ \overset{co}{\star} \{\epsilon\}) \to \Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$$

are in $C$.

(4) If $k > 0$, the morphisms

$$\Sigma^m(\emptyset \star [k-1]) \to \Sigma^m(\Sigma[n-k]_\circ \star [k-1]) \quad \text{and} \quad \Sigma^m([k-1]_\circ \overset{co}{\star} \emptyset) \to \Sigma^m([k-1]_\circ \overset{co}{\star} \Sigma[n-k])$$

are in $C$.

Proof. We will proceed by induction on $(k, n)$.

- The case $(0, 0)$ corresponds to the belonging of globes to $C$, which is true by the assumptions we made on the functor $i$ and by the proposition 1.2.3.11 that assert that the globes have no non-trivial automorphisms.
- We now suppose that the case $(n-1, n-1)$ holds and we are willing to show the case $(0, n)$. The assertions (1) and (2) are direct consequences of the case $(n-1, n-1)$ after remarking the isomorphisms:

$$\Sigma^m \Sigma[n] \cong \Sigma^{m+1}((\Sigma[0]_\circ) \star [n-2]) \qquad \Sigma^m \Sigma[n]_\circ \cong \Sigma^{m+1}([n-2]_\circ \overset{co}{\star} (\Sigma[0]))$$

It remains to show the third assertion. Let $m$ be any integer and $\epsilon \in \{0, 1\}$. By induction hypothesis and by the belonging of globes to $C$, the following morphism

$$\Sigma^m(\{\epsilon\}) \to \Sigma^m(\Sigma\{0\}) \cong \Sigma^{m+1}\{0\} \to \Sigma^{m+1}((\Sigma[0]_\circ) \star [n-2]) \cong \Sigma^m \Sigma[n]$$

is in $C$. As the morphism $\Sigma^m(\{\epsilon\}) \to \Sigma^m \Sigma[n]$ is their composite, it belongs to $C$. We proceed similarly to show that $\Sigma^m(\{\epsilon\}) \to \Sigma^m \Sigma[n]_\circ$ belongs to $C$. This concludes the proof of the case $(0, n)$.

- Suppose the result true for the couples $(k-1, n)$, $(k-1, n-1)$ and $(k-1, k-1)$ for an integer $k$ strictly superior to 0 and inferior or equal to $n$. We are willing to show the case $(k, n)$. Let $m$ be any integer.

As $R$ commutes with Gray operations and pushouts, the lemma 1.2.3.10 implies that $\Sigma^m((\Sigma[n-k]_\circ \coprod_{[0]}[1]) \star [k-2])$ together with all the objects appearing in the statement

106