1.2. GRAY OPERATIONS

Proof. As $K$ is a colimit of representables indexed by the Reedy cofibrant diagram $\Delta_{/K} \to \mathrm{Psh}(\Delta)$ (definition 1.1.3.1), and as $1 \coprod_{-\otimes\{0\}} - \otimes [1] \coprod_{-\otimes\{1\}} 1$ and $[\_, 1]$ preserve cofibrations, it is sufficient to demonstrate the result when $K := [n]$ for $n$ an integer. As $[\_, 1]$ and, by lemma 1.2.5.13, $\_ \otimes [1]$ send $\mathrm{Sp}_{[n]} \to [n]$ to $\overline{\mathrm{W}_2}$, it is sufficient to demonstrate the result when $[n] = [1]$. By proposition 1.2.5.4, the morphism

$$1 \coprod_{[1] \otimes\{0\}} [1] \otimes [1] \coprod_{[1] \otimes\{1\}} 1 \to [[1], 1]$$

fits in the cocartesian square

$$\begin{array}{ccc} [0] \coprod_{[1]} [2] & \coprod & [0] \coprod_{[1]} [2] \longrightarrow 1 \coprod_{[1] \otimes\{0\}} [1] \otimes [1] \coprod_{[1] \otimes\{1\}} 1 \\ & \downarrow & \downarrow \\ [1] & \coprod & [1] \xrightarrow{\quad} [[1], 1] \end{array}$$

As the canonical morphisms $[0] \coprod_{[1]} [2] \to [1]$ and $[2] \coprod_{[1]} \to [1]$ are in $\overline{\mathrm{W}_2}$, this concludes the proof. $\square$

Lemma 1.2.5.15. Let $n$ be an integer. The two morphisms

$$E^{eq} \otimes [n] \to [n] \quad \text{and} \quad [n] \otimes E^{eq} \to [n]$$

are in $\overline{\mathrm{W}_2}$.

Proof. As $\otimes$ sends spine inclusions to $\overline{\mathrm{W}_2}$, we can reduce to the case where $n = 1$. By stability by pushouts along monomorphisms, and using lemma 1.2.5.14, the composite

$$E^{eq} \otimes [1] \to 1 \coprod_{E^{eq} \otimes\{0\}} E^{eq} \otimes [1] \coprod_{E^{eq} \otimes\{1\}} 1 \to [E^{eq}, 1]$$

is in $\overline{\mathrm{W}_2}$. As $[E^{eq}, 1] \to [1]$ is in $\mathrm{W}_2$, this concludes the first assertion. We show the second one similarly. $\square$

proof of theorem 1.2.5.3. This is the content of lemmas 1.2.5.13 and 1.2.5.15. $\square$

We will also need the same analysis for the op-cone.

Construction 1.2.5.16. We define $1 \star \_ : \mathrm{Psh}(\Theta) \to \mathrm{Psh}(\Theta)$ as the left Kan extension of the functor

$$\Theta \xrightarrow{1 \star} (0, \omega)\text{-cat} \xrightarrow{\iota} \mathrm{Psh}(\Theta).$$

Proposition 1.2.5.17. The $\Theta$-set $1 \star [1]$ is the colimit, computed in $\mathrm{Psh}(\Theta)$, of the diagram

$$[[1], 1] \xleftarrow{[d^0, 1]} [1] \xrightarrow{d^1} [2]$$

Proof. We denote by $P$ the colimit of this diagram. Remark that $\mathbf{F}P$ is the $(0, \omega)$-category

$$\begin{array}{c} 1 \star \emptyset \\ \downarrow \\ \emptyset \star \{0\} \longrightarrow \emptyset \star \{1\} \end{array}$$

57