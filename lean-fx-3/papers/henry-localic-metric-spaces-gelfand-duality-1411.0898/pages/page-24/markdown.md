Therefore,

$$v \times v' \subseteq (v \vee v') \times (v \vee v') \subseteq \Delta_{q'},$$

and this concludes the proof.

☐

3.1.6. Definition : Let $X$ be a pre-metric locale, we will say that $X$ has a continuous distance if the pre-distance function $d : X \times X \to \overleftarrow{\mathbb{R}_+^\infty}$ internally corresponds to a continuous real number, i.e. if the pre-distance function factors into $X \times X \to \overline{\mathbb{R}_+^\infty} \to \overleftarrow{\mathbb{R}_+^\infty}$. In this situation we define $\Theta_q$ to be the open sublocale of $X \times X$ corresponding to $\{(x, y) | d(x, y) > q\}$.

3.1.7. Assuming the law of excluded middle, we indeed obtain continuity:

Proposition : Assuming the law of excluded middle in the base topos, any pre-metric locale has a continuous distance.

Proof :

If one assumes the law of excluded middle in the base topos then any fiberwise closed sublocale is in fact a closed sublocale. In particular, there exists open sublocales $\Theta'_q$ of $X \times X$, which are the complementary open sublocales of the (closed) sublocales $\overline{\Delta_q}$. From the fact, proved in 3.1.5 that for any $q < q'$ one has the relation

$$\Delta_q \leqslant \overline{\Delta_q} \leqslant \Delta_{q'}$$

and we deduce

$$\Delta_q \wedge \Theta'_q = \emptyset$$

$$\Delta_{q'} \vee \Theta'_q = X \times X$$

and $\overline{\Delta_q} \leqslant \overline{\Delta_{q'}}$ gives $\Theta'_q \geqslant \Theta'_{q'}$.

If we define, $\Theta_q = \bigvee_{q < q'} \Theta'_{q'}$, then $\Delta_q$ and $\Theta_q$ define a map from $X \times X$ to $\overline{\mathbb{R}_+^\infty}$ which yields the desired factorisation. ☐

24