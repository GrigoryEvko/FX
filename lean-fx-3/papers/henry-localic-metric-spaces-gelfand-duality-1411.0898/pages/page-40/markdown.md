Hence from 3.3.7 there is a map $\tilde{f}: Y \to \tilde{X}$ such that $\tilde{f}^*(U^\sim) = \tau^*(U) = \bigvee_{V \triangleleft U} i_* f^* V^\sim$. It remains to be proved that $\tilde{f}$ is indeed an extension of $f$, i.e. that $\tilde{f} \circ i = f$.

$$i^* \tilde{f}^*(U^\sim) = \bigvee_{V \triangleleft U} i^* i_* f^*(V^\sim) \leqslant \bigvee_{V \triangleleft U} f^*(V^\sim) = f^*(U^\sim)$$

Because $\bigvee_{V \triangleleft U} V^\sim = U^\sim$ by (CF4). One the other hand, from the non-metric part of 3.2.2

$$i^* \tilde{f}^*(U^\sim) = \bigvee_{V \triangleleft U} i^* i_* f^*(V^\sim) \geqslant \bigvee_{\substack{V \triangleleft U \\ V' \triangleleft f^*(V^\sim)}} V'.$$

As $f^*$ is uniform it is compatible with $\triangleleft$, hence the set of $V'$ appearing in the last union contains all the $f^*(W^\sim)$ for $W \triangleleft V$ hence

$$i^* \tilde{f}^*(U^\sim) \geqslant \bigvee_{\substack{V \triangleleft U \\ W \triangleleft V}} f^*(W^\sim) = f^*(U^\sim),$$

which proves $i^* \tilde{f}^*(U^\sim) = f^*(U^\sim)$ and concludes the proof. $\square$

We also note that if the map $f$ is metric (resp. isometric), the extension $\tilde{f}$ will also be metric (resp. isometric) by an application of 3.2.4.

3.3.12. **Theorem**: Let $X$ be a pre-metric locale, then the following conditions are equivalent:

1. The map \( X \to \tilde{X} \) is an isomorphism;
2. \(X\simeq \tilde{Y}\) for some \(Y\)
3. For any \( S \to Y \) a strongly dense isometric map between pre-metric locales, and any map from \( S \) to \( X \) there exists a map from \( Y \) to \( X \) making the triangle commute;
4. Any strongly dense isometric map from \( X \) to a metric locale \( Y \) is an isomorphism.

A locale satisfying these conditions is called a complete metric locale.

**Proof**:

1. \(\Rightarrow 2\) is clear.
2. \(\Rightarrow 3\) is a direct consequence of 3.3.11.
4. \(\Rightarrow 1\) is also clear because the map from \(X\) to \(\tilde{X}\) is a dense isometric map.
3. \(\Rightarrow 4\) remains to be proved. Let \(f:X\to Y\) be a strongly dense isometric map. The identity map from \(X\) to \(X\) can be extended into a map \(g\) from \(Y\) to \(X\) by 3., such that \(g\circ f = Id_X\). As, \(f\circ g\) restricted to \(X\) is the inclusion from \(X\) to \(Y\), \(f\circ g\) is the identity of \(Y\) by fiberwise density of \(X\) into \(Y\) and fiberwise separation of \(Y\) (3.2.3) hence \(g\) is an inverse for \(f\), and they are isomorphisms.

40