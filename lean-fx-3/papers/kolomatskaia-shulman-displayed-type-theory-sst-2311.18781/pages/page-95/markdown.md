1. For any co-section $p : I \to J$ of a sieve $i : J \hookrightarrow I$ in an ordered direct category, a partial substitution $\Gamma^J \vdash_{sm} \gamma^p : \Gamma^{J,I}$.
2. In addition, for any order-preserving relative isomorphism $H \to K$ between ordered presheaves, we have $\Theta^H[\gamma^p] \equiv \Theta^K$.
3. For $x \in I$, we have $B^x[\gamma^p] \equiv B^{p(x)}$.
4. For $\alpha : H \to K$ an order-preserving relative isomorphism and $h \in H(x)$, we have $b^x[\gamma^p] \equiv b^{\alpha(x)}$.

To construct 1, note that as before there are two possibilities for a sieve in $I \oplus H$: it can be $J$ or $J \oplus H$ for a sieve $J$ in $I$. In the latter case, we have $\Gamma^{J \oplus H, I \oplus H} = \Gamma^{J,I}$ weakened to $\Gamma^{J \oplus H}$, and a co-section of $J \oplus H \hookrightarrow I \oplus H$ is determined by a co-section $p$ of $J \subseteq I$; thus we can similarly weaken $\gamma^p$.

In the former case, a co-section $I \oplus H \to J$ is determined by a co-section $p : I \to J$ together with an object $x \in J$ and a relative isomorphism $H \to \partial_{\mathcal{K}_x}$. Since $\Gamma^{J, I \oplus H} = (\Gamma^{J,I}, A_x : \Theta^H \to \text{Type}_\ell)$ in this case, to extend $\gamma^p$ as desired it suffices to give a term of type $\Gamma^J \vdash_{sm} \Theta^H[\gamma^p] \to \text{Type}_\ell$. But using 2 inductively, this is equal to $\Gamma^J \vdash_{sm} \Theta^{\partial_{\mathcal{K}_x}} \to \text{Type}_\ell$, so we can use the variable $A_x$ in $\Gamma^J$.

Now to prove 2, we induct on the ordering of $H$ and $K$, inductively using 3. The inductive arguments for 3–4 are similar.

4.5.5.6 Categorical coning. Our last generic construction is a category-theoretic notion of 'coning' a direct category. Let $J \subseteq I$ be a sieve in a direct category that contains the bottom object, which we presciently denote $\langle 0 \rangle$. Let $I^+$ denote the direct category $I$ augmented by an additional morphism $\zeta_x : \langle 0 \rangle \to x$ for all objects $x \in I \setminus J$. We define $f \circ \zeta_x = \zeta_y$ for all $f : x \to y$; note that $x \in I \setminus J$ implies $y \in I \setminus J$ since $J$ is a sieve. If $I$ is ordered, we order $I^+$ by placing $\zeta_x$ before all other morphisms with codomain $x$; this is actually the only possibility given our definition of composition. Note that $J$ is still a sieve in $I^+$.

Similarly, for a presheaf $H$ on $I$, let $H^+$ denote the presheaf on $I^+$ consisting of $H$ augmented by a new element $\zeta_H \in H(\langle 0 \rangle)$, such that $H^+(\zeta_x)(h) = \zeta_H$ for all $h \in H(x)$. If $H$ is ordered, we order $H^+$ by putting $\zeta_H$ first.

We now inductively prove:

1. For any sieve \( J \subseteq I \) in an ordered direct category, we have \( \Gamma^{J,I^+} \equiv (z : B^{\langle 0 \rangle}) \to \Gamma^{J,I} \) (meaning a \( \Pi \)-telescope).
2. In addition, for any \( H \) on \( I \), if we transfer \( \Theta^H \) and \( \Theta^{H^+} \) across the isomorphisms

$$\Gamma^I \cong (\gamma : \Gamma^J \mid \delta : \Gamma^{J,I} \gamma)$$

$$\Gamma^{I^+} \cong (\gamma : \Gamma^J \mid \delta : \Gamma^{J,I^+} \gamma) \equiv (\gamma : \Gamma^J \mid \delta : (z : B^{\langle 0 \rangle} \gamma) \to \Gamma^{J,I} \gamma)$$

to get $\tilde{\Theta}^H$ and $\tilde{\Theta}^{H^+}$, then we have

$$\tilde{\Theta}^{H^+} \gamma \delta \equiv (z : B^{\langle 0 \rangle} \gamma, \tilde{\Theta}^H \gamma (\delta z))$$

Both proofs are entirely straightforward, using the inductive definition of $\Pi$-telescopes as well as $\Gamma^I$ and $\Theta^H$.

The notation is somewhat abusive, since the construction depends on $J$ as well as $I$.

95