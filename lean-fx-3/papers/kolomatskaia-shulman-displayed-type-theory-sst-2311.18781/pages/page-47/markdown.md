- The rules \((\Gamma \mid (\cdot)_{\mathbb{P}}) \equiv \Gamma\) and \((\Gamma \mid (\Theta, x: A)) \equiv ((\Gamma \mid \Theta), x: A)\) from section 2.3.1 hold. Note that these are equalities of objects of \(\mathcal{C}\), and in particular only make sense if \(\mathbb{P}\) and \(\mathbb{P}\) are algebraically representable.
- A morphism of polynomial functors \(\mathrm{P_{tpr}_{i_0}}\circ \mathrm{P_{tpr}_{i_1}}\to \mathrm{P_{tpr}_{i_0 + i_1}}\), giving the extension of telescopes by telescopes \((\upsilon :\Upsilon |\phi :\Phi \upsilon)\) from section 2.5.2, such that the rules from that section hold:

$$
(\Gamma \mid (\Upsilon \mid \Phi)) \equiv ((\Gamma \mid \Upsilon) \mid \Phi) \qquad (\Upsilon \mid ()) \equiv \Upsilon \qquad (\Upsilon \mid (\Phi, x: A)) \equiv ((\Upsilon \mid \Phi), x: A)
$$

Syntactically, this definition represents the rules from sections 2.3.1, 2.3.2 and 2.5.2, in the non-modal case. Because it is phrased in terms of presheaves and operations on them, it implicitly includes substitution into telescopes that commute with the other operations. Some of these commutation properties refer to weakening-two, which can be characterised in terms of them as well, for instance:

$$
\frac{\gamma : \Gamma \vdash \Upsilon \gamma \operatorname{tel}_{\ell} \qquad \sigma : \Delta \to \Gamma}{\delta : \Delta \vdash \Upsilon (\sigma \delta) \operatorname{tel}_{\ell}} \qquad \frac{\sigma : \Delta \to \Gamma \qquad \gamma : \Gamma \vdash \Upsilon \gamma \operatorname{tel}_{\ell}}{W_2^\Upsilon \sigma : (\delta : \Delta, \upsilon : \Upsilon (\sigma \delta)) \to (\gamma : \Gamma, \upsilon : \Upsilon \gamma)}
$$

$$
()^\sigma \equiv () \qquad (\upsilon : \Upsilon \gamma, a: A \gamma \upsilon)^\sigma \delta \equiv (\delta : \Upsilon (\sigma \delta), a: A ((W_2^\Upsilon \sigma) [\delta, \upsilon])) \quad
$$

$$
W_2^{(1)} \sigma \equiv \sigma \qquad W_2^{(\Upsilon, A)} \sigma \equiv W_2^A (W_2^\Upsilon \sigma)
$$

For example, we have:

$$
(a: A \gamma, b: B \gamma a)^\sigma \delta \equiv (a: A (\sigma \delta), b: B (\sigma (\operatorname{pt} [\delta, a])) (\operatorname{zv} [\delta, a]))
$$

When we allow ourselves to use variables in the usual way, justified by the internal type theory of presheaves, we can write this as:

$$
(a: A \gamma, b: B \gamma a)^\sigma \delta \equiv (a: A (\sigma \delta), b: B (\sigma \delta) a)
$$

Note that the meaning of this construction is simply iterating the canonical construction of pullbacks over a tower: