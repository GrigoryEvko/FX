From the first axiom in theorem B.15 of $U(\mathcal{C})$, it follows that the above must be $\eta_{\mathcal{C}}(g)\eta_{\mathcal{C}}(f)$ whenever $\mu$ and $\nu$ are successor ordinals. When we have limits, it follows by the universal property.

Now we must verify that it preserves display maps and canonical pullbacks. Both statements are direct consequences of the definitions. Furthermore, the proof from [Car78] works without mayor changes.

For the preservation of pullbacks: We let $f: A_{\lambda} \to B_{\mu+1}$ then

$$
\begin{aligned}
\eta_{\mathcal{C}}(f^*B) &= [\langle x_{\alpha}: \overline{A_{\delta}}(x_{\gamma})_{\gamma<\alpha}, x_{\epsilon}: \overline{f^*B_{\mu+1}}(x_{\alpha})_{\alpha<\lambda} \rangle_{\alpha<\lambda}] \\
&= [\langle x_{\alpha}: \overline{A_{\delta}}(x_{\gamma})_{\gamma<\alpha}, x_{\epsilon}: \overline{B_{\mu+1}}(\overline{p_{\beta}f}(x_{\alpha})_{\alpha<\lambda})_{\beta<\mu} \rangle_{\alpha<\lambda}] \\
&= [\langle \overline{p_{\beta}f}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}]^*[\langle x_{\beta}: \overline{B_{\beta}}(x_{\gamma})_{\gamma<\beta} \rangle_{\beta\le\mu}] \\
&= \eta_{\mathcal{C}}(f)^*\eta_{\mathcal{C}}(B).
\end{aligned}
$$

For a display map of $p_{\nu}: B_{\mu} \to B_{\nu}$ with height a successor ordinal, the same argument shows that the pullback along $f_{\nu}: A_{\lambda} \to B_{\nu}$ is preserved. When the height is a limit ordinal, we combine the previous case and the fact that in any $\kappa$-contextual category canonical pullbacks are unique. $\square$

**Lemma B.34.** *Let $\mathcal{C}, \mathcal{C}'$ be $\kappa$-contextual categories and a contextual functor $F: \mathcal{C} \to \mathcal{C}'$. Then the following diagram is commutative:*

$$
\begin{array}{ccc}
\mathcal{C} & \xrightarrow{\eta_{\mathcal{C}}} & \mathbb{C}_{U(\mathcal{C})} \\
F \downarrow & & \downarrow \mathbb{C}(U(F)) \\
\mathcal{C}' & \xrightarrow{\eta_{\mathcal{C}'}} & \mathbb{C}_{U(\mathcal{C}')}.
\end{array}
$$

*Proof.* If $f: A_{\lambda} \to B_{\mu}$ is a map in $\mathcal{C}$ then

$$
\begin{aligned}
\mathbb{C}(U(F))(\eta_{\mathcal{C}}(f)) &= \mathbb{C}(U(F))([\langle \overline{p_{\beta}f}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}]) \\
&= [\langle \overline{F(p_{\beta}f)}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}] \\
&= [\langle \overline{p_{\beta}F(f)}(x_{\alpha})_{\alpha<\lambda} \rangle_{\beta\le\mu}] \\
&= \eta_{\mathcal{C}'}(Ff).
\end{aligned}
$$

**Corollary B.35.** *There is a natural transformation $Id_{\kappa-CON} \Rightarrow \mathbb{C} \circ U$.*

It remains to show that this natural transformation is an isomorphism. For each $\kappa$-contextual category $\mathcal{C}$ we construct a $\kappa$-contextual functor

$$
\xi_{\mathcal{C}}: \mathbb{C}_{U(\mathcal{C})} \to \mathcal{C}
$$

which is a two-sided inverse to $\eta_{\mathcal{C}}$. From theorem A.13 we see that:

128