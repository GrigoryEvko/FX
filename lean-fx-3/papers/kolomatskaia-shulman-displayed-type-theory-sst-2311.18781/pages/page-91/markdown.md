Example 4.56. Let $\Delta_n$ be the subcategory of the category $\Delta^+$ from section 4.2.1 containing the objects $\langle k \rangle$ with $0 \leqslant k \leqslant n$. Thus $\Delta_n(\langle k \rangle, \langle l \rangle)$ is the set of length $l+1$ binary sequences containing exactly $k+1$ 1s. For fixed $l$ we give these morphisms Campion's ordering, namely the usual ordering of binary numbers. Then $\Delta_n$ is an ordered direct category.

For $x \in I$ we write $\partial_{\mathcal{K}_x}$ for the sub-presheaf of the representable $\mathcal{K}_x$ consisting of nonidentity morphisms, i.e. $\partial_{\mathcal{K}_x}(y) = \{f \in I(y, x) \mid f \neq 1_x\} = \{f \in I(y, x) \mid y \prec x\}$.

If $I$ is a finite direct category and $H$ is a finite presheaf on it, there is a new finite direct category $I \oplus H$, called the **collage** of $H$, which contains $I$ as a full subcategory, together with one new object $*$ such that $I(x, *) = H(x)$ for all $x \in I$. Note that $\partial_{\mathcal{K}_x}$ restricted to $I$ coincides with $H$. Moreover, $I$ and $H$ are ordered if and only if $I \oplus H$ is. Moreover, if $I$ is an ordered direct category of finite height with $x$ its object of greatest rank, then $I \cong (I \setminus \{x\}) \oplus \partial_{\mathcal{K}_x}$. Thus, we can treat this as an induction principle for ordered direct categories.

### 4.5.5.2 Classifying contexts.

As our first use of this sort of induction, we construct for each ordered direct category $I$ a 'classifying context' for Reedy fibrant $I$-presheaves. Specifically, we construct by simultaneous induction:

1. For each ordered direct category I, a context \(\Gamma^1\). This will be the classifying context of Reedy fibrant I-types at level \(\ell\).
2. For each ordered presheaf H on I, a telescope \(\Gamma^1 \vdash_{\mathrm{sm}} \Theta^H \operatorname{tel}_{\ell}\).
3. For each map of ordered presheaves \(\alpha: \mathsf{H} \to \mathsf{H}'\) (not necessarily order-preserving) on I, a partial substitution \(\Gamma^1 \vdash_{\mathrm{sm}} \theta^\alpha: \Theta^{\mathsf{H}'} \to \Theta^{\mathsf{H}}\), varying functorially.
4. For each object \( x \in I \), a type \( \Gamma^1 \mid \Theta^{\partial_{\mathcal{K}_x}} \vdash_{\mathrm{sm}} B^x \text{ type}_\ell \).
5. For each \( h \in H(x) \), inducing by the Yoneda lemma a map \( \beta_h: \partial_{\mathcal{K}_x} \subseteq_{\mathcal{K}_x} \to H \), a term \( \Gamma^1 \mid \Theta^H \vdash_{sm} b^h: B^x[\theta^{\beta_h}] \), such that \( b^h[\theta^\alpha] = b^{\alpha(h)} \) for any \( \alpha: H \to H' \).
6. For each sieve \( J \subseteq I \), a telescope \( \Gamma^J \vdash_{\mathrm{sm}} \Gamma^{J,1} \operatorname{tel}_{\mathrm{isuc} \ell} \) and an isomorphism \( \Gamma^I \cong (\Gamma^J \mid \Gamma^{J,1}) \). Moreover, for all the structure in 2-5, the action of the weakening substitution \( \Gamma^I \cong (\Gamma^J \mid \Gamma^{J,1}) \to \Gamma^J \) corresponds to left Kan extension along the inclusion \( J \hookrightarrow I \).

For 1, we inductively use 2 and set

$$
\begin{array}{l}
\Gamma^\emptyset \equiv () \\
\Gamma^{I \oplus H} \equiv \left( \Gamma^I, A_*: \Theta^H \to \mathsf{Type}_\ell \right).
\end{array}
$$

For 2, we argue inductively on the linear ordering of $H$. If $H$ is empty, we set

$$
\Theta^\emptyset \equiv ().
$$

Otherwise, $H = (H \setminus \{h\}) \cup \{h\}$ where $h \in H(x)$ is the last element in the ordering; the condition on the ordering ensures that $H \setminus \{h\}$ is still an (ordered) presheaf. By the Yoneda lemma, $h$ induces a map $\beta_h: \partial_{\mathcal{K}_x} \subseteq_{\mathcal{K}_x} \to H \setminus \{h\}$, hence by 3 a substitution $\Gamma^I \vdash_{\mathrm{sm}} \theta^{\beta_h}: \Theta^{H \setminus \{h\}} \to \Theta^{\partial_{\mathcal{K}_x}}$. Thus, inductively using 4 as well, we can define

$$
\Theta^H = \left( \Theta^{H \setminus \{h\}}, a_h: B^x[\theta^{\beta_h}] \right).
$$

91