J. Ceulemans, A. Nuyts and D. Devriese

29

## 5.2 Embedding and Renaming/Substitution

The core property for proving the soundness theorem is Proposition 34, which states that $\mathsf{embed}(t[\sigma]_{\mathsf{sub}}) \equiv^{\sigma} \mathsf{embed}(t)[\mathsf{embed}(\sigma)]_{\mathsf{ws}}$ for every $t$ and $\sigma$. In order to prove such a result, we will adopt a similar technique as in Section 4.1 for proving observational equivalence of SFMTT substitutions. First we show that it is sufficient to prove the result for variables after adding an arbitrary scoping telescope $\Phi$ to $\sigma$ (Lemma 28). Then we prove that actually the scoping telescope $\Phi$ only needs to be a lock telescope (Lemmas 29 and 31).

$\triangleright$ **Lemma 28.** *Let $\vdash_{\mathsf{sf}} \sigma \operatorname{aren} / \operatorname{asub}(\hat{\Gamma} \to \hat{\Delta}) @ m$ be an atomic SFMTT rensub and assume that $\hat{\Gamma} \cdot \Phi \vdash_{\mathsf{ws}} \mathsf{embed}\left(v[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \equiv^{\sigma} \mathsf{embed}(v)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \operatorname{expr} @ n$ for any scoping telescope $\Phi : \mathsf{sTele}(m \to n)$ and variable $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} v \operatorname{var} @ n$. Then we have that $\hat{\Gamma} \vdash_{\mathsf{ws}} \mathsf{embed}\left(t[\sigma]_{\operatorname{aren} / \operatorname{asub}}\right) \equiv^{\sigma} \mathsf{embed}(t)[\mathsf{embed}(\sigma)]_{\mathsf{ws}} \operatorname{expr} @ m$ for all expressions $\hat{\Delta} \vdash_{\mathsf{sf}} t \operatorname{expr} @ m$.*

**Proof.** We will prove the more general result that $\hat{\Gamma} \cdot \Phi \vdash_{\mathsf{ws}} \mathsf{embed}\left(t[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \equiv^{\sigma} \mathsf{embed}(t)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \operatorname{expr} @ n$ for all scoping telescopes $\Phi : \mathsf{sTele}(m \to n)$ and expressions $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} t \operatorname{expr} @ n$. This proof proceeds by induction on $t$. We only show the cases for variables, lambda abstraction and the modal term constructor. The other cases can be proved similarly.

$\triangleright$ CASE $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} v \operatorname{expr} @ n$ (SF-EXPR-VAR)
The result is exactly what we assumed in the lemma.

$\triangleright$ CASE $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} \lambda^{\mu}(t) \operatorname{expr} @ n$ (SF-EXPR-LAM)
We have that

$$
\begin{array}{l}
\mathsf{embed}\left(\left(\lambda^{\mu}(t)\right)[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \\
= \mathsf{embed}\left(\lambda^{\mu}\left(t\left[(\sigma \cdot \Phi)^{+}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Equation (9))} \\
= \lambda^{\mu}\left(\mathsf{embed}\left(t\left[(\sigma \cdot \Phi)^{+}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\equiv^{\sigma} \lambda^{\mu}\left(\mathsf{embed}(t)\left[\mathsf{embed}\left((\sigma \cdot \Phi)^{+}\right)\right]_{\mathsf{ws}}\right) \quad \text{(Induction hypothesis)} \\
\equiv^{\sigma} \lambda^{\mu}\left(\mathsf{embed}(t)\left[\left(\mathsf{embed}(\sigma \cdot \Phi)\right)^{+}\right]_{\mathsf{ws}}\right) \quad \text{(Lemma 27)} \\
\equiv^{\sigma}\left(\lambda^{\mu}(\mathsf{embed}(t))\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \quad \text{(WSMTT-EQ-EXPR-LAM-SUB)} \\
= \mathsf{embed}\left(\lambda^{\mu}(t)\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}}. \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\end{array}
$$

Note that we can indeed apply the induction hypothesis where it is indicated since $(\sigma \cdot \Phi)^{+} = \sigma \cdot (\Phi \cdot \mu)$.

$\triangleright$ CASE $\hat{\Delta} \cdot \Phi \vdash_{\mathsf{sf}} \mathsf{mod}_{\mu}(t) \operatorname{expr} @ n$ (SF-EXPR-MOD-TM)

Now we can compute that

$$
\begin{array}{l}
\mathsf{embed}\left(\left(\mathsf{mod}_{\mu}(t)\right)[\sigma \cdot \Phi]_{\operatorname{aren} / \operatorname{asub}}\right) \\
= \mathsf{embed}\left(\mathsf{mod}_{\mu}\left(t\left[(\sigma \cdot \Phi) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Equation (12))} \\
= \mathsf{mod}_{\mu}\left(\mathsf{embed}\left(t\left[(\sigma \cdot \Phi) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right]_{\operatorname{aren} / \operatorname{asub}}\right)\right) \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\equiv^{\sigma} \mathsf{mod}_{\mu}\left(\mathsf{embed}(t)\left[\mathsf{embed}\left((\sigma \cdot \Phi) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right)\right]_{\mathsf{ws}}\right) \quad \text{(Induction hypothesis)} \\
= \mathsf{mod}_{\mu}\left(\mathsf{embed}(t)\left[\left(\mathsf{embed}(\sigma \cdot \Phi)\right) \cdot \widehat{\mathbf{\Theta}}_{\mu}\right]_{\mathsf{ws}}\right) \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\equiv^{\sigma}\left(\mathsf{mod}_{\mu}\left(\mathsf{embed}(t)\right)\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}}. \quad \text{(WSMTT-EQ-EXPR-MOD-TM-SUB)} \\
= \mathsf{embed}\left(\mathsf{mod}_{\mu}(t)\right)[\mathsf{embed}(\sigma \cdot \Phi)]_{\mathsf{ws}} \quad \text{(Definition of } \mathsf{embed}(\_)) \\
\end{array}
$$