#### 4.1.6 Telescopes

We will often have finite towers of types:

\[
\begin{array}{l} \gamma : \Gamma \vdash A \gamma \text { type } _ {\ell_ {0}} \\ \gamma : \Gamma , a: A \vdash B \gamma a t y p e _ {\ell_ {1}} \\ \gamma : \Gamma , a: A, b: B \gamma a b \vdash C \gamma a b t y p e _ {\ell_ {2}} \\ \end{array}
\]

We represent these with a single judgement, defining a telescope:

\[
\gamma : \Gamma \vdash (a: A \gamma , b: B \gamma a, c: C \gamma a b) \gamma t e l _ {\ell}.
\]

Formally speaking, telescopes and their elements (which we call partial substitutions) are another CwF structure on the same category of contexts, which are related to the original one by specified operations. In natural model style, the definition is:

Definition 4.5. A natural model with levels C has telescopes if it is equipped with:

- Another family of (algebraically) representable natural transformations \(\mathrm{tpr}_{\ell}:\mathrm{PSub}_{\ell}\to\) \(\mathrm{Tel}_{\ell}\). This yields two families of judgments for telescopes and partial substitutions:

\[
\gamma : \Gamma \vdash \Upsilon \gamma \operatorname{tel} _ {\ell} \quad \Gamma : \Gamma \vdash \upsilon : \Upsilon
\]

Their representability yields the extension of a context by a telescope:

\[
\frac {\Gamma \text {   ob   } \quad \gamma : \Gamma \vdash \Upsilon \gamma \text {   tel } _ {\ell}}{(\gamma : \Gamma | \nu : \Upsilon \gamma) \text {   ob.   }}
\]

- Morphisms of polynomial functors \(1_{\mathcal{C}} \to P_{\mathrm{tpr}_{\ell}}\), i.e. pullback squares

\[
\begin{array}{c} 1 \longrightarrow \text { PSub } _ {\ell} \\ \Big \downarrow \quad \text {   } \quad \Big \downarrow \text { tpr } _ {\ell} \\ 1 \xrightarrow {\quad (\quad)} \text { Tel } _ {\ell}. \end{array}
\]

This gives 'empty telescopes' \(\gamma : \Gamma \vdash ()\) tel\(_{\ell}\) containing exactly one partial substitution \(\gamma : \Gamma \vdash [] : ()\).

- Morphisms of polynomial functors \( \mathrm{P}_{\mathrm{tpr}_{\ell}} \circ \mathrm{P}_{\mathrm{pr}_{\ell'}} \to \mathrm{P}_{\mathrm{tpr}_{\ell}} \) whenever \( \ell' \leqslant \ell \). This says how to extend a telescope by a type:\( ^8 \)

\[
\frac {\gamma : \Gamma \vdash \Upsilon   \gamma   \text { tel } _ {\ell} \qquad \gamma : \Gamma   |   \upsilon : \Upsilon   \gamma \vdash A   \gamma   \upsilon   \text { type } _ {\ell^ {\prime}} \qquad \ell^ {\prime} \leqslant \ell}{\gamma : \Gamma \vdash (\upsilon : \Upsilon   \gamma ,   a : A   \gamma   \upsilon)   \text { tel } _ {\ell_ {0} \sqcup \ell}}
\]

such that the partial substitutions in  \( (\upsilon:\Upsilon\gamma,\;a:A\gamma\nu) \)  are exactly pairs of a partial substitution in  \( \Upsilon \)  and a term in A, just as for  \( \Sigma \) -types. Thus we get the rules from section 2.3.2.

\( ^{8} \) Note that  \( P_{tpr} \circ P_{pr} \)  is the polynomial functor associated to a map whose codomain is  \( P_{tpr}(Ty) \) , which is the presheaf of types in a context extended by a telescope.

46