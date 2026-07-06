J. Ceulemans, A. Nuyts and D. Devriese

5

WSMTT-EQ-SUB-KEY-NATURAL

\[
\frac {\Lambda , \Theta : \text {LockTele} (m \to n) \qquad \alpha \in \text {locks} (\Lambda) \Rightarrow \text {locks} (\Theta) \qquad \vdash_ {\text {ws}} \sigma \text {sub} (\hat {\Gamma} \to \hat {\Delta}) @ m}{\vdash_ {\text {ws}} \mathbf {Q} _ {\hat {\Delta}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \circ (\sigma . \Theta) \equiv^ {\nu} (\sigma . \Lambda) \circ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \text {sub} (\hat {\Gamma} . \Theta \to \hat {\Delta} . \Lambda) @ n}
\]

WSMTT-EQ-SUB-KEY-UNIT

\[
\frac {\hat {\Gamma} \operatorname{sctx} @ m \quad \Lambda : \operatorname{LockTele} (m \to n)}{\vdash_ {\mathrm{ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {1 _ {\text {locks} (\Lambda)} \in \Lambda \Rightarrow \Lambda} \equiv^ {\nu} \operatorname{id} \operatorname{sub} (\hat {\Gamma} . \Lambda \to \hat {\Gamma} . \Lambda) @ n}
\]

WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL

\[
\begin{array}{c c} \hat {\Gamma} \text {sctx} @ m & \alpha \in \text {locks} (\Lambda) \Rightarrow \text {locks} (\Theta) \\ \Lambda , \Theta , \Psi : \text {LockTele} (m \to n) & \beta \in \text {locks} (\Theta) \Rightarrow \text {locks} (\Psi) \\ \hline \vdash_ {\text {ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \circ \alpha \in \Lambda \Rightarrow \Psi} \equiv^ {\nu} \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Lambda \Rightarrow \Theta} \circ \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Theta \Rightarrow \Psi} \text {sub} (\hat {\Gamma}. \Psi \to \hat {\Gamma}. \Lambda) @ n \end{array}
\]

WSMTT-EQ-SUB-KEY-COMPOSE-HORIZONTAL

\[
\hat {\Gamma} \operatorname{sctx} @ m \qquad \begin{array}{l l} \Theta_ {1}, \Theta_ {2}: \operatorname{LockTele} (n \to o) & \alpha \in \operatorname{locks} (\Theta_ {1}) \Rightarrow \operatorname{locks} (\Theta_ {2}) \\ \Lambda_ {1}, \Lambda_ {2}: \operatorname{LockTele} (m \to n) & \beta \in \operatorname{locks} (\Lambda_ {1}) \Rightarrow \operatorname{locks} (\Lambda_ {2}) \end{array}
\]

\[
\vdash_ {\mathrm{ws}} \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \star \alpha \in \Lambda_ {1} \cdot \Theta_ {1} \Rightarrow \Lambda_ {2} \cdot \Theta_ {2}} \equiv^ {\nu} (\mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Lambda_ {1} \Rightarrow \Lambda_ {2}} \cdot \Theta_ {1}) \circ \mathbf {Q} _ {\hat {\Gamma} \cdot \Lambda_ {2}} ^ {\alpha \in \Theta_ {1} \Rightarrow \Theta_ {2}} \operatorname{sub} (\hat {\Gamma} \cdot \Lambda_ {2} \cdot \Theta_ {2} \to \hat {\Gamma} \cdot \Lambda_ {1} \cdot \Theta_ {1}) @ o
\]

Figure 4 Definition of \(\sigma\)-equivalence for WSMTT expressions and substitutions (continued).

provides us with a pseudofunctor SSyn from  \( M^{coop} \)  to Cat that maps every mode m to the corresponding category  \( SCtx_{m} \)  of scoping contexts and substitutions:

A modality \(\mu : m \to n\) must then be sent to a functor \(\widehat{\mathbf{Q}}_{\mu} : \mathrm{SCtx}_n \to \mathrm{SCtx}_m\), whose object part (action on scoping contexts) is defined in Figure 1 (sCTX-LOCK), and whose morphism part (action on substitutions) is defined in Figure 2 (WSMTT-SUB-LOCK). We add rules expressing the functor laws for this functor: WSMTT-EQ-SUB-LOCK-ID expresses that \(\widehat{\mathbf{Q}}_{\mu}\) preserves the identity substitution and WSMTT-EQ-SUB-LOCK-COMPOSE expresses that it preserves composition of substitutions.
A 2-cell \(\alpha \in \mu \Rightarrow \nu\) must be sent to a natural transformation \(\mathbf{Q}_{\mathbf{x}}^{\alpha}:\mathbf{Q}_{\nu}\to \mathbf{Q}_{\mu}\) whose object part (action on scoping contexts) is defined in Figure 2 (WSMTT-SUB-KEY). We add a rule WSMTT-EQ-SUB-KEY-NATURAL expressing the naturality condition. However, we immediately express naturality not only for key substitutions between locks, but more generally for key substitutions between lock telescopes.
We add rules expressing that SSyn's action on Hom-categories is strictly functorial, i.e. that identity (WSMTT-EQ-SUB-KEY-UNIT) and composition (WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL) of 2-cells are preserved.
SSyn needs to respect identity up to isomorphism, i.e. \(\widehat{\mathbf{Q}}_{\mathbf{1}}\) needs to be naturally isomorphic to the identity functor. An invertible substitution \(\hat{\Gamma}.\widehat{\mathbf{Q}}_{\mathbf{1}} \cong \hat{\Gamma}\) is given by \(\mathbf{Q}_{\hat{\Gamma}}^{1_{1} \in \cdot \Rightarrow \widehat{\mathbf{Q}}_{\mathbf{1}}}\), and naturality follows from the existing naturality rule.
SSyn needs to respect composition up to isomorphism, i.e. the diagram

\[
\begin{array}{c} \operatorname{Hom} _ {\mathcal {M}} (n, o) \times \operatorname{Hom} _ {\mathcal {M}} (m, n) \xrightarrow {- 0 -} \operatorname{Hom} _ {\mathcal {M}} (m, o) \\ \Biggl \downarrow (\widehat {\mathbf {Q}} _ {r _ {2} (-)}, \widehat {\mathbf {Q}} _ {r _ {1} (-)}) \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad [ \mathrm{SCtx} _ {n}, \mathrm{SCtx} _ {m} ] \times [ \mathrm{SCtx} _ {o}, \mathrm{SCtx} _ {n} ] \xrightarrow {- 0 -} [ \mathrm{SCtx} _ {o}, \mathrm{SCtx} _ {m} ] \end{array}
\]

must commute up to natural isomorphism. For any composable pair of modalities \(\mu : m \to n\) and \(\nu : n \to o\), an invertible substitution \(\hat{\Gamma} \cdot \widehat{\mathbf{Q}}_{\circ \circ \mu} \cong \hat{\Gamma} \cdot \widehat{\mathbf{Q}}_{\nu} \cdot \widehat{\mathbf{Q}}_{\mu}\) is given by \(\mathbf{Q}_{\hat{\Gamma}}^{1_{1 \circ \mu} \in \widehat{\mathbf{Q}}_{\nu} \cdot \widehat{\mathbf{Q}}_{\mu} \Rightarrow \widehat{\mathbf{Q}}_{\circ \circ \mu}\) and naturality with respect to \(\hat{\Gamma}\) follows from the existing naturality