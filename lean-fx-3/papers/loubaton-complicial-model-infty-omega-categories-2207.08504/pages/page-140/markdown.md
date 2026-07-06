CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

Proposition 3.3.2.7. Let \( n \in \mathbb{N} \cup \{\omega\} \). There exist unique invertible natural transformations

\[
\begin{array}{c} \operatorname{Psh} (\Theta_ {n} \times \Delta) \xrightarrow {\pi_ {0}} (\infty , n) \text {-cat} \\ i _ {n} \Big \downarrow \qquad \cong \qquad \uparrow \tau_ {n} ^ {i} \\ \operatorname{tPsh} (\Delta) ^ {n} \xrightarrow [ \mathrm{R} ]{} (0, \omega) \text {-cat} \end{array}
\]

\[
\begin{array}{c} \operatorname{Psh} (\Theta_ {n} \times \Delta) \xrightarrow {\pi_ {0}} (\infty , n) \text {-cat} \\ N _ {i _ {n}} \Big \uparrow \qquad \cong \qquad \uparrow \tau_ {n} ^ {i} \\ \operatorname{tPsh} (\Delta) ^ {n} \xrightarrow [ \mathrm{R} ]{} (0, \omega) \text {-cat} \end{array}
\]

where \(\mathbf{R}\) is the functor defined in 2.2.3.1 and the functor \(\tau_n^i\) is defined in 1.1.1.12.

There exist a unique invertible natural transformation and a weekly unique weekly invertible natural transformation

\[
\begin{array}{c} (\infty , n) \text {-cat} \xrightarrow {N _ {\pi_ {0}}} \operatorname{Psh} (\Theta_ {n} \times \Delta) \\ \Big \downarrow \qquad \cong \qquad \uparrow N _ {i _ {n}} \\ (0, \omega) \text {-cat} \xrightarrow [ N ]{} \operatorname{tPsh} (\Delta) ^ {n} \end{array}
\]

\[
\begin{array}{c} (\infty , n) \text {-cat} \xrightarrow {N _ {\pi_ {0}}} \operatorname{Psh} (\Theta_ {n} \times \Delta) \\ \Big \downarrow \qquad \sim \qquad \Big \downarrow i _ {n} \\ (0, \omega) \text {-cat} \xrightarrow [ N ]{} \operatorname{tPsh} (\Delta) ^ {n} \end{array}
\]

where the functor \(\mathbf{N}\) is defined in 2.2.3.1.

Proof. As \((\infty, n)\)-cat \(\to (0, \omega)\)-cat is fully faithful and as \(\mathrm{tPsh}(\Delta)^n \to \mathrm{tPsh}(\Delta)^\omega\) is homotopically fully faithful, we can restrict to the case \(n = \omega\).

Remark that the two functors

\[
\Theta \times \Delta \xrightarrow {i} \mathrm{tPsh} (\Delta) ^ {\omega} \xrightarrow {\mathrm{R}} (0, \omega) \text {-cat}
\]

\[
\Theta \times \Delta \longrightarrow \operatorname{Psh} (\Theta_ {n} \times \Delta) \xrightarrow {\pi_ {0}} (0, \omega) \text {-cat}
\]

factor through \(\Theta\) as \(\pi_0\) and R sends weak equivalences to isomorphisms, and preserve globes by construction. The theorem 1.2.4.15 then implies that they are both isomorphic to the canonical inclusion \(\Theta \to (\infty, \omega)\)-cat. This implies the existence of the invertible natural transformation appearing in the first square of the first assertion. The unicity follows from the lemma 1.2.4.19 that states that globular sums have no non-trivial automorphisms. As R and \(\pi_0\) sends weak equivalences on isomorphisms, and as \((i, N_i)\) is a Quillen equivalence, this induces the existence and the unicity of the invertible natural transformation appearing in the second square of the first assertion.

Eventually, the second assertion follows by adjunction and from the fact that \((i,N_i)\) is a Quillen equivalence.

140