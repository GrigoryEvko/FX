18

Eliminating reversals from cubical type theories

The effect of this functor, which we exploit in §6, is to show that \( F \) and \( G \) are approximately "the same". Note that we need to know very little about \( F \) and \( G \) to obtain \( S_G^F \): this reflects that the constructs of \( \mathbb{C}\mathrm{TT}[\iota \Phi] \) are all characterized up to equivalence by their universal properties, so an interpretation has little choice in where to send them. It is key here that we are looking at second-order models, i.e., RMC functors; we would not have the same result for morphisms of first-order models.

For \(\Theta \in \mathbb{C}\mathrm{TT}\), we write the span \(S_G^F\Theta\) as \(F\Theta \stackrel{d_0}{\leftrightarrow} M_G^F\Theta \stackrel{d_1}{\rightarrow} G\Theta\). Because we intend \(S_G^F\) to be a morphism in the coslice under \(\mathbb{MLTT}_{\Sigma,\mathrm{Id}}\), the interpretations of the constructs of \(\mathbb{MLTT}_{\Sigma,\mathrm{Id}}\) are determined by the definition of Refl from the previous section.

From this point until the summary statement Theorem 62, we omit the annotations on \(\mathrm{S}_G^F\) and \(\mathrm{M}_G^F\) and simply write S and M.

▶ Component 50 (S, sorts). Set STy := {Ty \( \stackrel{d^{0}}{\leftarrow} \) Ty \( \stackrel{d^{1}}{\rightarrow} \) Ty} and STm := {Tm \( \stackrel{d^{0}}{\leftarrow} \) Tm \( \stackrel{d^{1}}{\rightarrow} \) Tm} as required by the definition of Refl. For the remaining sorts:

1. Set \(\mathrm{S}\mathbb{I}:=\{F\mathbb{I}\stackrel{d^{0}}{\leftarrow}F\mathbb{I}\times G\mathbb{I}\stackrel{d^{1}}{\rightarrow}G\mathbb{I}\}\).
2. Set MCof := (P P' \(\overline{\mathbb{P}}\): Cof, [\(\overline{\mathbb{P}}\to\mathbb{P},\overline{\mathbb{P}}\to\mathbb{P}'\)]) with \(d_{\mathrm{Cof}}^{0}, d_{\mathrm{Cof}}^{1}\) projecting P and P' respectively.
3. Set MTrue := ((P, P', \(\overline{\mathbb{P}}\)): MCof, \(\overline{\mathbb{P}}\)) with \(d_{\text{True}}^{0}, d_{\text{True}}^{1}\) applying the implications \(\overline{\mathbb{P}} \to \mathbb{P}\) and \(\overline{\mathbb{P}} \to \mathbb{P}'\), and define \(\mathrm{M}\pi_{\text{True}}\) to be the evident projection.

▶ Component 51 (S, interval theory). By definition of SⅡ, the interpretation of the interval theory is forced by F and G. Unfolding, the interpretation Mf of each operation  \( f: I^{n} \to I \)  of the interval theory is  \( (F\mathbb{I} \times G\mathbb{I})^{n} \cong F\mathbb{I}^{n} \times G\mathbb{I}^{n} \stackrel{Ff \times Gf}{\longrightarrow} F\mathbb{I} \times G\mathbb{I} \) .

▶ Component 52 (S, cofibration theory). We interpret the cofibration operations as follows.

\[
\begin{array}{l} (\mathrm{i}, \mathrm{x}) \approx_ {\mathrm{M}} (\mathrm{j}, \mathrm{y}) := (\mathrm{i} \approx_ {F} \mathrm{j}, \mathrm{x} \approx_ {G} \mathrm{y}, (\mathrm{i} \approx_ {F} \mathrm{j}) \cap (\mathrm{x} \approx_ {G} \mathrm{y})) \\ \mathrm{M} \top := (F \top , G \top , \top) \\ (\mathrm{P}, \mathrm{P} ^ {\prime}, \overline {{\mathrm{P}}}) \cap_ {\mathrm{M}} (\mathrm{Q}, \mathrm{Q} ^ {\prime}, \overline {{\mathrm{Q}}}) := (\mathrm{P} \cap_ {F} \mathrm{Q}, \mathrm{P} ^ {\prime} \cap_ {G} \mathrm{Q} ^ {\prime}, \overline {{\mathrm{P}}} \cap \overline {{\mathrm{Q}}}) \\ \mathrm{M} \bot := (F \bot , G \bot , \bot) \\ (\mathrm{P}, \mathrm{P} ^ {\prime}, \overline {{\mathrm{P}}}) \cup_ {\mathrm{M}} (\mathrm{Q}, \mathrm{Q} ^ {\prime}, \overline {{\mathrm{Q}}}) := (\mathrm{P} \cup_ {F} \mathrm{Q}, \mathrm{P} ^ {\prime} \cup_ {G} \mathrm{Q} ^ {\prime}, \overline {{\mathrm{P}}} \cup \overline {{\mathrm{Q}}}) \\ \end{array}
\]

The axioms for cofibrations ensure that these definitions preserve the implicit requirement that for  \( (\mathsf{P},\mathsf{P}^{\prime},\overline{\mathsf{P}}) \) : MCof we have  \( \overline{P}\to P \)  and  \( \overline{P}\to P^{\prime} \) . We use this to interpret the  \( elim_{\cup}^{Ty} \)  and  \( elim_{\cup}^{Tm} \)  eliminators. For  \( elim_{\cup}^{Ty} \) , for example, we are given  \( (\mathsf{P},\mathsf{P}^{\prime},\overline{\mathsf{P}}) \) : MCof,  \( (\mathsf{Q},\mathsf{Q}^{\prime},\overline{\mathsf{Q}}) \) : MCof, compatible A: [P] → Ty and B: [Q] → Ty, compatible A': [P'] → Ty and B': [Q'] → Ty, and compatible 1-to-1 correspondences  \( \overline{\mathsf{A}} \) : ([P], A, A') → Ty and  \( \overline{\mathsf{B}} \) : ([Q], B, B') → Ty, and we need to extend these to a 1-to-1 correspondence between  \( Felim_{\cup}^{Ty}(P,Q,A,B) \)  and  \( Gelim_{\cup}^{Ty}(P^{\prime},Q^{\prime},A^{\prime},B^{\prime}) \)  assuming  \( \overline{P}\cup\overline{Q} \) . To do so we case on  \( \overline{P}\cup\overline{Q} \)  and use that we either have both P and P' or both Q and Q' as a consequence.

▶ Component 53 (S, filling). To define Sfill, we are given inputs

|  A | : \( F\mathbb{I} \to \text{Ty} \) | \( (j, y) \) | : \( \text{M}\mathbb{I} \)  |
| --- | --- | --- | --- |
|  \( A' \) | : \( G\mathbb{I} \to \text{Ty} \) | \( a_0 \) | : \( A(j) \)  |
|  \( \overline{A} \) | : \( (i : F\mathbb{I}, x : G\mathbb{I}, a : A(i), a' : A'(x)) \to \text{Ty} \) | \( a'_0 \) | : \( A'(y) \)  |
|  \( (P, P', \overline{P}) \) | : \( \text{MCof} \) | \( \overline{a}_0 \) | : \( \overline{A}(j, y, a_0, a'_0) \)  |
|  \( a \) | : \( (i : F\mathbb{I}, P) \to A(i) \) | \( (k, z) \) | : \( \text{M}\mathbb{I} \)  |
|  \( a' \) | : \( (x : G\mathbb{I}, P') \to A'(x) \) |  |   |
|  \( \overline{a} \) | : \( (i : F\mathbb{I}, x : G\mathbb{I}, \overline{P}) \to \overline{A}(i, x, a(i), a'(x)) \) |  |   |