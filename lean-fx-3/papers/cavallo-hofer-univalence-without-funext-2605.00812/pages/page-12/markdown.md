CAVALLO, HÖFER

Lemma 4.12 Let \( I \in \mathrm{Tm}_{\mathbf{Poly}(\mathbb{C})}(\Gamma, \mathcal{U}) \) and \( A, B \in \mathrm{Tm}_{\mathbf{Poly}(\mathbb{C})}(\Gamma, \mathsf{Fam}(I)) \). The shapes of the type \( \mathsf{Iso}(I, A, B) \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma) \) are equivalent to the iterated \( \Sigma \) type in context \( \Gamma_S \) given by the following:

\[
s \colon \prod_ {i: I _ {S}} B _ {S} (i) \longrightarrow A _ {S} (i), \quad f \colon \prod_ {i: I _ {S}} A _ {S} (i) \longrightarrow B _ {S} (i), \quad r \colon \prod_ {i: I _ {S}} B _ {S} (i) \longrightarrow A _ {S} (i), \tag {1}
\]

\[
S \colon f \circ s = \mathrm{id} \quad i n \quad \mathcal {U} ^ {I _ {S}} (B _ {S}, B _ {S}), \qquad R \colon r \circ f = \mathrm{id} \quad i n \quad \mathcal {U} ^ {I _ {S}} (A _ {S}, A _ {S}),
\]

as well as the following functions and paths over this equivalence

\[
\widetilde{f}\colon \prod_{\substack{i:I_{S}\\ a:A_{S}(i)}}B_{P}(f(i,b))\longrightarrow \big(1 + I_{P}(i)\big) + A_{P}(i,a),
\]

\[
\widetilde{s}\colon \prod_{\substack{i:I_{S}\\ b:B_{S}(i)}}A_{P}(s(i,b))\longrightarrow \big(1 + I_{P}(i)\big) + B_{P}(i,b),\quad \widetilde{r}\colon \prod_{\substack{i:I_{S}\\ a:B_{S}(i)}}A_{P}(r(i,b))\longrightarrow \big(1 + I_{P}(i)\big) + B_{P}(i,b),\qquad (2)
\]

\[
S _ {*} \big (\widetilde {s} \circ (\widetilde {f} s) \big) = \mathrm{id} \quad i n \quad \mathcal {U} _ {1 + I _ {P}} ^ {\sum_ {I _ {S}} B _ {S}} (B _ {P}, B _ {P}), \qquad R _ {*} \big (\widetilde {f} \circ (\widetilde {r} f) \big) = \mathrm{id} \quad i n \quad \mathcal {U} _ {1 + I _ {P}} ^ {\sum_ {I _ {S}} A _ {S}} (A _ {P}, A _ {P}),
\]

where \((\widetilde{f}s)(i,b,u):= \widetilde{f} (i,s(i,b),u)\) and \((\widetilde{r} f)(i,a,u):= \widetilde{r} (i,f(i,a),u)\). The family of positions of \(A\cong_{\mathcal{U}^I}B\) is equivalent to the following family over the above characterization of the type of shapes

\[
\sum_ {\substack {i: I _ {S}, a: A _ {S} (i) \\ u: B _ {P} (a, f (i, a))}} \mathrm{is} _ {0} (\widetilde {f} (i, a, u)) + \sum_ {\substack {i: I _ {S}, b: B _ {S} (i) \\ u: A _ {P} (b, s (i, b))}} \mathrm{is} _ {0} (\widetilde {s} (i, b, u)) + \sum_ {\substack {i: I _ {S}, b: B _ {S} (i) \\ u: A _ {P} (b, r (i, b))}} \mathrm{is} _ {0} (\widetilde {r} (i, b, u)). \tag{3}
\]

Proof. The type \(\Gamma \vdash A \cong_{\mathcal{U}^I} B\) is the \(\Sigma\) type given by \(\Gamma \vdash f: \prod_{i:I} A(i) \to B(i)\), \(\Gamma \vdash s, r: \prod_{i:I} B(i) \to A(i)\), and \(\Gamma \vdash fs = \mathrm{id}\), \(\Gamma \vdash rf = \mathrm{id}\). By Proposition 3.7, the shape component of a \(\Sigma\) type is the \(\Sigma\) type of the shapes, and the position component of a \(\Sigma\) type is given by the coproduct of the positions. For the families of functions, these are characterized by Lemma 4.1. By associativity of \(\Sigma\) types, and the curry-uncurry isomorphism these correspond to the six families of functions in (1) and (2).

By Proposition 3.8, the shape of an identity type is the identity type of the shapes. As identity types of \(\Sigma\) types, these are equivalent to \(\Sigma\) types of identity types between the first and second component [36, Theorem 9.3.4]. Since identity types respect the strict isomorphism used above up to equivalence, we see that the shape components of the two identity types are equivalent to the four identity types in (1) and (2).

The composition corresponds to composition in the claimed category by Lemma 4.2. By Proposition 3.8, identity types have empty positions yielding together with Lemma 4.1 the above description given in (3).

Remark 4.13 We sketch the unfolding of \((A\simeq B)\in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)\). The data given by the functions \(f,s,r\) is the same as in Lemma 4.12. The homotopies contribute \(r_{SS}\circ f_{SS}\sim \mathrm{id}_{A_S}\) and \(f_{SS}\circ s_{SS}\sim \mathrm{id}_{B_S}\) to the shape part. Unlike in Lemma 4.12, however, the homotopies do not encode any relationship between \(f_{SP},s_{SP}\), and \(r_{SP}\); a homotopy in \(\mathbf{Poly}(\mathbb{C})\) unfolds only to a homotopy between shape components in \(\mathbb{C}\). As such, the homotopies in \((A\simeq B)_S\) witness an equivalence only between the shape components of \(A\) and \(B\). The family of positions of \(A\simeq B\) agrees with that of \(A\cong B\) in Lemma 4.12.

Lemma 4.14 (In \(\mathbb{C}\)) If \(\mathbb{C} \models \mathrm{CUA}_{\mathcal{U}}^{\bullet}\), then \(\mathrm{Iso}_S(I, A, B) \simeq \left( \sum_{e: A_S \cong_{\mathcal{U}^I_S} B_S} A_P \cong_{\mathcal{U}^I} B_P e \right)\) where \(\widetilde{I} := \sum_{I_S} A_S\).

Proof. Let \( I \stackrel{\circ}{=} (I_S, I_P) \colon \mathcal{U}_S \), \( A \stackrel{\circ}{=} (A_S, A_P) \), \( B \stackrel{\circ}{=} (B_S, B_P) \colon \mathsf{Fam}_S(I) \). Set \( J(i) := 1 + I_P(i) \) and \( \widetilde{I} := \sum_{i: I_S} A_S(i) \). Note that the components of \( \mathsf{Iso}_S(I, A, B) \) given in Lemma 4.12 (1) are equivalent to \( A_S \cong_{\mathcal{U}^I_S} B_S \). Denote the remaining components given in Lemma 4.12 (2) by \( E(I, A, B) \). It suffices to give for each \( e \colon A_S \cong_{\mathcal{U}^I_S} B_S \) an equivalence \( E(I, A, B, e) \simeq (A_P \cong_{\mathcal{U}^I} B_P e) \). By the fundamental theorem of identity types [36, Theorem 11.2.2] and \( \mathsf{CUA}_{\mathcal{U}}^\bullet \), it suffices to consider the case where \( A_S \stackrel{\circ}{=} B_S \) and \( e \stackrel{\circ}{=} \mathrm{id} \). But in this case \( E(I, A, B, \mathrm{id}) \) reduces to \( A_P \cong_{\mathcal{U}_J^\widetilde{I}} B_P \) which is equivalent to \( A_P \cong_{\mathcal{U}^\widetilde{I}} B_P \) by Proposition 4.10.

Lemma 4.15 (In \(\mathbb{C}\)) If \(\mathbb{C} \models \mathrm{CUA}_{\mathcal{U}}^{\bullet}\), then \(\sum_{B: \mathsf{Fam}_S(I)} \mathsf{Iso}_S(I, A, B)\) is contractible for \(I: \mathcal{U}_S\), \(A: \mathsf{Fam}_S(I)\).

12