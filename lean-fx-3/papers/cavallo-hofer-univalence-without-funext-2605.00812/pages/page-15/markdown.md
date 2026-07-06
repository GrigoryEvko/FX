CAVALLO, HÖFER

In any case, using  \( \mathbf{Poly}(-) \) , we will show that  \( CCUA_{U} \)  is strictly stronger than  \( CUA_{U} \)  and moreover not implied by  \( CUA_{U}^{\bullet} \) , yet still does not imply  \( FE_{U} \) . We strengthen Theorem 4.17 to  \( CCUA_{U} \)  by exploiting properties of types in the essential image of  \( \bigcirc_{S} \) . By general properties of reflective subcategories, these are exactly those with strictly invertible unit. In fact, they are also exactly those with categorically invertible unit, but we will not need this.

Proposition 6.3 Naturally in \(\Gamma\), for \(A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)\), the following are equivalent:

(i) \(\eta_A\colon A\to \bigcirc_S A\) is a strict isomorphism,
(ii) there is a map \(A_P \to 0\) in \(\mathbf{Ty}_{\mathbb{C}}(\Gamma_S.A_S)\),
(iii) \(A_{P}\) is strictly isomorphic to 0 in \(\mathbf{Ty}_{\mathbb{C}}(\Gamma_S.A_S)\).

Proof. Consider the morphism \(\eta_A\colon \Gamma .A\to \Gamma .\bigcirc_S A\) in \(\mathbf{Poly}(\mathbb{C})\) over \(\Gamma\). The shape component is given by \(\mathrm{id}_A\colon \Gamma_S.A_S\to \Gamma_S.A_S\). The positions component is given by \([\mathsf{in}_0,!_{A_P}]\colon \Gamma_S.A_S.\Gamma_P\mathsf{p} + 0\to \Gamma_P.A_S.\Gamma_P\mathsf{p} + A_P\). Since the shape component is an isomorphism, \(\eta_A\) is an isomorphism exactly if the position component is.

We work in the internal language of \(\mathbb{C}\). The direction (iii) \(\Longrightarrow\) (i) is clear. The equivalence (ii) \(\Longleftrightarrow\) (iii) follows from the strict \(\eta\) rule for 0. It is left to show (i) \(\Longrightarrow\) (ii). Suppose we are given a family of strict inverses \(\lambda a.[\mathsf{in}_0,i_a]\colon \prod_{a:A_S}\Gamma_P + A_P(a)\to \Gamma_P + 0\) to \(\lambda a.[\mathsf{in}_0,\mathsf{elim}_0]\colon \prod_{a:A_S}\Gamma_P + 0\to \Gamma_P + A_P(a)\). Then \(\lambda a.i_a\colon \prod_{a:A_S}A_P(a)\to \Gamma_P + 0\) and \(\lambda a.\mathsf{elim}_0\colon \prod_{a:A_S}0\to \Gamma_P + A_P(a)\) form an equivalence in \(\mathcal{U}_{\Gamma_P}^{A_S}\). Hence, the family of maps \(i\) is total by Corollary 4.9.

Definition 6.4 A type \(A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma)\) is \(\bigcirc_S\)-modal if the conditions from Proposition 6.3 hold.

Let \(A, B \in \mathrm{Ty}_{\mathbb{C}}(\Gamma)\), \(f \in \mathrm{Tm}_{\mathbb{C}}(\Gamma, A \to B)\), and \(F: \mathbb{C} \to \mathbb{D}\) a pseudomorphism. We write

\[
\widetilde {F} \colon \mathrm{Tm} (\Gamma , A \to B) \longrightarrow \mathrm{Tm} (F \Gamma , F A \to F B), \qquad f \longmapsto \lambda (F (\mathsf {a p p} (f))).
\]

The image of \( f \) under \( F\colon \mathbb{C}\to \mathbb{D} \) is \( Ff\in \mathrm{Tm}(F\Gamma ,F(A\to B)) \). There is always a comparison map \( \lambda (F(\mathsf{app}(\mathfrak{q}_{A\to B})))\colon F(B^{A})\to (FB)^{(FA)} \) [28, §4], and the image of \( Ff \) under this map coincides with \( \widetilde{F} f \).

Lemma 6.5 The pseudomorphism \(\bigcirc_S\colon \mathbb{C}\to \mathbf{Poly}(\mathbb{C})\) preserves paths between functions: naturally in \(\Gamma\), given \(A,B\in \mathrm{Ty}(\Gamma)\) and \(f,g\in \mathrm{Tm}(\Gamma ,A\to B)\), there is a map

\[
\operatorname{Tm} (\Gamma , f = _ {A \rightarrow B} g) \longrightarrow \operatorname{Tm} (\bigcirc_ {S} \Gamma , \widetilde {\bigcirc} _ {S} f = _ {\bigcirc_ {S} A \rightarrow \bigcirc_ {S} B} \widetilde {\bigcirc} _ {S} g).
\]

Proof. Let \( H \in \mathrm{Tm}(\Gamma, f = g) \). We have \( \bigcirc_S H \in \mathrm{Tm}(\bigcirc_S \Gamma, \bigcirc_S (f =_{A \to B} g)) \). By the definition of the identity types in \( \mathbf{Poly}(\mathbb{C}) \) (Proposition 3.8), they are preserved by the pseudomorphism \( \bigcirc_S \). In particular, we have \( \mathrm{Tm}(\bigcirc_S \Gamma, \bigcirc_S (f =_{A \to B} g)) \cong \mathrm{Tm}(\bigcirc_S \Gamma, \bigcirc_S f =_{\bigcirc_S (A \to B)} \bigcirc_S g) \). By lifting the comparison map \( \bigcirc_S (B^A) \to (\bigcirc_S B)^{(\bigcirc_S A)} \) to identity types, we obtain the desired element.

Corollary 6.6 The pseudomorphism \(\bigcirc_S\colon \mathbb{C}\to \mathbf{Poly}(\mathbb{C})\) preserves categorical equivalences: naturally in \(\Gamma\), given \(A,B\in \mathrm{Ty}(\Gamma)\), \(f\in \mathrm{Tm}(\Gamma ,A\to B)\) we have a map

\[
\operatorname{Tm} (\Gamma , \text { is - ceq } (f)) \longrightarrow \operatorname{Tm} (\bigcirc_ {S} \Gamma , \text { is - ceq } (\widetilde {\bigcirc} _ {S} f)).
\]

Proof. The action on functions  \( \widetilde{\bigcirc}_{S} \)  preserves composition and identities.

The \(\bigcirc_S\)-modal types in \(\mathbf{Poly}(\mathbb{C})\) behave like types of the base model. In particular, when the base model enjoys function extensionality, homotopy equivalences between \(\bigcirc_S\)-modal types can be improved to categorical equivalences.

Lemma 6.7 If \(\mathbb{C} \models \mathsf{FE}\), then equivalences coincide with categorical equivalences between \(\bigcirc_S\)-modal types.

Proof. Let \( A, B \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\Gamma) \) and \( f \colon A \to B \) an equivalence. Since \( -S \) preserves identity types, the map \( f_S \colon A_S \to B_S \) is an equivalence, and by FE also a categorical equivalence. The pseudomorphism \( \bigcirc_S \) preserves categorical equivalences by Corollary 6.6. Hence, so does the dependent right adjoint \( \bigcirc_S \) since

15