Shulman

18–11

- An element \((A, a) \in \mathrm{Tm}^!(\Gamma)\) consists of \(\mathsf{V}_A \in \mathcal{D}\), a type \(\mathsf{E}_A \in \mathrm{Ty}(\mathsf{V}_A)\), and \(a: \Gamma \to \mathsf{V}_A \triangleright \mathsf{E}_A\).
- The map \(\tau^{!}\) sends \(a\) to \({}^{r}A^{!} = \mathfrak{p}_{A} \circ a\).

Since \(\tau^!\) is the pullback of \(\tau\) along the map \(\mathrm{Ty}^! \to \mathrm{Ty}\) sending \(A\) to \(\mathsf{E}_A[\mathsf{A}']\), it is a natural model.

Given an adjoint modal pre-model, we define \(\widehat{\tau}_p^! = (\mathsf{L}^p)^*\tau_p^!\). Thus, an element \(A \in \widehat{\mathrm{Ty}}_p^!(\Gamma)\) consists of an object \(\mathsf{V}_A \in \mathcal{C}_p\), a type \(\mathsf{E}_A \in \mathrm{Ty}_p(\mathsf{V}_A)\), and a morphism \(^r A^! : \mathsf{L}^p\Gamma \to \mathsf{V}_A\), or equivalently \(^r A^! : \Gamma \to \mathsf{R}_p\mathsf{V}_A\).

Lemma 5.5 If \((\widehat{\mathcal{C}},\mathcal{C})\) is an adjoint modal pre-model over \((\mathcal{L},\mathcal{S})\), then \((\widehat{\mathcal{C}},\widehat{\tau}')\) is an adjoint modal natural model over \(\mathcal{L}[\mathcal{S}^{\dagger}]\).

Proof. The tangible morphisms in \(\mathcal{L}[\mathcal{S}^{\dagger}]\) are \(\mu \circ \nu^{\dagger}\), for \(\mu : q \to r\) in \(\mathcal{L}\) and \(\nu : q \to p\) in \(\mathcal{S}\). Thus, we must show that in this case \((\widehat{\mathcal{C}}_{\nu} \circ \widehat{\mathcal{C}}^{\mu})^{*}\widehat{\tau}_{p}^{!} = (\mathsf{L}^{p} \circ \widehat{\mathcal{C}}_{\nu} \circ \widehat{\mathcal{C}}^{\mu})^{*}\tau_{p}^{!}\) is representable. But by pseudonaturality of \(\mathsf{L}\), we have \(\mathsf{L}^{p} \circ \widehat{\mathcal{C}}_{\nu} \circ \widehat{\mathcal{C}}^{\mu} \cong \mathcal{C}_{\nu} \circ \mathsf{L}^{q} \circ \widehat{\mathcal{C}}^{\mu}\), and this has a right adjoint \(\widehat{\mathcal{C}}_{\mu} \circ \mathsf{R}_{q} \circ \mathcal{C}_{\nu^{\dagger}}\). Finally, restriction along any functor with a right adjoint preserves representability.

Explicitly, the comprehension \(\Gamma \triangleright^{\mu \circ \nu^{\dagger}}A\) is the pullback

\[
\begin{array}{c} \Gamma \triangleright^ {\mu \circ \nu^ {\dagger}} A \xrightarrow {} \widehat {\mathcal {C}} _ {\mu} R _ {q} \mathcal {C} _ {\nu^ {\dagger}} (V _ {A} \triangleright E _ {A}) \\ \widehat {\mathfrak {p}} _ {A} \Biggl \downarrow \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \quad \text {   } \\ \Gamma \xrightarrow {} \widehat {\mathcal {C}} _ {\mu} R _ {q} \mathcal {C} _ {\nu^ {\dagger}} \mathcal {C} _ {\nu} L ^ {q} \widehat {\mathcal {C}} ^ {\mu} (\Gamma) \xrightarrow [ r _ {A} ]{} \widehat {\mathcal {C}} _ {\mu} R _ {q} \mathcal {C} _ {\nu^ {\dagger}} V _ {A}. \end{array} \tag {5.6}
\]

Theorem-Schema 5.7 If \((\widehat{\mathcal{C}},\mathcal{C})\) is an adjoint modal pre-model, then for any of the type constructors considered in [29], if \((\mathcal{C},\tau)\) has weakly stable structure, then \((\widehat{\mathcal{C}},\widehat{\tau}')\) has strictly stable structure.

Proof. Since  \( L^{p} \)  preserves finite limits, any weakly stable or pseudo-stable structure on  \( \tau_{p} \)  lifts to  \( (\mathsf{L}^{p})^{*}\tau_{p} \) . Therefore, by [29],  \( ((\mathsf{L}^{p})^{*}\tau_{p})^{!} \)  has strictly stable structure. If we identify  \( C_{p} \)  with the image of  \( R_{p} \) , then  \( \widehat{\mathrm{Ty}}^{!}\subseteq((\mathsf{L}^{p})^{*}\mathrm{Ty}_{p})^{!} \)  consists of the types whose local universes lie in  \( C_{p} \) . By Lemma 5.4,  \( C_{p} \)  is closed under all the local universe manipulations of [29]; hence  \( \widehat{\tau}^{!} \)  is closed under the strictly stable structure. □

For the modal type formers, the “weakly stable” structure exists on C alone; thus we name its structure.

Definition 5.8 A modal pre-model over an adjoint mode theory \(\mathcal{M}\) is a pseudofunctor \(\mathcal{C}:\mathcal{M}\to \mathcal{C}at\) such that each \(\mathcal{C}_p\) is a natural pseudo-model.

### 5.3 \(\Pi\)-structure

Definition 5.9 A morphism \(\delta : \Gamma \to \Delta\) in a natural pseudo-model is type-exponentiable if for any \(B \in \mathrm{Ty}(\Gamma)\), the pushforward of \(\Gamma \triangleright B\) along \(\delta\) is isomorphic to a type projection \(\Delta \triangleright \Pi(f, B) \to \Delta\).

Definition 5.10 A modal pre-model \(\mathcal{C}\) has pre-\(\Pi\)-structure if for any sharp \(\mu : p \to q\) in \(\mathcal{M}\) and any \(\Gamma \in \mathcal{C}_p\) and \(A \in \mathrm{Ty}_p(\Gamma)\), any pullback of \(\mathcal{C}_{\mu} \mathfrak{p}_A : \mathcal{C}_{\mu}(\Gamma \triangleright A) \to \mathcal{C}_{\mu} \Gamma\) is type-exponentiable.

Lemma 5.11 Let \(\mathsf{L}:\mathcal{A}\rightleftarrows\mathcal{B}:\mathsf{R}\) be an adjunction where \(\mathsf{L}\) preserves pullbacks. Let \(f:A\to B\) be in \(\mathcal{A}\), \(g:C\to \mathsf{L}A\) in \(\mathcal{B}\), and suppose that the pushforward \((\mathsf{L}f)_{*}g:(\mathsf{L}f)_{*}C\to \mathsf{L}B\) of \(g\) along \(\mathsf{L}f\) exists in \(\mathcal{B}\). Then the pullback of \(\mathsf{R}((\mathsf{L}f)_{*}C)\) to \(B\) is a pushforward along \(f\) of the pullback of \(\mathsf{R}g\) to \(B\).

Proof. This is a fairly straightforward diagram chase.

□

Theorem 5.12 If \((\widehat{\mathcal{C}},\mathcal{C})\) is an adjoint modal pre-model over \((\mathcal{L},\mathcal{S})\) such that \(\mathcal{C}\) has pre-\(\Pi\)-structure over \(\mathcal{L}[\mathcal{S}^{\dagger}]\), then \((\widehat{\mathcal{C}},\widehat{\tau}^{\dagger})\) has \(\Pi\)-structure over \(\mathcal{L}[\mathcal{S}^{\dagger}]\).