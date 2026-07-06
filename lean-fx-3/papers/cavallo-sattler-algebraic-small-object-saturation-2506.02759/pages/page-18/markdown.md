We employ the following construction that transfers a pointed endofunctor along an adjunction.

Definition 2.3.9. Let \(\mathcal{E}: F \xleftrightarrow{\longleftrightarrow} G: \mathcal{F}\) be an adjoint pair of functors and let \((T, \tau)\) be a pointed endofunctor on \(\mathcal{E}\). When the pushout

\[
\begin{array}{c} F G \xrightarrow {F \tau G} F T G \\ \epsilon \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text {   (2.5)   } \\ \operatorname{Id} _ {\mathcal {F}} \xrightarrow [ \pi ]{\text {   }} P \end{array}
\]

in \([\mathcal{F},\mathcal{F}]\) exists and is computed pointwise, we say that the pointed endofunctor \((P,\pi)\) on \(\mathcal{F}\) is the transfer of \((T,\tau)\) along \(F\dashv G\).

Proposition 2.3.10. Let \(\mathcal{E}: F \xleftrightarrow{\longleftrightarrow} G: \mathcal{F}\) be an adjoint pair of functors and let \(S\) be a well-pointed endofunctor on \(\mathcal{E}\). When it exists, the transfer of \(S\) along \(F \dashv G\) is also well-pointed.

Proof. See Kelly [Kel80, Proposition 9.2].

Proposition 2.3.11. Let \(\mathcal{E}: F \xleftrightarrow{\longleftrightarrow} G: \mathcal{F}\) be an adjoint pair of functors and let \(\mathsf{T} = (T, \tau)\) be a pointed endofunctor on \(\mathcal{E}\). When the transfer \(\mathsf{P} = (P, \pi)\) of \(\mathsf{T}\) along \(F \dashv G\) exists, the square

\[
\begin{array}{c} \mathrm{P-Alg} \longrightarrow \mathrm{T-Alg} \\ U _ {\mathrm{P}} \Biggl \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text {   (2.6)   } \\ \mathcal {F} \xrightarrow [ G ]{} \mathcal {E} \end{array}
\]

is a pullback (and thus also a 2-pullback [JS93, Theorem 1]). Here the functor \(\mathsf{P}\text{-Alg} \to \mathsf{T}\text{-Alg}\) sends an algebra \(PA \to A\) to the transpose of the composite \(FTGA \to PA \to A\).

Proof. An explicit proof can be found in Seip [Sei24, Lemma 10]. The case where T is well-pointed is in Kelly [Kel80, Proposition 9.2], and the general case is used by Bourke and Garner [BG16a, Proposition 16] with reference to the proof for idempotent monads in Wolff [Wol78, §2]. □

In other words, the category of objects \( A \in \mathcal{F} \) paired with a T-algebra structure on \( GA \) is itself the category of algebras for a pointed endofunctor.

Definition 2.3.12. Let \(\mathcal{E}: F \xleftrightarrow{\longleftrightarrow} G: \mathcal{F}\) be an adjoint pair of functors and let \(\mathsf{T} = (T, \tau)\) be a pointed endofunctor on \(\mathcal{E}\) admitting a transfer \(\mathsf{P} = (P, \pi)\) along \(F \dashv G\). Given a \(\mathsf{P}\)-algebraized \(\alpha\)-chain \((X, x)\), write \(G(X, x)\) for the \(\mathsf{T}\)-algebraized \(\alpha\)-chain consisting of the \(\alpha\)-chain \(GX: (\alpha, \preceq) \to \mathcal{E}\) and maps

\[
T G X _ {\beta} \xrightarrow {\gamma_ {X _ {\beta}}} G P X _ {\beta} \xrightarrow {G x _ {\beta <   \alpha}} G X _ {\beta}
\]

for \(\beta < \alpha\), where \(\gamma: TG \to GP\) is the transpose of the transformation \(FTG \to P\) in the pushout (2.5) defining \(\mathsf{P}\).

Proposition 2.3.13. Let a strong morphism of adjunctions

\[
(U, V, \alpha , \beta) \colon (\mathcal {C} _ {1}, \mathcal {D} _ {1}, F _ {1}, G _ {1}, \eta_ {1}, \epsilon_ {1}) \to (\mathcal {C} _ {2}, \mathcal {D} _ {2}, F _ {2}, G _ {2}, \eta_ {2}, \epsilon_ {2})
\]

in \(\mathbf{Adj}_s\) be given together with an extension of \(U\) to a strong morphism of pointed endofunctors \((U,\gamma)\colon (\mathcal{C}_1,\mathsf{T}_1)\to (\mathcal{C}_2,\mathsf{T}_2)\) in \(\mathbf{PtdEndo}_s\). If the transfers \(\mathsf{P}_1\) of \(\mathsf{T}_1\) along \(F_{1}\dashv G_{1}\) and \(\mathsf{P}_2\) of \(\mathsf{T}_2\) along \(F_{2}\dashv G_{2}\) respectively exist and \(V\) preserves the pushouts defining \(\mathsf{P}_1\), then \(V\) extends to a morphism \((\mathcal{D}_1,\mathsf{P}_1)\to (\mathcal{D}_2,\mathsf{P}_2)\) in \(\mathbf{PtdEndo}_s\).

18