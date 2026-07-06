6.2. YONEDA LEMMA AND APPLICATIONS

6.2.2.8. We conclude this section with the proof of the following theorem.

Theorem 6.2.2.9. Let $u : C \to D$ and $v : D \to C$ be two functors between locally U-small $(\infty, \omega)$-categories. The two following are equivalent.

(1) The pair $(u, v)$ admits an adjoint structure.
(2) Their exists a pair of natural transformations $\mu : id_C \to vu$ and $\epsilon : uv \to id_D$ together with equivalences $(\epsilon \circ_0 u) \circ_1 (u \circ_0 \mu) \sim id_u$ and $(v \circ_0 \epsilon) \circ_1 (\mu \circ_0 v) \sim id_v$.

We directly give a corollary:

Corollary 6.2.2.10. Let $(u : B \to C, v : C \to B)$ be an adjoint pair between locally U-small $(\infty, \omega)$-categories and $D$ a locally U-small $(\infty, \omega)$-category. If $C$ and $B$ are U-small, this induces an adjunction

$$\_ \circ u : \underline{\mathrm{Hom}}(C, D) \xleftrightarrow{\perp} \underline{\mathrm{Hom}}(B, D) : \_ \circ v$$

and if $D$ is U-small an adjunction

$$u \circ \_ : \underline{\mathrm{Hom}}(D, C) \xleftrightarrow{\perp} \underline{\mathrm{Hom}}(D, B) : v \circ \_$$

Proof. Let $\mu$ and $\epsilon$ be the unit and the counit of the adjunction. We define $\mu' : \underline{\mathrm{Hom}}(C, D) \times [1] \to \underline{\mathrm{Hom}}(C, D)$, induced by currying the morphism

$$\underline{\mathrm{Hom}}(C, D) \times [1] \times C \xrightarrow{id \times \mu} \underline{\mathrm{Hom}}(C, D) \times C \xrightarrow{\mathrm{ev}} D$$

and $\epsilon' : \underline{\mathrm{Hom}}(B, D) \times [1] \to \underline{\mathrm{Hom}}(B, D)$ by currying the morphism

$$\underline{\mathrm{Hom}}(B, D) \times [1] \times B \xrightarrow{id \times \epsilon} \underline{\mathrm{Hom}}(B, D) \times B \xrightarrow{\mathrm{ev}} B$$

We can easily check that $\mu'$ and $\epsilon'$ fulfill the triangle identities, and theorem 6.2.2.9 then implies that the pair $(\_ \circ u, \_ \circ v)$ admits an adjunction structure. We proceed similarly for the second assertion.

6.2.2.11. For the remaining, we fix two functors $u : C \to D$ and $v : D \to C$ between $(\infty, \omega)$-categories as well as an equivalence

$$\phi : \mathrm{hom}_D(u(a), b) \sim \mathrm{hom}_C(a, v(b))$$

natural in $a : C^t$ and $b : D$.

347