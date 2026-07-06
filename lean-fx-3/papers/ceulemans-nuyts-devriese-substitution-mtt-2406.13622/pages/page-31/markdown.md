J. Ceulemans, A. Nuyts and D. Devriese

31

Furthermore, we have

$$\begin{array}{l} \operatorname{embed}(\operatorname{suc}\left(v^{\prime}\right))\left[\operatorname{embed}(\sigma \cdot \Phi^{\prime} \cdot \mu \cdot \Lambda)\right]_{\mathrm{ws}} \\ =\operatorname{embed}\left(v^{\prime}\right)\left[\pi \cdot \Lambda\right]_{\mathrm{ws}}\left[\left(\operatorname{embed}(\sigma \cdot \Phi^{\prime})\right)^{+} \cdot \Lambda\right]_{\mathrm{ws}} \quad\left(\text { Definition of } \operatorname{embed}(\operatorname{suc}\left(v^{\prime}\right))\right) \\ \equiv^{\sigma} \operatorname{embed}\left(v^{\prime}\right)\left[\left(\pi \circ\left(\operatorname{embed}(\sigma \cdot \Phi^{\prime})\right)^{+}\right) \cdot \Lambda\right]_{\mathrm{ws}} \quad(*) \\ \equiv^{\sigma} \operatorname{embed}\left(v^{\prime}\right)\left[\left(\operatorname{embed}(\sigma \cdot \Phi^{\prime}) \circ \pi\right) \cdot \Lambda\right]_{\mathrm{ws}} \quad\left(\text { WSMTT-EQ-SUB-EXTEND-WEAKEN }\right) \\ \equiv^{\sigma} \operatorname{embed}\left(v^{\prime}\right)\left[\operatorname{embed}(\sigma \cdot \Phi^{\prime} \cdot \Lambda)\right]_{\mathrm{ws}}\left[\pi \cdot \Lambda\right]_{\mathrm{ws}} . \quad(*) \end{array}$$

The steps marked with (*) make use of WSMTT-EQ-EXPR-SUB-COMPOSE and WSMTT-EQ-SUB-LOCK-COMPOSE.

▶ Lemma 30. Up to σ-equivalence, applying a weakening renaming commutes with the embedding function. In other words, for every lock telescope Λ : LockTele(m → n) and SFMTT expression Γ̂ . Λ ⊢_sf t expr @ n, we have that Γ̂ . μ . Λ ⊢_ws embed(t [π . Λ]_aren) ≡^σ embed(t) [π . Λ]_ws ≡^σ embed(t) [embed(π . Λ)]_ws expr @ n.

Proof. We first prove the second σ-equivalence by computing the following.

$$\begin{array}{l} \operatorname{embed}(\pi \cdot \Lambda)=\operatorname{embed}(\pi) \cdot \Lambda=\operatorname{embed}(\operatorname{weaken}(\operatorname{id}^{\mathrm{a}})) \cdot \Lambda \\ =\left(\operatorname{embed}(\operatorname{id}^{\mathrm{a}}) \circ \pi\right) \cdot \Lambda=(\operatorname{id} \circ \pi) \cdot \Lambda \\ \equiv^{\sigma} \pi \cdot \Lambda \quad\left(\text { WSMTT-EQ-SUB-ID-LEFT }\right) \end{array}$$

The rule WSMTT-EQ-SUB-ID-LEFT is not included in Figure 4, but it is similar to WSMTT-EQ-SUB-ID-RIGHT.

To prove the other σ-equivalence we use Lemma 29, so we take an arbitrary lock telescope Θ : LockTele(n → o) and a variable Γ̂ . Λ . Θ ⊢_sf v var @ o and then show that embed(v [π . Λ . Θ]_aren) = embed(v) [embed(π . Λ . Θ)]_ws. This can be easily proved by expanding the definition of embed(_) as follows.

$$\begin{array}{l} \operatorname{embed}\left(v[\pi]_{\text {aren }}^{\Lambda \cdot \Theta}\right)=\operatorname{embed}(\operatorname{suc}(v)) \\ =\operatorname{embed}(v)[\pi \cdot \Lambda \cdot \Theta]_{\mathrm{ws}} \\ \equiv^{\sigma} \operatorname{embed}(v)\left[\operatorname{embed}(\pi \cdot \Lambda \cdot \Theta)\right]_{\mathrm{ws}} \end{array}$$

Using Lemma 30, we can now prove a result similar to Lemma 29 but for substitutions instead of renamings.

▶ Lemma 31. Let ⊢_sf σ asub(Γ̂ → Δ̂) @ m be an atomic SFMTT substitution and assume that Γ̂ . Λ ⊢_ws embed(v [σ . Λ]_asub) ≡^σ embed(v) [embed(σ . Λ)]_ws expr @ n for every lock telescope Λ : sTele(m → n) and variable Δ̂ . Λ ⊢_sf v var @ n. Then we have that Γ̂ ⊢_ws embed(t [σ]_asub) ≡^σ embed(t) [embed(σ)]_ws expr @ m for all expressions Δ̂ ⊢_sf t expr @ m.

Proof. The proof is very similar to that of Lemma 29. Again we make use of Lemma 28, so we take an arbitrary Φ : sTele(m → n) and Δ̂ . Φ ⊢_sf v var @ n and show that Γ̂ . Φ ⊢_ws embed(v [σ . Φ]_asub) ≡^σ embed(v) [embed(σ . Φ)]_ws expr @ n by induction on the number of variables in Φ.

- CASE Φ = Λ, so Φ contains no variables
The result we need to show is exactly the assumption in the lemma.
- CASE Φ = Φ' . μ . Λ

We proceed by case distinction for the variable v.