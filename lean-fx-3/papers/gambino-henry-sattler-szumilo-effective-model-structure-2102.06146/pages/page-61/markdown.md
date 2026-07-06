**Lemma 12.12.** *The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ preserves cofibrations and trivial cofibrations.*

*Proof.* The forgetful functor preserves all colimits that exist so it is enough to show that the generating (trivial) cofibrations of $\mathfrak{s}\mathcal{E}$ are sent to (trivial) cofibrations. The case of cofibrations follows from Theorem 4.6 and Lemma 12.3. For trivial cofibrations, note that if $X \in \mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}$, then $\underline{U}\underline{X} = U\underline{X}$ (the first $U$ is the forgetful functor $\mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t} \to \mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$, the second one is $\mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$). Thus it is enough to show that $U\Lambda^n[k] \to U\Delta[n]$ is a trivial cofibration in $\mathfrak{s}_*\mathcal{E}$ for all $0 \leq k \leq n$. For this it is sufficient to show that $\Lambda^n[k] \to U\Delta[n]$ is a trivial cofibration in $\mathfrak{s}_*\mathcal{S}\mathfrak{e}\mathfrak{t}$ which was proven in [Hen18, Corollary 5.5.15 (ii)]. $\square$

Note that the forgetful functor $U$ preserves trivial fibrations, but trivial fibrations in $\mathfrak{s}_*\mathcal{E}$ are not necessarily weak equivalences. Nonetheless, the following statement is valid.

**Lemma 12.13.** *The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ sends trivial fibrations to weak equivalences.*

*Proof.* This follows by the same argument as the second part of [Hen19, Lemma 2.2.1]. $\square$

**Lemma 12.14.** *For each $X \in \mathfrak{s}_*\mathcal{E}$, the unit $X \to ULX$ is a trivial cofibration.*

*Proof.* The composite $UL$ preserves all the relevant colimits, so it is enough to check that for each generating cofibration $\underline{\partial\Delta_*[n]} \to \underline{\Delta_*[n]}$, the map

$$UL(\underline{\partial\Delta_*[n]}) \sqcup_{\underline{\partial\Delta_*[n]}} \underline{\Delta_*[n]} \to UL\underline{\Delta_*[n]}$$

is a trivial cofibration. It then follows from Lemma 3.20 that the same holds for all cofibrations and the case of $\varnothing \to X$ concludes the proof. Thus it suffices to prove the statement in the case of semisimplicial sets which is [Hen18, Proposition 5.5.14]. $\square$

**Proposition 12.15.** *The forgetful functor $U: \mathfrak{s}\mathcal{E} \to \mathfrak{s}_*\mathcal{E}$ preserves and reflects weak equivalences.*

*Proof.* The conclusion is valid for $\mathfrak{s}\mathcal{E} = \mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}$ by [Hen19, Lemma 2.2.1] and thus it holds for morphisms between fibrant objects. Indeed, $\operatorname{Hom}_{\mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}}(E, UX) = U\operatorname{Hom}_{\mathfrak{s}\mathcal{S}\mathfrak{e}\mathfrak{t}}(E, X)$ and weak equivalences between fibrant objects in both $\mathfrak{s}\mathcal{E}$ and $\mathfrak{s}_*\mathcal{E}$ are detected by pointwise evaluation.

For a general morphism $X \to Y$, we consider its fibrant replacement as constructed in the small object argument. Since $U$ preserves trivial cofibrations (by Lemma 12.12) and fibrations, it follows that it preserves such fibrant replacements. Thus the conclusion follows from the special case of morphisms between fibrant objects. $\square$

**Corollary 12.16.** *For each $X \in \mathfrak{s}\mathcal{E}$, the counit $LUX \to X$ is a weak equivalence.*

*Proof.* This follows from the triangle identities using Lemma 12.14 and Proposition 12.15. $\square$

**Theorem 12.17.** *When $\mathcal{E}$ is countably lextensive, the functor $U: \mathfrak{s}\mathcal{E}_{\text{fib}} \to \mathfrak{s}_*\mathcal{E}_{\text{fib}}$ is an equivalence of fibration categories.*

*Proof.* Consider the functor $L': \mathfrak{s}_*\mathcal{E}_{\text{fib}} \to \mathfrak{s}\mathcal{E}_{\text{fib}}$ obtained by composing $L$ with a chosen fibrant replacement functor in $\mathfrak{s}\mathcal{E}$. Such fibrant replacement along with the unit of the adjunction $L \dashv U$ induce a natural transformation $\operatorname{id}_{\mathfrak{s}_*\mathcal{E}_{\text{fib}}} \to UL'$ which is a weak equivalence by Lemma 12.14 and Proposition 12.15. Similarly, using the counit we obtain two natural transformations $L'UX \leftarrow LUX \to X$ for $X \in \mathfrak{s}\mathcal{E}$. They are weak equivalences by definition and by Corollary 12.16, but $LU$ is not an endofunctor of $\mathfrak{s}\mathcal{E}_{\text{fib}}$, just of $\mathfrak{s}\mathcal{E}$. However, we can apply a functorial factorisation to

61