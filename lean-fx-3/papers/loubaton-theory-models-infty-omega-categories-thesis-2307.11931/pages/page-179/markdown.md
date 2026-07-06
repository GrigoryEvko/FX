3.4. THE CASE $A := \mathrm{tPsh}(\Delta)^n$

3.4.3.5. Let $n \in \mathbb{N} \cup \{\omega\}$. We consider the functor

$$\Theta_n \times \Delta \to \mathrm{tPsh}(\Delta)$$

sending a pair $(a, [n])$ onto $\mathrm{N}(a) \times \tau_0^i([n])$. By left Kan extension, this induces an adjunction

$$L_n : \mathrm{Psh}_\Delta(\Theta_n) \xrightarrow{\perp} \mathrm{tPsh}(\Delta) : N_{L_n} \tag{3.4.3.6}$$

**Theorem 3.4.3.7** (Ozornova-Rovelli). *The adjunction*

$$L_n : \mathrm{Psh}_\Delta(\Theta_n) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)^n : N_{L_n}$$

*is a Quillen adjunction.*

*Proof.* This is [OR22, theorem 4.16].

**Remark 3.4.3.8.** The two authors demonstrate this result when $\mathrm{tPsh}(\Delta)$ is endowed with the model structure for $n$-complicial sets with $n < \omega$. However, their argument generalizes directly to the case $n = \omega$.

A direct induction using [OR22, theorem 3.22] implies that the left adjoint preserves globes.

**Proposition 3.4.3.9.** *For any $n \in \mathbb{N}$, the adjunction given in theorem 3.4.3.7 is a Quillen equivalence.*

*Proof.* This is an adjunction between two models of $(\infty, n)$-categories. As the left adjoint preserves globes up to homotopy, the result follows from [BSP21, proposition 15.10].

3.4.3.10. If $C$ is a model category, we denote by $C^{(\infty,1)}$ the corresponding $(\infty, 1)$-category.

**Lemma 3.4.3.11.** *For any integer $n$, the $(\infty, 1)$-functor*

$$\iota^n : (\mathrm{Psh}_\Delta(\Theta_n))^{(\infty,1)} \to (\mathrm{Psh}_\Delta(\Theta))^{(\infty,1)}$$

*is fully faithful.*

*Proof.* This is proposition 4.2.1.39.

**Lemma 3.4.3.12.** *For any integer $n$, the $(\infty, 1)$-functor*

$$\tau_n^i : (\mathrm{tPsh}(\Delta)^n)^{(\infty,1)} \to (\mathrm{tPsh}(\Delta)^\omega)^{(\infty,1)}$$

*is fully faithful.*

169