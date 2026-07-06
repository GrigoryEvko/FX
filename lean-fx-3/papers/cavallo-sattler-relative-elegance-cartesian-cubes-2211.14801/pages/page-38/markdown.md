38

E. Cavallo and C. Sattler

Proof For the non-trivial direction, assume that $L$ sends representables to weakly contractible objects. Given $n \geq 1$ and $I \subseteq [n]$, write $\Lambda_I^n$ for the union of the subobjects $d_i: \Delta^{n-1} \mapsto \Delta^n$ over $i \in I$. We check by induction that $L$ sends $\Lambda_I^n \mapsto \Delta^n$ to a trivial cofibration for $n \in \mathbb{N}$ and $\emptyset \subseteq I \subseteq [n]$. When $|I| = 1$, $\Lambda_I^n$ is the representable $\Delta^{n-1}$, so the claim holds by assumption and 2-out-of-3. Otherwise, choose some $i \in I$. We have the following pushout square, which is preserved by $L$:

$$\begin{array}{c} \Lambda_{d_i^{-1}(I)}^{n-1} \longrightarrow \Lambda_{I \setminus \{i\}}^n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \Delta^{n-1} \xrightarrow[d_i]{} \Lambda_I^n. \end{array}$$

By induction hypothesis, $L$ sends the left vertical map to a trivial cofibration. As trivial cofibrations are closed under cobase change, $L$ then also sends the right vertical map to a trivial cofibration. By induction hypothesis, $L$ sends $\Lambda_{I \setminus \{i\}}^n \mapsto \Delta^n$ to a trivial cofibration. By 2-out-of-3, we conclude that $L$ sends $\Lambda_{I \setminus \{i\}}^n \mapsto \Delta^n$ to a trivial cofibration. For $I = [n] \setminus k$, we obtain that $L$ sends the horn inclusion $\Lambda_k^n \to \Delta^n$ to a trivial cofibration. This makes $L$ a left Quillen adjoint.

The combinatorics of the above proof have a conceptual explanation in terms of the pushout join in augmented simplicial sets, which produces boundary inclusions and horn inclusions starting from the maps $\emptyset \to 1$ and $\Delta^{-1} \to 1$.

Corollary 4.53 (cf. Sat 19, Proposition 3.6) $\blacktriangle_!$ is a left Quillen adjoint $\widehat{\Delta}^{\mathrm{kq}} \to \overline{\square}_{\vee}^{\mathrm{ty}}$.

Proof By Lemma 4.49, $\blacktriangle_!$ preserves monomorphisms. Using Lemma 4.52, it suffices to show that $\blacktriangle_! \Delta^n \cong \not\cong [n]$ is weakly contractible for $n \in \mathbb{N}$. For this, we observe that $\not\cong [n]$ is a homotopy retract of 1 for each $n \in \mathbb{N}$ via the homotopy $(t, i) \mapsto (t \vee i): [1] \times [n] \to [n]$ and apply Corollary 4.51.

Lemma 4.54 (cf. Sat 19, §3.3) $\blacktriangle^*$ is a left Quillen adjoint $\overline{\square}_{\vee}^{\mathrm{ty}} \to \widehat{\Delta}^{\mathrm{kq}}$.

Proof $\blacktriangle^*$ preserves monomorphisms because it is a right adjoint. As it is also a left adjoint, it also preserves pushout products, so $\blacktriangle^*(\delta_k \overline{\times} m) \cong \blacktriangle^* \delta_k \overline{\times} \blacktriangle^* m \cong d_{1-k} \overline{\times} \blacktriangle^* m$ is a trivial cofibration for any $k \in \{0, 1\}$ and $m: A \mapsto B$.

We quickly see that $\blacktriangle_! \dashv \blacktriangle^*$ is a Quillen coreflection in the following sense:

Lemma 4.55 The derived unit $X \xrightarrow{\eta_X} \blacktriangle^* \blacktriangle_! X \to \blacktriangle^* ((\blacktriangle_! X)^{\mathrm{fib}})$ is valued in weak equivalences.

Proof It is equivalent to prove the unit $\eta$ is valued in weak equivalences: any fibrant replacement map $\blacktriangle_! X \mapsto (\blacktriangle_! X)^{\mathrm{fib}}$ is a trivial cofibration, so is mapped to a trivial cofibration by the left Quillen adjoint $\blacktriangle^*$. But $\blacktriangle$ is fully faithful, so the unit is valued in isomorphisms.

2025/10/16 00:43