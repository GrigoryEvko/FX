28

E. Cavallo and C. Sattler

Proposition 4.15 (Uniform trivial fibrations) We have a weak factorization system $(\mathcal{M}, \mathcal{F}_t)$ where $\mathcal{F}_t$ is the class of uniform trivial fibrations.

Proof By [GS17, Theorem 9.1], which goes through Garner's algebraic small object argument [Gar09], we have a factorization system $(\mathcal{C}, \mathcal{F}_t)$ where $\mathcal{F}_t$ is the class of uniform trivial fibrations. Here we need that the right $\mathcal{M}$-maps coincide with the right $\mathcal{M}^{\mathcal{K}}$-maps and that $\mathcal{M}^{\mathcal{K}}$ is a small category. That the algebraic small object argument is constructive in this case is explained in [GS17, Remark 9.4]; see also [Hen20, Appendix C].

An alternative construction of the factorization using partial map classifiers is described in [GS17, Remark 9.5] and used by Awodey et al. [AGH24; Awo23], while Swan [Swa18, §6] describes a construction using W-types with reductions. The partial map classifier factorization factors any map as a mono followed by a trivial fibration. By the retract argument, any map in $\mathcal{C}$ is then a retract of a mono and hence itself monic, so $\mathcal{C} = \mathcal{M}$.

Definition 4.16 Define $u_{\delta}: \{0, 1\} \times \mathcal{M}^{\mathcal{K}} \to \mathrm{PSh}_{\kappa}(\square_{\gamma})^{\to}$ by $u_{\delta}(k, -) := \delta_k \widehat{\times} (-)$. A uniform fibration is a right $u_{\delta}$-map.

Proposition 4.17 (Uniform fibrations) There exists a weak factorization system $(\mathcal{C}_t, \mathcal{F})$ such that $\mathcal{F}$ is the class of uniform fibrations.

Proof By [GS17, Theorem 7.5], using the algebraic small object argument. Again, see [GS17, Remark 9.4] for discussion of constructivity.

Though the algebraic/uniform description is important to constructively establish the existence of these weak factorization systems, we can also—still constructively—recognize that $\mathcal{F}_t$ and $\mathcal{F}$ are classes of maps with lifting properties in the non-algebraic sense.

Proposition 4.18 Let $f: Y \to X$ in $\mathrm{PSh}_{\kappa}(\square_{\gamma})$. Then

- $f$ is a right $\mathcal{M}$-map if and only if it has the right lifting property against all monomorphisms;
- $f$ is a right $u_{\delta}$-map if and only if it has the right lifting property with respect to $\delta_k \widehat{\times} m$ for all $k \in \{0, 1\}$ and monomorphisms $m$.

Proof By [GS17, Theorem 9.9].

With the two factorization systems in hand, it is straightforward to verify the following.

Proposition 4.19 $(\mathcal{C}_t, \mathcal{F})$ and $(\mathcal{M}, \mathcal{F}_t)$, together with the adjoint functorial cylinder $\mathbb{I} \times (-) \dashv (-)^{\mathbb{I}}$, constitute a cylindrical premodel structure.

2025/10/16 00:43