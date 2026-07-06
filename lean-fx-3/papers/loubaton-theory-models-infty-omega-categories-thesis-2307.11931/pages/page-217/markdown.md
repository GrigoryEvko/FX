4.3. GRAY OPERATIONS

Where the cartesianess of the left square comes from the fact that $i^*$ preserves cartesian squares as it is a right adjoint. We just have demonstrated that $i^*j$ is in $\widehat{\mathbf{M}}$. Using proposition 4.2.1.5, and by left cancellation, the right square implies that $j$ is in $\widehat{W}$, which concludes the proof.

**Proposition 4.2.2.8.** *Let $p : C \to D$ be a functor between $(\infty, \omega)$-categories. Then for any globular sums $a$, and any cartesian squares in $\mathrm{Psh}^\infty(\Theta)$:*

$$
\begin{array}{c}
C'' \xrightarrow{j} C' \longrightarrow C \\
\downarrow \quad \downarrow \quad \downarrow \quad \downarrow^p \\
\Sigma^n E^{eq} \longrightarrow \mathbf{D}_n \longrightarrow D
\end{array}
$$

*the morphism $j$ is in $\widehat{W}$.*

*Proof.* This is a direct consequence of lemma 4.2.2.7.

**Theorem 4.2.2.9.** *Let $f : C \to D$ be a discrete Conduché functor. The pullback functor $f^* : (\infty, \omega)\text{-cat}_{/D} \to (\infty, \omega)\text{-cat}_{/C}$ preserves colimits.*

*Proof.* As $\mathrm{Psh}^\infty(\Theta)$ is locally cartesian closed, we can use the corollary 4.1.3.4. The hypotheses are provided by lemmas 4.2.2.6 and proposition 4.2.2.8.

## 4.3 Gray Operations

### 4.3.1 Gray operations on $(\infty, \omega)$-categories

Theorem 3.4.3.14 states that the $(\infty, 1)$-category $(\infty, \omega)$-cat is represented by the model category of marked simplicial sets given in proposition 2.2.1.9 and the functor $\mathrm{N} : (0, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}$ corresponds to the Street nerve $\mathrm{N} : (\infty, \omega)\text{-cat} \to \mathrm{mPsh}(\Delta)$.

An important feature of this model category is that it admits a monoidal structure $\otimes$ given by the *Gray tensor product*. Furthermore, proposition 2.2.2.7 ensures that this operation commutes with colimits in both variables. The induced functor

$$
\_ \otimes [1] : (\infty, \omega)\text{-cat} \to (\infty, \omega)\text{-cat}
$$

is called the *Gray cylinder*. We will show later, in corollary 4.3.3.21, that we have a natural diagram

$$
\begin{array}{ccc}
(C \otimes \{1\})^\circ & \longrightarrow & (C \otimes [1])^\circ \longleftarrow & (C \otimes \{0\})^\circ \\
\downarrow \sim & & \downarrow \sim & & \downarrow \sim \\
C^\circ \otimes \{0\} & \longrightarrow & C^\circ \otimes [1] \longleftarrow & C^\circ \otimes \{1\}
\end{array}
$$

207