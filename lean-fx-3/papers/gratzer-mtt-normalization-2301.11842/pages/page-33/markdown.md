Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:33

$$\widehat{\mathsf{Mod}}^{*}(A).\mathsf{reify} = \lambda m.\mathsf{dec}^{\triangleleft}(\downarrow_{\mathsf{Mod}_{p}^{*}(\mathsf{El}^{*}(A))}\mathsf{dec}_{\widehat{\mathsf{Mod}}^{*}}(m))$$

The checks that all constructions lie over their syntactic counterparts follow immediately from the conclusions of realignment.

**Theorem 5.12.** $\mathcal{G}$ supports an MTT cosmos built around $(\mathsf{Ty}_{m}^{*}, \mathsf{Tm}_{m}^{*})$ and $\pi_{0}: \mathcal{G} \longrightarrow \mathcal{S}$ is a map of MTT cosmoi.

## 6. THE NORMALIZATION ALGORITHM

After Theorem 5.12, it remains only to parlay the existence of the normalization cosmos into a normalization function.

**6.1. The normalization function.** At this point, it becomes necessary to shift from working purely internally to $\mathcal{G}$ to inspecting some constructions externally. Accordingly, we will have use for the *total* spaces of terms and normal forms e.g. $\mathsf{Tm}_{m}^{*} = \sum_{A:\mathsf{Ty}_{m}^{*}}\mathsf{Tm}_{m}^{*}(A)$. We write $\mathcal{T}_{m}$ and $\mathcal{T}_{m}^{\bullet}$ for the presheaves of types and terms in $\mathcal{S}(m)$ to disambiguate them from $\mathsf{Ty}_{m}^{*}$ and $\mathsf{Tm}_{m}^{*}$.

**Lemma 6.1.** *There is a morphism $\downarrow: \mathsf{Tm}_{m}^{*} \longrightarrow \mathsf{Nf}_{m}$ which restricts to id under syn.*

*Proof.* Working internally, $\downarrow(A, M) = (A, \downarrow_{A}M)$.

Fix a term $\Gamma \vdash M: A \circledast m$. Theorems 3.9 and 5.12 define a map $[[M]]: [\Gamma] \longrightarrow \mathsf{Tm}_{m}^{*}$ in $\mathcal{G}(m)$ along with an isomorphism $\alpha: \pi_{0}([\Gamma]) \cong \mathbf{y}(\Gamma)$ such that $\pi_{0}([M]) = [M] \circ \alpha$.

We would like to obtain a normal form for $M$ from $[[M]]$. To this end, we can unfold $[[M]]$ along with $\downarrow$ from Lemma 6.1 to obtain a commuting diagram:

$$\begin{array}{c} \pi_{1}([\Gamma]) \longrightarrow \pi_{1}(\mathsf{Tm}_{m}^{*}) \longrightarrow \pi_{1}(\mathsf{Nf}_{m}) \\ \mathbf{i}[m]^{*}(\alpha) \circ [\Gamma] \Bigg\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathbf{i}[m]^{*}(\mathbf{y}(\Gamma)) \xrightarrow{\mathbf{i}[m]^{*}([M])} \mathbf{i}[m]^{*}(\mathcal{T}_{m}^{\bullet}) \end{array}$$

To normalize $M$, it suffices to construct $\mathsf{atoms}_{\Gamma}: \pi_{1}([\Gamma])_{\Gamma}$ such that $\alpha([\Gamma]) = \mathsf{id}: \mathbf{i}[m]^{*}(\mathbf{y}(\Gamma))_{\Gamma}$: pushing $\mathsf{atoms}_{\Gamma}$ along the top of the diagram would yield a normal form (an element of $\pi_{1}(\mathsf{Nf}_{m})$) which decodes to $M$ by Yoneda. Modulo technical details, $\mathsf{atoms}_{\Gamma}$ is produced by using $\uparrow$ to convert variables for each element of $\Gamma$ into elements of $\pi_{1}([\Gamma])$.

**Lemma 6.2.** *For any $\Gamma \subset \times \circledast m$ there exists $\mathsf{atoms}_{\Gamma}: (\mathbf{y}(\Gamma), \mathbf{y}(\Gamma)) \longrightarrow [\Gamma]$ in $\mathcal{G}$ lying over $\mathsf{id}: \mathbf{i}[m]^{*}(\mathbf{y}(\Gamma))$ in $\mathcal{S}$.*

*Proof.* This proof proceeds by induction on $\Gamma$.

**Case:** $\Gamma = 1$

Here $[\Gamma]$ is terminal, so $\mathsf{atoms}_{1}$ is its unique element. The requirement that $\mathsf{atoms}_{1}$ lie over id is then tautological.