Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:23

Proof. We consider the only case of $\bigcirc$, as the argument for $\bullet$ is identical. First, we observe that $\mathbf{Gl}(f,g)$ preserves $\bigcirc$ externally. That is, there is an isomorphism $\alpha : \mathbf{Gl}(f,g) \circ \bigcirc \cong \bigcirc \circ \mathbf{Gl}(f,g)$. It remains to show that this isomorphism can be internalized. Let us write $\tau_m : \mathcal{T}_m^* \longrightarrow \mathcal{T}_m$ for the universe of types in $\mathbf{Gl}(\rho_m)$ and write $\tau_n$ for its counterpart in $\mathbf{Gl}(\rho_n)$. Let us further write $i$, $\hat{\bigcirc}_m$, and $\hat{\bigcirc}_n$ for the cartesian natural transformations $\mathbf{Gl}(f,g)(\tau_n) \longrightarrow \tau_m$, $\bigcirc \tau_m \longrightarrow \tau_m$, and $\bigcirc \tau_n \longrightarrow \tau_n$ that are used to interpret $\langle \mu \mid - \rangle$ and $\bigcirc$ in both $\mathbf{Gl}(\rho_n)$ and $\mathbf{Gl}(\rho_m)$, respectively.

Unfolding this statement into the model, we must argue that the following pair of maps classify isomorphic families:

$$\mathbf{Gl}(f,g)(\bigcirc \mathcal{T}_n) \xrightarrow{\mathbf{Gl}(f,g)(\hat{\bigcirc})} \mathbf{Gl}(f,g)(\mathcal{T}_n) \xrightarrow{i} \mathcal{T}_m$$

$$\mathbf{Gl}(f,g)(\bigcirc \mathcal{T}_n) \xrightarrow{\bigcirc i \circ \alpha} \bigcirc \mathcal{T}_m \xrightarrow{\hat{\bigcirc}} \mathcal{T}_m$$

We check that both classify $\mathbf{Gl}(f,g)(\bigcirc \tau_n)$ as both $\mathbf{Gl}(f,g)$ and $\bigcirc$ preserve finite limits. $\square$

Remark 4.14. Technically, syn, $\bigcirc$, and $\bullet$ should be always annotated with a mode. In light of these results, however, we shall omit this annotation and systematically identify $\mathbf{syn}_m$ and $\langle \mu \mid \mathbf{syn}_n \rangle$. As both are subterminal, there are no coherence issues in this identification.

Definition 4.15. The language of multimodal STC (MSTC) is extensional MTT with a cumulative hierarchy of universes and a universe of propositions such that

- Each mode is equipped with a proposition syn.
- Each universe satisfies the realignment axiom for syn.
- MTT modalities commute with syn, $\bigcirc$, and $\bullet$.

Summarizing the preceding discussion:

Theorem 4.16. $\mathbf{Gl}(\rho_n)$, $\mathbf{Gl}(\rho_m)$, and $\mathbf{Gl}(f,g)$ assemble into a presheaf cosmos and a model of MSTC.

In fact, it is only a small step from this result to the full fundamental lemma of multimodal STC:

Theorem 4.17. Given a pair of cosmoi $F, G : \mathcal{M} \longrightarrow \mathbf{Cat}$ and a 2-natural transformation $\rho : F \longrightarrow G$ such that each $F(\mu), G(\mu)$ preserves finite colimits and each $\rho_m$ is continuous, $\mathbf{Gl}(\rho) : \mathcal{M} \longrightarrow \mathbf{Cat}$ both a presheaf cosmos and a model of MSTC. Furthermore $\pi_0 : \mathbf{Gl}(\rho) \longrightarrow F$ is a morphism of cosmoi.

## 5. THE NORMALIZATION COSMOS

Recall from Section 2.4 the 2-functor of categories of renamings $\mathsf{Ren}_{-}$. By an identical construction to Example 3.6, we obtain the cosmos of renamings $\mathcal{R}(-) = \mathbf{PSh}(\mathsf{Ren}_{-})$ and the 2-natural transformation $\mathbf{i}[-] : \mathsf{Ren}_{-} \longrightarrow \mathsf{Cx}_{-}$ acts by precomposition to yield a 2-natural transformation $\mathbf{i}[-]^* : \mathcal{S} \longrightarrow \mathcal{R}$. Theorem 4.17 then yields the following:

Definition 5.1. The normalization cosmos $\mathcal{G}$ is a presheaf cosmos and model of MSTC where $\mathcal{G}(m) = \mathbf{Gl}(\mathbf{i}[m]^*)$.