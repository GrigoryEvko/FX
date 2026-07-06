Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:37

$$\begin{array}{l} \llbracket \operatorname{mod}_{\mathrm{id}}(M) \rrbracket = \llbracket M \rrbracket \\ \llbracket \operatorname{let}_{\chi} \operatorname{mod}_{\xi}(\_) \leftarrow M \text { in } N \rrbracket = \llbracket N \rrbracket [\operatorname{id}.\llbracket M \rrbracket] \end{array}$$

Unfolding the interpretation of Equation 7.1, we observe that an inverse to this map corresponds to function extensionality for functions $\mathsf{Nat} \rightarrow A$. As function extensionality is independent of MLTT, there must be no inverse to Equation 7.1 definable within MTT. $\square$

In light of Theorem 7.2, we refer to the existence of an inverse to Equation 7.1 as modal extensionality. Modal extensionality is useful in practice. In incarnations of guarded recursion within MTT, for instance, some version of modal extensionality is required to prove any equalities involving guarded types [GKNB21, GB22]. It is therefore worth investigating whether modal extensionality is compatible with both normalization and canonicity.⁷

In work by Shulman [Shu18] and Gratzer [GKNB21], crisp induction principles are a variation of the induction principles for types such as bool or $\mathsf{Id}_A(a_0, a_1)$ which allow the scrutinee of the induction to occur beneath a modality. Crisp induction principles are derivable in MTT if the modality has an internal right adjoint [GKNB21], but they are justified in other situations. In particular, crisp induction for identity types is validated if and only if modal extensionality holds. In contrast to modal extensionality, however, it is straightforward to directly adapt the proofs of normalization and canonicity to account for crisp identity induction principles:

$$\begin{array}{l} \Gamma.(\mu \mid A).(\mu \mid A[\uparrow]).(\mu \mid \mathsf{Id}_{A[\uparrow^2]}(\mathbf{v}_1, \mathbf{v}_0)) \vdash B @ m \\ \Gamma.(\mu \mid A) \vdash M : B[\uparrow.\mathbf{v}_0.\mathbf{v}_0.\mathsf{refl}(\mathbf{v}_0)] @ m \\ \Gamma.\{\mu\} \vdash N_0, N_1 : A @ n \quad \Gamma.\{\mu\} \vdash P : \mathsf{Id}_A(N_0, N_1) @ n \\ \hline \Gamma \vdash \mathsf{J}^\mu(B, M, P) : B[\mathsf{id}.N_0.N_1.P] @ m \end{array}$$

$$\mathsf{J}^\mu(B, M, \mathsf{refl}(N)) = M[\mathsf{id}.N]$$

The modularity of our proof of normalization ensures that only local changes to the construction of identity types in $\mathcal{G}$ are needed to adapt the entire proof to support crisp induction. Concretely, two changes to primitive constants added to MSTC by Section 5.1. One alteration to the definition of cosmoi and one to the definition of neutral forms:

$$\begin{array}{l} \mathsf{J}_\mu : (\mu \mid A : \mathsf{Ty}_n)(B : (\mu \mid a_0, a_1 : \mathsf{Tm}_n(A))(\mu \mid p : \mathsf{Tm}_n(\mathsf{Id}(A, a_0, a_1))) \rightarrow \mathsf{Ty}_m) \\ \rightarrow ((\mu \mid a : \mathsf{Tm}_n(A)) \rightarrow \mathsf{Tm}_m(B(a, a, \mathsf{refl}(a)))) \\ \rightarrow (\mu \mid a_0, a_1 : \mathsf{Tm}_n(A))(\mu \mid p : \mathsf{Tm}_n(\mathsf{Id}(A, a_0, a_1))) \\ \rightarrow \mathsf{Tm}_m(B(a_0, a_1, p)) \\ \mathsf{J}_\mu : (\mu \mid A : \bigcirc \mathsf{Ty}_n)(B : (\mu \mid a_0, a_1 : \mathsf{V}_n(A))(\mu \mid p : \mathsf{V}_m(\mathsf{Id}(A, a_0, a_1))) \rightarrow \mathsf{NfTy}_m) \\ \rightarrow ((\mu \mid a : \mathsf{V}_n(A)) \rightarrow \mathsf{Nf}_m(B(a, a, \mathsf{refl}(a)))) \\ \rightarrow (\mu \mid a_0, a_1 : \bigcirc_z \mathsf{Tm}_n(z, A(z)))(\mu \mid p : \mathsf{Ne}_n(\mathsf{Id}(A, a_0, a_1))) \\ \rightarrow \mathsf{Ne}_m(B(a_0, a_1, \eta(p))) \end{array}$$

These changes simply reflect the change to the elimination principle of the identity type.

After having made this change, only one portion of Section 5.2 must change: Lemma 5.10 which shows that the gluing cosmos is closed under identity types. We must show that $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ is closed under crisp induction.

⁷Like function extensionality, it is straightforward to maintain either normalization or canonicity in the presence of modal extensionality. Ensuring for both simultaneously is far more difficult.