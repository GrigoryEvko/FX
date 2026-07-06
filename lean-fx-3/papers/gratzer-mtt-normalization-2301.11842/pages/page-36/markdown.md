27:36

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

In light of Corollary 6.6, to decide the equality of terms and types, it suffices to argue that one may decide the equality of neutral and normal forms along with normal types. For this purpose, we adapt the bidirectional algorithm given by Altenkirch and Kaposi [AK17]. This argument goes through essentially without alteration, except that since certain constructors are annotated with 1- and 2-cells from $\mathcal{M}$, we require a decision procedure for objects in the mode theory. Note that this procedure uses e.g., Corollary 6.9, which is why we have delayed its statement till now.

**Corollary 6.10.** *If $\mathcal{M}$ is decidable, type checking is decidable.*

Finally, Gratzer et al. [GKNB20a] show canonicity for MTT extended with the equality $\mathbf{1}.\{\mu\} = \mathbf{1}$. Normalization provides a (heavy-handed) proof of canonicity without this equation by scrutinizing the definition of normal forms:

**Corollary 6.11.** *If $\mathbf{1}.\{\mu\} \vdash M : \mathsf{bool} \circledast m$ then $M \in \{\mathsf{tt}, \mathsf{ff}\}$.*

## 7. EXTENDING MTT WITH CRISP IDENTITY INDUCTION

To demonstrate the flexibility of the normalization argument given in Sections 5 and 6, we now show how it may be extended to accommodate modal principles not included in MTT.

Recall that, intuitively, a modality in MTT corresponds to a right adjoint. This intuition is supported by the fact that MTT modalities commute with products. In an extensional version of MTT, modalities also commute with (extensional) equality. That is, the following canonical map is an equivalence:

$$(\mu \mid x, y : A) \rightarrow \mathsf{Id}_{\langle \mu | A \rangle}(\mathsf{mod}_\mu(x), \mathsf{mod}_\mu(y)) \rightarrow \langle \mu \mid \mathsf{Id}_A(x, y) \rangle \quad (7.1)$$

**Remark 7.1.** Constructing this map is slightly intricate. We begin by generalizing:

$$(x, y : \langle \mu \mid A \rangle) \rightarrow \mathsf{Id}_{\langle \mu | A \rangle}(x, y) \rightarrow \mathsf{let}_\nu \mathsf{mod}_\mu(x') \leftarrow x \text{ in } \mathsf{let}_\nu \mathsf{mod}_\mu(y') \leftarrow y \text{ in } \langle \mu \mid \mathsf{Id}_A(x', y') \rangle$$

In this form, we may use ordinary identity induction followed by modal induction to reduce to $(x : \langle \mu \mid A \rangle) \rightarrow \mathsf{let}_\nu \mathsf{mod}_\mu(x') \leftarrow x \text{ in } \mathsf{let}_\nu \mathsf{mod}_\mu(y') \leftarrow x \text{ in } \langle \mu \mid \mathsf{Id}_A(x', y') \rangle$ and then $(\mu \mid x : A) \rightarrow \langle \mu \mid \mathsf{Id}_A(x, x) \rangle$ respectively.

In *intensional* MTT, the same principle is not derivable.

**Theorem 7.2.** *There exists a model of intensional MTT with one mode $m$ and one modality $\mu : m \rightarrow m$ in which Equation 7.1 is not invertible.*

*Proof.* Consider intensional MTT and define an interpretation of MTT into intensional MLTT which interprets both modes as MLTT and sends all non-modal types to their counterparts within MLTT and interprets modal connectives as follows:

$$\begin{aligned} &\llbracket \Gamma.\{\mu\}\rrbracket = \llbracket \Gamma \rrbracket.\mathsf{Nat} \\ &\llbracket \Gamma.(\mu \mid A)\rrbracket = \llbracket \Gamma \rrbracket.\left(\mathsf{Nat} \rightarrow \llbracket A \rrbracket\right) \\ &\llbracket \Gamma.\{\mathsf{id}\}\rrbracket = \llbracket \Gamma \rrbracket \\ &\llbracket \Gamma.(\mathsf{id} \mid A)\rrbracket = \llbracket \Gamma \rrbracket.\llbracket A \rrbracket \\ &\llbracket \langle \mu \mid A \rangle \rrbracket = \mathsf{Nat} \rightarrow \llbracket A \rrbracket \\ &\llbracket \langle \mathsf{id} \mid A \rangle \rrbracket = \llbracket A \rrbracket \\ &\llbracket \mathsf{mod}_\mu(M)\rrbracket = \lambda(\llbracket M \rrbracket) \end{aligned}$$