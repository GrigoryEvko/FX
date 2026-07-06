Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:11

$$\overline{\Gamma \vdash ! : \mathbf{1} @ m \quad |!| = !} \quad \overline{\Gamma.(\mu \mid A) \vdash \uparrow : \Gamma @ m \quad |\uparrow| = \uparrow} \quad \overline{\Gamma \vdash \mathsf{id} : \Gamma @ m \quad |\mathsf{id}| = \mathsf{id}}$$

$$\frac{\Gamma_0 \vdash r : \Gamma_1 @ m \quad \Gamma_1 \vdash s : \Gamma_2 @ m}{\Gamma_0 \vdash s \circ r : \Gamma_2 @ m \quad |s \circ r| = |s| \circ |r|} \quad \frac{\Gamma \vdash r : \Delta @ m}{\Gamma.\{\mu\} \vdash r.\{\mu\} : \Delta.\{\mu\} @ n \quad |r.\{\mu\}| = |r|.\{\mu\}}$$

$$\frac{\mu, \nu : n \longrightarrow m \quad \alpha : \nu \longrightarrow \mu}{\Gamma.\{\mu\} \vdash \{\alpha\}_\Gamma : \Gamma.\{\nu\} @ n \quad |\{\alpha\}_\Gamma| = \{\alpha\}_\Gamma}$$

$$\frac{\Gamma \vdash r : \Delta @ m \quad \Gamma.\{\mu\} \vdash^\mathrm{re} \mathbf{v}_k^\alpha : A[|r|.\{\mu\}] @ n}{\Gamma \vdash r.\mathbf{v}_k^\alpha : \Delta.(\mu \mid A) @ m \quad |r.\mathbf{v}_k^\alpha| = |r|.\mathbf{v}_k^\alpha|}$$

Figure 2: Complete definition of renamings

**Renamings.** While normal and neutral forms are not stable under substitution, they are stable under the restricted class of *renamings*. The formal definition of renamings is presented in Figure 2. Intuitively, they are the smallest class of substitutions closed under weakening, composition, identity, modal substitutions $(-.\{\mu\},\{\alpha\})$, and extension by variables $\mathbf{v}_k^\alpha$.

Renamings are easily seen to act on normal forms, neutral forms, and normal types. Unlike normals and neutrals, however, renamings are taken up to a definitional equality which ensures that e.g., composition is associative and that modal substitutions organize into a 2-functor. This poses no issue as the action of renamings on normals and neutrals send definitionally equal renamings to identical normals and neutrals, ensuring that the action lifts to equivalences classes.

A nontrivial definitional equality on renamings is essential, however, as it ensures that the class of contexts of mode $m$ and renamings between them organizes into a category $\mathsf{Ren}_m$ and that the assignments $m \mapsto \mathsf{Ren}_m$, $\mu \mapsto -.\{\mu\}$, and $\alpha \mapsto \{\alpha\}$ define a 2-functor $\mathcal{M}^{\mathrm{coop}} \longrightarrow \mathbf{Cat}$.

**Lemma 2.3.** *The decoding of renamings to substitutions gives a 2-natural transformation $\mathbf{i}[-] : \mathsf{Ren}_- \longrightarrow \mathsf{Cx}_-$.*

### 3. MODELS AND COSMOI

Gratzer et al. [GKNB21] introduced MTT as a generalized algebraic theory so that MTT is automatically equipped with a category of models. A standard result of GATs ensures that the syntax of MTT organizes into an initial model which opens the possibility of semantic methods for proving results about syntax. Gratzer et al. [GKNB21] then repackages the definition of models in the language of natural models [Awo18].

**3.1. Natural models of MTT.** We begin by recalling the presentation of a model of MTT given by Gratzer et al. [GKNB21]. Recall that a natural model of type theory [Awo18] is a pair of a category $\mathcal{C}$—representing a category of contexts—together with a representable natural transformation $\tau : \mathcal{T}^\bullet \longrightarrow \mathcal{T}$:

**Definition 3.1.** A natural transformation $f : X \longrightarrow Y : \mathbf{PSh}(\mathcal{C})$ is *representable* when each fiber of $f$ over a representable point of $Y$ is itself representable i.e., $\mathbf{y}(C) \times_Y X$ is representable for each $\mathbf{y}(C) \longrightarrow Y$.