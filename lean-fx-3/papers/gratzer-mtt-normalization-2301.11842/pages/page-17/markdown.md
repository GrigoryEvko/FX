Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:17

model [KKA19]—and the latter takes the place of rule induction in the proof of normalization (see Theorem 6.4).

Proof. We write $\mathbf{El}_m$, $\mathbf{Ty}_m$ and $\mathbf{Tm}_m$ instead of $\tau_m$, $\mathcal{T}_m$, and $\mathcal{T}_m^\bullet$ in the syntactic model, reserving the latter exclusively for $G$. We write $[\![\mu]\!]$ for the functor sending $\Gamma$ to $\Gamma.\{\mu\}$. We begin by replacing $G$ by an equivalent strict 2-functor so that $\pi$ becomes strictly 2-natural.

We construct a displayed model of MTT [KKA19] which lies over the syntactic model. Using the existing coherence result for MTT [GKNB20b], we only ensure that $\Gamma.\{\mu\}.\{\nu\}$ and $\Gamma.\{\mu \circ \nu\}$ agree up to pseudonatural isomorphism.

- A context in $m$ is a triple $X: G(m)$, $\Gamma \circ \circ \circ m$, and $\alpha: \pi(X) \cong \mathbf{y}(\Gamma)$.
- A type in a context $(X, \Gamma, \alpha)$ is a pair of $\bar{A}: X \longrightarrow \mathcal{T}_m$ and $\Gamma \vdash A \circledcirc m$ such that $\pi(\bar{A}) = \lfloor A \rfloor \circ \alpha$.
- A term in a context $(X, \Gamma, \alpha)$ of type $(\bar{A}, A)$ is a pair $\bar{M}: X \longrightarrow \tau_m[\bar{A}]$ and $\Gamma \vdash M: A \circledcirc m$ such that $\pi(\bar{M}) = \lfloor M \rfloor \circ \alpha$.
- A substitution $(X, \Gamma, \alpha) \longrightarrow (Y, \Delta, \beta)$ is a pair $f: X \longrightarrow Y$ and $\Gamma \vdash \delta: \Delta \circledcirc m$ satisfying $\beta \circ \pi(f) = \mathbf{y}(\delta) \circ \alpha$

Once this model is constructed, the result follows from Theorem 3.4. The construction of contexts, substitutions, terms, and types is straightforward as $\pi$ is a 2-natural transformation which preserves finite limits, and commutes with all connectives. We show two cases.

The action of a modality on a context. Given a triple $(X, \Gamma, \alpha)$ at mode $m$ and a modality $\mu: n \longrightarrow m$, we define the 'locked' context to be the following:

$$(G(\mu)_!(X), \Gamma.\{\mu\}, \gamma \circ [\![\mu]\!]_! \alpha \circ \beta)$$

Here $\beta: \pi(G(\mu)_!X) \cong [\![\mu]\!]_! \pi(X)$ and $\gamma: [\![\mu]\!]_! \mathbf{y}(\Gamma) \cong \mathbf{y}(\Gamma.\{\mu\})$ are the canonical isomorphisms.

Modal types. Suppose we are given a context $(X, \Gamma, \alpha)$ and a type $(\bar{A}, A)$ in the context $(G(\mu)_!(\mu)(X), \Gamma.\{\mu\}, \gamma \circ [\![\mu]\!]^*(\alpha) \circ \beta_\mu)$. Writing $\bar{B}$ for the transpose of $\bar{A}$, we form the modal type as

$$(\mathbf{Mod}_\mu(\bar{B}), \langle \mu \mid A \rangle)$$

It remains to check that these types are coherent i.e.:

$$\pi(\mathbf{Mod}_\mu(\bar{B})) = \lfloor \langle \mu \mid A \rangle \rfloor \circ \alpha$$

By assumption, $\pi(\bar{B}) = \lfloor A \rfloor \circ \gamma \circ [\![\mu]\!]^*(\alpha) \circ \beta$. By our assumption that $\pi$ satisfies Beck-Chevalley $\pi(\bar{B}) = \widehat{\lfloor A \rfloor \circ \gamma} \circ \alpha$. The result follows from the fact that $\pi$ preserves $\mathbf{Mod}_\mu$. $\square$

3.3. Presheaf cosmoi. Example 3.6 shows that each model of MTT induces an MTT cosmos. In fact, such cosmoi are particularly well-behaved as they are comprised of presheaf topoi connected by adjoint triples. These cosmoi enjoy a privileged role in our proof and we observe some of their unique behavior.

Definition 3.12. A presheaf cosmos $F$ is a cosmos where $F$ is a strict 2-functor, each $F(m)$ is a presheaf topos, and each right adjoint $F(\mu)$ sends small families to small families.

What distinguishes presheaf cosmoi from other cosmoi is the rich internal language they offer. Gratzer et al. [GKNB21] have proven that such a cosmos $F$ supports a model of extensional MTT with the same mode theory where $\langle \mu \mid - \rangle$ is interpreted by $F(\mu)$. We will now use extensional MTT as a multimodal metalanguage to specify the structure of