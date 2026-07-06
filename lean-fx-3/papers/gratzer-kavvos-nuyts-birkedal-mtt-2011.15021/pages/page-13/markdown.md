Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:13

While this approach is straightforward and uncluttered, some readers might object to the lack of a more traditional formulation, e.g. a named syntax with variables and a metatheoretic substitution operation, like the one we informally presented in Section 2. We believe that it is indeed possible to define such a syntax and systematically show how to elaborate its terms to the algebraic syntax.

However, such a named syntax would not be directly suitable for implementation: for that purpose we ought to develop an entirely different algorithmic syntax. We believe that such a syntax can be constructed as an extension of existing bidirectional presentations of type theory [Coq96, PT00] as has been done for existing modal calculi [GSB19a]. Such a bidirectional presentation would occupy a midpoint between the maximally annotated algebraic syntax we present here, and the more typical named syntax of Section 2: it would contain only a select few annotations to ensure the decidability of typechecking, yet maintain readability. The development of such a syntax is a substantial undertaking that requires a proof of normalization, and is orthogonal to the foundational metatheoretic results that we seek to develop here. We thus refrain from developing it, and instead work directly with the GAT.

4.1. Sorts. We begin by defining the different sorts (contexts, types, terms, etc.) that constitute our type theory. In order to support multiple modes, our sorts will be parameterized in modes. Thus, rather than having a single sort of types, we will have a sort of types at mode $m \in \mathcal{M}$, and likewise for contexts at mode $m$, terms at mode $m$, etc.

Moreover, we take care to index our types by levels. The reason for doing so was discussed in Section 2.1: we seek to introduce a hierarchy of sizes, which we can then use to introduce universes à la [Coq13]. We stratify our types in two levels, drawn from the set $\mathcal{L} = \{0, 1\}$. There are no technical obstacles on the way to a richer hierarchy, but two levels suffice for our purposes: we aim to divide our types into small types (i.e. those that can be refied in a universe) and large types (which also include the universe itself). In order to enforce cumulativity we will also include an explicit coercion operator, which includes small types into large types.

The levelled approach raises an obvious question: on which level should we admit terms? We could follow the approach of [Ste19] in allowing terms at both, but this requires the introduction of term-level coercions, which then require equations relating term formers at different levels. Thus, for the sake of simplicity we will only allow the formation of terms at large types. Similarly, we will only allow the extension of a context by a large type.

MTT has four families of sorts, which are introduced by the following rules:

$$\frac{m : \mathcal{M}}{\text{ctx}_m \text{ sort}} \quad \frac{\ell : \mathcal{L} \quad m : \mathcal{M} \quad \Gamma : \text{ctx}_m}{\text{type}_m^\ell(\Gamma) \text{ sort}} \quad \frac{m : \mathcal{M} \quad \Gamma : \text{ctx}_m \quad A : \text{type}_m^\dagger(\Gamma)}{\text{tm}_m(\Gamma, A) \text{ sort}}$$
$$\frac{m : \mathcal{M} \quad \Gamma, \Delta : \text{ctx}_m}{\text{sb}_m(\Gamma, \Delta) \text{ sort}}$$

In the interest of clarity we will use the following shorthands:

$$\begin{array}{l} \Gamma \text{ ctx @ } m \triangleq \Gamma : \text{ctx}_m \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Gamma \vdash A \text{ type}_\ell @ m \triangleq A : \text{type}_m^\ell(\Gamma) \\ \Gamma \vdash M : A @ m \triangleq M : \text{tm}_m(\Gamma, A) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Gamma \vdash \delta : \Delta @ m \triangleq \delta : \text{sb}_m(\Gamma, \Delta) \end{array}$$