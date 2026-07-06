11:10

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

**Definitional equality in MTT.** A perennial problem in type theory is that of deciding where the boundary between those equalities that are *provable* in the system (e.g. using various forms of induction), and those that are *definitional*, i.e. hold by fiat. While we have simply followed standard practices in the MLTT connectives at each mode, the situation is somewhat more complicated regarding modal types. On the one hand, we have the expected $\beta$-rule TM/MODAL-BETA: see Figure 2. On the other hand, we do not include any definitional $\eta$-rules: as the eliminator is a *positive* pattern-matching construct, the proper $\eta$-rule would need *commuting conversions*, which would enormously complicate the metatheory.

**Notational conventions.** In the rest of the paper we shall make use of the following notational conventions.

**Notation 2.1.** When opening a modal term under the modality 1 we will suppress the 1 in the $\text{let}_1$ part of the term, and write $\text{let } \text{mod}_\mu(\_) \leftarrow M$ in $N$ instead.

**Notation 2.2.** As remarked before, Coquand-style universes do not require the introduction of codes that represent various types in the universe, for they are definable. Nevertheless, in examples we will often suppress both $\text{El}(-)$ and $\text{Code}(-)$, and in some straightforward cases even elide the coercion $\upharpoonright-$. This not only makes our terms more perspicuous, but can also be formally justified by an *elaboration procedure* which inserts the missing isomorphisms and coercions when needed.

### 3. PROGRAMMING WITH MODALITIES

In this section we show how MTT can be used to program and reason with modalities. We identify a handful of basic modal combinators which demonstrate the behaviour of our modal types. Then, in Section 3.2 we use them to present a type theory featuring an idempotent comonad with almost no additional effort.

**3.1. Modal Combinators.** We first show how each 2-cell $\alpha : \mu \Rightarrow \nu$ with $\mu, \nu : n \rightarrow m$ induces a natural transformation $\langle \mu \mid - \rangle \rightarrow \langle \nu \mid - \rangle$. We call the components of this natural transformation *coercions*. Given $\Gamma, \text{id}_\mu \vdash A \text{ type}_1 @ m$, define

$$\begin{aligned} \text{coe}\alpha : \mu \Rightarrow \nu : & \langle \mu \mid A \rangle \rightarrow \langle \nu \mid A^\alpha \rangle \\ \text{coe}\alpha : \mu \Rightarrow \nu \triangleq & \text{let } \text{mod}_\mu(z) \leftarrow x \text{ in } \text{mod}_\nu(z^\alpha) \end{aligned}$$

The heart of this combinator is a use of the rule TM/VAR. This operation completes the correspondence sketched in Section 1: objects of $\mathcal{M}$ correspond to modes, morphisms to modalities, and 2-cells to coercions.

Additionally, the assignment $\mu \mapsto \langle \mu \mid - \rangle$ is *functorial*. Unlike the action of locks, this functoriality is not definitional, but only a type-theoretic *equivalence* [Uni13, §4]. Fixing $\nu : o \rightarrow n$, $\mu : n \rightarrow m$, and $\Gamma, \text{id}_{\mu \circ \nu} \vdash A \text{ type}_1 @ m$, we let

$$\begin{aligned} \text{comp}_{\mu, \nu} : & \langle \mu \mid \langle \nu \mid A \rangle \rangle \rightarrow \langle \mu \circ \nu \mid A \rangle \\ \text{comp}_{\mu, \nu}(x) & \triangleq \text{let } \text{mod}_\mu(x_0) \leftarrow x \text{ in} \\ & \quad \text{let}_\mu \text{ mod}_\nu(x_1) \leftarrow x_0 \text{ in} \\ & \quad \text{mod}_{\mu \circ \nu}(x_1) \end{aligned}$$