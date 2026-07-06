Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:25

Following Hofmann [Hof99], the constructors for normal forms, neutrals, and normal types can be realized in $\mathbf{PSh}(\mathsf{Ren}_{-})$ by a form of higher-order abstract syntax. As $\mathsf{Nf}_m(A)$, $\mathsf{Ne}_m(A)$, and $\mathsf{NfTy}_m$ lie over $\mathsf{Tm}_m(A)$ and $\mathsf{Ty}_m$, one can extend this higher-order abstract syntax presentation to $\mathcal{G}$ and realize each normal form, neutral, and normal type as a constant of $\mathsf{Nf}_m(A)$, $\mathsf{Ne}_m(A)$, or $\mathsf{NfTy}_m$ which collapses to the appropriate syntactic constant under $z : \mathbf{syn}$. As a simple example, the normal form type for booleans along with the ordinary boolean type former induce maps $\mathsf{bool} : \mathbf{1} \longrightarrow \pi_1(\mathsf{NfTy}_m)$ and $\mathsf{bool} : \mathbf{1} \longrightarrow \mathsf{Ty}_m$ in $\mathbf{PSh}(\mathsf{Ren}_m)$ and $\mathbf{PSh}(\mathsf{Cx}_m)$ respectively. These maps pair together to introduce a morphism $[\![\mathsf{Bool}\!] : \mathbf{1} \longrightarrow [\![\mathsf{NfTy}_m]\!]$ in $\mathcal{G}(m)$ where we rely on the equation $|\mathsf{bool}| = \mathsf{bool}$ to ensure that these morphisms fit into the commutative square required by $\mathcal{G}(m)$. The full collection of constants is specified in Figure 5.

**Extension 3.** *There are constants internalizing normals, neutrals, and normal types.*

Finally, inspecting Definition 5.1 reveals that modalities are interpreted by functors which are both left and right adjoints as they preserve all (co)limits. As a result, modalities preserve coproducts:

**Extension 4.** $\langle \mu \mid A + B \rangle \cong \langle \mu \mid A \rangle + \langle \mu \mid B \rangle$

**5.2. The MTT cosmos.** We now extend $\mathcal{G}$ to an MTT cosmos. To ensure that $\pi_0$ induces a morphism of MTT cosmoi, it suffices to ensure that each constant we add to $\mathcal{G}$ is equal to the corresponding piece of $\mathcal{S}$ as internalized by Extension 1 under $z : \mathbf{syn}$.

**The universe of computable types and terms.** We begin with the definition of types and terms in this cosmos. Concretely, we require the following for each $m : \mathcal{M}$:

$$\begin{array}{l} \mathsf{Ty}_m^* : \{\mathsf{U}_2 \mid z : \mathbf{syn} \mapsto \mathsf{Ty}_m(z)\} \\ \mathsf{Tm}_m^* : (A : \mathsf{Ty}_m^*) \to \{\mathsf{U}_1 \mid z : \mathbf{syn} \mapsto \mathsf{Tm}_m(z, A)\} \end{array}$$

We start with the following putative definition of types:

$$\begin{array}{l} \text{record } T : \mathsf{U}_2 \text{ where} \\ \text{code} : \mathsf{NfTy}_m \\ \text{pred} : \{\mathsf{U}_1 \mid z : \mathbf{syn} \mapsto \mathsf{Tm}_m(z, \text{code})\} \\ \text{reflect} : \{\mathsf{Ne}_m(\text{code}) \to \text{pred} \mid \mathbf{syn} \mapsto \text{id}\} \\ \text{reify} : \{\text{pred} \to \mathsf{Nf}_m(\text{code}) \mid \mathbf{syn} \mapsto \text{id}\} \end{array} \tag{5.1}$$

In prose, $A : T$ contains the code of a normal type $A.\text{code}$ as well as a proof-relevant predicate on the elements of $A.\text{code}$.

The last two fields ensure that (1) all elements tracked by this predicate can be assigned normal forms, and (2) all neutrals lie within the predicate. We write $\downarrow_A$ and $\uparrow_A$ for $A.\text{reify}$ and $A.\text{reflect}$. Of the two, the reify is the crucial operation needed for the normalization algorithm: it ensures that computable elements can be given normal forms. Tait [Tai67], however, has shown that the pair of operations is necessary to close all type formers under just reify.

We cannot simply define $\mathsf{Ty}_m^* = T$, as $T$ does not satisfy the equation $z : \mathbf{syn} \vdash T = \mathsf{Ty}_m(z)$. It does, however, satisfy this condition up to isomorphism: under $z : \mathbf{syn}$, the types