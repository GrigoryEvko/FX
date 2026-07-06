Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:43

Preservation of context extension. We would like to show that the canonical morphism

$$\mu_{*}(\Gamma.A) \xrightarrow{\langle\mu_{*}\mathbf{p},\mu_{*}\mathbf{q}\rangle} \mu_{*}\Gamma.\mu_{*}A$$

is invertible. Consider an element $e : \mathbf{y}(D) \Rightarrow \mu_{*}(\Gamma.A)$. We can transpose along the adjunction $\mu^{*} \dashv \mu_{*}$ and decompose it to obtain a substitution and a term

$$e_{0} : \mu^{*}\mathbf{y}(D) \Rightarrow \Gamma \qquad e_{1} : \operatorname{Hom}_{\mathbf{PSh}(\int \mu^{*}\mathbf{y}(D))}(1, A[e_{0}])$$

We can thus write $e = \langle\widehat{e_{0},e_{1}}\rangle$. Thus, we can use naturality of the adjunction and of substitution to compute the action of $\langle\mu_{*}\mathbf{p},\mu_{*}\mathbf{q}\rangle$ on this $e$:

$$\langle\mu_{*}\mathbf{p},\mu_{*}\mathbf{q}\rangle \circ e = \langle\mu_{*}\mathbf{p} \circ e, (\mu_{*}\mathbf{q})[e]\rangle = \langle\widehat{\mathbf{p} \circ \langle e_{0},e_{1}\rangle}, \mathbf{q}[\langle e_{0},e_{1}\rangle]\rangle = \langle\widehat{e}_{0},e_{1}\rangle$$

We can then specify an inverse on generalized elements by $\langle\gamma,M\rangle \mapsto \langle\widehat{\gamma},M\rangle$.

Size preservation is immediate: if $A$ is small then so are its reindexings and the collections of points at each slice.

8.1. The other adjunction. We have so far concentrated on the adjunction $\mu^{*} \dashv \mu_{*}$ that arises through right Kan extension. Nevertheless, precomposition also has a left adjoint $\mu_{!}$ arising from left Kan extension. Might we also be able to interpret the lock functors by this left adjoint $\mu_{!}$, and lift precomposition $\mu^{*}$ to a modality instead?

It is in fact relatively easy to show that $\mu^{*}$ extends to a dependent right adjoint. However, the left Kan extensions $\mu_{!}$ cannot be assembled into a modal context structure. The reason is that context structures are strict 2-functors, but left Kan extensions do not compose strictly: we only have an isomorphism $F_{!} \circ G_{!} \cong (G \circ F)_{!}$. We have proven a strictification theorem that straightens these issues, but that is beyond the scope of this paper.

### 9. GUARDED RECURSION

We now show how MTT can be applied to a well-known modal situation: guarded recursion. By instantiating MTT with a carefully chosen mode theory and axiomitizing certain operations specific to guarded recursion (i.e. Löb induction), we obtain a calculus for guarded recursion simpler than prior hand-crafted calculi. We demonstrate the practicality of this guarded variant of MTT by reproducing some examples from prior work on guarded recursion [BGC$^{+}$16].

The key idea of guarded recursion [Nak00] is to use a modality $\blacktriangleright$, usually called later, to mark the types of data that may be used only if some 'computational progress' (e.g. a tick of a clock) has taken place, thereby enforcing productivity at the level of types. The later modality is usually equipped with three basic operations:

$$\text{next} : A \to \blacktriangleright A \qquad (\circledast) : \blacktriangleright (A \to B) \to \blacktriangleright A \to \blacktriangleright B \qquad \text{löb} : (\blacktriangleright A \to A) \to A$$

The first two make $\blacktriangleright$ into an applicative functor [MP08]. The third, which is commonly known as Löb induction, is a guarded fixed point operator [ML13]: it enables us to make definitions by provably productive recursion.

$\blacktriangleright$ also applies to the universe, so one can define data types by guarded recursion. The classic example is the guarded stream type $\operatorname{Str}_{A} \cong A \times \blacktriangleright \operatorname{Str}_{A}$, with constructor

$$\operatorname{cons}_{A} : A \times \blacktriangleright \operatorname{Str}_{A} \cong \operatorname{Str}_{A}$$