11:56

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

**10.4. Internal transposition.** The previous section offers a perfectly good internal representation of an external adjunction. However, it is usually much more economical to present an adjunction by a natural isomorphism

$$\operatorname{Hom}(L(A), B) \cong \operatorname{Hom}(A, R(B))$$

Unfortunately, this is not achievable in MTT for a multitude of reasons. First, notice that $\langle \nu \mid A \rangle \rightarrow B \oplus n$ and $A \rightarrow \langle \mu \mid B \rangle \oplus m$ are types in different modes, so the putative type $(\langle \nu \mid A \rangle \rightarrow B) \simeq (A \rightarrow \langle \mu \mid B \rangle)$ that would represent the isomorphism is ill-typed.

Second, even if the two modes coincide—so that $\nu, \mu$ are endomodalities—the aforementioned type is a bit too strong for our purpose: it is inhabited by *internal equivalences*, which are stronger than bijections of hom-sets. Such equivalences correspond to isomorphisms $B^{L(A)} \cong R(B)^A$ of exponential objects. In turn, these are equivalent to hom-set bijections only if the involved functors are *internal*, which is to say that we have functions

$$(A \rightarrow B) \rightarrow (\langle \nu \mid A \rangle \rightarrow \langle \nu \mid B \rangle) \quad (A \rightarrow B) \rightarrow (\langle \mu \mid A \rangle \rightarrow \langle \mu \mid B \rangle)$$

that compute the action of the modality $\langle \mu \mid - \rangle$ on morphisms *within* MTT.$^{10}$

Third, even if we could internalize our modalities, we would be flying too close to the sun. As we have $(1 \rightarrow A) \simeq A$ for any $A$ and $\langle \xi \mid 1 \rangle \simeq 1$ for any $\xi$, we may calculate that

$$A \simeq 1 \rightarrow A \simeq \langle \nu \mid 1 \rangle \rightarrow A \simeq 1 \rightarrow \langle \mu \mid A \rangle \simeq \langle \mu \mid A \rangle$$

Hence, $\langle \mu \mid - \rangle$ must be the identity functor up to equivalence. This short argument, which is due to [LOPS18, Theorem 5.1], is a *no-go theorem* that obstructs the internalization of an adjunction whose left adjoint preserves terminal objects.

[LOPS18] overcame this barrier by introducing the *global sections modality* $\flat$. Terms of $\flat A$ represent *global* elements of $A$: terms of $\flat (A \rightarrow B)$ are in bijection with morphisms in $\operatorname{Hom}(A, B)$. Thus, the previously problematic equivalence holds under $\flat$.

We can rephrase this argument in our syntax. The key thing to notice is that the functor $\flat : \mathbf{PSh}(\mathcal{C}) \rightarrow \mathbf{PSh}(\mathcal{C})$ which maps a presheaf to the constant presheaf $\_ \mapsto \operatorname{Hom}_{\mathbf{PSh}(\mathcal{C})}(1, P)$ of global sections is initial amongst functors that preserve the terminal object. Thus, we postulate an initial modality: suppose that $n = m$, and that $\operatorname{Hom}(m, m)$ is equipped with an initial object, i.e. a 1-cell $\flat : m \rightarrow m$ and a unique 2-cell $! : \flat \Rightarrow \xi$ for all $\xi$. As a consequence, we are able to use variables $x : (\flat \mid A)$ in any context. Assuming function extensionality, we have that

**Theorem 10.3.** *There is an equivalence $\langle \flat \mid \langle \nu \mid A! \rangle \rightarrow B \rangle \simeq \langle \flat \mid A \rightarrow \langle \mu \mid B! \rangle \rangle$.*

*Proof.* The equivalence is given by the functions

$$\begin{aligned} F & : \langle \flat \mid \langle \nu \mid A! \rangle \rightarrow B \rangle \rightarrow \langle \flat \mid A \rightarrow \langle \mu \mid B! \rangle \rangle \\ F(f) & \triangleq \operatorname{let} \operatorname{mod}_{\flat}(g) \leftarrow f \text{ in } \operatorname{mod}_{\flat}(\lambda x. \operatorname{mod}_{\mu}(g!) \circledast_{\mu} \operatorname{unit}(x)) \\ G & : \langle \flat \mid A \rightarrow \langle \mu \mid B! \rangle \rightarrow \langle \nu \mid A \rangle \rightarrow \langle \flat \mid \langle \nu \mid A! \rangle \rightarrow B \rangle \\ G(g) & \triangleq \operatorname{let} \operatorname{mod}_{\flat}(f) \leftarrow g \text{ in } \operatorname{mod}_{\flat}(\lambda x. \operatorname{counit}(\operatorname{mod}_{\nu}(f!) \circledast_{\nu} x)) \end{aligned}$$

These are well-typed because, by initiality of $\flat$, $A^\eta = (A!)^\eta = A!$, $(B!)^\epsilon = B!$. By function extensionality and $\eta$ for modalities, they are mutually inverse. $\square$

$^{10}$Such functors are usually called *enriched* (recall that cartesian closure is a self-enrichment).