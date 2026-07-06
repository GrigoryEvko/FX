Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:25

then provides a section $j$ of $E[-]$ defined on all of $I$. This section is above $C$, and extends $c$. Note that these fillers are not necessarily unique. Moreover, they are automatically *natural*: as all the types involved in this definition are closed, we are at liberty to weaken the context.

This style of lifting structure is an essential ingredient in recent work on models of intensional identity types. First, they play an important rôle in natural models: [Awo18, Lemma 19] shows that they precisely correspond to enriched left lifting properties in the sense of categorical homotopy theory [Rie14, §13]. In fact, the above definition given above is a word-for-word restatement in the internal language. Second, such lifting structures are also central devices in internal presentations of models of cubical type theory, in particular the recent work of [OP18].

We can now approach this in a manner similar to intensional identity types in *op. cit.* Recall that the elimination rule for $\langle \nu \mid A \rangle$ is

$$\begin{array}{c} \nu : \mathrm{Hom}_{\mathcal{M}}(o, n) \\ \mu : \mathrm{Hom}_{\mathcal{M}}(n, m) \qquad \Gamma \mathsf{ctx} \circledast m \qquad \Gamma \widehat{\bullet}_{\mu} \widehat{\bullet}_{\nu} \vdash A \mathsf{type}_1 \circledast o \qquad \Gamma \widehat{\bullet}_{\mu} \vdash M_0 : \langle \nu \mid A \rangle \circledast n \\ \Gamma.(\mu \mid \langle \nu \mid A \rangle) \vdash B \mathsf{type}_1 \circledast m \qquad \Gamma.(\mu \circ \nu \mid A) \vdash M_1 : B[\uparrow. \mathsf{mod}_{\nu}(\mathbf{v}_0)] \circledast m \\ \hline \Gamma \vdash \mathsf{let}_{\mu} \mathsf{mod}_{\nu}(\_) \leftarrow M_0 \text{ in } M_1 : B[\mathsf{id}.M_0] \circledast m \end{array}$$

First, we must remove the 'implicit cut' with $M_0$. We construct the substitution

$$\Gamma.(\mu \mid \langle \nu \mid A \rangle).(\mu \circ \nu \mid A[\uparrow. \widehat{\bullet}_{\mu \circ \nu}]) \vdash \sigma \triangleq \uparrow^2. \mathbf{v}_0 : \Gamma.(\mu \circ \nu \mid A) \circledast m$$

It then suffices to construct the elimination rule

$$\begin{array}{c} \nu : \mathrm{Hom}_{\mathcal{M}}(o, n) \qquad \mu : \mathrm{Hom}_{\mathcal{M}}(n, m) \qquad \Gamma \mathsf{ctx} \circledast m \qquad \Gamma. \widehat{\bullet}_{\mu} \widehat{\bullet}_{\nu} \vdash A \mathsf{type}_1 \circledast o \\ \Gamma.(\mu \mid \langle \nu \mid A \rangle) \vdash B \mathsf{type}_1 \circledast m \qquad \Gamma.(\mu \circ \nu \mid A) \vdash M_1 : B[\uparrow. \mathsf{mod}_{\nu}(\mathbf{v}_0)] \circledast m \\ \hline \Gamma.(\mu \mid \langle \nu \mid A \rangle) \vdash \mathsf{let}_{\mu} \mathsf{mod}_{\nu}(\_) \leftarrow \mathbf{v}_0 \text{ in } M_1[\sigma] : B \circledast m \end{array}$$

because we can calculate that

$$\Gamma \vdash (\mathsf{let}_{\mu} \mathsf{mod}_{\nu}(\_) \leftarrow \mathbf{v}_0 \text{ in } M_1[\sigma])[\mathsf{id}.M_0] = \mathsf{let}_{\mu} \mathsf{mod}_{\nu}(\_) \leftarrow M_0 \text{ in } M_1 : B[\mathsf{id}.M_0] \circledast m$$

We can rephrase this as the existence of a diagonal filler in the diagram

$$\begin{array}{c} \mathbf{y}(\Gamma.(\mu \circ \nu \mid A)) \xrightarrow{\lfloor M_1[\sigma] \rfloor} \widetilde{\mathcal{T}}_m \\ \mathbf{y}(\uparrow. \mathsf{mod}_{\nu}(\mathbf{v}_0)) \Biggl\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \mathbf{y}(\Gamma.(\mu \mid \langle \nu \mid A \rangle)) \xrightarrow{\lfloor B \rfloor} \mathcal{T}_m \end{array}$$

We can use a left lifting structure on a carefully chosen slice category to obtain such diagonal fillers. The internal language approach still applies because of the well-known lemma stating that the slice of a presheaf topos is also a presheaf topos, but over the corresponding category of elements. In symbols, for any $P : \mathbf{PSh}(\mathcal{C})$ we have an equivalence $\mathbf{PSh}(\mathcal{C})/P \simeq \mathbf{PSh}(\int_{\mathcal{C}} P)$: see [MLM92, III Ex. 8]