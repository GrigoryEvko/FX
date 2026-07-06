Shulman

18-5

$$\frac{\mu : p \to q \text{ sharp } \quad \Gamma/\mu \vdash A \text{ type}_p}{\Gamma \vdash \mu \boxdot A \text{ type}_q} \quad \frac{\mu : p \to q \text{ sharp } \quad \Gamma/\mu \vdash a : A}{\Gamma \vdash \text{mod}_\mu(a) : \mu \boxdot A}$$

$$\begin{array}{l} \mu : p \to q \text{ sharp } \quad \nu : q \to r \text{ transparent } \quad \Gamma/\nu \vdash d : \mu \boxdot A \\ \Gamma, y :^\nu \mu \boxdot A \vdash B \text{ type}_r \quad \Gamma, x :^{\nu \circ \mu} A \vdash b : B [y \leftarrow \text{mod}_\mu(x)] \\ \hline \Gamma \vdash \text{let}_\nu \text{ mod}_\mu(x) \leftarrow d \text{ in } b : B [y \leftarrow d] \end{array}$$

$$\begin{array}{l} \mu : p \to q \text{ sharp } \quad \nu : q \to r \text{ transparent } \quad \Gamma/(\nu \circ \mu) \vdash a : A \\ \Gamma, y :^\nu \mu \boxdot A \vdash B \text{ type}_r \quad \Gamma, x :^{\nu \circ \mu} A \vdash b : B [y \leftarrow \text{mod}_\mu(x)] \\ \hline \Gamma \vdash (\text{let}_\nu \text{ mod}_\mu(x) \leftarrow \text{mod}_\mu(a) \text{ in } b) = b [x \leftarrow a] \end{array}$$

Fig. 5. Positive modalities in MATT

$$\begin{array}{l} \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu^\dagger \vdash A \text{ type}_q}{\Gamma \vdash \mu \diamond \to A \text{ type}_p} \quad \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu^\dagger \vdash M : A}{\Gamma \vdash \mu \mapsto M : \mu \diamond \to A} \\ \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu \vdash M : \mu \diamond \to A}{\Gamma \vdash M \circledast \mu : A [1_\Gamma/\epsilon_\mu]} \quad \frac{\mu : p \to q \text{ sinister } \quad \Gamma/(\mu \circ \mu^\dagger) \vdash M : A}{\Gamma \vdash (\mu \mapsto M) \circledast \mu = M [1_\Gamma/\epsilon_\mu] : A [1_\Gamma/\epsilon_\mu]} \\ \frac{\mu : p \to q \text{ sinister } \quad \Gamma/\mu^\dagger \vdash (M [1_\Gamma/\eta_\mu]) \circledast \mu = (N [1_\Gamma/\eta_\mu]) \circledast \mu : A}{\Gamma \vdash M = N : \mu \diamond \to A} \end{array}$$

Fig. 6. Negative modalities in MATT

ent, while in [31] the transparent morphisms are also the image of $\mathcal{L}$. But in fact, if a morphism is both sinister and tangible, then it “might as well” be transparent, in that elimination rules with it as framing can be deduced from those with identity framing; the proof follows [37, Lemma 5.1].

Our semantics in the co-dextrification will apply to the following case.

Example 2.3 Let $\mathcal{L}$ be any 2-category and $\mathcal{S}$ a class of morphisms in it, and let $\mathcal{M} = \mathcal{L}[\mathcal{S}^\dagger]$ be the result of freely adjoining a right adjoint $\mu^\dagger$ for every morphism $\mu$ in $\mathcal{S}$. We identify $\mathcal{L}$ with its image in $\mathcal{L}[\mathcal{S}^\dagger]$. We take this image $\mathcal{L}$ to be the transparent morphisms, $\mathcal{S}$ to be the sinister morphisms, and the tangible and sharp morphisms to be those that are isomorphic to one of the form $\mu \circ \nu^\dagger$ where $\mu \in \mathcal{L}$ and $\nu \in \mathcal{S}$. This choice of tangible and sharp morphisms appears necessitated by our semantics (see Lemma 5.5), and $\mathcal{L}$ is then the largest class of transparent morphisms satisfying the composition axiom.

Assumption 2.4 We always consider $\mathcal{L}[\mathcal{S}^\dagger]$ to be an adjoint mode theory as in Example 2.3.

Example 2.5 We can regard Two-Level Type Theory [1] as an instance of MATT with two modes, f for (fibrant/inner) types and e for (non-fibrant/outer) exotypes, and an isomorphism $\iota : e \cong f$. We let all the morphisms be tangible, but we take only identities as sharp and transparent, and only the morphism $\iota : e \to f$ as sinister. Then $\iota \diamond \to -$ is the coercion from types to exotypes (c in [1]), with a bijection between terms of types $A$ and $\iota \diamond \to A$. Allowing $\iota$ to be sharp would produce fibrant replacements $\iota \boxdot A$, which are inconsistent [1, §2.7] with univalence for fibrant types and UIP for exotypes. Inspecting the proof shows that the same conclusion would follow if we had modal function-types $(x :^\iota A) \to B$.

Remark 2.6 It seems likely that normalization for MTT [10] extends to MATT. But to deduce decidability of type-checking from this requires decidability of equality for $\mathcal{M}$, whereas $\mathcal{L}[\mathcal{S}^\dagger]$ can fail to have decidable equality even if $\mathcal{L}$ does [7]. However, we can hope that $\mathcal{L}[\mathcal{S}^\dagger]$ will have decidable equality if $\mathcal{L}$