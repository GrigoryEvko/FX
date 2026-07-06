Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:35

Remarkably, it is not, and it is not novel either. As conjectured by Lawvere, proven by Freyd and published by Yetter [Yet87], for an arbitrary object $\mathbb{U}$ in an arbitrary topos, the transpension functor (there unnamed and denoted $\nabla$) over $\mathbb{U}$ exists if the amazing right adjoint exists. Indeed, in that case it can be constructed by the following pullback:

$$\begin{array}{ccc} \Sigma(u : \mathbb{U}).\circ[u]T & \longrightarrow & \mathbb{U} \surd (\Sigma(P : \text{Prop}).(P \to T)) \\ \downarrow_{\text{fst}} & & \downarrow_{\mathbb{U}\surd\text{fst}} \\ \mathbb{U} & \xrightarrow{(\lambda f.f \equiv \text{id}_{\mathbb{U}})^\top} & \mathbb{U} \surd \text{Prop} \end{array}$$

where $g^\top$ denotes the transpose of $g$ under $(\mathbb{U} \to \sqcup) \dashv (\mathbb{U} \surd \sqcup)$.

**6.8. Further reading.** We refer to the technical report [Nuy20b] for more information on

- composite multipliers $\sqcup \ltimes (U \ltimes U') := (\sqcup \ltimes U) \ltimes U'$,
- morphisms of multipliers $\sqcup \ltimes v : \sqcup \ltimes U \to \sqcup \ltimes U'$ (together with the previous point one could formalize the exchange rule),
- acting on slice objects as opposed to acting on elements (Section 6.5),
- properties of $\sqcup \ltimes \mathbf{y}U : \text{Psh}(\mathcal{W}) \to \text{Psh}(\mathcal{W})$, the left Kan extension along $\sqcup \ltimes U$, again viewed as a multiplier for $\mathbf{y}U$,
- non-endo multipliers $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$,
- rules for commuting (co)quantifiers for multipliers, (co)quantifiers for substitution, and (when adding the transpension type to an already modal type system) prior modalities.

## 7. THE FULLY FAITHFUL TRANSPENSION SYSTEM (FFTRAS) REVISITED

In Section 7.1, we give a pseudo-embedding of FFTraS (Section 2) into MTraS instantiated on a $\top$-slice fully faithful shape $\mathbb{U}$. In Sections 7.2 and 7.3, we revisit the results about internal transposition and higher-dimensional pattern-matching from Sections 2.3 and 2.4, as these also work for other shapes. Poles (Section 2.2) will be revisited in Section 9.1.

**7.1. Pseudo-Embedding of FFTraS in MTraS.** We give a pseudo-embedding of FFTraS into MTraS instantiated on a $\top$-slice fully faithful shape $\mathbb{U}$. Pseudo, in the sense that FF:CTX-FORALL:NIL will be only an isomorphism and some commutation properties w.r.t. shape substitution will only hold up to isomorphism, implying that a few other rules will need some adjustments before their translation is well-typed. We do not pay too much attention to those matters: the purpose of Section 2 was didactical and the purpose of the embedding is to show that it was also morally correct.

**7.1.1. Metatype of the embedding.** The judgement forms are translated as follows:

- A context $\Gamma \text{ctx}$ is translated as a pair consisting of a shape context $\{\Gamma\} \text{shpctx}$ listing the shape variables in $\Gamma$ and an internal context $\{\Gamma\} \mid \langle \Gamma \rangle \text{ctx}$.