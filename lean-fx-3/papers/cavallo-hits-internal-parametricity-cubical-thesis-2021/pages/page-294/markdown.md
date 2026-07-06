282 Formalism

**Mode theory** As always, we have two modes, the pointwise and the parametric.

$$\overline{\text{par mode}}$$

$$\overline{\text{pt mode}}$$

We seed the modality judgment with the three basic modalities, then generate a category structure by including an identity id and composition $-\otimes-$.

$$\overline{\text{cc} : \text{pt} \rightarrow \text{par}}$$

$$\overline{\text{dsc} : \text{par} \rightarrow \text{pt}}$$

$$\overline{\text{glo} : \text{pt} \rightarrow \text{par}}$$

$$\overline{\text{id} : m \rightarrow m}$$

$$\frac{\nu : n \rightarrow p \quad \mu : m \rightarrow n}{\nu \otimes \mu : m \rightarrow p}$$

$$\frac{\mu : m \rightarrow n}{\mu \otimes \text{id} = \mu : m \rightarrow n}$$

$$\frac{\mu : m \rightarrow n}{\text{id} \otimes \mu = \mu : m \rightarrow n}$$

$$\frac{\pi : p \rightarrow q \quad \nu : n \rightarrow p \quad \mu : m \rightarrow n}{(\pi \otimes \nu) \otimes \mu = \pi \otimes (\nu \otimes \mu) : m \rightarrow q}$$

The 2-cell judgment, $\alpha :: \mu \Rightarrow \mu' : m \rightarrow n$, codifies the adjunctions between the three basic modalities and the fact that cc and glo both cancel dsc up to isomorphism. To avoid some repetition, we encapsulate the basic adjoint relationships by an auxiliary judgment $m : \mu \dashv \nu : n$ (presupposing $\mu : m \rightarrow n$ and $\nu : n \rightarrow m$).

$$\overline{\text{pt} : \text{cc} \dashv \text{dsc} : \text{par}}$$

$$\overline{\text{par} : \text{dsc} \dashv \text{glo} : \text{pt}}$$

The 2-cell judgment is then required to support the following morphisms: unit and counit transformations for each adjunction, inverses for these in the dsc $\otimes$ cc and dsc $\otimes$ glo cases, and vertical and horizontal composition operations endowing the mode theory with the structure of a (strict) 2-category. (The former is "ordinary" composition of 2-cells, the latter the action of $-\otimes-$ on 2-cells).

$$\frac{m : \mu \dashv \nu : n}{\text{unit} :: \mu \otimes \nu \Rightarrow \text{id} : n \rightarrow n}$$

$$\frac{m : \mu \dashv \nu : n}{\text{cou} :: \text{id} \Rightarrow \nu \otimes \mu : m \rightarrow m}$$

$$\overline{\text{cou}^{-1} :: \text{dsc} \otimes \text{cc} \Rightarrow \text{id} : \text{pt} \rightarrow \text{pt}}$$

$$\overline{\text{unit}^{-1} :: \text{id} \Rightarrow \text{dsc} \otimes \text{glo} : \text{pt} \rightarrow \text{pt}}$$

$$\frac{\alpha' :: \mu' \Rightarrow \mu'' : m \rightarrow n \quad \alpha :: \mu \Rightarrow \mu' : m \rightarrow n}{\alpha' \circ \alpha :: \mu \Rightarrow \mu'' : m \rightarrow n}$$

$$\frac{\beta :: \nu \Rightarrow \nu' : n \rightarrow p \quad \alpha :: \mu \Rightarrow \mu' : m \rightarrow n}{\beta \otimes \alpha :: \nu \otimes \mu \Rightarrow \nu' \otimes \mu' : m \rightarrow p}$$