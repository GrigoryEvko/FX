2.4. GLOBULAR EQUIVALENCES

**Proposition 2.4.4.12.** *There exists an invertible natural transformation* $\mathrm{R}\,i \to \mathrm{R}$.

*Proof.* As $\Sigma[0]_\circ$ is isomorphic to $[1]$, the case $(n, n)$ for any integer $n$ of the lemma 2.4.4.7 imply that there exists an invertible transformation $\phi : (\mathrm{R}\,i)_{|\Delta} \to \mathrm{R}_{|\Delta}$ which is natural when restricted to the full subcategory of $\Delta$ whose morphisms are the monomorphisms.

The lemma 2.4.4.11 then implies that $\phi : (\mathrm{R}\,i)_{|\Delta} \to \mathrm{R}_{|\Delta}$ is natural. We can extend it to a natural transformation $\phi' : (\mathrm{R}\,i)_{|t\Delta} \to \mathrm{R}_{|t\Delta}$ thanks to the proposition 2.4.4.2.

Eventually, as both $\mathrm{R}\,i$ and $\mathrm{R}$ preserves colimits, we can extend $\phi'$ to a invertible natural transformation between $\mathrm{R}\,i$ and $\mathrm{R}$. $\square$

**Theorem 2.4.4.13.** *Let $i : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ be a left Quillen functor. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$. In particular, $i$ is a left Quillen equivalence.*

*Proof.* The proposition 2.4.4.12 implies that we have a natural transformation $\psi : i \to i_{str}$. Furthermore, hypotheses imply that this natural transformation is a weak equivalence on globes. According to proposition 2.4.3.1, $\psi$ is then a weakly invertible natural transformation. We then have a zigzag of weakly invertible natural transformations:

$$i \xrightarrow{\sim} i_{str} \xleftarrow{\sim} id.$$

**Corollary 2.4.4.14.** *Let $i : \mathrm{tPsh}(\Delta) \to \mathrm{tPsh}(\Delta)$ be a left Quillen functor. Suppose that there exists a zigzag of weakly invertible natural transformations:*

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

*Then, there exists a zigzag of weakly invertible natural transformations between $i$ and $id$. In particular, $i$ is a left Quillen equivalence.*

*Proof.* We recall that the adjunction between stratified and marked simplicial sets is denoted by:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}(\Delta) \xrightarrow{\perp} \mathrm{mPsh}(\Delta) : \iota$$

The proposition 2.1.2.8 states that this adjunction is a Quillen equivalence and that the functor $\iota$ preserves acyclic cofibrations.

Remark now that the functor $(\_)_{\mathrm{mk}} \circ i \circ \iota : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ verifies the hypothesis of theorem 2.4.4.13 and we then have a zigzag of of weakly invertible natural transformations:

$$(\_)_{\mathrm{mk}} \circ i \circ \iota \rightsquigarrow id$$

This induces a zigzag of of weakly invertible natural transformations:

$$i \to \iota \circ (\_)_{\mathrm{mk}} \circ i \circ \iota \circ (\_)_{\mathrm{mk}} \rightsquigarrow \iota \circ (\_)_{\mathrm{mk}} \leftarrow id$$

99