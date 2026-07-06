**Remark 11.5.** The $\infty$-category associated to the projective model structure on $\mathfrak{sPsh}\mathcal{D}$ is really the $\infty$-category of small presheaves of spaces on $\mathcal{D}$, essentially by the same argument as for small categories.

**Lemma 11.6.** *Given a locally connected countably lextensive category $\mathcal{E}$.*

- (i) *The restricted Yoneda embedding $y: \mathcal{E} \to \mathrm{Psh}(\mathcal{E}^{\mathrm{con}})$ is well-defined, fully faithful and preserves limits and all van Kampen coproducts.*
- (ii) *The restricted Yoneda embedding $y: \mathfrak{s}\mathcal{E} \to \mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ is well-defined, fully faithful and preserves limits, pushouts along a cofibration, tensoring by objects of $\mathcal{E}$ and $\mathfrak{sSet}$ and colimits of sequences of cofibrations.*

*Proof.* For any connected object $X \in \mathcal{E}^{\mathrm{con}}$, $\mathrm{Hom}_{\mathrm{Set}}(X, -)$ preserves coproducts by Lemma 11.3, hence as every object $Y \in E$ is a small van Kampen coproduct of connected objects, its image under the restricted Yoneda embedding is a small coproduct of representables, and hence is a small presheaf. This proves the existence and the preservation of coproducts by the Yoneda embedding. Preservation of limits is immediate. It is fully faithful on connected objects by the Yoneda lemma, and this implies that it is fully faithful in general as morphisms between van Kampen coproducts of connected objects can be explicitly described as maps between their components.

The simplicial version is just the ordinary version applied levelwise in the simplicial direction so all results of part (ii) follow immediately. For the preservation of colimits we use the fact that a functor that preserves countable coproducts preserves pushouts of complemented inclusions and colimits of sequences of complemented inclusions, and all the colimits considered in the lemma are levelwise of this form. $\square$

**Theorem 11.7** (Generalised Elmendorf's theorem). *Let $\mathcal{E}$ a locally connected countably lextensive category.*

- (i) *A map in $\mathfrak{s}\mathcal{E}$ is a cofibration, fibration or weak equivalence if and only if its image by the restricted Yoneda embedding is one for the projective model structure.*
- (ii) *If $\mathcal{E}$ is in addition completely lextensive, then the restricted Yoneda embedding induces an equivalence between the full subcategories of cofibrant objects of $\mathfrak{s}\mathcal{E}$ and $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$. In particular it induces an equivalence of the corresponding $\infty$-categories.*

*Proof.* The (cofibration, trivial fibration) and (trivial cofibration, fibration) weak factorisation systems on $\mathfrak{s}\mathcal{E}$ are cofibrantly generated in the (non-enriched) sense of [CD09] by the classes of arrows $\{i \cdot E \mid i \in I_{\mathfrak{sSet}}, E \in \mathcal{E}\}$ and $\{j \cdot E \mid j \in I_{\mathfrak{sSet}}, E \in \mathcal{E}\}$. As every object in $\mathcal{E}$ is assumed to be a (van Kampen) coproduct of connected objects, one can restrict to $E \in \mathcal{E}^{\mathrm{con}}$. Because of Lemma 11.6, these generators are sent exactly to the generators of the projective model structure of $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$.

It immediately follows that an arrow in $\mathfrak{s}\mathcal{E}$ is a (trivial) fibration if and only if it is one in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ as these classes are characterised by the same lifting property.

Moreover, also because of Lemma 11.6 the restricted Yoneda embedding preserves coproducts and pushouts of the generating cofibrations, transfinite composition of cofibrations and retracts. Thus because of how (trivial) cofibrations are constructed in $\mathfrak{s}\mathcal{E}$ from the small object argument, it follows that their images in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ are projective (trivial) cofibrations. Conversely, an arrow in $\mathfrak{s}\mathcal{E}$ which is a (trivial) cofibration in the projective model structure on $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$ has the lifting property against all (trivial) fibrations in $\mathfrak{sPsh}(\mathcal{E}^{\mathrm{con}})$, but as the restricted Yoneda embedding is

54