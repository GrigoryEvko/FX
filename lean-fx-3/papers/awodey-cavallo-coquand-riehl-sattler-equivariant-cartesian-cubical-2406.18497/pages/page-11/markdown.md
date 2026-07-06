Van den Berg and Faber [BF22] present a second approach to constructivizing Voevodsky's model replacing Kan fibrations with a restricted notion of *effective Kan fibration*. As in our own work, the idea is to impose additional uniformity conditions on lifts. Although this approach does not require restricting cofibrations to Reedy decidable monomorphisms and thus may avoid the coherence issues of [GH22], it is still work in progress: to our knowledge, neither an interpretation of universes nor a Quillen model structure have been established thus far.

1.7.4. *Cubical type theories.* Cohen, Coquand, Huber, and Mörtberg [CCHM15] present not only a model of homotopy type theory but also a *cubical type theory*, an extension of Martin-Löf type theory with new judgments and type formers that reflect the structure of the De Morgan cubical sets model. Angiuli et al. [AFH18; ABCHFL21] likewise devise a cubical type theory interpreting in cartesian cubical sets. Unlike HoTT as formulated in [UF13], these theories enjoy canonicity: any closed natural number computes definitionally to a numeral [AFH18; Hub19].

The cartesian cubical type theory of [ABCHFL21] can also be interpreted in the equivariant cartesian model: every equivariant fibration is in particular a fibration in the sense of the original cartesian cubical set model, so interprets the filling operator (sometimes also called the *composition* operator) of cartesian cubical type theory [ABCHFL21, §1.2]. Thus, cartesian cubical type theory has a model presenting the homotopy theory of spaces.

One could imagine extending cartesian cubical type theory with an equivariant filling operator. Such an operator could be introduced by the rule

$$\begin{array}{c} k \in \mathbb{N} \quad \Gamma, \vec{r}: I^k \vdash A \text{ type} \quad \Gamma \vdash \phi \text{ cof} \quad \Gamma \vdash \vec{r}, \vec{s}: I^k \\ \Gamma, \phi, \vec{r}: I^k \vdash u: A \quad \Gamma \vdash u_0: A[\vec{r}/\vec{r}] \quad \Gamma, \phi \vdash u[\vec{r}/\vec{r}] = u_0: A \\ \hline \Gamma \vdash \text{comp}_{\vec{r},A}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0: A[\vec{r}/\vec{r}] \end{array}$$

which straightforwardly generalizes the ordinary filling operator by replacing the interval $I$ with an arbitrary $k$-cube $I^k$, together with the usual equations

$$\begin{array}{ll} \text{comp}_{\vec{r},A}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0 = u[\vec{s}/\vec{r}] & \text{when } \phi \text{ holds} \\ \text{comp}_{\vec{r},A}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0 = u_0 & \text{when } \vec{r} = \vec{s} \end{array}$$

which specify that the output of comp is a filler for the input box. *Equivariance* states that, for each $\sigma \in \Sigma_k$, we have the equation

$$\text{comp}_{\vec{r},A}^{\sigma^* \vec{r} \rightarrow \sigma^* \vec{s}} [\phi \mapsto \vec{r}.u] \ u_0 = \text{comp}_{\vec{j},A[\sigma^* \vec{j}/\vec{r}]}^{\vec{r} \rightarrow \vec{s}} [\phi \mapsto \vec{j}.u[\sigma^* \vec{j}/\vec{r}]] \ u_0,$$

where $\sigma^*$ is the action of $\sigma$ on $k$-tuples of terms in $I$.

We are, however, not aware of any practical use for the equivariant filling operator in cubical type theory. Synthetic homotopy theorists working in cubical type theories have yet to encounter any fundamental difference in expressivity between, e.g., cartesian and De Morgan cubical type theories, or even between cubical type theories and HoTT à la [UF13], and the situation seems to be the same here. It would also be expensive and complicated to type-check equivariant filling operators: to compare two $k$-dimensional comp terms for equality requires testing whether they agree modulo any of the $k!$ permutations.

1.8. **Acknowledgments.** The discovery of the equivariant model occurred at the Centre for Advanced Study (CAS) at the Norwegian Academy of Science and Letters in Oslo, Norway, in the academic year 2018–19 research project on Homotopy Type Theory and Univalent Foundations organized by Marc Bezem and Bjørn Dundas. We gratefully acknowledge their support. The first and third authors are also grateful to the Institut des Hautes Études Scientifiques for hosting two weeks of very nice discussions in June 2022.

The perspective of the generating categories of cofibrations and trivial cofibrations as internally indexed by cubical species (see §4.3) was informed by discussions with Andrew Swan. Reid Barton's

11