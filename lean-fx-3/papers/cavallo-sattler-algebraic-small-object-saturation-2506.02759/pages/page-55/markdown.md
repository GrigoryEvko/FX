and a double category of cell complexes such as Athorne's, at least in some cases. To reach that point, we would need in particular to resolve the following issues involving retract lifting.

## 5.2 Retract lifting

Our Theorems 3.5.13 and 3.5.16 can assign some structure to every left map of a cofibrantly generated AWFS, but they say very little about the assignment except that it is functorial. In particular, there is no guarantee that the assignment is in some sense unique, nor that it relates to the input data in some way; we only get such guarantees in our Theorem 3.5.5, which is restricted to free coalgebras. We extend the assignment from free coalgebras to all copointed endofunctor coalgebras by assuming a retract lifting operator on the target, and we know of no conditions we could put on this operator that would ensure uniqueness.

To see the difficulty, consider what should be the prototypical notion of composable structure: a double category of left maps with its forgetful functor $U_{\mathsf{L}_{\mathsf{p}}}: \mathsf{L}_{\mathsf{p}} \text{-Coalg} \to \mathbb{S}\mathsf{q}(\mathcal{E})$. It lifts retracts in the sense that given a section-retraction pair $f' \xrightarrow{\sigma} f \xrightarrow{\rho} f'$ in $\mathcal{E}^{\neg}$ and a coalgebra structure $\beta: f \to Lf$ on $f$, we get a coalgebra structure $\beta' := L\rho \circ \beta \circ \sigma: f' \to Lf'$ on $f'$. However, the retract diagram itself need not lift: $\sigma$ and $\rho$ need not be morphisms of coalgebras between $(f, \beta)$ and $(f', \beta')$. In particular, "having retract lifts" is apparently a *structure* rather than a *property*; we can at least ask that the choice is functorial (and interacts nicely with composition of left maps, see Definition 3.5.14), but we know of no characteristic property of $(f, \beta')$ that abstractly singles it out among all lifts of $(f, \beta)$ along the retract.

One may also note that while Theorem 3.5.5 deals with free coalgebras and Theorems 3.5.13 and 3.5.16 deal with copointed endofunctor coalgebras, we have no theorem for mapping out of the intermediate category of *comonad* coalgebras. In that case, the natural requirement would be that the target notion of composable structure is *closed under retract equalizers* in the sense of Garner [Gar07, Proposition 44]. As used in Beck's monadicity theorem, any comonad coalgebra $(f, \beta: f \to Lf)$ can be written as a retract equalizer of free coalgebras in L-Coalg, namely the equalizer of the fork

$$Lf \xrightarrow[\Sigma_f]{L\beta} LLf.$$

Given a notion of composable structure $U: \mathbb{A} \to \mathbb{S}\mathsf{q}(\mathcal{E})$ and a lift $\boldsymbol{L}_{\mathbb{A}}: \mathcal{E}^{\neg} \to \mathbb{A}^{\sharp}$ of the free coalgebra functor through $\mathbb{A}$, one would like to extend the mapping to comonad coalgebras by assuming $U$ is closed under retract equalizers and sending $(f, \beta: f \to Lf)$ to the equalizer of a fork

$$\boldsymbol{L}_{\mathbb{A}}f \xrightarrow[?]{\boldsymbol{L}_{\mathbb{A}}\beta} \boldsymbol{L}_{\mathbb{A}}Lf.$$

However, we do not see how to arrange that $\Sigma_f$ lifts to a morphism $\boldsymbol{L}_{\mathbb{A}} \to \boldsymbol{L}_{\mathbb{A}}Lf$, nor alternatively how to adjust the retract equalizer closure condition to compensate for the absent map.

## 6 Acknowledgments

We thank Daniël Apol and Ivan Di Liberti for helpful conversations. We thank Benno van den Berg for calling our attention to problems with our first draft's description of constructive transfinite recursion and for sharing his own approach with us.

The first author was supported by the Knut and Alice Wallenberg Foundation (KAW) under Grant No. 2019.0116, and the second author was supported by the US Air Force Office of Scientific Research under award number FA9550-24-1-0302.

55