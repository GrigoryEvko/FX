Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:19

*The inverse is given by:*

$$\begin{array}{c} (\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, \kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}]) \\ \downarrow (\mathrm{id}_{(\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, y)}, \mathbf{\alpha}_{\varepsilon}^{\eta'}) \\ (\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, \kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}], \mathbf{\Omega}_{\kappa}^{\zeta}, \mathbf{\Omega}_{\mu}^{\kappa}) \\ \downarrow (1_{\Gamma}, \mathbf{\alpha}_{\eta}^{\varepsilon'}, y/x, \mathbf{\Omega}_{\mu}^{\kappa}) \\ (\Gamma, x : A, \mathbf{\Omega}_{\mu}^{\kappa}) \end{array}$$

*Correspondingly, given $B$ in the codomain context of $\sigma$, there is an isomorphism of types*

$$(x : A) \rightarrow \langle \mu \mid B[\sigma] \rangle \quad \cong \quad \left\langle \mu \mid (\kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}]) \rightarrow B \right\rangle$$

*expressing internal transposition.*

#### 4. THE MODAL TRANSPENSION SYSTEM (MTRAS): GENERAL MODE THEORY AND SEMANTICS

As mentioned in Section 1.3, in our modal transpension system (MTraS), the transpension modality $\mathfrak{d}[u]$ will be part of an adjoint triple of internal modalities $\Omega[u] \dashv \Pi u \dashv \mathfrak{d}[u]$ together with weakening $\Omega[u]$ and universal quantification $\Pi u$ or, more generally in potentially non-cartesian systems, an adjoint triple $\lrcorner[u] \dashv \forall u \dashv \mathfrak{d}[u]$ together with fresh weakening $\lrcorner[u]$ and substructural (e.g. linear/affine) universal quantification $\forall u$. The further left adjoints $\Sigma u$ (cartesian) or $\exists u$ (potentially non-cartesian) cannot be internalized because every internal MTT modality needs to have a further semantic left adjoint; thus, they will only appear as left names.

Notably, the aforementioned modalities all bind or depend on a variable, a phenomenon which is not supported by MTT. We shall address this issue in the current section by grouping shape variables such as $u : \mathbb{U}$ in a **shape context** which is not considered part of the type-theoretic context but instead serves as the *mode* of the judgement.

We assume that there are no prior modalities, i.e. that the type system to which we wish to add a transpension type is non-modal in the sense that it has a single mode and only the identity modality. We assume that this single prior mode is modelled by the presheaf category $\mathrm{Psh}(\mathcal{W})$. Prior modalities and in particular their commutation with the modalities mentioned above, are considered in the technical report [Nuy20b].

**4.1. Shape contexts.** Assume we have in the prior system a context $\mathbb{X}$ modelled by a presheaf $\Xi$ over $\mathcal{W}$. Then the presheaves $\mathrm{Psh}(\mathcal{W}/\Xi)$ over the category of elements $\mathcal{W}/\Xi$ of the presheaf $\Xi$ are also a model of dependent type theory. Denoting the judgements of the latter system with a prefix $\mathbb{X} \mid$, it happens to be the case that judgements $\mathbb{X} \mid \Gamma \vdash J$ (i.e. $\Gamma \vdash J$ in $\mathrm{Psh}(\mathcal{W}/\Xi)$) have precisely the same meaning as judgements $\mathbb{X} \mid \Gamma \vdash J$ in $\mathrm{Psh}(\mathcal{W})$ (for a suitable but straightforward translation of $J$). Thus, we will group together all shape variables (variables for which we want a transpension type) in a **shape context** $\mathbb{X}$ in front of the typing context. Our judgements will then take the form $\mathbb{X} \mid \Gamma \vdash J$. Modal techniques will be used to signal what part of the context $\Gamma$ is fresh for a shape variable $u : \mathbb{U}$, as this can then no longer be signalled by the position of $u : \mathbb{U}$ in the context. All of this allows us