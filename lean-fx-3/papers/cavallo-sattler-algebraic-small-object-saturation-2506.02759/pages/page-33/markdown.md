where $\rho$ is the vertical unitor for $\mathbb{A}$, and $\alpha$ is the associator. Thus, we can think of an $\mathbb{A}$-point over $(T, \tau)$ as a lift of $\tau$ through the vertical arrow category.

We use Theorem 2.3.27—and in particular fine-grained functoriality—to show that for cellular notions of composable structure $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$, an $\mathbb{A}$-point over a pointed endofunctor induces a canonical $\mathbb{A}$-point over its free monad.

**Theorem 3.4.4.** Let $(\mathcal{E}, \mathcal{M}, \mathsf{T}) \in \operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$ be a configuration for the free monad sequence on a pointed endofunctor. Let $U: \mathbb{A} \to \operatorname{Sq}(\mathcal{E})$ be a $(\kappa, \mathcal{M})$-cellular notion of composable structure. For any $\mathbb{A}$-point $(\overline{\mathsf{T}}, \theta)$ over $\mathsf{T}$, we have the following:

- (i) the free monad $\mathsf{M}$ on $\mathsf{T}$ admits an $\mathbb{A}$-point $(\overline{\mathsf{M}}, \psi)$;
- (ii) the canonical morphism $\gamma: \mathsf{T} \to \mathsf{M}_{\mathsf{p}}$ lifts to a morphism of $\mathbb{A}$-points $\overline{\gamma}: (\mathsf{T}, \theta) \to (\overline{\mathsf{M}}_{\mathsf{p}}, \psi)$;
- (iii) for any monad morphism $\alpha: \mathsf{M} \to \mathsf{M}'$, $\mathbb{A}$-point $(\overline{\mathsf{M}}', \psi')$ over $\mathsf{M}'$, and $\overline{\beta}: (\overline{\mathsf{T}}, \theta) \to (\overline{\mathsf{M}}'_{\mathsf{p}}, \psi')$ over $\alpha\gamma: \mathsf{T} \to \mathsf{M}_{\mathsf{p}}$, there is a unique $\overline{\alpha}: (\overline{\mathsf{M}}, \psi) \to (\overline{\mathsf{M}}', \psi')$ over $\alpha$ such that $\overline{\alpha}\,\overline{\gamma} = \overline{\beta}$.

*Proof.* We check that $\overline{\mathsf{T}} = (\overline{T}, \overline{\tau})$ defines a configuration $(\mathbb{A}^{\downarrow}, \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}), \overline{\mathsf{T}}) \in \operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$.

- 2.3.6(a) $\mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}})$ is a $\kappa$-backdrop in $\mathbb{A}^{\downarrow}$ by the assumption that $U$ is $(\kappa, \mathcal{M})$-cellular.
- 2.3.6(b) $\overline{\tau}$ is valued in $\mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}})$ because $\tau$ is valued in $\mathcal{M}$, by definition of $\operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$.
- 2.3.6(c) Given a square $(h, k): \boldsymbol{f} \to \boldsymbol{g}$ in $\mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}})$, the pushout application $\widehat{\overline{\tau}}(h, k)$ is a square of the form

$$\boldsymbol{g} \sqcup_{\boldsymbol{f}} \overline{\mathsf{T}} \boldsymbol{f} \begin{array}{c} \bullet \\ \downarrow \\ \bullet \end{array} \xrightarrow{\widehat{\overline{\tau}}(h, k)} \begin{array}{c} \bullet \\ \downarrow \\ \bullet, \end{array} \overline{\mathsf{T}} \boldsymbol{g}$$

so belongs to $\mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}})$ by definition of $\operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$.

2.3.6(d) The functor $\overline{\mathsf{T}}$ preserves colimits of $\kappa$-chains in $\mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}})$ because $\mathsf{T}$ preserves colimits of $\kappa$-chains in $\mathcal{M}$ (by definition of $\operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$) and $U^{\downarrow}$ is conservative.

By definition, the projections $\operatorname{dom}_{\downarrow}, \operatorname{cod}_{\downarrow}: \mathbb{A}^{\downarrow} \to \mathbb{A}$ form a span

$$(\mathcal{E}, \cong, \operatorname{Id}_{\mathcal{E}}) \xleftarrow{\operatorname{dom}_{\downarrow}} (\mathbb{A}^{\downarrow}, \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}), \overline{\mathsf{T}}) \xrightarrow{\operatorname{cod}_{\downarrow}} (\mathcal{E}, \mathcal{M}, \mathsf{T})$$

in $\operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$. By Theorem 2.3.27, applying the free monad construction yields a span

$$\operatorname{Id}_{\mathcal{E}} \xleftarrow{\operatorname{dom}_{\downarrow}} \overline{\mathsf{M}} \xrightarrow{\operatorname{cod}_{\downarrow}} \mathsf{M} \tag{3.3}$$

in $\mathbf{Mnd}_{\mathrm{s}}$ where $\mathsf{M}$ is the free monad on $\mathsf{T}$ and $\overline{\mathsf{M}}$ is a monad on $\mathbb{A}^{\downarrow}$. Because $U^{\downarrow}: \mathbb{A}^{\downarrow} \to \mathcal{E}^{\rightarrow}$ is an isofibration, we can assume without loss of generality that the associated isomorphisms $\operatorname{dom}_{\downarrow} \circ \overline{\mathsf{M}} \cong \operatorname{Id} \circ \operatorname{dom}_{\downarrow}$ and $\operatorname{cod}_{\downarrow} \circ \overline{\mathsf{M}} \cong \mathsf{M} \circ \operatorname{cod}_{\downarrow}$ are equalities.

The argument above also shows that $(\mathbb{A}^{\downarrow} \times_{\mathcal{E}} \mathbb{A}^{\downarrow}, \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}) \times_{\mathcal{E}} \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}), \overline{\mathsf{T}} \times_{\mathcal{E}} \mathbb{A}^{\downarrow}) \in \operatorname{ConfMnd}_{\mathsf{p}}^{\kappa}$. We have morphisms of configurations

$$\begin{array}{c} (\mathbb{A}^{\downarrow} \times_{\mathcal{E}} \mathbb{A}^{\downarrow}, \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}) \times_{\mathcal{E}} \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}), \overline{\mathsf{T}} \times_{\mathcal{E}} \mathbb{A}^{\downarrow}) \\ \xrightarrow{\pi_0} (\star, \theta) \Bigg\downarrow \quad \xrightarrow{\pi_1} (\mathbb{A}^{\downarrow}, \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}), \overline{\mathsf{T}}) \quad (\mathbb{A}^{\downarrow}, \mathbb{A}^{\downarrow}(\frac{\cong}{\mathcal{M}}), \overline{\mathsf{T}}) \end{array}$$

33