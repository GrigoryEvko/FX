1:12

M. SHULMAN

Vol. 19:2

In particular, $\mathcal{P}^{\mathrm{L}}$ is $*$-autonomous as soon as $\mathcal{P}$ has $\otimes, \mathbb{1}, (\cdot)^{*}$. And as in a $*$-autonomous category, duals can be constructed by homming into the counit:

$$A^{*} = A \multimap \bot.$$

Less familiar instances of Proposition 2.16 relate the modalities to the tensors and homs, particularly the mixed ones: we have

$$\begin{array}{l} X \multimap B = \mathsf{F}X \multimap B \quad X \rtimes A = \mathsf{F}X \otimes A \\ A \multimap B = \mathsf{U}(A \multimap B) \quad X \boxtimes Y = \mathsf{F}(X \times Y) \\ X \multimap B = \mathsf{U}(\mathsf{F}X \multimap B) \quad X \boxtimes Y = \mathsf{F}X \otimes \mathsf{F}Y \\ X \multimap B = X \to \mathsf{U}B \quad \mathbb{1} = \mathsf{F}1 \\ \mathsf{U}A = \mathbb{1} \multimap A \quad \mathsf{F}X = X \rtimes \mathbb{1} \\ \mathsf{U}A = 1 \multimap A \quad \mathsf{F}X = X \boxtimes 1 \end{array}$$

whenever all the operations on the right-hand side exist. In particular, since both $\mathsf{F}(X \times Y)$ and $\mathsf{F}X \otimes \mathsf{F}Y$ have the universal property of $X \boxtimes Y$, they are isomorphic if they both exist. (This is, of course, closely related to Seely's characterization of the modality $!$; see Remark 3.6.) Thus, if $\otimes, \mathbb{1}, \times, 1, \mathsf{F}$ exist then $\mathsf{F}$ is a strong monoidal functor. Similarly, if both $\mathsf{U}(\mathsf{F}X \multimap B)$ and $X \to \mathsf{U}B$ exist they are isomorphic (which is related to Girard's embedding of nonlinear logic in linear logic); if $\lrcorner(X \times Y)$ and $\lrcorner X \rtimes \lrcorner Y$ exist they are isomorphic; and so on.

**Remark 2.17.** As a trivial instance, a unary co-unary linear morphism, i.e. one of the form $\psi \in \mathcal{P}(\mid A; B)$, is universal if and only if it is an isomorphism (and similarly in the nonlinear case). Thus, Proposition 2.16 also implies that universal morphisms are stable under composition with isomorphisms, conversely to Proposition 2.9.

We can also consider limits and colimits in LNL polycategories. In general, we require a **limit** of a diagram of linear or nonlinear objects (and unary co-unary morphisms) to induce bijections on all hom-sets where it appears in the codomain, and similarly for a **colimit** whenever it appears in the domain. (In the case of products and coproducts, this definition appears in [Pas04].) The simplest case of this is that a limit of nonlinear objects satisfies

$$\mathcal{P}(\Theta; \lim_i X_i) \cong \lim_i \mathcal{P}(\Theta; X_i), \tag{2.1}$$

generalizing Proposition 2.11(iii) and reducing to an ordinary limit in the cartesian monoidal $\mathcal{P}^{\mathrm{NL}}$ if $\times, 1$ exist. However, a colimit of nonlinear objects satisfies both

$$\mathcal{P}(\Theta, \operatorname{colim}_i X_i; Y) \cong \lim_i \mathcal{P}(\Theta, X_i; Y) \tag{2.2}$$

$$\mathcal{P}(\Theta, \operatorname{colim}_i X_i \mid \Gamma; \Delta) \cong \lim_i \mathcal{P}(\Theta, X_i \mid \Gamma; \Delta) \tag{2.3}$$

induced by the same universal cocone. This implies that the colimit is

- (i) preserved in each variable by $\times$, insofar as $\times$ exists;
- (ii) sent by $\mathsf{F}$ to a colimit in $\mathcal{P}^{\mathrm{L}}$ that is preserved in each variable by $\otimes$, insofar as $\mathsf{F}, \otimes$ exist; and
- (iii) sent by $\lrcorner$ to a limit in $\mathcal{P}^{\mathrm{L}}$ that is preserved in each variable by $\Re$, insofar as $\lrcorner, \Re$ exist.

Moreover, if all $\times, \mathsf{F}, \lrcorner, \otimes, \Re$ exist, then a colimit in the ordinary category $\mathcal{P}^{\mathrm{NL}}$ is a colimit in $\mathcal{P}$ if and only if it is preserved in these ways.