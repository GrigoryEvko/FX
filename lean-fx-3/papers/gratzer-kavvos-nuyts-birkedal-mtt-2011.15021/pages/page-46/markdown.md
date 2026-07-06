11:46

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

(pronounced 'earlier'), given by

$$(\blacktriangleleft X)(n) \triangleq X(n+1)$$

It remains to show that the three left adjoints—$\Pi_0$, $\Delta$, and $\blacktriangleleft$—are given by precomposition. We define three monotone functions between the posets $1 \triangleq \{*\}$ and $\omega$:

$$\begin{array}{ccc} K_0: 1 \to \omega & \quad \quad !_\omega: \omega \to 1 & \quad l: \omega \to \omega \\ * \mapsto 0 & \quad n \mapsto * & \quad n \mapsto n+1 \end{array}$$

Identifying **Set** with **PSh(1)**, we see that

$$\Pi_0 = K_0^*: \mathbf{PSh}(\omega) \to \mathbf{Set} \quad \Delta = !_\omega^*: \mathbf{Set} \to \mathbf{PSh}(\omega) \quad \blacktriangleleft = l^*: \mathbf{PSh}(\omega) \to \mathbf{PSh}(\omega)$$

Moreover, we trivially have the following pointwise equations and inequalities:

$$\mathrm{id}_\omega \leq l \quad K_0 \circ !_\omega \leq \mathrm{id}_\omega \quad \mathrm{id}_1 = !_\omega \circ K_0 \quad \quad \quad !_\omega = !_\omega \circ l$$

Seeing posets as categories, pointwise inequalities are simply natural transformations between monotone maps. By feeding them into the strict 2-functor $(-)^*: \mathbf{Cat}^{\text{coop}} \to \mathbf{Cat}$, we are able to define a strict 2-functor $[\widehat{\mathbf{B}}_-]: \mathcal{M}_g^{\text{coop}} \to \mathbf{Cat}$ which maps

$$\begin{array}{rcl} \gamma: t \to s & \longmapsto & [\widehat{\mathbf{B}}_\gamma] = \Delta : \mathbf{Set} \to \mathbf{PSh}(\omega) \\ \delta: s \to t & \longmapsto & [\widehat{\mathbf{B}}_\delta] = \Pi_0 : \mathbf{PSh}(\omega) \to \mathbf{Set} \\ \ell: t \to t & \longmapsto & [\widehat{\mathbf{B}}_\ell] = \blacktriangleleft : \mathbf{PSh}(\omega) \to \mathbf{PSh}(\omega) \end{array}$$

This fully specifies the modal context structure, which consists of left adjoints. Each of these left adjoints is given by precomposition. Thus, the unique corresponding right adjoint is given by right Kan extension (see Section 8). Hence, by Lemma 8.2 and Theorem 7.1,

**Theorem 9.2.** *There is a model of MTT with mode theory $\mathcal{M}_g$, interpreting $s$ as $\mathbf{Set}$ and $t$ as $\mathbf{PSh}(\omega)$. Furthermore, this model interprets $\delta$ by the dependent right adjoint arising from $\Pi_0 \dashv \Delta$, $\gamma$ by $\Delta \dashv \Gamma$, and $\ell$ by $\blacktriangleleft \dashv \blacktriangleright$.*

**Remark 9.3.** This mode theory is a poset-enriched category. As a result, the key substitutions are unique: for any $\mu, \nu$ there is at most one substitution $\Gamma_{\widehat{\mathbf{B}}_\mu} \vdash \mathbf{A}_{\Gamma}^{\nu \leq \mu}: \Gamma_{\widehat{\mathbf{B}}_\nu} @ m$. This property means that we can elide them without ambiguity. However, this may sometimes make type-checking on pen-and-paper difficult, so we employ a simplified notation: we will write $A^{\nu \leq \mu}$ or $M^{\nu \leq \mu}$ for the application of the unique key substitution $\nu \leq \mu$ in context $\Gamma_{\widehat{\mathbf{B}}_\mu}$. For instance, given a type $\Gamma_{\widehat{\mathbf{B}}_1} = \Gamma \vdash A \text{ type}_1 @ t$ we can form the type $\Gamma_{\widehat{\mathbf{B}}_\ell} \vdash A^{1 \leq \ell} \text{ type}_1 @ t$, and hence the type $\Gamma \vdash \langle \ell \mid A^{1 \leq \ell} \rangle \text{ type}_1 @ t$.

**9.3. Guarded recursion, internally.** Given the model that we constructed above, we feel perfectly justified in defining the following shorthands within MTT:

$$\Box A \triangleq \langle b \mid A \rangle \quad \blacktriangleright A \triangleq \langle \ell \mid A \rangle \quad \Gamma A \triangleq \langle \gamma \mid A \rangle \quad \Delta A \triangleq \langle \delta \mid A \rangle$$

where $b \triangleq \delta \circ \gamma$. The aim of this section is to show that MTT equipped with $\mathcal{M}_g$ and these shorthands can be used to reason about guarded recursion. In particular, we will show that this is strict improvement on previous solutions, by establishing that

(1) When restricted to mode $s$, the type theory is simply standard Martin-Löf Type Theory.
(2) The modalities on mode $t$ give rise to the standard modalities and operations of Guarded Type Theory [BGC$^+$16] inside the type theory.