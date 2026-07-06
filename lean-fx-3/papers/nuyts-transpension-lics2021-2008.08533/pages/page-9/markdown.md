Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:9

$\text{mer}[u] a : \Diamond[u] A$ then lives in telescope $\Delta$, which extends $\Gamma, u : \mathbb{U}$. Thus, we remark that both $\Diamond[u] A$ and $\text{mer}[u] a$ depend on $u$, whereas $A$ and $a$ do not, so in a way the transpension lifts data to a higher dimension, turning points into $\mathbb{U}$-cells.

The type formation rule FF:TRANSP is parallel to the modal type formation rule of MTT (WDRA in Fig. 4), which internalizes a (weak) dependent right adjoint; its premises are such that the introduction rule is well-typed.

The elimination rule FF:TRANSP:ELIM is equivalent to the existence of the function

$$\lambda f.\text{unmer}(u.f u) : (\forall u.\Diamond[u] A) \to A,$$

which is essentially the co-unit of the adjunction; this differs from the elimination rule of MTT (WDRA:ELIM in Fig. 4) which works by pattern-matching, but is parallel to the projection function in Proposition 3.3, as are the $\beta$- and $\eta$-rules which internalize the adjunction laws and to which we get back in Section 2.1.6. The elimination rule takes data again to a lower dimension: it turns a dependent $\mathbb{U}$-cell in the transpension into a point in $A$.

2.1.4. Admissibility of telescope rules. The typing rules for the transpension type rely on the unusual notions of telescope quantification and application, which remain to be discussed. Before doing so, we remark that one can take either of two viewpoints w.r.t. these rules. One can take a syntactic viewpoint, viewing each of the typing rules concerned as a formal typing rule, i.e. as a constructor of our generalized algebraic syntax [Car86, Car78, AK16]. Alternatively, it is possible to prove metatheoretically that each of these rules is admissible, by defining $\forall u.(\delta : \Delta)$ as a telescope of the same length as $\Delta$, but where each variable's type is universally quantified over $u : \mathbb{U}$. This latter view is the one that inspires most of our notations, but we make a point of not violating the former possibility, because that one allows a pseudo-embedding$^4$ of the current specialized system in the main system of this paper (Section 7).

2.1.5. Telescope quantification. Given a context $\Gamma, u : \mathbb{U}, \delta : \Delta$ with no shape variables in $\Delta$, the rule FF:CTX-FORALL creates a new context $\Gamma, \forall u.(\delta : \Delta)$, which is just $\Gamma$ again if $\Delta$ has zero variables (FF:CTX-FORALL:NIL). From the syntactic viewpoint, it would perhaps be cleaner to write something like $[\forall u](\Gamma, u : \mathbb{U}, \delta : \Delta)$, or more generally $[\forall u]\Theta$ for any context $\Theta$ featuring $u : \mathbb{U}$ as its last shape variable. However, the notation we have chosen is possible since every such context is of the form $\Theta = \Gamma, u : \mathbb{U}, \delta : \Delta$ for some context $\Gamma$ and telescope $\Delta$, and moreover it is justified by the admissibility proof as well as in the following sense:

(1) The variables in $\Gamma$ can be accessed in context $[\forall u](\Gamma, u : \mathbb{U}, \delta : \Delta)$,
(2) For every variable $y : B$ in $\Delta$, we get a term of type $\forall v.B[\sigma]$ in context $[\forall u](\Gamma, u : \mathbb{U}, \delta : \Delta)$ (for a suitable substitution $\sigma$).

To see (1), we make use of the functoriality rule FF:CTX-FORALL:FMAP, which from the syntactic viewpoint we could more cleanly write as $[\forall(u/u')]\rho : [\forall u]\Theta \to [\forall u']\Theta'$ for $\rho : \Theta \to \Theta'$. The alternative notation in the typing rule is again possible since any such $\rho$ is of the form $\rho = (\sigma, u/u', \tau/\delta')$ for some $\sigma : \Gamma \to \Gamma'$ and well-typed vector of terms $\tau$, and justified for similar reasons as above. By applying functoriality to the weakening substitution $(\Gamma, u : \mathbb{U}, \delta : \Delta) \to (\Gamma, u : \mathbb{U})$, we get a substitution $(\Gamma, \forall u.(\delta : \Delta)) \to (\Gamma, \forall u.()) = \Gamma$, which we can use to ignore $\forall u.(\delta : \Delta)$ altogether and thus get access to the variables in context $\Gamma$.

$^4$Pseudo, because FF:CTX-FORALL:NIL is only an isomorphism in the general system, but that would undidactically complicate notations in the current section.