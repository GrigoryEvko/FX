**Construction 2.12.** At the beginning of the section, we have briefly called the language $\mathcal{L}_{\lambda,\kappa}^{T}$ before dropping the $\kappa$ from the notation, as it can be read from the fact that $T$ is a generalized $\kappa$-algebraic theory. However, we can consider $\mathcal{L}_{\lambda,\kappa'}^{T}$ for any $\kappa' \geqslant \kappa$. Indeed, given $T$ a generalized $\kappa$-algebraic theory, we can define a generalized $\kappa'$-algebraic theory $T_{\kappa'}$ by taking a set of axioms for $T$ and seeing them as axioms for a generalized $\kappa'$-algebraic theory. A model of $T_{\kappa'}$ is the same as a model of $T$. We then define

$$\mathcal{L}_{\lambda,\kappa'}^{T} := \mathcal{L}_{\lambda,\kappa'}^{T_{\kappa'}} = \mathcal{L}_{\lambda}^{T_{\kappa'}},$$

as well as its quotient

$$\mathbb{L}_{\lambda,\kappa'}^{T} := \mathbb{L}_{\lambda,\kappa'}^{T_{\kappa'}} = \mathbb{L}_{\lambda}^{T_{\kappa'}}.$$

**Example 2.13.** Let $\Sigma$ be a signature in the sense of traditional model theory, that is a set of formal symbols for types, functions and relations. Then we can consider the generalized algebraic theory $T_{\Sigma,=}$, which has one type in the empty context of each sort symbol $X$ in the signature. Each of these types have an equality predicate as the one constructed in theorem 2.4, a term for each function symbol, and for each relation symbol $R \subset X_1, \ldots, X_n$ a type axiom

$$x_1 : X_1, \ldots, x_n : X_n \vdash R(x_1, \ldots, x_n) \text{Type}$$

with the additional axiom

$$x_1 : X_1, \ldots, x_n : X_n, t_1, t_2 : R(x_1, \ldots, x_n) \vdash t_1 = t_2.$$

Models of this theory are exactly $\Sigma$-structures, and elements of $\mathbb{L}_{\omega,\omega}^{T_{\Sigma,=}}$ are essentially the same as usual first-order formulas in this signature. Elements of $\mathbb{L}_{\lambda,\kappa}^{T_{\Sigma,=}}$ correspond to infinitary first-order formulas using $\lambda$-small conjunction and disjunction and where $\exists$ and $\forall$ quantifiers can quantify over $\kappa$-small set of variables.

## 2.2 Categories of models and their weak factorization systems

In this section and the next we will abstract the notion of the first-order language of a generalized algebraic theory in terms of its category of models, this will allow us to generalize this notion of language to an arbitrary category. To be more precise, we will abstract it terms in terms of the category of models together with a certain weak factorization system we will introduce in this section, and in the next section we will generalize this to an arbitrary category equipped with a weak factorization system.

14