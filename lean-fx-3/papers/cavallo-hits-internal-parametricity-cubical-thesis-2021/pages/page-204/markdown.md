192

Programming with parametricity

the cubical language does contain terms that evaluate by case analysis on types, namely the Kan operators coe and hcom. Indeed, nothing prevents us from including a general type-case operator in the language; it will simply fail to be well-typed if used in a non-parametric way. In short, our parametricity is not a syntactic condition, but a semantic one. Indeed, the fact that $\lambda A.\lambda t.\lambda f.\mathrm{coe}^{0\to 1}_{-A}(t)$ can be given the type $\mathbb{B}$ reflects the fact that coe is defined on all elements of the universe, in particular Gel types, and so must behave parametrically.

## 10.2 The relativity principle

For our next trick, we prove the relativity principle (Definition 9.4.1): the isomorphism between bridges in the universe and relations, the equivalent of the univalence principle for bridges. Like univalence, it is rare that we need the principle in all its strength: as in the previous sections, we usually only use the ability to turn a relation into a bridge, which is to say the Gel type former. Nevertheless, it forms the conceptual backbone of the system.

Notation 10.2.1. Given a relation $R \in A \times B \to \mathrm{U}$ valued in some universe, we abbreviate the type $\operatorname{Gel}_r(A, B, a.b.R\langle a, b\rangle) \in \mathrm{U}$ as $\operatorname{Gel}_r(A, B, R)$.

One thing to notice in the following proof is its reliance on function extensionality and univalence. To prove an isomorphism between $\operatorname{Bridge}(\mathrm{U}, A, B)$ and $A \times B \to \mathrm{U}$, we necessarily must prove path equations in function types and the universe. In particular, it is essential that we can turn the isomorphism $\operatorname{Bridge}(\boldsymbol{x}.\operatorname{Gel}_x(A, B, R), a, b) \simeq R\langle a, b\rangle$ into a path; this is one of the inverse conditions for the main relativity isomorphism. The argument to come would not, therefore, go through in a type theory built on ITT rather than cubical type theory. To avoid the issue in their own formalism, Bernardy, Coquand, and Moulin therefore impose this as an exact equation, $\operatorname{Bridge}(\boldsymbol{x}.\operatorname{Gel}_x(A, B, R), a, b) = R\langle a, b\rangle$ type, as discussed in Remark 9.4.5.

Lemma 10.2.2 (Bridges in an isomorphism type). Let $\boldsymbol{x}: \mathrm{I} \gg A, B$ type be given together with isomorphisms $i_0: A[\mathbf{0}/\boldsymbol{x}] \simeq B[\mathbf{0}/\boldsymbol{x}]$ and $i_1: A[\mathbf{1}/\boldsymbol{x}] \simeq B[\mathbf{1}/\boldsymbol{x}]$. Then we have an isomorphism of the following type.

$$\operatorname{Bridge}(\boldsymbol{x}.A \simeq B, i_0, i_1)$$

$$\simeq$$

$$((a_0: A[\mathbf{0}/\boldsymbol{x}]) (a_1: A[\mathbf{1}/\boldsymbol{x}]) \to \operatorname{Bridge}(\boldsymbol{x}.A, a_0, a_1) \simeq \operatorname{Bridge}(\boldsymbol{x}.B, i_0 a_0, i_1 a_1))$$

Proof. The type of isomorphisms (Definition 1.2.1) is defined using product, function, and path types. We already have characterizations of bridges in each of these types