### 4.3 Four adjoint functors

Unlike the slice category \(\widehat{\mathcal{W}} / \Psi\), the equivalent category \(\widehat{\mathcal{W} / \Psi}\) is a presheaf category and therefore immediately a model of dependent type theory. Therefore, we prefer to work with that category, and to use the corresponding functors:

Definition 4.3.1. The adjoint functors \(\exists_{U}^{\prime \Psi}\dashv \exists_{U}^{\prime \Psi}\) give rise to four adjoint functors between presheaf categories over slice categories, which we denote

\[
\exists_ {\mathbf {y} U} ^ {\Psi |} \dashv \exists_ {\mathbf {y} U} ^ {\Psi |} \dashv \forall_ {\mathbf {y} U} ^ {\Psi |} \dashv \delta_ {\mathbf {y} U} ^ {\Psi |}. \tag {39}
\]

We call the fourth functor transpension.

The units and co-units will be denoted:

\[
\begin{array}{l} \operatorname{copy} _ {\mathbf {y} U} ^ {\Psi |}: \quad \operatorname{Id} \rightarrow \exists_ {\mathbf {y} U} ^ {\Psi |} \exists_ {\mathbf {y} U} ^ {\Psi |} \\ \operatorname{const} _ {\mathbf {y} U} ^ {\Psi |}: \quad \operatorname{Id} \rightarrow \forall_ {\mathbf {y} U} ^ {\Psi |} \exists_ {\mathbf {y} U} ^ {\Psi |} \\ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |}: \quad \operatorname{Id} \rightarrow \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \\ \operatorname{drop} _ {\mathbf {y} U} ^ {\Psi |}: \exists_ {\mathbf {y} U} ^ {\Psi |} \exists_ {\mathbf {y} U} ^ {\Psi |} \rightarrow \operatorname{Id} \\ \operatorname{app} _ {\mathbf {y} U} ^ {\Psi |}: \quad \exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \rightarrow \operatorname{Id} \\ \operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}: \quad \forall_ {\mathbf {y} U} ^ {\Psi |} \delta_ {\mathbf {y} U} ^ {\Psi |} \rightarrow \operatorname{Id} \\ \end{array}
\]

For now, we define all of these functors only up to isomorphism, i.e. for the middle two we do not specify whether they arise as a left, central or right lifting.

Note that, if in a judgement \(\Psi \mid \Gamma \vdash J\), we view the part before the pipe (|) as part of the context, then \(\exists_{\mathbf{y}U}^{\Gamma |}\) and \(\forall_{\mathbf{y}U}^{\Gamma |}\) bind a (substructural) variable of type \(\mathbf{y}U\), whereas \(\exists_{\mathbf{y}U}^{\Gamma |}\) and \(\delta_{\mathbf{y}U}^{\Gamma |}\) depend on one.

It is worth mentioning that, since \(\sqcup \ltimes U = \Sigma_U \exists_U\), the functors in definition 4.0.1 can be (essentially) retrieved as

\[
\sqcup \ltimes \mathbf {y} U = \Sigma_ {\mathbf {y} U} ^ {\top |} \exists_ {\mathbf {y} U} ^ {\top |} \quad \dashv \quad \mathbf {y} U \rightharpoonup \sqcup = \forall_ {\mathbf {y} U} ^ {\top |} \Omega_ {\mathbf {y} U} ^ {\top |} \quad \dashv \quad \mathbf {y} U \vee \sqcup = \Pi_ {\mathbf {y} U} ^ {\top |} \delta_ {\mathbf {y} U} ^ {\top |}. \tag {41}
\]

Corollary 4.3.2. The properties asserted by proposition 4.2.1 for \(\exists_{\mathbf{y}U}^{\prime \Psi}\) also hold for \(\exists_{\mathbf{y}U}^{\Psi}\).

Proof. Follows from the fact that \(\exists_{\mathbf{y}U}^{\Psi} \cong (\exists_{U}^{\prime \Psi})_{1}\), and the observation in proposition 4.2.1 that this functor in turn corresponds to \(\exists_{\mathbf{y}U}^{\prime \Psi}\).

Proposition 4.3.3 (Presheaf functoriality). A morphism of multipliers \(\sqcup \ltimes v: \sqcup \ltimes U \to \sqcup \ltimes U'\) gives rise to natural transformations

- \(\exists_{\mathbf{y}U'}^{\Psi|} \circ \Sigma^{\Psi \ltimes \mathbf{y}v|} \to \exists_{\mathbf{y}U'}^{\Psi}\) (if \(\top\)-slice (hence presheafwise) right-adjoint),
•  \( \Sigma^{\Psi\ltimes\mathbf{y}v|}\circ\exists_{\mathbf{y}U}^{\Psi|}\to\exists_{\mathbf{y}U'}^{\Psi|} \)  and  \( \exists_{\mathbf{y}U}^{\Psi|}\to\Omega^{\Psi\ltimes\mathbf{y}v|}\circ\exists_{\mathbf{y}U'}^{\Psi|} \) ,
•  \( \forall_{yU'}^{\Psi|}\to\forall_{yU'}^{\Psi|}\circ\Omega^{\Psi\ltimes yv|} \)  and  \( \forall_{yU'}^{\Psi|}\circ\Pi^{\Psi\ltimes yv|}\to\forall_{yU'}^{\Psi|} \) ,
•  \( \Pi^{\Psi\ltimes\mathbf{y}v|}\circ\delta_{\mathbf{y}U}^{\Psi|}\to\delta_{\mathbf{y}U'}^{\Psi|} \)

Proof. Follows directly from proposition 4.1.10.

Proposition 4.3.4 (Contextual quantification theorem). If \(\sqcup \ltimes U\) is

1. \(\top\)-slice (or equivalently presheafwise) fully faithful, then \(\mathrm{drop}_{\mathbf{y}U}^{\Psi|}\) (if \(\top\)-slice right adjoint), \(\mathrm{const}_{\mathbf{y}U}^{\Psi|}\) and \(\mathrm{unmerid}_{\mathbf{y}U}^{\Psi|}\) are natural isomorphisms.
2. copointed, then we have

(a)  \( \operatorname{hide}_{\mathbf{y}U}^{\Psi|}:\Sigma_{\mathbf{y}U}^{\Psi|}\to\exists_{\mathbf{y}U}^{\Psi|} \)  (if  \( \top \) -slice, or equivalently presheafwise, right adjoint),

(b)  \( \operatorname{spoil}_{\mathbf{y}U}^{\Psi|}:\exists_{\mathbf{y}U}^{\Psi|}\to\Omega_{\mathbf{y}U}^{\Psi|} \)

32