- Being a central lifting, \(\Omega_{(\in \partial U)}^{\Psi \ltimes \partial U|}\) is a CwF morphism and can be applied to \(B\), yielding a type in context

\[
\begin{array}{l} \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \left(\Gamma . \left(\mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right]\right) = \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \Gamma . \left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right] \\ \cong \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \Gamma . \top , \\ \end{array}
\]

where the isomorphism is an application of theorem 4.4.4. The substitution \((\mathrm{id},\_) = \pi^{-1}\) yields a type in context \(\Omega_{(\in \partial U)}^{\Psi \ltimes \partial U|}\Gamma\). We assume that \(b_{\partial}\) has this type.

- Being a central lifting, \(\forall_{\mathbf{y}U}^{\Psi|}\) is a CwF morphism and can be applied to \(B\), yielding a type in context

\[
\forall_ {\mathbf {y} U} ^ {\Psi |} \left(\Gamma . \left(\mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right]\right) = \forall_ {\mathbf {y} U} ^ {\Psi |} \Gamma . \left(\forall_ {\mathbf {y} U} ^ {\Psi |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right].
\]

The natural transformation \((\mathrm{unmerid}_{\mathbf{y}U}^{\Psi|})^{-1}\) gives rise [Nuy18] to a function

\[
\left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1}: A \rightarrow \left(\forall_ {\mathbf {y} U} ^ {\Psi |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right)\left[\left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} \right]. \tag {46}
\]

Now, by the adjunction laws, \(\forall_{\mathbf{y}U}^{\Psi |}\mathrm{reidx}_{\mathbf{y}U}^{\Psi |}\circ \mathrm{unmerid}_{\mathbf{y}U}^{\Psi |} = \mathrm{id},\) so

\[
\forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} = \forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \circ \operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |} \circ \left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} = \left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1}. \tag {47}
\]

Then we have

\[
\left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1}: A \rightarrow \left(\forall_ {\mathbf {y} U} ^ {\Psi |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right)\left[ \forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right]. \tag {48}
\]

Thus, we can substitute \(\forall_{\mathbf{y}U}^{\Psi |}B\) with \((\pi ,(\mathrm{unmerid}_{\mathbf{y}U}^{\Psi |})^{-1}(\xi))\), yielding a type in the desired context. We assume that \(\hat{b}\) has this type.

- In the coherence criterion, we have applied operations to \( b_{\partial} \) and \( \hat{b} \) before equating them. We have to ensure that the resulting terms are well-typed in the given context and type.

- If we apply \(\exists_{\mathbf{y}U}^{\Psi|}\) to the term \(\hat{b}\), we get

\[
\Psi \ltimes \mathbf {y} U \mid \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \Gamma\right). \exists_ {\mathbf {y} U} ^ {\Psi |} A \vdash^ {\exists_ {\mathbf {y} U} ^ {\Psi |}} \hat {b}: \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} B\right) \left[ \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right].
\]

If we subsequently apply app \( _{yU}^{\Psi|} \) , we get

\[
\Psi \ltimes \mathbf {y} U \mid \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \Gamma\right). \exists_ {\mathbf {y} U} ^ {\Psi |} A \vdash \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \hat {b}\right): B \left[ \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] \left[ \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right].
\]

Next, we apply \(\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y}U|}\) and obtain something of type

\[
\left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} B\right) \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right].
\]

Now if we look at the context of \(\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y}U|}B\), we see that the last type is the unit type by theorem 4.4.4, so the substitution applied to \(B\) is determined by its weakening. So we rewrite:

\[
\begin{array}{l} \dots = \left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} B\right) [ (\mathrm{id}, \_) ] [ \pi ] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right] \\ = \left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} B\right) [ (\mathrm{id}, \_) ] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] [ \pi ] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right] \\ \end{array}
\]

37