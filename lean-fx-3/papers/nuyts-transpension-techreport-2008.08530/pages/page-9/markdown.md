and every pullback diagram in a presheaf category is isomorphic to a diagram of this form. We have the following commutation properties:

|   | \( \Sigma_B \) | \( \Omega_B \) | \( \Pi_B \) | \( \S_B \)  |
| --- | --- | --- | --- | --- |
|  \( \Sigma_A \) | \( \Sigma^{\alpha}|\Sigma^{\beta'}| \cong \Sigma^{\beta}|\Sigma^{\alpha'}| \) | \( \Sigma^{\alpha'}|\Omega^{\beta'}| \cong \Omega^{\beta}|\Sigma^{\alpha}| \) | \( \Sigma^{\alpha}|\Pi^{\beta'}| \to \Pi^{\beta}|\Sigma^{\alpha'}| \) |   |
|  \( \Omega_A \) | \( \Omega^{\alpha}|\Sigma^{\beta}| \cong \Sigma^{\beta'}|\Omega^{\alpha'}| \) | \( \Omega^{\alpha'}|\Omega^{\beta}| = \Omega^{\beta'}|\Omega^{\alpha}| \) | \( \Omega^{\alpha}|\Pi^{\beta}| \cong \Pi^{\beta'}|\Omega^{\alpha'}| \) | \( \Omega^{\alpha'}|\S^{\beta}| \to \S^{\beta'}|\Omega^{\alpha}| \)  |
|  \( \Pi_A \) | \( \Pi^{\alpha}|\Sigma^{\beta'}| \leftarrow \Sigma^{\beta}|\Pi^{\alpha'}| \) | \( \Pi^{\alpha'}|\Omega^{\beta'}| \cong \Omega^{\beta}|\Pi^{\alpha}| \) | \( \Pi^{\alpha}|\Pi^{\beta'}| \cong \Pi^{\beta}|\Pi^{\alpha'}| \) | \( \Pi^{\alpha'}|\S^{\beta'}| \cong \S^{\beta}|\Pi^{\alpha}| \)  |
|  \( \S_A \) |  | \( \S^{\alpha'}|\Omega^{\beta}| \leftarrow \Omega^{\beta'}|\S^{\alpha}| \) | \( \S^{\alpha}|\Pi^{\beta}| \cong \Pi^{\beta'}|\S^{\alpha'}| \) | \( \S^{\alpha'}|\S^{\beta}| \cong \S^{\beta'}|\S^{\alpha}| \)  |

where every statement holds if the mentioned functors exist.

Proof. In the base category, it is evident that \(\Sigma^{\prime \alpha}\Sigma^{\prime \beta^{\prime}} = \Sigma^{\prime \beta}\Sigma^{\prime \alpha^{\prime}}\). By applying the functor \(\sqcup^{*}\), we obtain \(\Omega^{\alpha^{\prime}}|\Omega^{\beta}| = \Omega^{\beta^{\prime}}|\Omega^{\alpha}|\), whence by lemma 2.1.2 the entire diagonal of the commutation table.

It is a well-known fact that \(\Sigma\)- and \(\Pi\)-types are respected by substitution, which gives us the isomorphisms for swapping \(\Omega\) and either \(\Sigma\) or \(\Pi\). Lemma 2.1.2 then gives the rest.

Theorem 2.3.19. Given \(\sigma : \Psi' \to \Psi\), the following operations are invertible:

\[
\frac {\Psi \mid \Sigma^ {\sigma} | \Gamma \vdash T \text {type}}{\Psi^ {\prime} \mid \Gamma \vdash (\Omega^ {\sigma} | T) [ \mathsf {c o p y} ^ {\sigma} | ] \text {type}} \quad \frac {\Psi \mid \Sigma^ {\sigma} | \Gamma \vdash t : T}{\Psi^ {\prime} \mid \Gamma \vdash (\Omega^ {\sigma} | t) [ \mathsf {c o p y} ^ {\sigma} | ] : (\Omega^ {\sigma} | T) [ \mathsf {c o p y} ^ {\sigma} | ]} \tag {13}
\]

Proof. Note that \( T \) is a presheaf over \( (\mathcal{W} / \Psi) / \Sigma^{\sigma}|\Gamma \), and \( (\Omega^{\sigma}|T)[\mathrm{copy}^{\sigma}] \) is a presheaf over \( (\mathcal{W} / \Psi') / \Gamma \). We compare the objects of these categories:

\[
\operatorname{Obj} \left(\left(\mathcal {W} / \Psi\right) / \Sigma^ {\sigma} \mid \Gamma\right)
\]

\[
= (W \in \mathcal {W}) \times (\psi : W \Rightarrow \Psi) \times \exists ((W ^ {\prime}, \psi^ {\prime}) \in \mathcal {W} / \Psi^ {\prime}. (\chi : (W, \psi) \rightarrow \Sigma^ {\prime \sigma} (W ^ {\prime}, \psi^ {\prime})) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong (W \in \mathcal {W}) \times (\psi : W \Rightarrow \Psi) \times \exists W ^ {\prime}. (\psi^ {\prime}: W ^ {\prime} \Rightarrow \Psi^ {\prime}) \times (\chi : (W, \psi) \rightarrow \Sigma^ {\prime \sigma} (W ^ {\prime}, \psi^ {\prime})) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong (W \in \mathcal {W}) \times (\psi : W \Rightarrow \Psi) \times \exists W ^ {\prime}. (\psi^ {\prime}: W ^ {\prime} \Rightarrow \Psi^ {\prime}) \times (\chi : (W, \psi) \rightarrow (W ^ {\prime}, \sigma \circ \psi^ {\prime})) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong (W \in \mathcal {W}) \times \exists W ^ {\prime}. (\psi^ {\prime}: W ^ {\prime} \Rightarrow \Psi^ {\prime}) \times (\chi : W \rightarrow W ^ {\prime}) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

because \(\chi\) is a slice morphism iff \(\psi = \sigma \circ \psi' \circ \chi\)

\[
\cong (W \in \mathcal {W}) \times (\psi^ {\prime}: W \Rightarrow \Psi^ {\prime}) \times ((W, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong \operatorname{Obj} \left(\left(\mathcal {W} / \Psi^ {\prime}\right) / \Gamma\right).
\]

A similar consideration of the Hom-sets leads to the conclusion that both categories are isomorphic. Moreover, we remark that the isomorphism sends  \( ((W,\psi'),\gamma) \)  on the right to  \( ((W,\sigma\circ\psi'),\Sigma^{\sigma}|\gamma) \)  on the left. When we consider the action of  \( (\Omega^{\sigma}|T)[\mathsf{copy}^{\sigma}] \)  on  \( ((W,\psi'),\gamma) \) , we find:

\[
\left((W, \psi^ {\prime}) \triangleright (\Omega^ {\sigma} | T) [ \mathsf {c o p y} ^ {\sigma} | ] [ \gamma \rangle\right) = \left(\Sigma^ {\prime \sigma} (W, \psi^ {\prime}) \triangleright T \Big [ \Sigma^ {\sigma} | \gamma \Big \rangle\right)
\]

\[
= \left(\left(W, \sigma \circ \psi^ {\prime}\right) \triangleright T \left[ \Sigma^ {\sigma} | \gamma \right\rangle\right)
\]

In other words, the types \( T \) and \( (\Omega^{\sigma}|T)[\mathrm{copy}^{\sigma}] \) are equal over an isomorphism of categories. Then certainly \( T \) can be retrieved from \( (\Omega^{\sigma}|T)[\mathrm{copy}^{\sigma}] \). An identical argument works for terms.

#### 2.3.6 Reconstructing right adjoints

Proposition 2.3.20. Given a left adjoint functor \( L: \widehat{\mathcal{W}} \to \mathcal{C} \), we can construct a right adjoint \( R_L: \mathcal{C} \to \widehat{\mathcal{W}} \) without using the axiom of choice.

Proof. Define  \( (W \Rightarrow R_{L}\Gamma) := (L\mathbf{y}W \to \Gamma) \) . As a matter of notational hygiene, write  \( \alpha_{L} : (L\mathbf{y}W \to \Gamma) \to (W \Rightarrow R_{L}\Gamma) \)  for the identity function. Define restriction by  \( \alpha_{L}(\gamma) \circ \varphi = \alpha_{L}(\gamma \circ L\mathbf{y}\varphi) \)  and the functorial action by  \( R_{L}\sigma \circ \alpha_{L}(\gamma) = \alpha_{L}(\sigma \circ \gamma) \) . This is a well-defined presheaf functor.

Now we show that \( L \dashv R_L \). Since \( L \) is a left adjoint, it has a right adjoint \( R \). We have natural isomorphisms

\[
(W \Rightarrow R _ {L} \Gamma) = (L \mathbf {y} W \rightarrow \Gamma) \cong (\mathbf {y} W \rightarrow R \Gamma) \cong (W \Rightarrow R \Gamma)
\]

so that  \( R_{L} \)  is naturally isomorphic to R and indeed right adjoint to L.

□

9