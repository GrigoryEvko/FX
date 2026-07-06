Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:49

$\Psi \Vdash \varepsilon(\Psi) := (\mathrm{id}_{\Psi}, \varepsilon / \boldsymbol{x}) \in (\Psi, \boldsymbol{x} : \mathbf{I})$ induces a corresponding transformation $\varepsilon_{!} : Id \to (-\otimes \mathbf{I})$ in the presheaf category interpreting the endpoint substitution SUBST-FACE.

6.3. Type and term formers. To interpret the rules for forming types and terms—Bridge-types, Gel-types, and extent—it is useful to observe that the semantic judgments, like the computational ones in Section 4, are determined by their instantiations at interval contexts (i.e., representables). For example, a semantic type $T$ in context $G$ is determined by the types $g^{*}T$ for $g : \not\cong\Psi \to G$: recalling that the Yoneda lemma identifies morphisms $g : \not\cong\Psi \to G$ with elements $g \in G(\Psi)$, we have as we have $T(\Psi, g) = (g^{*}T)(\Psi, \mathrm{id}_{\Psi})$. Conversely, if we have a family of types $T_{g}$ over $\not\cong\Psi$ for every $g : \not\cong\Psi \to G$ such that $(\not\cong\psi)^{*}T_{g} = T_{g \circ \not\cong\psi}$ for all $\Psi' \Vdash \psi \in \Psi$, then this determines a type $T$ over $G$: take $T(\Psi, g) := T_{g}(\Psi, \mathrm{id}_{\Psi})$. A similar principle applies to terms.

The upshot is that we may verify that rules hold in an arbitrary context by showing they hold (naturally) in any interval context, as we did for the computational interpretation in Section 4.5. In the restricted case we may take advantage of the characterizations $Res_{!}(\not\cong\Psi, \boldsymbol{r}) \cong \not\cong(\Psi \backslash \boldsymbol{r})$ and $Ext_{!}(\not\cong\Psi) \cong \not\cong(\boldsymbol{x}/\boldsymbol{x}) : \not\cong(\Psi, \boldsymbol{x} : \mathbf{I}) \to \not\cong(\boldsymbol{x} : \mathbf{I})$, saving us from formal reasoning with the general Kan extension.

**Theorem 6.12.** $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ is closed under Bridge-pretypes.

*Proof.* Per the argument above, we narrow our attention without loss of generality to the cases where the ambient context is representable.

$\triangleright$ *Formation.*

Let a semantic pretype $T$ in context $\not\cong\Psi \otimes \mathbf{I} \cong \not\cong(\Psi, \boldsymbol{x} : \mathbf{I})$ be given together with endpoint elements $t_{0}$ of $\not\cong(\mathbf{0}/\boldsymbol{x})^{*}T$ and $t_{1}$ of $\not\cong(\mathbf{1}/\boldsymbol{x})^{*}T$. We define a semantic pretype $Bridge(T, t_{0}, t_{1})$ over $\not\cong\Psi$ as follows.

$$Bridge(T, t_{0}, t_{1})(\Psi', \psi) := \{a \in T((\Psi', \boldsymbol{x} : \mathbf{I}), (\psi, \boldsymbol{x}/\boldsymbol{x})) \mid \forall \varepsilon. T(\varepsilon/\boldsymbol{x})(a) = t_{\varepsilon}(\Psi', \psi)\}$$

That is, an element of $Bridge(T, t_{0}, t_{1})$ in context $\Psi'$ is an element of $T$ in context $(\Psi', \boldsymbol{x} : \mathbf{I})$ with the requested endpoints. The action of $Bridge(T, t_{0}, t_{1})$ on substitutions is likewise defined from the action of $T$ in the natural way.

$\triangleright$ *Introduction.*

Similarly, given a semantic element $t$ of $T$ such that $\not\cong(\mathbf{1}/\boldsymbol{x})^{*}t = t_{0}$ and $\not\cong(\mathbf{1}/\boldsymbol{x})^{*}t = t_{1}$, we have an abstracted element $lam^{\mathbf{I}}(t)$ of $Bridge(T, t_{0}, t_{1})$ defined as follows.

$$lam^{\mathbf{I}}(t)(\Psi, g) := t((\Psi, \boldsymbol{x} : \mathbf{I}), (\psi, \boldsymbol{x}/\boldsymbol{x}))$$

$\triangleright$ *Elimination.*

To interpret application, we assume now that we have some $\boldsymbol{r} : \not\cong\Psi \to \not\cong(\Psi, \boldsymbol{x} : \mathbf{I})$ and that the pretype $T$ lies in context $Res_{!}(\not\cong\Psi, \boldsymbol{r}) \otimes \mathbf{I} \cong \not\cong(\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I})$. Given an element $u$ of $Bridge(T, t_{0}, t_{1})$,

$$app^{\mathbf{I}}(u)(\Psi', \psi) := T(\boldsymbol{r}\psi/\boldsymbol{x})(u(\Psi' \backslash \boldsymbol{r}\psi, \psi \backslash \boldsymbol{r}))$$

Here $\Psi' \backslash \boldsymbol{r}\psi \Vdash \psi \backslash \boldsymbol{r} \in \Psi \backslash \boldsymbol{r}$ is the functorial action of restriction on $\psi$. By definition of the bridge type, the term $u(\Psi' \backslash \boldsymbol{r}\psi, \psi \backslash \boldsymbol{r})$ is an element of $T((\Psi' \backslash \boldsymbol{r}\psi, \boldsymbol{x} : \mathbf{I}), (\psi \backslash \boldsymbol{r}, \boldsymbol{x}/\boldsymbol{x}))$; applying $T(\boldsymbol{r}\psi/\boldsymbol{x})$ thus gives an element of $T(\Psi', \psi)$.

We leave it to the reader to check that these definitions are natural and that the $\beta$-, $\eta$-, and boundary rules are satisfied. $\square$