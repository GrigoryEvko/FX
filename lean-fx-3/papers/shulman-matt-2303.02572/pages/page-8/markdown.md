18–8

Semantics of multimodal adjoint type theory

Proof. The limits, and colimits in (i), are defined pointwise. For (ii), an oplax limit is the category of coalgebras for a finitely continuous comonad on a product category (see [42] or [19, B3.4.6]), and the stated properties are closed under products and such coalgebras (e.g. [19, A4.2.1]). For (iii), by [30, Theorem 5.1.6] accessible categories and functors are closed under limits, and an accessible category is locally presentable if and only if it is cocomplete. For (iv), we use (ii) and (iii), since Grothendieck topoi are the locally presentable elementary topoi [19, C2.2.8], and left and right adjoints are accessible. \(\square\)

Lemma 4.6 For \(\varpi : r \to s\), the functor \(\mathsf{L}^{\varpi} : \widehat{\mathcal{C}}_s \to \mathcal{C}_r\) has a right adjoint, which we write \(\mathbf{R}_{\varpi}\).

Proof. Given \(\Gamma \in \mathcal{C}_r\), we must first define \((\mathbf{R}_{\varpi}\Gamma)^{\nu} \in \mathcal{C}_p\) for any \(\nu : p \to s\). Let \((\varpi \downarrow (\nu \circ -))\) be the category of pairs \((\sigma : r \to p, \beta : \varpi \Rightarrow \nu \circ \sigma)\). Any such \((\sigma, \beta)\) induces an object \(\mathcal{C}_{\sigma}(\Gamma) \in \mathcal{C}_p\); we define

\[
(\mathbf {R} _ {\varpi} \Gamma) ^ {\nu} = \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\nu \circ -))} \mathcal {C} _ {\sigma} (\Gamma).
\]

Now suppose given also \(\varrho : p \to q\) and \(\alpha : \mu \Rightarrow \nu \circ \varrho\). Then \((\mathbf{R}_{\varpi}\Gamma)^{\alpha}\) should be a morphism

\[
(\mathbf {R} _ {\varpi} \Gamma) ^ {\nu} = \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\nu \circ -))} \mathcal {C} _ {\sigma} (\Gamma) \longrightarrow \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\mu \circ -))} \mathcal {C} _ {\varrho} \mathcal {C} _ {\sigma} (\Gamma) \stackrel {{\cong}} {{\to}} \mathcal {C} _ {\varrho} ((\mathbf {R} _ {\varpi} \Gamma) ^ {\mu}).
\]

If \((\sigma, \beta) \in (\varpi \downarrow (\mu \circ -))\) indexes a factor \(\mathcal{C}_{\varrho} \mathcal{C}_{\sigma}(\Gamma)\) of this codomain, then \((\varrho \circ \sigma, (\alpha \triangleright \sigma) \circ \beta) \in (\varpi \downarrow (\nu \circ -))\), and the factor \(\mathcal{C}_{\varrho \circ \sigma}(\Gamma)\) of the domain is isomorphic to \(\mathcal{C}_{\varrho} \mathcal{C}_{\sigma}(\Gamma)\). Thus, this determines a map \((\mathbf{R}_{\varpi} \Gamma)^{\alpha}\) between the limits. This defines \(\mathbf{R}_{\varpi} \Gamma \in \widehat{\mathcal{C}}_s\). Now we observe that

\[
(\mathbf {R} _ {\varpi} \Gamma) ^ {\varpi} = \lim _ {(\sigma , \beta) \in (\varpi \downarrow (\varpi \circ -))} \mathcal {C} _ {\sigma} (\Gamma).
\]

Since \((1_r, 1_\varpi) \in (\varpi \downarrow (\varpi \circ -))\), with \(\mathcal{C}_{1_r}(\Gamma) \cong \Gamma\), there is a projection \(\epsilon_\Gamma : (\mathbf{R}_\varpi \Gamma)^\varpi \to \Gamma\). We claim this is a universal arrow from \(\mathsf{L}^\varpi\). For \(\Delta \in \widehat{\mathcal{C}}_s\), a map \(\theta : \Delta \to \mathbf{R}_\varpi \Gamma\) consists of, for any \(\nu : p \to r\) and any \((\sigma, \beta) \in (\varpi \downarrow (\nu \circ -))\), a morphism \(\theta^{\nu, (\sigma, \beta)} : \Delta^\nu \to \mathcal{C}_\sigma \Gamma\), such that for any \(\alpha : \mu \Rightarrow \nu \circ \varrho\) and \(\beta : \varpi \Rightarrow \mu \circ \sigma\):

\[
\begin{array}{c} \boldsymbol {\Delta} ^ {\nu} \xrightarrow {\boldsymbol {\Delta} ^ {\alpha}} \mathcal {C} _ {\varrho} (\boldsymbol {\Delta} ^ {\mu}) \\ \left( \begin{array}{c c c} \mathcal {C} _ {\varrho} (\boldsymbol {\theta} ^ {\nu}) & & \boldsymbol {\theta} ^ {\mu} \\ \downarrow & & \downarrow \\ (\mathbf {R} _ {\varpi} \Gamma) ^ {\nu} & \xrightarrow {(\mathbf {R} _ {\varpi} \Gamma) ^ {\alpha}} & \mathcal {C} _ {\varrho} ((\mathbf {R} _ {\varpi} \Gamma) ^ {\mu}) \\ \downarrow & & \downarrow \\ \mathcal {C} _ {\varrho \circ \sigma} \Gamma & \xrightarrow {\cong} & \mathcal {C} _ {\varrho} \mathcal {C} _ {\sigma} \Gamma . \end{array} \right) \boldsymbol {\theta} ^ {\mu , (\sigma , \beta)} \end{array}
\]

Taking \(\nu = \varpi\) and \(\sigma = 1_r\) with \(\beta = 1_{\varpi}\) yields the composite \(\Delta^{\varpi} \xrightarrow{\theta^{\varpi}} (\mathbf{R}_{\varpi}\Gamma)^{\varpi} \xrightarrow{\epsilon_{\Gamma}} \Gamma\). Moreover, if in the above condition we take \(\mu = \varpi\) with \((\sigma, \beta) = (1_r, 1_{\varpi})\), then the left-hand vertical composite becomes \(\theta^{\nu, (\varrho, \alpha)}\), which is fully general; thus all the components of \(\theta\) are determined by \(\theta^{\varpi, (1_r, 1_{\varpi})}\).

Now, given \(\vartheta : \Delta^{\varpi} \to \Gamma\), for any \(\nu\) and \((\sigma, \beta)\) we have a composite \(\Delta^{\nu} \xrightarrow{\Delta^{\beta}} \mathcal{C}_{\sigma}(\Delta^{\varpi}) \xrightarrow{\mathcal{C}_{\sigma}(\vartheta)} \mathcal{C}_{\sigma}\Gamma\). The above compatibility condition follows from the axioms of Definition 4.3, so we have a map \(\Delta \to \mathbf{R}_{\varpi}\Gamma\). Its underlying map \(\Delta^{\varpi} \to \Gamma\) is \(\Delta^{\varpi} \xrightarrow{\Delta^{1_{\varpi}}} \mathcal{C}_{1_r}(\Delta^{\varpi}) \xrightarrow{\mathcal{C}_{1_{\varpi}}(\vartheta)} \mathcal{C}_{1_{\varpi}}\Gamma \cong \Gamma\), which is equal to \(\vartheta\).

When \(\varpi = 1_r\), we write \(\mathsf{L}^r = \mathsf{L}^{1_r}\) and \(\mathbf{R}_r = \mathbf{R}_{1_r}\).

Lemma 4.7 The functor \(\mathbf{R}_r:\mathcal{C}_r\to \widehat{\mathcal{C}}_r\) is fully faithful.