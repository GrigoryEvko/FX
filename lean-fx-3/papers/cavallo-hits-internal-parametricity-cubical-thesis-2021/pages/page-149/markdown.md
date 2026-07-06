Kan operations 137

Using the fact that $Pcoe^\nu$ is closed under formal coercions, we see that it supports not only parameter coercion but coercion in general.

**Lemma 6.3.17.** $Pcoe^\nu$ supports coercion at $\text{Ind}_{\mathcal{K}\psi}^{\Delta\psi}(\bar{v}_\Delta)$, $\text{Ind}_{\mathcal{K}'\psi}^{\Delta'\psi}(\bar{v}_\Delta)$.

*Proof.* Per Figure 6.6, a coercion in a higher inductive type reduces to a parameter coercion followed by a formal coercion. By Lemma 6.3.8, $Pcoe^\nu$ is closed under parameter coercion, and it is likewise closed under formal coercion by Corollary 6.3.11. $\square$

To coerce a constructor term, we must be able to coerce its arguments. Below, we see that we can coerce in the instantiation relation $\{\Theta\}_{\mathcal{K}}(R)$ induced by a relation $R$ that itself supports coercion.

**Lemma 6.3.18.** Let $\Psi \Vdash \Delta \mid \mathcal{K} \blacktriangleright \Theta = \Theta'$ actx be given. If a $(\Psi, \Delta)$-PER $R$ supports coercion at $\text{Ind}_{\mathcal{K}}^\Delta(\bar{v}_\Delta)$, $\text{Ind}_{\mathcal{K}'}^\Delta(\bar{v}_\Delta)$, then $\{\Theta\}_{\mathcal{K}}(R)$ supports coercion at $(\Theta)_{\mathcal{K}'}^\Delta, (\Theta')_{\mathcal{K}'}^\Delta$.

*Proof.* By induction on the derivation of $\Psi \Vdash \Delta \mid \mathcal{K} \blacktriangleright \Theta = \Theta'$ actx, proving an auxiliary lemma for support of coercion in argument types to handle the successor case. Argument types are built from the inductive family, function types, and path types; the proposition thus follows by the arguments that function and path types are Kan, together with the assumption that $R$ supports coercion at the inductive types. $\square$

Coercion in a constructor term applies coercions to the arguments and wraps the result in the same constructor, but also applies a formal heterogeneous composite (fcom, defined in Figure 6.5) to correct the boundary and index. As with the introduction rules, showing the reduction is well-typed for a constructor $\ell$ requires assuming $Pcoe^\nu$ is closed under the preceding constructors.

**Lemma 6.3.19 (Reduction of pcoe on intro).** Let $\ell \in \mathcal{K}$ be given. Suppose that we have $\text{Intro}_{\ell'}^{\mathcal{K}}(Pcoe^\nu) \subseteq Pcoe^\nu$ for every $\ell'$ with $|\ell'|_{\mathcal{K}} < |\ell|_{\mathcal{K}}$. Then the following rule is validated for any substitution $\Psi', x: \mathbb{I} \Vdash \psi \in \Psi$, terms $\Psi' \Vdash r, s \in \mathbb{I}$, and $\Psi' \Vdash \delta \in \Delta\psi[r/x]$.

$$
\begin{aligned}
(\ell : \Phi.\Omega.\{\delta; \Theta.\overline{\xi_i \hookrightarrow M_i}\}) &\in \mathcal{K}\psi & \Psi' \Vdash \Delta\psi[r/x] \blacktriangleright \mathcal{K}\psi[r/x] = \mathcal{K}' \text{ spec} \\
\Psi' \Vdash \phi &\in \Phi[r/x] & \Psi' \Vdash \omega \in \Omega[r/x]\phi & \chi \in \biguplus \{\{\Theta[r/x][\phi, \omega]\}_{\mathcal{K}}(Pcoe^\nu\psi[r/x]) \\
(\forall t) &\omega^t := \overline{\text{coe}}_{x.\omega\phi}^{r\to t}(\omega) & (\forall t) &\chi^t := \overline{\text{coe}}_{x.\{\Theta[\phi,\omega^x]\}_{\mathcal{K}\psi}^{r\to t}}(\chi) \\
(\forall i) &M_i^x := \text{pcoe}_{x.\Delta\psi \blacktriangleright x.\mathcal{K}\psi}^{x\to s}(\{\Theta.M_k[\phi, \omega^x]\}_{\mathcal{K}\psi}(\chi^x)) & \delta^x := \overline{\text{coe}}_{x.\Delta\psi}^{x\to s}(\delta\omega^x) \\
\hline
\text{pcoe}_{x.\Delta\psi \blacktriangleright x.\mathcal{K}\psi}^{r\to s}(\text{intro}_{\ell}^{\mathcal{K}'}(\phi; \omega; \chi)) & \approx \\
\text{fcom}_{x.\delta^s}^{s\to r}(\text{intro}_{\ell}^{\mathcal{K}\psi[s/x]}(\phi; \omega^s; \chi^s); \overline{\xi_i\phi \hookrightarrow x.M_i^x}) & \in \\
\Downarrow Fcom?(\text{Intro}_{\ell}^{\mathcal{K}}?(\text{Pcoe}^\nu))[\psi[s/x], \overline{\text{coe}}_{x.\Delta\psi}^{r\to s}(\delta)]
\end{aligned}
$$