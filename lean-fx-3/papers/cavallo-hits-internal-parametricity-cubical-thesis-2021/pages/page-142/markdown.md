130

General higher inductive types

Observe that the universe U of $\tau_1^H$ is closed under HITs whose index and types are drawn from U. The parameters of a family of HITs in U, on the other hand, are not required to be of types belonging to U. Suppose, for example, we have some family of HITs $\tau_1^H \vDash \Gamma \gg \Delta \blacktriangleright \mathcal{K}$ spec well-formed in the larger type system. For the induced family of inductive types $\Gamma, \Delta \gg \text{Ind}_{\mathcal{K}}^{\Delta}(\overline{v}_{\Delta})$ type to belong to U, we need only that $\tau_0^H \vDash \Psi \Vdash \Delta \gamma \blacktriangleright \mathcal{K}\gamma = \mathcal{K}\gamma'$ spec holds for every $\Psi \Vdash \gamma = \gamma' \in \Gamma$. This can be the case even if the types in $\Gamma$ do not themselves belong to $\tau_0^H$. As mentioned in Chapter 5, for example, we will have $A: U, a_0: A, a_1: A \gg \text{Id}(A, a_0, a_1) \in U$, which requires that the type $A$ of the indices belongs to U but not that the type U of the parameter belongs to U.

We work relative to the type system $\tau_1^H$ for the remainder of this chapter, in which we check that the inductive pretypes enjoy the rules we expect from them. The formation rule is immediate by coherent value introduction and stability of the specification judgment—the type and its substitution instances are all values—while the introduction follows from lemmas we have already proven.

**Rule 6.2.25 (Pretype formation).**

$$\frac{\Psi \Vdash \Delta = \Delta' \text{ tel} \quad \Psi \Vdash \Delta \blacktriangleright \mathcal{K} = \mathcal{K}' \text{ spec} \quad \Psi \Vdash \delta = \delta' \in \Delta}{\Psi \Vdash \text{Ind}_{\mathcal{K}}^{\Delta}(\delta) = \text{Ind}_{\mathcal{K}'}^{\Delta'}(\delta') \text{ pretype}}$$

*Proof.* By coherent value introduction.

**Rule 6.2.26 (Constructor introduction).** Let $\Psi \Vdash \Delta \blacktriangleright \mathcal{K} = \mathcal{K}'$ spec and a constructor $(\ell: \Phi.\Omega.[\delta; \Theta.\overline{\xi_i \hookrightarrow M_i}]) \in \mathcal{K}$ be given.

$$\frac{\Psi \Vdash \phi = \phi' \in \Phi \quad \Psi \Vdash \omega = \omega' \in \Gamma\phi \quad \Psi \Vdash \chi = \chi' \in (\Theta[\phi, \omega])_{\mathcal{K}}^{\Delta}}{\Psi \Vdash \text{intro}_{\ell}^{\mathcal{K}}(\phi; \omega; \chi) = \text{intro}_{\ell}^{\mathcal{K}'}(\phi'; \omega'; \chi') \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta[\phi, \omega])}$$

$$\frac{\Psi \Vdash \xi_j \text{ satisfied} \quad \Psi \Vdash \phi \in \Phi \quad \Psi \Vdash \omega \in \Gamma\phi \quad \Psi \Vdash \chi \in (\Theta[\phi, \omega])_{\mathcal{K}}^{\Delta}}{\Psi \Vdash \text{intro}_{\ell}^{\mathcal{K}}(\phi; \omega; \chi) = (\Theta.M_j[\phi, \omega])_{\mathcal{K}}(\chi) \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta[\phi, \omega])}$$

*Proof.* By Lemma 6.2.18.

**Rule 6.2.27 (Formal coercion introduction).** Let $\Psi \Vdash \Delta \blacktriangleright \mathcal{K}$ spec.

$$\frac{\Psi, x: \mathbb{I} \Vdash \delta = \delta' \in \Delta \quad \Psi \Vdash r, s \in \mathbb{I} \quad \Psi \Vdash M = M' \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta[r/x])}{\Psi \Vdash \text{fcoe}_{x,\delta}^{r\to s}(M) = \text{fcoe}_{x,\delta'}^{r\to s}(M') \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta[s/x])}$$

$$\frac{\Psi, x: \mathbb{I} \Vdash \delta \in \Delta \quad \Psi \Vdash r \in \mathbb{I} \quad \Psi \Vdash M \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta[r/x])}{\Psi \Vdash \text{fcoe}_{x,\delta}^{r\to r}(M) = M \in \text{Ind}_{\mathcal{K}}^{\Delta}(\delta[r/x])}$$