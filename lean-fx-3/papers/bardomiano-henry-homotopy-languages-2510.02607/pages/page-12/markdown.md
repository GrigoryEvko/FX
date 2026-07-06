3. $\forall \Phi \in \mathcal{L}_{\lambda}^{T}(\Gamma), \Phi \wedge \neg \Phi \vdash \bot$ and $\top \vdash \Phi \vee \neg \Phi$.
4. For any $\lambda$-small family $(\Phi_i)_{i \in I} \in \mathcal{L}_{\lambda}^{T}(\Gamma)$ we have

$$\bigvee_{i \in I} \Phi_i \vdash_{\Gamma} \Psi \Leftrightarrow \forall i, (\Phi_i \vdash_{\Gamma} \Psi)$$

$$\Psi \vdash \bigwedge_{i \in I} \Phi_i \Leftrightarrow \forall i, (\Psi \vdash_{\Gamma} \Phi_i)$$

5. For $\Gamma' \equiv \left( \Gamma, \left\{ x_{\beta} : \Gamma'_{\beta} \right\}_{\gamma \in \beta < \alpha} \right)$ a context extension, with $p : \Gamma' \rightarrow \Gamma$ the corresponding generalized display map, $\Psi \in \mathcal{L}_{\lambda}^{T}(\Gamma')$ and $\Phi \in \mathcal{L}_{\lambda}^{T}(\Gamma)$ we have

$$\exists \{ x_{\beta} : \Gamma_{\beta} \}_{\gamma \in \beta < \alpha} \Psi \vdash_{\Gamma} \Phi \Leftrightarrow \Psi \vdash_{\Gamma'} p^* \Phi,$$

$$\Phi \vdash_{\Gamma} \forall \{ x_{\beta} : \Gamma_{\beta} \}_{\gamma \in \beta < \alpha} \Psi \Leftrightarrow p^* \Phi \vdash_{\Gamma'} \Psi.$$

While we have not included the following in the definition, we can show that:

**Proposition 2.7.** *If $f : \Delta \rightarrow \Gamma$ is a context morphism in $T$, and $\Phi \vdash_{\Gamma} \Psi$ then $f^* \Phi \vdash_{\Delta} f^* \Psi$.*

*Proof.* We can show that if we define the relation $\Phi \vdash_{\Gamma}' \Delta$ to be “For all $f : \Delta \rightarrow \Gamma$, we have $f^* \Phi \vdash_{\Delta} f^* \Psi$” then it satisfies all the conditions from theorem 2.6. Which shows that $\vdash \Rightarrow \vdash'$ and hence concludes the proof. $\square$

In section B.4 we define a model for a generalized $\kappa$-algebraic theory $T$ is as a morphism of contextual categories $X : \mathbb{C}_T \rightarrow \mathbf{Fam}_{\kappa}$ where $\mathbf{Fam}_{\kappa}$ is a contextual categories of “families of sets”. By theorem B.50 this turns out to be equivalent to the naive definition of models where for each dependent type we have a family of sets, for each term a function, and equation axioms give us equations. Importantly for us, for each model $X$ and context $\Gamma$, there is a set $X(\Gamma)$, an element of which is a choice of an interpretation of each variable of $\Gamma$ as an element of the corresponding set in $X$. These $X(\Gamma)$ forms a functor on the category of contexts of $T$.

In what follows, we will use notation as explained in theorem B.51.

**Construction 2.8.** Given a model $X$ of our theory $T$, $\Gamma$ a context, $x \in X(\Gamma)$ and $\Phi \in \mathcal{L}_{\lambda}^{T}(\Gamma)$, we can interpret $\Phi(x)$ as a proposition *i.e.*, true or false in the obvious way by substituting the components of $x$ into $\phi$ and interpreting all the logic symbols in the usual way. Formally we have:

12