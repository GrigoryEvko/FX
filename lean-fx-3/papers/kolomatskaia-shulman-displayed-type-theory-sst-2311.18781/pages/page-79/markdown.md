Using this, we can verify that our intended model is indeed a model.

**Theorem 4.40.** *The simplicial model of sections 4.2 and 4.3 has type display, and hence complete display, which respects $\Pi$-types and universes.*

*Proof.* We constructed a display operation for the simplicial model in section 4.2, but it does not yet have exactly the needed form. What we have so far is a 'global' operation that décalages the whole context:

$$\frac{\gamma : \Gamma \vdash_{\text{sm}} A \gamma \text{ type}}{\gamma^+ : \Gamma^D, a : A^{\rho_\Gamma} \gamma^+ \vdash_{\text{sm}} A^d \gamma^+ a \text{ type}}.$$

(Note that this is only defined on the original simplicial model sm, not the extended one sm$_{+}$: indeed, décalage is not even defined on flat contexts.) But the (meta-abstracted version of the) operation we specified in the syntax of section 2 is a 'local' one that only décalages part of the context, keeping the rest of it modally locked away:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon \vdash_{\text{sm}} A \gamma \nu \text{ type}}{\gamma : \Gamma, \nu^+ : \Upsilon^D, a : A^{\mathbf{a}_{\mathbf{s}} \triangleq \mathbb{I}_{\text{sm}}} \gamma (\nu^+)^{\text{ev}} \vdash_{\text{sm}} A^d \gamma \nu^+ a \text{ type}}$$

However, it is straightforward to obtain the latter from the former. In sm$_{+}$, a context of the form $(\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon)$ is not flat, hence lies essentially in sm so that décalage is defined on it. Furthermore, we already observed that $(\Gamma, \mathbf{\Omega}_{\square})^D \equiv (\Gamma, \mathbf{\Omega}_{\square})$ since $\mathbf{\Omega}_{\square}$ lands in constant presheaves. Thus, when $\Upsilon$ is a telescope built out of types, we have

$$(\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon)^D \equiv (\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu^+ : \Upsilon^D)$$

and so the global operation yields as a special case

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu : \Upsilon \vdash_{\text{sm}_+} A \gamma \nu \text{ type}}{\gamma : \Gamma, \mathbf{\Omega}_{\Delta\square}, \nu^+ : \Upsilon^D, a : A^\rho \gamma \nu^+ \vdash_{\text{sm}_+} A^d \gamma \nu^+ a \text{ type}}.$$

Now we simply substitute along $\mathbf{a}_{\mathbf{s}} \triangleq \mathbb{I}_{\text{sm}}$ to obtain the desired local rule. The necessary computation rules for décalage, $\Pi$-types, and universes follow immediately from the rules we proved for the global operation in section 4.2. $\square \triangleleft$

### 4.4.4 Display of $\omega$-limits

Finally, when we have both display and also $\omega$-limits, it is reasonable to require the former to compute on the latter, in the following way. Suppose that $\Gamma, \mathbf{\Omega}_{\Delta\square} \mid \phi : \Phi \vdash_{\text{sm}} \tilde{\Upsilon} \phi \text{ stel}^\infty$, and we want to compute $\Gamma, \phi : \Phi^D, u : \lim \tilde{\Upsilon} \vdash \lim \tilde{\Upsilon}^d \phi u$. Then by definition, we have

$$\begin{array}{l} \Gamma, \mathbf{\Omega}_{\Delta\square} \vdash_{\text{sm}} \Upsilon^{\partial n} \text{ tel} / \phi : \Phi \\ \Gamma, \mathbf{\Omega}_{\Delta\square} \vdash_{\text{sm}} \Upsilon^n \text{ type} / \phi : \Phi, \partial \nu : \Upsilon^{\partial n} \phi \end{array}$$

and therefore

$$\begin{array}{l} \Gamma \vdash_{\text{sm}} (\Upsilon^{\partial n})^d \text{ tel}_\ell / \phi : \Phi^D, \partial \nu : \Upsilon^{\partial n} \phi^{\text{ev}} \\ \Gamma \vdash_{\text{sm}} (\Upsilon^n)^d \text{ type}_\ell / \phi : \Phi^D, \partial \nu : (\Upsilon^{\partial n})^D \phi, \nu : \Upsilon^n \phi^{\text{ev}} \partial \nu^{\text{ev}} \end{array}$$

79