210

Formalism and models

Like path intervals, we may add a bridge interval to the context, in which case we have a variable interval term.

$$\frac{\Gamma \operatorname{ctx}}{\Gamma . \mathbf{I} \operatorname{ctx}} \quad \frac{\Gamma \operatorname{ctx}}{\Gamma . \mathbf{I} \vdash v_{\mathbf{I}} : \mathbf{I}} \quad \frac{\Gamma \vdash r : \mathbf{I} \quad \Gamma' \vdash \gamma : \Gamma}{\Gamma' \vdash r [\gamma] : \mathbf{I}}$$

Where the context $\Gamma . \mathbf{I}$ is characterized as the cartesian product of $\Gamma$ with $\cdot . \mathbf{I}$, however, here we need the extension to behave as a *separated* product. To express this, we introduce a new context former for interval restriction.

$$\frac{\Gamma \operatorname{ctx} \quad \Gamma \vdash r : \mathbf{I}}{\Gamma . \backslash r \operatorname{ctx}} \quad \frac{\Gamma' \vdash r : \mathbf{I} \quad \Gamma' . \backslash r \vdash \gamma : \Gamma}{\Gamma' \vdash \gamma . r : \Gamma . \mathbf{I}}$$

A substitution from $\Gamma'$ into some $\Gamma . \mathbf{I}$ is therefore composed of an interval term $\Gamma' \vdash r : \mathbf{I}$ paired with a substitution $\Gamma' . \backslash r \vdash \delta : \Gamma$, an instantiation of $\Gamma$ which "does not use" $r$. (At this point the intuition of "use" becomes more intuition than reality; in the formalism and computational interpretation, it is indeed impossible to access an interval variable from behind the restriction, but the meaning of "use" is less obvious in non-syntactic models such as the upcoming presheaf interpretation.)

Moreover, we make this principle invertible: given $\Gamma' \vdash \gamma : \Gamma . \mathbf{I}$, there is an underlying substitution into $\Gamma$ that does not use the term $\Gamma' \vdash v_{\mathbf{I}}[\gamma] : \mathbf{I}$ substituted for $\mathbf{I}$. We write $\gamma^{\dagger}$ for this substitution.

$$\frac{\Gamma' \vdash \gamma : \Gamma . \mathbf{I}}{\Gamma' . \backslash v_{\mathbf{I}}[\gamma] \vdash \gamma^{\dagger} : \Gamma} \quad \frac{\Gamma \operatorname{ctx} \quad \Gamma' \vdash \gamma : \Gamma . \mathbf{I}}{\Gamma' \vdash \gamma = \gamma^{\dagger} . v_{\mathbf{I}}[\gamma] : \Gamma . \mathbf{I}} \quad \frac{\Gamma' \vdash r : \mathbf{I} \quad \Gamma' . \backslash r \vdash \gamma : \Gamma}{\Gamma' . \backslash r \vdash \gamma = (\gamma . r)^{\dagger} : \Gamma}$$

This sets up an adjunction between the category of contexts sliced over the bridge interval and the category of contexts. An object of said slice category is a pair $(\Gamma' . r)$ consisting of a context $\Gamma'$ and term $\Gamma' \vdash r : \mathbf{I}$. Given such an object and a second context $\Gamma$, we have a correspondence between substitutions $\Gamma' . \backslash r \vdash \gamma : \Gamma$ and substitutions $\Gamma' \vdash \gamma' : \Gamma . \mathbf{I}$ with the property that $\Gamma' \vdash v_{\mathbf{I}}[\gamma'] = r : \mathbf{I}$, instrumented by the $-.r$ and $-^{\dagger}$ substitution formers. Note that we can also derive functorial actions of extension and restriction using said operators.

$$\frac{\Gamma' \vdash \gamma : \Gamma}{\Gamma' . \mathbf{I} \vdash \gamma^{\mathbf{I}} := (\gamma \circ \operatorname{id}^{\dagger}) . v_{\mathbf{I}} : \Gamma . \mathbf{I}} \quad \frac{\Gamma' \vdash \gamma : \Gamma \quad \Gamma \vdash r : \mathbf{I}}{\Gamma' . \backslash r [\gamma] \vdash (\gamma \backslash r) := ((\operatorname{id} . r) \circ \gamma)^{\dagger} : \Gamma . \backslash r}$$

We make the correspondence into a genuine adjunction by additionally imposing natural-