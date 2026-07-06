### 2.4.4 Computing décalage

Now we can give the rules 'defining' telescope décalage on telescopes extended by a variable. Specifically, when extending by a non-modal variable, we also extend by its displayed version. But that displayed version needs to depend on $\Theta^D$, so we define it in terms of display for meta-abstractions. Note that the well-typedness of $t^d$ in these rules depends on the reduction of meta-abstraction display on displayed partial substitutions.

$$(\theta : \Theta, x : A)^D \equiv (\theta^+ : \Theta^D, x : A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | \theta^{+ev}], x' : ((A))_{\theta : \Theta^d} \theta^+ x)$$

$$[\sigma, t]^D \equiv [\sigma^D, t, t^d]$$

$$[\sigma^+, t, t']^{ev} \equiv [\sigma^{+ev}, t]$$

The case of a nontrivially modal variable is actually simpler. Note that in this case, the modality must be of the form $\triangle \circ \mu$. Recalling that semantically, $\triangle$ constructs a constant simplicial type, we should have informally $(\triangle A)^D = \triangle A$, and therefore $(\triangle A)^d$ is trivial. For an action on types, this would mean that $(\triangle A)^d x$ is the unit type; for our current action on telescopes, it means we can just omit the displayed variables.

$$(\theta : \Theta, x : ^{\triangle\circ\mu} A)^D \equiv (\theta^+ : \Theta^D, x : ^{\triangle\circ\mu} A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | \theta^{+ev}, \mathbf{Q}_{\triangle\circ\mu}])$$

$$[\sigma, t]^D \equiv [\sigma^D, t]$$

$$[\sigma^+, t]^{ev} \equiv [\sigma^{+ev}, t]$$

◁

### 2.4.5 Computing display

Recall from section 1 that we treat display computationally like the identity types of HOTT, so that it computes on the basic type-formers. Note that the abstracting telescope changes as we compute, so these rules could not be stated for ordinary display alone.

#### 2.4.5.1 Non-modal $\Pi$-Types

This rule represents the traditional behavior of parametricity and logical relations on functions: a computability witness for a function says that it preserves computability witnesses.

$$\left( (x : A) \to B \right)_{v : \gamma^d} \equiv \left( \left( x : A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | v^{+ev}] \right) (x' : ((A))_{v : \gamma^d} v^+ x) \to \right.$$

$$\left. \left( (B)_{v : \gamma, x : A}^d v^+ x x' (f x) \right)_{v^+ : \gamma^D, f : (x : A) \to B} \right.$$

$$\llbracket \lambda x . t \rrbracket_{v : \gamma^d} \equiv \llbracket \lambda x x'. \llbracket t \rrbracket_{v : \gamma, x : A}^d v^+ x x' \rrbracket_{v^+ : \gamma^D}$$

$$\llbracket f a \rrbracket_{v : \gamma^d} \equiv \llbracket (\llbracket f \rrbracket_{v : \gamma^d} v^+) a (\llbracket a \rrbracket_{v : \gamma^d} v^+) \rrbracket_{v^+ : \gamma^D}$$

#### 2.4.5.2 Nontrivially modal $\Pi$-Types

As with décalage, here we use the fact that display of $\triangle$ is trivial. Note also that here a modal variable appears in the domain of a meta-abstraction. This is the reason that we cannot restrict to strict telescopes in general.

$$\left( (x : ^{\triangle\circ\mu} A) \to B \right)_{v : \gamma^d} \equiv \left( \left( x : ^{\triangle\circ\mu} A [\mathbf{Q}^{\triangle\square\leqslant 1_{sm}} | v^{+ev}, \mathbf{Q}_{\triangle\circ\mu}] \right) \to \right.$$

$$\left. \left( (B)_{v : \gamma, x : ^{\triangle\circ\mu} A}^d v^+ x (f x) \right)_{v^+ : \gamma^D, f : (x : ^{\triangle\circ\mu} A) \to B} \right.$$

$$\llbracket \lambda x . t \rrbracket_{v : \gamma^d} \equiv \llbracket \lambda x. \llbracket t \rrbracket_{v : \gamma, x : ^{\triangle\circ\mu} A}^d v^+ x \rrbracket_{v^+ : \gamma^D}$$

$$\llbracket f a \rrbracket_{v : \gamma^d} \equiv \llbracket \llbracket f \rrbracket_{v : \gamma^d} v^+ a \rrbracket_{v^+ : \gamma^D}$$

21