The empty context is the chosen terminal object $\mathbb{1}$, and is denoted by:

$$\text{() ob}$$

The morphisms of $\mathcal{C}$ are called substitutions and denoted by $\sigma$, $\tau$. For $\sigma : \text{mor}_{\mathcal{C}}(\Delta, \Gamma)$ we write:

$$\sigma : \Delta \to \Gamma$$

The unique substitution into the empty context is denoted by:

$$\text{[] : } \Gamma \to \text{()}$$

The notations $\Gamma$ ob and $\sigma : \Delta \to \Gamma$ are examples of 'absolute' or 'context-less' judgments. In the notation of this section, each absolute judgment asserts that some element belongs to some set, such as the set of objects or a hom-set of $\mathcal{C}$. Note that a set can be 'dependent' on elements of another set, such as the hom-set $\text{mor}_{\mathcal{C}}(\Delta, \Gamma)$ depending on $\Delta$, $\Gamma : \text{ob}_{\mathcal{C}}$; and thus elements of one absolute judgment can appear in another absolute judgment, such as $\sigma : \Delta \to \Gamma$ where $\Delta$ ob and $\Gamma$ ob. Operations on sets can be written as rules, such as composition of morphisms:

$$\frac{\sigma : \Delta \to \Gamma \qquad \tau : \Gamma \to \Theta}{\tau \circ \sigma : \Delta \to \Theta}.$$

Equations between these operations can likewise be written as rules, where we use $\equiv$ for equality since it corresponds to definitional equality in syntax:

$$\frac{\sigma : \Delta \to \Gamma \qquad \tau : \Gamma \to \Theta \qquad \upsilon : \Theta \to \Upsilon}{\upsilon \circ (\tau \circ \sigma) \equiv (\upsilon \circ \tau) \circ \sigma}.$$

The elements of $\text{Ty}_{\ell}$ are called types of level $\ell$ and denoted by $A, B$. For $A : \text{Ty}_{\ell} \Gamma$ we write:

$$\gamma : \Gamma \vdash A \ \gamma \ \text{type}_{\ell}$$

Similarly, the elements of $\text{Tm}_{\ell}$ are called terms and denoted by $t$, $s$. For $t : \text{Tm}_{\ell}(\Gamma, A)$ we write:

$$\gamma : \Gamma \vdash t \ \gamma : A \ \gamma$$

These notations are examples of 'hypothetical' or 'contextual' judgments. In the notation of this section, each hypothetical judgment asserts that some element belongs to a value of some presheaf, such as $\text{Tm}_{\ell}$ or $\text{Ty}_{\ell}$. The object of $\mathcal{C}$ at which the presheaf is evaluated (in these examples, $\Gamma$) is written on the left-hand side of the turnstile $\vdash$. We annotate it with a formal 'variable' such as $\gamma$, and 'apply' all the elements appearing on the right-hand side to that element; at the moment this is just a convention of notation. As with absolute judgments, one presheaf can be dependent on another, such as $\text{Tm}_{\ell}(\Gamma, A)$ depending on $A : \text{Ty}_{\ell} \Gamma$; and thus the elements of one hypothetical judgment can appear in another hypothetical judgment, such as $\gamma : \Gamma \vdash t \ \gamma : A \ \gamma$ where $\gamma : \Gamma \vdash A \ \gamma \ \text{type}_{\ell}$.

For a morphism $\sigma : \Delta \to \Gamma$, we denote its functorial action on types $A$ and terms $t$ by $A^{\sigma}$ and $t^{\sigma}$; thus the presheaf actions of $\text{Ty}_{\ell}$ and $\text{Tm}_{\ell}$ can be expressed by rules

$$\frac{\sigma : \Delta \to \Gamma \qquad \gamma : \Gamma \vdash A \ \gamma \ \text{type}_{\ell}}{\delta : \Delta \vdash A^{\sigma} \ \delta \ \text{type}_{\ell}}$$

$$\frac{\sigma : \Delta \to \Gamma \qquad \gamma : \Gamma \vdash t : A}{\delta : \Delta \vdash t^{\sigma} \ \delta : A^{\sigma} \ \delta}$$

41