Formalisms 41

**Explicit substitutions** We eliminate the dependence on raw term substitution by making substitution application an operation *inside* the type theory, taking an open substitution $\Gamma' \vdash \gamma : \Gamma$ as an argument.

$$\frac{\Gamma' \vdash \gamma : \Gamma \quad \Gamma \vdash A \text{ type}}{\Gamma' \vdash A[\gamma] \text{ type}} \qquad \frac{\Gamma' \vdash \gamma : \Gamma \quad \Gamma \vdash M : A}{\Gamma' \vdash M[\gamma] : A[\gamma]}$$

The substitutions form a category: there is always an identity substitution, and we can compose substitutions.

$$\frac{\Gamma \vdash \text{id} : \Gamma}{\Gamma'' \vdash \gamma' : \Gamma' \quad \Gamma' \vdash \gamma : \Gamma} \qquad \frac{\Gamma'' \vdash \gamma \circ \gamma' : \Gamma}{\Gamma'' \vdash \gamma \circ \gamma' : \Gamma}$$

These are subject to the usual equations: $\text{id} \circ \gamma = \gamma$, $\gamma \circ \text{id} = \gamma$, and $\gamma \circ (\gamma' \circ \gamma'') = (\gamma \circ \gamma') \circ \gamma''$. We moreover have equations for computing the action of a substitution.

$$\frac{A[\text{id}] = A \text{ type}}{\Gamma'' \vdash \gamma' : \Gamma' \quad \Gamma' \vdash \gamma : \Gamma \quad \Gamma \vdash A \text{ type}} \qquad \frac{\Gamma \vdash A[\gamma \circ \gamma'] = A[\gamma][\gamma'] \text{ type}}{\Gamma \vdash A[\gamma \circ \gamma'] = A[\gamma][\gamma'] \text{ type}}$$

When we arrive at the function type below, we will introduce further equations that compute substitutions at each term and type former; for example, function application will come with an equation $(FM)[\gamma] = F[\gamma] M[\gamma]$.

**Hypotheses and variables** Again for the purpose of simplifying metatheoretic analysis, we avoid introducing named variables. Thus, a context is not a lookup table associating names with types, but merely a list of types.

$$\frac{\Gamma \vdash A \text{ type}}{\Gamma \vdash A \text{ ctx}} \cdot \text{ctx}$$

An extended context $\Gamma \cdot A$ comes with a weakening substitution (written p for “projection”) that throws away the assumption. On the other hand, we can construct a substitution from some $\Gamma'$ into an extended context $\Gamma \cdot A$ by taking a substitution $\Gamma' \vdash \gamma : \Gamma$ and attaching an additional term $\Gamma' \vdash M : A[\gamma]$.

$$\frac{\Gamma \text{ ctx} \quad \Gamma \vdash A \text{ type}}{\Gamma \cdot A \vdash p : \Gamma} \qquad \frac{\Gamma' \vdash \gamma : \Gamma \quad \Gamma \vdash A \text{ type} \quad \Gamma' \vdash M : A[\gamma]}{\Gamma' \vdash \gamma \cdot M : \Gamma \cdot A}$$

In an extended context $\Gamma \cdot A$, we always have access to at least one variable, namely the one of type $A$ at the top of the the context; we write v for this variable. (Note that we weaken $A$ so that it is well-formed in context $\Gamma \cdot A$.)

$$\frac{\Gamma \vdash A \text{ type}}{\Gamma \cdot A \vdash v : A[p]}$$