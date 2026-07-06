• There is a pullback square

$$\begin{array}{c} \mathrm{P}_{\mathrm{tpr}_{\ell_0}}(\mathrm{PSub}_{\ell_1}) \longrightarrow \mathrm{PSub}_{\ell_0 \sqcup \ell_1} \\ \mathrm{P}_{\mathrm{tpr}_{\ell_0}}(\mathrm{tpr}_{\ell_1}) \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \\ \mathrm{P}_{\mathrm{tpr}_{\ell_0}}(\mathrm{Tel}_{\ell_1}) \xrightarrow{\Pi} \mathrm{Tel}_{\ell_0 \sqcup \ell_1}, \end{array}$$

• The computation rules from section 2.5.3 hold.

Now the above rules allow us to build telescopes up from the empty telescope by adding types, just as the rules of a CwF allow us to build contexts from the empty context by adding types. However, just as in the case of contexts, the rules do not stipulate that every telescope is obtained in that way. Indeed, there is no way to assert such a thing in a Generalised Algebraic Theory. However, it holds 'admissibly' in the initial syntactic model, and any CwF can be extended with telescopes in this way:

**Theorem 4.7.** *Any CwF with levels can be equipped with telescopes. If it has Π-types, it also has Π-telescopes.*

*Proof.* We define $\mathrm{tpr}_{\ell}$ to be the map such that

$$\mathrm{P}_{\mathrm{tpr}_{\ell}} = \sum_{\substack{n \leqslant n \\ \forall i \leqslant n, \ell_i \leqslant \ell}} \mathrm{P}_{\mathrm{pr}_{\ell_0}} \circ \dots \circ \mathrm{P}_{\mathrm{pr}_{\ell_n}}.$$

Thus an element of $\mathrm{Tel}_{\ell}(\Gamma)$ is a tower of $n$ types over $\Gamma$ of level $\leqslant \ell$, and similarly for terms. The two morphisms of polynomial functors are then immediate. We define context extension in the obvious way by iterating context extension by types, and the equations hold. (This is the *initial* structure of telescopes on $\mathcal{C}$ in a straightforward sense.) Similarly, we define Π-telescopes by using the rules for computing them on extended telescopes. $\square \triangleleft$

### 4.1.7 Meta-abstractions

Because meta-abstractions are not 'reified' in the theory as types, they do not require assuming any structure beyond that which is already present in the presheaf category. Specifically, the rules for the judgment $\Gamma \vdash A \text{ type}_{\ell: \Upsilon}$ simply say that it should be (up to isomorphism) the object $\mathrm{P}_{\mathrm{tpr}}(\mathrm{Ty})$ that classifies types indexed by a telescope. Similarly, the rules for the elements of a meta-abstraction simply say that these are the object $\mathrm{P}_{\mathrm{tpr}}(\mathrm{Tm})$ that classifies terms indexed by a telescope. In other words, meta-abstractions of types and their terms are classified by a map (isomorphic to) $\mathrm{P}_{\mathrm{tpr}}(\mathrm{pr})$. Likewise, meta-abstractions of telescopes (the judgment $\Gamma \vdash \Theta \text{ tel}_{\ell: \Upsilon}$) are classified by a map isomorphic to $\mathrm{P}_{\mathrm{tpr}}(\mathrm{tpr})$. This gives all the rules from sections 2.3.3 and 2.5.1; thus any natural model with telescopes also has meta-abstractions of types and telescopes.

Semantically, we don't ever need to discuss meta-abstractions explicitly, since to judge $\Gamma \vdash A \text{ type}_{\ell/\delta: \Upsilon}$ is equivalent to judging $\Gamma \mid \Upsilon \vdash A \text{ type}_{\ell}$, and so on. Thus we will generally talk only about types and telescopes in contexts. $\triangleleft$

48