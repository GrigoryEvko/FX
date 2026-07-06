288

Formalism

Explicitly, an element of $(\mu \mid T)(\Psi, g)$ is a family of terms $t_{\Psi',h} \in T(\Psi', [\mu](g) \circ h)$ indexed by contexts $\Psi'$ and closing substitutions $h : \mathcal{K}(\Psi') \to [\mu](\mathcal{K}(\Psi))$ and satisfying the property that $T(\psi, h)(t_{\Psi',h}) = t_{\Psi'',h \circ \mathcal{K}(\psi)}$ for every $\Psi'' \Vdash \psi \in \Psi' \circledast m$.

Finally, the extension $G.(\mu \mid T) \in PSh(\mathbb{R}_n)$ of a context $G$ by a modal hypotheses $T$ over $[\mu](G)$ is defined as the ordinary context extension by $(\mu \mid T)$.

$$(G.(\mu \mid T))(\Psi) := \sum_{g \in G(\Psi)} (\mu \mid T)(\Psi, g)$$

$$(G.(\mu \mid T))(\psi)(g, t) := (G(\psi)(g), (\mu \mid T)(\psi, g)(t))$$

**Modal types** We can interpret the two right adjoint modal types using the modal hypothesis pretypes already defined. Given a semantic type $T$ over $[\mathrm{dsc}](G)$, we define the semantic type $\mathrm{Glo}(T) := (\mathrm{dsc} \mid T)$; given $T$ over $[\mathrm{glo}](G)$, we likewise define $\mathrm{Codisc}(T) := (\mathrm{glo} \mid T)$. We leave it to the reader to reconstruct the interpretations of the introduction and elimination rules and Kan operators following their computational definitions.

For the discrete type, we must close $(\mathrm{cc} \mid T)$ under formal homogeneous composites. Just as we construct the value relation for the computational type $\mathrm{Disc}(A)$ as the least fixed-point of a process adding formal composite values, we can arrive at $\mathrm{Disc}(T)$ as a sequential colimit of presheaves beginning with $(\mathrm{cc} \mid T)$ and adding a layer of formal composites in each step. Alternatively, a second method of constructing cubical sets with formal composites can be found in [CHM18, §2.4] in the context of constructing higher inductive types.