211

ity equations.

$$\frac{\Gamma'' \vdash r : \mathbf{I} \quad \Gamma'' \cdot \backslash r \vdash \gamma' : \Gamma' \quad \Gamma' \vdash \gamma : \Gamma}{\Gamma'' \vdash (\gamma \circ \gamma') \cdot r = \gamma^I \circ (\gamma' \cdot r) : \Gamma \cdot \mathbf{I}}$$

$$\frac{\Gamma'' \vdash \gamma' : \Gamma' \quad \Gamma' \vdash \gamma : \Gamma \cdot \mathbf{I}}{\Gamma'' \cdot \backslash v_I[\gamma \circ \gamma'] \vdash (\gamma \circ \gamma')^\dagger = \gamma^\dagger \circ (\gamma' \backslash v_I[\gamma]) : \Gamma}$$

Finally, we include the two interval constants and the additional structural rules available to bridge interval variables: weakening and exchange as well as exchange with path interval variables.

$$\frac{\Gamma \vdash 0_I : \Gamma \cdot \mathbf{I}}{\Gamma \vdash 1_I : \Gamma \cdot \mathbf{I}} \quad \frac{\Gamma \cdot \mathbf{I} \vdash p_I : \Gamma}{\Gamma \cdot \mathbf{I} \vdash p_I : \Gamma} \quad \frac{\Gamma \text{ ctx}}{\Gamma \cdot \mathbf{I} \cdot \mathbf{I} \vdash \text{ex}_II : \Gamma \cdot \mathbf{I} \cdot \mathbf{I}} \quad \frac{\Gamma \text{ ctx}}{\Gamma \cdot \mathbf{I} \cdot \mathbf{I} \vdash \text{ex}_II : \Gamma \cdot \mathbf{I} \cdot \mathbf{I}}$$

The constant interval *terms* are then obtained as $\Gamma \vdash v_I[0_I] : \mathbf{I}$ and $\Gamma \vdash v_I[1_I] : \mathbf{I}$. We deliberately introduce the constants as substitutions rather than as terms, as the former is stronger than the latter: given some $\Gamma \vdash r : \mathbf{I}$, we can only construct a substitution $\Gamma \vdash \text{id.}r : \Gamma \cdot \backslash r \cdot \mathbf{I}$, not a substitution from $\Gamma$ to $\Gamma \cdot \mathbf{I}$. Using $\Gamma \vdash \varepsilon_I : \Gamma \cdot \mathbf{I}$, on the other hand, we are able to access hypotheses beneath restriction by a constant: $\Gamma \cdot \backslash v_I[\varepsilon_I] \vdash \varepsilon_I^\dagger : \Gamma$.

We require the structural and endpoint substitutions to satisfy various unsurprising equations, expressing their naturality and interactions with each other. (We refer to Grandis and Mauri [GM03] for more detailed analysis of the equations generating various categories of cubical sets.)

$$\frac{\varepsilon \in \{0, 1\} \quad \Gamma' \vdash \gamma : \Gamma}{\Gamma' \vdash \gamma^I \circ \varepsilon_I = \varepsilon_I \circ \gamma : \Gamma \cdot \mathbf{I}} \quad \frac{\Gamma' \vdash \gamma : \Gamma}{\Gamma' \cdot \mathbf{I} \vdash \gamma \circ p_I = p_I \circ \gamma^I : \Gamma}$$

$$\frac{\Gamma' \vdash \gamma : \Gamma}{\Gamma' \cdot \mathbf{I} \cdot \mathbf{I} \vdash \gamma^II \circ \text{ex}_II = \text{ex}_II \circ \gamma^II : \Gamma \cdot \mathbf{I} \cdot \mathbf{I}} \quad \frac{\varepsilon \in \{0, 1\}}{\Gamma \vdash p_I \circ \varepsilon_I = \text{id} : \Gamma} \quad \frac{\Gamma \text{ ctx}}{\Gamma \cdot \mathbf{I} \cdot \mathbf{I} \vdash p_I \circ \text{ex}_II = p_I^I : \Gamma \cdot \mathbf{I}}$$

$$\frac{\Gamma \text{ ctx}}{\Gamma \cdot \mathbf{I} \cdot \mathbf{I} \vdash \text{ex}_II^I \circ \text{ex}_II \circ \text{ex}_II^I = \text{ex}_II \circ \text{ex}_II^I \circ \text{ex}_II : \Gamma \cdot \mathbf{I} \cdot \mathbf{I} \cdot \mathbf{I}} \quad \frac{\Gamma \text{ ctx}}{\Gamma \cdot \mathbf{I} \cdot \mathbf{I} \vdash (p_I^I \cdot v_I) \circ \text{ex}_II = \text{id} : \Gamma \cdot \mathbf{I} \cdot \mathbf{I}}$$

$$\frac{\Gamma \text{ ctx}}{\Gamma \cdot \mathbf{I} \cdot \mathbf{I} \vdash \text{ex}_II \circ (p_I^I \cdot v_I) = \text{id} : \Gamma \cdot \mathbf{I} \cdot \mathbf{I}}$$

This judgmental structure is sufficient to express the typing rules for the bridge and Gel types as well as the extent operator. We display rules for bridge and Gel types in Figures 11.1 and 11.2 respectively. (Expressing the rules for extent without named variables is sufficiently painful that we leave this as an exercise to the reader.)