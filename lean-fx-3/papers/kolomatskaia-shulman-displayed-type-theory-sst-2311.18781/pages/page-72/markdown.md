### 4.3.6 Modal Variables

We have the following rules for extending a context and substitution modally:

$$\frac{\mu : p \to q \quad \Gamma \text{ ob}_{[\![q]\!]} \quad \gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} A \gamma \text{ type}_{\ell}}{(\gamma : \Gamma, a :^{\mu+} A \gamma) \text{ ob}_{[\![q]\!]}}$$

$$\frac{\sigma : \Delta \to_{[\![q]\!]} \Gamma \quad \gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} t \gamma : A \gamma}{[\sigma, t]_{\mu+} : \Delta \to_{[\![q]\!]} (\gamma : \Gamma, a :^{\mu+} A \gamma)}$$

The case of $\triangle_+$ is defined as follows, splitting on whether or not $\Gamma$ is flat:

$$(\gamma : \text{in}_{\text{dm}} \Gamma, a :^{\triangle_+} A \gamma) \equiv \text{in}_{\text{dm}} (\gamma : \Gamma, a : A \gamma)$$

$$[\text{in}_{\text{dm}} \sigma, t]_{\triangle_+} \equiv \text{in}_{\text{dm}} [\sigma, t]$$

$$(\gamma : \text{in}_{\text{sm}} \Gamma, a :^{\triangle_+} A \gamma) \equiv \text{in}_{\text{sm}} (\gamma : \Gamma, a :^{\triangle} A \gamma)$$

$$[\text{in}_{\text{sm}} \sigma, t]_{\triangle_+} \equiv \text{in}_{\text{sm}} [\sigma, t]_{\triangle}.$$

Following this, the rest of the definitions say that the case of modal extension reduces to extension by a variable or term of modal type:

$$(\gamma : \Gamma, a :^{\diamond_+} A \gamma) \equiv (\gamma : \Gamma, a : \diamond A \gamma)$$

$$[\sigma, t]_{\diamond_+} \equiv [\sigma, t]$$

$$(\gamma : \Gamma, a :^{\triangle\diamond_+} A \gamma) \equiv (\gamma : \Gamma, a :^{\triangle_+} \diamond A \gamma)$$

$$[\sigma, t]_{\triangle\diamond_+} \equiv [\sigma, t]_{\triangle_+}$$

$$(\gamma : \Gamma, a :^{\square_+} A \gamma) \equiv (\gamma : \Gamma, a : \square A \gamma)$$

$$[\sigma, t]_{\square_+} \equiv [\sigma, t]$$

$$(\gamma : \Gamma, a :^{\triangle\square_+} A \gamma) \equiv (\gamma : \Gamma, a :^{\triangle_+} \square A \gamma)$$

$$[\sigma, t]_{\triangle\square_+} \equiv [\sigma, t]_{\triangle_+}.$$

Each of the context extension operations comes with a notion of parent maps and variables:

$$\frac{\gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} A \gamma \text{ type}_{\ell}}{\text{pt}_{\mu_+}^A : (\gamma : \Gamma, a :^{\mu_+} A \gamma) \to \Gamma} \quad \frac{\gamma : \Gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} A \gamma \text{ type}_{\ell}}{\gamma : \Gamma, a :^{\mu_+} A \gamma, \mathbf{\Theta}_{\mu}^{+} \vdash_{[\![p]\!]} zv_{\mu_+}^A \gamma a : A^{[\text{pt}_{\mu_+}^A, \mathbf{\Theta}_{\mu}^{+}]} \gamma a}$$

For the parent maps $\text{pt}_{\triangle_+}^A$, we make a definition by cases on whether or not $\Gamma$ is flat:

$$\text{pt}_{\triangle_+}^A \equiv \begin{cases} \text{in}_{\text{dm}} \text{ pt}_{\text{dm}}^A & \text{for} \quad \text{in}_{\text{dm}} \Gamma \\ \text{in}_{\text{sm}} \text{ pt}_{\triangle}^A & \text{for} \quad \text{in}_{\text{sm}} \Gamma. \end{cases}$$

The parent maps for $\diamond_+$ and $\square_+$ reduce to discrete parent maps of variables of modal type:

$$\text{pt}_{\diamond_+}^A \equiv \text{pt}_{\text{dm}}^{\diamond A} \quad \text{pt}_{\square_+}^A \equiv \text{pt}_{\text{dm}}^{\square A}.$$

Then, for $\triangle\diamond_+$ and $\triangle\square_+$, we combine this with the substitution above:

$$\text{pt}_{\triangle\diamond_+}^A \equiv \text{pt}_{\triangle_+}^{\diamond A} \quad \text{pt}_{\triangle\square_+}^A \equiv \text{pt}_{\triangle_+}^{\square A}.$$

72