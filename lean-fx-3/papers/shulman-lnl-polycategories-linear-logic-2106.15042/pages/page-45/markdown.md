Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:45

**Proposition 8.1.** *There is a bijection between the valid judgments $R \text{ type}^{\tau}$ and the $\tau$-objects of $\tilde{S}_{\mathbb{D}}$.*

*Proof.* Define the *height* of $R \text{ type}^{\tau}$ recursively: the height of an object of $\mathcal{S}$ is zero, while that of $\bigodot_{\mathcal{C}}[R_1, \ldots, R_n]$ is one more than the maximum height of $R_1, \ldots, R_n$. (If $n = 0$, the height of $\bigodot_{\mathcal{C}}[]$ is 1.) I claim that there is a bijection between the valid judgments $R \text{ type}^{\tau}$ of height $\le n$ and the $\tau$-objects of $\mathcal{S}_n$. This is true for $n = 0$. The objects of $\mathcal{S}_{n+1}$ are those of $\mathcal{S}_n$ plus a new vertex for each $u : \partial\mathcal{C} \to \mathcal{S}_n$ not factoring through $\mathcal{S}_{n-1}$. But the latter are the applications of the $\bigodot_{\mathcal{C}}$-rule with at least one premise of height $n$, hence whose conclusion has height $n + 1$. $\square$

We denote the sequents in entries-only style as $\vdash \Phi$, where $\Phi$ is an admissible list of signed types, defined analogously to the semantic case in Section 4. The structural rules are shown in Figure 2b. The first is the identity rule and the second is the cut rule. The third incorporates exchange for all types, plus contraction and weakening for nonlinear types, as in Section 4. Similarly, the generator rule in Figure 2c says that every morphism of $\mathcal{S}$ induces a derivation of a sequent.

We may write $\Theta \mid \Gamma \vdash \Delta$ for $\vdash \Theta^-, \Gamma^-, \Delta^+$, and $\Theta \vdash X$ for $\vdash \Theta^-, X^+$. In this notation, the identity and cut rules multifurcate into linear and nonlinear versions:

$$\begin{array}{l} \frac{A \text{ type}^{\text{L}}}{\cdot \mid A \vdash A} \qquad \frac{X \text{ type}^{\text{NL}}}{X \vdash X} \qquad \frac{\Upsilon \vdash X \qquad \Theta, X \vdash Y}{\Theta, \Upsilon \vdash Y} \\ \frac{\Theta' \mid \Gamma' \vdash \Delta', A \qquad \Theta \mid \Gamma, A \vdash \Delta}{\Theta, \Theta' \mid \Gamma, \Gamma' \vdash \Delta, \Delta'} \qquad \frac{\Upsilon \vdash X \qquad \Theta, X \mid \Gamma \vdash \Delta}{\Theta, \Upsilon \mid \Gamma \vdash \Delta}. \end{array}$$

We divide the logical rules into *invertible* (right rules for negative types and left rules for positive types) and *noninvertible* (left rules for negative types and right rules for positive types). The generic noninvertible rule is in Figure 2d. Here $\varepsilon$ and the $\varepsilon_j$'s are signs $+, -$. For instance, if $\mathcal{C}$ is the cone for $\otimes$, with objects $a, b$ and vertex $c$, there is one abstract projection $f \in \mathcal{C}(a^-, b^-, c^+)$ and the rule becomes

$$\frac{A \text{ type}^{\text{L}} \qquad B \text{ type}^{\text{L}}}{\cdot \mid A, B \vdash A \otimes B}.$$

If $\mathcal{C}$ is the cone for $\&$, with objects $a, b$ and vertex $c$, there are two abstract projections $f \in \mathcal{C}(a^+, c^-)$ and $g \in \mathcal{C}(b^+, c^-)$, and the rule becomes two:

$$\frac{A \text{ type}^{\text{L}} \qquad B \text{ type}^{\text{L}}}{\cdot \mid A \& B \vdash A} \qquad \frac{A \text{ type}^{\text{L}} \qquad B \text{ type}^{\text{L}}}{\cdot \mid A \& B \vdash B}.$$

The rules for the modalities are

$$\frac{X \text{ type}^{\text{NL}}}{X \mid \cdot \vdash \mathsf{F}X} \qquad \frac{A \text{ type}^{\text{L}}}{\mathsf{U}A \mid \cdot \vdash A} \qquad \frac{X \text{ type}^{\text{NL}}}{X \mid \not\perp X \vdash \cdot} \qquad \frac{A \text{ type}^{\text{L}}}{\cap A \mid A \vdash \cdot}$$

Unlike noninvertible rules in most common sequent calculi, ours does not build in a cut. But we can always apply a cut afterwards, since the latter is primitive in our system. (We leave cut-elimination for future study.) Since the modalities are the most novel aspect of this calculus, we list their derived cut-containing rules:

$$\frac{\Theta \vdash X}{\Theta \mid \cdot \vdash \mathsf{F}X} \qquad \frac{\Theta \mid \Gamma, A \vdash \Delta}{\Theta, \mathsf{U}A \mid \Gamma \vdash \Delta} \qquad \frac{\Theta \vdash X}{\Theta \mid \not\perp X \vdash \cdot} \qquad \frac{\Theta \mid \Gamma \vdash \Delta, A}{\Theta, \cap A \mid \Gamma \vdash \Delta}.$$