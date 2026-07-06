## B.2 Interlude: categorical facts

We collect and recall some categorical facts about general $\kappa$-contextual categories.

**Proposition B.7** (The slice $\kappa$-contextual category). *Let $\mathcal{C}$ be a $\kappa$-contextual category. For any object $B \in Ob_\mu(\mathcal{C})$ there is a $\kappa$-contextual category which is a full subcategory of the slice $\mathcal{C}_{/B}$ which has objects display maps $A \twoheadrightarrow B$ where $A \in Ob_\lambda(\mathcal{C})$ with $\lambda \geq \mu$.*

Since we will rarely use categories other than $\kappa$-contextual categories, we will employ the slice notation $\mathcal{C}_{/B}$ for the category from the previous proposition.

*Proof.* The proof is completely formal. The important fact to remember is that the pullback of a display map is also a display map. $\square$

It is a well known fact that the pasting of two pullbacks give us a pullback, in our case consider the following diagram:

$$\begin{array}{ccc} f^*B_\mu & \xrightarrow{q(f, B_\mu)} & B_\mu \\ \vdots & & \vdots \\ q(f, B_{\nu+1})^*B_{\nu+2} & \xrightarrow{q(q(f, B_{\nu+1}), B_{\nu+2})} & B_{\nu+2} \\ \downarrow & & \downarrow \\ f^*B_{\nu+1} & \xrightarrow{q(f, B_{\nu+1})} & B_{\nu+1} \\ \downarrow & & \downarrow \\ A_\lambda & \xrightarrow{f} & B_\nu \end{array}$$

Then if $\mu$ is a limit ordinal, the object $B_\mu$ is the limit of the sequence on the right-hand side. Thus, $f^*B_\mu$ is the limit of the sequence on the left-hand side. Note that pairwise we have $q(f, B_{\nu+1})^*B_{\nu+2} = f^*B_{\nu+2}$ and $q(f, B_{\mu+2}) = q(q(f, B_{\mu+1}), B_{\mu+2})$.

If $f: A_\lambda \to B_\nu$ and $p_\nu: B_\mu \twoheadrightarrow B_\nu$ is a display map with $\mu = \nu + 1$, using the

114