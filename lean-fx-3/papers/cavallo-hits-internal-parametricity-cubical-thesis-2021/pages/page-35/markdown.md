A logic of programs 23

The open judgments are defined by *functionality*: an open type is well-formed when it takes equal instantiations of its variables to equal closed types, and likewise for elements. The two open judgments are defined together with the *context judgment* $\Gamma$ ctx and the *closing substitution* judgment $\Vdash \gamma \in \Gamma$. A context is a collection of typed variables $(a_1 : A_1, \dots, a_n : A_n)$, while a closing substitution into a context $\Gamma$ is a list of instantiations $(M_1/a_1, \dots, M_n/a_n)$ for the variables listed in $\Gamma$. Given a term $M$ and a substitution $\gamma$, we write $M\gamma$ for the result of applying the substitutions in $\gamma$ to $M$.

**Definition 2.1.10 (Contexts, closing substitutions, and open judgments).**

- • *Closing substitutions*: $\Vdash \gamma = \gamma' \in \Gamma$ is the least judgment closed under the following rules.

$$\frac{\vdash \cdot = \cdot \in \cdot}{\vdash \cdot \cdot = \cdot \in \cdot} \quad \frac{\vdash \gamma = \gamma' \in \Gamma \quad \vdash M = M' \in A\gamma}{\vdash (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)}$$

- • *Open types*: $\Gamma \gg A = A'$ type is defined to hold when $\Vdash A\gamma = A'\gamma'$ type holds for all $\vdash \gamma = \gamma' \in \Gamma$.
- • *Open terms*: $\Gamma \gg M = M' \in A$ is defined to hold when $\Vdash M\gamma = M\gamma' \in A\gamma$ holds for all $\vdash \gamma = \gamma' \in \Gamma$.
- • *Contexts*: $\Gamma = \Gamma'$ ctx is the least judgment closed under the following rules.

$$\frac{\cdot = \cdot \text{ ctx}}{\cdot = \cdot \text{ ctx}} \quad \frac{\Gamma = \Gamma' \text{ ctx} \quad \Gamma \gg A = A' \text{ type}}{(\Gamma, a : A) = (\Gamma', a : A') \text{ ctx}}$$

The unary judgments $\Vdash \gamma \in \Gamma$, $\Gamma \gg A$ type, $\Gamma \gg M \in A$, and $\Gamma$ ctx are shorthand for $\Vdash \gamma = \gamma \in \Gamma$, $\Gamma \gg A = A$ type, $\Gamma \gg M = M \in A$, and $\Gamma = \Gamma$ ctx respectively.

**Notation 2.1.11.** When we want to emphasize the dependence of the judgments on the background type system, we add the prefix $\tau \vDash \dots$, as in $\tau \vDash \Gamma \gg A = A'$ type.

**Notation 2.1.12.** In a value type system $\tau$, given $A$ type, we write $[[A]]^\tau$ for the necessarily unique value relation such that $\tau \vDash A \downarrow [[A]]^\tau$. We omit the annotation $\tau$ when it is clear from context.

Having defined the type-theoretic judgments, we can begin checking that they satisfy the kind of properties we would expect, assembling a collection of rules that can be used to build up larger results without explicitly working with the definitions of the judgments. From this point forward, we assume that our candidate type system $\tau$ is a genuine type system. As all of these rules are standard and fairly intuitive, we will not provide proofs except to give a feel for the general shape of the arguments; for a more thorough tour, we refer as always to [Ang19].