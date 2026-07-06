40 Martin-Löf's type theory

We make one concession to readability by not completely annotating terms. For our formalism to be a GAT, the terms should be annotated with enough information to recover the derivation of their well-formedness; for example, the function application $F N$ should be annotated with the domain and codomain types of $F$. It is mechanical enough for a reader to deduce what annotations should be present in a completely formal presentation, so we will suppress them here.

In the following, we describe the skeleton of a formalism for our small type theory, highlighting the considerations that drive formalism design (as opposed to the design of computational models).

### 2.2.1 Intensional type theory

|  Judgment | Presuppositions | Reading  |
| --- | --- | --- |
|  $\Gamma \text{ ctx}$ |  | $\Gamma$ is a context  |
|  $\Gamma' \vdash \gamma : \Gamma$ | $(\Gamma, \Gamma' \text{ ctx})$ | $\gamma$ is a substitution from $\Gamma$ to $\Delta$  |
|  $\Gamma' \vdash \gamma = \gamma' : \Gamma$ | $(\Gamma' \vdash \gamma, \gamma' : \Gamma)$ | $\gamma$ and $\gamma'$ are equal substitutions  |
|  $\Gamma \vdash A \text{ type}$ | $(\Gamma \text{ ctx})$ | $A$ is a type in context $\Gamma$  |
|  $\Gamma \vdash A = A' \text{ type}$ | $(\Gamma \vdash A, A' \text{ type})$ | $A$ and $A'$ are equal types in context $\Gamma$  |
|  $\Gamma \vdash M : A$ | $(\Gamma \vdash A \text{ type})$ | $M$ is a term of type $A$ in context $\Gamma$  |
|  $\Gamma \vdash M = M' : A$ | $(\Gamma \vdash M, M' : A)$ | $M$ and $M'$ are equal terms  |

Figure 2.3: Judgments of the **ITT** formalism

**Judgments and presuppositions** Like a type theory, a formalism is based on a collection of judgments delineating the well-formed and equal types and elements. For **ITT**, we have the judgments shown in Figure 2.3. We use $\vdash$ and : for entailment and elementhood in formal judgments, reserving $\gg$ and $\in$ for computational judgments. Whereas a computational type theory *defines* the judgments, a formalism merely provides an interface in the form of a collection of rules.

To simplify the presentation of rules, we attach to each formal judgment a collection of *presuppositions*, assumptions under which it makes sense to state a judgment. For example, the judgment $\Gamma \vdash M : A$ presupposes that $\Gamma$ is a context and $A$ is a type; only under those circumstances does it make sense to ask whether $M$ is an element of $A$ supposing $\Gamma$. This allows us to omit hypotheses like $\Gamma \text{ ctx}$ and $\Gamma \vdash A$ type from rules when it is clear the rule would not make sense otherwise. Unlike the PER-based computational interpretation, in which we define the unary judgment forms from the binary, here we require both sides of an equation to be well-formed before we can state it.