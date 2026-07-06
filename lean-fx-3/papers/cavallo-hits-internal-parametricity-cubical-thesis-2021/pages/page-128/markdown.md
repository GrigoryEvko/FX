116

General higher inductive types

# Contexts

$$\frac{\Delta \mid \mathcal{K} \blacktriangleright \Theta \text{ actx}}{\Delta \mid \mathcal{K} \blacktriangleright (\Theta, a : A) \text{ actx}} \quad \frac{\Delta \mid \mathcal{K} \blacktriangleright \Theta \text{ actx} \quad \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright A \text{ atype}}{\Delta \mid \mathcal{K} \blacktriangleright (\Theta, a : A) \text{ actx}}$$

# Substitutions

$$\frac{\Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright \cdot \in \cdot}{\Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright \theta = \theta' \in \Theta \quad \Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright M = M' \in A} \quad \frac{\Delta \mid \mathcal{K} \mid \Theta' \blacktriangleright (\theta, M/a) = (\theta', M'/a) \in (\Theta, a : A)}{}$$

# Types

$$\frac{\delta = \delta' \in \Delta}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \text{IND}(\delta) = \text{IND}(\delta') \text{ atype}}$$

$$\frac{A = A' \text{ type} \quad a : A \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright B = B' \text{ atype}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright (a : A) \rightarrow B = (a : A') \rightarrow B' \text{ atype}}$$

$$\frac{x : \mathbb{I} \gg \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright A = A' \text{ atype}}{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright M_0 = M'_0 \in A[0/x] \quad \Delta \mid \mathcal{K} \mid \Theta \blacktriangleright M_1 = M'_1 \in A[1/x]} \quad \frac{\Delta \mid \mathcal{K} \mid \Theta \blacktriangleright \text{PATH}(x, A, M_0, M_1) = \text{PATH}(x, A', M'_0, M'_1) \text{ atype}}{}$$

Figure 6.3: Inductive definition of the argument contexts, substitutions, and types. The ambient context $\Gamma$ is omitted for readability.

boundary constraint. In order to ensure that the recursive arguments to a constructor are strictly positive in the type being defined, the domain of an argument function type $(a : A) \rightarrow B$ is not itself an argument type but an ordinary “external” type.

This language could be straightforwardly extended to include product types $(a : A) \times B$, for example, without significantly disrupting the development that follows. Our choice of a fairly minimal theory is motivated by a desire to avoid huge definitions and proofs by case analysis in what follows, not by any fundamental concerns about particular extensions.

We will take for granted standard admissibility theorems such as weakening and stability under substitution for the formal type theory; the theory does not contain any features that would interfere with standard proofs of such results.