changing in the definition every instance of “finite” by “size strictly less than $\kappa$” we get the correct notion, this is indeed the case. We carve out the definition with a fair amount of detail, since the applications we have in mind benefit from having an explicit syntax. The technicalities and motivations for introducing a generalized algebraic in the following way are presented in Cartmell [Car78].

From now on, we fix a regular cardinal $\kappa$, unless otherwise stated, all other ordinals mentioned will be strictly smaller than $\kappa$.

Let $V$ be a set such that $|V| = \kappa$, this set will be called the set of *variables*. We make an additional assumption on this set: Its elements have *canonical names*, this is $V = \{x_\alpha\}_{\alpha < \kappa}$. This is also known as an *enumeration*. This is a minor assumption that allows to change variables. Otherwise, we would need to prove a result similar to [Car78, Corollary, pp 1.32]$^5$. Let $A$ be any set, which as before is called *alphabet*. Following [Car78] we define inductively the collection of *expressions* $A^*$ over the alphabet $A$. An expression is any $\lambda$-sequence of $A \cup V \cup \{\{\} \cup \{\}\} \cup \{,\}$ subject to:

i) If $x_\alpha \in V$ then $x_\alpha \in A^*$,
ii) If $F \in A$ then $F \in A^*$,
iii) If $F \in A$ and $\{e_\alpha\}_{\alpha < \lambda} \subseteq A^*$ then $F(e_\alpha)_{\alpha < \lambda} \in A^*$.

A *premise* is any $\lambda$-sequence of $V \times A^*$. We will usually write premises as $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ where $x_\alpha$ are variables and $\Delta_\alpha$ are expressions for $\alpha < \lambda$. Suppose we have a premise $\Gamma$, or later a *context*, and we need an extra premise (or *context*), according to our variable numbering, formally, we must write $\Gamma$, $\{x_\alpha : \Delta_\alpha\}_{\lambda \leq \alpha < \mu}$, where $\lambda$ represents the number of variables in $\Gamma$. This is clearly a problem when the expression complexity increases. In order to avoid overloading the notation, we choose to reset the variable counting to only the essential variables in use. Under this convention, we will write $\Gamma$, $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ instead. We will freely assume that $\Gamma$ is a premise unless otherwise specified.

**Definition A.1.** A *judgment* is an expression over the alphabet $A$ that has one of the following forms:

1. Type judgment: $\Gamma \vdash \Delta \text{ Type}$.
2. Element judgment: $\Gamma \vdash t : \Delta$.

5This result states that under the substitution property the derived rules are stable under substitution of variables by another variables

91