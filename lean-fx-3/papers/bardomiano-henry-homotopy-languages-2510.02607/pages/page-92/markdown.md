3. Type equality judgment: $\Gamma \vdash \Delta \equiv \Delta'$.
4. Term equality judgment: $\Gamma \vdash t \equiv_\Delta t'$.

where $\Gamma$ is a premise.

Given a premise $\Gamma$, $\{e_\alpha\}_{\alpha < \lambda}$ expression and $\{x_\alpha\}_{\alpha < \lambda}$ variables then the new expression

$$\Gamma[e_\alpha | x_\alpha]_{\alpha < \lambda}$$

it is obtained by simultaneously changing the variables in $\Gamma$ by the expressions. This process, unsurprisingly, is called *substitution* of variables. Along with the infinitary substitutions, we will also allow operations to have possibly infinite arity. This is made explicit:

**Definition A.2.** A $\kappa$-*pretheory* $T$ consists of the following data:

i) A set $S$, called the set of *sort symbols*,
ii) A set $O$, called the set of *operation symbols*,
iii) For each sort symbol $B$, a judgment of the form:

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash B(x_\alpha)_{\alpha < \lambda} \text{ Type}$$

where $\lambda$ is some ordinal strictly smaller than $\kappa$,

iv) For each operator symbol $F$, a judgment:

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash F(x_\alpha)_{\alpha < \lambda} : \Delta$$

where $\lambda$ is an ordinal strictly smaller than $\kappa$,

v) A set of judgments, each of which is either a type equality judgment or a term equality judgment, listed in theorem A.1. This is the set of *axioms* of the $\kappa$-pretheory.

The following definitions are of inductive nature:

**Definition A.3.** 1. A premise $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$ is a *context* if the judgment

$$\{x_\beta : \Delta_\beta\}_{\beta < \alpha} \vdash \Delta_\alpha \text{ Type}$$

is a *derived judgment* of $T$ for every $\alpha < \lambda$. Whenever we want to specify that a premise $\Gamma$ is a context we will write $\vdash \Gamma \text{ Ctxt}$.

92