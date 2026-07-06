v) A set of axioms.

To understand our generalization let us examine the previous definition in more detail, for this we need some preliminary notions. An *expression* is a finite sequence of $A \cup V \cup \{\{\} \cup \{\}\} \cup \{,\}$. Inductively:

i) Elements of $V$ and $A$ are expressions,
ii) If $f \in A$ and $e_1, e_2, ..., e_n$ are expressions, then $f(e_1, e_2, ..., e_n)$ is an expression.

The set of expressions is denoted by $E$. This is simply to say that an expression is a finite string taken from the set $A \cup V \cup \{\{\} \cup \{\}\} \cup \{,\}$. A *premise* is a finite (possibly empty) sequence of $V \times E$. A *conclusion* is an n-tuple of expressions, i.e. any element of $E^n$ for some $n \in \mathbb{N}$. Finally, a *rule* is given by a premise $P$ and a conclusion $C$. Rules are written as: $P \vdash C$. This intends to convey the idea that under the premise $P$, the conclusion $C$ is a valid expression. Whenever $P$ is a premise we will write $x_1 : \Delta_1, x_2 : \Delta_2, ..., x_n : \Delta_n$. For a conclusion, this is slightly more involved since we differentiate depending on the size of the tuple. For example, if we have a 1-tuple $\Delta$, then we write $\Delta_{\text{Type}}$. We favour the notation “:” from type theory instead of the set theoretic one “$\epsilon$” used by Cartmell. Furthermore, we will take advantage of conventions and notation from type theory.

The most important definition we will need to change is that of a *context*. In a Cartmell theory, a *context* is the premise such that a rule

$$x_1 : \Delta_1, x_2 : \Delta_2(x_1), ..., x_n : \Delta_n(x_1, x_2, \cdots, x_{n-1}) \vdash \Delta(x_1, x_2, \cdots, x_n) \text{ Type}$$

is a *derived rule*.

The only difference between Cartmell theories and infinitary Cartmell theories is that in we allow infinitely many variables in the contexts. Just as any Cartmell theory gives rise to a contextual category, the same is true for the infinitary case with the appropriate generalized version of a contextual category.

### A.1 Generalized algebraic theories

In this section, we give the formal definition of an infinitary Cartmell theory. We follow Cartmell [Car78] to develop the theory; however, there will be some instances where a change has to be made. We could say that by

90