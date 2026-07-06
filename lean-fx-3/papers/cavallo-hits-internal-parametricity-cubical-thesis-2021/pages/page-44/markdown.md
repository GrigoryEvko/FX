32

Martin-Löf's type theory

Proof. Function types are always values: we have $(a:A) \to B \Downarrow (a:A) \to B$ and likewise for $(a:A') \to B'$. Thus the conclusion follows from the hypotheses and the definition of the type system, which gives $\tau_i \vDash (a:A) \to B \approx (a:A') \to B' \downarrow R$ (for a certain $R$). $\square$

Next, we have the introduction rule, which gives conditions under which we may construct (i.e., introduce) an element of a function type. An element of $(a:A) \to B$ is, as one might expect, an element of $B$ that is typed in a context extended with a hypothesis of type $A$.

# **Rule 2.1.33 (Function introduction).**

$$\frac{\Vdash A \text{ type} \quad a:A \gg B \text{ type} \quad a:A \gg N = N' \in B}{\Vdash \lambda a.N = \lambda a.N' \in (a:A) \to B}$$

Proof. $\lambda$-abstractions are always values, so it is enough to check that $\tau_i \vDash (a:A) \to B \downarrow R$ with $\lambda a.N \approx \lambda a.N' \in R$, which holds by the hypotheses and definition of $\tau_i$. $\square$

So far we have dealt only with values; now we come to some actual computation. Whereas we *introduce* a function by abstracting a variable, we use (or *eliminate*) a function by applying it to some term.

# **Rule 2.1.34 (Function elimination).**

$$\frac{\Vdash F = F' \in (a:A) \to B \quad \Vdash M = M' \in A}{\Vdash FM = F'M' \in B[M/a]}$$

Proof. From the assumption $\Vdash F = F' \in (a:A) \to B$ and the definition of the relation for the function type, we have that $F \Downarrow \lambda a.N$ and $F \Downarrow \lambda a.N'$ for some $N,N'$ such that $a:A \gg N = N' \in B$. We may instantiate the latter judgment with the closing substitution $(M/a) = (M'/a) \in (a:A)$ to obtain $\Vdash N[M/a] = N'[M'/a] \in B[M/a]$. Expanding the definition, we have $B[M/a] \Downarrow V, N[M/a] \Downarrow W$, and $N'[M'/a] \Downarrow W'$ with $\tau_i \vDash V \downarrow R$ (for some $R$) and $W \approx W' \in R$.

Referring to the operational semantics for functions in Figure 2.2, we see that $FM \longmapsto^* (\lambda a.N)M$ and $(\lambda a.N)M \longmapsto N[M/a]$; thus $FM \Downarrow W$. Likewise, we have $F'M' \Downarrow W'$. It therefore follows from $W \approx W' \in R$ that $\Vdash FM = F'M' \in B[M/a]$. $\square$

We can show that the operational semantics rule $(\lambda a.N)M \longmapsto N[M/a]$ gives rise to an equation in the type theory: if we define a function by abstracting a variable in a term and then apply it to some second term, this is the same as substituting the second term for the variable in the first. Such a rule that governs the reduction of an elimination form applied to an introduction form is often called a $\beta$-rule.