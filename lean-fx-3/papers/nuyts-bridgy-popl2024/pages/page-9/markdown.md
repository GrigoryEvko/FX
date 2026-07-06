Internal and Observational Parametricity for Cubical Agda

8-9

where $\Gamma \setminus x$ would appear in the CH theory. An example of such a rule is BDG-ELIM-CH. We call these constraints *freshness typechecking constraints*. Their definitions are given in Definition 2.1, 2.2. Such freshness constraints can be raised on different occasions during typechecking, which we list here.

- We are typechecking a bridge application $\Gamma \vdash aa x$.
- We are typechecking an affine function elimination $\Gamma \vdash f x$.
- We are computing (so reducing or comparing terms) and need capturing to occur.

Note that affine functions are exactly like bridges, but without fixed endpoints. Affine functions will be used to express the type of **extent**, for example. The first two cases are similar. If the raised constraint is found satisfiable, typechecking can continue and perhaps succeed. Else, a typechecking error occurs. In the third case, a freshness constraint called *semi-freshness* is raised. If it is found satisfiable computing goes on. Else, computing halts (no further reduction, or a failed comparison).

We now present the primitives of Agda --bridges: their typing rules and equational theory, details about their implementation as well as core theorems they guarantee. Following the above, several of these typing rules have premises that are (semi-) freshness constraints. Recall that all the theorems we obtain using Agda --bridges are available in our accompanying library.

## 2.3 Affine Functions and Bridges

First of all, Agda --bridges postulates the existence of a bridge interval type **BI** equipped with two endpoints **bi0, bi1 : BI** and no further operations. Next, we define the type former of affine functions. Bridges will essentially be affine functions with definitionally fixed endpoints.

2.3.1 *Affine Functions*. Affine functions are implemented as normal Agda dependent functions but their domain is **BI** and it carries what is called a tick annotation (building on [Veltri and Vezzosi 2020, 2023]). The type of non-dependent affine functions with codomain $C$ is denoted (@tick $x$ : **BI**) $\rightarrow$ $C$ or @**BI** $\rightarrow$ $C$. We call an affine function $A$ : (@tick $x$ : **BI**) $\rightarrow$ **Type** an (affine) line of types and such lines are sometimes denoted $x$. $Ax$.

Given a line $A$ : (@tick $x$ : **BI**) $\rightarrow$ **Type** one can form the type of dependent affine functions over $A$ denoted (@tick $x$ : **BI**) $\rightarrow$ $Ax$. Compared to normal dependent functions, the tick annotation has the net effect of raising an additional freshness constraint while typechecking the application of a function $f$ : (@tick $x$ : **BI**) $\rightarrow$ $Ax$ to a bridge variable ($x$ : **BI**) in a given context. That is to say, the following typing rule is implemented.

$$\frac{\Gamma \vdash f : (@tick \ x : BI) \rightarrow Ax \quad (x : BI) \in \Gamma \quad fresh(f, x)}{\Gamma \vdash f x : Ax} \quad TICK-APP$$

The other rules of (@tick $x$ : **BI**) $\rightarrow$ $Ax$ are those of normal dependent functions. Notice how this time the context in which $f$ typechecks is not restricted. The constraint on free variables implied by the context restriction operation of (2.2) is instead expressed as a typechecking side condition denoted $fresh(f, x)$ (understood to live at the same context $\Gamma$ than $f$). We call the latter side condition a freshness constraint and it is defined as the following decidable condition on $f, x$.

*Definition 2.1 (Freshness constraint)*. Setting $\Gamma = \Gamma_1$, ($x$ : **BI**), $\Gamma_2$, the freshness constraint $fresh(f, x)$ is satisfied if for every free variable $v$ of $f$ one of the following holds:

- $v$ appears in $\Gamma_1$ (i.e., $v \in \Gamma_1$)
- $v$ appears in $\Gamma_2$ and is a path or a bridge variable$^3$, i.e., ($v : I$) $\in \Gamma_2$ or ($v : BI$) $\in \Gamma_2$.

We also adopt the convention that **bi0, bi1** are always fresh for any term $f$.

$^3$Additionally, $v$ can be a variable witnessing the truth of a face constraint (Section 5.2) that does not mention $x$.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.