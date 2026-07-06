Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:11

sense to study the contortion problems only with respect to the number of variables in $\Psi$, which in turn determines the size of the goal boundary $\phi$.

**Proposition 3.3.** *For any $\Gamma$,* $\mathrm{CARTESIAN}(\Gamma, \Psi, \phi)$ *is in $P$ as a function of $\Psi$ and $\phi$.*

*Proof.* For any $a(\Psi') : [\phi']$ in $\Gamma$, there are $(n + 2)^m$ many cartesian contortions for $m := |\Psi'|$ and $n = |\Psi|$. Since we treat the cell context (and therefore also the dimension $m$ of each of its cells) as constant, there are polynomially many contortions that we need to check. $\square$

If we include disjunctions into our dimension terms, we have $(2^n + 1)^m$ contortions of an $m$-dimensional cell into $n$ dimensions, which means brute-force is not polynomial for DISJUNCTIVE, even for fixed cell contexts. However, enumerating all DISJUNCTIVE contortions can still feasibly be done also in higher dimensions—in contrast to the Dedekind and De Morgan theories, whose sizes explode with growing $n$. In the case of DEDEKIND, the number of ways to contort an $m$-cube to fit an $n$-dimensional goal is $D(n)^m$ where $D(n)$ is the $n$-th Dedekind number [Awo26, App. B]. The Dedekind numbers grow extremely quickly: there are $D(6) = 7\,828\,354$ many ways to contort a 1-cube into a 6-dimensional cube; the 42-digit $D(9)$ was only recently computed using supercomputing [VHDCG$^+$24, Jäk23]. The problems DEDEKIND and DEMORGAN thus seem to be computationally very hard, and our focus in §4 will be on heuristics that quickly yield solutions to boundary problems that appear in practice, rather than on worst-case asymptotics. The following results give some indication of this difficulty.

**Proposition 3.4.** *There exist $\Gamma$ for which* $\mathrm{DEDEKIND}(\Gamma, \Psi, \phi)$ *is coNP-hard as a function of $\Psi$ and $\phi$.*

*Proof.* We give a reduction from the entailment problem for monotone Boolean formulas, which is equivalent to the equivalence problem for monotone Boolean formulas, which is known to be coNP-complete [Rei03, Theorem 15].

Given two monotone formulas $\varphi_0$ and $\varphi_1$ over variables $\vec{x} = x_1, \dots, x_n$, we want to decide whether $\varphi_0 \models \varphi_1$. Note that we can treat each $\varphi_i$ as a Dedekind dimension term $\vec{x} \vdash \varphi_i \dim$ by reading $\bot$ and $\top$ as $\mathbf{0}$ and $\mathbf{1}$ and disjunction and conjunction as $\vee$ and $\wedge$. We claim that $\varphi_0 \models \varphi_1$ iff the following boundary problem is solvable:

$$s(j) : [\ ] \mid l, \vec{x} \vdash_c ? : [l = \mathbf{0} \mapsto s(\varphi_0) \mid l = \mathbf{1} \mapsto s(\varphi_1)].$$

Suppose $\varphi_0 \models \varphi_1$. Then we can define a Dedekind contortion $\psi : (l, \vec{x}) \rightsquigarrow (j)$ as $\psi(l, \vec{x}) = (\varphi_0(\vec{x}) \vee (l \wedge \varphi_1(\vec{x})))$. The contorted cell $s(\psi)$ then solves the boundary problem.

Conversely, if $\varphi_0 \not\models \varphi_1$, then there is an assignment $\vec{e}$ to the variables $\vec{x}$ such that $\varphi_0(\vec{e}) = \mathbf{1}$ but $\varphi_1(\vec{e}) = \mathbf{0}$. But then any contortion $\psi : (l, \vec{x}) \rightsquigarrow (j)$ which would contort $s$ into the goal would be non-monotone, with $\psi(\mathbf{0}, \vec{e}) = \varphi_0(\vec{e}) > \varphi_1(\vec{e}) = \psi(\mathbf{1}, \vec{e})$, which is impossible with a Dedekind contortion. $\square$

Another perspective on contortion problems is given by considering not the cell context as constant, but instead the dimension of the goal boundary. Even restricting to 1-dimensional goals, contortion problems are NP-hard as soon as the contortion language includes two connections, which underlines that the contortion problems DEDEKIND and DEMORGAN are very complex.

**Proposition 3.5.** *For $\Psi$ containing at least one variable,* $\mathrm{DEDEKIND}(\Gamma, \Psi, \phi)$ *is NP-complete as a function of $\Psi$ and $\phi$.*