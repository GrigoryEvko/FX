28:12

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

Proof. Membership in NP follows from Proposition 3.2. For completeness, we give a reduction from SAT. Suppose we have a Boolean CNF formula $\varphi$ over $\vec{x} = x_1, \ldots, x_n$. Replace each $\neg x_i$ in $\varphi$ by a variable $y_i$ to obtain a dimension term $r$ in variables $\vec{x}, \vec{y}$. Then $\varphi$ is satisfiable if and only if there is $\psi: () \rightsquigarrow (\vec{x}, \vec{y})$ such that $r\langle\psi\rangle = 1$ and $(x_k \wedge y_k)\langle\psi\rangle = 0$ and $(x_k \vee y_k)\langle\psi\rangle = 1$ for each $k$. Take $\Gamma_\varphi$ to be the context

$$a: [], p(z, j_0, j_1): [], q(\vec{x}, \vec{y}, i): [i = 0 \mapsto a \mid i = 1 \mapsto p(r, \bigvee_k (x_k \wedge y_k), \bigwedge_k (x_k \vee y_k))]$$

and consider the boundary problem $\Gamma_\varphi \mid i \vdash_c ?: [i = 0 \mapsto a \mid i = 1 \mapsto p(1, 0, 1)]$. Any $\psi: () \rightsquigarrow (\vec{x}, \vec{y})$ such that $r\langle\psi\rangle = 1$ and $(x_k \wedge y_k)\langle\psi\rangle = 0$ and $(x_k \vee y_k)\langle\psi\rangle = 1$ for each $k$ yields a solution $\Gamma_\varphi \mid i \vdash_c q(\psi, i)$ cell. Conversely, any solution to the problem will be of the form $\Gamma_\varphi \mid i \vdash_c q(\psi', r)$ cell for some $\psi': i \rightsquigarrow (\vec{x}, \vec{y})$ and $i \vdash r$ dim, in which case $\psi'(1): () \rightsquigarrow (\vec{x}, \vec{y})$ induces a satisfying assignment for $\varphi$.

The same reduction also works to establish that DEMORGAN($\Gamma, \Psi, \phi$) is NP-hard. In fact, the proof can be slightly simplified as the negated variables do not have to be replaced first.

**Corollary 3.6.** For $\Psi$ with at least one variable, DEMORGAN($\Gamma, \Psi, \phi$) is NP-complete as a function of $\Psi$ and $\phi$.

In summary, contortion problems are, even if decidable, not necessarily tractable for the more complicated contortion theories that we consider.

**3.2. Undecidability of Kan solving.** The Kan filling problem has—in contrast to the contortion problems—an infinite search space, and we will in the following establish that it is undecidable. This result is independent of which underlying contortion theory one considers. Let us formally introduce the problem of finding Kan cells.

**Problem 3.7 (KAN).** Given a Kan boundary $\Gamma \mid \Psi \vdash \phi$ bdy, the problem $\text{KAN}(\Gamma, \Psi, \phi)$ is to determine if there exists a Kan cell $t$ such that $\Gamma \mid \Psi \vdash t: [\phi]$.

For example, the problem (2.2) of inverting a path does not have a solution in DEDEKIND but does have solutions in KAN, such as $\text{fill}^{0 \to 1} i.[j = 0 \mapsto p(i) \mid j = 1 \mapsto p(0)] p(0)$.

Unlike contortion solving, deciding whether a Kan solution to a problem exists is not only difficult but actually impossible in general. Intuitively, Kan solving is a higher-dimensional generalisation of a more familiar undecidable problem: the word problem for a finitely presented group. This is the problem of deciding, for finite sets $X$ of generators and $R$ of equations, whether two words on $X$ are equal in the free group on $X$ modulo $R$. In Kan solving, the context $\Gamma$ can be thought of as a collection of generators in which each $(n + 1)$-dimensional cell serves as an “equation” between $n$-dimensional cells, while Kan filling generalises the multiplication and inverse operations available in a group.

We now make this precise by giving a reduction from the word problem for a given finitely presented group to Kan solving over a corresponding context. This argument applies to Kan solving relative to any of the sublanguages of contortions (cartesian, disjunctive, Dedekind, De Morgan) we have introduced. As a side effect, we will get to see some more complex constructions in the cubical type theory we have defined.

A group presentation $\langle X|R\rangle$ consists of a finite set $X$, the generators, and a finite set $R$ of equations of the form $w = 1$ where $w$ is a word on $X$, i.e., a finite list of the form $x_0^{\alpha_0}, \ldots, x_k^{\alpha_k}$ where each $x_i$ is in $X$ and each $\alpha_i$ is $-1$ or $1$. The group $G$ presented by $\langle X|R\rangle$ is the free group on $X$ modulo the equations in $R$; given words $w, v$ over $X$, we write $w \equiv_G v$