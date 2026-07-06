28:10

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

Remark 2.14. In [DCM24], the rule we gave for the fill constructor had the premise $\Gamma \mid \Psi, i \vdash \phi$ bdy in place of $\Gamma \mid \Psi \parallel i \vdash \phi$ bdy. This is incorrect: it would allow us for every $\Gamma \mid \Psi \vdash t, u$ cell to construct a path

$$\Gamma \mid \Psi, i \vdash \text{fill}^{0 \to i} j. [j = 1 \mapsto u] t : [i = 0 \mapsto t \mid i = 1 \mapsto u]$$

between them. Fortunately, our results and implementation from [DCM24] did not actually make use of this error.

### 3. COMPLEXITY OF CONTORTION SOLVING AND UNDECIDABILITY OF KAN FILLING

After having specified what solutions to boundary problems look like, we will now classify the different kinds of problems that we study in this paper. We will first look at the complexities of contortion solving for the different contortion theories that we introduced, and then show that the problem of finding Kan fillers is undecidable.

3.1. Complexity of contortion solving. Let us formally introduce the contortion problem for the different contortion theories that we study.

Problem 3.1 (CARTESIAN/DISJUNCTIVE/DEDEKIND/DEMORGAN). Given $\Gamma \mid \Psi \vdash_c \phi$ bdy,

- the problem CARTESIAN($\Gamma, \Psi, \phi$) is to determine if there exists a cartesian contortion $\psi: \Psi \leadsto \Psi'$ such that $\Gamma \mid \Psi \vdash_c a(\psi) : [\phi]$ for some variable $a(\Psi') : [\phi']$ in $\Gamma$.
- the problem DISJUNCTIVE($\Gamma, \Psi, \phi$) is to determine if there exists a disjunctive contortion $\psi: \Psi \leadsto \Psi'$ such that $\Gamma \mid \Psi \vdash_c a(\psi) : [\phi]$ for some variable $a(\Psi') : [\phi']$ in $\Gamma$.
- the problem DEDEKIND($\Gamma, \Psi, \phi$) is to determine if there exists a Dedekind contortion $\psi: \Psi \leadsto \Psi'$ such that $\Gamma \mid \Psi \vdash_c a(\psi) : [\phi]$ for some variable $a(\Psi') : [\phi']$ in $\Gamma$.
- the problem DEMORGAN($\Gamma, \Psi, \phi$) is to determine if there exists a De Morgan contortion $\psi: \Psi \leadsto \Psi'$ such that $\Gamma \mid \Psi \vdash_c a(\psi) : [\phi]$ for some variable $a(\Psi') : [\phi']$ in $\Gamma$.

All four problems are decidable: there are finitely many cell variables in $\Gamma$ and all contortion theories that we consider are finite, so we can try all possible contortions of each cell variable by brute-force.

Moreover, we can efficiently recognise a solution if we are given one. For this, we need to decide equality between contorted cells, for which we need to normalise a contorted cell by looking at its boundary, if it is specified. For example, in context (2.1) the cell $p(0)$ normalises to $a$. The number of such normalisation steps is bounded by the length of the context.

Proposition 3.2. CARTESIAN($\Gamma, \Psi, \phi$), DISJUNCTIVE($\Gamma, \Psi, \phi$), DEDEKIND($\Gamma, \Psi, \phi$) and DEMORGAN($\Gamma, \Psi, \phi$) are in NP as functions of $\Gamma$, $\Psi$, and $\phi$.

Proof. For any contortion theory, we can determine in polynomial time if a given variable $a(\Psi') : [\phi']$ and contortion $\psi: \Psi \leadsto \Psi'$ form a solution to a boundary problem, i.e., that $\Gamma \mid \Psi \vdash_c a(\psi) : [\phi]$, by normalising $a(\psi)$ and $\phi$ and comparing. Note that the complexity of our check increases polynomially with the number of cells in $\Gamma$; the dimension variables in $\Psi$; and the specified faces of $\phi$. $\square$

Boundary problems have multiple parameters; for more detailed analysis of the complexity of the different contortion problems we will in the following fix some of them. In our contortion solver in §4, we will primarily study boundary problems over some small fixed cell context $\Gamma$, and try to contort a given cell into ever higher dimensions. It hence makes