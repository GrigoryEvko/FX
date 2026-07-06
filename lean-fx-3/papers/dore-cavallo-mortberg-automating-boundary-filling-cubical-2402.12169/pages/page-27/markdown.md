Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:27

We try to solve KANCSP with no open sides. This CSP has 7 variables corresponding to sides $i$, $j$, $k$ and a backside $l = \mathbf{0}$. If we can construct all 7 cubes in a compatible way, we have solved the boundary problem as we can then return a filler in direction $\mathbf{0} \rightarrow \mathbf{1}$. Note in particular that the dimension $\ell$ is only part of the filler term, while the cube we are filling is three-dimensional.

After imposing the first set of constraints, the domains for the $i$ and $j$ sides are significantly reduced, e.g., $D_{(i=0)} = \{p(\Sigma)\}$ for $\Sigma : \mathbf{I}^3 \rightarrow \mathcal{P}(\mathbf{I}^2)$ is given by:

$$\begin{array}{cccccc} 000 \mapsto \{00\} & 001 \mapsto \{00\} & 010 \mapsto \{00, 01\} & 011 \mapsto \{01\} \\ 100 \mapsto \{00, 10\} & 101 \mapsto \{10\} & 110 \mapsto \{00, 01, 10, 11\} & 111 \mapsto \{11\} \end{array}$$

The PPM $\Sigma$ gives rise to 9 contortions of $p$, which contrasts with $D(3)^2 = 400$ total contortions of $p$. The domains for $D_{(k=0)}$, $D_{(k=1)}$, and the back side $D_{(l=0)}$ still contain all contortions of $x$, $p$ and $q$ into three dimensions since the $k$ sides of the goal boundary do not give any indication which contortion could be used for this side of the filler.

The second set of constraints ensures that all sides of the Kan filler have matching boundaries, after which we find a solution to KANCSP that gives rise to the following filler:

$$\Gamma \mid i, j, k \vdash \text{fill}^{\mathbf{0} \rightarrow \mathbf{1}} \ l. \left[ \begin{array}{lll} i = \mathbf{0} \mapsto p(j, k \wedge l) & j = \mathbf{0} \mapsto q(i, k) & k = \mathbf{0} \mapsto x \\ i = \mathbf{1} \mapsto p(j, k \wedge l) & j = \mathbf{1} \mapsto q(i, k) & k = \mathbf{1} \mapsto p(j, l) \end{array} \right] \ q(i, k) \ \text{cell}$$

This filler captures the argument sketched in Figure 1, albeit in a single step: the $p$ sides are mapped to the $k = \mathbf{1}$ side such that they cancel out as in Figure 1(c), while the $q$ sides are constantly mapped to the backside of the filler, which is the cube from Figure 1(d).

**5.2. A solver for Kan.** We now give an algorithm to construct fillers of open cubes which might have fillers on their faces, and not only contorted terms as in KANCSP. We also make use of a procedure $\text{KANFILL}(\Gamma, \Psi, \phi)$ which produces fillers with the same dimension as $\phi$: we check for any face of $\phi$ if it gives rise to a natural filler.

The difficult part of KAN is the construction of higher-dimensional fillers, which might possibly have fillers on their sides. We introduce a variable $d$ to iteratively deepen the level of such nested fillers, which effects a sort-of “breadth-first” search for nested fillers.

Given a goal boundary $\phi$, we search for solutions either by natural fillers or by higher-dimensional fillers constructed with KANCUBE on line 4. In KANCUBE, we first select a set of sides that are left open on line 6 and then pick a solution to the corresponding KANCSP on line 7, which will fill all sides not left open with contorted cells. Finally, we call KANSOLVER recursively on the open sides on line 9, where $\lceil \phi' [i = e] \rceil$ denotes the boundary at $i = e$ induced by the faces already present in $\phi'$.