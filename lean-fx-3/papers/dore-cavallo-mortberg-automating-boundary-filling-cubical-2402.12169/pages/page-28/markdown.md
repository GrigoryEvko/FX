28:28

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

Algorithm 2 Finding Kan cells

Input: \(\Gamma \mid \Psi \vdash \phi\) bdy, depth variable \(d\)

Output: \(\Gamma \mid \Psi \vdash t : [\phi]\), if \(\mathrm{KAN}(\Gamma, \Psi, \phi)\) solvable with \(\leq d\) nested Kan fillers

1: procedure KANSOLVER(\(\Gamma, \Psi, \phi, d\))
2:    if \(d = 0\) then
3:    return Unsolvable
4:    \(t \leftarrow \mathrm{KANFILL}(\Gamma, \Psi, \phi) \cup \mathrm{KANCUBE}(\Gamma, \Psi, \phi, d)\)
5: procedure KANCUBE(\(\Gamma, \Psi, \phi, d\))
6:    \(Ope \leftarrow \mathcal{P}(\{(i = e) \mid i \in \Psi, e \in \{0, 1\}\} \cup \{(k = 0)\})\)
7:    \(\phi' \leftarrow \mathrm{KANCSP}(\phi, Ope)\)
8:    for \((i = e) \in Ope\) do
9:    \(t \leftarrow \mathrm{KANSOLVER}([\phi'[i = e]], d - 1)\)
10:    \(\phi' := [\phi' \mid i = e \mapsto t]\)
11:    return \(\Gamma \mid \Psi \vdash \mathrm{fill}^{0 \to 1} k.[\phi' - (k = 0)] (\phi'[k = 0]) : [\phi]\)

The choices of solutions and open sides on lines 4, 6, 7 and 9 are non-deterministic, which is implemented using the list monad in the solver discussed in §6. In practice, the performance of the algorithm depends heavily on the choices we make at this point. In our implementation, we first try to solve KANCSP with \( Ope = \emptyset \). If contortions are not enough to construct all sides, it is useful to first use natural fillers which are induced by the goal boundary. In addition, it is expedient to incrementally increase the number of open sides solutions of KANCSP, e.g., using the depth-parameter \( d \).

We now devise a complete search procedure for KAN with Algorithm 3. The SOLVER starts by trying to contort some cell of the context into the goal boundary. If this fails, we perform iterative deepening on the level of nested Kan cells constructed by Algorithm 2. Again, the contortion theory is a parameter to our solver, which means that CONTORT will call the solver for Dedekind and De Morgan contortions introduced in §4, or simply look for a cartesian or disjunctive contortion by brute-force.

Algorithm 3 A solver for boundary problems

Input: \(\Gamma \mid \Psi \vdash \phi\) bdy  
Output: \(\Gamma \mid \Psi \vdash t : [\phi]\), if \(\mathrm{KAN}(\Gamma, \Psi, \phi)\) is solvable  
1: procedure SOLVER \((\Gamma, \Psi, \phi)\)  
2: for \(p \in \Gamma\) do  
3: \(t \leftarrow \mathrm{CONTORT}(\Gamma, \Psi, \phi, p)\)  
4: if \(t \neq\) Unsolvable then  
5: return \(t\)  
6: for \(d \in \{1, \ldots\}\) do  
7: \(t \leftarrow \mathrm{KANSOLVER}(\Gamma, \Psi, \phi, d)\)  
8: if \(t \neq\) Unsolvable then  
9: return \(t\)

Example 5.4 (Sq→Comp). To complete the proof of Eckmann-Hilton, we need to fill the cube from Figure 1(a) using Figure 1(b). This problem can be solved directly using Dedekind contortions, but finding the four-dimensional filler is relatively involved (but can be done using the solver presented in §6). Instead, it is easier to consider a lower-dimensional—and