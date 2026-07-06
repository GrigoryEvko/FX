28:22

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

Algorithm 1 Constructing a Dedekind contortion

Input: \(\Gamma \mid \Psi \vdash_{\mathrm{c}} \phi\) bdy and \(a(\Psi') : [\phi'] \in \Gamma\). Let \(m := |\Psi|\) and \(n := |\Psi'|\).

Output: \(\psi: \Psi \rightsquigarrow \Psi'\) s.t. \(\Gamma \mid \Psi \vdash_{\mathrm{c}} a(\psi) : [\phi]\) if such a \(\psi\) exists, Unsolvable otherwise

1: procedure DEDEKINDCONTORT(\(\Gamma, \Psi, \phi, a\))
2:    \(\Sigma := \{x \mapsto \mathbf{I}^n \mid x \in \mathbf{I}^m\}\)
3:    for \((i = e \mapsto b(\psi)) \in \phi\) with \(\psi: \Psi[i = e] \rightsquigarrow \Psi''\), in descending order of \(|\Psi''|\) do
4:    if \(a = b\) then
5:    \(\Theta := \{x \mapsto \{\psi_{\mathbf{I}}(x)\} \mid x \in \mathbf{I}_{i=e}^m\}\)
6:    else
7:    \(\Theta := \{x \mapsto \emptyset \mid x \in \mathbf{I}_{i=e}^m\}\)
8:    for \(\sigma \in \text{UNFOLDPPM}(\Sigma|_{\mathbf{I}_{i=e}^m})\) do
9:    if \(a(\sigma_{\vee\wedge}) = b(\psi)\) then
10:    for \(x \in \mathbf{I}_{i=e}^m\) do
11:    \(\Theta(x) := \Theta(x) \cup \{\sigma(x)\}\)
12:    for \(x \in \mathbf{I}_{i=e}^m\) do
13:    UPDATEPPM(\(\Sigma, x, \Theta(x)\))
14:    if \(\exists \sigma \in \text{UNFOLDPPM}(\Sigma)\) such that \(\Gamma \mid \Psi \vdash_{\mathrm{c}} a(\sigma_{\vee\wedge}) : [\phi]\) then
15:    return \(\sigma_{\vee\wedge}\)
16:    else
17:    return Unsolvable

The main computational effort in Algorithm 1 consists unfolding all poset maps from a subposet on line 8. For an unconstrained PPM, we have to check \( D(m - 1)^n \) poset maps, and as we are doing this for up to \( 2m \) faces of \( \phi \), we are unfolding \( 2m \cdot D(m - 1)^n \) poset maps in the worst case. In many boundary problems, the cell to be contorted appears in the boundary, which means the search space significantly shrinks before any PPM is unfolded. This allows us to compute many contortions that would have been impossible to find by naive brute-force.

Example 4.2 (Square to cube contortion). Suppose that we are given the cell context \(\Gamma := a : [ ], s(i,j) : [i = 0 \mapsto a \mid i = 1 \mapsto a \mid j = 0 \mapsto a \mid j = 1 \mapsto a]\) and want to contort the square \(s\) to match the following 3-cube boundary, which has a contortion of \(s\) on one face and squares which are constantly \(a\) otherwise:

\[
\Gamma \mid i, j, k \vdash_ {\mathrm{c}} \mathbf {?} \colon \left[ \begin{array}{c c c} i = \mathbf {0} \mapsto s (j \wedge k, j \vee k) & j = \mathbf {0} \mapsto a & k = \mathbf {0} \mapsto a \\ i = \mathbf {1} \mapsto a & j = \mathbf {1} \mapsto a & k = \mathbf {1} \mapsto a \end{array} \right]
\]

This is a difficult instance of DEDEKIND because most faces of the goal are contortions of a 0-cell, which can be obtained in many ways. To construct \(\psi: (i,j,k) \rightsquigarrow (i,j)\) such that \(s(\psi)\) has boundary \(\phi\), we search for the equivalent poset map \(\mathbf{I}^3 \to \mathbf{I}^2\) using 1.

On line 2, the total PPM \(\Sigma : \mathbf{I}^3 \to \mathcal{P}(\mathbf{I}^2)\) is initialised with \(x \mapsto \mathbf{I}^2\) for all \(x \in \mathbf{I}^3\). We then go through all faces of the goal boundary and use them to restrict \(\Sigma\), starting with the contortion of \(s\) at \(i = 0\). Since \(s\) is also the cell that we are contorting, the subposet \(\mathbf{I}_{i=0}^3\) of the domain of \(\Sigma\) is mapped in a unique way to the elements of \(\mathbf{I}^2\). The monotonicity restrictions on PPMs further restrict \(\Sigma\), which only contains 10 poset maps after this first restriction. In the next iteration of the outer loop, we only have degenerate \(a\) faces left in the goal boundary. Going through each face further restricts \(\Sigma\), as most induced poset maps give rise to a contortion of \(s\) which is not the constant \(a\) square. Afterwards, \(\Sigma\) comprises a