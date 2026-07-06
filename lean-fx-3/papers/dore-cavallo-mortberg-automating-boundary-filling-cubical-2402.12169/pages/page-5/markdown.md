Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:5

This variant assumes a path $p$ without naming its endpoints and seeks a path from $p(\mathbf{1})$ to $p(\mathbf{0})$. The format extends gracefully to higher cells; for example, the diagonal of a square can be requested by posing

$$s(i, j) : [ ] \mid k \vdash ? : [ k = \mathbf{0} \mapsto s(\mathbf{0}, \mathbf{0}) \mid k = \mathbf{1} \mapsto s(\mathbf{1}, \mathbf{1}) ] \tag{2.3}$$

Here we assume a 2-dimensional cell $s$ with unspecified boundary and seek a path from $s(\mathbf{0}, \mathbf{0})$ to $s(\mathbf{1}, \mathbf{1})$. In the remaining section, we introduce two ways to produce solutions to boundary problems: contortions and Kan filling.

2.1. Contorting cubes. Intuitively, the problem (2.3) has a simple solution: $? := s(k, k)$. That is, we take the hypothesised 2-cube $s$ and apply a reparameterisation $k \mapsto (k, k)$. We call such reparameterisations contortions. Different cubical type theories offer different kinds of contortions. The only contortions of cartesian cubical type theory of Angiuli et al. [AFH18, ABC$^+$21] are variables and the constants $\mathbf{0}, \mathbf{1}$, whereas the theory of Cohen et al. (CCHM) [CCHM18] includes binary operators $\vee$ and $\wedge$, conventionally called connections [BH81], as well as a unary involution operator $\sim$. We think of $\vee$ as taking the maximum of two parameters and $\wedge$ as taking the minimum, whereas $\sim$ is thought of as negation sending $i \in [\mathbf{0}, \mathbf{1}]$ to $\mathbf{1} - i$. For example, given a cell context containing a path $p$, the operator $\vee$ can be used to define a square whose value at coordinate $(j, k)$ is the value of $p$ at the maximum of $j$ and $k$:

$$p(i) : [ ] \mid j, k \vdash p(j \vee k) : \left[ \begin{array}{l l} j = \mathbf{0} \mapsto p(k) & k = \mathbf{0} \mapsto p(j) \\ j = \mathbf{1} \mapsto p(\mathbf{1}) & k = \mathbf{1} \mapsto p(\mathbf{1}) \end{array} \right] \tag{2.4}$$

We will study both the cartesian and CCHM theories in the following, as well as two theories which lie in between the two in terms of expressiveness. If we remove the involution operation of CCHM, leaving $\vee$ and $\wedge$, we have a distributive lattice which we call the Dedekind contortion theory. Removing moreover one of the connections yields the disjunctive contortion theory, which is used by Cavallo and Sattler [CS25]. Choosing a more expressive contortion theory naturally means more problems can be solved by contortion. For example, the path inversion problem (2.2) above is immediately solved with an involution:

$$p(i) : [ ] \mid j \vdash p(\sim i) : [ j = \mathbf{0} \mapsto p(\mathbf{1}) \mid j = \mathbf{1} \mapsto p(\mathbf{0}) ]$$

Without an involution, this problem instead requires Kan filling (which will be introduced in §2.2). On the other hand, adding more contortions makes contortion solving more complex.$^4$ There is hence a trade-off for which class of contortions are allowed for proof search.

We now formally introduce the language of boundary problems, starting with the fragment needed to formulate solutions by contortion.

Definition 2.1. A dimension context $\Psi$ is either a list of (unique) dimension variables $(i_1, \ldots, i_n)$ or the inconsistent context $\bot$.

We think of a dimension context with $n$ variables as a topological unit $n$-cube, each axis being labelled with one variable, while $\bot$ is the empty space; note that the “empty” context () is the unit 0-cube, which does have a unique point. We write $\Psi, i$ for the extension of $\Psi$ by a fresh variable $i$, which is $(i_1, \ldots, i_n, i)$ when $\Psi = (i_1, \ldots, i_n)$ and $\bot$ when $\Psi = \bot$.

$^4$It is also unclear whether cubical type theories with more complex contortion theories admit semantics in standard homotopy types; see discussion in [CS25, ACC$^+$26].