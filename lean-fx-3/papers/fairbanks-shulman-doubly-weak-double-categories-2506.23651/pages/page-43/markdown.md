DOUBLY WEAK DOUBLE CATEGORIES

43

is a bijection, per boundary, and

- if we define a vertical (resp. horizontal) bigon to be a square whose vertical (resp. horizontal) boundaries are identities:

$$\begin{array}{ccc} A & \xrightarrow{1_A^R} & A \\ f \downarrow & \alpha & \downarrow_g \\ B & \xrightarrow{1_B^R} & B \end{array} \qquad \begin{array}{ccc} A & \xrightarrow{f} & B \\ 1_A^V \downarrow & \beta & \downarrow_{1_B^V} \\ A & \xrightarrow{g} & B \end{array}$$

then these data with the derived bigon identity, composition, and action operations

$$\begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & 1 & \downarrow_1 \\ \cdot & \xrightarrow{f} & \cdot \end{array} \qquad \begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & \alpha & \downarrow_1 \\ \cdot & -x & \cdot \\ 1 \downarrow & \beta & \downarrow_1 \\ \cdot & \xrightarrow{g} & \cdot \end{array} \mapsto \begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & \alpha & \downarrow_1 \\ \cdot & -g & \cdot \\ \cdot & \xrightarrow{g} & \cdot \end{array} \mapsto \begin{array}{ccc} \cdot & \xrightarrow{f} & \cdot \\ 1 \downarrow & \alpha & \downarrow_1 \\ \cdot & -g & \cdot \\ \cdot & \xrightarrow{g} & \cdot \end{array}$$

(and similarly in other directions) satisfy the laws of a double bicategory.

(Here one could use either of the two inverse bijections to define composition of bigons; it does not matter.)

*Proof.* The double bicategory so-defined is automatically tidy. Conversely, given any tidy double bicategory, we obtain an isomorphic one by replacing all the sets of bigons by the sets of squares to which they are in bijection by tidiness. After this replacement, the tidiness isomorphisms become identities, and all the composition operations on bigons become equal to the corresponding ones on squares; thus we have a structure as described in the statement. The two processes are evidently inverse up to isomorphism. □

This definition can be convenient when constructing examples that do not start with a given bicategory.

*Example 7.23.* As in Example 3.7, let $X$ be a topological space, let the 0-cells be points of $X$, the 1-cells be continuous paths $p : [0,1] \to X$, and the 2-cells be homotopy classes of continuous maps $[0,1] \times [0,1] \to X$ rel their boundaries. We take the composition operations on these data to be the usual ones, and the associator and unitor squares to be the usual reparametrizing homotopies. It is then straightforward to verify the axioms.

We will also see a worked example putting this definition to use in the next section.