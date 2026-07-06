Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:7

We have a **constraining substitution** $(r = e) \colon \Psi[r = e] \to \Psi$ that sends $r$ to $e$ if $r$ is a variable, is the unique substitution from $\perp$ when $r$ is $\overline{e}$, and the identity substitution otherwise.

For example, $(j = \mathbf{0}) \colon (i, j)[j = \mathbf{0}] \to (i, j)$ is the inclusion $(i \mapsto i, j \mapsto \mathbf{0}) \colon (i) \rightsquigarrow (i, j)$ of the face where $j = \mathbf{0}$ into the 2-cube $(i, j)$.

The *cell contexts* $(\Gamma \text{ ctx})$, *contorted boundaries* $(\Gamma \mid \Psi \parallel \Psi' \vdash_c \phi \text{ bdy})$, and *contorted cells* $(\Gamma \mid \Psi \vdash_c t \text{ cell and } \Gamma \mid \Psi \vdash_c t : [\phi])$ are mutually inductively defined as follows. The subscript $c$ on $\vdash_c$ indicate that these judgements concern contortions and we leave the contortion theory implicit as the judgements are the same for all theories. Substitutions act on each of these judgements in the usual way: given some kind of term $t$ and a substitution $\psi \colon \Psi' \to \Psi$ where $\Psi = (i_1, \ldots, i_n)$ and $\psi = (r_1, \ldots, r_n)$, we write $t[\psi]$ for the result of replacing each $i_k$ by $r_k$ in $t$. General contortions act only on some of our syntactic sorts, namely dimension terms and contorted cells (Definition 2.10); for those sorts we write $t\langle \psi \rangle$ for application of a contortion. As above, we say a context/boundary/term is **cartesian/disjunctive/Dedekind/De Morgan** when it only mentions contortion operations from that sublanguage.

**Definition 2.7.** The **cell contexts** $\Gamma \text{ ctx}$ are inductively defined by the rules

$$\overline{() \text{ ctx}} \qquad \frac{\Gamma \text{ ctx} \quad \Gamma \mid \Psi \parallel () \vdash_c \phi \text{ bdy}}{(\Gamma, a(\Psi) : [\phi]) \text{ ctx}}$$

where in the second rule, $a$ is a fresh variable name standing for a cell over dimension variables $\Psi$ and with boundary $\phi$.

That is, a cell context is a list of variables each paired with a dimension context and boundary over that context; the boundary for one variable may mention preceding variables. The list of inputs to a boundary problem, such as $a : [\ ]$, $b : [\ ]$, $p(i) : [i = \mathbf{0} \mapsto a \mid i = \mathbf{1} \mapsto b]$ from (2.1), is a cell context.

**Definition 2.8.** The **contorted boundaries** $\Gamma \mid \Psi \parallel \Psi' \vdash_c \phi \text{ bdy}$ are inductively defined by the rules

$$\overline{\Gamma \mid \Psi \parallel \Psi' \vdash_c () \text{ bdy}}$$

$$\frac{\Gamma \mid \Psi \parallel () \vdash_c \phi \text{ bdy} \quad \Psi \vdash r \text{ atom} \quad e \in \{\mathbf{0}, \mathbf{1}\} \quad \Gamma \mid \Psi[r = e], \Psi' \vdash_c t : [\phi[r = e]]}{\Gamma \mid \Psi \parallel \Psi' \vdash_c (\phi \mid r = e \mapsto t) \text{ bdy}}$$

Here $\phi[r = e]$ is the application of the constraining substitution $(r = e)$ to the boundary $\phi$.

A contorted boundary is thus a list of entries $r = e \mapsto t$, where each $t$ is a contorted cell over $\Psi[r = e]$, $\Psi'$, such that each entry agrees with the previous entries when their constraints overlap. The constraints $r = e$ can only refer to variables in $\Psi$, while the constrained terms $t$ can also refer to variables in $\Psi'$. We will only use the cases where $\Psi'$ is empty or a singleton, the latter being used in the definition of Kan cells (Definition 2.12). We write $\Gamma \mid \Psi \vdash_c \phi \text{ bdy}$ as shorthand for $\Gamma \mid \Psi \parallel () \vdash_c \phi \text{ bdy}$, and use implicitly that any $\Gamma \mid \Psi \parallel \Psi' \vdash_c \phi \text{ bdy}$ can be viewed as a $\Gamma \mid \Psi, \Psi' \vdash_c \phi \text{ bdy}$ (but not vice versa).

In (2.4), for example, we saw the contorted boundary

$$p(i) : [\ ] \mid j, k \vdash_c (j = \mathbf{0} \mapsto p(k) \mid k = \mathbf{0} \mapsto p(j) \mid j = \mathbf{1} \mapsto p(\mathbf{1}) \mid k = \mathbf{1} \mapsto p(\mathbf{1})) \text{ bdy} \tag{2.5}$$