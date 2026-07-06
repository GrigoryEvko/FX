Unfortunately the last two are not the same! This is not just about ordering the variables in a telescope; although the second and third arguments of $A^{dd}$ both lie in $A^d$ $a$, it need not be symmetrical with respect to those arguments. So again we see that without adding symmetry to the theory, it seems we can't give a general corecursor for $d\text{Coind}^d$, and hence we can't compute $\text{corec}^d$ to something more primitive.

### 3.4 EXAMPLES OF DISPLAYED COINDUCTIVE TYPES

We now continue our exploration of the theory of semi-simplicial types from section 3.2, now using the general notion of displayed coinductive type. As in section 3.2, we will use Agda-esque codata and copattern-matching definitions, and assume that our type theory has plenty of other structure.

We have already noted that SST is in some sense the 'universal' (unparametrised) displayed coinductive type, whose determining family $x : A \vdash \mathcal{B} \times \text{type}_{\ell_2}$ is the universal one $X : \text{Type}_\ell \vdash \text{El} \times \text{type}_\ell$. Moreover, it seems likely that in order for an unparametrised displayed coinductive type to be interesting, the types $A$ and $\mathcal{B}$ must have nontrivial display structure, i.e. they must not be discrete. But the simplicial universe $\text{Type}_\ell$ is the primary source of types with nontrivial display, just as the universe in homotopy type theory is a primary source of types with higher homotopy structure. (In section 5.0.0.9 we will speculate about a notion of 'display inductive type' analogous to higher inductive types, which are the other source of higher homotopy structure in homotopy type theory.) For these reasons, we do not have a lot of interesting examples of other unparametrised displayed coinductive types, but there is at least one: augmented semi-simplicial types.

#### 3.4.1 Augmented semi-simplicial types

If we simply omit the Z input of S in the definition of SST, we obtain a definition of augmented semi-simplicial types. (Recall from section 1 that these are equivalently unary semicubical types.)

codata ASST : Type where
Z+ : ASST → Type
S+ : (A : ASST) → ASSTd A

We can convince ourselves of this by extracting types of low-dimensional simplices from an X : ASST:

$$\vdash X_{-1} \equiv Z^+ X$$

$$\mathfrak{z}_i : X_{-1} \vdash X_0 \mathfrak{z}_i \equiv Z^{+d} (S^+ X)$$

$$\mathfrak{z}_i : X_{-1}, x_0 : X_0 \mathfrak{z}_i, x_0 : X_0 \mathfrak{z}_i \vdash X_1 \mathfrak{z}_i x_0 x_0 \equiv Z^{+dd} (S^{+d} (S^+ X)) \mathfrak{z}_i x_0 x_0$$

and so on. Now we can observe that the construction Fib of section 3.2.4 factors through ASST via a pair of maps, both defined by copattern-matching:

Int : (X : Type) → ASST
Z+ (Int X) = X
S+ (Int X) = Intd X

38