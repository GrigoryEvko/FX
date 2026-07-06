could be used to encode many, if not all, other infinitely coherent structures. In indexed style, a semi-simplicial type consists of type families $A_0$, $A_1$, $A_2$, and so on, having types that start out as follows:

$A_0$: Type

$A_1: (x_0: A_0) (x_0: A_0) \rightarrow \text{Type}$

$A_2: (x_{01}: A_0) (x_{01}: A_0) (\beta_{01}: A_1 x_{01} x_{01}) (x_{01}: A_0) (\beta_{01}: A_1 x_{01} x_{01}) (\beta_{01}: A_1 x_{01} x_{01}) \rightarrow \text{Type}$

$A_3: (x_{001}: A_0) (x_{001}: A_0) (\beta_{001}: A_1 x_{001} x_{001}) (x_{001}: A_0) (\beta_{001}: A_1 x_{001} x_{001}) (\beta_{001}: A_1 x_{001} x_{001})$

$(f_{011}: A_2 x_{001} x_{011} \beta_{011} x_{011} \beta_{011} \beta_{011})$ $(x_{100}: A_0) (\beta_{100}: A_1 x_{001} x_{100})$ $(\beta_{100}: A_1 x_{001} x_{100})$

$(f_{111}: A_2 x_{001} x_{011} \beta_{011} x_{011} \beta_{011} \beta_{011})$ $(\beta_{110}: A_1 x_{010} x_{010})$ $(f_{110}: A_2 x_{001} x_{010} \beta_{010} x_{010} \beta_{010} \beta_{010})$

$(f_{110}: A_2 x_{010} x_{010} \beta_{010} x_{010} \beta_{010} \beta_{010}) \rightarrow \text{Type}$

First, we have a type $A_0$ of points. Second, we have for every two points $x_0, x_0: A_0$, a type $A_1 x_0 x_0$ of lines joining $x_0$ and $x_0$. Third, for every three points $x_{01}, x_{01}, x_{00}: A_0$ and three lines $\beta_{01}: A_0 x_{01} x_{01}$, $\beta_{01}: A_0 x_{01} x_{00}$, and $\beta_{01}: A_0 x_{01} x_{00}$, a type $A_1 x_{01} x_{00} \beta_{01} x_{01} \beta_{01} \beta_{01}$ of triangles with the given boundary. The pattern continues with tetrahedra, which we may also, more technically, call 3-simplices. In general, $A_n$ describes the type of n-simplices indexed by their boundaries.

**Remark 1.1.** The binary subscripts on variables above follow a scheme that we learned from Tim Campion, although related schemas have been rediscovered many times. The $2^{n+1} - 1$ simplices constituting an n-simplex and its boundary are labeled by the numbers from 1 to $2^{n+1} - 1$ written in binary, where the number of 1s in a binary number corresponds to the dimension of the simplex, and the binary numbers corresponding to the boundary of some simplex are obtained by replacing one or more of the 1s in its binary number by 0s. (As we will see later, the binary number 0 can also be regarded as denoting the unique (-1)-simplex in the boundary of an n-simplex in an augmented semi-simplicial set.)

We then list these simplices in the order given by these numbers. This ordering may seem somewhat curious, compared to the more naïve approach of listing all the 0-simplices, then all the 1-simplices, and so on; but it does retain the important property that all the simplices in the boundary of some simplex are listed before it (thus, for instance, it makes the semi-simplex category into an 'ordered direct category'; see section 4.5.5). We will see later that this ordering is what arises most naturally in (co)inductive constructions of semi-simplicial sets (which was also Campion's motivation).

In addition to subscripting simplex variables by binary numbers according to this scheme, in this paper we will use different base letters to indicate the dimension of each variable. Thus for instance $x_{01}$, $x_{01}$, and $x_{00}$ are all 0-simplices, while $\beta_{01}$, $\beta_{01}$, and $\beta_{00}$ are all 1-simplices, and $f_{01}$ is a 2-simplex. We will not have much occasion to denote 3-simplices; for (-1)-simplices we use the Cyrillic letter ʒ (ze). We may also use different letters from the same alphabets for simplices in different semi-simplicial types, e.g. $\gamma_0: B_1 y_0 y_0$ and $\delta_0: C_1 z_0 z_0$.

One may think of the terms $A_0$, $A_1$, $A_2$, and so on as defining the fields of an infinite record type. Terms of this infinite record type SST are known as semi-simplicial types. Thus, the problem is to define a type of semi-simplicial types within homotopy type theory, continuing the above pattern. As a correctness criterion, one would expect that when interpreted in any $(\infty, 1)$-topos the type SST becomes a classifier of semi-simplicial objects. However,

3