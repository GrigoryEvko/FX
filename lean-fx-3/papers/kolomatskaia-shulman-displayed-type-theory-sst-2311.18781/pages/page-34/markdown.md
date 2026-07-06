Sing : Top → SST
Z (Sing X) = pt X
S (Sing X) x = Sing^d X (paths X x)

#### 3.2.4 Fibers and higher spans

As we will see in section 4, semantically each type at mode sm is already an augmented semi-simplicial type. We expect that if we fix a particular  \( (-1) \) -simplex in an augmented semi-simplicial type, we should obtain an (unaugmented) semi-simplicial type as its 'fibre'. And indeed, we can define this operation:

Fib : (X :  \( \triangle\square \)  Type) ( \( \mathfrak{z} \)  : X) → SST
Z (Fib X  \( \mathfrak{z} \) ) = X \( ^{d} \)   \( \mathfrak{z} \) 
S (Fib X  \( \mathfrak{z} \) ) x = Fib \( ^{d} \)  X  \( \mathfrak{z} \)  x

Note that X is required to be modal so that we can take display of it. Then we have, for instance, if  \( z_{0}: X \)  and  \( x_{0}, x_{0}: X^{d} z_{0} \) ,

\[
\begin{array}{l} (\text { Fib } X _ {\mathfrak {z} _ {0}}) _ {0} \equiv Z (\text { Fib } X _ {\mathfrak {z} _ {0}}) \\ \equiv X ^ {d} \mathfrak {z} _ {0} \\ \left(\operatorname{Fib} X _ {\mathfrak {z} _ {0}}\right) _ {1} x _ {0} x _ {0} \equiv Z ^ {d} \left(S \left(\operatorname{Fib} X _ {\mathfrak {z} _ {0}}\right) x _ {0}\right) x _ {0} \\ \equiv Z ^ {d} \left(\operatorname{Fib} ^ {d} X _ {\mathfrak {z} _ {0}} x _ {0}\right) x _ {0} \\ \equiv X ^ {d d} \mathfrak {z} _ {0} x _ {0} x _ {0} \\ \end{array}
\]

and as a last example

\[
\begin{array}{l} \left(\text { Fib } X _ {\mathfrak {z} _ {0}}\right) _ {2} x _ {0 1} x _ {0 1} \beta_ {0 1} x _ {0 0} \beta_ {0 1} \beta_ {0 1} \equiv Z ^ {d d} \left(S ^ {d} \left(S \left(\text { Fib } X _ {\mathfrak {z} _ {0}}\right) x _ {0 1}\right) x _ {0 1} \beta_ {0 1}\right) x _ {0 0} \beta_ {0 1} \beta_ {0 1} \\ \equiv Z ^ {d d} \left(S ^ {d} \left(\operatorname{Fib} ^ {d} X _ {\mathfrak {z} _ {0 0}} x _ {0 1}\right) x _ {0 0} \beta_ {0 1}\right) x _ {0 0} \beta_ {0 1} \beta_ {0 1} \\ \equiv Z ^ {d d} \left(\operatorname{Fib} ^ {d d} X _ {\mathfrak {z} _ {0 0}} x _ {0 1} x _ {0 0} \beta_ {0 1}\right) x _ {0 0} \beta_ {0 1} \beta_ {0 1} \\ \equiv \operatorname{Fib} ^ {d d} X _ {\mathfrak {z} _ {0 0}} x _ {0 1} x _ {0 0} \beta_ {0 1} x _ {0 0} \beta_ {0 1} \beta_ {0 1}. \\ \end{array}
\]

In particular, if we let \( X = \text{Type}_\ell \) be a universe and \( \mathfrak{z} = \top \) be a unit type, we have

\[
\begin{array}{l} (\text { Fib   Type } _ {\ell} \top) _ {0} \equiv \text { Type } _ {\ell} ^ {d} \top \\ \equiv \top \rightarrow \text { Type } _ {\ell} \\ \cong \text { Type } _ {\ell} \\ \end{array}
\]

\[
\left(\text { Fib   Type } _ {\ell} \top\right) _ {1} X _ {0} X _ {0} \equiv \text { Type } _ {\ell} ^ {\mathrm{dd}} \top X _ {0} X _ {0}
\]

\[
\cong X _ {0} \rightarrow X _ {0} \rightarrow \text { Type } _ {\ell}
\]

\[
\left(\text { Fib   Type } _ {\ell} \top\right) _ {2} X _ {0 1} X _ {0 0} B _ {0 1} X _ {0 0} B _ {0 1} B _ {0 1} \equiv \text { Type } _ {\ell} ^ {\text { ddd }} \top X _ {0 1} X _ {0 0} B _ {0 1} X _ {0 0} B _ {0 1} B _ {0 1}
\]

\[
\cong \left(\mathrm{x} _ {0 1}: \mathrm{X} _ {0 1}\right) \left(\mathrm{x} _ {0 2}: \mathrm{X} _ {0 2}\right) \left(\beta_ {0 1}: \mathrm{B} _ {0 1} \mathrm{x} _ {0 1} \mathrm{x} _ {0 2}\right)
\]

\[
\left(\mathrm{x} _ {0 0}: \mathrm{X} _ {0 0}\right)\left(\beta_ {0 1}: \mathrm{B} _ {0 1} \mathrm{x} _ {0 1} \mathrm{x} _ {0 2}\right)\left(\beta_ {0 2}: \mathrm{B} _ {0 2} \mathrm{x} _ {0 2} \mathrm{x} _ {0 3}\right)\rightarrow \text {Type} _ {\ell}
\]

Thus \(\text{Fib Type}_\ell \top\) is the semi-simplicial type of types, spans, and a sort of simplicial 'higher spans' that could also be called 'heterogeneous simplices'. More generally, \(\text{Fib Type}_\ell A\) for any type \(A\) consists of types, spans, and simplicial higher spans indexed by \(A\).

34