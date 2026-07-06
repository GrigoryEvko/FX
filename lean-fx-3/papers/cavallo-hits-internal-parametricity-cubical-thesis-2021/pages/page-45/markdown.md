A logic of programs 33

# **Rule 2.1.35 (Function reduction).**

$$\frac{a : A \gg N \in B \quad \Vdash M \in A}{\Vdash (\lambda a . N) M = N[M/a] \in B[M/a]}$$

*Proof.* By instantiating $a : A \gg N \in B$, we have $\Vdash N[M/a] \in B[M/a]$. Thus $B[M/a] \Downarrow V$ and $N[M/a] \Downarrow W$ with $\tau_i \vDash V \downarrow R$ (for some $R$) and $W \in R$. As $(\lambda a . N) M \longmapsto N[M/a]$, we also have $(\lambda a . N) M \Downarrow V$, and thus $\Vdash (\lambda a . N) M = N[M/a] \in B[M/a]$. $\square$

The proof of function reduction is an instance of a general principle called *head expansion*: if $M \longmapsto^* N$ and $N = N' \in A$, then $M = N' \in A$.

Finally, we can show that any element of a function type is equal to some $\lambda$-abstraction. A rule of this kind, characterizing all elements of a type as equal to some introduction form, is often called an $\eta$-rule.

# **Rule 2.1.36 (Function uniqueness).**

$$\frac{\Vdash A \text{ type} \quad a : A \gg B \text{ type} \quad \Vdash F \in (a : A) \to B}{\Vdash F = \lambda a . F a \in (a : A) \to B}$$

*Proof.* By $\Vdash F \in (a : A) \to B$, we have that $F \Downarrow \lambda a . N$ with $a : A \gg N \in B$. By head expansion, it follows that $\Vdash F = \lambda a . N \in (a : A) \to B$. By weakening and function elimination (for open terms), we thus have $a : A \gg F a = (\lambda a . N) a \in B$. Function reduction then gives $a : A \gg (\lambda a . N) a = N \in B$, so by transitivity $a : A \gg F a = N \in B$. Applying function introduction and symmetry, we get $\Vdash \lambda a . N = \lambda a . F a \in (a : A) \to B$. A second application of head expansion with $F \longmapsto^* \lambda a . N$ gives the result. $\square$

# **2.1.5.2 Products**

The elements of the product type $(a : A) \times B$ are pairs $\langle M, N \rangle$ where $M$ is in $A$ and $N$ is in $B[M/a]$; given an element of the product type, we can project its first component with the first operator or its second component with the second operator. The proofs of the rules for function types are readily adapted to check the corresponding rules for product types, so we merely list the results here and leave the proofs as an exercise for the reader.