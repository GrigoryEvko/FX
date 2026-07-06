Formalisms 43

We leave off congruence rules—if $A = A'$ type and $B = B'$ type then $A \rightarrow B = A' \rightarrow B'$ type and so on—as these can be mechanically inferred.

To give equations for the calculation of substitutions in function types, we first observe that context extension has a functorial action on substitutions: given $\Gamma' \vdash \gamma : \Gamma$ and a type $\Gamma \vdash A$ type, we have $\Gamma'.A[\gamma] \vdash \gamma^\times : \Gamma.A$ defined by $\gamma^\times := (\gamma \circ p).v$. Using this, we can propagate substitutions beneath binders as follows.

$$
\begin{aligned}
(A \rightarrow B)[\gamma] &= A[\gamma] \rightarrow B[\gamma^\times] \\
(\lambda(M))[\gamma] &= \lambda(M[\gamma^\times]) \\
(FM)[\gamma] &= F[\gamma] M[\gamma]
\end{aligned}
$$

Remember, this is not a definition of substitution by clauses; this is a specification of equations that an interpretation of substitution should satisfy. Of course, if we do not provide sufficient equations, the formalism will be poorly behaved, but this does not mean the formalism is incompletely defined, only unsatisfactory.

We leave the formulation of rules for the other types to the reader; one may simply mimic the suite of rules developed in Section 2.1.

**Interpretation in computational type theories** Once we have laid out a formalism, we can ask whether a given computational type theory is an instance of the interface it presents.

To start with, we need an interpretation $|-|$ of formal contexts, substitutions, types, and terms as untyped syntax (or operations, in the case of substitutions).$^{1}$ Given this, there is a canonical candidate interpretation for a formalism with the judgments given above in the kind of computational type theory we have described: we interpret $\Gamma \vdash A$ type as $|\Gamma| \gg |A|$ type, $\Gamma \vdash M : A$ as $|\Gamma| \gg |M| \in |A|$, and so on. The interpretation is sound if the interpretation of every rule in the formalism is a true principle in the interpretation. We will not go through the work of proving such a theorem here, but the process is fairly straightforward: we have already done the bulk of the work by proving rules for each of the type formers in Section 2.1.

**Adequacy** One key property we can ask of a formalism for a computational interpretation is *computational adequacy*, the property that the reductions of the interpretation’s operational semantics are tracked by the equational theory of the formalism.

**Proposition 2.2.1 (Adequacy).** If $\cdot \vdash M : A$ and $|M| \longmapsto |N|$, then $\cdot \vdash M = N : A$.

$^{1}$As we are translating from a nameless to named representation of variables, this function should really be parameterized by a variable environment.