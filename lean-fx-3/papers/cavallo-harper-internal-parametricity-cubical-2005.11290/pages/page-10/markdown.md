5:10

E. CAVALLO AND R. HARPER

Vol. 17:4

1.2. Path-types. Path-types simply internalize dependence on an interval variable, much as function types internalize dependence on a term variable. When we have a type $x : \mathbb{I} \gg A$ type depending on an interval variable $x$ and elements $M_0 \in A[0/x]$ and $M_1 \in A[1/x]$ inhabiting its endpoints, we can form the type $\mathsf{Path}_{x.A}(M_0, M_1)$ of paths from $M_0$ to $M_1$ over $x.A$. Recall that the univalence axiom, which we will validate in due time, identifies paths between types with isomorphisms. With that intuition in mind, we think of an element of $\mathsf{Path}_{x.A}(M_0, M_1)$ as a proof that $M_0$ corresponds to $M_1$ along the isomorphism between $A[0/x]$ and $A[1/x]$ represented by $x.A$. In the special case that $A$ does not depend on $x$, an element of $\mathsf{Path}_{\_A}(M_0, M_1)$ is simply an identification between $M_0$ and $M_1$ in $A$. (In that case, we generally write $\mathsf{Path}_A(M_0, M_1)$ rather than $\mathsf{Path}_{\_A}(M_0, M_1)$.)

Rules for Path-types are displayed in Figure 1. Like functions, we introduce paths by abstraction: if $x : \mathbb{I} \gg M \in A$, then $\lambda^{\mathbb{I}}x.M$ is a path from $M[0/x]$ to $M[1/x]$. Conversely, if we have a path $P \in \mathsf{Path}_{x.A}(M_0, M_1)$, we can apply it to any interval term $r$ to get an element $P@r \in A[r/x]$. (Moreover, we have $P@0 = M_0$ and $P@1 = M_1$.) Abstraction and application interact via the usual $\beta$- and $\eta$-rules for function types.

Although many theorems rely on the Kan operations introduced in the next section, we can observe some basic facts about paths already. First, we have reflexive paths given by interval variable weakening.

$$\frac{M \in A}{\lambda^{\mathbb{I}}x.M \in \mathsf{Path}_A(M, M)}$$

Second, functions act on paths. Note that we also use weakening here when we apply $F$ in a context extended with $x : \mathbb{I}$.

$$\frac{F \in (a:A) \to B \qquad P \in \mathsf{Path}_A(M_0, M_1)}{\lambda^{\mathbb{I}}x.F(P@x) \in \mathsf{Path}_{x.B[P@x/a]}(FM_0, FM_1)}$$

Finally, we have function extensionality: functions are path-equal when they are point-wise path-equal. Although function extensionality is a (non-trivial) consequence of univalence [Uni13, §4.9], cubically it follows more directly from exchange of term and interval variables.

$$\frac{F_0, F_1 \in (a:A) \to B \qquad H \in (a:A) \to \mathsf{Path}_B(F_0a, F_1a)}{\lambda^{\mathbb{I}}x.\lambda a.Ha@x \in \mathsf{Path}_{(a:A)\to B}(F_0, F_1)}$$

It is easy to see that this function is an isomorphism—its inverse simply exchanges the arguments in the opposite order.

The preceding argument can more generally characterize $\mathsf{Path}_{x.(a:A)\to B}(F_0, F_1)$ when $B$ depends on $x$, but not when $A$ does: if $A$ depends on $x$, then the type “$(a:A) \to \mathsf{Path}_{x.B}(F_0a, F_1a)$” is nonsensical. In the most general case, we can instead construct a map taking paths between functions to functions from paths to paths: “equal functions take equal arguments to equal results.”

Lemma 1.1. Let $x : \mathbb{I} \gg A$ type, $x : \mathbb{I}, a : A \gg B$ type, $F_0 \in ((a:A) \to B)[0/x]$, and $F_1 \in ((a:A) \to B)[1/x]$ be given. Then we have the following principle.

$$\frac{Q \in \mathsf{Path}_{x.(a:A)\to B}(F_0, F_1)}{\mathsf{funapp}(Q) \in (a_0:A[0/x])(a_1:A[1/x])(p:\mathsf{Path}_{x.A}(a_0, a_1)) \to \mathsf{Path}_{x.B[p@x/a]}(F_0a_0, F_1a_1)}$$

Proof. $\mathsf{funapp}(Q) := \lambda a_0.\lambda a_1.\lambda p.\lambda^{\mathbb{I}}x.(Q@x)(p@x)$.

□