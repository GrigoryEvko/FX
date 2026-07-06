Truncations 103

examples do not present any new difficulties as far as implementing the Kan operations is concerned. Rather, they demonstrate constructor shapes we want to be able to express in our schema.

**Propositional truncation** Recall the following specification of the propositional truncation from Chapter 4.

$A : \cup \gg \textbf{inductive} \|A\| \textbf{where}$
$\mid \text{pt}(a : A) \in \|A\|$
$\mid \text{squash}(t : \|A\|, t' : \|A\|, x : \mathbb{I}) \in \|A\| \quad [x \equiv 0 \hookrightarrow t \mid x \equiv 1 \hookrightarrow t']$

Like the suc constructor for the natural numbers, the squash constructor is recursive: it takes arguments from the type being constructed. In the case of a path constructor, we therefore also want to allow recursive arguments to occur in the boundary of a path constructor, as they do in squash.

For the eliminator, we aim to satisfy the following rule.

$$\begin{aligned} & q : \|A\| \gg D \text{ type} \quad M \in \|A\| \quad a : A \gg T_{\text{pt}} \in D[\text{pt}(a)/q] \\ & t : \|A\|, t' : \|A\|, x : \mathbb{I}, r : D[t/q], r' : D[t'/q] \gg T_{\text{squash}} \in D[\text{squash}(t, t', x)/q] \\ & t : \|A\|, t' : \|A\|, r : D[t/q], r' : D[t'/q] \gg T_{\text{squash}}[0/x] = r \in D[t/q] \\ & t : \|A\|, t' : \|A\|, r : D[t/q], r' : D[t'/q] \gg T_{\text{squash}}[1/x] = r' \in D[t/q] \\ & \hline \text{elim}(q.D; M; a.T_{\text{pt}}, a.a'.x.r.r'.T_{\text{squash}}) \in D[M/q] \end{aligned}$$

To the squash clause, we supply not only the arguments $t : \|A\|, t' : \|A\|, x : \mathbb{I}$ to the constructor, but also the results $r : D[t/q], r' : D[t'/q]$ of applying the eliminator to those terms, just as in the suc case of the natural number eliminator. In the operational semantics, these hypotheses are instantiated by recursive calls as in the following rule.

$$\begin{aligned} & N := \text{elim}(q.D; M; a.T_{\text{pt}}, a.a'.x.r.r'.T_{\text{squash}}) \\ & N' := \text{elim}(q.D; M'; a.T_{\text{pt}}, a.a'.x.r.r'.T_{\text{squash}}) \\ & \hline \text{elim}(q.D; \text{squash}(M, M', y); a.T_{\text{pt}}, a.a'.x.r.r'.T_{\text{squash}}) \\ & \longmapsto \\ & T_{\text{squash}}[M/t, M'/t', y/x, N/r, N'/r'] \end{aligned}$$

The equations in the elimination rule require the endpoints of the squash clause to agree with the two recursive calls, ensuring that the reduction rule above is sufficiently coherent.