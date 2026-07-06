We are now ready to prove theorem C.11:

*Proof.* We go over all the conditions of theorem C.1. The validity of conditions 1, 3, 7 and 4 is trivial. Condition 2 is theorem C.18 together with its dual. Condition 5 is theorem C.19, and condition 6 is the dual statement.

The proof of conditions 10 is essentially the same as the proof for ordinary model categories, as for example in Chapter 15 of [Hir03] or in Chapter 5.2 of [Hov99]. The key step in the proof is that in order to construct a diagonal lift in a square:

$$\begin{array}{c} A \longrightarrow X \\ \downarrow i \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

where say $i$ is a core cofibration and $p$ is a core fibration, one of them being a (level-wise) weak equivalence. Then we proceed by induction as in the usual proof, at each step we need to produce a diagonal lift in a square of the form

$$\begin{array}{c} A(r) \sqcup_{L_r A} L_r(B) \longrightarrow X(r) \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Now, by theorem C.17 (and its dual) the object $A(r) \sqcup_{L_r A} L_r(B)$ is cofibrant and $Y(r) \times_{M_r Y} M_r X$ is fibrant. By definition of Reedy cofibration and fibration, the left vertical map is a cofibration and the right vertical is a fibration, and if one of $i$ or $p$ (say $i$) is a weak equivalence. Then the second point of theorem C.16 shows that the left vertical map is a trivial cofibration, hence the square admits a diagonal lift, which concludes the proof.

The proof of condition 8 and (dually of condition 9), also follows very closely the classical proof, as in Chapter 15 of [Hir03] or in Chapter 5.2 of [Hov99]. Given $A \rightarrow X$ a map from a Reedy cofibrant diagram to a Reedy fibrant diagram that we want to factor as a core trivial Reedy cofibration followed by a core Reedy fibration, $A \rightarrow B \rightarrow X$. We proceed by induction to construct the diagram, the object $B(r)$, and the maps $A(r) \rightarrow B(r) \rightarrow X(r)$ gradually by induction on the degree of $r$. Following the classical proof, at each stage, we need to construct a factorization of a map in $\mathcal{M}$:

$$A(r) \sqcup_{L_r A} L_r B \rightarrow X(r) \times_{M_r X} M_r B$$

as a trivial cofibration followed by a fibration. But as observed above, the domain is cofibrant and the target is fibrant, so this is indeed possible in

154