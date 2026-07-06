(3*4) Summarizing, given a pair $$(A : \cup_1, B : A \to \cup_1)$$ together with an operation an operation $$\dot{+} : A \times A \to A$$ such that $$B(a_1 \dot{+} a_2) = B(a_1) + B(a_2)$$ there exists a type $$W_A B$$ together with a pair of relations $$\leq, \prec : W_A B \times W_A B \to \Omega$$ satisfying the following conditions:

1) $$\leq$$ is transitive and reflexive.
2) $$\prec$$ is transitive and well-founded.
3) If $$u \prec v$$, then $$u \leq v$$.
4) If $$u \prec v \leq w$$ or $$u \leq v \prec w$$ then $$u \prec w$$
5) If there exists $$a : A$$ such that $$B(a) = \mathbf{0}$$ then $$(W_A B, \leq)$$ has a least element.
6) For any $$a : A$$, both $$\leq$$ and $$\prec$$ have upper-bounds for all $$B(a)$$-families.
7) Given $$u, v$$ there exists an element $$u \sqcup v$$ such that $$u \sqcup v \leq w$$ if and only if $$u, v \leq w$$.
8) If $$u, v \prec w$$ then $$u \sqcup v \prec w$$.

(3*5) Given a pair $$(A : \cup_1, B : A \to \cup_1)$$, define a new pair $$(C, D)$$ by setting $$C = \text{List}(A)$$ and specifying $$D$$ inductively:

$$D([]) = \mathbf{0} \qquad D(\text{cons}(a, c)) = B(a) + D(c)$$

Then (3*4) instantiated with this new family shows that $$(W_C D, \leq, \prec)$$ satisfies the requirements outlined by (0*1).

## References

[Mar84] Per Martin-Löf. Intuitionistic type theory. Notes by Giovanni Sambin. Vol. 1. Studies in Proof Theory. Bibliopolis, 1984, pp. iv+91. ISBN: 88-7088-105-9 (cit. on p. 2).

[Tay96] Paul Taylor. “Intuitionistic sets and ordinals”. In: The Journal of Symbolic Logic 61.3 (1996), pp. 705–744. DOI: 10.2307/2275781 (cit. on p. 1).

[Nip98] Tobias Nipkow. An Inductive Proof of the Wellfoundedness of the Multiset Order. Exposition of a proof due to Wilfried Buchholz. 1998. URL: https://www21.in.tum.de/~nipkow/Misc/multiset.ps (cit. on p. 3).

[AAG05] Michael Abbott, Thorsten Altenkirch, and Neil Ghani. “Containers: Constructing strictly positive types”. In: Theoretical Computer Science 342.1 (2005). Applied Semantics: Selected Topics, pp. 3–27. ISSN: 0304-3975. DOI: 10.1016/j.tcs.2005.06.002 (cit. on p. 2).

[FPS21] Marcelo P. Fiore, Andrew M. Pitts, and S. C. Steenkamp. Quotients, inductive types, and quotient inductive types. 2021. arXiv: 2101.02994 [cs.LO] (cit. on p. 1).

[SG22] Jonathan Sterling and Daniel Gratzer. agda-directed-plump-ordering. https://github.com/jonsterling/agda-directed-plump-ordering. 2022 (cit. on p. 1).

4