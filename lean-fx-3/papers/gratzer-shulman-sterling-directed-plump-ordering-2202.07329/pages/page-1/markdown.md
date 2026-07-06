arXiv:2202.07329v2 [cs.LO] 17 Mar 2022

# The directed plump ordering

Daniel Gratzer

Michael Shulman

Jonathan Sterling

March 21, 2022

## Abstract

Based on Taylor's hereditarily directed plump ordinals, we define the *directed plump ordering* on W-types in Martin-Löf type theory. This ordering is similar to the plump ordering but comes equipped with non-empty finite joins in addition to the usual properties of the plump ordering.

**(0*0)** *Acknowledgment.* This research was supported by the United States Air Force Office of Scientific Research under award number FA9550-21-1-0009.

**(0*1)** The theory of plump ordinals [Tay96] has been adapted to Martin-Löf type theory by Fiore, Pitts, and Steenkamp [FPS21] to produce directed well-founded orders suitable for certain transfinite constructions. Given a pair $(A : \cup_1, B : A \to \cup_1)$, *op. cit.* defines the *plump ordering*: a pair of relations $\leq, \prec$ on a type $W$ of well-founded trees satisfying the following conditions:

1) $\leq$ is reflexive and transitive
2) $\prec$ is transitive and well-founded.
3) If $u \prec v$ then $u \leq v$.
4) If $u \prec v \leq w$ or $u \leq v \prec w$ then $u \prec w$.
5) $(W, \leq)$ has a least element.
6) For each $a : A$, both $\leq$ and $\prec$ have upper-bounds for all $B(a)$-families.

Following Taylor's theory of hereditarily directed plump ordinals [Tay96], we refine this ordering to obtain well-behaved least upper-bounds:

7) Given $u, v : W$ there exists $u \sqcup v$ such that $u \sqcup v \leq w$ if and only if $u, v \leq w$.
8) If $u, v \prec w$ then $u \sqcup v \prec w$.

**(0*2)** We have partially formalized our results in Martin-Löf type theory with the UIP principle in the Agda proof assistant [SG22].$^1$ In particular, all results except the well-foundedness of the list ordering $\sqsubseteq$ of Section 2 are formalized in Agda.

$^1$http://www.jonmsterling.com/agda-directed-plump-ordering/.

1