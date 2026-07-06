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

# 1 An ordering on W-types

(1*1) Fix a U₁-container A ⊃ B in the sense of Abbott, Altenkirch, and Ghani [AAG05], i.e. a pair of a type A : U₁ together with a family of types B : A → U₁. The extension of A ⊃ B is the endofunctor [[A ⊃ B]] : U₁ → U₁ defined like so:

record [[A ⊃ B]] (X : U₁) : U₁ where
constructor (−, −)
lbl : A
sub : B(lbl) → X

The extension of a container is also known as the polynomial endofunctor associated to the corresponding morphism Σₓ:ₐB(x) → A.

(1*2) The initial algebra for the extension [[A ⊃ B]] of a given container can be computed as a W-type in the sense of Martin-Löf [Mar84] consisting of well-founded trees labeled in a : A with subtrees of arity B(a), written WₐB : U₁. The structure map for this initial algebra is written ub : [[A ⊃ B]](WₐB) → WₐB, which can be thought of as producing an upper-bound in the subtree order.
(1*3) Suppose that the container A ⊃ B is closed under binary coproducts of shapes in the sense that we have an operation + : A × A → A such that B(a₁ + a₂) ≡ B(a₁) + B(a₂). Given two trees u, v : WₐB, we will write u ⊔ v for ub(u.lbl + v.lbl, [u.sub | v.sub]). For a non-empty finite set of trees {uᵢ | i ≤ n}, we will write ⊔ᵢuᵢ for the corresponding n-ary instance of ⊔.
(1*4) We may define the following two binary relations ≤, ◁ on WₐB as the smallest ones closed under the following rules:

$$\frac{\exists b_1, \dots b_n : B(v.lbl). u \leq \bigsqcup_i v.sub(b_i)}{u < v}$$

$$\frac{\forall b : B(u.lbl). u.sub(b) < v}{u \leq v}$$

Each of (1*5) through (1*8) has been formally verified in Agda.

(1*5) The relation ≤ is reflexive.
(1*6) For any u, v, w : WₐB we have the following:

1) Transitivity. If u ≤ v ≤ w then u ≤ w; likewise if u < v < w then u < w.
2) Left flex. If u ≤ v and v < w then u < w.
3) Right flex. If u < v and v ≤ w then u < w.

(1*7) For any u, v : WₐB, if u < v then u ≤ v.

(1*8) Let {uᵢ | i ≤ n} be a non-empty finite family of trees, and let v : WₐB be a tree; we have ⊔ᵢuᵢ ≤ v if and only if uᵢ ≤ v for all i ≤ n. Moreover, we have ⊔ᵢuᵢ < v if uᵢ < v for all i ≤ n.

# 2 An intermezzo on list orderings

(2*1) Given a relation R : A × A → Ω, define the accessibility predicate as the following inductive type:

data Acc(R) : A → Ω where

acc : (a : A) → ((b : A) → R(b, a) → Acc(R, b)) → Acc(R, a)

2

A relation is said to be well-founded when all its elements are accessible. Note that a well-founded relation need not be transitive.

(2*2) We eventually wish to show that $\prec$ is well-founded but prior to this we must introduce a supplementary well-founded ordering. The well-foundedness of $\prec$ will follow from well-founded induction on this secondary ordering.

Fix a type $X$ and a well-founded relation $\prec : X \times X \to \Omega$ for the remainder of this section. We define a new relation $\sqsubset$ on $\operatorname{List}(X)$:

$$\frac{m \geq 1 \quad \exists f : \{1 \dots n\} \to \{1 \dots m\}. \forall i \leq n. x_i < y_{f(i)}}{[x_1, \dots, x_n] \sqsubset [y_1, \dots, y_m]}$$

We adapt a proof due to Wilfried Buchholz as described by Nipkow [Nip98] to prove that $\sqsubset$ is well-founded.

(2*3) The empty list is \(\sqsubset\)-accessible.
(2*4) If a list is \(\sqsubset\)-accessible, so too is any permutation.
(2*5) Fix \( y: X \). Suppose for all accessible \( l: \operatorname{List}(X) \) and \( x < y \), \( \operatorname{cons}(x, l) \) is accessible. Then for all accessible \( l: \operatorname{List}(X) \), \( \operatorname{cons}(y, l) \) is accessible.

Proof. Fix an accessible $l$ and suppose that $n \sqsubset \operatorname{cons}(y, l)$. By definition, there exists a division of $n$ into $n_l$ and $n_y$ such that $n_l \sqsubset l$ and each element of $n_y$ is dominated by $y$. Because $l$ is accessible, so too is $n_l$. Therefore, $n_y + n_l$ is accessible by induction on the size of $n_y$ and repeated use of the assumption. Because $n$ is a permutation of $n_y + n_l$, we conclude that $n$ is accessible.

(2*6) If $l : \operatorname{List}(X)$ is $\sqsubset$-accessible and $x : X$, then $\operatorname{cons}(x, l)$ is accessible.

Proof. This follows immediately from the (2*5) and $\prec$-induction on $x$.

(2*7) If $\prec$ is well-founded, so too is $\sqsubset$.

Proof. Fix $l : \operatorname{List}(X)$. We argue by induction on $l$ that $l$ is accessible. In the base case apply (2*3) and in the inductive step apply (2*6).

### 3 Well-foundedness of the directed plump ordering

(3*1) Write \(\operatorname{List}^{+}(X)\) for the type of non-empty lists. Given an non-empty list \(l = [u_0, \ldots, u_n]\), write \(\sqcup l\) for \(\sqcup_{i \leq n} u_i\).
(3*2) Given \( l: \operatorname{List}^{+}(\mathrm{W}_{A}B) \), if \( u \leq \sqcup l \) then \( u \) is \( \prec \)-accessible.

Proof. This follows by well-founded induction on the $\sqsubset$-accessibility of $l$; the details are formalized in Agda.

(3*3) The relation $\prec$ is well-founded.

Proof. We must prove that every $u : \mathrm{W}_A B$ is $\prec$-accessible, but this is a consequence of (3*2) setting $l$ to be the singleton list $[u]$; the details are formalized in Agda.

3

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