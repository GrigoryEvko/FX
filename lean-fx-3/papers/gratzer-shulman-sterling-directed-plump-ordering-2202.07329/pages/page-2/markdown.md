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