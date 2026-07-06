1:18

M. SHULMAN

Vol. 19:2

LNL multicategories of Kleisli type correspond to syntaxes for intuitionistic linear logic that have only one class of type, such as [Bar96, Has05], rather than two syntactic classes for “linear types” and “nonlinear types”.

Example 3.10. We conjecture that the Linear Non-Linear multicategories suggested by [HT21] are equivalent to LNL multicategories of Kleisli type. In addition, the IL-indexed categories of [MdPR00] are equivalent to LNL multicategories of Kleisli type having ⊗, 1, &, ⊤, →, and → (our → being written “→”).

We can also attempt to induce an LNL multicategory from a monad on a cartesian monoidal category or multicategory. In fact this is quite easy: the 2-category of symmetric multicategories has Eilenberg–Moore objects, so any monad T therein on a multicategory E induces an adjunction of multicategories  \( E \rightleftharpoons E^{T} \) . If E is cartesian, by Proposition 3.1 this yields an LNL multicategory with F, U. The interesting thing is that if E is representable, hence a (cartesian) monoidal category, then a symmetric-multicategory-monad on it is the same as a lax symmetric monoidal monad, and hence by [Koc72] the same as a commutative strong monad.

Proposition 3.11. Any commutative strong monad T on a cartesian monoidal category E induces an LNL multicategory P having F, U, ×, 1, 1, where  \( P^{NL} = E \)  and the  \( P^{L} \)  is the symmetric multicategory of T-algebras. Moreover:

(i) If \(\mathcal{E}\) is cartesian closed with equalizers, then \(\mathcal{P}\) has \(\rightarrow\), \(\rightharpoonup\).
(ii) If \(\mathcal{E}\) and \(T\) are such that the category of \(T\)-algebras has coequalizers (e.g. \(\mathcal{E}\) is locally presentable and \(T\) is accessible, or \(\mathcal{E}\) is cartesian closed with reflexive coequalizers preserved by \(T\)) then \(\mathcal{P}\) also has \(\otimes\), and thus is an LNL adjunction.

Proof. We have already observed the first statement, except for noting that  \( 1 = T1 \) . Statements (i) and (ii) follow by results in the literature [Koc71, Sea13]. ☐

Of course, we can also restrict to any full sub-multicategory of the Eilenberg–Moore category, such as the Kleisli category, and still have an LNL multicategory. As in the comonad case, when given a commutative strong monad on a cartesian monoidal category we generally regard it as an LNL multicategory via the Kleisli construction; thus we have the following locally full sub-2-categories of LNLPoly:

- Cartesian monoidal categories with a commutative strong monad.
- Cartesian monoidal categories with a commutative strong monad and any desired limits and any desired colimits preserved by the product in each variable.
- Cartesian closed categories with a commutative strong monad and any desired limits and colimits.

A non-commutative monad T on a cartesian monoidal category E does not induce a multicategory structure on its Eilenberg–Moore category  \( E^{T} \) . However, as long as T is a strong monad, we can still combine E with  \( E^{T} \)  to produce an LNL multicategory, albeit a rather degenerate one. Specifically, if A and B are T-algebras and X is an object of E, we can define an X-indexed family of algebra maps  \( A \to B \)  to be a morphism  \( f : X \times A \to B \)  such that the following diagram commutes:

\[
\begin{array}{c} X \times T A \longrightarrow T (X \times A) \xrightarrow {T f} T B \\ \Big \downarrow \\ X \times A \xrightarrow [ f ]{} B \end{array}
\]