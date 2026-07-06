4

Eliminating reversals from cubical type theories

We begin studying opaque cubical type theory in §4, where we define the extension of a self-dual interval theory with a reversal and the twist interpretation from a cubical type theory extended with a reversal back to the original theory. In §5, we define the representable map category of spans and develop tools to relate pairs of interpretations between cubical type theories. We use these in §6 to prove a general theorem for deriving weak equivalences from interpretations; we apply it with the twist interpretation to deliver the conservativity of reversals over opaque cubical type theories with self-dual interval theories. In §7, we construct a model of strict cubical type theory with reversals whose homotopy theory is classically that of ∞-groupoids.

## 2 Type theories and models

### 2.1 SOGATs

We use Uemura's framework of second-order generalized algebraic theories (SOGATs) [37, Chapter 4] and their semantic counterparts, representable map categories [37, Chapter 4] [38] (also called categories with representable maps). The language of SOGATs is a logical framework (cf. Harper, Honsell, and Plotkin [18]) with which we can specify type theories themselves in type-theoretic language. In a SOGAT, we specify the judgment forms of a type theory while marking some as hypothesizable or representable. To begin with an example, basic dependent type theory MLTT [37, Example 4.6.1] is specified by two sorts, one for types and one for terms:

$$\mathsf{Ty} : () \Rightarrow \square$$

$$\mathsf{Tm} : (\mathsf{A} : () \rightarrow \mathsf{Ty}) \Rightarrow \star$$

The type sort Ty takes no parameters (() ⇒ ... ) and is non-representable (□), so hypotheses “A : Ty” cannot appear in the contexts of the type theory being specified. The term sort Tm takes one type (A : () → Ty) as a parameter and is representable (★), meaning we allow hypotheses “a : Tm(A)”.

In general, a SOGAT consists of declarations Φ ⇒ s where Φ is an environment and s is either □, ★, a previously introduced sort, or an equation between expressions such a sort. An environment is a list (A₁ : Γ₁ → e₁, ..., Aₙ : Γₙ → eₙ) of metavariables Aᵢ that take a context Γᵢ and output an eᵢ which is either a previously defined sort or an equation between expressions in such a sort. Finally, a context is a list (a₁ : A₁, ..., aₙ : Aₙ) of variables aᵢ of representable sorts Aᵢ. Everything can depend on what precedes it. We refer to Uemura [37, Chapter 4] for a much more precise description.

▶ Notation 1. We omit empty contexts (() → ...) and environments (() ⇒ ...), writing, e.g., Ty : □ and Tm : (A : Ty) ⇒ ★. We also omit variable names when what follows does not depend on them, as in Tm : Ty ⇒ ★. We surround arguments in square brackets when we intend to leave them implicit, as in the following example of Σ types. Specifically to MLTT: we leave the Tm operator implicit and write a : A rather than a : Tm(A).

▶ Notation 2 (cf. [37, Remark 5.4.6]). Any context can be treated as an environment; one level up, any environment Φ over a SOGAT T can be treated as an extension of T with new declarations. We write T[Φ] for the extended SOGAT combining T with Φ.

Uemura gives encodings of standard type formers of Martin-Löf type theory such as (negative) unit types, (negative) dependent sums, and dependent products [37, §4.6.1]. For