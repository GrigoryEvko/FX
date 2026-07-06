164

Introduction

**Reynolds' parametricity** Parametricity, introduced in the seminal work of Reynolds [Rey83], is a property that constrains the behavior of *polymorphic functions*, functions that depend on type variables. Strachey [Str67] distinguishes two varieties of polymorphism: *parametric* and *ad-hoc*. As retold by Reynolds, a parametrically polymorphic function is intuitively one whose behavior is uniform in its type variables, which "does the same thing" no matter how those variables are instantiated, such as the following commutator for the sum/coproduct type.

$$\lambda A. \lambda B. \lambda c. \left[ \begin{array}{l} \text { case } c \text { of } \\ | \operatorname{inl}(a) \mapsto \operatorname{inr}(a) \\ | \operatorname{inr}(b) \mapsto \operatorname{inr}(b) \end{array} \right] \in (A, B: U) \rightarrow A + B \rightarrow B + A$$

An ad-hoc polymorphic function, on the other hand, is one whose behavior *does* depend on how its type variables are instantiated, such as the following bizarre function that behaves differently when its type argument is Int.

$$\lambda A. \lambda a. \left[ \begin{array}{l} \text { case } A \text { of } \\ | \operatorname{Int} \mapsto 2 \\ | \_ \mapsto a \end{array} \right] \in (A: U) \rightarrow A \rightarrow A$$

In this telling, the property of being parametric is a syntactic condition: a function is parametric when its definition does not use any case analysis on its type variables. Reynolds' realization was that this syntactic condition implies a powerful semantic property: the existence of an *action on relations*.

Reynolds' original results apply to a formal simple type theory with type variables: the theory with non-dependent functions ($A \rightarrow B$), non-dependent products ($A \times B$), and booleans (Bool). Terms are built from function definition and application, pairing and projections, boolean constructors tt and ff, and boolean case analysis. (Reynolds also allows for some additional fixed collection of type and term constants.) Note that no facility for case analysis on types is provided. This type theory has a canonical interpretation in set theory: given an assignment $E = \{X_1 \mapsto S_1, \ldots, X_n \mapsto S_n\}$ of sets to each type variable in a type $A$, we have an induced set $[[A]]_E$, with function types translated into sets of set-theoretic functions and so on. Likewise, any term $t: A$ has an interpretation as an element $[[t]]_E \in [[A]]_E$. Reynolds' semantic definition of parametric polymorphism is given in terms of this interpretation.

To understand Reynolds' result, let us focus our attention on the simplest case: the type of functions $X \rightarrow X$ polymorphic in the type variable $X$. Given an interpretation $X \mapsto S$, the interpretation of this type is naturally the set of functions $S \rightarrow S$.

**Definition.** A family of set-theoretic functions ($f_S \in S \rightarrow S \mid S \in Set$) is *parametric* when it preserves all binary relations: for every pair of sets $S, T \in Set$ and binary relation $R \subseteq S \times T$, if $(s, t) \in R$, then $(f_S(s), f_T(t)) \in R$.