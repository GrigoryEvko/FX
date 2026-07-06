154 Conclusions

providing a convenient interface for elimination akin to the case analysis pseudo-code we employ in this thesis.

**Quotient inductive types** Although we have focused on the combination of higher inductive types with univalence and higher-dimensional equality more generally, higher inductive types are also useful in “zero-dimensional” settings. Higher inductive types truncated at the set level have become known as *quotient inductive types* (QITs) [ACDKN18].

Of particular interest are quotient *inductive-inductive* types (QIITs), which permit the simultaneous definition of several inductive types in which one inductive type may appear as an index to another. A schema for QIITs can serve as a *logical framework*, a schema for defining logics. The syntax of ITT, for example, is higher inductive-inductive type, a collection of interdependent inductively generated judgments ($\Gamma \text{ ctx}, \Gamma \vdash A \text{ type}$) together with their equality judgments (e.g., $\Gamma \vdash A = A' \text{ type}$). This application is explored by Altenkirch and Kaposi [AK16; Kap17]. Dijkstra [Dij17], Altenkirch et al. [ACDKN18], and Kovács and Kaposi [KK20b] define theories and semantics of quotient inductive-inductive types.

Some quotient inductive types can be realized by taking an ordinary inductive type and applying a simple (truncated) quotient in the sense of Section 5.1. In cases with recursive constructors, however, the correctness of this construction may rely on the axiom of choice (AC). Primitive quotient inductive types may therefore be used to avoid relying on AC. This is exploited by Altenkirch, Danielsson, and Kraus to define a partiality monad [ADK17]. Fiore, Pitts, and Steenkamp observe, however, that a combination of (ordinary) inductive-inductive types, quotient types, and size types is sufficient to obtain many quotient inductive types [FPS20].

On the subject of choice, Lumsdaine and Shulman describe a higher inductive type that can be interpreted in Zermelo-Fraenkel set theory with but not without choice [LS20, §9]. As written, this type is not an instance of our schema; it uses definitions by natural number recursion into the type being specified in the boundary of a path constructor, as in the following example.

**inductive Ex where**

$$\begin{aligned} &\text{ | } a \in \text{Ex} \\ &\text{ | } b(t : \text{Ex}) \in \text{Ex} \\ &\text{ | } c(n : \text{Nat}, x : \mathbb{I}) \in \text{Ex} \quad [x \equiv 0 \hookrightarrow a \mid x \equiv 1 \hookrightarrow \text{elim}_{\text{Nat}}(\dots \text{Ex}; n; a, \dots t.b(t))] \end{aligned}$$

However, this kind of specification can be encoded by taking a function matching the recursive definition as an argument as follows, where $T_{\text{zero}} := \text{Path}(\text{Ex}, f \text{ zero}, a)$ and $T_{\text{suc}} := (n : \text{Nat}) \to \text{Path}(\text{Ex}, f (\text{suc}(n)), b(f n))$.