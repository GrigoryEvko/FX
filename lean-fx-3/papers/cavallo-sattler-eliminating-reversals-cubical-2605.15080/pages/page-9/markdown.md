E. Cavallo and C. Sattler

9

and Lumsdaine's tools for comparing type theories [22], though we could have redeveloped these with path types. The more technical reason is that we want to include (higher) inductive types in \(\mathbb{C}\Pi\). The span interpretation (§5) that we use to prove conservativity interprets inductive types as inductive families [15], and we use identity types to define these families. This is the one place where identities cannot straightforwardly be replaced with paths.

#### 3.3.1 Cofibrations

In CTT, we add new operators and equations for the sorts of COF. A cofibration can be thought of as a constraint on interval terms. Cofibration truth is a strict proposition in the sense that any two witnesses to truth of a cofibration are strictly equal:

\[
\_ \quad : \quad (P: \text { Cof }, u v: \text { True } (P)) \Rightarrow u \equiv v: \text { True } (P)
\]

As with Tm, we will leave the True operator implicit. Cofibrations are closed under finite conjunction  \( (\top, \cap) \)  and disjunction  \( (\bot, \cup) \) :

\[
\begin{array}{l} \top , \bot : \text {Cof} \quad -: (P Q: \text {Cof}, P, Q) \Rightarrow P \cap Q \\ (- \cap -): (P Q: \text {Cof}) \Rightarrow \text {Cof} \quad -: (P Q: \text {Cof}, P \cap Q) \Rightarrow P \\ (- \cup -): (P Q: \text {Cof}) \Rightarrow \text {Cof} \quad -: (P Q: \text {Cof}, P \cap Q) \Rightarrow Q \\ \_ \quad : \quad \top \quad \_ \quad : \quad (P Q: C o f, P) \Rightarrow P \cup Q \\ \_ \quad : \quad (P: \text {Cof}, \bot) \Rightarrow P \quad \_ \quad : \quad (P Q: \text {Cof}, Q) \Rightarrow P \cup Q \\ -: (P Q R: \text {Cof}, P \to R, Q \to R, P \cup Q) \Rightarrow R \\ \end{array}
\]

Eliminators for the nullary and binary disjunction \((\mathrm{elim}_{\perp}^{\mathrm{Ty}},\mathrm{elim}_{\perp}^{\mathrm{Tm}},\mathrm{elim}_{\cup}^{\mathrm{Ty}},\mathrm{elim}_{\cup}^{\mathrm{Tm}})\) allow us to define types and terms by case analysis. We abbreviate

\[
\Phi_ {\cup \mathrm{Ty}} = (P Q: \text {Cof}, A: [ P ] \rightarrow \mathrm{Ty}, B: [ Q ] \rightarrow \mathrm{Ty}, [ P \cap Q \rightarrow A \equiv B: \mathrm{Ty} ])
\]

\[
\Phi_ {\cup \mathrm{Tm}} = (P Q: \text {Cof}, A: [ P \cup Q ] \rightarrow \mathrm{Ty}, a: [ P ] \rightarrow A, b: [ Q ] \rightarrow A, [ P \cap Q \rightarrow a \equiv b: A ])
\]

and specify

\[
\begin{array}{l} \operatorname{elim} _ {\perp} ^ {\mathrm{Ty}}: [ \bot ] \Rightarrow \mathrm{Ty} \\ \operatorname{elim} _ {\perp} ^ {\mathrm{Tm}}: (A: [ \bot ] \rightarrow \mathrm{Ty}, [ \bot ]) \Rightarrow A \\ \operatorname{elim} _ {\cup} ^ {\mathrm{Ty}}: \left(\Phi_ {\cup \mathrm{Ty}}, [ \mathrm{P} \cup \mathrm{Q} ]\right) \Rightarrow \mathrm{Ty} \\ \_ \quad : \quad (\Phi_ {\cup T y}, P) \Rightarrow \operatorname{elim} _ {\cup} ^ {T y} (P, Q, A, B) \equiv A: T y \\ \_ \quad : \quad (\Phi_ {\cup T y}, Q) \Rightarrow \operatorname{elim} _ {\cup} ^ {T y} (P, Q, A, B) \equiv B: T y \\ \operatorname{elim} _ {\cup} ^ {\mathrm{Tm}}: \left(\Phi_ {\cup \mathrm{Tm}}, [ \mathrm{P} \cup \mathrm{Q} ]\right) \Rightarrow \mathrm{A} \\ \_ \quad : \quad (\Phi_ {\cup T m}, P) \Rightarrow \operatorname{elim} _ {\cup} ^ {T m} (P, Q, A, a, b) \equiv a: A \\ \_ \quad : \quad (\Phi_ {\cup T m}, Q) \Rightarrow \operatorname{elim} _ {\cup} ^ {T m} (P, Q, A, a, b) \equiv b: A \\ \end{array}
\]

The basic cofibrations are equations on interval terms, which we write with \(\approx\). The two endpoints 0 and 1 are distinct, and we can convert between \(\approx\) and strict equality \(\equiv\).

\[
\begin{array}{l} - \approx -: (i j: \mathbb {I}) \Rightarrow \text {Cof} \quad -: (i: \mathbb {I}) \Rightarrow i \approx i \\ -: (0 \approx 1) \Rightarrow \bot -: (i j: \mathbb {I}, i \approx j) \Rightarrow i \equiv j: \mathbb {I} \\ \end{array}
\]

▶ Remark 18. We could have included various algebraic laws for cofibrations, such as  \( P \cap Q \equiv Q \cap P \) , or cofibration extensionality (P : Cof, Q : Cof,  \( P \to Q \) ,  \( Q \to P \) ) →  \( P \equiv Q : Cof \) . Our proofs go through for such variations without much change.