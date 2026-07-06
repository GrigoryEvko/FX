2.4. GLOBULAR EQUIVALENCES

#### 2.4.2 A criterion to be a weak equivalence

2.4.2.1. A morphism  \( p: C \to D \)  between complicial sets is a D-equivalence if

\[
\pi_ {0} (C) \to \pi_ {0} (D)
\]

is an equivalence of categories, and for any n > 0 and pair of parallel arrow s, t, the induced functor

\[
\pi_ {n} (s, t, C) \rightarrow \pi_ {n} (p s, p t, D)
\]

is an equivalence of categories.

A D-trivial fibration is a fibration having the right lifting property against  \( \partial D_{n} \rightarrow D_{n} \)  and  \( \mathbf{D}_{n} \rightarrow (\mathbf{D}_{n})_{t} \) .

Lemma 2.4.2.2. Let \(\alpha \in \{-, +\}\). The morphism \(i_{n+1}^{\alpha}: \mathbf{D}_n \to (\mathbf{D}_{n+1})_t\) is an acyclic cofibration.

Proof. We have a pushout diagram

\[
\begin{array}{c} \mathbf {D} _ {n} \times \{\alpha \} \cup \partial \mathbf {D} _ {n} \times [ 1 ] _ {t} \xrightarrow {i d \cup \partial \times s ^ {0}} \mathbf {D} _ {n} \times \{\alpha \} \\ \Biggl \downarrow \\ \mathbf {D} _ {n} \times [ 1 ] _ {t} \xrightarrow {} (\mathbf {D} _ {n}) _ {t} \end{array}
\]

The left hand morphism being an acyclic cofibration, this concludes the proof.

Lemma 2.4.2.3. Acyclic cofibrations between complicial sets are D-equivalences.

Proof. Let \( i: A \to B \) be an acyclic cofibration. The morphism \( i \) admits a retraction \( r: B \to A \):

\[
\begin{array}{c} A \xrightarrow {i d} A \\ i \Big \downarrow \quad \nearrow \\ B. \end{array}
\]

and a homotopy  \( \psi \)  between  \( id_{B} \)  and ir which is constant on the image of i, obtained as the lift in the following diagram:

\[
\begin{array}{c} B \times \{0 \} \coprod_ {A \times \{0 \}} A \times [ 1 ] _ {t} \longrightarrow B \\ \Big \downarrow \\ B \times [ 1 ] _ {t} \end{array}
\]

Let \( n > 0 \) be an integer, and \( s, t \) be two \( (n - 1) \)-cells of \( C \). The retraction implies that \( i_{!} \) is an injection on morphisms. For any \( n \)-cell \( y: i(s) \to i(t) \) in \( B \), the homotopy \( \psi \) induces

97