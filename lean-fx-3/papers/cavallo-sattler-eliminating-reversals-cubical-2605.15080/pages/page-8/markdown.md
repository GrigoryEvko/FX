8

Eliminating reversals from cubical type theories

A morphism \( G \colon (\mathbb{S}, F) \to (\mathbb{S}', F') \) in the coslice (2,1)-category \( \mathbb{R} / \mathbf{RMC} \) induces a morphism \( \mathbf{0}_G \colon \mathbf{0}_F \to \mathbf{0}_{F'} \) of models of \( \mathbb{R} \). A special case of the above construction is its application to the identity \( \operatorname{Id} \colon \mathbb{R} \to \mathbb{R} \): the model \( \mathbf{0}_{\mathbb{R}} \in \mathbf{Mod}(\mathbb{R}) \) is a bi-initial object in \( \mathbf{Mod}(\mathbb{R}) \), the initial model of \( \mathbb{R} \) [37, §5.4.1].

## 3 Cubical type theories

### 3.1 The interval

Before defining cubical type theory, we first introduce a simple SOGAT specifying the interval alone. This will let us easily speak about cubical type theories with different interval theories.

▶ Definition 14. The SOGAT INT of an interval has one representable sort with two points:

\[
\mathbb {I}: () \Rightarrow \star \quad 0, 1: () \Rightarrow \mathbb {I}
\]

▶ Definition 15. An interval theory is an environment \(\Phi \in \mathbb{INT}\).

Per §2.1, a context in \(\mathbb{INT}\) is simply a list \((\mathbf{i}_1:\mathbb{I},\ldots ,\mathbf{i}_n:\mathbb{I})\). An environment \(\Phi\) consists of declarations of the form \(\mathbf{r}:\Gamma \to \mathbb{I}\) and \(\_ :\Gamma \to r_1\equiv r_2:\mathbb{I}\). In other words, \(\Phi\) specifies a single-sorted algebraic theory extending the theory of two points 0, 1.

▶ Example 16. The cartesian interval theory  \( \Phi_{cart} \)  is the trivial environment  \( 1 := () \in \mathbb{INT} \) . The distributive lattice interval theory  \( \Phi_{DL} \)  is the environment beginning with

\[
\begin{array}{l l}(- \wedge -), (- \vee -)&: (\mathbf {i}: \mathbb {I}, \mathbf {j}: \mathbb {I}) \to \mathbb {I}\\_ {-}&: (\mathbf {i j k}: \mathbb {I}) \to \mathbf {i} \wedge (\mathbf {j} \vee \mathbf {k}) \equiv (\mathbf {i} \wedge \mathbf {j}) \vee (\mathbf {i} \wedge \mathbf {k}): \mathbb {I}\end{array}
\]

and continuing with the other equations of a bounded distributive lattice, as enumerated for example by Buchholtz and Morehouse [8, Table 1]: associativity and commutativity of \(\wedge\) and \(\vee\), unit laws \(\mathbf{i} \wedge \mathbf{l} \equiv \mathbf{i}\) and \(\mathbf{i} \vee \mathbf{0} \equiv \mathbf{i}\), and absorption laws \(\mathbf{i} \wedge (\mathbf{i} \vee \mathbf{j}) \equiv \mathbf{i}\) and \(\mathbf{i} \vee (\mathbf{i} \wedge \mathbf{j}) \equiv \mathbf{i}\).

### 3.2 Cofibrations

In addition to Ty, Tm, and I, cubical type theory has a sort of cofibrations and, over the sort of cofibrations, a representable sort for cofibration truth:

\[
\text { Cof } \quad : \quad \square \quad \text { True } \quad : \quad (\mathrm{P}: \mathrm{Cof}) \Rightarrow \star
\]

We write \(\mathbb{C}\mathrm{OF}\) for the SOGAT consisting of these two sorts. In fact we have \(\mathbb{C}\mathrm{OF} \cong \mathbb{M}\mathrm{LTT}\), but it will be useful to have distinct notation for this sub-SOGAT of our cubical type theories.

### 3.3 Opaque cubical type theory

We define opaque cubical type theory, \(\mathbb{C}\mathrm{TT}\), as a mutual extension of the SOGATs of Martin-Löf type theory with \(\Sigma\), \(\Pi\), and identity types (\(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{M},\Pi}\)), an interval (\(\mathbb{INT}\)), and a cofibration classifier (\(\mathbb{COF}\)). We roughly follow Uemura's encodings of cubical type theory [37, §4.6.3] [38, Example 5.14]. We introduce the declarations of \(\mathbb{C}\mathrm{TT}\) (beyond those of \(\mathbb{M}\mathrm{LTT}_{\Sigma,\mathrm{M},\Pi}\), \(\mathbb{INT}\), and \(\mathbb{COF}\)) in stages over the course of this section (§3.3).

▶ Remark 17. Given that path types serve as equality types in cubical type theories, it may seem strange that we include Martin-Löf's identity types in CTT, though their coexistence is semantically justified [12, §9.1] [9, §3.3] [2, §2.16]. We do so partly in order to reuse Kapulkin