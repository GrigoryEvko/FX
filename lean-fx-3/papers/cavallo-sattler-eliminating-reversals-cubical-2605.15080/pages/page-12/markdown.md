12

Eliminating reversals from cubical type theories

For elimination, we fix the environment

\[
\begin{array}{r c l} \Phi_ {\text {elim}} & = & ([ A: T y ], C: (t: S u s p (A)) \to T y, \\ & & n: C (\text {north}), s: C (\text {south}), m: (a: A) \to \text {Path} (\langle i \rangle C (\text {merid} (a) @ i), n, s)) \end{array}
\]

and specify

\[
\begin{array}{l} \text { elim } \quad : \quad (\Phi_ {\text { elim }}, t: \text { Susp } (A)) \Rightarrow C (t) \\ - \quad : \quad (\Phi_ {\text {elim}}) \Rightarrow \operatorname{elim} (C, n, s, m, \text {north}) \equiv n: C (\text {north}) \\ - \quad : \quad (\Phi_ {\text {elim}}) \Rightarrow \operatorname{elim} (C, n, s, m, \text {south}) \equiv s: C (\text {south}) \\ \text { merid } \beta : (\Phi_ {\text { elim }}, a: A) \Rightarrow \lambda i. \text { elim } (C, n, s, m, \text { merid } (a) @ i) \sim m \\ \end{array}
\]

This is an “opaque” suspension type in that merid \( \beta \) constructor is a path rather than a strict equality. This is how HITs are usually formulated in Book HoTT [39, §6.2], strict computation rules being characteristic of cubical type theory.

### 3.4 Strict cubical type theory

Strict cubical type theories—i.e., cubical type theories as they are usually defined—are designed to satisfy strict canonicity [19, 3], the property that every closed term of type N is strictly equal to a numeral. This requires two adjustments to our opaque cubical type theory, which we sketch here. A full description of the specific strict theory we model in §7 can be found in Angiuli et al. [2]. We write  \( C_{TT_{s}} \)  for the extension of the SOGAT CTT with the symbols and equations indicated below, following Angiuli et al.'s specification.

First, we add equations for each concrete type former for evaluating applications of the filling operator at that type. For  \( \Sigma \)  types, for example, we have an equation reducing  \( \text{fill}(\langle i\rangle\Sigma a:A(i).B(i,a),P,s,j,s_{0},k) \)  to a pair of two calls to the filling operator, one over A and one over an instance of B. For higher inductive types such as Susp, some applications of the filling operator are treated as values (i.e., not reduced), and equations are instead introduced for reducing the eliminator at these values [2, §2.15].

Second, we strictify the path  \( merid\beta \) , replacing it with a strict equation or, to express strict cubical type theory as an extension of opaque cubical type theory, introducing the strict equation and equating  \( merid\beta \)  with the reflexive path.

## 4 The twist interpretation

To prove conservativity of opaque cubical type theories with reversals over the corresponding theories without reversals, we first construct interpretations from the former to the latter. In §§5–6 we show that the existence of these interpretations abstractly implies conservativity. As sketched in §1.1, we exploit twist constructions: the fact that the “square” environment  \( \mathbb{I} \times \mathbb{I} = (\mathbf{i}_{0} : \mathbb{I}, \mathbf{i}_{1} : \mathbb{I}) \in \mathbb{C}\mathbb{T}\mathbb{T} \)  is an interval object with a reversal and inherits certain algebraic structure from I. Thus, we call our translation the twist interpretation.

### 4.1 Extension by a reversal

We have an interpretation Flip of INT in itself by taking  \( \text{Flip}(\mathbb{I}) := \mathbb{I} \) ,  \( \text{Flip}(0) := 1 \) , and  \( \text{Flip}(1) := 0 \) . By the (2, 1)-categorical universal property of  \( \mathbb{CL}(\mathbb{INT}) \)  [37, Theorem 4.8.18], this determines (up to isomorphism) an RMC functor  \( \text{Flip} \colon \mathbb{INT} \to \mathbb{INT} \)  with an isomorphism  \( \theta \colon \text{Flip} \circ \text{Flip} \cong \text{Id} \)  satisfying  \( \theta \circ \text{Flip} = \text{Flip} \circ \theta \)  and  \( \theta_{I} = id \) .

▶ Definition 23. A self-dual interval theory  \( (\Phi,\phi) \)  is an interval theory  \( \Phi \)  equipped with an isomorphism  \( \phi\colon\operatorname{Flip}(\Phi)\cong\Phi \)  such that  \( \operatorname{Flip}(\phi)\circ\phi=\theta_{\Phi}:\operatorname{Flip}(\operatorname{Flip}(\Phi))\cong\Phi \) .