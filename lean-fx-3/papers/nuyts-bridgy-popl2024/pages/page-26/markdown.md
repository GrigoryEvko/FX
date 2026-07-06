8:26

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

definitionally adjusted on a fragment of the type they live in. More precisely, suppose the ambient context \(\Gamma\) contains a number of path variables \(\Phi = j, k, \ldots\) and suppose \(\Gamma \vdash \chi : 1\). Intuitively, the term \(\Gamma \vdash \mathsf{hcomp}\{B : \mathsf{Type}\} \{\chi : 1\} v(v_0 : B)\) is \(v_0 : B\) but definitionally adjusted (using the \(v\) argument, not explained here) on the fragment of \(\Gamma \vdash B\) where \(\chi(j, k, \ldots) = i1\) (since \(v_0, B, \chi\) live in context \(\Gamma\) they can depend on variables in \(\Phi\)). In cubical type theory, constraints like \(\chi(j, k, \ldots) = i1\) are called face constraints or alternatively cofibrations and can be regarded as subsets of a cube \(\chi \subseteq \Phi\). The language used to express face constraints is called a face or cofibration logic. The cofibration logic used by Agda --cubical is De Morgan algebra and assertions in this logic are encoded as terms \(\chi : 1\). If \(\Gamma \vdash j, k, l : 1\), an example of face constraint is \(\chi = ((\neg j) \vee k) \wedge l\).

In our case we would like, in a context extended with  \( (x : \text{BI}) \) , to definitionally adjust the term transp  \( (i. A i x) \varphi(u_0 x) \)  of type A i1 x when x = bi0 and x = bi1 (and in fact when  \( \varphi = i1 \) ). The problem of course is that x is a bridge variable, and that hcomp only allows constraints  \( \varphi : I \)  on path variables. The mixed homogeneous composition mhcomp primitive of Agda --bridges generalizes hcomp w.r.t. bridge variables and can be used in place of hcomp to specify the result of transporting along a line of bridges.

### 5.2 Mixed Homogeneous Composition

The mhcomp primitive of Agda --bridges has a type different than that of hcomp.

\[
\operatorname{mhcomp}: \forall \{A: \text { Type } \} \{\zeta : \text { MCstr } \} (u: (i: 1) \rightarrow \text { MPartial } \zeta A) (u _ {0}: A) \rightarrow A
\]

This time \( u_0 \) and its type \( A \) can have free path variables \( \Phi = (j, k, \ldots) \) but also free bridge variables \( \Psi = (x, y, \ldots) \) and \( u_0 \) ought to be definitionally adjusted on a subset \( \zeta \) of the mixed cube \( \Phi \times \Psi \). For this reason mhcomp expects face constraints \( \zeta \) expressed in an extended cofibration logic called MCstr. Concretely, the latter is a type postulated by Agda --bridges and equipped with primitives for combining atomic mixed face constraints. Instead of precisely explaining these primitives we provide a formula MCstr(\( \Phi, \Psi \)) expressing what mixed constraints \( \zeta \) can be built in a context containing \( \Phi \) and \( \Psi \) as above. First, define \( I(\Phi) = \{\varphi | \Phi \vdash \varphi : I\} \). Second, define the set of bridge hyperfaces of \( \Psi \) as \( H(\Psi) = \Psi \times \{bi0, bi1\} \). We define BCstr(\( \Psi \)) = \( \left\{ \bigvee_{(x, bi\epsilon) \in H'} (x = bi\epsilon) | H' \subseteq H \right\} \cup \{\top\} \), i.e., bridge face constraints obtainable in \( \Psi \) are disjunctions of bridge hyperfaces (this includes an empty disjunction \( \bot \)), or a vacuous constraint denoted \( \top \). Finally we set

\[
\operatorname{MCstr} (\Phi , \Psi) = \frac {\operatorname{I} (\Phi) \times \operatorname{Bcstr} (\Psi)}{\forall \varphi \psi . (\mathrm{i} 1 , \psi) = (\varphi , \top) = : \top_ {\mathrm{MCstr}}}
\]

The quotient is taken to turn the map \(\varphi \mapsto (\varphi, \bot)\) into an embedding of logics: a --cubical constraint \(\varphi : 1\) holds if and only if its image \((\varphi, \bot) : \mathsf{MCstr}\) is a mixed constraint that holds. This condition is required to ensure that a term typechecks in Agda --cubical if and only if it typechecks in Agda --bridges. An example of mixed constrained \(\zeta : \mathsf{MCstr}\) is \(\zeta := (\varphi, (x = \mathsf{bi0}) \vee (x = \mathsf{bi1}))\) which appears when transporting bridges, as hinted above.

\[
\operatorname{transp} (i. \operatorname{BridgeP} _ {x, A i x} (a _ {0} i) (a _ {1} i)) \varphi u _ {0} \mapsto
\]

\[
\lambda (x: \mathrm{BI}). \operatorname{mhcomp} \left\{A \mathrm{i} 1 x \right\} \left\{\left(\varphi , (x = \mathrm{bi} 0) \vee (x = \mathrm{bi} 1)\right) \right\} (\dots) (\operatorname{transp} (i. A i x) \varphi (u _ {0} x))
\]

Similar to transp, the operational semantics of mhcomp is defined by induction on the syntax of its A : Type argument. Concretely, Agda --bridges duplicates the hcomp equations for Glue, hcomp, PathP,  \( \Sigma \) ,  \( \Pi \) , record and (non-indexed, non-HIT) data types, but propagating a mixed constraint  \( \zeta \)  this time. Additionally, it implements reductions at BridgeP and Gel types. The latter clause uses capturing. Following --cubical, if A is a HIT, an inhabitant mhcomp  \( \{A\}\{\zeta\} \)   \( u_{0}:A \)  is considered normal and functions defined by pattern matching on A compute on it if  \( \zeta=(\varphi,\bot) \)  for some  \( \varphi \) .

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.