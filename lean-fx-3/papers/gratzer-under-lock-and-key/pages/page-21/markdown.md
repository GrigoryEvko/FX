VAR

\[
\frac {\mu : n \to m \qquad \alpha : \mu \Rightarrow \mathsf {l o c k s} (\Delta)}{\Gamma , x : (\mu \mid A) , \Delta \vdash x ^ {\alpha} : A @ n}
\]

PAIR

\[
\frac {\Gamma \vdash M : A @ m \qquad \Gamma \vdash N : B @ m}{\Gamma \vdash (M , N) : A \times B @ m}
\]

PROJ

\[
\frac {\Gamma \vdash P : A _ {1} \times A _ {2} @ m}{\Gamma \vdash \pi_ {i} (P) : A _ {i} @ m}
\]

LAM

\[
\frac {\Gamma , x : (\mu \mid A) \vdash M : B @ m}{\Gamma \vdash \lambda x : (\mu \mid A) . M : (\mu \mid A) \to B @ m}
\]

APP

\[
\frac {\mu : n \to m \qquad \Gamma \vdash M : (\mu \mid A) \to B @ m \qquad \Gamma , \widehat {\mathbf {m}} _ {\mu} \vdash N : A @ n}{\Gamma \vdash M (N) _ {\mu} : B @ m}
\]

INJ

\[
\frac {\Gamma \vdash M : A _ {i} @ m}{\Gamma \vdash \mathsf {i n} _ {i} (M) : A _ {1} + A _ {2} @ m}
\]

CASE

\[
\frac {\Gamma \vdash M : A + B @ m \qquad \Gamma , x : (1 \mid A) \vdash P : C @ m \qquad \Gamma , y : (1 \mid B) \vdash Q : C @ m}{\Gamma \vdash \mathsf {c a s e} (M ; x _ {A} . P ; y _ {B} . Q) : C @ m}
\]

MOD

\[
\frac {\mu : n \to m \qquad \Gamma , \widehat {\mathbf {m}} _ {\mu} \vdash M : A @ n}{\Gamma \vdash \operatorname{mod} _ {\mu} (M) : \langle \mu \mid A \rangle @ m}
\]

LET

\[
\frac {\nu : o \to n \qquad \mu : n \to m \qquad \Gamma , \widehat {\mathbf {m}} _ {\mu} \vdash M : \langle \nu \mid A \rangle @ n \qquad \Gamma , x : (\mu \circ \nu \mid A) \vdash N : B @ m}{\Gamma \vdash \operatorname{let} _ {\mu} \operatorname{mod} _ {\nu} (x _ {A}) \leftarrow M \text {in} N : B @ m}
\]

Figure 2: Terms of Multimodal Logic

\[
\operatorname{locks} (\Gamma , x: (\mu \mid A)) \stackrel {{\text { def }}} {{=}} \operatorname{locks} (\Gamma)
\]

\[
\operatorname{locks} (\Gamma , \widehat {\mathbf {m}} _ {\mu}) \stackrel {{\text { def }}} {{=}} \operatorname{locks} (\Gamma) \circ \mu
\]

This operation clearly preserves Eqs. (1) and (2), and is hence well-defined on contexts. One can show by induction on pre-contexts that this operation is a homomorphism with respect to concatenation, i.e. that

\[
\operatorname{locks} (\Gamma , \Delta) = \operatorname{locks} (\Gamma) \circ \operatorname{locks} (\Delta)
\]

when both sides are defined. \( ^{2} \)

The term assignment system for multimodal logic is given in Fig. 2. The basic judgement is of the form \(\Gamma \vdash M: A @ m\), which means that \(M\) is a term of type \(A\) under

\( ^{2} \) Recall that concatenation is in general not an admissible rule of the judgment  \( \Gamma \)  ctx @ m, as locks may interfere with the mode  \( m \in M \) .

21