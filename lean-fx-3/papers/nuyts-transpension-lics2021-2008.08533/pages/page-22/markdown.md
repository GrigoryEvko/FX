16:22

A. NUYTS AND D. DEVRIESE

Vol. 20:2

Notation 5.3. We will use a slightly unconventional notation for substitutions in order to have them make maximal sense both as a substitution (as in \(\Omega[\sigma]\)) and as a function domain (as in \(\Pi\sigma\)):

- Every weakened variable (if weakening is available for the given shape) will be declared, e.g. we get a presheaf morphism \((u:\mathbb{U}):\llbracket \mathbb{X},u:\mathbb{U}\rrbracket \to \llbracket \mathbb{X}\rrbracket\) and hence \(\Omega [u:\mathbb{U}]:\mathbb{X}\to (\mathbb{X},u:\mathbb{U})\) and \(\Pi (u:\mathbb{U}):(\mathbb{X},u:\mathbb{U})\to \mathbb{X}\). Furthermore, we may omit the shape, writing just \(\Omega [u]\) and \(\Pi u\). Thus, this is what weakening and shape abstraction look like:

\[
\frac {\mathbb {X} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ u ]} ^ {\Sigma u} \vdash t : T}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {m o d} _ {\Omega [ u ]}   t : \langle \Omega [ u ] \mid T \rangle}, \qquad \frac {\mathbb {X} , u : \mathbb {U} \mid \Gamma , \widehat {\mathbf {0}} _ {\Pi   u} ^ {\Omega [ u ]} \vdash t : T}{\mathbb {X} \mid \Gamma \vdash \mathsf {m o d} _ {\Pi   u}   t : \langle \Pi   u \mid T \rangle}.
\]

The projection function (Proposition 3.3) for \(\Pi u\) is function application:

\[
\frac {\mathbb {X} , u : \mathbb {U} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ u ] \circ \Pi   u} ^ {\Omega [ u ] \circ \Sigma   u} \vdash A   \text {type}}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {a p p} _ {u} : (\Omega [ u ] \mid \langle \Pi   u \mid A \rangle) \to A \left[ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {u} : \Omega [ u ] \circ \Pi   u \Rightarrow 1} ^ {\mathsf {c o p y} _ {u} : 1 \Rightarrow \Omega [ u ] \circ \Sigma   u} \right]} \text {Proposition 3.3}
\]

The 2-cell \(\Omega[u] \circ \Sigma u \Leftarrow 1: \mathsf{copy}_u \dashv \mathsf{app}_u: \Omega[u] \circ \Pi u \Rightarrow 1\) signals a contraction of shape variables, namely of the one bound by the \(\Pi\)-modality and the one to which the function is applied.

- When a variable is substituted, we denote this as \( u := t \) instead of \( t / u \), e.g. in a cubical type theory we get a presheaf morphism \( (i := 0) : [\mathbb{X}] \to [\mathbb{X}, i : \mathbb{I}] \) and hence \( \Omega[i := 0] : (\mathbb{X}, i : \mathbb{I}) \to \mathbb{X} \) which binds \( i \) and \( \Pi(i := 0) : \mathbb{X} \to (\mathbb{X}, i : \mathbb{I}) \) which depends on \( i \), so we may substitute 0 for \( i \) but we may also abstract over the assumption that \( i \) is 0:

\[
\frac {\mathbb {X} , i : \mathbb {I} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ i : = 0 ]} ^ {\Sigma (i : = 0)} \vdash t : T}{\mathbb {X} \mid \Gamma \vdash \mathsf {m o d} _ {\Omega [ i : = 0 ]}   t : \langle \Omega [ i : = 0 ] \mid T \rangle}, \qquad \frac {\mathbb {X} \mid \Gamma , \widehat {\mathbf {0}} _ {\Pi (i : = 0)} ^ {\Omega [ i : = 0 ]} \vdash t : T}{\mathbb {X} , i : \mathbb {I} \mid \Gamma \vdash \mathsf {m o d} _ {\Pi (i : = 0)}   t : \langle \Pi (i : = 0) \mid T \rangle}.
\]

And apply:

\[
\frac {\mathbb {X} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ i : = 0 ] \circ \Pi (i : = 0)} ^ {\Omega [ i : = 0 ] \circ \Sigma (i : = 0)} \vdash A   \text {type}}{\mathbb {X} \mid \Gamma \vdash \mathsf {a p p} _ {i : = 0} : (\Omega [ i : = 0 ] \mid \langle \Pi (i : = 0) \mid A \rangle) \to A \left[ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {i : = 0} : \Omega [ i : = 0 ] \circ \Pi (i : = 0) \Rightarrow 1} ^ {\mathsf {c o p y} _ {i : = 0} : 1 \Rightarrow \Omega [ i : = 0 ] \circ \Sigma (i : = 0)} \right]} \text {prop. 3.3}
\]

- Finally, if \(\sigma\) involves weakening, then the codomain of the co-unit may be a variable renaming that is sugar for the identity, e.g.

\[
\mathsf {a p p} _ {(u / v: \mathbb {U})}: \Omega [ u: \mathbb {U} ] \circ \Pi (v: \mathbb {U}) \Rightarrow \Omega [ u: \mathbb {U}, v := u ]
\]

is exactly the same thing as

\[
\mathsf {a p p} _ {(u: \mathbb {U})}: \Omega [ u: \mathbb {U} ] \circ \Pi (u: \mathbb {U}) \Rightarrow 1.
\]

This way, we may adjust \(\mathsf{app}_{(u:\mathbb{U})}\) in order to be able to apply to a different variable:

\[
\frac {\mathbb {X} , v : \mathbb {U} \mid \Gamma , \widehat {\mathbf {0}} _ {\Omega [ u ] \circ \Pi   v} ^ {\Omega [ v ] \circ \Sigma   u} \vdash A   \text {type}}{\mathbb {X} , u : \mathbb {U} \mid \Gamma \vdash \mathsf {a p p} _ {u / v} : (\Omega [ u ] \mid \langle \Pi   v \mid A \rangle) \to \left\langle \Omega [ u , v : = u ] \mid A \left[ \widehat {\mathbf {a}} _ {\mathsf {a p p} _ {u / v}: \Omega [ u ] \circ \Pi   u \Rightarrow \Omega [ u , v : = u ]} ^ {\mathsf {c o p y} _ {v / u}: \Omega [ v , u : = v ] \Rightarrow \Omega [ u ] \circ \Sigma   u} \right] \right\rangle}
\]

Again, bear in mind that shape substitutions are in fact defined as presheaf morphisms and that therefore, notions such as weakening and contraction reflected by the syntax introduced here, need to be shallowly interpreted in presheaf morphisms.