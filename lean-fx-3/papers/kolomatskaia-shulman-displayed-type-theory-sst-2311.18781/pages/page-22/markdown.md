2.4.5.3 Universes As with \(\Pi\)-types, this rule represents the traditional behavior of parametricity and logical relations on universes: a computability witness for a type is a relation on that type.

\[
\left(\left(\text { Type } _ {\ell}\right)\right) _ {v: \Upsilon^ {d}} \equiv \left(\left(\text { El   A } \rightarrow \text { Type } _ {\ell}\right)\right) _ {v ^ {+}: \Upsilon^ {0}, A: \text { Type } _ {\ell}}
\]

\[
\llbracket \text {Code} A \rrbracket_ {v: \Upsilon^ {d}} \equiv \llbracket \lambda a. \text {Code} \left(\llbracket A \rrbracket_ {v: \Upsilon^ {d}} v ^ {+} a\right) \rrbracket_ {v ^ {+}: \Upsilon^ {0}}
\]

\[
\left(\left(\text {El} A\right)\right) _ {v: \Upsilon^ {d}} \equiv \left(\left(\text {El} \left(\llbracket A \rrbracket_ {v: \Upsilon^ {d}} v ^ {+} a\right)\right)\right) _ {v ^ {+}: \Upsilon^ {0}, a: \text {El} A}
\]

### 2.5 TELESCOPES AND META-ABSTRACTIONS, II

The rules given so far essentially suffice to characterise the basic theory of dTT. However, in order to formulate our definition of semi-simplicial types, we need a bit more structure. To this end, in this section we introduce some more operations on telescopes that can be 'defined' in terms of those already given.

#### 2.5.1 Meta-abstracted telescopes

We start with another judgement form \(\Gamma \vdash_{\mathfrak{p}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon}\) for a telescope dependent on a telescope, with rules entirely analogous to those for types and terms in section 2.3.3.

\[
\frac {\Gamma \mid (v : \Upsilon) \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}}}{\Gamma \vdash_ {p} ((\Phi)) _ {v : \Upsilon} \operatorname{tel} _ {\ell_ {1} / v : \Upsilon}} \quad \frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1} / v : \Upsilon} \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} \Phi \sigma \operatorname{tel} _ {\ell_ {1}}}
\]

\[
\frac {\Gamma \mid (v : \Upsilon) \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} ((\Phi)) _ {v : \Upsilon} \sigma \equiv \Phi [ 1 _ {\Gamma} | \sigma ]}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma \vdash_ {p} \Psi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma | (v : \Upsilon) \vdash_ {p} \Phi v \equiv \Psi v}{\Gamma \vdash_ {p} \Phi \equiv \Psi}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma | (v : \Upsilon) \vdash_ {p} t : \Phi v}{\Gamma \vdash_ {p} [ [ t ] ] _ {v : \Upsilon} : ((\Phi)) _ {v : \Upsilon}}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma \vdash_ {p} t : \Phi \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} t \sigma : \Phi \sigma \operatorname{tel} _ {\ell_ {1}}}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma | (v : \Upsilon) \vdash_ {p} t : \Phi v \quad \Gamma \vdash_ {p} \sigma : \Upsilon}{\Gamma \vdash_ {p} [ [ t ] ] _ {v : \Upsilon} \sigma \equiv t [ 1 _ {\Gamma} | \sigma ]}
\]

\[
\frac {\Gamma \vdash_ {p} \Phi \operatorname{tel} _ {\ell_ {1}} / _ {v : \Upsilon} \quad \Gamma \vdash_ {p} t : \Phi \quad \Gamma \vdash_ {p} s : \Phi \quad \Gamma | (v : \Upsilon) \vdash_ {p} t v \equiv s v}{\Gamma \vdash_ {p} t \equiv s}
\]

#### 2.5.2 Telescope concatenation

Telescope concatenation is not necessary for the syntactic definition of SSTs, but seems to be required for a clean description of the semantics. It is essentially a  \( \Sigma \) -type for telescopes, which is definitionally associative with context and telescope extension.

22