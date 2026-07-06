Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:9

PATH-FORM

\[
\frac {\Gamma , x : \mathbb {I} \gg A \text {type} \qquad \Gamma \gg M _ {0} \in A [ 0 / x ] \qquad \Gamma \gg M _ {1} \in A [ 1 / x ]}{\Gamma \gg \operatorname{Path} _ {x . A} (M _ {0} , M _ {1}) \text {type}}
\]

PATH-INTRO

\[
\frac {\Gamma , x : \mathbb {I} \gg M \in A}{\Gamma \gg \lambda^ {\mathbb {I}} x . M \in \operatorname{Path} _ {x . A} (M [ 0 / x ] , M [ 1 / x ])}
\]

PATH-ELIM

\[
\frac {\Gamma \gg P \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1}) \qquad \Gamma \gg r \in \mathbb {I}}{\Gamma \gg P @ r \in A [ r / x ]}
\]

PATH- \( \beta \)

\[
\frac {\Gamma , x : \mathbb {I} \gg M \in A}{\Gamma \gg (\lambda^ {\mathbb {I}} x . M) @ r = M [ r / x ] \in A [ r / x ]}
\]

PATH- \( \partial \)

\[
\frac {\Gamma \gg P \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1}) \qquad \varepsilon \in \{0 , 1 \}}{\Gamma \gg P @ \varepsilon = M _ {\varepsilon} \in A [ \varepsilon / x ]}
\]

PATH-η

\[
\frac {\Gamma \gg P \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1})}{\Gamma \gg P = \lambda^ {\mathbb {I}} x . P @ x \in \mathsf {P a t h} _ {x . A} (M _ {0} , M _ {1})}
\]

Figure 1: Rules for Path-types

substitution rules defined for any \(\Gamma\) ctx.

I-WEAKENING

\[
\overline {{\Gamma , x : \mathbb {I} \gg \mathsf {p} _ {\mathbb {I}} \in \Gamma}}
\]

I-CONTRACTION

\[
\overline {{\Gamma , z : \mathbb {I} \gg (\mathrm{id} _ {\Gamma} , z / x , z / y) \in (\Gamma , x : \mathbb {I} , y : \mathbb {I})}}
\]

I-EXCHANGE

\[
\overline {{\Gamma , y : \mathbb {I} , x : \mathbb {I} \gg (\mathrm{id} _ {\Gamma} , x / x , y / y) \in (\Gamma , x : \mathbb {I} , y : \mathbb {I})}}
\]

We may also exchange interval variable assumptions with term variable assumptions when it makes type sense to do so. The contraction and exchange substitutions may be derived from the following more fundamental rule, which allows us to extend a substitution by a path interval term.

I-SUBST

\[
\frac {\Gamma^ {\prime} \gg \gamma \in \Gamma \qquad \Gamma^ {\prime} \gg r \in \mathbb {I}}{\Gamma^ {\prime} \gg (\gamma , r / x) \in (\Gamma , x : \mathbb {I})}
\]

Finally, cubical type theory includes one more way to extend the context: with a constraint, an assumption that two interval terms are (exactly) equal. These become relevant when we introduce composition below.

\[
\frac {\Gamma \gg r \in \mathbb {I} \quad \Gamma \gg s \in \mathbb {I}}{\Gamma \gg r = s \text {   constraint }}
\]

\[
\frac {\Gamma \gg \xi \text {   constraint }}{(\Gamma , \xi) \text {   ctx }}
\]

\[
\frac {\Gamma \gg r \in \mathbb {I} \qquad \Gamma \gg s \in \mathbb {I}}{\Gamma , r = s \gg r = s \in \mathbb {I}}
\]

Once again, we have weakening, exchange, and contraction for constraints.

Aside from these additions, the judgmental apparatus of cubical type theory matches ordinary Martin-Löf type theory. We take standard type formers (functions, products, universes) for granted and proceed to the novel components: Path-types, the Kan operations, V-types (which underlie univalence), and higher inductive types.