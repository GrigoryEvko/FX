78

Cubical type theory

|  Judgment | Presuppositions | Reading  |
| --- | --- | --- |
|  \( \Gamma \vdash r : \mathbb{I} \) | \( (\Gamma \text{ ctx}) \) | \( r \) is a path interval term in context \( \Gamma \)  |
|  \( \Gamma \vdash r = r' : \mathbb{I} \) | \( (\Gamma \vdash r, r' : \mathbb{I}) \) | \( r \) and \( r' \) are equal path interval terms  |
|  \( \Gamma \vdash \xi : \mathbb{F} \) | \( (\Gamma \text{ ctx}) \) | \( \xi \) is a constraint in context \( \Gamma \)  |
|  \( \Gamma \vdash \xi = \xi' : \mathbb{F} \) | \( (\Gamma \vdash \xi, \xi' : \mathbb{F}) \) | \( \xi \) and \( \xi' \) are equal constraints  |
|  \( \Gamma \vdash \xi \) satisfied | \( (\Gamma \vdash \xi : \mathbb{F}) \) | \( \xi \) is a satisfied constraint in context \( \Gamma \)  |

The interval and constraint judgments are simple to axiomatize, interval and constraint assumptions behaving not dissimilarly to ordinary term variable assumptions. To begin with, we have two new context formers.

\[
\frac {\Gamma \operatorname{ctx}}{\Gamma . \mathbb {I} \operatorname{ctx}} \qquad \qquad \frac {\Gamma \vdash \xi : \mathbb {F}}{\Gamma . \xi \operatorname{ctx}}
\]

The rules for substitutions into contexts with an interval or constraint match their term equivalents.

\[
\frac {\Gamma^ {\prime} \vdash \gamma : \Gamma \qquad \Gamma^ {\prime} \vdash r : \mathbb {I}}{\Gamma^ {\prime} \vdash \gamma . r : \Gamma . \mathbb {I}} \qquad \overline {{\Gamma . \mathbb {I} \vdash p _ {\mathbb {I}} : \Gamma}} \qquad \frac {\Gamma^ {\prime} \vdash \gamma : \Gamma \qquad \Gamma^ {\prime} \vdash \xi [ \gamma ] \text {satisfied}}{\Gamma^ {\prime} \vdash \gamma . \star : \Gamma . \xi}
\]

\[
\frac {\Gamma \vdash \xi : \mathbb {F}}{\Gamma . \xi \vdash p _ {\mathbb {F}} : \Gamma} \qquad \Gamma^ {\prime} \vdash p \circ (\gamma . r) = \gamma : \Gamma \qquad \Gamma^ {\prime} \vdash \gamma = (p _ {\mathbb {I}} \circ \gamma). v _ {\mathbb {I}} [ \gamma ]: \Gamma . \mathbb {I}
\]

\[
\Gamma^ {\prime} \vdash p _ {\mathbb {F}} \circ (\gamma . \star) = \gamma : \Gamma \quad \Gamma^ {\prime} \vdash \gamma = (p _ {\mathbb {F}} \circ \gamma). \star : \Gamma . \xi
\]

In addition to variables, the interval is inhabited by the two constants; constraints take the form of equations and are satisfied when those equations hold.

\[
\frac {\Gamma \operatorname{ctx}}{\Gamma . \mathbb {I} \vdash v _ {\mathbb {I}} : \mathbb {I}} \qquad \overline {{\Gamma \vdash 0 : \mathbb {I}}} \qquad \overline {{\Gamma \vdash 1 : \mathbb {I}}} \qquad \frac {\Gamma \vdash \delta : \Delta \qquad \Gamma \vdash r : \mathbb {I}}{\Gamma \vdash v _ {\mathbb {I}} [ \delta . r ] = r : \mathbb {I}} \qquad \frac {\Gamma \operatorname{ctx}}{\Gamma . \xi \vdash \xi \text {satisfied}}
\]

\[
\frac {\Gamma \vdash r : \mathbb {I} \qquad \Gamma \vdash s : \mathbb {I}}{\Gamma \vdash r \equiv s : \mathbb {F}} \qquad \qquad \frac {\Gamma \vdash r : \mathbb {I}}{\Gamma \vdash r \equiv r \text {satisfied}}
\]

\[
\frac {\Gamma \vdash r : \mathbb {I} \qquad \Gamma \vdash s : \mathbb {I} \qquad \Gamma \vdash r \equiv s \text {   satisfied }}{\Gamma \vdash r = s : \mathbb {I}}
\]

With the judgmental apparatus in place, we can specify the type-generic rules for coercion.