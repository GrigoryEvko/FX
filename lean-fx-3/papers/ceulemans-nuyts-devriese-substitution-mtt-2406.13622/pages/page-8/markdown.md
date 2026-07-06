8

A Substitution Algorithm for Multimode Type Theory: Technical Report

### 3.2 Applying SFMTT Substitutions

#### Atomic rensubs acting on non-variable expressions

All cases for applying an atomic rensub to an SFMTT expression that is not a variable are shown below. These also include the cases that were omitted in Section 3.2.1 in the paper.

\[
\text { Bool } [ \sigma ] _ {\text { aren / asub }} = \text { Bool } \tag {4}
\]

\[
\text { true } [ \sigma ] _ {\text { aren / asub }} = \text { true } \tag {5}
\]

\[
\text { false } [ \sigma ] _ {\text { aren / asub }} = \text { false } \tag {6}
\]

\[
\text { if } (A; s; t; t ^ {\prime}) [ \sigma ] _ {\text { aren / asub }} =
\]

\[
\text { if } \left(A \left[ \sigma^ {+} \right] _ {\text { aren / asub }}; s [ \sigma ] _ {\text { aren / asub }}; t [ \sigma ] _ {\text { aren / asub }}; t ^ {\prime} [ \sigma ] _ {\text { aren / asub }}\right) \tag {7}
\]

\[
\left((\mu \mid A) \rightarrow B\right) [ \sigma ] _ {\text {aren / asub}} = \left(\mu \mid A [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}\right)\rightarrow B [ \sigma^ {+} ] _ {\text {aren / asub}} \tag {8}
\]

\[
\left(\lambda^ {\mu} (t)\right) [ \sigma ] _ {\text {aren / asub}} = \lambda^ {\mu} \left(t [ \sigma^ {+} ] _ {\text {aren / asub}}\right) \tag {9}
\]

\[
\operatorname{app} _ {\mu} (f; t) [ \sigma ] _ {\text {aren / asub}} = \operatorname{app} _ {\mu} \left(f [ \sigma ] _ {\text {aren / asub}}; t [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}\right) \tag {10}
\]

\[
\langle \mu | A \rangle [ \sigma ] _ {\text {aren / asub}} = \left\langle \mu | A [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}} \right\rangle \tag {11}
\]

\[
\operatorname{mod} _ {\mu} (t) [ \sigma ] _ {\text {aren / asub}} = \operatorname{mod} _ {\mu} \left(t [ \sigma . \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}\right) \tag {12}
\]

\[
\operatorname{letmod} _ {\nu , \mu} (A; B; t; s) [ \sigma ] _ {\text {aren / asub}} =
\]

\[
\operatorname{letmod} _ {\nu , \mu} \left(A [ \sigma . \widehat {\mathbf {u}} _ {\nu}. \widehat {\mathbf {u}} _ {\mu} ] _ {\text {aren / asub}}; B [ \sigma^ {+} ] _ {\text {aren / asub}}; t [ \sigma . \widehat {\mathbf {u}} _ {\nu} ] _ {\text {aren / asub}}; \right.
\]

\[
s \left[ \sigma^ {+} \right] _ {\text {aren / asub}}) \tag {13}
\]

#### Atomic rensubs acting on variables

For easy reference in the proofs in the next sections, we recall the algorithm for applying an atomic rensub to a variable. First of all, for applying a 2-cell to a variable, we have the following:

\[
\mathbf {v} _ {0} ^ {\beta} [ \alpha ] _ {2 - \text { cell }} ^ {\Theta \Rightarrow \Psi} = \mathbf {v} _ {0} ^ {(1 _ {\text { locks } (\Lambda)} \star \alpha) \circ \beta} \tag {14}
\]

\[
\operatorname{suc} (v) [ \alpha ] _ {2 - \text { cell }} ^ {\Theta \Rightarrow \Psi} = \operatorname{suc} \left(v [ \alpha ] _ {2 - \text { cell }} ^ {\Theta \Rightarrow \Psi}\right). \tag {15}
\]

The algorithm for applying a renaming to a variable is given by

\[
v \left[ \mathrm{id} ^ {\mathrm{a}} \right] _ {\text {aren,var}} ^ {\Lambda} = v \tag {16}
\]

\[
v \left[ \text { weaken } (\sigma) \right] _ {\text { aren,var }} ^ {\Lambda} = \text { suc } \left(v [ \sigma ] _ {\text { aren,var }} ^ {\Lambda}\right) \tag {17}
\]

\[
v \left[ \sigma . \widehat {\mathbf {u}} _ {\mu} \right] _ {\text {aren,var}} ^ {\Lambda} = v \left[ \sigma \right] _ {\text {aren,var}} ^ {\widehat {\mathbf {u}} _ {\mu}. \Lambda} \tag {18}
\]

\[
v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Theta \Rightarrow \Psi} \right] _ {\text {aren,var}} ^ {\Lambda} = v \left[ \beta \star 1 _ {\text {locks} (\Lambda)} \right] _ {2 - \text {cell}} ^ {\Theta . \Lambda \Rightarrow \Psi . \Lambda} \tag {19}
\]

\[
\mathbf {v} _ {0} ^ {\alpha} [ \sigma . w ] _ {\text {aren,var}} ^ {\Lambda} = w [ \alpha ] _ {2 - \text {cell}} ^ {\widehat {\mathbf {u}} _ {\alpha} \Rightarrow \Lambda} \tag {20}
\]

\[
\operatorname{suc} (v) [ \sigma . w ] _ {\text {aren,var}} ^ {\Lambda} = v [ \sigma ] _ {\text {aren,var}} ^ {\Lambda}. \tag {21}
\]