J. Ceulemans, A. Nuyts and D. Devriese

27

= CASE  \( v = v_{0}^{\alpha} \)  with  \( \alpha \in \mu \Rightarrow \text{locks}(\Lambda) \) .

Then we get that

\[
\begin{array}{l} \mathbf {v} _ {0} ^ {\alpha} \left[ \pi^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 6}) \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 6, repeated}) \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \left[ \boldsymbol {\mathcal {Q}} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}} \quad (\text {Equation (26)}) \\ = \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ \begin{array}{c} \boldsymbol {\mathcal {Q}} _ {\hat {\Delta} \mu} ^ {\alpha \in \widehat {\boldsymbol {\Omega}} _ {\mu} \Rightarrow \Lambda} \\ \end{array} \right] _ {\text {aren}} [ [ [ \sigma ] ] \cdot \Lambda ] _ {\text {sub}} \quad (\text {Proposition 23}) \\ = \mathbf {v} _ {0} ^ {\alpha} \left[ [ [ \sigma ] ] \cdot \Lambda \right] _ {\text {sub}}. \\ \end{array}
\]

= CASE  \( v = \text{suc}(v') \)  with  \( \hat{\Delta} \cdot \Lambda \vdash_{sf} v' \text{ var } @ o \)

Now we can compute

\[
\begin{array}{l} \operatorname{suc} \left(v ^ {\prime}\right) \left[ \pi^ {+} \right] _ {\text {asub}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \\ = v ^ {\prime} [ \pi ] _ {\text {asub}} ^ {\Lambda} [ \pi ] _ {\text {aren}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} [ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 6}) \\ = \operatorname{suc} \left(v ^ {\prime}\right) [ \pi ] _ {\text {aren}} ^ {\Lambda} \left[ [ [ \sigma ] ] ^ {+} \cdot \Lambda \right] _ {\text {sub}} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} [ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} ] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ [ [ \sigma ] ] \cdot \Lambda \right] _ {\text {sub}} \left[ \pi \right] _ {\text {aren}} ^ {\Lambda} \left[ \mathrm{id} ^ {\mathrm{a}}. \mathbf {v} _ {0} ^ {1 _ {\mu}} \left[ [ [ \sigma ] ] \cdot \widehat {\boldsymbol {\Omega}} _ {\mu} \right] _ {\text {sub}} \right] _ {\text {asub}} ^ {\Lambda} \quad (\text {Lemma 9}) \\ = \operatorname{suc} \left(v ^ {\prime}\right) \left[ [ [ \sigma ] ] \cdot \Lambda \right] _ {\text {sub}}, \\ \end{array}
\]

where the last equation is proved as in the case of WSMTT-EQ-SUB-EXTEND-WEAKEN.

CASE \(\vdash_{\mathrm{ws}}\mathrm{id}.\widehat{\boldsymbol{\Omega}}_{\mu}\equiv^{\sigma}\mathrm{id}\mathrm{sub}(\hat{\Gamma}.\widehat{\boldsymbol{\Omega}}_{\mu}\to \hat{\Gamma}.\widehat{\boldsymbol{\Omega}}_{\mu})@m\) (WSMTT-EQ-SUB-LOCK-ID)

The translations of both sides of this equivalence are the empty sequence of atomic SFMTT substitutions, so this case is trivial.

CASE \(\vdash_{\mathrm{ws}} (\sigma \circ \tau) \cdot \widehat{\boldsymbol{\Omega}}_{\mu} \equiv^{\sigma} (\sigma \cdot \widehat{\boldsymbol{\Omega}}_{\mu}) \circ (\tau \cdot \widehat{\boldsymbol{\Omega}}_{\mu}) \operatorname{sub}(\hat{\Gamma} \cdot \widehat{\boldsymbol{\Omega}}_{\mu} \to \widehat{\Xi} \cdot \widehat{\boldsymbol{\Omega}}_{\mu}) @ m\) (WSMTT-EQ-SUB-LOCK-COMPOSE)

Again this case is trivial since a lock is applied to every atomic substitution in a sequence and hence it distributes over sequence concatenation.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Delta}}^{\alpha \in \Lambda \Rightarrow \Theta} \circ (\sigma \cdot \Theta) \equiv^{\sigma} (\sigma \cdot \Lambda) \circ \mathcal{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta} \operatorname{sub}(\hat{\Gamma} \cdot \Theta \to \hat{\Delta} \cdot \Lambda) @ n\) (WSMTT-EQ-SUB-KEY-NATURAL)

This is a direct consequence of Proposition 23.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Gamma}}^{1_{\mathrm{locks}(\Lambda)} \in \Lambda \Rightarrow \Lambda} \equiv^{\sigma} \mathrm{id} \operatorname{sub}(\hat{\Gamma} \cdot \Lambda \to \hat{\Gamma} \cdot \Lambda) @ n\) (WSMTT-EQ-SUB-KEY-UNIT)

Applying an SFMTT key substitution is exactly the same as applying the corresponding key renaming (which can be easily proved using Proposition 11), so this case follows immediately from Proposition 20.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Gamma}}^{\beta \circ \alpha \in \Lambda \Rightarrow \Psi} \equiv^{\sigma} \mathcal{Q}_{\hat{\Gamma}}^{\alpha \in \Lambda \Rightarrow \Theta} \circ \mathcal{Q}_{\hat{\Gamma}}^{\beta \in \Theta \Rightarrow \Psi} \operatorname{sub}(\hat{\Gamma} \cdot \Psi \to \hat{\Gamma} \cdot \Lambda) @ n\) (WSMTT-EQ-SUB-KEY-COMPOSE-VERTICAL)

In the same way, the result in this case is proved by Proposition 21.

CASE \(\vdash_{\mathrm{ws}} \mathcal{Q}_{\hat{\Gamma}}^{\beta \circ \alpha \in \Lambda_1 \cdot \Theta_1 \Rightarrow \Lambda_2 \cdot \Theta_2} \equiv^{\sigma} (\mathcal{Q}_{\hat{\Gamma}}^{\beta \in \Lambda_1 \Rightarrow \Lambda_2 \cdot \Theta_1}) \circ \mathcal{Q}_{\hat{\Gamma} \cdot \Lambda_2}^{\alpha \in \Theta_1 \Rightarrow \Theta_2} \operatorname{sub}(\hat{\Gamma} \cdot \Lambda_2 \cdot \Theta_2 \to \hat{\Gamma} \cdot \Lambda_1 \cdot \Theta_1) @ o\) (WSMTT-EQ-SUB-KEY-COMPOSE-HORIZONTAL)

This is a direct consequence of Proposition 22.

◀