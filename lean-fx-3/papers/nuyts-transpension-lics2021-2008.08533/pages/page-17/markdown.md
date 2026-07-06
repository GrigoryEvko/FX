Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:17

MODPI

\[
\begin{array}{l} p \mid \Gamma , \widehat {\mathbf {a}} _ {\mu} \vdash A \text {type} _ {\ell} \quad \mu : p \to q \\ q \mid \Gamma , \mu \mid x: A \vdash B \text {type} _ {\ell} \\ \hline q \mid \Gamma \vdash (\mu \mid x: A) \rightarrow B \text {type} _ {\ell} \end{array}
\]

MODPI:INTRO

\[
\begin{array}{l} \mu : p \to q \\ q \mid \Gamma , \mu \mid x: A \vdash b: B \\ \hline q \mid \Gamma \vdash \lambda (\mu \mid x). b: (\mu \mid x: A) \to B \\ \text { where } \lambda (\mu \mid x). (f \cdot_ {\mu} x) = f \end{array}
\]

MODPI:ELIM

\[
\begin{array}{l} q \mid \Gamma \vdash f: (\mu \mid x: A) \rightarrow B \\ p \mid \Gamma , \widehat {\mathbf {a}} _ {\mu} \vdash a: A \quad \mu : p \to q \\ \hline q \mid \Gamma \vdash f \cdot_ {\mu} a: B [ a / x ] \\ \text { where } (\lambda (\mu \mid x). b) \cdot_ {\mu} a = b [ a / x ] \end{array}
\]

Figure 6: Typing rules for MTT's modal \(\Pi\)-types [GKNB21][Nuy20a, fig. 5.7] (of which non-modal \(\Pi\)-types are a special case for \(p = q\) and \(\mu = 1\)).

Then the only remaining thing we need is a 2-cell \(\alpha : \mu \Rightarrow \text{locks}(\Delta)\). This leads to the following admissible variable 'rule'

CTX-MODEXT:VAR:LOOKUP

\[
\begin{array}{l} q \mid \Gamma \text { ctx } \quad \mu : p \to q \\ p \mid \Gamma , \widehat {\mathbf {a}} _ {\mu} \vdash T \text {type} \quad \alpha : \mu \Rightarrow \operatorname{locks} (\Delta) \\ \hline q \mid \Gamma , \mu \mid x: T, \Delta \vdash x _ {\alpha}: T [ \mathrm{id} _ {\Gamma}, \widehat {\mathbf {a}} _ {\alpha} ] \end{array}
\]

where \(x_{\alpha}\) is defined as \(x[\mathrm{id}_{(\Gamma, \mu : x:T)}, \widehat{\mathbf{a}}_{\alpha : \mu \Rightarrow \mathrm{locks}(\Delta)}]\), leaving the necessary weakenings under locks implicit. Substitution is then given by

\[
\begin{array}{l} x _ {\alpha} \left[ \mathrm{id} _ {\Gamma}, a / x, \mathrm{id} _ {\Delta} \right] = x \left[ \mathrm{id} _ {(\Gamma , \mu : x: T)}, \widehat {\mathbf {a}} _ {\alpha} \right] \left[ \mathrm{id} _ {\Gamma}, a / x, \mathrm{id} _ {\Delta} \right] \\ = x \left[ \mathrm{id} _ {\Gamma}, a / x, \widehat {\mathbf {a}} _ {\mu} \right] \left[ \mathrm{id} _ {\Gamma}, \widehat {\mathbf {a}} _ {\alpha} \right] \\ = a [ \mathrm{id} _ {\Gamma}, \widehat {\mathbf {a}} _ {\alpha} ], \\ \end{array}
\]

or more briefly \(x_{\alpha}[a / x] = a[\widehat{\mathbf{a}}_{\alpha}]\).

3.3.4. Modal types, part 2. Modal elimination (WDRA:ELIM, Fig. 4) uses a let-syntax to turn the modal type into a judgemental annotation on a variable.

3.3.5. Modal function types. Modal function type formation and introduction (Fig. 6) are by simple abstraction. Modal function application checks the argument in a locked context, just like modal variable substitution does.

3.4. Left adjoint reminders. In MTT, we can on one hand apply a modality \(\mu : p \to q\) to a type \(T\) to obtain a modal type \(\langle \mu | T \rangle\), and on the other hand we can apply its left adjoint \(\widehat{\mathbf{a}}_{\mu}\) to a context \(\Gamma\) to obtain \(\Gamma, \widehat{\mathbf{a}}_{\mu}\). Type-theoretically, it is only sensible that the lock \(\widehat{\mathbf{a}}_{\mu}\) mentions \(\mu\) for \(\mu\) is a premise of the LOCK rule. From a semantic/categorical viewpoint however, the indirection of mentioning \(\mu\) when you are actually talking about some left adjoint functor \(K = [\widehat{\mathbf{a}}_{\mu}]\) to \(M = [\mu]\) can really get in the way of understanding what is going on.