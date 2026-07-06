#### 4.3.3.1 Contexts and substitutions. We have the following introduction rules:

\[
\frac {\Gamma \mathrm{ob} _ {\mathrm{dm}}}{\mathrm{in} _ {\mathrm{dm}} \Gamma \mathrm{ob} _ {\mathrm{sm} _ {+}}}
\]

\[
\frac {\Gamma \mathrm{ob} _ {\mathrm{sm}}}{\mathrm{in} _ {\mathrm{sm}} \Gamma \mathrm{ob} _ {\mathrm{sm} _ {+}}}
\]

\[
\frac {\sigma : \Delta \rightarrow_ {\mathrm{sm}} \Gamma}{\mathrm{in} _ {\mathrm{sm}} \sigma : \mathrm{in} _ {\mathrm{sm}} \Delta \rightarrow_ {\mathrm{sm} _ {+}} \mathrm{in} _ {\mathrm{sm}} \Gamma}
\]

\[
\frac {\sigma : \Delta \rightarrow_ {\mathrm{dm}} \Gamma}{\mathrm{in} _ {\mathrm{dm}} \sigma : \mathrm{in} _ {\mathrm{dm}} \Delta \rightarrow_ {\mathrm{sm} _ {+}} \mathrm{in} _ {\mathrm{dm}} \Gamma}
\]

\[
\frac {\sigma : \Delta \rightarrow_ {\mathrm{dm}} \Gamma_ {- 1}}{\mathrm{in} _ {\mathrm{fl}} \sigma : \mathrm{in} _ {\mathrm{dm}} \Delta \rightarrow_ {\mathrm{sm} _ {+}} \mathrm{in} _ {\mathrm{sm}} \Gamma}
\]

Equivalently, we can say that the underlying category of \(\mathfrak{sm}_{+}\), which we denote \(\mathcal{C}_{+}^{\Delta +}\), is defined as follows:

\[
\mathrm{ob} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \cong \mathrm{ob} _ {\mathcal {C}} \sqcup \mathrm{ob} _ {\mathcal {C} ^ {\Delta^ {+}}}
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{dm}} \Delta , \operatorname{in} _ {\mathrm{dm}} \Gamma\right) \cong \operatorname{mor} _ {\mathcal {C}} (\Delta , \Gamma)
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{sm}} \Delta , \operatorname{in} _ {\mathrm{sm}} \Gamma\right) \cong \operatorname{mor} _ {\mathcal {C} ^ {\Delta^ {+}}} (\Delta , \Gamma)
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{dm}} \Delta , \operatorname{in} _ {\mathrm{sm}} \Gamma\right) \cong \operatorname{mor} _ {\mathcal {C}} \left(\Delta , \Gamma_ {- 1}\right)
\]

\[
\operatorname{mor} _ {\mathcal {C} _ {+} ^ {\Delta^ {+}}} \left(\operatorname{in} _ {\mathrm{sm}} \Delta , \operatorname{in} _ {\mathrm{dm}} \Gamma\right) \cong \emptyset .
\]

This makes sense, because we intuitively think of  \( in_{dm} \Delta \)  as having been extended by zeroes, thus it is easy to map out of. A substitution of the form  \( in_{fl} \sigma \)  is known as flat.

#### 4.3.3.2 Types and Terms. We have the following introduction forms for types and terms in \(\mathfrak{sm}_{+}\):

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{dm}} A \gamma \text {type} _ {\ell}}{\gamma : \text {in} _ {\mathrm{dm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{dm}} A \gamma \text {type} _ {\ell}}
\]

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{sm}} A \gamma \text {type} _ {\ell}}{\gamma : \text {in} _ {\mathrm{sm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{sm}} A \gamma \text {type} _ {\ell}}
\]

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{dm}} t \gamma : A \gamma}{\gamma : \text {in} _ {\mathrm{dm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{dm}} t \gamma : \text {in} _ {\mathrm{dm}} A \gamma}
\]

\[
\frac {\gamma : \Gamma \vdash_ {\mathrm{sm}} t \gamma : A \gamma}{\gamma : \text {in} _ {\mathrm{sm}} \Gamma \vdash_ {\mathrm{sm} _ {+}} \text {in} _ {\mathrm{sm}} t \gamma : \text {in} _ {\mathrm{sm}} A \gamma}.
\]

Formally, we set the following, depending on whether on not  \( \Gamma \)  is flat:

\[
\mathrm{Ty} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{dm}} \Gamma\right) \cong \mathrm{Ty} _ {\mathrm{dm}} \Gamma
\]

\[
\mathrm{Tm} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{dm}} \Gamma\right) \left(\mathrm{in} _ {\mathrm{dm}} A\right) \cong \mathrm{Tm} _ {\mathrm{dm}} \Gamma A
\]

\[
\mathrm{Ty} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{sm}} \Gamma\right) \cong \mathrm{Ty} _ {\mathrm{sm}} \Gamma
\]

\[
\mathrm{Tm} _ {\mathrm{sm} _ {+}} \left(\mathrm{in} _ {\mathrm{sm}} \Gamma\right) \left(\mathrm{in} _ {\mathrm{sm}} A\right) \cong \mathrm{Tm} _ {\mathrm{sm}} \Gamma A.
\]

Note that, in the following definition of the functorial action of substitutions, the flat case discards higher data:

\[
\left(\operatorname{in} _ {\mathrm{dm}} A\right) ^ {\operatorname{in} _ {\mathrm{dm}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{dm}} t\right) ^ {\operatorname{in} _ {\mathrm{dm}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} A\right) ^ {\operatorname{in} _ {\mathrm{sm}} \sigma} \equiv \operatorname{in} _ {\mathrm{sm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} t\right) ^ {\operatorname{in} _ {\mathrm{sm}} \sigma} \equiv \operatorname{in} _ {\mathrm{sm}} A ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} A\right) ^ {\operatorname{in} _ {\mathrm{fl}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} \left(A _ {- 1}\right) ^ {\sigma}
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} t\right) ^ {\operatorname{in} _ {\mathrm{fl}} \sigma} \equiv \operatorname{in} _ {\mathrm{dm}} \left(A _ {- 1}\right) ^ {\sigma}.
\]

Extension of contexts operates by passing under the inclusion:

\[
\left(\operatorname{in} _ {\mathrm{dm}} \Gamma , \operatorname{in} _ {\mathrm{dm}} A\right) \equiv \operatorname{in} _ {\mathrm{dm}} (\Gamma , A)
\]

\[
\left(\operatorname{in} _ {\mathrm{sm}} \Gamma , \operatorname{in} _ {\mathrm{sm}} A\right) \equiv \operatorname{in} _ {\mathrm{sm}} (\Gamma , A)
\]

\[
\left[ \begin{array}{c c} \text {in} _ {\mathrm{dm}} & \sigma , \text {in} _ {\mathrm{dm}} t \end{array} \right] \equiv \text {in} _ {\mathrm{dm}} [ \sigma , t ]
\]

\[
\left[ \begin{array}{c c} \text {in} _ {\mathrm{sm}} & \sigma , \text {in} _ {\mathrm{sm}} t \end{array} \right] \equiv \text {in} _ {\mathrm{sm}} [ \sigma , t ]
\]

\[
\left[ \begin{array}{c c} \text {in} _ {\mathrm{fl}} & \sigma , \text {in} _ {\mathrm{dm}} t \end{array} \right] \equiv \text {in} _ {\mathrm{fl}} [ \sigma , t ].
\]

68