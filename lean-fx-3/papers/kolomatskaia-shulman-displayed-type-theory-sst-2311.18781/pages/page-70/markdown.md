#### 4.3.4 Locks and Keys

The definition of \(\mathfrak{sm}^+\) is tailored to allow us to define \(\widehat{\mathbf{a}}_{\diamond}\). Putting this together with the \(\widehat{\mathbf{a}}_{\triangle}\) and \(\widehat{\mathbf{a}}_{\square}\) defined on \(\mathfrak{sm}\) in sections 4.3.1 and 4.3.2, we now define a 2-functor \([[-]]: \mathcal{M}^{\mathrm{coop}} \to \mathcal{C}at\), where \(\mathcal{M}^{\mathrm{coop}}\) denotes the 2-category obtained by reversing both 1 and 2 cells. On modes, we have:

\[
[ [ \mathrm{dm} ] ] \equiv \mathcal {C}
\]

\[
[ [ \mathrm{sm} ] ] \equiv \mathcal {C} _ {+} ^ {\Delta^ {+}}.
\]

To define this 2-functor on modalities, we extend the prior definitions of locks to \(\mathfrak{sm}_{+}\):

\[
\left(-, \widehat {\mathbf {a}} _ {\triangle} ^ {+}\right): \mathcal {C} _ {+} ^ {\Delta^ {+}} \rightarrow \mathcal {C}
\]

\[
\left(-, \widehat {\mathbf {a}} _ {\square} ^ {+}\right): \mathcal {C} \rightarrow \mathcal {C} _ {+} ^ {\Delta^ {+}}
\]

\[
\left(-, \widehat {\mathbf {a}} _ {\diamond} ^ {+}\right): \mathcal {C} \rightarrow \mathcal {C} _ {+} ^ {\Delta^ {+}}
\]

\[
\left(\operatorname{in} _ {\mathfrak {s m}} \Gamma , \widehat {\mathbf {a}} _ {\triangle} ^ {+}\right) \equiv (\Gamma , \widehat {\mathbf {a}} _ {\triangle})
\]

\[
\left(\Gamma , \widehat {\mathbf {a}} _ {\square} ^ {+}\right) \equiv \operatorname{in} _ {\mathrm{sm}} \left(\Gamma , \widehat {\mathbf {a}} _ {\square}\right)
\]

\[
\left(\Gamma , \widehat {\mathbf {a}} _ {\diamond} ^ {+}\right) \equiv \operatorname{in} _ {\mathrm{dm}} \Gamma
\]

\[
\left(\operatorname{in} _ {\mathrm{dm}} \Gamma , \widehat {\mathbf {a}} _ {\triangle} ^ {+}\right) \equiv \Gamma
\]

\[
[ \mathrm{in} _ {\mathrm{sm}} \sigma , \widehat {\mathbf {a}} _ {\triangle} ^ {+} ] \equiv \sigma_ {- 1}
\]

\[
[ \sigma , \widehat {\mathbf {a}} _ {\square} ^ {+} ] _ {m + 1} \equiv \operatorname{in} _ {\mathrm{sm}} [ \sigma , \widehat {\mathbf {a}} _ {\square} ]
\]

\[
[ \sigma , \widehat {\mathbf {a}} _ {\diamond} ^ {+} ] \equiv \operatorname{in} _ {\mathrm{dm}} \sigma .
\]

\[
[ \mathrm{in} _ {\mathrm{dm}} \sigma , \widehat {\mathbf {a}} _ {\triangle} ^ {+} ] \equiv \sigma
\]

\[
[ \mathrm{in} _ {\mathrm{fl}} \sigma , \widehat {\mathbf {a}} _ {\triangle} ^ {+} ] \equiv \sigma
\]

We then define the evident composites:

\[
\left(-, \widehat {\mathbf {a}} _ {\triangle \square} ^ {+}\right) \equiv \left(-, \widehat {\mathbf {a}} _ {\triangle} ^ {+}, \widehat {\mathbf {a}} _ {\square} ^ {+}\right)
\]

\[
\left(-, \widehat {\mathbf {a}} _ {\triangle \diamond} ^ {+}\right) \equiv \left(-, \widehat {\mathbf {a}} _ {\triangle} ^ {+}, \widehat {\mathbf {a}} _ {\diamond} ^ {+}\right).
\]

Finally, it is easy to check that \(\left(-,\widehat{\mathbf{a}}_{\square}^{+},\widehat{\mathbf{a}}_{\triangle}^{+}\right)\) and \(\left(-,\widehat{\mathbf{a}}_{\diamond}^{+},\widehat{\mathbf{a}}_{\triangle}^{+}\right)\) define identity functors. It follows that we have a contravariantly functorial assignment:

\[
\frac {\mu : p \to q}{[ [ \mu ] ] \equiv (- , \widehat {\mathbf {a}} _ {\mu} ^ {+}) : [ [ q ] ] \to [ [ p ] ]}
\]

Next, to define this 2-functor on 2-cells, we define the key natural transformations. We have \(\square \leqslant \diamond\), \(\triangle \square \leqslant 1_{\mathrm{sm}_+}\), and \(1_{\mathrm{sm}_+} \leqslant \triangle \diamond\), which corresponds to the following natural transformations:

\[
\mathbf {a} _ {\bullet} ^ {\square \leqslant \diamond}: (-, \widehat {\mathbf {a}} _ {\diamond} ^ {+}) \Rightarrow (-, \widehat {\mathbf {a}} _ {\square} ^ {+})
\]

\[
\mathbf {a} _ {\bullet} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm} +}}: 1 _ {\mathrm{sm} +} \Rightarrow (-, \widehat {\mathbf {a}} _ {\triangle \square} ^ {+})
\]

\[
\mathbf {a} _ {\bullet} ^ {1 _ {\mathrm{sm} +} \leqslant \triangle \diamond}: (-, \widehat {\mathbf {a}} _ {\triangle \diamond} ^ {+}) \Rightarrow 1 _ {\mathrm{sm} +}
\]

\[
\mathbf {a} _ {\Gamma} ^ {\square \leqslant \diamond} \equiv \operatorname{in} _ {\mathrm{fl}} 1 _ {\Gamma}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{sm}} \Gamma} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm} +}} \equiv \operatorname{in} _ {\mathrm{sm}} \mathbf {a} _ {\Gamma} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm}}}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{sm}} \Gamma} ^ {1 _ {\mathrm{sm}} \leqslant \triangle \diamond} \equiv \operatorname{in} _ {\mathrm{fl}} 1 _ {\Gamma - 1}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{dm}} \Gamma} ^ {\triangle \square \leqslant 1 _ {\mathrm{sm}}} \equiv \operatorname{in} _ {\mathrm{fl}} 1 _ {\Gamma}
\]

\[
\mathbf {a} _ {\mathrm{in} _ {\mathrm{dm}} \Gamma} ^ {1 _ {\mathrm{sm}} \leqslant \triangle \diamond} \equiv \operatorname{in} _ {\mathrm{dm}} 1 _ {\Gamma}.
\]

We also have \(\mathbf{a}_{\bullet}^{\triangle \square \leqslant \triangle \diamond} \equiv \mathbf{a}_{\bullet}^{\triangle \square \leqslant 1_{\mathrm{sm}_{+}}} \circ \mathbf{a}_{\bullet}^{1_{\mathrm{sm}_{+}} \leqslant \triangle \diamond}\). The keys assemble into a contravariantly functorial assignment:

\[
\frac {\alpha : \mu \leqslant \nu}{[ [ \alpha ] ] \equiv \mathbf {a} _ {\bullet} ^ {\alpha} : [ [ \nu ] ] \Rightarrow [ [ \mu ] ]}.
\]

One checks whiskering identities to verify that  \( [[-] \)  defines a 2-functor  \( M^{coop} \to Cat \) .

◀

70