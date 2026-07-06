#### 4.1.8 Infinite Telescopes

We now define a new judgement \(\gamma : \Gamma \vdash \bar{\Upsilon} \gamma \operatorname{stel}_{\ell}^{\infty}\) whose elements are 'infinite telescopes'. As with meta-abstractions, this is not (yet) introducing new structure on a CwF, rather it is a definition that can be made in the presheaf category of any CwF. The idea is that an infinite telescope consists of an infinite sequence of types each dependent on all the previous ones:

\[
\gamma : \Gamma \vdash \bar {\Upsilon} ^ {0} \gamma \text { type } _ {\ell_ {0}}
\]

\[
\gamma : \Gamma , v ^ {0}: \bar {\Upsilon} ^ {0} \gamma \vdash \bar {\Upsilon} ^ {1} \gamma v ^ {0} \text {type} _ {\ell_ {1}}
\]

\[
\gamma : \Gamma , v ^ {0}: \bar {\Upsilon} ^ {0} \gamma , v ^ {1}: \bar {\Upsilon} ^ {1} \gamma v ^ {0} \vdash \bar {\Upsilon} ^ {1} \gamma v ^ {0} v ^ {1} \text {type} _ {\ell_ {2}}
\]

•
•
•

where \(\ell_n \leqslant \ell\) for all \(n\). Formally, we define this along with its approximating finite telescopes:

\[
\bar {\Upsilon} ^ {\partial 0} \gamma \equiv ()
\]

\[
\bar {\Upsilon} ^ {\partial 1} \gamma \equiv (v ^ {0}: \bar {\Upsilon} ^ {0} \gamma)
\]

\[
\bar {\Upsilon} ^ {\partial 2} \gamma \equiv \left(v ^ {0}: \bar {\Upsilon} ^ {0} \gamma , v ^ {1}: \bar {\Upsilon} ^ {1} \gamma v ^ {0}\right)
\]

•
•
•

so that we can say that in general \(\bar{\Upsilon}^n\) is a type in context (\(\gamma : \Gamma \mid \upsilon : \bar{\Upsilon}^{\partial n}\)). In syntax, this means we give the following bidirectional rule with infinitely many premises:

\[
\begin{array}{l} \left(\gamma : \Gamma \vdash \bar {\Upsilon} ^ {\partial n} \gamma \operatorname{tel} _ {\ell}\right) _ {n \in \mathbb {N}} \quad \left(\gamma : \Gamma \mid \partial v: \bar {\Upsilon} ^ {\partial n} \gamma \vdash \bar {\Upsilon} ^ {n} \gamma \partial v \operatorname{type} _ {\ell_ {n}}\right) _ {n \in \mathbb {N}} \quad (\ell_ {n} \leqslant \ell) _ {n \in \mathbb {N}} \\ \bar {\Upsilon} ^ {\partial 0} \gamma \equiv () \quad (\gamma : \Gamma \vdash \bar {\Upsilon} ^ {\partial (n + 1)} \gamma \equiv (\partial v: \bar {\Upsilon} ^ {\partial n} \gamma , v: \bar {\Upsilon} ^ {n} \gamma \partial v)) _ {n \in \mathbb {N}} \\ \hline \gamma : \Gamma \vdash \bar {\Upsilon} \gamma \operatorname{stel} _ {\ell} ^ {\infty} \\ \end{array}
\]

(It would also be possible to define infinite contexts coinductively, but for our purposes this concrete definition is easier to work with.)

We have already defined substitution on finite telescopes, and that definition extends level-wise to infinite telescopes. Given \(\sigma : \Delta \to \Gamma\) and \(\gamma : \Gamma \vdash \bar{\Upsilon} \gamma \operatorname{stel}_{\ell}^{\infty}\), we define \(\delta : \Delta \vdash \bar{\Upsilon} (\sigma \delta) \operatorname{stel}_{\ell}^{\infty}\) to consist of the data:

\[
\delta : \Delta , \partial v: \bar {\Upsilon} ^ {n} (\sigma \delta) \vdash \bar {\Upsilon} ^ {n} (\sigma \delta) \partial v \text { type } _ {\ell_ {n}}
\]

Similarly, we would like to define infinite partial substitutions as infinite lists of terms sectioning an infinite telescope. This is encapsulated by the judgement  \( \gamma : \Gamma \vdash \bar{\upsilon} \gamma : \bar{\Upsilon} \gamma \) , which is characterised by a similar bidirectional rule:

\[
\begin{array}{l} (\gamma : \Gamma \vdash \bar {v} ^ {\partial n} \gamma : \bar {\Upsilon} ^ {\partial n} \gamma) _ {n \in \mathbb {N}} \quad (\gamma : \Gamma \vdash \bar {v} ^ {n} \gamma : \bar {\Upsilon} ^ {n} \gamma (\bar {v} ^ {\partial n} \gamma)) _ {n \in \mathbb {N}} \\ \bar {v} ^ {\partial 0} \gamma \equiv [ ] \quad (\gamma : \Gamma \vdash \bar {v} ^ {\partial (n + 1)} \gamma \equiv [ \bar {v} ^ {\partial n} \gamma , \bar {v} ^ {n} \gamma ]) _ {n \in \mathbb {N}} \\ \hline \gamma : \Gamma \vdash \bar {v}   \gamma : \bar {\Upsilon}   \gamma \\ \end{array}
\]

Pullback of infinite partial substitutions is defined, as before, to consist of the data:

\[
\delta : \Delta \vdash \bar {v} ^ {n} (\sigma \delta): \bar {\Upsilon} ^ {n} (\sigma \delta) (\bar {v} ^ {\partial n} (\sigma \delta))
\]

49