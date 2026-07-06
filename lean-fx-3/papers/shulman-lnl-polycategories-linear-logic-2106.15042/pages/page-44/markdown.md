1:44

M. SHULMAN

Vol. 19:2

\[
\frac {A \in \mathcal {S} ^ {\tau}}{A \text {type} ^ {\tau}} \qquad \frac {\mathcal {C} \text {a} \mathbb {D} \text {-cone} \qquad \partial \mathcal {C} = \{r _ {1} ^ {\tau_ {1}} , \ldots , r _ {n} ^ {\tau_ {n}} \} \qquad R _ {1} \text {type} ^ {\tau_ {1}} \qquad \cdots \qquad R _ {n} \text {type} ^ {\tau_ {n}}}{\bigodot_ {\mathcal {C}} [ R _ {1} , \ldots , R _ {n} ] \text {type} ^ {\tau_ {\mathcal {C}}}}
\]

(A) Type-forming rules

\[
\frac {R \text {type} ^ {\tau}}{\vdash R ^ {-} , R ^ {+}} \qquad \frac {\vdash \Phi , K \qquad \vdash K ^ {\bullet} , \Psi}{\vdash \Phi , \Psi} \qquad \frac {\vdash \Psi \qquad \sigma : \Phi \to \Psi \text {a structural map}}{\vdash \Phi}
\]

(B) Structural rules

\[
\frac {f \in \mathcal {S} (\Phi)}{\vdash \Phi}
\]

(c) Generator rule

\[
\begin{array}{c} \mathcal {C} \text {a} \mathbb {D} \text {-cone with vertex} r ^ {\varepsilon} \qquad \partial \mathcal {C} = \{r _ {1} ^ {\tau_ {1}}, \ldots , r _ {n} ^ {\tau_ {n}} \} \\ R _ {1} \text {type} ^ {\tau_ {1}} \qquad \dots \qquad R _ {n} \text {type} ^ {\tau_ {n}} \qquad f \in \mathcal {C} (r _ {i _ {1}} ^ {\varepsilon_ {1}}, \ldots , r _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, r ^ {\varepsilon}) \text {an abstract projection} \\ \hline \vdash R _ {i _ {1}} ^ {\varepsilon_ {1}}, \ldots , R _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, \bigodot_ {\mathcal {C}} [ R _ {1}, \ldots , R _ {n} ] ^ {\varepsilon} \end{array}
\]

(D) Noninvertible logical rule

\[
\begin{array}{l} \mathcal {C} \text {   a   } \mathbb {D} \text {-cone with vertex   } r ^ {\varepsilon} \text {   of   class   } \tau_ {\mathcal {C}} \qquad \partial \mathcal {C} = \{r _ {1} ^ {\tau_ {1}}, \ldots , r _ {n} ^ {\tau_ {n}} \} \\ R _ {1} \text {type} ^ {\tau_ {1}} \quad \dots \quad R _ {n} \text {type} ^ {\tau_ {n}} \quad S _ {1} \text {type} ^ {\sigma_ {1}} \quad \dots \quad S _ {m} \text {type} ^ {\sigma_ {m}} \\ | \mathbb {D} | (\tau_ {\mathcal {C}} ^ {- \varepsilon}, \sigma_ {1} ^ {\eta_ {1}}, \dots , \sigma_ {m} ^ {\eta_ {m}}) \neq \emptyset \\ \left\{\vdash R _ {i _ {1}} ^ {\varepsilon_ {1}}, \dots , R _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, S _ {1} ^ {\eta_ {1}}, \dots , S _ {m} ^ {\eta_ {m}} \right\} _ {f \in \mathcal {C} (r _ {i _ {1}} ^ {\varepsilon_ {1}}, \dots , r _ {i _ {\ell}} ^ {\varepsilon_ {\ell}}, r ^ {\varepsilon}) \text {an abstract projection}} \\ \vdash \bigodot_ {\mathcal {C}} [ R _ {1}, \dots , R _ {n} ] ^ {- \varepsilon}, S _ {1} ^ {\eta_ {1}}, \dots , S _ {m} ^ {\eta_ {m}} \\ \end{array}
\]

(E) Invertible logical rule

FIGURE 2. LNL Sequent calculus

We can now describe \(\widehat{\mathcal{S}}_{\mathbb{D}}\) using a sequent calculus, defined formally in Figure 2. There are two classes of types, linear and nonlinear, written \(A\) type\(^{\mathrm{L}}\) and \(X\) type\(^{\mathrm{NL}}\). Generically, we write \(R\) type\(^{\tau}\) for an arbitrary class \(\tau \in \{\mathrm{L},\mathrm{NL}\}\). The first rule in Figure 2a says that every object of \(\mathcal{S}\) determines a type of the appropriate class.

By assumption, the reduct \(\partial \mathcal{C}\) of each \(\mathbb{D}\)-cone is a discrete LNL polycategory with finitely many objects. We assume the objects of each \(\partial \mathcal{C}\) are ordered as \(\{r_1^{\tau_1},\ldots ,r_n^{\tau_n}\}\), the notation meaning that \(r_i\) is of class \(\tau_{i}\), and the vertex \(k\) of class \(\tau_{\mathcal{C}}\). The second rule in Figure 2a says that every such cone induces an operation on types. The notation \(\bigodot_{\mathcal{C}}[R_1,\dots ,R_n]\) is chosen to be generic over the cone \(\mathcal{C}\), but for particular choices of \(\mathcal{C}\) we use the notations of Section 2, e.g. \(A\otimes B\), \(\mathsf{F}X\), \(X\times A\), \(A\& B\), etc.