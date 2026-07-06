4.2.4.2 The Inductive Cases Now we give the inductive definitions and proofs of the objects and theorems declared previously. The model \(\mathfrak{sm}^{-2}\) is the terminal CwF on the terminal category. For \(\mathfrak{sm}^{-1}\), we have that:

\[
A _ {\partial (- 1)} \equiv () _ {d m} \quad t _ {\partial (- 1)} \equiv [ ] _ {d m}
\]

from which the rest of the definitions and theorems evidently follow.

Suppose now that the model \(\mathfrak{sm}^{n + 1}\) has been defined with all of the above structure and properties. We first define matching telescopes and substitutions as follows:

\[
A _ {\partial (n + 2)} \gamma_ {n + 2} \equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \gamma_ {n + 2}, a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} \gamma_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} [ \gamma_ {n + 2}, \partial a, a ]\right)
\]

\[
\mathsf {t} _ {\partial (n + 2)} \gamma_ {n + 2} \equiv [ (\pi \mathsf {t} ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)}, (\mathsf {t} ^ {\rho_ {\Gamma}}) _ {n + 1}, (\mathsf {t} ^ {d}) _ {\partial (n + 1)} ].
\]

The stability of these under substitution follows from that of the constituent constructions in the previous dimension; for \(\sigma : \Delta \to \Gamma\) in \(\mathcal{C}^{\Delta_{n+2}^{\tau}}\):

\[
\left(A ^ {\pi \sigma}\right) _ {\partial (n + 2)} \delta_ {n + 2}
\]

\[
\equiv \left(\partial a: (\pi A ^ {\pi \pi \sigma \circ \rho_ {\pi \Delta}}) _ {\partial (n + 1)} \delta_ {n + 2}, a: (A ^ {\pi \sigma \circ \rho_ {\Delta}}) _ {n + 1} \delta_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(\left(A ^ {\pi \sigma}\right) ^ {d}\right) _ {\partial (n + 1)} [ \delta_ {n + 2}, \partial a, a ]\right)
\]

\[
\equiv \left(\partial a: \left(\pi A ^ {\rho_ {\pi \Gamma} \circ \pi \sigma^ {0}}\right) _ {\partial (n + 1)} \delta_ {n + 2}, a: \left(A ^ {\rho_ {\Gamma} \circ \sigma^ {0}}\right) _ {n + 1} \delta_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(\left(A ^ {d}\right) ^ {\pi W _ {2} ^ {A ^ {\rho_ {\Gamma}}} \sigma^ {0}}\right) _ {\partial (n + 1)} [ \delta_ {n + 2}, \partial a, a ]\right)
\]

\[
\equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \left(\sigma_ {n + 1} ^ {D} \delta_ {n + 2}\right), a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} \left(\sigma_ {n + 1} ^ {D} \delta_ {n + 2}\right) \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} \left[ \left(\sigma_ {n + 1} ^ {D} \delta_ {n + 2}\right), \partial a, a \right]\right)
\]

\[
\equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} (\sigma_ {n + 2} \delta_ {n + 2}), a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} (\sigma_ {n + 2} \delta_ {n + 2}) \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} \left[ \left(\sigma_ {n + 2} \delta_ {n + 2}\right), \partial a, a \right]\right)
\]

\[
\equiv \left(\partial a: (\pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \gamma_ {n + 2}, a: (A ^ {\rho_ {\Gamma}}) _ {n + 1} \gamma_ {n + 2} \partial a, \right.
\]

\[
\left. \partial a ^ {\prime}: \left(A ^ {d}\right) _ {\partial (n + 1)} \left[ \gamma_ {n + 2}, \partial a, a \right]\right) ^ {\sigma_ {n + 2}}
\]

\[
\equiv A _ {\partial (n + 2)} \left(\sigma_ {n + 2} \delta_ {n + 2}\right).
\]

For display, we define:

\[
\pi (A ^ {d}) \equiv \pi A ^ {d} \quad (A ^ {d}) _ {n + 1} \equiv A _ {n + 2}
\]

\[
\pi (t ^ {d}) \equiv \pi t ^ {d} \qquad \qquad (t ^ {d}) _ {n + 1} \equiv t _ {n + 2}.
\]

This definition is well typed because the expected typing judgement for  \( (A^{d})_{n+1} \)  is:

\[
\gamma_ {n + 2}: \Gamma_ {n + 2}, \partial a: (\pi \pi A ^ {\rho_ {\pi \Gamma}}) _ {\partial (n + 1)} \gamma_ {n + 2}, a: (\pi A ^ {\rho_ {\Gamma}}) _ {n + 1} \gamma_ {n + 2} \partial a,
\]

\[
\partial a ^ {\prime}: \left(\pi A ^ {d}\right) _ {\partial (n + 1)} \gamma_ {n + 2} \partial a a \vdash_ {d m} \left(A ^ {d}\right) _ {n + 1} [ \gamma_ {n + 2}, \partial a, a ] \partial a ^ {\prime} \text {type} _ {\mathrm{f}}
\]

56