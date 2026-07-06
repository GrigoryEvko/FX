Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:43

\(\Gamma \mathrm{ctx}\) \(\Gamma\) is a context  
\(\Gamma \vdash r:\mathbf{I}\) \(r\) is a bridge interval term in context \(\Gamma\)  
\(\Gamma \vdash A\) type \(A\) is a type in context \(\Gamma\)  
\(\Gamma \vdash M:A\) \(M\) is a term of type \(A\) in context \(\Gamma\)  
\(\Gamma \vdash \delta :\Delta\) \(\delta\) is a substitution for context \(\Delta\) in context \(\Gamma\)

Figure 9: Judgments of formal parametric type theory

If \( r\psi \) is a variable \( x \), then \( \Psi' \Vdash \mathsf{hcom}_G^{r \rightsquigarrow s}(Q; \overline{\xi_i \hookrightarrow y.Q_i}) = \mathsf{gel}_x(M_{0,s}, M_{1,s}, P) \in G\psi \) and \( \Psi' \Vdash \mathsf{hcom}_{G'}^{r \rightsquigarrow s}(Q'; \overline{\xi_i \hookrightarrow y.Q_i'}) = \mathsf{gel}_x(M_{0,s}', M_{1,s}', P') \in G'\psi \) as defined in Lemma 4.30. Then we have the following.

\(\triangleright \Psi^{\prime}\Vdash \mathsf{hcom}_{G}^{r\rightsquigarrow s}(Q;\overline{\xi_{i}\hookrightarrow y.Q_{i}}) = \mathsf{hcom}_{G^{\prime}}^{r\rightsquigarrow s}(Q^{\prime};\overline{\xi_{i}\hookrightarrow y.Q_{i}^{\prime}})\in G\psi\) follows from the fact that \(\Psi^{\prime}\Vdash \mathsf{gel}_{\pmb{x}}(M_{0,s},M_{1,s},P) = \mathsf{gel}_{\pmb{x}}(M_{0,s}^{\prime},M_{1,s}^{\prime},P^{\prime})\in G\psi\), which holds by GEL-INTRO-\(\partial\), GEL-ELIM, and the assumption that the \(A_{\varepsilon}\) and \(R\) are Kan.
\(\triangleright \Psi^{\prime}\Vdash \mathsf{hcom}_{G}^{r\rightsquigarrow s}(Q;\overline{\xi_{i}\hookrightarrow y.Q_{i}}) = Q_{i}[s / y]\in G\psi\) if \(\xi_{i}\) is true follows by cases on \(\xi_{i}\). If \(\pmb{x}\) does not occur in \(\xi_{i}\), then \(\forall \pmb {x}.\xi_{i} = \xi_{i}\). It follows by the boundary equations for \(\mathsf{hcom}\) in \(A_{\varepsilon}\) and \(R\) that the composite is equal to \(\mathsf{gel}_{\pmb{x}}(Q_{i}[\mathbf{0} / \pmb {x}],Q_{i}[\mathbf{1} / \pmb {x}],\mathsf{ungel}(\pmb {x}.Q_{i}))[s / y]\), and this term is equal to \(Q_{i}[s / y]\) by GEL- \(\eta\). If \(\pmb{x}\) does occur in \(\xi_{i}\), then the constraint must be either \(\pmb {x} = \mathbf{0}\) or \(\pmb {x} = \mathbf{1}\), in which case it is contradictory that \(\xi_{i}\) is true.
\(\triangleright \Psi^{\prime}\Vdash \mathsf{hcom}_{G}^{r\rightsquigarrow r}(Q;\overline{\xi_{i}\hookrightarrow y.Q_{i}}) = Q\in G\psi\) holds by the corresponding Kan equations for the \(A_{\varepsilon}\) and \(R\) together with GEL-INTRO and GEL-\(\eta\).

## 5. FORMAL PARAMETRIC TYPE THEORY

While we have anchored our type theory in a computational interpretation, we would also like to use parametric cubical type theory as a logic for reasoning about other settings. For this reason, we abstract a formal type theory from the collection of inference rules we have developed in the preceding sections. The proofs of those inference rules, as given for Gel-types in Section 4.5, establish that the computational interpretation is one model of the formalism. In Section 6, we see that the theory can also be interpreted in cartesian-affine bicubical sets.

We focus on parametric type theory here; for the cubical ingredients, we defer to prior work [Ang19, Appendix B]. In the pure parametric case, the theory is defined by the judgments shown in Figure 9 and their equality counterparts. We take care to ensure our definition constitutes a generalized algebraic theory (GAT) [Car86], using for example explicit substitutions. \( ^{2} \)  Ensuring admissibility of substitution—that every term is equal to one containing no explicit substitutions—requires some innovation. In particular, the theory presented in [BCM15] does not satisfy admissibility of substitution, a consequence of the way rules using interval terms (such as bridge elimination) are formulated. Rectifying this issue motivates the introduction of the context restriction operator  \( -\backslash- \)  we have already encountered. We present a formulation of context restriction as an explicit context former characterized as a left adjoint to extension by an interval variable.

\( ^{2} \) We will nevertheless permit ourselves a certain amount of routine syntactic sugar; for one, we will not fully annotate terms.