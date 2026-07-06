Proof. Consider a diagram \((A,B,f)\colon (1 + \alpha ,\preceq)\to \mathcal{E}^{\mathfrak{g}}\) given by functors \(A,B\colon (1 + \alpha ,\preceq)\to \mathcal{E}\) factoring through \(\mathcal{M}\) and a natural transformation \(f\colon TA\to B\) such that \(f\circ \tau A\) has components in \(\mathcal{M}\). We will show that the colimit \((X,Y,k)\coloneqq \mathrm{colim}_{1 + \alpha}(A,B,f)\) exists in \(T\downarrow \mathcal{E}\) and lifts to \(\mathcal{E}^{\mathfrak{g}}\). By Lemma 2.3.7 and 2.3.6(a), the colimits of \(A,B,TA\) exist and have coprojections in \(\mathcal{M}\). We take \(X = \mathrm{colim}_{1 + \alpha}A\) and compute \(Y\) and \(k\) via the following pushout:

\[
\begin{array}{c} \operatorname{colim} _ {1 + \alpha} A \xrightarrow {\operatorname{colim} _ {1 + \alpha} \tau A} \operatorname{colim} _ {1 + \alpha} T A \xrightarrow {\operatorname{colim} _ {1 + \alpha} f} \operatorname{colim} _ {1 + \alpha} B \\ \tau \operatorname{colim} _ {1 + \alpha} A \xrightarrow {} T \operatorname{colim} _ {1 + \alpha} A \xrightarrow {k} Y. \end{array} \tag {2.13}
\]

Again by Lemma 2.3.7 and 2.3.6(a), the middle vertical map is in \(\mathcal{M}\). By 2.3.6(a), the pushout exists and the rightmost vertical map is in \(\mathcal{M}\). Thus the colimit \((X,Y,k)\) exists in \(T\downarrow \mathcal{E}\). By 2.3.6(a), the composite top row is in \(\mathcal{M}\). The composite \(X\xrightarrow{\tau_X} TX\xrightarrow{k} Y\) thus factors as a sequence \(\mathrm{colim}_{1 + \alpha}A\to \mathrm{colim}_{1 + \alpha}B\to Y\) of maps in \(\mathcal{M}\), so is itself in \(\mathcal{M}\). Thus the colimit lifts to \(\mathcal{E}^{\mathfrak{g}}\).

Lemma 2.3.23. For any \((\mathcal{E},\mathcal{M},\mathsf{T})\in \mathrm{ConfMnd}_{\mathrm{p}}^{\kappa}\) and \(\mathsf{T}^{\mathfrak{g}}\)-algebraized \(\kappa\)-chain \((X,x)\) such that \(X\) and \(x\) factor through \(\mathcal{M}^{\mathfrak{g}}\), \(X\) admits a colimit in \(\mathcal{E}^{\mathfrak{g}}\).

Proof. Write \( X = (A, B, f) \colon (\kappa, \preceq) \to \mathcal{E}^{\mathfrak{g}} \). Our colimit is \( (X, Y, k) \) where \( X = \operatorname{colim}_{\kappa} A \), \( Y = \operatorname{colim}_{\kappa} B \), and \( k \) is the composite

\[
T \operatorname{colim} _ {\kappa} A \xrightarrow {\cong} \operatorname{colim} _ {\kappa} T A \xrightarrow {\operatorname{colim} _ {\kappa} f} \operatorname{colim} _ {\kappa} B.
\]

To check that \(k\tau_{X}\) is in \(\mathcal{M}\), observe that Definition 2.3.12 gives us a \(\mathsf{Tgt}_{\mathcal{E}}\)-algebraized \(\kappa\)-chain \(\tau^{!}(X,x)\) in \(\mathcal{E}_{\mathcal{M}}^{\rightarrow}\), which we can also see as a \(\mathsf{Tgt}_{\mathcal{E}}\)-algebraized \(\kappa\)-chain in \(\mathcal{E}^{\rightarrow}\). This chain has a colimit in \(\mathcal{E}^{\rightarrow}\), namely \(\operatorname{colim}_{\alpha < \kappa}f_{\alpha}\tau_{A_{\alpha}}\), which is isomorphic to \(k\tau_{X}\). Since \(\mathsf{Tgt}_{\mathcal{E}}\) preserves this colimit, it follows from Lemma 2.2.8 that the colimit is a \(\mathsf{Tgt}_{\mathcal{E}}\)-algebra, i.e., an isomorphism. Hence \(k\tau_{X}\) is an isomorphism and in particular belongs to \(\mathcal{M}\).

Corollary 2.3.24. For any \((\mathcal{E},\mathcal{M},\mathsf{T})\in \mathrm{ConfMnd}_{\mathrm{p}}^{\kappa}\), we have \((\mathcal{E}^{\mathfrak{g}},\mathcal{M}^{\mathfrak{g}},\mathsf{T}^{\mathfrak{g}})\in \mathrm{ConfMnd}_{\mathrm{wp}}^{\kappa}\).

Proof. Condition 2.2.6(a) is part of Lemma 2.3.20 and condition 2.2.6(b) is Lemma 2.3.22. Condition 2.2.6(c) follows from Lemma 2.3.23, 2.3.6(d), and commutativity of colimits. \(\square\)

Lemma 2.3.25. The assignment of Corollary 2.3.24 extends to a functor \(\mathrm{ConfMnd}_{\mathrm{p}}^{\kappa} \to \mathrm{ConfMnd}_{\mathrm{wp}}^{\kappa}\).

Proof. Let \((F,\gamma)\colon (\mathcal{E}_1,\mathcal{M}_1,\mathsf{T}_1)\to (\mathcal{E}_2,\mathcal{M}_2,\mathsf{T}_2)\) be a morphism in \(\mathrm{ConfMnd}_{\mathrm{p}}^{\kappa}\). To see that \(F\) lifts to a functor \(F^{\mathfrak{g}}\colon \mathcal{E}_1^{\mathfrak{g}}\to \mathcal{E}_2^{\mathfrak{g}}\), we examine the pullback square (2.8) defining \(\mathcal{E}_1^{\mathfrak{g}}\) and \(\mathcal{E}_2^{\mathfrak{g}}\). Since \((F,\gamma)\) is a map of pointed endofunctors, we have an isomorphism

\[
\begin{array}{c} T _ {1} \downarrow \mathcal {E} _ {1} \xrightarrow {\tau_ {1} ^ {!}} \mathcal {E} _ {1} ^ {\rightarrow} \\ \Biggl \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ T _ {2} \downarrow \mathcal {E} _ {2} \xrightarrow {\tau_ {2} ^ {!}} \mathcal {E} _ {2} ^ {\rightarrow}. \end{array}
\]

where the left vertical functor sends \((A,B,f\colon T_1A\to B)\) to \((FA,FB,Ff\circ \gamma_A^{-1}\colon T_2FA\to FB)\). By assumption, \(F^{\rightarrow}\colon \mathcal{E}_1^{\rightarrow}\to \mathcal{E}_2^{\rightarrow}\) restricts to a functor \((\mathcal{E}_1)_{\mathcal{M}_1}\to (\mathcal{E}_2)_{\mathcal{M}_2}\). Together, these induce the lift \(F^{\mathfrak{g}}\colon \mathcal{E}_1^{\mathfrak{g}}\to \mathcal{E}_2^{\mathfrak{g}}\). Note that \(F^{\mathfrak{g}}\) maps \(\mathcal{M}_1^{\mathfrak{g}}\) to \(\mathcal{M}_2^{\mathfrak{g}}\), since \(F\) maps \(\mathcal{M}_1\) to \(\mathcal{M}_2\).

To extend \( F^{\mathfrak{g}} \) to a morphism \( (\mathcal{E}_1, \mathsf{T}_1^{\mathfrak{g}}) \to (\mathcal{E}_2, \mathsf{T}_2^{\mathfrak{g}}) \) in PtdEndo, we use the functoriality of transfer (Proposition 2.3.13). Clearly \( F^{\rightarrow} \colon (\mathcal{E}_1)_{\mathcal{M}_1} \to (\mathcal{E}_2)_{\mathcal{M}_2} \) defines a strong morphism of pointed endofunctors from \( \mathsf{Tgt}_{\mathcal{E}_1} \) to \( \mathsf{Tgt}_{\mathcal{E}_2} \). Using that \( F \) preserves the pushout (2.7) defining

22