Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:39

\(\triangleright \Gamma \gg (\gamma, r / x) = (\gamma, r' / x) \in (\Gamma, x : \mathbb{I})\) when \(\Gamma \gg \gamma = \gamma' \in \Gamma\) and \(\Gamma \gg r = r' \in \mathbb{I}\).  
\(\triangleright \Gamma \gg (\gamma, r / x) = (\gamma, r' / x) \in (\Gamma, x : \mathbf{I})\) when \(\Gamma \gg r = r' \in \mathbf{I}\) and \(\Gamma \backslash r \Vdash \gamma = \gamma' \in \Gamma\).  
\(\triangleright \Gamma \gg \gamma = \gamma' \in (\Gamma, \xi)\) when \(\Gamma \gg \gamma = \gamma' \in \Gamma\) and \(\xi \gamma\) is true.

Now that we have laid out the extrapolation of open judgments from a value type system, it remains to construct a particular type system that will validate the inference rules we presented in Sections 1 and 2.

4.4. Constructing a value type system. We obtain a value type system by a fixed-point construction, first defining the least candidate value type system closed under our desired type formers and then showing that it constitutes a value type system. To start, we define the pieces corresponding to each type former. Relative to [Ang19], the novelties here are the Bridge- and Gel-types.

\(\begin{array}{rl} & {\mathrm{BRIDGE}(\tau):=}\\ & {\left\{(\Psi ,\mathrm{Bridge}_{\pmb{x},A}(M_0,M_1),\mathrm{Bridge}_{\pmb{x},A'}(M_0',M_1'),\varphi)\mid \right.}\\ & {\quad \exists \alpha .\Psi ,\pmb {x}:\mathbf{I}\Vdash A\sim A^{\prime}\downarrow \alpha \in \tau \wedge \mathrm{Coh}(\alpha)}\\ & {\quad \wedge (\forall \varepsilon \in \{0,1\} .\Psi \Vdash M_{\varepsilon}\sim M_{\varepsilon}^{\prime}\in \alpha [\pmb {\varepsilon} / \pmb {x}])}\\ & {\quad \wedge \varphi = \left\{(\lambda^{\mathbf{I}}\pmb {x}.M,\lambda^{\mathbf{I}}\pmb {x}.M^{\prime})\mid \Psi ,\pmb {x}:\mathbf{I}\Vdash M\sim M^{\prime}\in \alpha \wedge \forall \varepsilon .\Psi \Vdash M[\pmb {\varepsilon} / \pmb {x}]\sim M_{\varepsilon}\in \alpha [\pmb {\varepsilon} / \pmb {x}]\right\} \right\}}\\ & {\mathrm{GEL}(\tau):=}\\ & {\left\{(\Psi ,\mathrm{Gel}_{\pmb{x}}(A_{0},A_{1},a_{0}.a_{1}.R),\mathrm{Gel}_{\pmb{x}}(A_{0}',A_{1}',a_{0}.a_{1}.R'),\varphi)\mid \right.}\\ & {\quad \exists \alpha^{0},\alpha^{1},\beta^{(-,-,-,-,-)}.}\\ & {(\forall \varepsilon .\Psi \backslash \pmb {x}\Vdash A_{\varepsilon}\sim A_{\varepsilon}^{\prime}\downarrow \alpha \in \tau \wedge \mathrm{Coh}(\alpha^{\varepsilon}))}\\ & {\quad \wedge (\forall \Psi^{\prime}\Vdash \psi \in (\Psi \backslash \pmb {x}).\forall M_{0},M_{1},M_{0}^{\prime},M_{1}^{\prime}.(\forall \varepsilon .\alpha_{\psi}^{\varepsilon}(M_{\varepsilon},M_{\varepsilon}^{\prime}))\implies \\ & {\quad \Psi^{\prime}\Vdash R[M_{0},M_{1}/a_{0},a_{1}]\sim R^{\prime}[M_{0}^{\prime},M_{1}^{\prime}/a_{0},a_{1}]\downarrow \beta^{(\psi ,M_{0},M_{1},M_{0}^{\prime},M_{1}^{\prime})}\in \tau}\\ & {\quad \wedge \mathrm{Coh}(\beta^{(\psi ,M_{0},M_{1},M_{0}^{\prime},M_{1}^{\prime})}))}\\ & {\quad \wedge \varphi = \left\{(\mathrm{gel}_{\pmb{x}}(M_{0},M_{1},P),\mathrm{gel}_{\pmb{x}}(M_{0}^{\prime},M_{1}^{\prime},P^{\prime}))\mid \\ & {\quad \forall \varepsilon .(\Psi \backslash \pmb {x}\Vdash M_{\varepsilon}\sim M_{\varepsilon}^{\prime}\in \alpha^{\varepsilon})\wedge \Psi \backslash \pmb {x}\Vdash P\sim P^{\prime}\in \beta^{(\mathrm{id},M_0,M_1,M_0',M_1')} \right\} \right\}} \end{array}\)

Next, we have an operator on candidate value type systems that applies one level of type formers.

\[
K (\tau) := \operatorname{BRIDGE} (\tau) \cup \operatorname{GEL} (\tau) \cup \dots
\]

Finally, we obtain a least fixed-point  \( \tau_{0} \)  of this operator by the Knaster-Tarski fixed-point theorem [DP02, 2.35]. It is tedious but straightforward to check that this candidate value type system is in fact a value type system [Ang19, Lemma 4.8]. To construct a value type system with a universe, we can repeat the fixed-point construction with the addition of a type U interpreted by the relation  \( \tau_{0} \) , producing a new type system  \( \tau_{1} \)  that is closed under the same type formers as  \( \tau_{0} \)  but also contains  \( \tau_{0} \)  as a universe. This can be repeated further to produce a hierarchy of value type systems  \( \tau_{0} \subseteq \tau_{1} \subseteq \tau_{2} \subseteq \cdots \)  each containing its predecessors as universes; for our purposes, a single universe is sufficient.

As an immediate consequence of the way the typing judgments are defined, we have a canonicity theorem: any closed well-typed term is guaranteed to evaluate to a value of that type. In particular, any closed term of natural number type evaluates to a numeral.