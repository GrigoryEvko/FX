7.

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad \Gamma \vdash t_1 \equiv_{A_1} t_2}{\Gamma \vdash t_2 \equiv_{A_2} t_1}$$

8.

$$\frac{\Gamma \vdash A_1 \equiv A_2 \quad \Gamma \vdash t : A_1}{\Gamma \vdash t : A_2}$$

9.

$$\frac{\Gamma, \{x_\delta : A_\delta\}_{\delta < \beta < \lambda} \vdash A_\beta \text{ Type}}{\Gamma, \{x_\alpha : A_\alpha\}_{\alpha < \lambda} \vdash x_\alpha : A_\alpha}$$

10. For any $B$ sort symbol with a well-formed introduction type judgment:

$$\frac{\{x_\alpha : A_\alpha\}_{\alpha < \lambda} \vdash B(x_\lambda) \text{ Type}, \quad \vdash \Gamma \text{ Ctxt}, \quad \Gamma \vdash t_\alpha : B[t_\alpha | x_\alpha]}{\Gamma \vdash B(t_\lambda) \text{ Type}}$$

11. For any $F$ operator symbol with a well-formed introduction type element judgment:

$$\frac{\Gamma, \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash F(x_\lambda) : \Delta, \quad \Gamma \vdash t_\alpha : \Delta_\alpha[t_\alpha | x_\alpha]}{\Gamma, \{t_\alpha : \Delta_\alpha[t_\alpha | x_\alpha]\}_{\alpha < \lambda} \vdash F(t_\lambda) : \Delta[t_\lambda | x_\lambda]}$$

12.

$$\begin{array}{c} \vdash \Gamma \text{ Ctxt} \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta' \\ \Gamma, t_\alpha : \Delta_\alpha[t_\beta | x_\beta]_{\beta < \alpha}, t'_\alpha : \Delta'_\alpha[t'_\beta | x_\beta]_{\beta < \alpha} \vdash t_\alpha \equiv_{\Delta_\alpha[t_\beta | x_\beta]_{\beta < \alpha}} t'_\alpha \\ \hline \Gamma, \{t_\alpha : \Delta_\alpha[t_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda}, \{t'_\alpha : \Delta'_\alpha[t'_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda} \\ \vdash \Delta[t_\alpha | x_\alpha]_{\alpha < \lambda} \equiv \Delta'[t'_\alpha | x_\alpha]_{\alpha < \lambda} \end{array}$$

13.

$$\begin{array}{c} \vdash \Gamma \text{ Ctxt} \quad \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t' \\ \Gamma, s_\alpha : \Delta_\alpha[s_\beta | x_\beta]_{\beta < \alpha}, s'_\alpha : \Delta_\alpha[s'_\beta | x_\beta]_{\beta < \alpha} \vdash s_\alpha \equiv_{\Delta_\alpha[s'_\beta | x_\beta]_{\beta < \alpha}} s'_\alpha \\ \hline \Gamma, \{s_\alpha : \Delta_\alpha[s_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda}, \{s'_\alpha : \Delta_\alpha[s'_\beta | x_\beta]_{\beta < \alpha}\}_{\alpha < \lambda} \\ \vdash t[s_\alpha | x_\alpha]_{\alpha < \lambda} \equiv_{\Delta[s_\alpha | x_\alpha]_{\alpha < \lambda}} t'[s'_\alpha | x_\alpha]_{\alpha < \lambda} \end{array}$$

94