Note that by definition the left vertical morphism is also display. If there is another commutative square

$$\begin{array}{c} [\{x_{\zeta}:\Gamma_{\zeta}\}_{\zeta<\xi}] \xrightarrow{[\langle g_{\beta}\rangle_{\beta<\mu+1}]} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\mu+1}] \\ [\langle f_{\alpha}\rangle_{\alpha<\lambda}] \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [\{x_{\alpha}:\Delta_{\alpha}\}_{\alpha<\lambda}] \xrightarrow{[\langle t_{\beta}\rangle_{\beta<\mu}]} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\mu}], \end{array}$$

the map

$$[\langle f_{\alpha},g_{\mu}\rangle_{\alpha<\lambda}]:[\{x_{\zeta}:\Gamma_{\zeta}\}_{\zeta<\xi}] \to [\{x_{\alpha}:\Delta_{\alpha}, x_{\mu}:\Omega_{\mu}[t_{\beta} \mid x_{\beta}]_{\beta<\mu}\}_{\alpha<\lambda}]$$

shows that the square (2) is the pullback.

Next, assume that we have a diagram

$$\begin{array}{c} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\mu}] \\ \Big\downarrow [\langle x_{\beta}\rangle_{\beta<\mu}] \\ [\{x_{\alpha}:\Delta_{\alpha}\}_{\alpha<\lambda}] \xrightarrow{[\langle t_{\beta}\rangle_{\beta<\nu}]} [\{x_{\beta}:\Omega_{\beta}\}_{\beta<\nu}] \end{array}$$

where $\mu$ is a limit ordinal and $\mu > \nu$. We simplify the notation as follows:

$$\begin{array}{c} B_{\mu} \\ \Big\downarrow \\ A_{\lambda} \xrightarrow[\langle t_{\beta}\rangle_{\beta<\nu}]{} B_{\nu} \end{array}$$

Assume that the factorization of the map $B_{\mu} \twoheadrightarrow B_{\nu}$ is of the form

$$\dots \twoheadrightarrow B_{\nu+2} \twoheadrightarrow B_{\nu+1} \twoheadrightarrow B_{\nu}$$

and therefore $B_{\mu}$ is the limit (obtained similarly as in theorem A.34 and theorem A.32). Then we can take the successive pullback

$$\begin{array}{c} f^{*}B_{\mu} \xrightarrow{q(f,B_{\mu})} B_{\mu} \\ \vdots \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ q(f,B_{\nu+1})^{*}B_{\nu+2} \xrightarrow{q(q(f,B_{\nu+1}),B_{\nu+2})} B_{\nu+2} \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ f^{*}B_{\nu+1} \xrightarrow{q(f,B_{\nu+1})} B_{\nu+1} \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A_{\lambda} \xrightarrow{f} B_{\nu} \end{array} \tag{3}$$

108