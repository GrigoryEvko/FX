140

General higher inductive types

# Eliminator

$$\frac{M \longmapsto M'}{\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; M; \mathcal{E}) \longmapsto \operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; M'; \mathcal{E})}$$

$$\frac{(\ell : \Phi.\Omega.[-; \Theta.\overline{\xi_i \hookrightarrow M_i}]) \in \mathcal{K}}{\rho := \overline{\operatorname{act}}(\Theta; \overline{v}_{\delta}.h.\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; h; \mathcal{E}); \chi) \qquad (\ell : \overline{v}_{\Phi}.\overline{v}_{\Omega}.\overline{v}_{\chi}.\overline{v}_{\rho}.T) \in \mathcal{E}}{\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; \operatorname{intro}_{\ell}^{\mathcal{K}}(\phi; \omega; \chi); \mathcal{E}) \longmapsto T[\phi, \omega, \chi, \rho]}$$

$$\frac{F_x := \operatorname{fcoe}_{x.\delta'}^{r \to x}(M)}{\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; \operatorname{fcoe}_{x.\delta'}^{r \to s}(M); \mathcal{E}) \longmapsto \operatorname{coe}_{x.D[\delta',F_x/h]}^{r \to s}(\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta'[r/x]; M; \mathcal{E}))}$$

$$\frac{F_x := \operatorname{fhcom}^{r \to x}(M; \overline{\xi_i \hookrightarrow x.N_i})}{\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; \operatorname{fhcom}^{r \to s}(M; \overline{\xi_i \hookrightarrow x.N_i}); \mathcal{E})} \longmapsto \operatorname{com}_{x.D[\delta',F_x/h]}^{r \to s}(\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; M; \mathcal{E}); \overline{\xi_i \hookrightarrow x.\operatorname{elim}(\overline{v}_{\delta}.h.D; \delta; N_i; \mathcal{E}))}$$

# Action of argument types

$$\frac{\overline{\operatorname{act}}(\Theta.\operatorname{IND}(\delta); \overline{v}_{\delta}.h.T; M) \longmapsto T[\delta, M/a]}{\operatorname{act}(\Theta.(a:A) \to B; \overline{v}_{\Delta}.h.T; M) \longmapsto \lambda a.\operatorname{act}(\Theta.B; \overline{v}_{\Delta}.h.T; Ma)}$$ $$\overline{\operatorname{act}(\Theta.\operatorname{PATH}(x.A, M_0, M_1); \overline{v}_{\Delta}.h.T; M) \longmapsto \lambda^{\frac{1}{2}}x.\operatorname{act}(\Theta.A; \overline{v}_{\Delta}.h.T; Mx)}$$

# Action of argument contexts

$$\overline{\operatorname{act}}(\cdot; \overline{v}_{\Delta}.h.T; \chi) := \cdot$$
$$\overline{\operatorname{act}}((\Theta, a:A); \overline{v}_{\Delta}.h.T; (\chi, M/a)) := (\overline{\operatorname{act}}(\Theta; \overline{v}_{\Delta}.h.T; \chi), \operatorname{act}(\Theta.A; \overline{v}_{\Delta}.h.T; M)/a)$$

Figure 6.7: Operational semantics of the eliminator and action of argument contexts