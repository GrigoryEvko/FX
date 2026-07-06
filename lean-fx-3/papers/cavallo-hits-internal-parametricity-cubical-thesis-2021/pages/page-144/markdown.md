132

General higher inductive types

### Coercion along telescopes

$$\overline{\mathrm{coe}}_{x\cdot}^{r\to s}(\cdot):=\cdot$$

$$\overline{\mathrm{coe}}_{x\cdot(\Omega,a:A)}^{r\to s}(\omega,M/a):=(\overline{\mathrm{coe}}_{x\cdot\Omega}^{r\to s}(\omega),\mathrm{coe}_{x\cdot A[\overline{\mathrm{coe}}_{x\cdot\Omega}^{r\to s}(\omega)]}^{r\to s}(M)/a)$$

### Parameter coercion

$$\frac{M\longmapsto M'}{\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(M)\longmapsto\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(M')}$$

$$(\ell:\Phi.\Omega.[\delta;\Theta.\overline{\xi_i\hookrightarrow M_i}])\in\mathcal{K}$$

$$(\nexists i)\xi_i\text{ satisfied}\quad(\forall t)\omega^t:=\overline{\mathrm{coe}}_{x\cdot\omega\phi}^{r\to t}(\omega)\quad(\forall t)\chi^t:=\overline{\mathrm{coe}}_{x\cdot(\Theta[\phi,\omega^x])_\mathcal{K}}^{r\to t}(\chi)$$

$$(\forall i)M_i^x:=\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{x\to s}(\|\Theta.\mathrm{M}_k[\phi,\omega^x]\|_\mathcal{K}(\chi^x))\quad\delta^x:=\overline{\mathrm{coe}}_{x\cdot\Delta}^{x\to s}(\delta\omega^x)$$

$$\frac{\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(\mathrm{intro}_{\ell}^{\mathcal{K}^s}(\phi;\omega;\chi))\longmapsto\mathrm{fcom}_{x\cdot\delta^s}^{s\to t}(\mathrm{intro}_{\ell}^{\mathcal{K}[s/x]}(\phi;\omega^s;\chi^s);\overline{\xi_i\phi\hookrightarrow x\cdot M_i^x})}{}$$

$$t\neq u\quad(\nexists i)\xi_i\text{ satisfied}$$

$$\frac{\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(\mathrm{fhcom}^{t\to u}(M;\overline{\xi_i\hookrightarrow y\cdot N_i}))}{\longmapsto}$$

$$\longmapsto$$

$$\mathrm{fhcom}^{t\to u}(\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(M);\overline{\xi_i\hookrightarrow y\cdot\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(N_i)})$$

$$t\neq u$$

$$\frac{\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(\mathrm{fcoe}_{y\cdot\delta}^{t\to u}(M))\longmapsto\mathrm{fcoe}_{y\cdot\mathrm{coe}_{x\cdot\Delta}^{r\to s}(\delta)}^{t\to u}(\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(M))}{}$$

### Coercion

$$\overline{\mathrm{coe}}_{x\cdot\mathrm{Ind}_\mathcal{K}^\Delta(\delta)}^{r\to s}(M)\longmapsto\mathrm{fcoe}_{x\cdot\overline{\mathrm{coe}}_{x\cdot\Delta}^{x\to s}(\delta)}^{r\to s}(\mathrm{pcoe}_{x\cdot\Delta\blacktriangleright x\cdot\mathcal{K}}^{r\to s}(M))$$

### Composition

$$\overline{\mathrm{hcom}}_{\mathrm{Ind}_\mathcal{K}^\Delta(\delta)}^{r\to s}(M;\overline{\xi_i\hookrightarrow x\cdot N_i})\longmapsto\mathrm{fhcom}^{r\to s}(M;\overline{\xi_i\hookrightarrow x\cdot N_i})$$

Figure 6.6: Operational semantics of coercion and composition in HITs