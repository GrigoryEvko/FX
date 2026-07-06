142

General higher inductive types

pendent interpretation of M, written $$(\Theta.M)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$, as follows.

$$(\Theta.a)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := a\rho$$

$$(\Theta.INTRO_{\ell}(\phi;\omega;\theta))_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := T[\phi,\omega,\chi',\rho']$$

$$\text{where } \chi' := (\Theta.\theta)_{\mathcal{K}}(\chi)$$

$$\rho' := (\Theta.\theta)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$

$$(\ell:\bar{v}_{\phi}.\bar{v}_{\omega}.\bar{v}_{\chi'}.\bar{v}_{\rho'}.T) \in \mathcal{E}$$

$$(\Theta.FCOE_{x,\delta}^{r\to s}(M))_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := coe_{x,D[\delta,F_x/h]}^{r\to s}((\Theta.M)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho))$$

$$\text{where } F_x := fcoe_{x,\delta}^{r\to s}((\Theta.M)_{\mathcal{K}}(\chi))$$

$$(\Theta.FHCOM_{\delta}^{r\to s}(M;\overline{\xi_i \hookrightarrow x.N_i}))_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := com_{x,D[\delta,F_x/h]}^{r\to s}(M;\overline{\xi_i \hookrightarrow N_i})$$

$$\text{where } M := (\Theta.M)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$

$$N_i := (\Theta.M)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$

$$F_x := fhcom^{r\to x}((\Theta.M)_{\mathcal{K}}(\chi);\overline{\xi_i \hookrightarrow (\Theta.N_i)_{\mathcal{K}}(\chi)})$$

$$(\Theta.\lambda a.N)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := \lambda a.(\Theta.N)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$

$$(\Theta.FM)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := ((\Theta.F)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho))M$$

$$(\Theta.\lambda^{\dagger}x.M)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := \lambda^{\dagger}x.(\Theta.N)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$

$$(\Theta.Pr)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho) := ((\Theta.P)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho))r$$

We define $$(\Theta.\theta)_{\Delta.h.D}^{\mathcal{K},\mathcal{E}}(\chi;\rho)$$ for argument substitutions $$\theta$$ elementwise.

$$(\Theta.\cdot)_{\Delta.h.D}^{\mathcal{K},\mathcal{E}}(\chi;\rho) := \cdot$$

$$(\Theta.(\theta,M/a))_{\Delta.h.D}^{\mathcal{K},\mathcal{E}}(\chi;\rho) := ((\Theta.\theta)_{\Delta.h.D}^{\mathcal{K},\mathcal{E}}(\chi;\rho),(\Theta.M)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)/a)$$

**Definition 6.4.2 (Dependent interpretation of types).** Let $$\Delta$$ be a telescope and $$\Delta.h.D$$ be a type, $$\mathcal{K}$$ and $$\mathcal{E}$$ be constructor and eliminator specifications, and let A be an argument type in context $$\Theta$$. Let $$\chi$$ and $$\rho$$ be instantiations for the variables in $$\Theta$$ and let M be a term. We define the dependent interpretation of A, written $$(\Theta.A)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho;M)$$, as follows.

$$(\Theta.IND(\delta))_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho;M) := D[\delta,M/h]$$

$$(\Theta.(a:A) \to B)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho;M) := (a:A) \to (\Theta.B)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho;Ma)$$

$$(\Theta.PATH(x.A,M_0,M_1))_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho;M) := Path(x.(A)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho;Mx),M_0',M_1')$$

$$\text{where } M'_\varepsilon := (\Theta.M_0)_{\mathcal{K},\mathcal{E}}^{\Delta.h.D}(\chi;\rho)$$