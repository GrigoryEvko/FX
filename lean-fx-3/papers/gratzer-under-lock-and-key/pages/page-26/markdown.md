$$\operatorname{CASE}(\Gamma, x : (\mu \mid A), \Delta \vdash \operatorname{let}_{\rho} \operatorname{mod}_{\xi}(y_A) \leftarrow N_0 \text{ in } N_1 : B @ b).$$

Suppose $\rho : a \rightarrow b$. We then know that for some $C$

$$\begin{array}{l} \Gamma, x : (\mu \mid A), \Delta, \widehat{\bullet}_{\rho} \vdash N_0 : \langle \xi \mid C \rangle @ a \\ \Gamma, x : (\mu \mid A), \Delta, y : (\rho \circ \xi \mid C) \vdash N_1 : B @ b \end{array}$$

We deduce by the IH that

$$\begin{array}{l} \Gamma, \Delta, \widehat{\bullet}_{\rho} \vdash N_0[\Gamma; M/x] : \langle \xi \mid C \rangle @ a \\ \Gamma, \Delta, y : (\rho \circ \xi \mid C) \vdash N_1[\Gamma; M/x] : B @ b \end{array}$$

and hence

$$\Gamma, \Delta \vdash \operatorname{let}_{\rho} \operatorname{mod}_{\xi}(y_A) \leftarrow N_0[\Gamma; M/x] \text{ in } N_1[\Gamma; M/x] : B @ b$$

which is just $(\operatorname{let}_{\rho} \operatorname{mod}_{\xi}(y_A) \leftarrow N_0 \text{ in } N_1)[\Gamma; M/x]$.

**Equational theory** With the preceding metatheorems in hand we are now able to formulate an *equational theory of terms* for this system. The equational theory specifies a minimal set of equations between *proofs* of a certain formula/type. In particular, the cut elimination theorem suggests the following two $\beta$-rules:

$$\frac{\mu : n \rightarrow m \quad \Gamma, x : (\mu \mid A) \vdash M : B @ m \quad \Gamma, \widehat{\bullet}_{\mu} \vdash N : A @ n}{\Gamma \vdash (\lambda x : (\mu \mid A). M)(N)_{\mu} = M[\Gamma; N/x] : B @ m}$$

$$\frac{\mu : n \rightarrow m \quad \nu : o \rightarrow n \quad \Gamma, \widehat{\bullet}_{\mu}, \widehat{\bullet}_{\nu} \vdash M : A @ o \quad \Gamma, x : (\mu \circ \nu \mid A) \vdash N : B @ m}{\Gamma \vdash \operatorname{let}_{\mu} \operatorname{mod}_{\nu}(x_A) \leftarrow \operatorname{mod}_{\nu}(M) \text{ in } N = N[\Gamma; M/x] : B @ m}$$

A very similar equational theory was developed by Gratzer, Kavvos, Nuyts, and Birkedal [Gra+20; Gra+21], but for an algebraically-specified system of dependent types.

Finally, we could also make these equations *directed*, and consider them as *reductions* from one term to another. That way we could see this system as a programming language that is equipped with an *operational semantics*.

## 6. RELATED WORK

Multimode logics were inspired by the decomposition of the ! modality of Linear Logic [Gir87] into two adjoint functors/modalities. This was used by Benton [Ben95] to present Linear Logic through the LNL (linear-non-linear) calculus, which had two modes, linear and intuitionistic. Many years later this pattern was used by [Ree09] in an unpublished manuscript which presented *adjoint logic*, the first multimode and multimodal logic. The modes and modalities of the Reed's logic were presented through a mode theory that was a pre-order; in our terminology this means that the 2-category had no transformations,

26