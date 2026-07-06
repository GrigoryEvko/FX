for $\gamma < \beta$. For $\beta < \alpha$, define $x_{\beta < \alpha} : SX_\beta \rightarrow X_\alpha$ to be the composite

$$SX_\beta \xrightarrow{S\theta_\beta^\alpha} SX_\beta^\alpha \xrightarrow{v_\beta} X_\alpha. \quad (2.3)$$

We check that $(X, x)$ is a S-algebraized $\kappa$-chain. For 2.2.3(a), that $x_{\beta < \alpha} \circ \sigma_{X_\beta} = X_{\beta \leq \alpha}$, first observe that for $\beta < \alpha$ the diagram

$$\begin{array}{ccc} & X_\beta^\alpha & \xrightarrow{\sigma_{X_\beta^\alpha}} SX_\beta^\alpha \\ \theta_\beta^\alpha & & \searrow v_\alpha \\ X_\beta & \xrightarrow{X_{\beta \leq \alpha}} & X_\alpha \end{array} \quad (2.4)$$

commutes by probing with $v_\gamma : SX_\gamma^\beta \rightarrow X_\beta$ for $\gamma < \beta$: we have

$$\begin{aligned} v_\alpha \circ \sigma_{X_\beta^\alpha} \circ \theta_\beta^\alpha \circ v_\gamma &= v_\alpha \circ \sigma_{X_\beta^\alpha} \circ x_{\gamma < \beta}^\alpha \circ SX_\gamma^{\beta \leq \alpha} \\ &= v_\alpha \circ Sx_{\gamma < \beta}^\alpha \circ \sigma_{SX_\gamma^\alpha} \circ SX_\gamma^{\beta \leq \alpha} \\ &= v_\alpha \circ Sx_{\gamma < \beta}^\alpha \circ S\sigma_{X_\gamma^\alpha} \circ SX_\gamma^{\beta \leq \alpha} \quad \text{(well-pointedness)} \\ &= v_\alpha \circ SX_{\gamma \leq \beta}^\alpha \circ SX_\gamma^{\beta \leq \alpha} \\ &= v_\gamma \circ SX_\gamma^{\beta \leq \alpha} \\ &= X_{\beta \leq \alpha} \circ v_\gamma. \end{aligned}$$

It follows that $x_{\beta < \alpha} \circ \sigma_{X_\beta} = v_\beta \circ S\theta_\beta^\alpha \circ \sigma_{X_\beta} = v_\beta \circ \sigma_{X_\beta^\alpha} \circ \theta_\beta^\alpha = X_{\beta \leq \alpha}$.

For 2.2.3(b), let $\beta < \alpha < \kappa$ and $\beta' < \alpha' < \kappa$ with $\beta \leq \beta'$ and $\alpha \leq \alpha'$. We can check that the diagram

$$\begin{array}{ccc} X_\beta & \xrightarrow{X_{\beta \leq \beta'}} & X_{\beta'} \\ \theta_\beta^\alpha & & \downarrow \theta_{\beta'}^\alpha \\ X_\beta^\alpha & \xrightarrow{X_{\beta}^{\alpha \leq \alpha'}} & X_{\beta}^{\alpha'} \xrightarrow{X_{\beta \leq \beta'}^{\alpha'}} & X_{\beta'}^{\alpha'} \end{array}$$

commutes by probing with $v_\gamma : SX_\gamma^\beta \rightarrow X_\beta$ for all $\gamma < \beta$. From this it follows that

$$\begin{array}{ccc} & SX_\beta & \xrightarrow{SX_{\beta \leq \beta'}} & SX_{\beta'} \\ x_{\beta < \alpha} & \downarrow & & \downarrow S\theta_{\beta'}^\alpha \\ & SX_\beta^\alpha & \xrightarrow{SX_{\beta}^{\alpha \leq \alpha'}} & SX_{\beta}^{\alpha'} \xrightarrow{SX_{\beta \leq \beta'}^{\alpha'}} & SX_{\beta'}^{\alpha'} \\ & v_\beta & & \downarrow v_\beta \\ & X_\alpha & \xrightarrow{X_{\alpha \leq \alpha'}} & X_{\alpha'} \end{array} \begin{array}{c} \downarrow \\ \downarrow \\ \downarrow \\ X_{\alpha'} \end{array} \begin{array}{c} \downarrow \\ \downarrow \\ \downarrow \\ X_{\beta' < \alpha'} \end{array}$$

commutes.

Finally, to see that $(X, x)$ is colimiting, observe that each $\theta_\beta^\alpha$ is an isomorphism, with inverse $X_\beta^\alpha \rightarrow X_\beta$ induced by the cocone $(v_\gamma \circ S(X_{\gamma}^{\alpha \leq \alpha'})^{-1} : SX_\gamma^\alpha \rightarrow X_\beta)_{\gamma < \beta}$, and these assemble to a natural isomorphism $\theta^\alpha : X \mid \alpha \simeq X^\alpha$. It thus follows from the definition (2.3) of $x$ that the cocones $(x_{\gamma < \beta})_{\gamma < \beta}$ are colimiting for all $\beta < \alpha$. $\square$

The combination of Proposition 2.2.9 and Lemma 2.2.10 would immediately give us initial algebras, *i.e.*, free algebras on initial objects. To construct free algebras on arbitrary objects, we pass to a coslice.

14