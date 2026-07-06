We then use the constructions above to construct a modal type former:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} A \gamma \text{ type}_t}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square_{\mathrm{sm}} A \gamma \text{ type}_t}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square_{\mathrm{sm}} t \gamma : \square_{\mathrm{sm}} A \gamma}$$

$$\frac{\gamma_{-1} : \mathbf{\Omega}_{\triangle} \Gamma \vdash_{\mathrm{dm}} t \gamma_{-1} : \square A \gamma_{-1}}{\gamma : \Gamma \vdash_{\mathrm{sm}} \mathbf{\Sigma}_{\mathrm{sm}}^A t \gamma : A \left( \mathbf{\Omega}_{\mathbf{t}}^\triangle \square \leqslant 1_{\mathrm{sm}} \gamma \right)}$$

(Recall from section 4.3.1 that $\mathbf{\Omega}_{\triangle} \Gamma \equiv \Gamma_{-1}$.) In order to form these, we will take an $\omega$-limit of sequences $A_{\square}$ or $t_{\square}$ obtained from the $m$-simplex levels of $A$ or $t$:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} A \gamma \text{ type}_t}{\gamma : \Gamma \vdash_{\mathrm{dm}} A_{\square} \text{ stel}_t^{\infty}}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square} \vdash_{\mathrm{sm}} t \gamma : A \gamma \text{ type}_t}{\gamma : \Gamma \vdash_{\mathrm{dm}} t_{\square} \gamma : A_{\square} \gamma}$$

These are defined as follows:

$$A_{\square}^{\partial(m+1)} \gamma \equiv (\pi_m A)_{\square(m+1)} \gamma$$

$$A_{\square}^{m+1} \gamma \square a \equiv A_{m+1} \gamma \left( \left( zv_{\square_m}^{\pi_m A} \right)_{\partial(m+1)} \gamma \square a \right)$$

$$t_{\square}^{\partial(m+1)} \gamma \equiv (\pi_m t)_{\square(m+1)} \gamma$$

$$t_{\square}^{m+1} \gamma \equiv t_{m+1} \gamma.$$

We then define:

$$\square_{\mathrm{sm}} A \equiv \lim A_{\square}$$

$$\square_{\mathrm{sm}} t \equiv \lim t_{\square}.$$

We define the eliminator by:

$$\pi_{n+1} \left( \mathbf{\Sigma}_{\mathrm{sm}}^A a \right) \gamma_{n+1} \equiv zv_{\square_{n+1}}^{\pi_{n+1} A} \gamma_{n+1}^{\partial^{n+1}} \left[ \text{res}^{\partial(n+1)} \gamma_{n+1}^{\partial^{n+1}} a, \text{res}^{n+1} \gamma_{n+1}^{\partial^{n+1}} a \right].$$

One then checks the computation laws.

◁

### 4.3.3 The Extended Simplicial Model

So far, we have equipped the simplicial model sm with the locks $\mathbf{\Omega}_{\triangle}$ and $\mathbf{\Omega}_{\square}$, modal extension and modal $\Pi$-types for $\triangle$, and a modality $\square_{\mathrm{sm}}$ with Fitch-style introduction and elimination rules. (Because $\square_{\mathrm{sm}}$ satisfies an $\eta$-rule, we could then derive modal extension and modal $\Pi$-types for $\square_{\mathrm{sm}}$ by simply extending and mapping out of $\square_{\mathrm{sm}} A$, as we will do in sections 4.3.6 and 4.3.7 for our eventual model.)

The modality $\diamond$ presents a different problem: in syntax, for $\Gamma \text{ ob}_{\mathrm{dm}}$, the context $(\Gamma, \mathbf{\Omega}_{\diamond})$ is flat. This creates an issue of how we store such contexts semantically. Our solution is to extend the simplicial model constructed in section 4.2 to what we call the extended simplicial model, $\text{sm}_+$, built out of a copy of dm (representing the flat contexts) and the original sm (representing the non-flat contexts). We start with the non-modal aspects of this model.

67