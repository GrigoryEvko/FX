Then we inductively define:

$$\left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+1}}^{\mathrm{A}} \right)_{\mathrm{m}+1} \equiv \left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n}}^{\pi \mathrm{A}} \right)_{\mathrm{m}+1} \quad \text { for } \quad \mathrm{m}<\mathrm{n}$$

$$\left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+2}}^{\mathrm{A}} \right)_{\mathrm{n}+2} \equiv \left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+1}}^{\pi \mathrm{A}^{\mathrm{p} \mathrm{r}}} \right)_{\mathrm{n}+1} \circ \left( \mathrm{p} \mathrm{t}_{\mathrm{sm}^{n+1}}^{\mathrm{A}^{\mathrm{d}}} \right)_{\mathrm{n}+1}$$

$$\pi\left( \mathrm{zv}_{\mathrm{sm}^{n+2}}^{\mathrm{A}} \right) \equiv \mathrm{zv}_{\mathrm{sm}^{n}}^{\pi \mathrm{A}}$$

$$\left( \mathrm{zv}_{\mathrm{sm}^{n+2}}^{\mathrm{A}} \right)_{\mathrm{n}+2} \equiv \left( \mathrm{zv}_{\mathrm{sm}^{n+1}}^{\mathrm{A}^{\mathrm{d}}} \right)_{\mathrm{n}+1} .$$

This says that the constructions are performed level-wise. From this, theorems eqs. (4.16) and (4.17) then follow inductively, since the hypothesised décalage and display formulas were used to define each successive level.

Are these definitions correct? We gave well typed definitions, but to show that they give a notion of parent maps and zero variables, we have to verify that equations eqs. (4.2) to (4.4) hold. These verification appear in appendix A.1.

### 4.2.6 $\Pi$-Types

We construct $\Pi$-types inductively, with all of the assumptions of a $\Pi$-type structure outlined before assumed at all prior levels. Now note that we have the following two types in the same context:

$$\gamma^{+}: \Gamma^{\mathrm{D}}, f: \left( \Pi^{\mathrm{sm}^{n}} \pi \mathrm{A} \pi \mathrm{B} \right)^{\mathrm{p} \mathrm{r}} \gamma^{+} \vdash_{\mathrm{sm}^{n}} \left( \Pi^{\mathrm{sm}^{n+1}} \mathrm{A} \mathrm{B} \right)^{\mathrm{d}} \gamma^{+} \mathrm{f} \text { type }_{\ell}$$

$$\gamma^{+}: \Gamma^{\mathrm{D}}, f: \left( \Pi^{\mathrm{sm}^{n}} \pi \mathrm{A} \pi \mathrm{B} \right)^{\mathrm{p} \mathrm{r}} \gamma^{+} \vdash_{\mathrm{sm}^{n}}$$

$$\left( a: \pi \mathrm{A}^{\mathrm{p} \mathrm{r}} \gamma^{+} \right)\left( a^{\prime}: \mathrm{A}^{\mathrm{d}} \gamma^{+} a \right) \rightarrow \mathrm{B}^{\mathrm{d}}\left[\gamma^{+}, a, a^{\prime}\right]\left( \operatorname{app}\left[\gamma^{+}, f, a, a^{\prime}\right] f a \right) \text { type }_{\ell} .$$

We will prove inductively along with our definition that these two types are equal. In point-free notation, this means we will have:

$$\left( \Pi^{\mathrm{sm}^{n+1}} \mathrm{A} \mathrm{B} \right)^{\mathrm{d}} \equiv \Pi^{\mathrm{sm}^{n}}\left( \pi \mathrm{A}^{\mathrm{p} \mathrm{r}} \right)^{\mathrm{p} \mathrm{t}} \Pi^{\mathrm{sm}^{n}}\left(\mathrm{A}^{\mathrm{d}}\right)^{\mathrm{W}_{2}^{\pi \mathrm{A}^{\mathrm{p} \mathrm{r}}} \mathrm{p} \mathrm{t}}\left(\mathrm{B}^{\mathrm{d}}\right)^{\left[\mathrm{W}_{2}^{\mathrm{A}^{\mathrm{d}}} \mathrm{W}_{2}^{\pi \mathrm{A}^{\mathrm{p} \mathrm{r}}} \mathrm{p} \mathrm{t}, \operatorname{app} \mathrm{zv}^{\mathrm{p} \mathrm{t} \mathrm{p} \mathrm{t}} \mathrm{zv}^{\mathrm{p} \mathrm{t}}\right]}$$

$$\left( \lambda^{\mathrm{sm}^{n+1}} \mathrm{t} \right)^{\mathrm{d}} \equiv \lambda^{\mathrm{sm}^{n}}\left( \lambda^{\mathrm{sm}^{n}} \mathrm{t}^{\mathrm{d}} \right)$$

$$\left( \operatorname{app}^{\mathrm{sm}^{n+1}} \mathrm{f} \mathrm{s} \right)^{\mathrm{d}} \equiv \operatorname{app}^{\mathrm{sm}^{n}}\left( \operatorname{app}^{\mathrm{sm}^{n}} \mathrm{f}^{\mathrm{d}} \pi \mathrm{s}^{\mathrm{p} \mathrm{r}} \right) \mathrm{s}^{\mathrm{d}} .$$

Now to start on the induction, for $\mathrm{sm}^{-1}$ we define:

$$\left( \Pi^{\mathrm{sm}^{-1}} \mathrm{A} \mathrm{B} \right)_{-1} \equiv \Pi^{\mathrm{dm}} \mathrm{A}_{-1} \mathrm{B}_{-1}$$

$$\left( \lambda^{\mathrm{sm}^{-1}} \mathrm{t} \right)_{-1} \equiv \lambda^{\mathrm{dm}} \mathrm{t}_{-1}$$

$$\left( \operatorname{app}^{\mathrm{sm}^{-1}} \mathrm{f} \mathrm{s} \right)_{-1} \equiv \operatorname{app}^{\mathrm{dm}} \mathrm{f}_{-1} \mathrm{s}_{-1} .$$

59