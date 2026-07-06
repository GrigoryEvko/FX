For the zero variables for $\diamondsuit_{+}$ and $\square_{+}$, one checks that the following are well-typed:

$$z v_{\diamondsuit_{+}}^{A} \equiv \diamondsuit^{A} z v_{d m}^{\diamondsuit A}$$

$$z v_{\square_{+}}^{A} \equiv \blacksquare^{A} z v_{d m}^{\square A}.$$

For the zero variables $z v_{\triangle_{+}}^{A}$, we once again case split:

$$z v_{\triangle_{+}}^{A} \equiv \begin{cases} z v_{d m}^{A} & \text{for } \text{in}_{d m} \Gamma \\ z v_{\triangle}^{A} & \text{for } \text{in}_{s m} \Gamma. \end{cases}$$

Then, for $\diamondsuit_{+}$ and $\triangle \square_{+}$, we use $z v_{\triangle_{+}}$:

$$z v_{\diamondsuit \diamondsuit_{+}}^{A} \equiv \diamondsuit^{A} z v_{\triangle_{+}}^{\diamondsuit A}$$

$$z v_{\triangle \square_{+}}^{A} \equiv \blacksquare^{A} z v_{\triangle_{+}}^{\square A}.$$

### 4.3.7 Modal $\Pi$-Types

The last remaining modal construct that we must address is modal $\Pi$-types. These behave according to the following rules:

$$\frac{\mu : p \to q \quad \gamma : \Gamma, \widehat{\blacksquare}_{\mu}^{+} \vdash_{[p]} A \gamma \text{ type}_{\ell_0} \quad \gamma : \Gamma, a :^{\mu_{+}} A \gamma \vdash_{[q]} B \gamma a \text{ type}_{\ell_1}}{\gamma : \Gamma \vdash_{[q]} \Pi_{\mu}^{s m_{+}} A B \gamma \text{ type}_{\ell_0 \sqcup \ell_1}}$$

$$\frac{\gamma : \Gamma, a :^{\mu_{+}} A \gamma \vdash_{[q]} t \gamma a : B \gamma a}{\gamma : \Gamma \vdash_{[q]} \lambda_{\mu}^{s m_{+}} t \gamma : \Pi_{\mu}^{s m_{+}} A B \gamma}$$

$$\frac{\gamma : \Gamma \vdash_{[q]} f \gamma : \Pi_{\mu}^{s m_{+}} A B \gamma \quad \gamma : \Gamma, \widehat{\blacksquare}_{\mu}^{+} \vdash_{[p]} s \gamma : A \gamma}{\gamma : \Gamma \vdash_{[q]} \text{app}_{\mu}^{s m_{+}} f s \gamma : B^{\lceil \lceil \Gamma, s \rceil_{\mu}} \gamma}$$

For $\triangle_{+}$ we define:

$$\Pi_{\triangle}^{s m_{+}} A \text{ (in}_{s m} B) \equiv \text{in}_{s m} \left( \Pi_{\triangle}^{s m} A B \right)$$

$$\Pi_{\triangle}^{s m_{+}} A \text{ (in}_{d m} B) \equiv \text{in}_{d m} \left( \Pi^{d m} A B \right)$$

$$\lambda_{\triangle}^{s m_{+}} \text{ (in}_{s m} t) \equiv \text{in}_{s m} \left( \lambda_{\triangle}^{s m} t \right)$$

$$\lambda_{\triangle}^{s m_{+}} \text{ (in}_{d m} t) \equiv \text{in}_{d m} \left( \lambda^{d m} t \right)$$

$$\text{app}_{\triangle}^{s m_{+}} \text{ (in}_{s m} f) s \equiv \text{in}_{s m} \left( \text{app}_{\triangle}^{s m} f s \right)$$

$$\text{app}_{\triangle}^{s m_{+}} \text{ (in}_{d m} f) s \equiv \text{in}_{d m} \left( \text{app}^{d m} f s \right).$$

The other cases reduce to functions of a modal variable:

$$\Pi_{\diamondsuit}^{s m_{+}} A B \equiv \Pi^{s m_{+}} (\diamondsuit A) B$$

$$\Pi_{\triangle \diamondsuit}^{s m_{+}} A B \equiv \Pi_{\triangle}^{s m_{+}} (\diamondsuit A) B$$

$$\Pi_{\square}^{s m_{+}} A B \equiv \Pi^{s m_{+}} (\square A) B$$

$$\Pi_{\triangle \square}^{s m_{+}} A B \equiv \Pi_{\triangle}^{s m_{+}} (\square A) B$$

The cases of $\lambda$ and app are similar.

◁

73