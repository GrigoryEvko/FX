CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

By construction, we then have for any i ≤ j ≤ 2

$$u_j^\alpha = v_j^\alpha + w_j^\alpha + t_j^\alpha.$$

and

$$\partial(v_{i+1}^-) = v_i^+ - v_i^- \quad \partial(w_{i+1}^-) = w_i^+ - w_i^- \quad \partial(t_{i+1}^-) = t_i^+ - t_i^-$$

and

$$\partial(u_i^\alpha) = \partial(v_i^\alpha) = \partial(w_i^\alpha) = \partial(t_i^\alpha)$$

It then remains to show that for any i + 1 < j ≤ 2

$$\partial v_j^\alpha = v_{j-1}^+ - v_{j-1}^- \quad \partial w_j^\alpha = w_{j-1}^+ - w_{j-1}^- \quad \partial t_j^\alpha = t_{j-1}^+ - t_{j-1}^- \tag{1.2.2.12}$$

and

$$v_i^- \ge 0 \quad w_i^- \ge 0 \tag{1.2.2.13}$$

Indeed, if the assertions (1.2.2.12) and (1.2.2.13) are fulfilled, this implies that the sequences {v_j^β}, {w_j^β} and {t_j^β} are arrays and then correspond respectively to the unique cells v, w and t fulfilling the desired condition.

We first deal with the assertion (1.2.2.12). Suppose first that there exists an integer j such that i + 1 < j ≤ 2. This implies that i = 0. The lemma 1.2.2.9 then implies that w_2^α = λx with λ ∈ {0, 1}. By assumption, we have

$$\partial(u_2^\beta) = u_1^+ - u_1^-$$

and then

$$\partial(v_2^\beta) + \partial(w_2^\beta) + \partial(t_2^\beta) = v_1^+ - v_1^- + w_1^+ - w_1^- + t_1^+ - t_1^-$$

The lemma 1.2.2.10 implies that any element of the base belonging to ∂(v_2^β) (resp. to ∂(t_2^β)) is 0-inferior to x (resp. 0-superior to x). Moreover, for any b ∈ ∂(w_2^β) = λ∂x, we have ¬(b < 1^r x) ∨ ¬(x < 1^r b).

The previous equality then implies

$$\partial(v_2^\beta) = v_1^+ - v_1^- \quad \partial(w_2^\beta) = w_1^+ - w_1^- \quad \partial(t_2^\beta) = t_1^+ - t_1^-$$

We now deal with the assertion (1.2.2.12). We claim that we have

$$\partial^+ v_{i+1}^\alpha \wedge \partial^- w_{i+1}^\alpha = 0 \quad \partial^+ w_{i+1}^\alpha \wedge \partial^- t_{i+1}^\alpha = 0 \quad \partial^+ v_{i+1}^\alpha \wedge \partial^- t_{i+1}^\alpha = 0$$

Indeed, suppose that ∂+v_{i+1}^α ∧ ∂-w_{i+1}^α ≠ 0. This implies that there exists an element of the base b ∈ w_{i+1}^α and c ∈ v_{i+1}^α such that b < i c. As we have by definition c < i x, this directly implies that b < i x which is absurd. We show similarly the two other equalities. This implies that

$$\begin{array}{l} u_i^+ \ge \partial(u_{i+1}^-) \\ = \partial^+(v_{i+1}^- + w_{i+1}^- + t_{i+1}^-) \\ = \partial^+(v_{i+1}^-) + (\partial^+(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + (\partial^+(t_{i+1}^-) - \partial^-(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ \end{array}$$

As a consequence, we have

$$\begin{array}{l} v_i^- = u_i^+ - \partial(v_{i+1}^-) \\ = u_i^+ - \partial^+(v_{i+1}^-) + \partial^-(v_{i+1}^-) \\ \ge (\partial^+(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + (\partial^+(t_{i+1}^-) - \partial^-(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + \partial^-(v_{i+1}^-) \\ \ge (\partial^+(w_{i+1}^-) - \partial^-(v_{i+1}^-))_+ + \partial^-(v_{i+1}^-) \\ \ge \partial^+(w_{i+1}^-) \end{array}$$

34