5.2. CARTESIAN FIBRATIONS

Lemma 5.2.5.13. Let p be a left cartesian fibration over I². We have an equivalence

$$\mathbf{L}(i \times id_{a^b})_!(p \times id_{a^b}) \sim (\mathbf{L}i_!p) \times id_{a^b}.$$

Let q be a left cartesian fibration over A². We have an equivalence

$$\mathbf{R}(i \times id_{a^b})^*(q \times id_{a^b}) \sim (\mathbf{R}i^*q) \times id_{a^b}.$$

Proof. The first assertion is straightforward as the cartesian product with aᵇ preserves initial morphisms and left cartesian fibrations. The second assertion is obvious. □

We define $\tilde{E}_0$ and $\tilde{E}_1$ as the full sub $(\infty, 1)$-categories of $E_0$ and $E_1$ whose objects are respectively of shape $p \times id_a$ and $q \times id_a$ for p and q classified left cartesian fibrations over I and A². The last lemma implies that (5.2.5.12) restricts to an adjunction

$$i_! : \tilde{E}_0 \xrightarrow{\perp} \tilde{E}_1 : i^* \tag{5.2.5.14}$$

# Lemma 5.2.5.15.

(1) Let $q \to q'$ be a morphism in $\tilde{E}_0$ corresponding to a cartesian square. The induced morphism $i_!(q) \to i_!(q')$ also corresponds to a cartesian square.
(2) Let $q \to q'$ be a morphism in $\tilde{E}_1$ corresponding to a cartesian square. The induced morphism $i^*(q) \to i^*(q')$ also corresponds to a cartesian square.

Proof. Cartesian morphisms in $\tilde{E}_0$ corresponds to cartesian squares

$$\begin{array}{c} X \times a^b \longrightarrow X \times b^b \\ \downarrow_{p \times id_a} \qquad \qquad \qquad \qquad \downarrow_{p \times id_b} \\ I \times a^b \longrightarrow I \times b^b \end{array}$$

and cartesian morphisms in $\tilde{E}_1$ corresponds to cartesian squares

$$\begin{array}{c} Y \times a^b \longrightarrow Y \times b^b \\ \downarrow_{q \times id_a} \qquad \qquad \qquad \qquad \downarrow_{q \times id_b} \\ A^\sharp \times a^b \longrightarrow A^\sharp \times b^b \end{array}$$

The results directly follows from lemma 5.2.5.13. □

The canonical projection $\tilde{E}_0 \to \Theta$ and $\tilde{E}_1 \to \Theta$ are Grothendieck fibrations in $(\infty, 1)$-categories. The cartesian lifting is given by cartesian squares. Moreover, their Grothendieck deconstructions correspond respectively to $a \mapsto \mathrm{LCart}^c(I; a)$ and $a \mapsto$

295