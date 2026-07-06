4.1.2. Proposition : Let $(\mathcal{H}, \|.\|)$ be a pre-Banach locale. Let $s$ and $p$ denote the maps $\mathcal{H} \times \mathcal{H} \to \mathcal{H}$ defined by:

$$s(x, y) = x - y$$

$$p(x, y) = x + y$$

Let $m$ denote the map $x \mapsto -x$ and $n$ be the norm map, $n : \mathcal{H} \to \overleftarrow{\mathbb{R}}^\infty$.

Finally we will denote $B_q 0 = n^*([0, q])$ (point 5 ensures that there is no possible confusion).

Then, one has the following facts:

1. The map \( n \circ s \) is a pre-distance on \( \mathcal{H} \).
2. The maps \(s\) and \(p\) are open maps.
3. The open sublocales \(\Delta_q\) coincide with \(s^*(B_q0)\).
4. If \(\mathcal{L}\) is any sublocale of \(\mathcal{H}\) then \(B_q\mathcal{L}\) coincide with both \(p_{!}(\mathcal{L}\times B_{q}0)\) and \(s_{!}(\mathcal{L}\times B_{q}0)\).
5. \(B_{q}0\) is the same things as \(B_{q}\{0\}\).

# Proof :

1. A proof by generalized points will be exactly the same as the usual proof that \( d(x,y) = \| x - y\| \) is a distance on a normed space.
2. We will consider two maps \(\mathcal{H} \times \mathcal{H} \to \mathcal{H} \times \mathcal{H}\) given by

$$\tau_p = (p, m \circ \pi_1);$$

$$\tau_s = (\pi_1, s).$$

These maps correspond in term of generalized points to the maps $\tau_p(x, y) = -x + y, -y)$ and $\tau_s(x, y) = (x, x - y)$, and they are both involutive and hence bijective. The maps $s$ and $p$ are then obtained as $\pi_2 \circ \tau_s$ and $\pi_1 \circ \tau_p$, but as $\mathcal{H}$ is locally positive, both $\pi_1$ and $\pi_2$ are open maps. Hence by composition $s$ and $p$ are open maps.

3. \(\Delta_q\) is by definition \(d^* ([0,q])\), but as \(d = n\circ s\), one has \(\Delta_q = s^* n^* ([0,q]) = s^* (B_q0)\).
4. The involutive map \(\tau_s\) introduced in the proof of point 2 exchange \(\pi^*(\mathcal{L}) \wedge \Delta_q\) with \(\mathcal{L} \times B_q0\), indeed:

$$\tau_s^*(\mathcal{L} \times B_q 0) = p i_1^*(\mathcal{L}) \wedge s^*(B_q 0) = \pi_1^*(\mathcal{L}) \wedge \Delta_q.$$

Hence $\pi_2!(\pi_1^*(\mathcal{L}) \wedge \Delta_q) = (\pi_2 \circ \tau_s)!(\mathcal{L} \times B_q 0)$ and $\pi \circ \tau_s = s$, which shows that $B_q \mathcal{L} = s!(\mathcal{L} \times B_q 0)$.

It also coincides with $p!(\mathcal{L} \times B_q 0)$ because as $n \circ m = n$ one has $m^*(B_q 0) = B_q 0$, and as $s = p \circ (Id, m)$ this concludes the proof.

51