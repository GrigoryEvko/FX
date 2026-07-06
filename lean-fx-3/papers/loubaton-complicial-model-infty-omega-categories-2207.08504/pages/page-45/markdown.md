1.2. GRAY OPERATIONS

Definition 1.2.3.13. We define the wedges as the functors

$$[\_, 1] \vee [1] : \mathrm{ADC} \to \mathrm{ADC} \qquad [1] \vee [\_, 1] : \mathrm{ADC} \to \mathrm{ADC}$$

where $[K, 1] \vee [1]$ and $[1] \vee [K, 1]$ are defined as the following pushouts:

$$\begin{array}{c} \lambda[0] \xrightarrow{\{0}} [1] \\ \{1\} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [K, 1] \longrightarrow [K, 1] \vee [1] \end{array}$$

$$\begin{array}{c} \lambda[0] \xrightarrow{\{0}} [K, 1] \\ \{1\} \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1] \longrightarrow [1] \vee [K, 1] \end{array}$$

Once again, we can easily check that $[K, 1] \vee [1]$ and $[1] \vee [K, 1]$ have a loop free and unitary basis when this is the case for $K$. These functors then induce functors

$$[\_, 1] \vee [1] : \mathrm{ADC}_{\mathrm{B}} \to \mathrm{ADC}_{\mathrm{B}} \qquad [1] \vee [\_, 1] : \mathrm{ADC}_{\mathrm{B}} \to \mathrm{ADC}_{\mathrm{B}}$$

Unfolding the definition, we have

$$[(K, K', e), 1] \vee [1] := ([K, 1] \vee [1], ([K, 1] \vee [1])^*, e)$$

$$[1] \vee (K, K', e), 1] := ([1] \vee [K, 1], ([1] \vee [K, 1])^*, e)$$

where

- $[K, 1] \vee [1]$ and $[1] \vee [K, 1]$ are the chain complexes whose value on $n$ are:

$$[K, 1] \vee [1] := \left\{ \begin{array}{ll} \mathbb{Z}[\{0\}, \{1\}, \{2\}] & \text{if } n = 0 \\ \{[x, 1], x \in K_0\} \oplus \mathbb{Z}[e_1] & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 1 \end{array} \right.$$

$$[1] \vee [K, 1] := \left\{ \begin{array}{ll} \mathbb{Z}[\{0\}, \{1\}, \{2\}] & \text{if } n = 0 \\ \mathbb{Z}[e_1] \oplus \{[x, 1], x \in K_0\} & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 1 \end{array} \right.$$

and the differentials are the unique graded group morphism fulfilling:

$$\partial_{[K, 1] \vee [1]}(e_1) := \{2\} - \{1\} \quad \partial_{[K, 1] \vee [1]}([x, 1]) := \left\{ \begin{array}{ll} \{1\} - \{0\} & \text{if } |x| = 0 \\ [\partial x, 1] & \text{if } |x| > 0 \end{array} \right.$$

$$\partial_{[1] \vee [K, 1]}(e_1) := \{1\} - \{0\} \quad \partial_{[1] \vee [K, 1]}([x, 1]) := \left\{ \begin{array}{ll} \{2\} - \{1\} & \text{if } |x| = 0 \\ [\partial x, 1] & \text{if } |x| > 0 \end{array} \right.$$

- $([K, 1] \vee [1])^*$ and $([1] \vee [K, 1])^*$ are given on all integer $n$ by:

$$([K, 1] \vee [1])^* := \left\{ \begin{array}{ll} \{\{0\}, \{1\}, \{2\}\} & \text{if } n = 0 \\ \{[x, 1], x \in K_0^*\} \oplus \mathbb{N}[e_1] & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}\} & \text{if } n > 1 \end{array} \right.$$

$$([1] \vee [K, 1])^* := \left\{ \begin{array}{ll} \{\{0\}, \{1\}, \{2\}\} & \text{if } n = 0 \\ \mathbb{N}[e_1] \oplus \cup\{[x, 1], x \in K_0^*\} & \text{if } n = 1 \\ \{[x, 1], x \in K_{n-1}^*\} & \text{if } n > 1 \end{array} \right.$$

45