242

Cohesive parametric type theory

Connected components $(( \gamma : \Gamma) \otimes \text{cc})$

$$(\cdot : \cdot) \otimes \text{cc} := \cdot$$

$$((\gamma, M/a) : (\Gamma, (\mu \mid a : A))) \otimes \text{cc} := \begin{cases} ((\gamma : \Gamma) \otimes \text{cc}, M/a), & \text{if } \mu = \text{cc}, \mu' \\ (\gamma : \Gamma) \otimes \text{cc}, & \text{otherwise} \end{cases}$$

$$((\gamma, r/x) : (\Gamma, x : \mathbb{I})) \otimes \text{cc} := ((\gamma : \Gamma) \otimes \text{cc}, r/x)$$

$$((\gamma, r/x) : (\Gamma, x : 2)) \otimes \text{cc} := ((\gamma : \Gamma) \otimes \text{cc}, r/x)$$

$$((\gamma, r/x) : (\Gamma, x : \mathbb{I})) \otimes \text{cc} := (\gamma : \Gamma) \otimes \text{cc}$$

$$(\gamma : (\Gamma, \xi)) \otimes \text{cc} := (\gamma : \Gamma) \otimes \text{cc}$$

Discrete embedding $(( \gamma : \Gamma) \otimes \text{dsc})$

$$(\gamma : \Gamma) \otimes \text{dsc} := \gamma$$

Global sections $(( \gamma : \Gamma) \otimes \text{glo})$

$$(\gamma : \Gamma) \otimes \text{glo} := \gamma$$

Figure 14.2: Definitions of the modal substitution operators

Interval restriction $(\Gamma \setminus r)$

If a bridge term $r$ is equal to an endpoint term, then restriction has no effect.

$$\Gamma \setminus r := \Gamma \quad \text{if } \Gamma \gg r = s \in \mathbb{I} \text{ @ par for some } \Gamma \gg s \in 2 \text{ @ par}$$

Otherwise, restriction is defined as follows.

$$(\Gamma, y : \mathbb{I}) \setminus x := (\Gamma \setminus x), y : \mathbb{I}$$

$$(\Gamma, y : 2) \setminus x := (\Gamma \setminus x), y : 2$$

$$(\Gamma, y : \mathbb{I}) \setminus x := \begin{cases} \Gamma & \text{if } x = y \\ (\Gamma \setminus x), y : \mathbb{I} & \text{otherwise} \end{cases}$$

$$(\Gamma, y : \mathbb{I}) \setminus x := \Gamma \setminus x, y : \mathbb{I}$$

$$(\Gamma, \xi) \setminus x := (\Gamma \setminus x), \xi$$

$$(\Gamma, (\mu \mid a : A)) \setminus x := \begin{cases} \Gamma \setminus x, (\mu \mid a : A), & \text{if } \mu = (\text{cc}, \mu') \\ \Gamma \setminus x, & \text{otherwise} \end{cases}$$

Figure 14.3: Definition of interval restriction