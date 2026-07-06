Open judgments 241

# **Connected components ( $\Gamma.cc$ )**

$$\begin{aligned} \cdot .cc &:= \cdot \\ (\Gamma, x : \mathbb{I}).cc &:= \Gamma.cc, x : \mathbb{I} \\ (\Gamma, x : 2).cc &:= \Gamma.cc, x : 2 \\ (\Gamma, x : \mathbb{I}).cc &:= \Gamma.cc \\ (\Gamma, r \equiv s).cc &:= \Gamma.cc, r \equiv s \\ (\Gamma, r \equiv \varepsilon).cc &:= \begin{cases} \Gamma.cc, r \equiv \varepsilon, & \text{if } \Gamma \gg r \in 2 \text{ @ par} \\ \Gamma.cc, \neg \varepsilon \equiv \varepsilon, & \text{if not but } \Gamma \gg r = \neg \varepsilon \in \mathbb{I} \text{ @ par} \\ \Gamma.cc, & \text{otherwise} \end{cases} \\ (\Gamma, (\mu \mid a : A)).cc &:= \begin{cases} \Gamma.cc, (\mu' \mid a : A), & \text{if } \mu = cc, \mu' \\ \Gamma.cc, & \text{otherwise} \end{cases} \end{aligned}$$

# **Discrete embedding ( $\Gamma.dsc$ )**

$$\begin{aligned} \cdot .dsc &:= \cdot \\ (\Gamma, x : \mathbb{I}).dsc &:= \Gamma.dsc, x : \mathbb{I} \\ (\Gamma, x : 2).dsc &:= \Gamma.dsc, x : 2 \\ (\Gamma, \xi).dsc &:= \Gamma.dsc, \xi \\ (\Gamma, (\mu \mid a : A)).dsc &:= \Gamma.dsc, (cc, \mu \mid a : A) \end{aligned}$$

# **Global sections ( $\Gamma.glo$ )**

$$\begin{aligned} \cdot .glo &:= \cdot \\ (\Gamma, x : \mathbb{I}).glo &:= \Gamma.glo, x : \mathbb{I} \\ (\Gamma, x : 2).glo &:= \Gamma.glo, x : 2 \\ (\Gamma, x : \mathbb{I}).glo &:= \Gamma.glo, x : 2 \\ (\Gamma, \xi).glo &:= \Gamma.glo, \xi \\ (\Gamma, (\mu \mid a : A)).glo &:= \Gamma.glo, (dsc, \mu \mid a : A) \end{aligned}$$

Figure 14.1: Definitions of the modal context operators