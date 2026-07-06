# Chapter 1

## $(0, \omega)$-Categories and presheaves on $\Theta$

### Contents

|  **1.1 Basic constructions** | **13**  |
| --- | --- |
|  1.1.1 $(0, \omega)$-Categories | 13  |
|  1.1.2 The category $\Theta$ | 16  |
|  1.1.3 The link between presheaves on $\Theta$ and on $\Delta[\Theta]$ | 20  |
|  **1.2 Gray Operations** | **25**  |
|  1.2.1 Recollection on Steiner theory | 25  |
|  1.2.2 2-Polygraphs and presheaves on $\Theta_2$ | 30  |
|  1.2.3 Gray operations on augmented directed complexes | 40  |
|  1.2.4 Gray operations on $(0, \omega)$-categories | 46  |
|  1.2.5 Gray tensor product of simplicial sets | 52  |

The first section is devoted to the definition of $(0, \omega)$-categories and of the category $\Theta$ of Joyal. We also show that the category $\Theta$ presents the category of $(0, \omega)$-categories, and we also exhibit an other presentation of this category (corollary 1.1.3.4).

The second section begins with a review of Steiner theory, which is an extremely useful tool for providing concise and computational descriptions of $(0, \omega)$-categories. Following Ara and Maltsiniotis, we employ this theory to define the Gray tensor product, denoted by $\otimes$, in $(0, \omega)$-categories. We then introduce the Gray operations, starting with the Gray cylinder $\_ \otimes [1]$ which is the Gray tensor product with the directed interval $[1] := 0 \rightarrow 1$. Then, we have the *Gray cone*, the *Gray o-cone* and the *Gray op-cone*, denoted by $\_ \star 1$, $1 \star \_ \_ \_ \_ \_ and $1 \star \_ \_$, that send an $(0, \omega)$-category $C$ onto the following pushouts:

$$\begin{array}{ccc} C \otimes \{1\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & C \star 1 \end{array} \qquad \begin{array}{ccc} C \otimes \{0\} & \longrightarrow & C \otimes [1] \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \star C \end{array} \qquad \begin{array}{ccc} \{0\} \otimes C & \longrightarrow & [1] \otimes C \\ \downarrow & & \downarrow \\ 1 & \longrightarrow & 1 \star C \end{array}$$

We also present a formula that illustrates the interaction between the suspension and the Gray cylinder. As this formula plays a crucial role in this text, we provide its intuition at this stage.

11