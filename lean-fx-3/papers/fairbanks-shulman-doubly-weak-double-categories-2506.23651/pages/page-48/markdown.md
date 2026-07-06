48

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

use single identity 1-cells as the composites of the nullary left and right boundaries, and obtain a coherence 2-cell. We will write all of these coherence 2-cells as “≅”, save for the identity squares written as “1” (which, observe, are a special case of coherence 2-cells), and we often write elongated = signs for identity 1-cells. For instance, here is horizontal associativity:

$$\begin{array}{c} \cdot \xrightarrow{f(gh)} \cdot \\ \Big\| \quad \cong \quad \Big\| \\ \cdot \quad \xrightarrow{(fg)h} \cdot \end{array}$$

Our discussion at the beginning of this section implies that two formal composites, i.e. squares in a free cubical bicategory, constructed from the same grid of squares are equal if and only if they have the same boundary. (By definition, the 2-cells in a free cubical bicategory on a double graph are compatible grids of squares with bracketed boundaries.) In particular, any formal composite featuring only coherence cells is itself a coherence cell, since there is at most one formal composite with any given boundary featuring *no* squares.

We next verify the double bicategory laws. The double-categorical interchange laws are automatic from the cubical bicategory structure. To show the remaining laws, note that in a *tidy* cubical bicategory, we have cancellation with respect to composing with identities. Therefore one strategy to show an equation between two squares is to compose both of them with identities and then to express the resulting two squares as formal composites derived from the same grid. (Then since we know these squares must be equal, by cancellation the original squares are equal.)

Let us start with the unitar naturality laws. We must show that the following compositions with coherence bigons are equal:

$$\begin{array}{c} \boxed{\cong} \\ \boxed{\zeta} \end{array} \mapsto \boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{(1\zeta)} \mapsto \boxed{\cong} \\ \boxed{(1\zeta)} \mapsto \boxed{(1\zeta)} \mapsto \boxed{(1\zeta)}$$

Observe

$$\begin{array}{c} \boxed{\cong} \\ \boxed{\zeta} \end{array} = \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{\zeta} \mapsto \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{\zeta} \mapsto \boxed{\begin{array}{c} 1 \\ \hline \end{array}} = \boxed{\begin{array}{c} \zeta \\ \hline 1 \end{array}}$$

since each is a formal composite constructed from the same $1 \times 1$ grid $\zeta$. Hence by definition of bigon composition we have

$$\begin{array}{c} \boxed{1} \\ \boxed{\cong} \\ \boxed{\zeta} \end{array} = \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{\zeta} \mapsto \boxed{\begin{array}{c} 1 \\ \hline \end{array}} \\ \boxed{1} \mapsto \boxed{\begin{array}{c} \zeta \\ \hline 1 \end{array}} = \boxed{\begin{array}{c} \zeta \\ \hline 1 \end{array}}$$

and therefore by cancelling identities

$$\boxed{\cong} \\ \boxed{\zeta} \mapsto \boxed{\zeta} \mapsto \boxed{(1\zeta)} \mapsto \boxed{\cong}$$