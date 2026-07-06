DOUBLY WEAK DOUBLE CATEGORIES

49

The other unitor naturality laws are analogous, as well as the associator naturality laws, where we use

$$\begin{array}{c} \boxed{f(gh)} \\ \boxed{\cong} \\ \boxed{(\zeta\xi)\psi} \\ \boxed{(fg)h} \end{array} = \boxed{f(gh)} \begin{array}{c} \boxed{f(gh)} \\ \boxed{1} \\ \boxed{\zeta\xi\psi} \\ \boxed{(fg)h} \end{array} \quad \text{and} \quad \boxed{f(gh)} \begin{array}{c} \boxed{f(gh)} \\ \boxed{\zeta(\xi\psi)} \\ \boxed{\cong} \\ \boxed{(fg)h} \end{array} = \boxed{f(gh)} \begin{array}{c} \boxed{f(gh)} \\ \boxed{\zeta\xi\psi} \\ \boxed{1} \\ \boxed{(fg)h} \end{array}$$

constructed from the same $1 \times 3$ grid (and similarly in the vertical case, with a $3 \times 1$ grid). We also have that the inverse pairs of coherence cells do behave as such:

$$\boxed{\begin{array}{c} \boxed{\cong} \\ \boxed{\cong} \end{array}} = \boxed{\begin{array}{c} 1 \\ \boxed{1} \end{array}}$$

Similarly the pentagon and triangle laws of a bicategory are satisfied because all formal compositions of coherence cells agree, as noted above.

The next law we show is the identity square commutativity law of a double bicategory. Observe for any square $\alpha$, we have the equations

$$\boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha & 1 \end{array}} = \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \end{array}} \quad \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \end{array}} = \boxed{\begin{array}{c|c|c} 1 & \alpha & 1 \\ \hline 1 & 1 & 1 \end{array}}$$

since both sides of each equation have the same boundary and are formal composites constructed from the $1 \times 1$ grid $\alpha$. (Of course, whenever we compose a grid, we must choose some bracketing of its boundary, but we will omit such annotations from our diagrams, trusting the reader to supply suitable choices.)

When $\alpha$ is moreover a *bigon* (bordered on either side by identities), we get

$$\boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha & 1 \end{array}} = \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \end{array}} = \boxed{\begin{array}{c|c|c} 1 & \alpha & 1 \\ \hline 1 & 1 & 1 \end{array}}$$

(The composite in the middle agrees the two from above since there is a unique coherence cell for any bracketed boundary of a $0 \times 0$ grid.) Hence by cancelling the identities on the left and right, we obtain

$$\boxed{\begin{array}{c} 1 \\ \hline \alpha \end{array}} = \boxed{\begin{array}{c} \alpha \\ \hline 1 \end{array}}$$

Horizontal identity square commutativity is similar.

The bigon identity laws are trivial. We also have the associativity laws for composing bigons (with squares or bigons):

$$\boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha\beta & \zeta \\ \hline 1 & 1 & 1 \end{array}} = \boxed{\begin{array}{c|c} \boxed{\cong} & \boxed{\alpha} \\ \hline \alpha\beta & \zeta \\ \hline \end{array}} = \boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline \alpha & \beta & \zeta \\ \hline 1 & 1 & 1 \end{array}} = \boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline \alpha & 1 & \beta\zeta \\ \hline 1 & 1 & 1 \end{array}} = \boxed{\begin{array}{c|c|c} 1 & 1 & 1 \\ \hline 1 & \alpha & \beta\zeta \\ \hline 1 & 1 & 1 \end{array}}$$

and the action compatibility laws: