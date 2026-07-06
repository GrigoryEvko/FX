$\mathrm{Ho}(\mathcal{N})$ can be represented by a cospan

$$FB \to (FC)^{\mathrm{FIB}} \stackrel{\sim}{\leftarrow} FC \in \mathcal{N}.$$

Therefore, we can use theorem 4.13 to find a map $B \to C$ in $\mathrm{Ho}(\mathcal{M})$ which is in the preimage.

Lastly, we see that the induced functor is faithful. Let $A, C \in \mathcal{M}^{\mathrm{COF}}$ cofibrant and two maps $f, g : A \to C \in \mathcal{M}$ which become equal in $\mathrm{Ho}(\mathcal{N})$ under the functor induced by $F$. This is just saying that the maps $F\bar{f}, F\bar{g} : FA \to F(C^{\mathrm{FIB}})$ are homotopic where $\bar{f}, \bar{g} : A \to C^{\mathrm{FIB}}$ are maps in $\mathcal{M}$. It will be enough to show that $\bar{f}$ and $\bar{g}$ are homotopic *i.e.*, there is a diagonal filler for the diagram

$$\begin{array}{c} A \coprod A \xrightarrow{(\bar{f}, \bar{g})} C^{\mathrm{FIB}} \\ \Big\downarrow \\ IA \end{array}$$

where $IA$ is a weak cylinder object for $A$. Since $F$ is a left Quillen functor, we can assume that cylinders are preserved. Furthermore, homotopies are independent of the choice of cylinders. We can express the homotopy between of $F\bar{f}$ and $F\bar{g}$ in $\mathcal{N}$ as the commutative square

$$\begin{array}{c} F(A \coprod A) \xrightarrow{(F\bar{f}, F\bar{g})} F(B^{\mathrm{FIB}}) \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F(IA) \xrightarrow{h} F(B^{\mathrm{FIB}})^{\mathrm{FIB}}, \end{array}$$

where $h$ is the homotopy, and the fibrant replacement $F(C^{\mathrm{FIB}})^{\mathrm{FIB}}$ is necessary since $F(C^{\mathrm{FIB}})$ is not fibrant as $F$ is only left Quillen. The assumptions of theorem 4.13 are now satisfied, so this produces a diagonal as on the left whose image fits on the right square up to homotopy:

$$\begin{array}{c} A \coprod A \xrightarrow{(\bar{f}, \bar{g})} C^{\mathrm{FIB}} \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ IA \end{array}$$

$$\begin{array}{c} F(A \coprod A) \xrightarrow{(F\bar{f}, F\bar{g})} F(C^{\mathrm{FIB}}) \\ \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ F(IA) \xrightarrow{h} F(C^{\mathrm{FIB}})^{\mathrm{FIB}} \end{array}$$

The above shows that $\mathrm{Ho}(\mathcal{M}) \to \mathrm{Ho}(\mathcal{N})$ is faithful, concluding the proof that $F$ is a left Quillen equivalence. $\square$

65