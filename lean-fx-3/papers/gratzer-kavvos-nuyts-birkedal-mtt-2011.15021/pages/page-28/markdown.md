11:28

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

Recall that we are trying to find a diagonal filler to the $\mathbf{PSh}(\mathcal{C}[m])$ diagram

$$\begin{array}{c} \mathbf{y}(\Gamma.(\mu \circ \nu \mid A)) \xrightarrow{\lfloor M_1 \rfloor} \widetilde{\mathcal{T}}_m \\ \mathbf{y}(\mathbf{p}.\mathbf{mod}_\nu(\mathbf{q})) \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \mathbf{y}(\Gamma.(\mu \mid \mathbf{Mod}_\nu(A))) \xrightarrow{\lfloor B \rfloor} \mathcal{T}_m \end{array} \tag{5.9}$$

We use the adjunction $\sum_Z \dashv Z^*$ to transpose this diagram, and we compose with the isomorphisms (5.8) to obtain the following diagram in $\mathbf{PSh}(\mathcal{C}[m])/Z$:

$$\begin{array}{c} \lfloor A \rfloor \times_Z \left[ \widehat{\mathbf{\Theta}}_{\mu \circ \nu} \right]^* \widetilde{\mathcal{T}}_o \xrightarrow{\widehat{[M_1]}} Z^*(\widetilde{\mathcal{T}}_m) \\ \text{id} \times_Z \left[ \widehat{\mathbf{\Theta}}_\mu \right]^* m \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \lfloor A \rfloor \times_Z \left[ \widehat{\mathbf{\Theta}}_\mu \right]^* h \xrightarrow{\text{ open}_\nu^\mu} Z^*(\mathcal{T}_m) \\ \hline \lfloor B \rfloor \end{array}$$

We may then use the lifting structure to prove a diagonal filler, and transpose backwards along the adjunction to obtain a filler for (5.9). The naturality of all these steps (composing isomorphisms, transposition, and lifting structure) ensure that the choice is natural.

5.2.3. *Boolean Structure.* A boolean structure is defined similarly to the structure for modal types. First, we require two constants, as well as naturally given diagonal fillers for the appropriate squares:

$$\begin{array}{c} \mathbf{tt} \\ 1 \xrightarrow{\text{ }} \widetilde{\mathcal{T}}_m \\ \mathbf{ff} \\ 1 \xrightarrow{\text{ }} \mathcal{T}_m \\ \mathbf{Bool} \end{array} \quad \begin{array}{c} 1 + 1 \xrightarrow{\text{ }} \widetilde{\mathcal{T}}_m \\ \mathbf{tt}, \mathbf{ff} \\ \tau_m^{-1}(\mathbf{Bool}) \end{array} \quad \begin{array}{c} \mathbf{tt}, \mathbf{ff} \\ \tau_m \\ \tau_m^{-1}(\mathbf{Bool}) \end{array}$$

$\tau_m^{-1}(\mathbf{Bool})$ is the fibre of $\tau_m$ over $\mathbf{Bool}$, and the map $[\mathbf{tt}, \mathbf{ff}]$ is obtained as the cotuple of the maps obtained by factoring $\mathbf{tt}$ and $\mathbf{ff}$ through the fibre. Requiring a left lifting structure

$$\mathbf{if} : [\mathbf{tt}, \mathbf{ff}] \pitchfork \tau_m[-]$$

in the internal language provides enough naturality to yield diagonal fillers for all squares

$$\begin{array}{c} \mathbf{y}(\Gamma) + \mathbf{y}(\Gamma) \xrightarrow{\text{ }} \widetilde{\mathcal{T}}_m \\ [\text{id}.\mathbf{tt}, \text{id}.\mathbf{ff}] \Bigg\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{ } \\ \mathbf{y}(\Gamma.\mathbf{Bool}) \xrightarrow{\text{ }} \mathcal{T}_m \end{array}$$