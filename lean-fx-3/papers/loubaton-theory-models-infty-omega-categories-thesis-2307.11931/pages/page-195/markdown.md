4.2. BASIC CONSTRUCTIONS

If the functor $f^*: C_{/d} \to C_{/c}$ preserves colimits and $f^*(S_{/c}) \subset S_{/d}$, the adjunction

$$f^*: C_{/d} \xrightarrow{\perp} C_{/c}: f_*$$

induces an adjunction

$$\mathbf{L}f^*: (C_{/d})_{S_{/d}} \xrightarrow{\perp} (C_{/c})_{S_{/c}}: \mathbf{R}f_*$$

## 4.2 Basic constructions

### 4.2.1 $(\infty, \omega)$-Categories

The definitions of section 1.1.2 will be used freely here.

#### 4.2.1.1. We denote by

$$[\_, \_]: \mathrm{Psh}^\infty(\Theta) \times \mathrm{Psh}^\infty(\Delta) \to \mathrm{Psh}^\infty(\Delta[\Theta])$$

the extension by colimit of the functor $\Theta \times \Delta \to \mathrm{Psh}^\infty(\Delta[\Theta])$ sending $(a, n)$ onto $[a, n]$. For an integer $n$, we denote

$$[\_, n]: \mathrm{Psh}^\infty(\Theta)^n \to \mathrm{Psh}^\infty(\Theta)$$

the extension by colimit of the functor $\Theta^n \to \mathrm{Psh}^\infty(\Theta)$ sending $\mathbf{a} := \{a_1, ..., a_n\}$ onto $[\mathbf{a}, n]$.

#### 4.2.1.2. We have an adjunction

$$i_! : \mathrm{Psh}^\infty(\Delta[\Theta]) \xrightarrow{\longleftrightarrow} \mathrm{Psh}^\infty(\Theta) : i^* \tag{4.2.1.3}$$

where the left adjoint is the left Kan extension of the functor $\Delta[\Theta] \xrightarrow{i} \Theta \to \mathrm{Psh}^\infty(\Theta)$. The sets of morphisms W and M are respectively defined in paragraphs 1.1.2.14 and 1.1.2.15. There is an obvious inclusion $i_!(M) \subset W$. The previous adjunction then induced a derived adjunction

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta])_M \xrightarrow{\longleftrightarrow} \mathrm{Psh}(\Theta)_W : \mathbf{R}i^* \tag{4.2.1.4}$$

**Proposition 4.2.1.5.** *The unit and counit of the adjunction (4.2.1.3) are respectively in $\widehat{M}$ and $\widehat{W}$. As a consequence, the adjunction (4.2.1.4) is an adjoint equivalence.*

*Proof.* We denote by $\iota : \mathrm{Psh}(\Theta) \to \mathrm{Psh}^\infty(\Theta)$ and $\iota : \mathrm{Psh}(\Delta[\Theta]) \to \mathrm{Psh}^\infty(\Delta[\Theta])$ the two canonical inclusions. By the definition of the smallest precocomplete class (paragraph 1.1.3.1) and according to lemma 4.1.1.6, we have inclusions $\iota(\overline{W}) \subset \widehat{W}$ and $\iota(\overline{M}) \subset \widehat{M}$. The result then directly follows from theorem 1.1.3.3. $\square$

185