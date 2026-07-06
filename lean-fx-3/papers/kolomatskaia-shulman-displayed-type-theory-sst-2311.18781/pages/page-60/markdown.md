Then we inductively define:

$$\pi(\Pi^{\text{sm}^{n+2}} \text{ A B}) \equiv \Pi^{\text{sm}^{n+1}} \pi \text{A} \pi \text{B}$$

$$(\Pi^{\text{sm}^{n+2}} \text{ A B})_{n+2} \equiv \left( \Pi^{\text{sm}^{n+1}} (\pi \text{A}^{\rho_{\Gamma}})^{\text{pt}} \Pi^{\text{sm}^{n+1}} (\text{A}^{\text{d}})^{\text{W}_2^{\pi \text{A}^{\rho_{\Gamma}} \text{pt}}} (\text{B}^{\text{d}})^{\left| \text{W}_2^{\text{A}^{\text{d}} \text{W}_2^{\pi \text{A}^{\rho_{\Gamma}} \text{pt}}, \text{app} \text{zv}^{\text{pt} \circ \text{pt}} \text{zv}^{\text{pt}} \right|} \right)_{n+1}$$

$$\pi(\lambda^{\text{sm}^{n+2}} \text{ t}) \equiv \lambda^{\text{sm}^{n+1}} \pi \text{t}$$

$$(\lambda^{\text{sm}^{n+2}} \text{ t})_{n+2} \equiv \left( \lambda^{\text{sm}^{n+1}} \left( \lambda^{\text{sm}^{n+1}} \text{ t}^{\text{d}} \right) \right)_{n+1}$$

$$\pi(\text{app}^{\text{sm}^{n+2}} \text{ f s}) \equiv \text{app}^{\text{sm}^{n+1}} \pi \text{f} \pi \text{s}$$

$$(\text{app}^{\text{sm}^{n+2}} \text{ f s})_{n+2} \equiv \left( \text{app}^{\text{sm}^{n+1}} \left( \text{app}^{\text{sm}^{n+1}} \text{ f}^{\text{d}} \pi \text{s}^{\rho_{\Gamma}} \right) \text{ s}^{\text{d}} \right)_{n+1}.$$

As before, this says that the constructions are performed level-wise. From this, theorems eqs. (4.19) to (4.21) then follow inductively, since the hypothesised display formulas were used to define each successive level. The correctness of these definitions will follow from verifying the $\beta$ and $\eta$ laws in appendix A.2.

### 4.2.7 Universes

The universes of the discrete model are denoted $\text{Disc}_{\ell}$. We construct universes in $\text{sm}^n$ inductively, with all of the assumptions of a $\mathcal{U}$-type structure outlined before assumed at all prior levels. We will inductively have that:

$$(\text{Type}_{\ell}^{\text{sm}^{n+1}})^{\text{d}} \equiv \Pi^{\text{sm}^n} (\text{EI zv}) \text{ Type}_{\ell}^{\text{sm}^n} \tag{4.22}$$

$$(\text{Code}^{\text{sm}^{n+1}} \text{ A})^{\text{d}} \equiv \lambda^{\text{sm}^n} (\text{Code}^{\text{sm}^n} \text{ A}^{\text{d}}) \tag{4.23}$$

$$(\text{EI}^{\text{sm}^{n+1}} \text{ A})^{\text{d}} \equiv \text{EI}^{\text{sm}^n} (\text{app}^{\text{sm}^n} (\text{A}^{\text{d}})^{\text{pt}} \text{ zv}). \tag{4.24}$$

For $\text{sm}^{-1}$, we define:

$$(\text{Type}_{\ell}^{\text{sm}^{-1}})_{-1} \equiv \text{Disc}_{\ell}$$

$$(\text{Code}^{\text{sm}^{-1}} \text{ A})_{-1} \equiv \text{Code}^{\text{dm}} \text{ A}_{-1}$$

$$(\text{EI}^{\text{sm}^{-1}} \text{ A})_{-1} \equiv \text{EI}^{\text{dm}} \text{ A}_{-1}.$$

Then we inductively define:

$$\pi(\text{Type}_{\ell}^{\text{sm}^{n+2}}) \equiv \text{Type}_{\ell}^{\text{sm}^{n+1}}$$

$$(\text{Type}_{\ell}^{\text{sm}^{n+2}})_{n+2} \equiv \left( \Pi^{\text{sm}^{n+1}} (\text{EI zv}) \text{ Type}_{\ell}^{\text{sm}^{n+1}} \right)_{n+1}$$

$$\pi(\text{Code}^{\text{sm}^{n+2}} \text{ A}) \equiv \text{Code}^{\text{sm}^{n+1}} \pi \text{A}$$

$$(\text{Code}^{\text{sm}^{n+2}} \text{ A})_{n+2} \equiv \left( \lambda^{\text{sm}^{n+1}} (\text{Code}^{\text{sm}^{n+1}} \text{ A}^{\text{d}}) \right)_{n+1}$$

$$\pi(\text{EI}^{\text{sm}^{n+2}} \text{ A}) \equiv \text{EI}^{\text{sm}^{n+1}} \pi \text{A}$$

$$(\text{EI}^{\text{sm}^{n+2}} \text{ A})_{n+2} \equiv \left( \text{EI}^{\text{sm}^{n+1}} (\text{app}^{\text{sm}^{n+1}} (\text{A}^{\text{d}})^{\text{pt}} \text{ zv}) \right)_{n+1}.$$

Again, this says that the constructions are performed level-wise. From this, theorems eqs. (4.22) to (4.24) then follow inductively, since the hypothesised display formulas were

60