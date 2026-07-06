6

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

1.2. FROM REALIGNMENT TO CUMULATIVE HIERARCHIES. The true utility of (U8) is the ability to choose a representation for a morphism $f \in \mathcal{S}$ subject to a strict equation. For instance, (U8) is sufficient to 'strictify' a hierarchy of universes so that the choices of codes for connectives commute with the coercion maps from one universe to another [Shu15]. In particular, let $\mathcal{S} \subseteq \mathcal{T}$ be two universes equipped with a choice of cartesian monomorphism $i: \pi_{\mathcal{S}} \mapsto \pi_{\mathcal{T}}$. Further assume that $\mathcal{T}$ satisfies realignment for the class of all monomorphisms.

1.2.1. NOTATION. Given a morphism $f: X \longrightarrow Y$, we write $P_f: \mathcal{E} \longrightarrow \mathcal{E}$ for the polynomial endofunctor given by the composite $Y \circ f_* \circ X^*$.

Both $\mathcal{S}, \mathcal{T}$ are closed under dependent products, hence there exist cartesian morphisms $\Pi_{\mathcal{S}}: P_{\pi_{\mathcal{S}}}(\pi_{\mathcal{S}}) \longrightarrow \pi_{\mathcal{S}}$ and $\Pi_{\mathcal{T}}: P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}}) \longrightarrow \pi_{\mathcal{T}}$, but Diagram 1 below need not commute:

$$\begin{array}{ccc} P_{\pi_{\mathcal{S}}}(\pi_{\mathcal{S}}) & \xrightarrow{\Pi_{\mathcal{S}}} & \pi_{\mathcal{S}} \\ P_i(i) & \downarrow & \downarrow \\ P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}}) & \xrightarrow{\Pi_{\mathcal{T}}} & \pi_{\mathcal{T}} \end{array} \quad (1)$$

We can replace $\Pi_{\mathcal{S}}, \Pi_{\mathcal{T}}$ with new codes $\Pi_{\mathcal{S}}', \Pi_{\mathcal{T}}'$ for which the analogue to Diagram 1 commutes. We set $\Pi_{\mathcal{S}}' := \Pi_{\mathcal{S}}$ and define $\Pi_{\mathcal{T}}'$ by realigning $i \circ \Pi_{\mathcal{S}}'$ along $P_i(i)$:

$$\begin{array}{ccc} P_{\pi_{\mathcal{S}}}(\pi_{\mathcal{S}}) & \xrightarrow{\Pi_{\mathcal{S}}'} & \pi_{\mathcal{S}} \\ P_i(i) & \downarrow & \downarrow \\ P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}}) & \xrightarrow{\Pi_{\mathcal{T}}'} & \pi_{\mathcal{T}} \end{array} \quad (2)$$

If we further assume that $\mathcal{E}$ is sufficiently cocomplete, *e.g.*, if it is a Grothendieck topos, the technique above easily extends to infinite and even transfinite hierarchies of universes. In the latter case, one realigns along the *join* of all the subobjects $P_{\pi_{\mathcal{S}}'}(\pi_{\mathcal{S}}') \mapsto P_{\pi_{\mathcal{T}}}(\pi_{\mathcal{T}})$ pertaining to the formation data for dependent product type codes at lower universes. Then a coherent hierarchy of such codes is built 'from the ground up' by induction.

1.3. STRUCTURE OF THE PAPER. We survey the landscape of universe constructions available in Grothendieck toposes and show that they inherit a plentiful supply of well-behaved universes from **Set**.

**Section 2.** We revisit the presheaf-theoretic universe construction of Hofmann and Streicher [HS97], lifting a Grothendieck universe in **Set** to a universe of pointwise small families of presheaves satisfying (U1–8). Presenting a sheaf topos as a subcategory of a presheaf topos, we recall from Streicher [Str05] that the Hofmann–Streicher construction