import FX.Kernel.Term
import FX.Kernel.Grade

/-!
# Q57 — Kernel-local compact Term pretty-printer

`repr Term` renders every `Grade` field individually and every
sub-term's record verbatim — a Pi with defaulted grades fans
into a ~30-line record dump per arrow.  Two concrete costs:

  * T002 (type mismatch) in `Typing.lean` emits two `repr`s
    side-by-side — ~60 lines for the simplest shape mismatch.
  * Any trusted-layer error carrying a `Term` goes through the
    same path, so CI scrapers see runaway payloads.

`Term.prettyCompact` collapses:
  * `Grade.default`, `Grade.ghost`, `Grade.shared` → named
    abbreviations (`def`, `ghost`, `ω`).
  * `Grade`s with non-trivial usage → `g<usage>` short form.
  * Effect rows → `{IO, Alloc, …}` list; `Tot` → omitted.
  * Ctors/Inds → `T.ctorN` fallback when no spec available;
    named lookups require the GlobalEnv and therefore live in
    the CLI layer (`termPrettyWith`).

Trust-layer note: this file is pure derivation from Term +
Grade + Effect + Level.  No sorries, no axioms, no I/O.  Safe
to include in `FX/Kernel/**` per the axiom-audit gate.

Compared to CLI's `termPrettyWith` (which threads `userSpecs`
for ctor-name resolution): this variant deliberately skips the
env threading so `TypeError.atTerm` doesn't need a `GlobalEnv`
parameter.  The result is slightly less readable (`Nat.ctor0`
vs `Nat.Zero`), but the structural shape — which is what T002
users need — is preserved.
-/

namespace FX.Kernel

namespace Grade

/-- Compact grade rendering.  Collapses the three named grades
    to their labels and falls back to `g<usage>` for other
    shapes. -/
def prettyCompact (grade : Grade) : String :=
  if grade == Grade.default then "def"
  else if grade == Grade.ghost then "ghost"
  else if grade == Grade.shared then "ω"
  else
    -- Fallback: show just the usage — the overwhelming majority
    -- of non-default grades in practice differ only on usage.
    match grade.usage with
    | .zero  => "0"
    | .one   => "1"
    | .omega => "ω"

end Grade

namespace Effect

/-- Compact effect-row rendering.  `Tot` renders empty (so the
    caller can conditionally append a `→{...}` fragment).  Other
    rows list their active labels comma-separated. -/
def prettyCompact (effect : Effect) : String :=
  let labels : List String :=
    (if effect.io    then ["IO"]    else []) ++
    (if effect.div   then ["Div"]   else []) ++
    (if effect.ghost then ["Ghost"] else []) ++
    (if effect.exn   then ["Exn"]   else []) ++
    (if effect.alloc then ["Alloc"] else []) ++
    (if effect.read  then ["Read"]  else []) ++
    (if effect.write then ["Write"] else []) ++
    (if effect.async then ["Async"] else [])
  String.intercalate ", " labels

end Effect

namespace Level

/-- Compact level rendering.  `0`, `(succ 0)`, `lvl#i` for
    universe-poly vars, `(max a b)` for joins. -/
def prettyCompact : Level → String
  | .zero        => "0"
  | .succ inner  => s!"({prettyCompact inner} +1)"
  | .max a b     => s!"max({prettyCompact a}, {prettyCompact b})"
  | .var index   => s!"lvl#{index}"

end Level

namespace Term

/-- Compact term rendering.  See module docstring for the
    trade-offs vs `repr`.  Used by `TypeError` formatting in
    `Typing.lean` (Q57). -/
partial def prettyCompact : Term → String
  | .var index => s!"#{index}"
  | .type level => s!"Type<{Level.prettyCompact level}>"
  | .const name => name
  | .coind typeName args =>
    if args.isEmpty then typeName
    else
      let argStrings := args.map prettyCompact
      s!"{typeName}({String.intercalate ", " argStrings})"
  | .forallLevel body =>
    s!"∀lvl. {prettyCompact body}"
  | .app func arg =>
    s!"{prettyCompact func}({prettyCompact arg})"
  | .lam grade domainType body =>
    s!"λ(_:{prettyCompact domainType} :_{Grade.prettyCompact grade}). {prettyCompact body}"
  | .pi grade domainType codomainType returnEffect =>
    let effectSuffix :=
      let effectLabels := Effect.prettyCompact returnEffect
      if effectLabels.isEmpty then ""
      else " →{" ++ effectLabels ++ "}"
    s!"Π(_:{prettyCompact domainType} :_{Grade.prettyCompact grade}){effectSuffix}. {prettyCompact codomainType}"
  | .sigma grade domainType codomainType =>
    s!"Σ(_:{prettyCompact domainType} :_{Grade.prettyCompact grade}). {prettyCompact codomainType}"
  | .ind typeName [] => typeName
  | .ind typeName args =>
    let argStrings := args.map prettyCompact
    s!"{typeName}({String.intercalate ", " argStrings})"
  | .ctor typeName ctorIndex _typeArgs [] =>
    s!"{typeName}.ctor{ctorIndex}"
  | .ctor typeName ctorIndex _typeArgs ctorArgs =>
    let argStrings := ctorArgs.map prettyCompact
    s!"{typeName}.ctor{ctorIndex}({String.intercalate ", " argStrings})"
  | .indRec typeName _motive methods target =>
    let methodStrings := methods.map prettyCompact
    s!"indRec[{typeName}]({prettyCompact target}, methods=[{String.intercalate ", " methodStrings}])"
  | .id baseType leftEndpoint rightEndpoint =>
    s!"Id({prettyCompact baseType}, {prettyCompact leftEndpoint}, {prettyCompact rightEndpoint})"
  | .refl witness =>
    s!"refl({prettyCompact witness})"
  | .idJ _motive base eqProof =>
    s!"idJ(base={prettyCompact base}, eq={prettyCompact eqProof})"
  | .quot baseType relation =>
    s!"Quot({prettyCompact baseType}, {prettyCompact relation})"
  | .quotMk _relation witness =>
    s!"Quot.mk({prettyCompact witness})"
  | .quotLift lifted _respects target =>
    s!"Quot.lift({prettyCompact lifted}, {prettyCompact target})"
  | .coindUnfold typeName _typeArgs arms =>
    let armStrings := arms.mapIdx
      (fun idx arm => s!"#{idx} => {prettyCompact arm}")
    s!"unfold<{typeName}>({String.intercalate "; " armStrings})"
  | .coindDestruct typeName destructorIndex target =>
    s!"{typeName}.dtor{destructorIndex}({prettyCompact target})"

end Term

end FX.Kernel
