import LeanFX2.FX1Bridge.RoundTrip
import LeanFX2.FX1Bridge.Unit
import LeanFX2.FX1Bridge.Var
import LeanFX2.FX1Bridge.Lambda
import LeanFX2.FX1Bridge.Application
import LeanFX2.FX1Bridge.Pi
import LeanFX2.FX1Bridge.Bool
import LeanFX2.FX1Bridge.Nat
import LeanFX2.FX1Bridge.Interval
import LeanFX2.FX1Bridge.Path
import LeanFX2.FX1Bridge.Record
import LeanFX2.FX1Bridge.Universe
import LeanFX2.FX1Bridge.Id
import LeanFX2.FX1Bridge.IdJ
import LeanFX2.FX1Bridge.Equiv

/-! # FX1Bridge

Root status: Bridge.

Public umbrella for rich LeanFX2-to-FX1 translation and soundness fragments.
This namespace is intentionally separate from both `LeanFX2.Rich` and
`LeanFX2.FX1`: bridge modules may import rich syntax plus FX1 metatheory, while
neither side should silently depend on the other through a broad umbrella.
-/

namespace LeanFX2
namespace FX1Bridge

end FX1Bridge
end LeanFX2
