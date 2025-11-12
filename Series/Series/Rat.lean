import Interval.Approx.Rat
import Series.Series.Basic

/-!
# Rationals approximate series computations over any field

We want to do power series computations over `ℚ`, where these approximate `ℂ` via field structure.
This works because our `spray` series functions uses only field operations on scalars.
-/

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

instance : SeriesScalar ℚ where
instance : ApproxSeries ℚ 𝕜 where
