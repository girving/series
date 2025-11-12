import Interval.Approx.Dyadic
import Series.Series.Basic

/-!
# Dyadic rationals approximate series computations over any field

We want to do power series computations over `Dyadic`, where these approximate `ℂ` as a ring.
This works because our `spray` series functions uses only ring operation and `div2` on scalars.
-/

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

instance : SeriesScalar Dyadic where
instance : ApproxSeries Dyadic 𝕜 where
