import Interval.Interval.Complex
import Series.Series.Basic

/-!
# `Interval` satisfies our `Series` typeclasses
-/

instance : SeriesScalar Interval where
instance : ApproxSeries Interval ℝ where
instance : ApproxSeries Interval ℂ where
