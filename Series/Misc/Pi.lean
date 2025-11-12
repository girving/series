import Interval.Approx.Approx

/-!
# Approx instances for functions
-/

variable {α β β' : Type} [Approx β β']

instance Pi.instApprox : Approx (α → β) (α → β') where
  approx f f' := ∀ x, approx (f x) (f' x)
