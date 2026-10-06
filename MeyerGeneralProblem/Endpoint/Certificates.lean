module

public import MeyerGeneralProblem.Endpoint.LayerMonotonicity

@[expose] public section

/-!
# Analytic certificates for the density branches

The hard subcritical and supercritical arguments expose only the data used by
the abstract endpoint and cardinal arguments.  These structures contain no
density assumption: source-bound analytic modules must construct them before
the corresponding density theorem can be exported.
-/

open Filter

namespace MeyerGeneralProblem

noncomputable section

/-- The exact output required from the no-separation subcritical analysis. -/
structure SubcriticalEndpointCertificate (S : LocallyFiniteCarrier) where
  /-- Every positive fixed-order Meyer layer is finite-dimensional. -/
  finiteLayer :
    ∀ m : ℕ, ∀ hm : 1 ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm)
  /-- The intrinsic reduced endpoint has a strict eventual gap. -/
  eventualGap :
    ∀ᶠ m : ℕ in atTop, ∀ hm : 1 ≤ m,
      fixedOrderReducedRadius S m hm < 1

/-- The exact output required from the supercritical analysis. -/
structure SupercriticalEndpointCertificate (S : LocallyFiniteCarrier) where
  /-- A positive Hermite order witnessing the infinite layer. -/
  order : ℕ
  /-- The selected order is positive. -/
  order_pos : 1 ≤ order
  /-- The selected fixed-order Meyer layer is infinite-dimensional. -/
  infiniteLayer :
    ¬ FiniteDimensional ℂ (FixedOrderMeyerLayer S order order_pos)

/-- A subcritical certificate exports fixed-order finiteness without reopening
the analytic proof. -/
theorem SubcriticalEndpointCertificate.fixedOrderFiniteness
    {S : LocallyFiniteCarrier} (C : SubcriticalEndpointCertificate S) :
    ∀ m : ℕ, ∀ hm : 1 ≤ m,
      FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm) :=
  C.finiteLayer

/-- A subcritical certificate exports its intrinsic eventual endpoint gap. -/
theorem SubcriticalEndpointCertificate.endpointGap
    {S : LocallyFiniteCarrier} (C : SubcriticalEndpointCertificate S) :
    ∀ᶠ m : ℕ in atTop, ∀ hm : 1 ≤ m,
      fixedOrderReducedRadius S m hm < 1 :=
  C.eventualGap

/-- A supercritical certificate exports an infinite fixed-order layer. -/
theorem SupercriticalEndpointCertificate.exists_infiniteLayer
    {S : LocallyFiniteCarrier} (C : SupercriticalEndpointCertificate S) :
    ∃ m : ℕ, ∃ hm : 1 ≤ m,
      ¬ FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm) :=
  ⟨C.order, C.order_pos, C.infiniteLayer⟩

end

end MeyerGeneralProblem
