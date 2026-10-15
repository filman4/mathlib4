module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Data.Set.Restrict
/-!
## Riemann Sphere
-/

@[expose] public section

open Metric Topology Complex Set

noncomputable section

abbrev RiemannSphere := OnePoint ℂ

def ZeroSource : Set RiemannSphere := {z | z ≠ OnePoint.infty}

def ZeroTarget : Set ℂ := Set.univ

def InftySource : Set RiemannSphere := {z | z ≠ (0 : ℂ)}

def InftyTarget : Set ℂ := Set.univ

def ChartZero : OnePoint ℂ → ℂ
  | OnePoint.infty => 0
  | OnePoint.some z => z

def ChartZeroInv : ℂ → RiemannSphere := fun z => z

def ChartInfty : RiemannSphere → ℂ
  | OnePoint.infty => 0
  | OnePoint.some z => z⁻¹

def ChartInftyInv : ℂ → RiemannSphere := fun z => if z = 0 then OnePoint.infty else (z⁻¹ : ℂ)

def ChartZeroOn : ZeroSource → ℂ :=
  ZeroSource.domRestrict ChartZero

def ChartInftyOn : InftySource → ℂ :=
  InftySource.domRestrict ChartInfty

def ChartZeroIsOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialHomeomorph := {
    toPartialEquiv := {
      toFun := ChartZero
      invFun := ChartZeroInv
      source := ZeroSource
      target := ZeroTarget
      map_source' _ _ := by simp [ZeroTarget]
      map_target' z _ := by
        change (z : OnePoint ℂ) ≠ OnePoint.infty
        exact OnePoint.coe_ne_infty z
      left_inv'
      right_int'
    }
  }
def ChartInftyIsOpenPartialHomeomorph :

instance RiemannSphereIsChartedSpace : ChartedSpace ℂ RiemannSphere :=
