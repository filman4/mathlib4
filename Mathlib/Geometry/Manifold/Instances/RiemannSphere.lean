/-
Copyright (c) 2026 Filip Moruś. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Moruś
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Data.Set.Restrict
public import Mathlib.Topology.Continuous
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Data.Set.Operations



/-!
## Riemann Sphere
-/

set_option linter.style.setOption false
set_option linter.flexible false

@[expose] public section

open Set OnePoint

noncomputable section

namespace SphereComplex

abbrev RiemannSphere := OnePoint ℂ

def ZeroSource : Set RiemannSphere := {OnePoint.infty}ᶜ

def ZeroTarget : Set ℂ := Set.univ

def InftySource : Set RiemannSphere := {OnePoint.some 0}ᶜ

def InftyTarget : Set ℂ := Set.univ

def ZeroChart : RiemannSphere → ℂ
  | OnePoint.infty => 0
  | OnePoint.some z => z

def ZeroChartInv : ℂ → RiemannSphere :=
  fun z => ((↑) : ℂ → RiemannSphere) z

def InftyChart : RiemannSphere → ℂ
  | OnePoint.infty => 0
  | OnePoint.some z => z⁻¹

def InftyChartInv : ℂ → RiemannSphere := fun z => if z = 0 then OnePoint.infty else (z⁻¹ : ℂ)

def ZeroChartIsOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialHomeomorph := {
    toPartialEquiv := {
      toFun := ZeroChart
      invFun := ZeroChartInv
      source := ZeroSource
      target := ZeroTarget
      map_source' _ _ := by simp [ZeroTarget]
      map_target' z _ := by
        change (z : OnePoint ℂ) ≠ OnePoint.infty
        exact OnePoint.coe_ne_infty z
      left_inv' z hz := by
        cases z with
        | none =>
          exact absurd hz (by
            rw [ZeroSource, compl_infty]
            exact infty_notMem_range_coe)
        | some z => rfl
      right_inv' z hz := by simp [ZeroChartInv, ZeroChart]
    }
    continuousOn_toFun := by
      have hs : ZeroSource = range ((↑) : ℂ → RiemannSphere) := by
        rw [ZeroSource, compl_infty]
      rw [hs]
      exact OnePoint.isOpenMap_coe.continuousOn_range_of_leftInverse
        (fun z => by simp [ZeroChart])
    continuousOn_invFun := by
      simp [ZeroTarget]
      exact continuous_coe
  }
  open_source := by
    change IsOpen ZeroSource
    rw [ZeroSource, compl_infty]
    exact isOpen_range_coe
  open_target := by
    change IsOpen ZeroTarget
    exact isOpen_univ


def InftyChartIsOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialHomeomorph := {
    toPartialEquiv := {
      toFun := InftyChart
      invFun := InftyChartInv
      source := InftySource
      target := InftyTarget
      map_source' _ _ := by simp [InftyTarget]
      map_target' z _ := by
        by_cases hz : z = 0 <;> simp [InftyChartInv, hz, InftySource]
      left_inv' z hz := by
        cases z with
        | none =>
          simp [InftyChart, InftyChartInv, infty]
          rfl
        | some z =>
          rw [InftyChart, InftyChartInv]
          have hw : z ≠ 0 := by


          simp [hw]
    }
  }
  open_source := by
    change IsOpen ZeroSource
    rw [ZeroSource, compl_infty]
    exact isOpen_range_coe
  open_target := by
    change IsOpen ZeroTarget
    exact isOpen_univ

end SphereComplex
