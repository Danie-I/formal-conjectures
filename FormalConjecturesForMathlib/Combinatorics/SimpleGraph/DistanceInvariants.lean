/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.DiamExtra
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SzegedIndex
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Harary index of `G`. -/
noncomputable def hararyIndex (G : SimpleGraph α) : ℚ :=
  ∑ e ∈ (completeGraph α).edgeFinset,
    e.lift ⟨fun u v => 1 / (G.dist u v : ℚ), by simp [dist_comm]⟩

/-- The hyper-Wiener index of `G`. -/
noncomputable def hyperWienerIndex (G : SimpleGraph α) : ℚ :=
  (1 / 2) * ∑ e ∈ (completeGraph α).edgeFinset,
    e.lift ⟨fun u v => (G.dist u v : ℚ) + (G.dist u v : ℚ) ^ 2, by simp [dist_comm]⟩

/-- The Gutman index of `G`. -/
noncomputable def gutmanIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ (completeGraph α).edgeFinset,
    e.lift ⟨fun u v => G.degree u * G.degree v * G.dist u v,
      by simp [dist_comm, mul_comm]⟩

/-- The Schultz index of `G`. -/
noncomputable def schultzIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ (completeGraph α).edgeFinset,
    e.lift ⟨fun u v => (G.degree u + G.degree v) * G.dist u v,
      by simp [dist_comm, add_comm]⟩

/-- The modified Schultz index of `G`. -/
noncomputable def modifiedSchultzIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  gutmanIndex G

/-- The proximity of `G`. -/
noncomputable def proximity (G : SimpleGraph α) : ℚ :=
  let n := Fintype.card α
  if n < 2 then 0 else
    let transmissions := (Finset.univ.toList.map (fun u => ∑ v, (G.dist u v : ℚ)))
    (transmissions.min?).getD 0 / (n - 1 : ℚ)

/-- The remoteness of `G`. -/
noncomputable def remoteness (G : SimpleGraph α) : ℚ :=
  let n := Fintype.card α
  if n < 2 then 0 else
    let transmissions := (Finset.univ.toList.map (fun u => ∑ v, (G.dist u v : ℚ)))
    (transmissions.max?).getD 0 / (n - 1 : ℚ)

/-- The reciprocal complementary Wiener index of `G`. -/
noncomputable def reciprocalComplementaryWiener (G : SimpleGraph α) : WithTop ℚ :=
  match G.ediam with
  | ⊤ => ⊤
  | (d : ℕ) =>
    let sum : ℚ := ∑ e ∈ (completeGraph α).edgeFinset,
      e.lift ⟨fun u v => 1 / ((d : ℚ) + 1 - (G.dist u v : ℚ)), by simp [dist_comm]⟩
    (sum : WithTop ℚ)

/-- The size of the barycenter set of `G`. -/
noncomputable def barycenterSetSize (G : SimpleGraph α) : ℕ :=
  let transmissions := Finset.univ.toList.map (fun u => ∑ v, G.dist u v)
  let min_trans := (transmissions.min?).getD 0
  (Finset.univ.filter (fun u => (∑ v, G.dist u v) = min_trans)).card

/-- The Balaban J-index of `G`. -/
noncomputable def balabanJIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  let m := G.edgeFinset.card
  let mu_plus_1 := (m : ℤ) - (n : ℤ) + 2
  if mu_plus_1 <= 0 then 0 else
    let D (u : α) : ℝ := ∑ v, (G.dist u v : ℝ)
    let sum := ∑ e ∈ G.edgeFinset,
      e.lift ⟨fun u v => 1 / Real.sqrt (D u * D v), by simp [mul_comm]⟩
    (m : ℝ) / (mu_plus_1 : ℝ) * sum

/-- The Mostar index of `G`. -/
noncomputable def mostarIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => Nat.dist (szeged_aux G u v) (szeged_aux G v u),
      by simp [Nat.dist_comm]⟩

/-- Distance from a vertex `v` to an edge `e` in `G`.
    Returns `⊤` if `e` is not reachable from `v`. -/
noncomputable def distToEdge (G : SimpleGraph α) (v : α) (e : Sym2 α) : ℕ∞ :=
  e.lift ⟨fun x y =>
    if G.Reachable v x ∨ G.Reachable v y then
      min (if G.Reachable v x then (G.dist v x : ℕ∞) else ⊤)
          (if G.Reachable v y then (G.dist v y : ℕ∞) else ⊤)
    else ⊤,
    by intro x y
       dsimp
       rw [or_comm, min_comm]⟩

/-- Auxiliary function for Edge-PI index: counts edges closer to u than v. -/
noncomputable def edge_pi_aux (G : SimpleGraph α) (u v : α) : ℕ :=
  (G.edgeFinset.filter (fun f => G.distToEdge u f < G.distToEdge v f)).card

/-- The Edge-PI index of `G`. -/
noncomputable def piIndex (G : SimpleGraph α) : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => edge_pi_aux G u v + edge_pi_aux G v u,
      by intro u v; dsimp; rw [add_comm]⟩

/-- The Wiener polarity index of `G`. -/
noncomputable def wienerPolarityIndex (G : SimpleGraph α) : ℕ :=
  ((completeGraph α).edgeFinset.filter (fun e =>
    e.lift ⟨fun u v => G.dist u v == 3, by simp [dist_comm]⟩
  )).card

end SimpleGraph
