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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The density of `G`. -/
noncomputable def graphDensity (G : SimpleGraph α) : ℚ :=
  let n := Fintype.card α
  if n < 2 then 0 else
    (2 * G.edgeFinset.card : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))

/-- The degeneracy of `G`. -/
noncomputable def degeneracy (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  let min_degs := Finset.univ.toList.map (fun s : Finset α => (G.induce s).minDegree)
  (min_degs.max?).getD 0

/-- The maximum core size of `G`. -/
noncomputable def maxCoreSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  let d := degeneracy G
  let core_subsets := Finset.univ.filter (fun s : Finset α => (G.induce s).minDegree ≥ d)
  (core_subsets.biUnion id).card

/-- The number of triangles in `G`. -/
noncomputable def trianglesCount (G : SimpleGraph α) : ℕ :=
  (Finset.filter (fun (s : Finset α) => G.IsClique (s : Set α) ∧ s.card = 3) Finset.univ.powerset).card

/-- The minimum non-edge neighborhood union of `G`. -/
noncomputable def minimumNonEdgeNeighborhoodUnion (G : SimpleGraph α) : ℕ :=
  let non_edges := (completeGraph α).edgeFinset.filter (fun e =>
    e.lift ⟨fun u v => ¬ G.Adj u v, by simp [adj_comm]⟩
  )
  let union_sizes := non_edges.toList.map (fun e =>
    e.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card, by simp [Finset.union_comm]⟩
  )
  (union_sizes.min?).getD 0

end SimpleGraph
