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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The feedback vertex set size of `G`. -/
noncomputable def feedbackVertexSetSize (G : SimpleGraph α) : ℕ :=
  let fvs_sizes := (Finset.univ.toList.filter (fun s : Finset α =>
    IsAcyclic (G.induce ((s : Set α)ᶜ))
  )).map Finset.card
  (fvs_sizes.min?).getD 0

/-- Helper to check if a set of edges is a matching. -/
def isMatching (M : Finset (Sym2 α)) : Prop :=
  ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
    ∀ x, ¬ (x ∈ e1 ∧ x ∈ e2)

/-- The Hosoya index of `G`. -/
noncomputable def hosoyaIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter isMatching).card

/-- The Merrifield-Simmons index of `G`. -/
noncomputable def merrifieldSimmonsIndex (G : SimpleGraph α) : ℕ :=
  ((Finset.univ : Finset α).powerset.filter (fun S : Finset α => G.IsIndepSet S)).card

/-- Helper to check if a set of vertices is resolving. -/
def isResolvingSet (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ u v : α, u ≠ v → ∃ s ∈ S, G.edist u s ≠ G.edist v s

/-- The metric dimension of `G`. -/
noncomputable def metricDimension (G : SimpleGraph α) : ℕ :=
  let resolving_sets := Finset.univ.toList.filter (fun S : Finset α => isResolvingSet G S)
  let sizes := resolving_sets.map Finset.card
  (sizes.min?).getD 0

end SimpleGraph
