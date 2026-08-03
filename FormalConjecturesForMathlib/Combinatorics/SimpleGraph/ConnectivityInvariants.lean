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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of connected components of `G`. -/
noncomputable def connectedComponentsCount (G : SimpleGraph α) : ℕ :=
  Fintype.card G.ConnectedComponent

/-- The vertex connectivity of `G`. -/
noncomputable def vertexConnectivity (G : SimpleGraph α) : ℕ :=
  let separating_sets := Finset.univ.toList.filter (fun S : Finset α =>
    let G_minus_S := G.induce ((S : Set α)ᶜ)
    ¬ G_minus_S.Connected ∨ Fintype.card α - S.card ≤ 1
  )
  let sizes := separating_sets.map Finset.card
  (sizes.min?).getD 0

/-- The edge connectivity of `G`. -/
noncomputable def edgeConnectivity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  let n := Fintype.card α
  if n <= 1 then
    0
  else
    let separating_edge_sets := (Finset.powerset G.edgeFinset).toList.filter (fun (E' : Finset (Sym2 α)) =>
      ¬ (G.deleteEdges ↑E').Connected
    )
    let sizes := separating_edge_sets.map Finset.card
    (sizes.min?).getD 0

/-- Check if `v` is a cut vertex in `G`. -/
def isCutVertex (G : SimpleGraph α) (v : α) : Prop :=
  G.connectedComponentsCount < (G.induce ({v}ᶜ : Set α)).connectedComponentsCount

/-- The number of cut vertices in `G`. -/
noncomputable def cutVerticesCount (G : SimpleGraph α) : ℕ :=
  ((Finset.univ : Finset α).filter (fun v => G.isCutVertex v)).card

/-- Check if `e` is a bridge in `G`. -/
def isBridge (G : SimpleGraph α) (e : Sym2 α) : Prop :=
  G.connectedComponentsCount < (G.deleteEdges ({e} : Set (Sym2 α))).connectedComponentsCount

/-- The number of bridges in `G`. -/
noncomputable def bridgesCount (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.filter (fun e => G.isBridge e)).card

/-- The toughness of `G`. -/
noncomputable def toughness (G : SimpleGraph α) : WithTop ℚ :=
  let separating_sets := Finset.univ.powerset.toList.filter (fun S : Finset α =>
    let G_minus_S := G.induce ((S : Set α)ᶜ)
    ¬ G_minus_S.Connected
  )
  let values := separating_sets.map (fun S : Finset α =>
    (S.card : ℚ) / (G.induce ((S : Set α)ᶜ)).connectedComponentsCount
  )
  match values.min? with
  | none => ⊤
  | some t => t

/-- The cyclic connectivity of `G`. -/
noncomputable def cyclicConnectivity (G : SimpleGraph α) [DecidableRel G.Adj] : WithTop ℕ :=
  let edge_subsets := G.edgeFinset.powerset.toList
  let valid_subsets := edge_subsets.filter (fun S : Finset (Sym2 α) =>
    let G_minus_S := G.deleteEdges (S : Set (Sym2 α))
    let components := Finset.univ.filter (fun c : G_minus_S.ConnectedComponent =>
      let comp_verts := Finset.univ.filter (fun v => G_minus_S.connectedComponentMk v = c)
      ¬ (G_minus_S.induce (comp_verts : Set α)).IsAcyclic
    )
    components.card ≥ 2
  )
  let sizes := valid_subsets.map (fun S => S.card)
  match sizes.min? with
  | none => ⊤
  | some c => c

end SimpleGraph
