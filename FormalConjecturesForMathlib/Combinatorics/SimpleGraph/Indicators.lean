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
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Matching
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Check if `G` is Eulerian. -/
def isEulerian (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  G.edgeFinset.card = 0 ∨ (G.Connected ∧ ∀ v, Even (G.degree v))

/-- The Eulerian indicator of `G`. -/
noncomputable def eulerianIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if G.isEulerian then 1 else 0

/-- Check if `G` has a claw (K_{1,3}) as an induced subgraph. -/
def hasClaw (G : SimpleGraph α) : Prop :=
  ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d ∧ ¬G.Adj c d

/-- The claw-free indicator of `G`. -/
noncomputable def clawFreeIndicator (G : SimpleGraph α) : ℕ :=
  if hasClaw G then 0 else 1

/-- Check if `G` is twin-free. -/
def isTwinFree (G : SimpleGraph α) : Prop :=
  ∀ u v : α, u ≠ v → G.neighborFinset u ≠ G.neighborFinset v

/-- The twin-free indicator of `G`. -/
noncomputable def twinFreeIndicator (G : SimpleGraph α) : ℕ :=
  if isTwinFree G then 1 else 0

/-- The matchability indicator of `G` (1 if it has a perfect matching, 0 otherwise). -/
noncomputable def matchabilityIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  let n := Fintype.card α
  if n % 2 = 0 ∧ 2 * G.matchingNumber = (n : ℝ) then 1 else 0

/-- The bipartite indicator of `G`. -/
noncomputable def bipartiteIndicator (G : SimpleGraph α) : ℕ :=
  if G.IsBipartite then 1 else 0

/-- The triangle-free indicator of `G`. -/
noncomputable def triangleFreeIndicator (G : SimpleGraph α) : ℕ :=
  if G.cliqueNum < 3 then 1 else 0

/-- The acyclic indicator of `G`. -/
noncomputable def acyclicIndicator (G : SimpleGraph α) : ℕ :=
  if G.IsAcyclic then 1 else 0

/-- The well-totally-dominated indicator of `G`. -/
noncomputable def wellTotallyDominatedIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if G.IsWellTotallyDominated then 1 else 0

end SimpleGraph
