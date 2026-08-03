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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Set.Card
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)

/-- The multiset of degrees of a graph. -/
def degreeMultiset (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v

/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/--
The maximum number of occurrences of any term of the degree sequence of `G`.
-/
noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

/-- Infinite graphs: definitions for max degree and clique number so that the maximum
degree of a graph with unbounded degree is
`∞` rather than 0.
-/
noncomputable
def edegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ∞ := (G.neighborSet v).encard

noncomputable
def emaxDegree {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨆ v, G.edegree v

/-- Cardinality of the union of the neighbourhoods of the ends of the non-edge `e`. -/
def non_edge_neighborhood_card (G : SimpleGraph α) [DecidableRel G.Adj] (e : Sym2 α) : ℕ :=
  Sym2.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card,
    fun u v => by simp [Finset.union_comm]⟩ e

/-- Minimum size of the neighbourhood of a non-edge of `G`. -/
noncomputable def NG (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let non_edges := (compl G).edgeFinset
  if h : non_edges.Nonempty then
    let neighbor_sizes := non_edges.image (non_edge_neighborhood_card G)
    (neighbor_sizes.min' (Finset.Nonempty.image h _))
  else
    (Fintype.card α : ℝ)

noncomputable def S (G : SimpleGraph α) : ℝ :=
  open scoped Classical in
  let card := Fintype.card α
  if card < 2 then 0 else
    let degrees := Multiset.ofList (List.map (fun v => G.degree v) Finset.univ.toList)
    let sorted_degrees := degrees.sort (· ≤ ·)
    ↑((sorted_degrees[card - 2]?).getD 0)

/-- The **second-smallest degree** of `G`'s degree sequence — DeLaVina's `σ(G)`
per the WOWII definitions popup (defEntry 65): "order the degree sequence in
nondecreasing order `d₁ ≤ d₂ ≤ … ≤ dₙ`, the second smallest degree of the
sequence is the 2nd entry". For graphs with `n ≤ 1` we conventionally
return `0`. -/
noncomputable def secondSmallestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (degreeSequence G).getD 1 0

/-- The number of triangles (3-cliques) of `G` incident to vertex `v`:
the number of 3-element cliques containing `v`. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card

/-- The length of a graph: the square root of the sum of the squares of degrees. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

/-- The number of vertices of degree k in `G`. -/
def countDegreeK (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = k)).card

/-- The first Zagreb index of `G`. -/
def firstZagrebIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ v, (G.degree v) ^ 2

/-- The second Zagreb index of `G`. -/
noncomputable def secondZagrebIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => G.degree u * G.degree v, by simp [mul_comm]⟩

/-- The first Zagreb coindex of `G`. -/
noncomputable def firstZagrebCoindex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ (compl G).edgeFinset,
    e.lift ⟨fun u v => G.degree u + G.degree v, by simp [add_comm]⟩

/-- The second Zagreb coindex of `G`. -/
noncomputable def secondZagrebCoindex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ (compl G).edgeFinset,
    e.lift ⟨fun u v => G.degree u * G.degree v, by simp [mul_comm]⟩

/-- The forgotten index of `G`. -/
def forgottenIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ v, (G.degree v) ^ 3

/-- The Albertson index of `G`. -/
noncomputable def albertsonIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => Nat.dist (G.degree u) (G.degree v), by simp [Nat.dist_comm]⟩

/-- The Platt index of `G`. -/
noncomputable def plattIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => G.degree u + G.degree v - 2, by simp [add_comm]⟩

/-- The Narumi-Katayama index of `G`. -/
def narumiKatayamaIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∏ v, G.degree v

/-- The first hyper-Zagreb index of `G`. -/
noncomputable def firstHyperZagrebIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (G.degree u + G.degree v) ^ 2, by simp [add_comm]⟩

/-- The second hyper-Zagreb index of `G`. -/
noncomputable def secondHyperZagrebIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (G.degree u * G.degree v) ^ 2, by simp [mul_comm]⟩

/-- The harmonic index of `G`. -/
noncomputable def harmonicIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (2 : ℚ) / ((G.degree u : ℚ) + (G.degree v : ℚ)), by simp [add_comm]⟩

/-- The inverse sum indeg index of `G`. -/
noncomputable def inverseSumIndegIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => ((G.degree u : ℚ) * (G.degree v : ℚ)) / ((G.degree u : ℚ) + (G.degree v : ℚ)),
      by simp [mul_comm, add_comm]⟩

/-- The symmetric division deg index of `G`. -/
noncomputable def symmetricDivisionDegIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (G.degree u : ℚ) / (G.degree v : ℚ) + (G.degree v : ℚ) / (G.degree u : ℚ),
      by simp [add_comm]⟩

/-- The inverse degree index of `G`. -/
noncomputable def inverseDegreeIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ v ∈ Finset.univ.filter (fun v => G.degree v > 0), 1 / (G.degree v : ℚ)

/-- The augmented Zagreb index of `G`. -/
noncomputable def augmentedZagrebIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (((G.degree u : ℚ) * (G.degree v : ℚ)) / ((G.degree u : ℚ) + (G.degree v : ℚ) - 2)) ^ 3,
      by simp [mul_comm, add_comm]⟩

/-- The Randić index of `G`. -/
noncomputable def randicIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => 1 / Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ)),
      by simp [mul_comm]⟩

/-- The Sombor index of `G`. -/
noncomputable def somborIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => Real.sqrt ((G.degree u : ℝ) ^ 2 + (G.degree v : ℝ) ^ 2),
      by simp [add_comm]⟩

/-- The atom-bond connectivity (ABC) index of `G`. -/
noncomputable def abcIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => Real.sqrt (((G.degree u : ℝ) + (G.degree v : ℝ) - 2) / ((G.degree u : ℝ) * (G.degree v : ℝ))),
      by simp [mul_comm, add_comm]⟩

/-- The geometric-arithmetic (GA) index of `G`. -/
noncomputable def gaIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (2 * Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ))) / ((G.degree u : ℝ) + (G.degree v : ℝ)),
      by simp [mul_comm, add_comm]⟩

/-- The reciprocal Randić index of `G`. -/
noncomputable def reciprocalRandicIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ)),
      by simp [mul_comm]⟩

/-- The general sum connectivity index of `G` with exponent `r` (default 0.5). -/
noncomputable def generalSumConnectivityIndex (G : SimpleGraph α) [DecidableRel G.Adj] (r : ℝ := 0.5) : ℝ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => ((G.degree u : ℝ) + (G.degree v : ℝ)) ^ r, by simp [add_comm]⟩

/-- The F-index of `G` (alias for forgotten index). -/
def fIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ := forgottenIndex G

/-- The second largest degree in `G`. -/
noncomputable def secondLargestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  let seq := degreeSequence G
  if seq.length < 2 then 0 else (seq[seq.length - 2]?).getD 0

end SimpleGraph
