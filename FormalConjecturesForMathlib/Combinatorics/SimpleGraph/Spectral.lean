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

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace SimpleGraph
open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Helper to prove IsHermitian from IsSymm for real matrices. -/
lemma isHermitian_of_isSymm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (h : A.IsSymm) : A.IsHermitian := by
  ext i j
  simp [conjTranspose_apply, h.apply]

/-- Adjacency matrix of `G` over `ℝ` is Hermitian. -/
noncomputable def adjMatrixRealIsHermitian (G : SimpleGraph α) [DecidableRel G.Adj] : IsHermitian (G.adjMatrix ℝ) :=
  isHermitian_of_isSymm (isSymm_adjMatrix G)

/-- Laplacian matrix of `G` over `ℝ` is Hermitian. -/
noncomputable def lapMatrixRealIsHermitian (G : SimpleGraph α) [DecidableRel G.Adj] : IsHermitian (G.lapMatrix ℝ) :=
  isHermitian_of_isSymm (isSymm_lapMatrix G)

/-- Adjacency eigenvalues of `G` sorted descending. -/
noncomputable def adjacencyEigenvalues (G : SimpleGraph α) [DecidableRel G.Adj] : Fin (Fintype.card α) → ℝ :=
  (adjMatrixRealIsHermitian G).eigenvalues₀

/-- Laplacian eigenvalues of `G` sorted descending. -/
noncomputable def laplacianEigenvalues (G : SimpleGraph α) [DecidableRel G.Adj] : Fin (Fintype.card α) → ℝ :=
  (lapMatrixRealIsHermitian G).eigenvalues₀

/-- The spectral radius of `G`. -/
noncomputable def spectralRadius (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let eigs := (List.finRange (Fintype.card α)).map (fun i => abs (G.adjacencyEigenvalues i))
  (eigs.max?).getD 0

/-- The second largest eigenvalue of `G`. -/
noncomputable def secondLargestEigenvalue (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  if h : 2 ≤ Fintype.card α then
    G.adjacencyEigenvalues ⟨1, h⟩
  else
    0

/-- The smallest eigenvalue of `G`. -/
noncomputable def smallestEigenvalue (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  if h : 0 < n then
    G.adjacencyEigenvalues ⟨n - 1, by omega⟩
  else
    0

/-- The nullity of `G`. -/
noncomputable def nullity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ((List.finRange (Fintype.card α)).filter (fun i => G.adjacencyEigenvalues i = 0)).length

/-- The graph energy of `G`. -/
noncomputable def graphEnergy (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ((List.finRange (Fintype.card α)).map (fun i => abs (G.adjacencyEigenvalues i))).sum

/-- The algebraic connectivity of `G`. -/
noncomputable def algebraicConnectivity (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  if h : 2 ≤ n then
    G.laplacianEigenvalues ⟨n - 2, by omega⟩
  else
    0

/-- The largest Laplacian eigenvalue of `G`. -/
noncomputable def largestLaplacianEigenvalue (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  if h : 0 < Fintype.card α then
    G.laplacianEigenvalues ⟨0, h⟩
  else
    0

/-- The Laplacian energy of `G`. -/
noncomputable def laplacianEnergy (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  if 0 < n then
    let mean_deg := (2 * (G.edgeFinset.card : ℝ)) / (n : ℝ)
    ((List.finRange n).map (fun i => abs (G.laplacianEigenvalues i - mean_deg))).sum
  else
    0

/-- The Randić matrix of `G`. -/
noncomputable def randicMatrix (G : SimpleGraph α) [DecidableRel G.Adj] : Matrix α α ℝ :=
  of fun u v => if G.Adj u v then 1 / Real.sqrt (G.degree u * G.degree v) else 0

/-- Randić matrix is symmetric. -/
theorem isSymm_randicMatrix (G : SimpleGraph α) [DecidableRel G.Adj] : (G.randicMatrix).IsSymm := by
  ext u v
  simp [randicMatrix]
  by_cases h : G.Adj u v
  · have h_symm := G.symm h
    simp [h, h_symm, mul_comm]
  · have h2 : ¬ G.Adj v u := fun h2 => h (G.symm h2)
    simp [h, h2]

/-- Randić eigenvalues of `G` sorted descending. -/
noncomputable def randicEigenvalues (G : SimpleGraph α) [DecidableRel G.Adj] : Fin (Fintype.card α) → ℝ :=
  (isHermitian_of_isSymm (isSymm_randicMatrix G)).eigenvalues₀

/-- The Randić energy of `G`. -/
noncomputable def randicEnergy (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ((List.finRange (Fintype.card α)).map (fun i => abs (G.randicEigenvalues i))).sum

/-- Signless Laplacian eigenvalues of `G` sorted descending. -/
noncomputable def signlessLaplacianEigenvalues (G : SimpleGraph α) [DecidableRel G.Adj] : Fin (Fintype.card α) → ℝ :=
  let Q := G.degMatrix ℝ + G.adjMatrix ℝ
  have hQ : Q.IsSymm := (isSymm_degMatrix G).add (isSymm_adjMatrix G)
  (isHermitian_of_isSymm hQ).eigenvalues₀

/-- The incidence energy of `G`. -/
noncomputable def incidenceEnergy (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ((List.finRange (Fintype.card α)).map (fun i => Real.sqrt (G.signlessLaplacianEigenvalues i))).sum

/-- The Estrada index of `G`. -/
noncomputable def estradaIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  ((List.finRange (Fintype.card α)).map (fun i => Real.exp (G.adjacencyEigenvalues i))).sum

/-- The number of spanning trees of `G`. -/
noncomputable def numberOfSpanningTrees (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  if n <= 1 then
    n
  else if G.Connected then
    let eigs := (List.finRange (n - 1)).map (fun i => G.laplacianEigenvalues ⟨i.val, by omega⟩)
    eigs.prod / n
  else
    0

/-- The Kirby index of `G`. -/
noncomputable def kirbyIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  if n <= 1 then
    0
  else if G.Connected then
    let sum_recip := ((List.finRange (n - 1)).map (fun i => 1 / G.laplacianEigenvalues ⟨i.val, by omega⟩)).sum
    (n : ℝ) * sum_recip
  else
    0

/-- The largest normalized Laplacian eigenvalue of `G`. -/
noncomputable def largestNormalizedLaplacianEigenvalue (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let n := Fintype.card α
  if h : 0 < n then
    1 - G.randicEigenvalues ⟨n - 1, by omega⟩
  else
    0

end SimpleGraph
