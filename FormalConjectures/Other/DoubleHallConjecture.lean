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
import FormalConjectures.Util.ProblemImports

namespace DoubleHallConjecture

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The statement of the double Hall cycle conjecture, proposed by Nika Salia. -/
def double_hall_cycle_conjecture (G : SimpleGraph α) [DecidableRel G.Adj] (A B : Finset α) : Prop :=
  G.Colorable 2 →
  (∀ S ⊆ A, 2 ≤ S.card → S.card ≤ (hatN G B S).card) →
  ∃ (v : α) (c : G.Walk v v), c.IsCycle ∧ ∀ a ∈ A, a ∈ c.support

end DoubleHallConjecture
