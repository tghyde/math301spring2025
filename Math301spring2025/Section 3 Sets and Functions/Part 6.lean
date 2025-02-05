/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Library.Theory.S3.P3
import Library.Theory.S3.P4

/-
## Sets and Functions
## Part 6: Cantor-Schoder-Bernstein Theorem
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false


variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

namespace Math301

/-
We have now learned enough that we can try tackling something more challenging. The `Cantor-Schroder-Bernstein theorem` says that if `X` and `Y` are sets and there exists injective functions `f : X → Y` and `g : Y → X`, then there exists a bijection `h : X → Y`. In other words, `X ≤ Y` and `Y ≤ X` imply `X ∼ Y`. For finite sets this is not so hard to show, but for infinite sets it's tough. There are several proofs of this theorem, I have provided one on Moodle that is conducive to formalization. If you'd like an extra challenge, try to prove the theorem yourself! You may need to prove some lemmas or define some auxiliary functions along the way. Good luck!
-/

-- The proof requires classical reasoning
open Classical

theorem cantor_schroder_bernstein
  (f : X → Y)
  (hf : is_injective f)
  (g : Y → X)
  (hg : is_injective g)
  : ∃ h : X → Y, is_bijective h := by
    sorry
    done

end Math301
