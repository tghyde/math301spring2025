import Lake
open Lake DSL

-- package math301 where
--   moreServerArgs := #[
--     "-Dlinter.unusedVariables=false", -- ignores unused variables
--     "-DquotPrecheck=false",
--     "-DwarningAsError=false",
--     "-Dpp.unicode.fun=true"  -- pretty-prints `fun a ↦ b`
--   ]

package math301 where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedTactic, false⟩
  ]

lean_lib Library


require "leanprover-community" / "mathlib" @ git "v4.15.0"
