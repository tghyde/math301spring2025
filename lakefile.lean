import Lake
open Lake DSL

package «math301spring2025» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.15.0"

@[default_target]
lean_lib «math301spring2025» {
  -- add any library configuration options here
}
