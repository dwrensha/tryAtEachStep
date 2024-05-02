import Lake
open Lake DSL

package «tryAtEachStep» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require std from git "https://github.com/leanprover/std4" @ "v4.8.0-rc1"

@[default_target]
lean_exe «tryAtEachStep» where
  root := `tryAtEachStep
  supportInterpreter := true
