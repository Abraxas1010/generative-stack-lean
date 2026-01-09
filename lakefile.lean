import Lake
open Lake DSL

package «GenerativeStack» where
  -- Standalone package for the Generative Stack formalization

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

-- Mathlib auxiliary pins (for reproducibility)
require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "91c18fa62838ad0ab7384c03c9684d99d306e1da"
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "dea6a3361fa36d5a13f87333dc506ada582e025c"
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "725ac8cd67acd70a7beaf47c3725e23484c1ef50"
require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "d768126816be17600904726ca7976b185786e6b9"
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "8da40b72fece29b7d3fe3d768bac4c8910ce9bee"

-- Combinatorial game theory (for surreal bridge)
require CombinatorialGames from git
  "https://github.com/vihdzp/combinatorial-games" @ "a195e146cdb97ca2e98a4bf923f50b559a07044a"

@[default_target]
lean_lib «HeytingLean» where
  -- Main library containing the generative stack formalization

-- Demo executables
lean_exe eigenform_demo where
  root := `HeytingLean.LoF.Combinators.EigenformBridge
  supportInterpreter := true

lean_exe sky_demo where
  root := `HeytingLean.LoF.Combinators.SKY
  supportInterpreter := true
