# Generative Stack Verification (Self-Contained Bundle)

## A) System Prerequisites

- Lean is managed by elan; lake will fetch deps.
- Linux/macOS expected.
- Network access is required for initial dependency fetch.

## B) One-Command Verification

```bash
./scripts/verify_generative_stack.sh
```

## C) What It Checks

1. **Sorry/Admit Scan** - Zero tolerance for incomplete proofs
2. **Strict Build** - `lake build --wfail` (warnings as errors)
3. **Axiom Audit** - Only standard kernel axioms
4. **Demo Execution** - Key executables run successfully
5. **Hash Verification** - Reproducible source fingerprint

## D) Key Outputs

| Output | Location | Description |
|--------|----------|-------------|
| Build log | `reports/BUILD_TRANSCRIPT_STRICT.txt` | Full compilation output |
| Sorry scan | `reports/SORRY_SCAN.txt` | Should be empty |
| Axiom list | `reports/AXIOM_AUDIT.txt` | Standard axioms only |
| Hash digest | `reports/HASH_DIGEST.txt` | SHA256 of sources |

## E) Key Theorems to Verify

After build, these declarations should exist (verified via `#check` in sanity tests):

```lean
-- Fixed Points / Eigenforms
HeytingLean.LoF.Combinators.EigenformBridge.Y_eigenform
HeytingLean.LoF.Combinators.EigenformBridge.gremlin_fixedpoint
HeytingLean.LoF.Bauer.scottFix_isFixed

-- Surreal Preservation
HeytingLean.Numbers.SurrealCore.PreGame.toIGame_addConway
HeytingLean.Numbers.SurrealCore.PreGame.toIGame_negConway

-- Denotational Soundness
HeytingLean.LoF.Combinators.SKYModel.denote_steps

-- Lawvere Fixed Points
HeytingLean.LoF.Bauer.Lawvere.exists_fixedPoint_of_pointSurjective
HeytingLean.LoF.Bauer.LawvereCategorical.exists_fixedPoint_of_weaklyPointSurjective

-- Logic Ratchet
HeytingLean.Topos.DimensionalRatchet.Sasaki.proj_idempotent
HeytingLean.Topos.DimensionalRatchet.Interface.omlToHeyting_ofTranslate
```

## F) Manual Verification (Alternative)

```bash
# Step 1: Check for sorry
grep -rn "sorry\|admit" HeytingLean/ --include="*.lean"
# Expected: no output

# Step 2: Strict build
lake build --wfail
# Expected: success, 0 warnings

# Step 3: Run demos
lake exe eigenform_demo
lake exe sky_eigenform_demo
lake exe canon_smoke
```

## G) Documentation

| File | Description |
|------|-------------|
| `../01_Lean_Map.md` | Concept → Lean mapping |
| `../02_Proof_Index.md` | Complete theorem index |
| `../03_Reproducibility.md` | Build instructions |
| `../04_Dependencies.md` | Dependency pins |
