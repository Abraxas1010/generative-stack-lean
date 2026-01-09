import HeytingLean.Numbers.Surreal.BridgeToPGame

/-!
# SurrealCore → IGame: arithmetic preservation (noncomputable bridge)

`HeytingLean.Numbers.Surreal.BridgeToPGame` defines `SurrealCore.PreGame.toIGame`, a
noncomputable bridge from the repo’s lightweight `{L|R}` representation into the verified
`CombinatorialGames.Game.IGame` development.

This file adds:

* a *structural* (non-fuel) Conway-style addition and negation on `SurrealCore.PreGame`; and
* preservation theorems showing that `toIGame` commutes with those operations.

We keep this separate from the executable `SurrealCore.add/neg` (which are fuel-bounded
approximations for demos) because `IGame`’s operations are definitional/recursive rather than
fuel-bounded.
-/

namespace HeytingLean
namespace Numbers
namespace SurrealCore

namespace PreGame

/-! ## Size-of helpers for termination proofs -/

private theorem sizeOf_lt_sizeOf_list_of_mem [SizeOf α] {x : α} {xs : List α} (hx : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => cases hx
  | cons h t ih =>
      cases hx with
      | head =>
          have hpos : 0 < 1 + sizeOf t := by
            have : 0 < sizeOf t + 1 := Nat.succ_pos _
            exact lt_of_lt_of_eq this (by simp [Nat.add_comm])
          have hlt : sizeOf x < sizeOf x + (1 + sizeOf t) :=
            Nat.lt_add_of_pos_right hpos
          refine lt_of_lt_of_eq hlt ?_
          rw [List.cons.sizeOf_spec]
          calc
            sizeOf x + (1 + sizeOf t) = 1 + (sizeOf x + sizeOf t) := by
              exact Nat.add_left_comm (sizeOf x) 1 (sizeOf t)
            _ = 1 + sizeOf x + sizeOf t := by
              exact (Eq.symm (Nat.add_assoc 1 (sizeOf x) (sizeOf t)))
      | tail _ hx1 =>
          have hlt : sizeOf x < sizeOf t := ih hx1
          have htpos : 0 < 1 + sizeOf h := by
            have : 0 < sizeOf h + 1 := Nat.succ_pos _
            exact lt_of_lt_of_eq this (by simp [Nat.add_comm])
          have ht_lt : sizeOf t < sizeOf t + (1 + sizeOf h) :=
            Nat.lt_add_of_pos_right htpos
          have ht_lt' : sizeOf t < sizeOf (h :: t) := by
            refine lt_of_lt_of_eq ht_lt ?_
            rw [List.cons.sizeOf_spec]
            calc
              sizeOf t + (1 + sizeOf h) = 1 + (sizeOf t + sizeOf h) := by
                exact Nat.add_left_comm (sizeOf t) 1 (sizeOf h)
              _ = 1 + sizeOf t + sizeOf h := by
                exact (Eq.symm (Nat.add_assoc 1 (sizeOf t) (sizeOf h)))
              _ = 1 + sizeOf h + sizeOf t := by
                exact Nat.add_right_comm 1 (sizeOf t) (sizeOf h)
          exact Nat.lt_trans hlt ht_lt'

private theorem sizeOf_lt_sizeOf_pregame_mk_left
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ L) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf L := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf R + sizeOf birth) := by
    refine lt_of_lt_of_eq (Nat.succ_pos (sizeOf R + sizeOf birth)) ?_
    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  have hlt : sizeOf L < sizeOf L + (1 + sizeOf R + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hL : sizeOf L < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hL

private theorem sizeOf_lt_sizeOf_pregame_mk_right
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ R) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf R := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf L + sizeOf birth) := by
    refine lt_of_lt_of_eq (Nat.succ_pos (sizeOf L + sizeOf birth)) ?_
    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  have hlt : sizeOf R < sizeOf R + (1 + sizeOf L + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hR : sizeOf R < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hR

private theorem sizeOf_lt_sizeOf_left (g : PreGame) {x : PreGame} (hx : x ∈ g.L) :
    sizeOf x < sizeOf g := by
  cases g with
  | mk L R birth =>
      simpa using (sizeOf_lt_sizeOf_pregame_mk_left L R birth hx)

private theorem sizeOf_lt_sizeOf_right (g : PreGame) {x : PreGame} (hx : x ∈ g.R) :
    sizeOf x < sizeOf g := by
  cases g with
  | mk L R birth =>
      simpa using (sizeOf_lt_sizeOf_pregame_mk_right L R birth hx)

/-! ## Structural Conway operations on `SurrealCore.PreGame` -/

/-- Conway-style (structural) negation on `SurrealCore.PreGame`, using `PreGame.build`
to maintain consistent birthdays. -/
noncomputable def negConway : PreGame → PreGame
  | { L := L, R := R, birth := _ } =>
      PreGame.build (R.map negConway) (L.map negConway)
termination_by g => sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_lt_sizeOf_pregame_mk_left _ _ _ (by assumption)
    | exact sizeOf_lt_sizeOf_pregame_mk_right _ _ _ (by assumption)

/-- Conway-style (structural) addition on `SurrealCore.PreGame`, using `PreGame.build`
to maintain consistent birthdays. -/
noncomputable def addConway : PreGame → PreGame → PreGame
  | x, y =>
      let L :=
        (x.L.map (fun xl => addConway xl y)) ++
        (y.L.map (fun yl => addConway x yl))
      let R :=
        (x.R.map (fun xr => addConway xr y)) ++
        (y.R.map (fun yr => addConway x yr))
      PreGame.build L R
termination_by x y => (sizeOf x, sizeOf y)
decreasing_by
  all_goals
    first
    | -- `xl ∈ x.L`
      exact Prod.Lex.left (b₁ := sizeOf y) (b₂ := sizeOf y) (sizeOf_lt_sizeOf_left (g := x) (by assumption))
    | -- `yl ∈ y.L`
      exact Prod.Lex.right (a := sizeOf x) (sizeOf_lt_sizeOf_left (g := y) (by assumption))
    | -- `xr ∈ x.R`
      exact Prod.Lex.left (b₁ := sizeOf y) (b₂ := sizeOf y) (sizeOf_lt_sizeOf_right (g := x) (by assumption))
    | -- `yr ∈ y.R`
      exact Prod.Lex.right (a := sizeOf x) (sizeOf_lt_sizeOf_right (g := y) (by assumption))

private lemma addConway_L (x y : PreGame) :
    (addConway x y).L =
      (x.L.map (fun xl => addConway xl y)) ++ (y.L.map (fun yl => addConway x yl)) := by
  -- Unfold only the outer `addConway x y`; keep recursive calls under lambdas opaque.
  conv_lhs => unfold addConway
  simp [PreGame.build]

private lemma addConway_R (x y : PreGame) :
    (addConway x y).R =
      (x.R.map (fun xr => addConway xr y)) ++ (y.R.map (fun yr => addConway x yr)) := by
  conv_lhs => unfold addConway
  simp [PreGame.build]

/-! ## Preservation theorems for `toIGame` -/

private def setOfList (xs : List α) : Set α :=
  Set.range (fun i : Fin xs.length => xs.get i)

private instance instSmall_setOfList (xs : List α) : Small (setOfList xs) := by
  dsimp [setOfList]
  infer_instance

private lemma mem_setOfList_iff {α : Type _} (xs : List α) (x : α) :
    x ∈ setOfList xs ↔ x ∈ xs := by
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem xs i
  · intro hx
    rcases (List.mem_iff_get.1 hx) with ⟨i, hi⟩
    exact ⟨i, hi⟩

private lemma setOfList_map {α β : Type _} (xs : List α) (f : α → β) :
    setOfList (xs.map f) = f '' setOfList xs := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ xs.map f := (mem_setOfList_iff (xs := xs.map f) (x := y)).1 hy
    rcases List.mem_map.1 hy' with ⟨x, hx, rfl⟩
    rcases (List.mem_iff_get.1 hx) with ⟨i, hi⟩
    refine ⟨xs.get i, ?_, ?_⟩
    · exact ⟨i, rfl⟩
    · exact congrArg f hi
  · rintro ⟨y', hy', rfl⟩
    rcases hy' with ⟨i, rfl⟩
    exact (mem_setOfList_iff (xs := xs.map f) (x := f (xs.get i))).2 (by
      refine List.mem_map.2 ?_
      exact ⟨xs.get i, List.get_mem xs i, rfl⟩)

private lemma setOfList_append {α : Type _} (xs ys : List α) :
    setOfList (xs ++ ys) = setOfList xs ∪ setOfList ys := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ xs ++ ys := (mem_setOfList_iff (xs := xs ++ ys) (x := x)).1 hx
    rcases (List.mem_append.1 hx') with hx' | hx'
    · exact Or.inl ((mem_setOfList_iff (xs := xs) (x := x)).2 hx')
    · exact Or.inr ((mem_setOfList_iff (xs := ys) (x := x)).2 hx')
  · intro hx
    rcases hx with hx | hx
    · have hx' : x ∈ xs := (mem_setOfList_iff (xs := xs) (x := x)).1 hx
      exact (mem_setOfList_iff (xs := xs ++ ys) (x := x)).2 (List.mem_append.2 (Or.inl hx'))
    · have hx' : x ∈ ys := (mem_setOfList_iff (xs := ys) (x := x)).1 hx
      exact (mem_setOfList_iff (xs := xs ++ ys) (x := x)).2 (List.mem_append.2 (Or.inr hx'))

private lemma toIGame_eq_ofSets (x : PreGame) :
    toIGame x = !{setOfList (x.L.map toIGame) | setOfList (x.R.map toIGame)} := by
  cases x with
  | mk L R b =>
      simp [toIGame, setOfList]

/-- `toIGame` commutes with Conway negation. -/
theorem toIGame_negConway (x : PreGame) :
    toIGame (negConway x) = - toIGame x := by
  classical
  refine (measure (fun g : PreGame => sizeOf g)).wf.induction x
    (C := fun g => toIGame (negConway g) = -toIGame g) ?_
  intro g ih
  cases g with
  | mk L R b =>
      let g0 : PreGame := { L := L, R := R, birth := b }
      have hmapL :
          L.map (fun x => toIGame (negConway x)) = L.map (fun x => -toIGame x) := by
        refine List.map_congr_left ?_
        intro x hx
        exact ih x (sizeOf_lt_sizeOf_left (g := g0) hx)
      have hmapR :
          R.map (fun x => toIGame (negConway x)) = R.map (fun x => -toIGame x) := by
        refine List.map_congr_left ?_
        intro x hx
        exact ih x (sizeOf_lt_sizeOf_right (g := g0) hx)

      have hnegL :
          setOfList (L.map (fun x => -toIGame x)) = -setOfList (L.map toIGame) := by
        calc
          setOfList (L.map (fun x => -toIGame x))
              = setOfList ((L.map toIGame).map Neg.neg) := by
                  refine congrArg setOfList ?_
                  simp [List.map_map, Function.comp]
          _ = Neg.neg '' setOfList (L.map toIGame) := by
                  exact setOfList_map (xs := L.map toIGame) (f := Neg.neg)
          _ = -setOfList (L.map toIGame) := by
                  simp [Set.image_neg_eq_neg]

      have hnegR :
          setOfList (R.map (fun x => -toIGame x)) = -setOfList (R.map toIGame) := by
        calc
          setOfList (R.map (fun x => -toIGame x))
              = setOfList ((R.map toIGame).map Neg.neg) := by
                  refine congrArg setOfList ?_
                  simp [List.map_map, Function.comp]
          _ = Neg.neg '' setOfList (R.map toIGame) := by
                  exact setOfList_map (xs := R.map toIGame) (f := Neg.neg)
          _ = -setOfList (R.map toIGame) := by
                  simp [Set.image_neg_eq_neg]

      -- Rewrite both sides as `!{ | }` and compare the defining move sets.
      -- Left side: `toIGame` of the structurally negated pregame.
      have hLHS :
          toIGame (negConway g0) =
            !{-setOfList (R.map toIGame) | -setOfList (L.map toIGame)} := by
        -- Convert `toIGame` to `ofSets`, unfold `negConway` once, then rewrite move sets.
        have hL : setOfList ((R.map negConway).map toIGame) = -setOfList (R.map toIGame) := by
          calc
            setOfList ((R.map negConway).map toIGame)
                = setOfList (R.map (fun x => x.negConway.toIGame)) := by
                    refine congrArg setOfList ?_
                    -- Avoid `simp` here to keep `List.map` in a stable normal form.
                    -- `List.map_map` produces a composed function; we rewrite it via pointwise `rfl`.
                    have :
                        (R.map negConway).map toIGame =
                          R.map (toIGame ∘ negConway) := by
                      simp [List.map_map]
                    -- Now replace `toIGame ∘ negConway` with dot-notation.
                    -- (This is definitional, but we do it explicitly to avoid `simp` loops.)
                    calc
                      (R.map negConway).map toIGame
                          = R.map (toIGame ∘ negConway) := this
                      _ = R.map (fun x => x.negConway.toIGame) := by
                          refine List.map_congr_left ?_
                          intro x hx
                          rfl
            _ = setOfList (R.map (fun x => -toIGame x)) := by
                    simpa using congrArg setOfList hmapR
            _ = -setOfList (R.map toIGame) := by
                    exact hnegR
        have hR : setOfList ((L.map negConway).map toIGame) = -setOfList (L.map toIGame) := by
          calc
            setOfList ((L.map negConway).map toIGame)
                = setOfList (L.map (fun x => x.negConway.toIGame)) := by
                    refine congrArg setOfList ?_
                    have :
                        (L.map negConway).map toIGame =
                          L.map (toIGame ∘ negConway) := by
                      simp [List.map_map]
                    calc
                      (L.map negConway).map toIGame
                          = L.map (toIGame ∘ negConway) := this
                      _ = L.map (fun x => x.negConway.toIGame) := by
                          refine List.map_congr_left ?_
                          intro x hx
                          rfl
            _ = setOfList (L.map (fun x => -toIGame x)) := by
                    simpa using congrArg setOfList hmapL
            _ = -setOfList (L.map toIGame) := by
                    exact hnegL

        calc
          toIGame (negConway g0)
              = !{setOfList ((negConway g0).L.map toIGame) | setOfList ((negConway g0).R.map toIGame)} := by
                  simpa using (toIGame_eq_ofSets (x := negConway g0))
          _ = !{setOfList ((R.map negConway).map toIGame) | setOfList ((L.map negConway).map toIGame)} := by
                  simp [negConway, g0, PreGame.build]
          _ = !{-setOfList (R.map toIGame) | -setOfList (L.map toIGame)} := by
                  exact (IGame.ofSets_inj).2 ⟨hL, hR⟩

      -- Right side: negate `toIGame g0` using the CGT lemma `neg_ofSets`.
      have hRHS :
          (-toIGame g0) = !{-setOfList (R.map toIGame) | -setOfList (L.map toIGame)} := by
        -- `toIGame g0` is an `ofSets`-game with the list-range sets, then `neg_ofSets` swaps/negates.
        calc
          (-toIGame g0)
              = -!{setOfList (L.map toIGame) | setOfList (R.map toIGame)} := by
                  simp [g0, toIGame_eq_ofSets]
          _ = !{-setOfList (R.map toIGame) | -setOfList (L.map toIGame)} := by
                  simp

      exact hLHS.trans hRHS.symm

/-- `toIGame` commutes with Conway addition. -/
theorem toIGame_addConway (x y : PreGame) :
    toIGame (addConway x y) = toIGame x + toIGame y := by
  classical
  refine (measure (fun p : PreGame × PreGame => sizeOf p.1 + sizeOf p.2)).wf.induction (x, y)
    (C := fun p => toIGame (addConway p.1 p.2) = toIGame p.1 + toIGame p.2) ?_
  intro p ih
  rcases p with ⟨x, y⟩
  cases x with
  | mk xL xR xb =>
    cases y with
    | mk yL yR yb =>
      let x0 : PreGame := { L := xL, R := xR, birth := xb }
      let y0 : PreGame := { L := yL, R := yR, birth := yb }

      have ih_xL :
          xL.map (fun xl => toIGame (addConway xl y0)) = xL.map (fun xl => toIGame xl + toIGame y0) := by
        refine List.map_congr_left ?_
        intro xl hxl
        have hlt : sizeOf xl + sizeOf y0 < sizeOf x0 + sizeOf y0 :=
          Nat.add_lt_add_right (sizeOf_lt_sizeOf_left (g := x0) hxl) _
        simpa [x0, y0] using ih (xl, y0) hlt

      have ih_xR :
          xR.map (fun xr => toIGame (addConway xr y0)) = xR.map (fun xr => toIGame xr + toIGame y0) := by
        refine List.map_congr_left ?_
        intro xr hxr
        have hlt : sizeOf xr + sizeOf y0 < sizeOf x0 + sizeOf y0 :=
          Nat.add_lt_add_right (sizeOf_lt_sizeOf_right (g := x0) hxr) _
        simpa [x0, y0] using ih (xr, y0) hlt

      have ih_yL :
          yL.map (fun yl => toIGame (addConway x0 yl)) = yL.map (fun yl => toIGame x0 + toIGame yl) := by
        refine List.map_congr_left ?_
        intro yl hyl
        have hlt : sizeOf x0 + sizeOf yl < sizeOf x0 + sizeOf y0 :=
          Nat.add_lt_add_left (sizeOf_lt_sizeOf_left (g := y0) hyl) _
        simpa [x0, y0] using ih (x0, yl) hlt

      have ih_yR :
          yR.map (fun yr => toIGame (addConway x0 yr)) = yR.map (fun yr => toIGame x0 + toIGame yr) := by
        refine List.map_congr_left ?_
        intro yr hyr
        have hlt : sizeOf x0 + sizeOf yr < sizeOf x0 + sizeOf y0 :=
          Nat.add_lt_add_left (sizeOf_lt_sizeOf_right (g := y0) hyr) _
        simpa [x0, y0] using ih (x0, yr) hlt

      -- Turn both sides into `!{ | }` and compare their defining move sets.
      -- Left-hand side: the bridge applied to the structural sum.
      have hLHS :
          toIGame (addConway x0 y0) =
            !{(· + toIGame y0) '' setOfList (xL.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yL.map toIGame) |
              (· + toIGame y0) '' setOfList (xR.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yR.map toIGame)} := by
        -- Expand the `PreGame.build`-based definition of `addConway`.
        -- Use IH to simplify `toIGame (addConway _ _)` inside the lists, then
        -- use `setOfList_map` and `setOfList_append` to turn list concatenation into union.
        have hleft :
            setOfList (((xL.map (fun xl => addConway xl y0)) ++ (yL.map (fun yl => addConway x0 yl))).map toIGame)
              =
              (· + toIGame y0) '' setOfList (xL.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yL.map toIGame) := by
          -- rewrite the mapped list using the IH equations
          calc
            setOfList (((xL.map (fun xl => addConway xl y0)) ++ (yL.map (fun yl => addConway x0 yl))).map toIGame)
                = setOfList ((xL.map (fun xl => toIGame (addConway xl y0))) ++ (yL.map (fun yl => toIGame (addConway x0 yl)))) := by
                    refine congrArg setOfList ?_
                    -- Avoid `simp [List.map_map]` producing composed functions.
                    have hx :
                        (xL.map (fun xl => addConway xl y0)).map toIGame =
                          xL.map (fun xl => toIGame (addConway xl y0)) := by
                      calc
                        (xL.map (fun xl => addConway xl y0)).map toIGame
                            = xL.map (toIGame ∘ fun xl => addConway xl y0) := by
                                simp [List.map_map]
                        _ = xL.map (fun xl => toIGame (addConway xl y0)) := by
                                refine List.map_congr_left ?_
                                intro xl hxl
                                rfl
                    have hy :
                        (yL.map (fun yl => addConway x0 yl)).map toIGame =
                          yL.map (fun yl => toIGame (addConway x0 yl)) := by
                      calc
                        (yL.map (fun yl => addConway x0 yl)).map toIGame
                            = yL.map (toIGame ∘ fun yl => addConway x0 yl) := by
                                simp [List.map_map]
                        _ = yL.map (fun yl => toIGame (addConway x0 yl)) := by
                                refine List.map_congr_left ?_
                                intro yl hyl
                                rfl
                    -- Avoid `simp` here: `List.map_map` is a simp lemma and would reintroduce
                    -- composed functions, which are awkward to normalize under `--wfail`.
                    rw [List.map_append]
                    rw [hx, hy]
            _ = setOfList (xL.map (fun xl => toIGame (addConway xl y0))) ∪
                  setOfList (yL.map (fun yl => toIGame (addConway x0 yl))) := by
                    simp [setOfList_append]
            _ = setOfList (xL.map (fun xl => toIGame xl + toIGame y0)) ∪
                  setOfList (yL.map (fun yl => toIGame x0 + toIGame yl)) := by
                    have hx :
                        setOfList (xL.map (fun xl => toIGame (addConway xl y0))) =
                          setOfList (xL.map (fun xl => toIGame xl + toIGame y0)) := by
                      simpa using congrArg setOfList ih_xL
                    have hy :
                        setOfList (yL.map (fun yl => toIGame (addConway x0 yl))) =
                          setOfList (yL.map (fun yl => toIGame x0 + toIGame yl)) := by
                      simpa using congrArg setOfList ih_yL
                    rw [hx, hy]
            _ = (· + toIGame y0) '' setOfList (xL.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yL.map toIGame) := by
                    -- convert each `setOfList (map ..)` into an image over the base move-set
                    have hx :
                        setOfList (xL.map (fun xl => toIGame xl + toIGame y0)) =
                          (· + toIGame y0) '' setOfList (xL.map toIGame) := by
                      calc
                        setOfList (xL.map (fun xl => toIGame xl + toIGame y0))
                            = setOfList ((xL.map toIGame).map (fun a => a + toIGame y0)) := by
                                refine congrArg setOfList ?_
                                induction xL with
                                | nil => rfl
                                | cons a tl ih =>
                                    simp [List.map]
                        _ = (fun a => a + toIGame y0) '' setOfList (xL.map toIGame) := by
                                exact setOfList_map (xs := xL.map toIGame) (f := fun a => a + toIGame y0)
                    have hy :
                        setOfList (yL.map (fun yl => toIGame x0 + toIGame yl)) =
                          (toIGame x0 + ·) '' setOfList (yL.map toIGame) := by
                      calc
                        setOfList (yL.map (fun yl => toIGame x0 + toIGame yl))
                            = setOfList ((yL.map toIGame).map (fun a => toIGame x0 + a)) := by
                                refine congrArg setOfList ?_
                                induction yL with
                                | nil => rfl
                                | cons a tl ih =>
                                    simp [List.map]
                        _ = (fun a => toIGame x0 + a) '' setOfList (yL.map toIGame) := by
                                exact setOfList_map (xs := yL.map toIGame) (f := fun a => toIGame x0 + a)
                    rw [hx, hy]

        have hright :
            setOfList (((xR.map (fun xr => addConway xr y0)) ++ (yR.map (fun yr => addConway x0 yr))).map toIGame)
              =
              (· + toIGame y0) '' setOfList (xR.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yR.map toIGame) := by
          calc
            setOfList (((xR.map (fun xr => addConway xr y0)) ++ (yR.map (fun yr => addConway x0 yr))).map toIGame)
                = setOfList ((xR.map (fun xr => toIGame (addConway xr y0))) ++ (yR.map (fun yr => toIGame (addConway x0 yr)))) := by
                    refine congrArg setOfList ?_
                    have hx :
                        (xR.map (fun xr => addConway xr y0)).map toIGame =
                          xR.map (fun xr => toIGame (addConway xr y0)) := by
                      calc
                        (xR.map (fun xr => addConway xr y0)).map toIGame
                            = xR.map (toIGame ∘ fun xr => addConway xr y0) := by
                                simp [List.map_map]
                        _ = xR.map (fun xr => toIGame (addConway xr y0)) := by
                                refine List.map_congr_left ?_
                                intro xr hxr
                                rfl
                    have hy :
                        (yR.map (fun yr => addConway x0 yr)).map toIGame =
                          yR.map (fun yr => toIGame (addConway x0 yr)) := by
                      calc
                        (yR.map (fun yr => addConway x0 yr)).map toIGame
                            = yR.map (toIGame ∘ fun yr => addConway x0 yr) := by
                                simp [List.map_map]
                        _ = yR.map (fun yr => toIGame (addConway x0 yr)) := by
                                refine List.map_congr_left ?_
                                intro yr hyr
                                rfl
                    rw [List.map_append]
                    rw [hx, hy]
            _ = setOfList (xR.map (fun xr => toIGame (addConway xr y0))) ∪
                  setOfList (yR.map (fun yr => toIGame (addConway x0 yr))) := by
                    simp [setOfList_append]
            _ = setOfList (xR.map (fun xr => toIGame xr + toIGame y0)) ∪
                  setOfList (yR.map (fun yr => toIGame x0 + toIGame yr)) := by
                    have hx : setOfList (xR.map (fun xr => toIGame (addConway xr y0))) =
                        setOfList (xR.map (fun xr => toIGame xr + toIGame y0)) := by
                      simpa using congrArg setOfList ih_xR
                    have hy : setOfList (yR.map (fun yr => toIGame (addConway x0 yr))) =
                        setOfList (yR.map (fun yr => toIGame x0 + toIGame yr)) := by
                      simpa using congrArg setOfList ih_yR
                    rw [hx, hy]
            _ = (· + toIGame y0) '' setOfList (xR.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yR.map toIGame) := by
                    have hx :
                        setOfList (xR.map (fun xr => toIGame xr + toIGame y0)) =
                          (· + toIGame y0) '' setOfList (xR.map toIGame) := by
                      calc
                        setOfList (xR.map (fun xr => toIGame xr + toIGame y0))
                            = setOfList ((xR.map toIGame).map (fun a => a + toIGame y0)) := by
                                refine congrArg setOfList ?_
                                induction xR with
                                | nil => rfl
                                | cons a tl ih =>
                                    simp [List.map]
                        _ = (fun a => a + toIGame y0) '' setOfList (xR.map toIGame) := by
                                exact setOfList_map (xs := xR.map toIGame) (f := fun a => a + toIGame y0)
                    have hy :
                        setOfList (yR.map (fun yr => toIGame x0 + toIGame yr)) =
                          (toIGame x0 + ·) '' setOfList (yR.map toIGame) := by
                      calc
                        setOfList (yR.map (fun yr => toIGame x0 + toIGame yr))
                            = setOfList ((yR.map toIGame).map (fun a => toIGame x0 + a)) := by
                                refine congrArg setOfList ?_
                                induction yR with
                                | nil => rfl
                                | cons a tl ih =>
                                    simp [List.map]
                        _ = (fun a => toIGame x0 + a) '' setOfList (yR.map toIGame) := by
                                exact setOfList_map (xs := yR.map toIGame) (f := fun a => toIGame x0 + a)
                    rw [hx, hy]

        -- Now unfold `addConway` once and rewrite the move sets using `hleft`/`hright`.
        -- We avoid `simp [addConway]` here to keep the recursive calls opaque.
        -- Put the left-hand side into `!{ | }` form using the bridge lemma, then rewrite the sets.
        -- `PreGame.build` only affects birthdays, which `toIGame` ignores.
        have hcut :
            toIGame (addConway x0 y0) =
              !{setOfList (((xL.map (fun xl => addConway xl y0)) ++ (yL.map (fun yl => addConway x0 yl))).map toIGame) |
                setOfList (((xR.map (fun xr => addConway xr y0)) ++ (yR.map (fun yr => addConway x0 yr))).map toIGame)} := by
          -- Start from the generic `ofSets`-shape, then rewrite `.L`/`.R` of the *outer*
          -- `addConway x0 y0` without unfolding recursive calls under lambdas.
          have h0 :
              toIGame (addConway x0 y0) =
                !{setOfList ((addConway x0 y0).L.map toIGame) | setOfList ((addConway x0 y0).R.map toIGame)} := by
            simpa using (toIGame_eq_ofSets (x := addConway x0 y0))

          -- Field equations for the outer Conway sum.
          have haddL :
              (addConway x0 y0).L =
                (xL.map (fun xl => addConway xl y0)) ++ (yL.map (fun yl => addConway x0 yl)) := by
            simpa [x0, y0] using (addConway_L x0 y0)
          have haddR :
              (addConway x0 y0).R =
                (xR.map (fun xr => addConway xr y0)) ++ (yR.map (fun yr => addConway x0 yr)) := by
            simpa [x0, y0] using (addConway_R x0 y0)

          -- Use `ofSets_inj` to avoid dependent rewriting issues with the implicit `Small` instances.
          refine h0.trans ?_
          apply (IGame.ofSets_inj).2
          constructor
          · -- left-move set
            -- Rewrite `.L` using `haddL`.
            rw [haddL]
          · -- right-move set
            rw [haddR]
        -- Finish `hLHS` by rewriting the left/right move sets.
        -- The goal has already been rewritten to the bridge form.
        -- Use `hcut` to get the concrete `!{ | }`-shape.
        -- Rewrite the left and right move sets inside `!{ | }` using `hleft` and `hright`.
        refine hcut.trans ?_
        exact (IGame.ofSets_inj).2 ⟨hleft, hright⟩

      -- Right-hand side: use CGT's characterization of addition.
      have hRHS :
          toIGame x0 + toIGame y0 =
            !{(· + toIGame y0) '' setOfList (xL.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yL.map toIGame) |
              (· + toIGame y0) '' setOfList (xR.map toIGame) ∪ (toIGame x0 + ·) '' setOfList (yR.map toIGame)} := by
        -- `IGame.add_eq` + the fact that `toIGame` is built from `ofSets` using list-range sets.
        simpa [x0, y0, toIGame_eq_ofSets] using (IGame.add_eq (toIGame x0) (toIGame y0))

      have h : toIGame (addConway x0 y0) = toIGame x0 + toIGame y0 := by
        exact hLHS.trans hRHS.symm
      simpa [x0, y0] using h

end PreGame

end SurrealCore
end Numbers
end HeytingLean
