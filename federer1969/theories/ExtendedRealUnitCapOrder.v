(** Supporting scalar order laws for the finite metric
    carrier of Federer (1969), 3.2.46, p. 281. They
    prove the metric triangle law and exact agreement at
    small radii; no Hausdorff invariance is assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import constructive_ereal.
From Federer Require Import ExtendedRealUnitCap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [extended_real_unit_cap_monotone]: order
    preservation on original nonnegative distances, technical
    metric support for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_monotone (R : realType) (z w : \bar R) :
  (0 <= z)%E -> (0 <= w)%E -> (z <= w)%E ->
  extended_real_unit_cap z <= extended_real_unit_cap w.
Proof.
case: z=> [r| |] hz.
- case: w=> [s| |] hw hzw.
  + rewrite lee_fin in hzw.
    by rewrite !extended_real_unit_cap_finite le_min !ge_min hzw lexx orbT orTb.
  + rewrite extended_real_unit_cap_posinf; exact: extended_real_unit_cap_le_one.
  + by [].
- case: w=> [s| |] hw hzw.
  + by [].
  + by rewrite extended_real_unit_cap_posinf.
  + by [].
- by [].
Qed.

(** Source for [extended_real_unit_cap_below_original]: the
    finite adapter never enlarges the original nonnegative
    distance, technical support for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_below_original (R : realType) (z : \bar R) :
  (0 <= z)%E -> ((extended_real_unit_cap z)%:E <= z)%E.
Proof.
case: z=> [s| |] hz.
- by rewrite extended_real_unit_cap_finite lee_fin ge_min lexx.
- exact: leey.
- by [].
Qed.

(** Source for [extended_real_unit_cap_small_le]: non-strict
    diameter cutoffs below one retain the original distance
    test, technical support for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_small_le (R : realType) (z : \bar R) (r : R) :
  (0 <= z)%E -> r < 1 ->
  (extended_real_unit_cap z <= r) = (z <= r%:E)%E.
Proof.
case: z=> [s| |] hz hr.
- by rewrite extended_real_unit_cap_finite ge_min (lt_geF hr) orbF lee_fin.
- by rewrite extended_real_unit_cap_posinf (lt_geF hr).
- by [].
Qed.

(** Source for [scalar_unit_cap_subadditive]: elementary
    positive scalar cap inequality supporting the technical
    metric triangle proof for 3.2.46, p. 281. *)
Lemma scalar_unit_cap_subadditive (R : realType) (r s : R) :
  0 <= r -> 0 <= s ->
  Order.min (r+s) 1 <= Order.min r 1 + Order.min s 1.
Proof.
move=> hr hs.
have hTop : Order.min (r+s) 1 <= 1 by rewrite ge_min lexx orbT.
have hSum : Order.min (r+s) 1 <= r+s by rewrite ge_min lexx.
case: (leP r 1)=> hR; case: (leP s 1)=> hS.
- exact: hSum.
- apply: le_trans hTop _; by rewrite lerDr.
- apply: le_trans hTop _; by rewrite lerDl.
- apply: le_trans hTop _; by rewrite lerDl ler01.
Qed.

(** Source for [extended_real_unit_cap_subadditive]:
    subadditivity on original nonnegative extended distances,
    technical support for the metric triangle in 3.2.46,
    p. 281. Infinite component distances are included. *)
Lemma extended_real_unit_cap_subadditive (R : realType) (z w : \bar R) :
  (0 <= z)%E -> (0 <= w)%E ->
  extended_real_unit_cap (z+w)%E <= extended_real_unit_cap z + extended_real_unit_cap w.
Proof.
case: z=> [r| |] hz.
- have hCapZ := extended_real_unit_cap_nonnegative hz.
  case: w=> [s| |] hw.
  + rewrite lee_fin in hz hw.
    rewrite -EFinD !extended_real_unit_cap_finite.
    exact: scalar_unit_cap_subadditive hz hw.
  + rewrite addey // extended_real_unit_cap_posinf lerDr; exact: hCapZ.
  + by [].
- case: w=> [s| |] hw.
  + have hCapW := extended_real_unit_cap_nonnegative hw.
    rewrite addye // extended_real_unit_cap_posinf lerDl; exact: hCapW.
  + rewrite addye // extended_real_unit_cap_posinf; by rewrite lerDl ler01.
  + by [].
- by [].
Qed.

(** Source for [extended_real_unit_cap_small_ball]: at
    every radius below one the capped and original distances
    give exactly the same balls. Technical local representation
    support for 3.2.46, p. 281, including infinite distances. *)
Lemma extended_real_unit_cap_small_ball (R : realType) (z : \bar R) (r : R) :
  (0 <= z)%E -> r < 1 ->
  (extended_real_unit_cap z < r) = (z < r%:E)%E.
Proof.
case: z=> [s| |] hz hr.
- by rewrite extended_real_unit_cap_finite gt_min (le_gtF (ltW hr)) orbF lte_fin.
- by rewrite extended_real_unit_cap_posinf (le_gtF (ltW hr)).
- by [].
Qed.
