(** Public scalar cap laws supporting the finite metric
    carrier for Federer (1969), 3.2.46, p. 281. The
    original extended curve distance remains unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealUnitCapUP ExtendedRealUnitCapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [extended_real_unit_cap]: the opaque technical
    finite cap for metric support in 3.2.46, p. 281. Its
    implementation is hidden and is used through its scalar laws. *)
Definition extended_real_unit_cap (R : realType) (z : \bar R) : R :=
  @ExtendedRealUnitCap.value R z.
Arguments extended_real_unit_cap {R} z.

(** Source for [extended_real_unit_cap_finite]: exact finite
    cap formula, technical support for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_finite (R : realType) (r : R) :
  extended_real_unit_cap r%:E = Order.min r 1.
Proof. exact (@unit_cap_finite R (@extended_real_unit_cap R) (ExtendedRealUnitCap.laws R) r). Qed.

(** Source for [extended_real_unit_cap_posinf]: a disconnected
    component has capped separation one, technical support for
    3.2.46, p. 281, without a finite-path-distance claim. *)
Lemma extended_real_unit_cap_posinf (R : realType) :
  extended_real_unit_cap (+oo : \bar R)%E = 1.
Proof. exact (@unit_cap_posinf R (@extended_real_unit_cap R) (ExtendedRealUnitCap.laws R)). Qed.

(** Source for [extended_real_unit_cap_neginf]: irrelevant total
    value at negative infinity; original path distances are
    nonnegative. Technical support for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_neginf (R : realType) :
  extended_real_unit_cap (-oo : \bar R)%E = 0.
Proof. exact (@unit_cap_neginf R (@extended_real_unit_cap R) (ExtendedRealUnitCap.laws R)). Qed.

(** Source for [extended_real_unit_cap_nonnegative]: nonnegative
    distances have nonnegative capped values, technical metric
    support for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_nonnegative (R : realType) (z : \bar R) :
  (0 <= z)%E -> 0 <= extended_real_unit_cap z.
Proof.
case: z=> [r| |] hz.
- rewrite lee_fin in hz.
  by rewrite extended_real_unit_cap_finite le_min hz ler01.
- rewrite extended_real_unit_cap_posinf; exact: ler01.
- by [].
Qed.

(** Source for [extended_real_unit_cap_le_one]: the finite
    carrier has diameter at most one, a technical fact for
    3.2.46, p. 281, not a bound on the original path metric. *)
Lemma extended_real_unit_cap_le_one (R : realType) (z : \bar R) :
  extended_real_unit_cap z <= 1.
Proof.
case: z=> [r| |].
- by rewrite extended_real_unit_cap_finite ge_min lexx orbT.
- by rewrite extended_real_unit_cap_posinf.
- by rewrite extended_real_unit_cap_neginf ler01.
Qed.

(** Source for [extended_real_unit_cap_zero]: a zero original
    distance has zero capped value, technical metric support
    for 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_zero (R : realType) :
  extended_real_unit_cap (0 : \bar R)%E = 0.
Proof. by rewrite extended_real_unit_cap_finite min_l //; exact: ler01. Qed.

(** Source for [extended_real_unit_cap_zero_iff]: capping a
    nonnegative distance preserves separation, technical support
    for the metric claim in 3.2.46, p. 281. *)
Lemma extended_real_unit_cap_zero_iff (R : realType) (z : \bar R) :
  (0 <= z)%E -> (extended_real_unit_cap z == 0) = (z == 0%E).
Proof.
case: z=> [r| |] hz.
- rewrite extended_real_unit_cap_finite eqe.
  case: (leP r 1)=> hr; first reflexivity.
  have hPositive : 0 < r := lt_trans ltr01 hr.
  by rewrite oner_eq0 (gt_eqF hPositive).
- by rewrite extended_real_unit_cap_posinf oner_eq0.
- by [].
Qed.

(** Source for [extended_real_unit_cap_small_value]: every
    original nonnegative distance at most one retains exactly
    its value, technical local-metric support for 3.2.46,
    p. 281. Hausdorff compatibility is proved separately. *)
Lemma extended_real_unit_cap_small_value (R : realType) (z : \bar R) :
  (0 <= z <= 1)%E -> (extended_real_unit_cap z)%:E = z.
Proof.
case: z=> [r| |] /andP [hz hSmall].
- rewrite lee_fin in hSmall.
  by rewrite extended_real_unit_cap_finite (min_l hSmall).
- by [].
- by [].
Qed.
