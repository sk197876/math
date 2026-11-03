(** Federer (1969), 3.2.40, p. 276: consequences of the
    independent rapid-schedule laws. No interval implementation,
    chosen global sequence or content conclusion is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RapidPowerCantorScalesUP CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rapid_power_cantor_width_positive]: supporting
    positive scales for Federer 3.2.40, p. 276. The initial
    width is one; every later width is an actual positive
    equal-cost child width. *)
Lemma rapid_power_cantor_width_positive (R:realType) (c m:R) n s:
  is_rapid_power_cantor_scales c m n s ->forall j,0<s j.
Proof.
move=>hScales [|j].
- by rewrite (rapid_power_cantor_root hScales).
- exact:(cantor_split_radius_bounds (rapid_power_cantor_split hScales j)).1.
Qed.

(** Source for [rapid_power_cantor_subdivisions_diverge]: supporting
    n_j tending to infinity in Federer 3.2.40, p. 276.
    The stronger quantitative selection was proved possible
    independently; this conclusion is ordinary eventual
    domination of every natural threshold. *)
Lemma rapid_power_cantor_subdivisions_diverge (R:realType) (c m:R) n s:
  is_rapid_power_cantor_scales c m n s ->
  forall N:nat,exists J:nat,forall j,(J<=j)%N ->(N<=n j)%N.
Proof.
move=>hScales N; exists N=>j hNj.
apply:leq_trans hNj _.
apply:leq_trans _ (rapid_power_cantor_count hScales j).
exact:(leq_trans (leqnSn j) (leqnSn j.+1)).
Qed.
