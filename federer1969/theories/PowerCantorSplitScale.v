(** Federer (1969), 3.3.20, pp. 307–308:
    original equal-cost power-gauge radii scale under positive similarities. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology ring.
From Federer Require Import CantorSplitRadiusUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [power_cantor_split_positive_scale]: supporting
    actual similarity reduction in 3.3.20,
    pp. 307–308. The original positive split
    radius and cost equation transform homogeneously
    under positive scaling, for every original
    subdivision number. No chosen radius construction
    or desired Cantor-set identity is used. *)
Lemma power_cantor_split_positive_scale (R:realType) (c m d s r:R) n:
  0<r ->0<d ->is_cantor_split_radius (fun t=>c * real_power t m) d n s ->
  is_cantor_split_radius (fun t=>c * real_power t m) (r * d) n (r * s).
Proof.
move=>hr hd hSplit.
have [hs hBound]:=cantor_split_radius_bounds hSplit.
constructor.
- split;first exact:mulr_gt0 hr hs.
  have h:r * s<r * (d/n%:R) by rewrite ltr_pM2l.
  by rewrite mulrA in h.
- rewrite (@real_power_product R r s m (ltW hr) (ltW hs))
    (@real_power_product R r d m (ltW hr) (ltW hd)).
  have hLeft:c * (real_power r m * real_power s m)=real_power r m * (c * real_power s m) by ring.
  rewrite hLeft (cantor_split_radius_cost hSplit);ring.
Qed.
