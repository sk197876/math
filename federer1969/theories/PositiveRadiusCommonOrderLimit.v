(** Federer (1969), 3.3.4, p. 291: the
    common density supplied by 3.2.19 gives
    an ordinary all-positive-radius limit. This
    supporting order theorem treats finite values
    and both infinities with the existing limit
    specifications, without selected sequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds PositiveRadiusLimits
  PositiveRadiusLimitBounds PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_lower_gt_iff]:
    supporting lower small-ball estimate from
    the common density in Federer 3.3.4,
    p. 291. All positive real cutoffs,
    infinite endpoints and strict inequalities remain. *)
Lemma positive_radius_lower_gt_iff (R:realType) (f:R->\bar R) a:
  a<positive_radius_lower_limit f <->
  exists e:R,(0<e)%R /\ a<extended_real_inf (positive_radius_values f e).
Proof.
split.
- move=>hLower; apply:contrapT=>hNo.
  have hBound:positive_radius_lower_limit f<=a.
    apply:extended_real_sup_least=>v [e [he ->]].
    rewrite leNgt; apply/negP=>h; apply:hNo; by exists e.
  by have:=lt_le_trans hLower hBound; rewrite ltxx.
- move=>[e [he hSmall]].
  exact:(lt_le_trans hSmall (positive_radius_lower_ge_level f he)).
Qed.

(** Source for [positive_radius_common_order_limit]:
    equality of the actual upper and lower
    densities gives the ordinary limit invoked
    in Federer 3.3.4, p. 291. The conclusion
    uses every positive radius and the original
    independent extended order-limit laws. *)
Theorem positive_radius_common_order_limit (R:realType) (f:R->\bar R) l:
  positive_radius_lower_limit f=l ->positive_radius_upper_limit f=l ->
  positive_right_extended_order_limit f l.
Proof.
move=>hLower hUpper; split.
- move=>a ha.
  have h: a<positive_radius_lower_limit f by rewrite hLower.
  have [e [he hBound]]:=(positive_radius_lower_gt_iff f a).1 h.
  exists e; split=>// r hr hre.
  apply:lt_le_trans hBound _; apply:extended_real_inf_lower.
  exists r; split=>//; by apply/andP.
- move=>b hb.
  have h:positive_radius_upper_limit f<b by rewrite hUpper.
  have [e [he hBound]]:=(positive_radius_upper_lt_iff f b).1 h.
  exists e; split=>// r hr hre.
  apply:le_lt_trans _ hBound; apply:extended_real_sup_upper.
  exists r; split=>//; by apply/andP.
Qed.
