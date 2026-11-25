(** Federer (1969), 4.1.11, p. 364: smooth maps can push
    forward the compact current product in the original join.
    Reuse the earlier compact-source properness on exactly the
    actual support, as in 4.1.9, p. 363. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentProperSupport
  CurrentProperOnContainingSet CurrentCompactContainingProper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_compact_map_proper]: a continuous map
    on the original source is proper on a compact current support,
    supporting Federer 4.1.11, p. 364. Properness on the whole open
    source is neither assumed nor asserted. *)
Theorem current_compact_map_proper
    (R : realType) (h2 : (1+1:R)!=0) (n nu j : nat)
    (U : set (R_n R n)) (V : set (R_n R nu))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T : @current_space R h2 n U hU j)
    (f : R_n R n -> R_n R nu)
    (hImage : forall x, U x -> V (f x)) :
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu)) U f ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU j T) ->
  @is_current_proper_on_support R h2 n nu j U hU V T f hImage.
Proof.
move=> hF hCompact.
pose C := @current_support R h2 n U hU j T.
have hCU : forall x, C x -> U x by move=> x hx; exact: hx.1.
apply: (@current_proper_on_containing_set R n nu U V C hCU
  f hImage h2 j hU T (fun _ hx => hx)).
exact: (@current_compact_containing_map_proper R n nu U V C hCU
  f hImage hF hCompact).
Qed.
