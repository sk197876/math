(** Federer (1969), 3.1.20, p. 232: instantiate the smooth
    cutoff functions u_s of 3.1.13 in the public sealed
    multilinear representation used by the coordinate classes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness NormRegularity ContinuousMultilinearUP ContinuousMultilinearSealed
  EuclideanPartitionBallCoverUP EuclideanPartitionBumps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_partition_bump_class]: u_s is of
    class k on the whole Euclidean space, Federer 3.1.13,
    p. 224, as used for the interpolation in 3.1.20, p. 232.
    This only instantiates the already proved smoothness law. *)
Lemma euclidean_partition_bump_class (R:realType) n
    (Phi:set (set (inner_metric_space (@euclidean_inner_productP R n)))) S :
  (forall T,Phi T -> open T) -> is_federer_partition_ball_cover Phi S ->
  forall s,S s -> forall k,
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (scalar_absolute_value_norm R) (fun _=>True) (euclidean_partition_bump Phi s) k.
Proof.
move=>ho hS s hs k.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hAbs:=scalar_absolute_value_norm R.
exact (@euclidean_partition_bump_smooth R n Phi S
  (fun j=>@ContinuousMultilinear.space R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs)
  (fun j=>@ContinuousMultilinear.evaluation R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs)
  (fun j=>@ContinuousMultilinear.norm R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs)
  (fun j=>@ContinuousMultilinear.laws R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs) s hs k).
Qed.
