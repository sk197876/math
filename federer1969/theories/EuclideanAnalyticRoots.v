(** Federer (1969), 3.1.24, p. 240: an analytic
    function on a connected open Euclidean domain either vanishes
    identically or has a Lebesgue-null root set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerNormConnectedAdapter RealNormUP NormMetric NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  NormAnalyticUP NormAnalyticLocal NormSmoothFields NormAnalyticFlatIdentity
  EuclideanLebesgueDimensions MeasureUP MeasureBasic MeasureAlmostBasic
  EuclideanContinuousZeroSetMeasurable EuclideanFullDensityCore NormZeroJetsOnDensitySet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_analytic_roots_positive_dimension]:
    the root-set alternative in Federer 3.1.24, p. 240,
    in positive dimension. The zero set is measurable. Remove
    its null subset of failed density points, differentiate
    successively on the remaining full-density core, and apply
    the connected-domain flat-point identity theorem. No target
    dimension or completeness hypothesis is required. *)
Theorem euclidean_analytic_roots_positive_dimension (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R n.+1)) (f:R_n R n.+1->Y) :
  @connected (inner_metric_space (@euclidean_inner_productP R n.+1)) A ->
  @norm_analytic R (R_n R n.+1) Y _ NY
    (inner_norm_real_norm (@euclidean_inner_productP R n.+1)) hNY A f ->
  (fun x=>A x /\ f x=0)= A \/
    euclidean_lebesgue_measure n.+1 (fun x=>A x /\ f x=0)=0%E.
Proof.
move=>hconn hf.
pose NX:=inner_norm (@euclidean_inner_productP R n.+1).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n.+1).
pose Z i:=@ContinuousMultilinear.space R i (R_n R n.+1) Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i (R_n R n.+1) Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i (R_n R n.+1) Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i (R_n R n.+1) Y NX NY hNX hNY.
pose E:=fun x=>A x /\ f x=0.
have hclass:=norm_analytic_class_all_orders hf.
have [D hD]:=@norm_smooth_fields_exist R (R_n R n.+1) Y NX NY hNX hNY A f hclass.
have hEm:=@euclidean_continuous_zero_set_measurable R n.+1 Y NY hNY A f (hclass 0%N).1.
have [S [hSE [hNull hDen]]]:=@euclidean_full_density_core_exists R n.+1 E hEm.
have hSA x (hx:S x):A x:=(hSE x hx).1.
have hSf x (hx:S x):f x=0:=(hSE x hx).2.
have hJets:=@norm_zero_jets_on_density_set R n Y NY hNY Z ev ZN hZ A S f D
  hSA hSf hDen (fun i=>(hD i).1).
case:(pselect (exists a,S a))=>[[a ha]|hEmpty].
- left.
  have hFlat m (z:Z m) (hz:has_norm_higher_differential NX ev ZN A f m a z):z=0.
    rewrite (@norm_higher_differential_unique R (R_n R n.+1) Y NX NY hNX hNY Z ev ZN hZ
      A f m a z (D m a) hz ((hD m).1 a (hSA a ha))).
    exact (hJets m a ha).
  have hConnected: @connected (real_norm_metric_space hNX) A.
    exact ((inner_norm_connectedP (@euclidean_inner_productP R n.+1) A).1 hconn).
  have hzero:=@norm_analytic_flat_identity R (R_n R n.+1) Y NX NY hNX hNY A f a
    hConnected hf (hSA a ha) hFlat.
  apply/seteqP; split=>x hx; first exact hx.1.
  by split; [exact hx|exact (hzero x hx)].
- right.
  have he:E `\` S= E.
    apply/seteqP; split=>x hx; first exact hx.1.
    split; first exact hx.
    move=>hs; apply:hEmpty; by exists x.
  by rewrite he in hNull.
Qed.

(** Source for [euclidean_analytic_roots]: the root-set
    alternative of Federer 3.1.24, p. 240, with the
    dimension-zero and empty-domain cases retained. Dimension zero
    uses its singleton carrier directly and avoids the empty
    punctured approximate quotient. *)
Theorem euclidean_analytic_roots (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R n)) (f:R_n R n->Y) :
  @connected (inner_metric_space (@euclidean_inner_productP R n)) A ->
  @norm_analytic R (R_n R n) Y _ NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A f ->
  (fun x=>A x /\ f x=0)= A \/
    euclidean_lebesgue_measure n (fun x=>A x /\ f x=0)=0%E.
Proof.
case:n A f=>[|n] A f hc hf; last exact (@euclidean_analytic_roots_positive_dimension R n Y NY hNY A f hc hf).
have heq (x y:R_n R 0):x=y.
  apply/ffunP=>i; by have:=valP i; rewrite ltn0.
case:(pselect (f 0=0))=>[hz|hnz].
- left; apply/seteqP; split=>x hx; first exact hx.1.
  split; first exact hx; by rewrite (heq x 0).
- right.
  have he:(fun x=>A x /\ f x=0)=set0.
    apply/seteqP; split=>x hx; last by case:hx.
    apply:hnz; rewrite -(heq x 0); exact hx.2.
  by rewrite he (measure_empty (euclidean_lebesgue_is_measure R 0)).
Qed.
