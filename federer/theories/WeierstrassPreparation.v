(** Federer (1969), 3.4.6(2), pp. 321–324:
    the original Weierstrass preparation theorem for every
    supplied continuous xi with xi(v)=1. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  AnalyticGermUP AnalyticGermRing WeierstrassRegularUP WeierstrassTransverseSealed
  WeierstrassPreparationUP WeierstrassPreparationExistence WeierstrassPreparationUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Preparation.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable v:X.
Variable xi:Hom X R^o.
Variable hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Variable hUnit:xi v= 1.
Let K:=@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit.
Let NK:=@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit.
Let hNK:=@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit.
Let inclusion:=@WeierstrassTransverse.inclusion R X NX hNX v xi hXi hUnit.
Let projection:=@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit.

(** Source for [weierstrass_preparation]: for every
    original xi the monic preparation exists, Q(0) is
    nonzero, Wi(0)=0, and all its germs are unique,
    3.4.6(2), p. 322. Retain the printed
    Banach source and original regularity. The actual
    kernel is exposed only through its opaque splitting
    and inherited-norm laws. *)
Theorem weierstrass_preparation
    (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
    (Phi:@analytic_germ_ring R X NX hNX 0) k:
  is_weierstrass_regular_germ Phi k v ->
  exists Q W:@analytic_germ_ring R X NX hNX 0,
    exists Wi:'I_k->@analytic_germ_ring R K NK hNK 0,
      @is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi Q W Wi /\
      forall Q' W' Wi',@is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi Q' W' Wi' ->
        Q'=Q /\W'=W /\forall i,Wi' i=Wi i.
Proof.
move=>hRegular.
have hSplit:=@WeierstrassTransverse.laws R X NX hNX v xi hXi hUnit.
have [Q [W [Wi hPreparation]]]:=@weierstrass_preparation_with_transverse_exists R X K NX NK hNX hNK
  v xi inclusion projection k Phi hSplit hXi hRegular.
exists Q,W,Wi;split;first exact:hPreparation.
move=>Q' W' Wi' hCandidate.
exact:(@weierstrass_preparation_with_transverse_unique R X K NX NK hNX hNK v xi inclusion projection k
  Phi Q' W' Q W Wi' Wi hSplit hXi hRegular hCandidate hPreparation).
Qed.
End Preparation.
