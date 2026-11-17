(** Federer (1969), 3.4.12, p. 339, extending 3.4.6(2), pp. 321–324:
    the original complex Weierstrass preparation theorem for every
    supplied continuous xi with xi(v)=1. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  HolomorphicGermUP HolomorphicGermRing ComplexWeierstrassRegularUP ComplexWeierstrassTransverseSealed
  ComplexWeierstrassPreparationUP ComplexWeierstrassPreparationExistence ComplexWeierstrassPreparationUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Preparation.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variable hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi).
Variable hUnit:xi v= 1.
Let K:=@ComplexWeierstrassTransverse.space R X NX hNX v xi hXi hUnit.
Let NK:=@ComplexWeierstrassTransverse.norm R X NX hNX v xi hXi hUnit.
Let hNK:=@ComplexWeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit.
Let inclusion:=@ComplexWeierstrassTransverse.inclusion R X NX hNX v xi hXi hUnit.
Let projection:=@ComplexWeierstrassTransverse.projection R X NX hNX v xi hXi hUnit.

(** Source for [complex_weierstrass_preparation]: for every
    original xi the monic preparation exists, Q(0) is
    nonzero, Wi(0)=0, and all its germs are unique,
    3.4.6(2), p. 322. Retain the printed
    Banach source and original regularity. The actual
    kernel is exposed only through its opaque splitting
    and inherited-norm laws. *)
Theorem complex_weierstrass_preparation
    (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space (complex_norm_real hNX)])
    (Phi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0) k:
  is_complex_weierstrass_regular_germ hNX Phi k v ->
  exists Q W:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0,
    exists Wi:'I_k->@holomorphic_germ_ring R K NK (complex_norm_real hNK) 0,
      @is_complex_weierstrass_preparation R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) xi projection k Phi Q W Wi /\
      forall Q' W' Wi',@is_complex_weierstrass_preparation R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) xi projection k Phi Q' W' Wi' ->
        Q'=Q /\W'=W /\forall i,Wi' i=Wi i.
Proof.
move=>hRegular.
have hSplit:=@ComplexWeierstrassTransverse.laws R X NX hNX v xi hXi hUnit.
have [Q [W [Wi hPreparation]]]:=@complex_weierstrass_preparation_with_transverse_exists R X K NX NK hNX hNK
  v xi inclusion projection k Phi hSplit hXi hRegular.
exists Q,W,Wi;split;first exact:hPreparation.
move=>Q' W' Wi' hCandidate.
exact:(@complex_weierstrass_preparation_with_transverse_unique R X K NX NK hNX hNK v xi inclusion projection k
  Phi Q' W' Q W Wi' Wi hSplit hXi hRegular hCandidate hPreparation).
Qed.
End Preparation.
