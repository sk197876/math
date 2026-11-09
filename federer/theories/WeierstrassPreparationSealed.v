(** Federer (1969), 3.4.6(2), p. 322: opaque
    preparation, exposed through the original multiplier,
    monic polynomial, transverse coefficients and uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP AnalyticGermUP AnalyticGermRing
  WeierstrassRegularUP WeierstrassTransverseSealed WeierstrassPreparationUP WeierstrassPreparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type WeierstrassPreparationSignature.
(** Source for [multiplier]: the original multiplier germ,
    3.4.6(2), p. 322. *)
Parameter multiplier:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (v:X) (xi:Hom X R^o) (hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi) (hUnit:xi v= 1)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  (Phi:@analytic_germ_ring R X NX hNX 0) k (hRegular:is_weierstrass_regular_germ Phi k v),
  @analytic_germ_ring R X NX hNX 0.
(** Source for [polynomial]: the original polynomial germ,
    3.4.6(2), p. 322. *)
Parameter polynomial:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (v:X) (xi:Hom X R^o) (hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi) (hUnit:xi v= 1)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  (Phi:@analytic_germ_ring R X NX hNX 0) k (hRegular:is_weierstrass_regular_germ Phi k v),
  @analytic_germ_ring R X NX hNX 0.
(** Source for [coefficients]: the original transverse
    analytic germs Wi, 3.4.6(2), p. 322. *)
Parameter coefficients:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (v:X) (xi:Hom X R^o) (hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi) (hUnit:xi v= 1)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  (Phi:@analytic_germ_ring R X NX hNX 0) k (hRegular:is_weierstrass_regular_germ Phi k v),
  'I_k->@analytic_germ_ring R (@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit) (@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit) (@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit) 0.
(** Source for [laws]: all original preparation equations
    and values at zero, 3.4.6(2), p. 322. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (v:X) (xi:Hom X R^o) (hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi) (hUnit:xi v= 1)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  (Phi:@analytic_germ_ring R X NX hNX 0) k (hRegular:is_weierstrass_regular_germ Phi k v),
  @is_weierstrass_preparation R X (@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit) NX (@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit) hNX (@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit) xi (@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit) k Phi
    (@multiplier R X NX hNX v xi hXi hUnit hComplete Phi k hRegular) (@polynomial R X NX hNX v xi hXi hUnit hComplete Phi k hRegular) (@coefficients R X NX hNX v xi hXi hUnit hComplete Phi k hRegular).
(** Source for [unique]: every original preparation germ
    is uniquely determined, 3.4.6(2), p. 322. *)
Parameter unique:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (v:X) (xi:Hom X R^o) (hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi) (hUnit:xi v= 1)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  (Phi:@analytic_germ_ring R X NX hNX 0) k (hRegular:is_weierstrass_regular_germ Phi k v),
  forall Q W Wi,@is_weierstrass_preparation R X (@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit) NX (@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit) hNX (@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit) xi (@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit) k Phi Q W Wi ->
    Q=@multiplier R X NX hNX v xi hXi hUnit hComplete Phi k hRegular /\W=@polynomial R X NX hNX v xi hXi hUnit hComplete Phi k hRegular /\forall i,Wi i=@coefficients R X NX hNX v xi hXi hUnit hComplete Phi k hRegular i.
End WeierstrassPreparationSignature.
Module WeierstrassPreparation:WeierstrassPreparationSignature.
Section Parameters.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable v:X.
Variable xi:Hom X R^o.
Variable hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Variable hUnit:xi v= 1.
Variable hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX].
Variable Phi:@analytic_germ_ring R X NX hNX 0.
Variable k:nat.
Variable hRegular:is_weierstrass_regular_germ Phi k v.
Let K:=(@WeierstrassTransverse.space R X NX hNX v xi hXi hUnit).
Let NK:=(@WeierstrassTransverse.norm R X NX hNX v xi hXi hUnit).
Let hNK:=(@WeierstrassTransverse.norm_laws R X NX hNX v xi hXi hUnit).
Let projection:=(@WeierstrassTransverse.projection R X NX hNX v xi hXi hUnit).
Let witness:=cid (@weierstrass_preparation R X NX hNX v xi hXi hUnit hComplete Phi k hRegular).
(** Source for [multiplier]: a private witness of the
    proved original preparation theorem, 3.4.6(2), p. 322. *)
Definition multiplier:@analytic_germ_ring R X NX hNX 0:=projT1 witness.
Let polynomial_witness:=cid (projT2 witness).
(** Source for [polynomial]: a private witness of the
    proved original preparation theorem, 3.4.6(2), p. 322. *)
Definition polynomial:@analytic_germ_ring R X NX hNX 0:=projT1 polynomial_witness.
Let coefficient_witness:=cid (projT2 polynomial_witness).
(** Source for [coefficients]: private witnesses of the
    original transverse coefficient existence, 3.4.6(2), p. 322. *)
Definition coefficients:'I_k->@analytic_germ_ring R K NK hNK 0:=projT1 coefficient_witness.
(** Source for [laws]: all original preparation laws
    hold for the opaque witnesses, 3.4.6(2), p. 322. *)
Lemma laws:@is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi multiplier polynomial coefficients.
Proof. exact:(projT2 coefficient_witness).1. Qed.
(** Source for [unique]: every original preparation candidate
    agrees with the opaque witnesses, 3.4.6(2), p. 322. *)
Lemma unique Q W Wi:@is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi Q W Wi ->
  Q=multiplier /\W=polynomial /\forall i,Wi i=coefficients i.
Proof. exact:(projT2 coefficient_witness).2 Q W Wi. Qed.
End Parameters.
End WeierstrassPreparation.
