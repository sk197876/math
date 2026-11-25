(** Federer (1969), 3.1.22, p. 236: gluing local
    ambient extensions using the partition of unity of 3.1.13. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormRegularity NormRegularityOperations RelativeClassUP NormCutoffProductClass
  FiniteFamilySumUP FiniteFamilySumSealed NormLocallyFiniteFamilyUP
  LocallyFiniteSupportTransfer PartitionWeightedAgreement NormRegularityLocallyFiniteSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [relative_partition_extension]: supporting the single
    ambient extension in Federer 3.1.22, p. 236. A locally
    finite class-k partition subordinate to the domains of local
    extensions gives a class-k extension on the partition domain.
    Only the finite-sum laws are used, so the target need not be complete. *)
Theorem relative_partition_extension (R:realType) (X Y:lmodType R) (J:choiceType)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S U:set X) (f:X->Y) k (I:J->Prop) (u:J->X->R^o)
    (T P:J->set X) (g:J->X->Y) :
  (forall x,U x -> norm_domain_interior NX U x) ->
  S `<=` U -> S `<=` A ->
  is_norm_locally_finite_function_family NX U I u ->
  is_finite_family_sum_on U I u (fun _=>1) ->
  (forall j,I j -> norm_class hNX (scalar_absolute_value_norm R) setT (u j) k) ->
  (forall j,I j -> norm_class hNX hNY (T j) (g j) k) ->
  (forall j,I j -> @closed (real_norm_metric_space hNX) (P j)) ->
  (forall j,I j -> P j `<=` T j) ->
  (forall j,I j -> forall x,~P j x -> u j x=0) ->
  (forall j,I j -> forall x,S x -> T j x -> f x=g j x) ->
  exists G,@is_norm_relative_extension R X Y NX NY hNX hNY A S f k U G.
Proof.
move=>hUint hSU hSA hloc hOne hu hg hP hPT hu0 hfg.
pose w:=fun j x=>u j x*:g j x.
have hlocw:is_norm_locally_finite_function_family NX U I w.
  apply: (norm_locally_finite_zero_transfer hloc)=>j hj x hx hz.
  by rewrite /w hz scale0r.
pose hfinw:=norm_locally_finite_active_family hlocw.
pose G:=@FiniteFamilySum.value X J Y U I w hfinw.
have hSum:=@FiniteFamilySum.laws X J Y U I w hfinw.
have hclass: norm_class hNX hNY U G k.
  apply: (norm_class_locally_finite_sum hlocw hSum)=>j hj.
  have hw:=@norm_class_cutoff_product R X Y NX NY hNX hNY (T j) (P j)
    (u j) (g j) k (hg j hj) (hu j hj) (hP j hj) (hPT j hj) (hu0 j hj).
  exact (@norm_class_open_restriction R X Y NX NY hNX hNY setT U (w j) k
    (fun _ _=>Logic.I) hUint hw).
have hweight j (hj:I j) x (hxS:S x) (_:U x):w j x=u j x*:f x.
  case:(eqVneq (u j x) 0)=>[hz|hn].
  - by rewrite /w hz !scale0r.
  - have hxP:P j x.
      apply: contrapT=>hx; move: hn; by rewrite (hu0 j hj x hx) eqxx.
    by rewrite /w (hfg j hj x hxS (hPT j hj x hxP)).
exists G; split=>//; split=>// x hxS; split; first exact (hSA x hxS).
symmetry; exact (@partition_weighted_agreement R X Y J U S I u w f G
  (norm_locally_finite_active_family hloc) hOne hSum hweight x hxS (hSU x hxS)).
Qed.
