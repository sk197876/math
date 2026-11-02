(** Federer (1969), 3.2.33, p. 270: analytic maps
    on W possess actual relative differentials, by
    3.1.22 and 3.1.24, pp. 235,239. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormRegularity NormClassOneUP NormCoordinateSystemUP
  PartialFunctionUP RelativeDifferentialUP RelativeDifferentialRestriction
  NormAnalyticUP NormAnalyticLocal NormAnalyticRelativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_analytic_differential_exists]: the
    actual Df relative to W used in Federer 3.2.33,
    p. 270. A local analytic representative supplies its
    actual first derivative; the exact tangent restriction
    supplies the relative differential. The witness remains
    local and no ambient derivative field is assumed. *)
Theorem relative_analytic_differential_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A W:set X) (f:X->Y) a:
  @norm_analytic_relative R X Y NX NY hNX hNY A W f ->W a ->
  exists d:partial_function X Y,
    @has_relative_norm_differential R X Y NX NY hNX A W f a d.
Proof.
move=>hf ha; have [U [g [haU [hg hAgree]]]]:=hf a ha.
have [D hD]:=(norm_class_firstP hNX hNY U g).1
  (norm_analytic_class_all_orders hg 1%N).
have [d hd]:=tangent_differential_restriction_exists NX W a (D a).
exists d; split; first exact:subset_closure ha.
exists U,g,(D a); split; first exact:(norm_class_one_differential hD haU).
by split.
Qed.
