(** Federer (1969), 4.1.5, pp. 349–350:
    zero extension identifies original compact continuous
    fields on U with their ambient representatives.
    It preserves pointwise addition and scalar multiples
    and lands in the original extension domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompactContinuousVectorFields CompactContinuousDomainFields
  CompactContinuousVectorZeroExtension CompactContinuousSubspaceSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_vector_open_extension_add]:
    zero extension commutes with addition in the
    original compact continuous D of Federer 4.1.5,
    p. 349. *)
Lemma compact_vector_open_extension_add (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (w v:set_type U->Y):
  @compact_vector_open_extension R X U Y (fun x=>w x+v x)=
    (fun x=>compact_vector_open_extension w x+compact_vector_open_extension v x).
Proof.
apply:funext=>x; rewrite /compact_vector_open_extension; case:pselect=>// _.
by rewrite addr0.
Qed.

(** Source for [compact_vector_open_extension_scale]:
    zero extension commutes with real scalar multiplication
    in Federer 4.1.5, p. 349. *)
Lemma compact_vector_open_extension_scale (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) c (w:set_type U->Y):
  @compact_vector_open_extension R X U Y (fun x=>c*:w x)=
    (fun x=>c*:compact_vector_open_extension w x).
Proof.
apply:funext=>x; rewrite /compact_vector_open_extension; case:pselect=>// _.
by rewrite scaler0.
Qed.

(** Source for [compact_vector_open_extension_domain]:
    every original compact continuous field on U
    gives an actual ambient extension-domain field,
    Federer 4.1.5, pp. 349–350. *)
Theorem compact_vector_open_extension_domain (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY):
  hausdorff_space X ->open U ->forall w:set_type U->Y,
    @compact_continuous_vector_fields R (set_type U) Y NY hNY w ->
    @compact_continuous_domain_fields R X U Y NY hNY (compact_vector_open_extension w).
Proof.
move=>hh hU w hw; split.
- exact:(@compact_vector_open_extension_compact R X hh U hU Y NY hNY w hw).
- exact:(@compact_vector_extension_support_inside R X hh U Y NY hNY w hw).
Qed.
