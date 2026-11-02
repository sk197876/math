(** Federer (1969), 3.1.20, pp. 232–233: the sealed patching
    sequence produces a class-k retraction on an open neighbourhood
    of B, once local finiteness and the inner-ball cover are proved. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormClassZeroTopology
  RetractionUP LocalRetractionUP RetractionPatchingUP RetractionPatchingSealed
  RetractionPatchingStabilization StationaryRetractionUP StationaryRetractionLimit LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [locally_finite_retractions_glue]: the conclusion
    of the forward proof of Federer 3.1.20, pp. 232–233, from
    its local coordinate data. The final domain contains B and
    is open by the proved class law. Only the sealed intermediate
    sequence laws are used. *)
Theorem locally_finite_retractions_glue (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (B U:set X) (P Q:nat->set X) k :
  is_retraction_patch_family hNX hNY B U P Q k ->
  @is_locally_finite_family_on [the topologicalType of real_norm_metric_space hNX]
    [the choiceType of (nat:Type)] U setT P ->
  (forall b,B b -> exists i,Q i b) ->
  exists (A:set X) (f:X->X),
    @open [the topologicalType of real_norm_metric_space hNX] A /\
    is_norm_class_retraction hNX A B f k.
Proof.
move=>hF hLF hcover.
pose s:=@RetractionPatching.value R X Y NX NY hNX hNY B U P Q k hF.
have hS:=@RetractionPatching.laws R X Y NX NY hNX hNY B U P Q k hF.
change (is_retraction_patching_sequence hNX B U P Q s.1 s.2 k) in hS.
have hpartial:=@patching_partial_maps R X NX hNX B U P Q s.1 s.2 k hS.
have hWU:=@patching_domains_inside R X NX hNX B U P Q s.1 s.2 k hS.
have hstation:=@patching_locally_stationary R X NX hNX B U P Q s.1 s.2 k hS hLF.
have hBA:=@patching_eventual_domain_contains_B R X NX hNX B U P Q s.1 s.2 k hS hcover.
have [f hf]:=@stationary_retraction_limit R X NX hNX B U s.1 s.2 k hpartial hWU hstation hBA.
exists (eventual_open_domain s.1),f; split=>//.
exact (@norm_class_zero_domain_open R X X NX NX hNX (eventual_open_domain s.1) f
  (norm_class_continuous (norm_retraction_class hf))).
Qed.
