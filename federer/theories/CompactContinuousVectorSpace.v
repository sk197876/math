(** Federer (1969), 4.1.5, p. 349: the compact
    continuous Y-valued fields form the original vector
    space D. Existing continuous-family and scalar compact
    support laws prove its pointwise closure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP CompactSupportFunctionLattice
  VectorDaniellHypotheses ContinuousVectorFamily CompactContinuousVectorFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_vector_space]: the actual
    D is a vector space for the application of 2.5.12 in
    Federer 4.1.5, p. 349. No compactness of the whole
    domain or separability of Y is needed for these laws. *)
Theorem compact_continuous_vector_space (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY):
  is_vector_function_space (@compact_continuous_vector_fields R X Y NY hNY).
Proof.
have hContinuous:=@continuous_normed_functions_vector_space R X Y NY hNY.
constructor.
- split; first exact:vector_function_space_zero hContinuous.
  have hZero:(fun x:X=>NY (0:Y))=(fun _:X=>(0:R)).
    apply:funext=>x; exact:real_seminorm_zero hNY.1.
  rewrite hZero; exact:(@compactly_supported_zero_function R X).2.
- move=>w v [hw hW] [hv hV]; split.
  + exact:(@vector_function_space_add R X Y (@continuous_normed_functions R X Y NY hNY) hContinuous w v hw hv).
  + apply:(@compact_support_binary_operation R X (fun x=>NY (w x)) (fun x=>NY (v x))
      (fun x=>NY (w x+v x)) hW hV)=>x hW0 hV0.
    by rewrite (hNY.2 _ hW0) (hNY.2 _ hV0) addr0 (real_seminorm_zero hNY.1).
- move=>c w [hw hW]; split.
  + exact:(@vector_function_space_scale R X Y (@continuous_normed_functions R X Y NY hNY) hContinuous c w hw).
  + apply:(@compact_support_unary_operation R X (fun x=>NY (w x)) (fun x=>NY (c*:w x)) hW)=>x hW0.
    by rewrite (hNY.2 _ hW0) scaler0 (real_seminorm_zero hNY.1).
Qed.
