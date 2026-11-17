(** Federer (1969), 3.4.12, p. 339: independent local
    double-cover laws for the actual square map. Each branch is
    holomorphic, the two values are distinct, they exhaust each
    actual fibre, and their images are relatively open. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm RealNormUP NormMetric HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_original_complex_square_local_cover]: local
    holomorphic sheets replace global ordered sheets in 3.4.12,
    p. 339. The base and all inverse equations concern the
    original polynomial; no existence assertion enters these laws. *)
Definition is_original_complex_square_local_cover (R:realType)
    (w:ComplexScalars.C R)
    (W:set (real_norm_metric_space (@complex_modulus_real_norm R)))
    (s:'I_2->ComplexScalars.C R->ComplexScalars.C R):Prop:=
  @open (real_norm_metric_space (@complex_modulus_real_norm R)) W /\W w /\
  (forall v,W v ->v<>0) /\
  (forall i,@is_holomorphic R (ComplexScalars.C R)^o (ComplexScalars.C R)^o
    (@complex_modulus R) (@complex_modulus R) (@complex_modulus_real_norm R)
    (@complex_modulus_real_norm R) W (s i)) /\
  (forall i v,W v ->(s i v)^+2=v) /\
  (forall i j v,W v ->s i v=s j v ->i=j) /\
  (forall z,W (z^+2) ->exists i:'I_2,s i (z^+2)=z) /\
  forall i,exists O:set (real_norm_metric_space (@complex_modulus_real_norm R)),
    @open (real_norm_metric_space (@complex_modulus_real_norm R)) O /\
      s i @` W=[set z|z<>0] `&` O.
