(** Federer (1969), 4.1.1, pp. 343–345, reused in
    4.1.15, p. 373: a smooth function vanishing off
    a compact set is an actual original test. This
    narrow adapter uses the existing opaque smooth-space
    and subspace realization laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormRegularity SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces
  SmoothTestSubspaces LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_test_realisation]: the exact original
    D(U,Y) realization of a smooth compactly supported
    function, Federer 4.1.1, pp. 343–345. This
    supports the literal scalar-test membership of the
    example sequence in 4.1.15, p. 373. *)
Theorem smooth_test_realisation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (K:smooth_compact_set hNX U) (f:X->Y):
  norm_class_all_orders hNX hNY U f ->
  (forall x,~smooth_compact_carrier K x->f x=0) ->
  exists phi:smooth_test_space hE,forall x,U x->
    ev (smooth_test_inclusion hE phi) x=f x.
Proof.
move=>hSmooth hOff.
have [g hG]:=smooth_function_evaluation_surjective hE hSmooth.
have hSupport:smooth_compact_support_subspace hE g.
  exists K;apply:(smooth_function_compact_support_iff hE K g).2=>x hx.
  case:(pselect (U x))=>hUx.
  - rewrite (hG x hUx);exact:hOff x hx.
  - exact:(@smooth_function_evaluation_outside R X Y NX NY hNX hNY U E ev hE
      g x hUx).
have [phi hPhi]:=subspace_representation_full (smooth_test_space_laws hE) hSupport.
exists phi=>x hx;rewrite hPhi;exact:hG x hx.
Qed.
