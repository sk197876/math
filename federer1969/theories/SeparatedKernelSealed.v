(** Federer (1969), 4.1.3, p. 348: opaque access to
    one common scalar factor and its actual normalized
    coordinate-product kernel. The laws were proved before
    this witness was chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP GrassmannAbbreviations SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothingKernelUP SeparatedKernelExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type SeparatedKernelSignature.
(** Source for [factor]: the common original one-variable test,
    Federer 4.1.3, p. 348. *)
Parameter factor:forall (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av),smooth_test_space hA.
(** Source for [laws]: the coordinate product of the actual factor
    has every original kernel law, Federer 4.1.3, p. 348. *)
Parameter laws:forall (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av),
  is_smoothing_kernel (fun x:R_n R n=>
    \prod_i smooth_test_value hA (@factor R n A av hA) (x i)).
End SeparatedKernelSignature.
Module SeparatedKernel:SeparatedKernelSignature.
(** Source for [factor]: private choice of the proved common
    scalar factor in Federer 4.1.3, p. 348. *)
Definition factor (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av):smooth_test_space hA:=
  projT1 (cid (@separated_kernel_exists R n A av hA)).
(** Source for [laws]: the proved original kernel laws are retained
    by the opaque common factor, Federer 4.1.3, p. 348. *)
Lemma laws (R:realType) (n:nat) (A:lmodType R) (av:A->R^o->R^o)
  (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
    (@scalar_absolute_value_norm R) (fun _=>True) av):
  is_smoothing_kernel (fun x:R_n R n=>
    \prod_i smooth_test_value hA (@factor R n A av hA) (x i)).
Proof. exact:(projT2 (cid (@separated_kernel_exists R n A av hA))). Qed.
End SeparatedKernel.
