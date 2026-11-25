(** Federer (1969), 4.1.1, p. 344: locally
    finite smooth vector sums support the common-support
    sequence theorem. Existence is proved by the sealed
    finite-family sum and the original class gluing
    theorem of 3.1.13, p. 225. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormRegularity NormRegularityLocallyFiniteSum
  NormLocallyFiniteFamilyUP FiniteFamilySumUP FiniteFamilySumSealed SmoothFunctionSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_locally_finite_sum_exists]: every
    locally finite family of actual smooth functions
    has its actual smooth sum with all original
    finite evaluation laws, supporting Federer
    4.1.1, p. 344. Completeness of the
    target is unnecessary for locally finite sums. *)
Theorem smooth_locally_finite_sum_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (J:choiceType) (I:J->Prop) (f:J->E):
  is_norm_locally_finite_function_family NX U I (fun j x=>ev (f j) x) ->
  exists g:E,is_finite_family_sum_on U I (fun j x=>ev (f j) x) (ev g).
Proof.
move=>hLocal.
pose hFin:=norm_locally_finite_active_family hLocal.
pose G:=@FiniteFamilySum.value X J Y U I (fun j x=>ev (f j) x) hFin.
have hG:=@FiniteFamilySum.laws X J Y U I (fun j x=>ev (f j) x) hFin.
have hClass:norm_class_all_orders hNX hNY U G.
  move=>k; apply:(norm_class_locally_finite_sum hLocal hG)=>j hj.
  exact:(@smooth_function_evaluation_smooth R X Y NX NY hNX hNY U E ev hE (f j) k).
have [g hg]:=smooth_function_evaluation_surjective hE hClass.
exists g=>x hx F hFI hZero.
rewrite (hg x hx); exact:(hG x hx F hFI hZero).
Qed.
