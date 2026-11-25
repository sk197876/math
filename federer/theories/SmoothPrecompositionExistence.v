(** Federer (1969), 4.1.7, p. 359:
    actual precomposition by a smooth map
    exists on the original smooth spaces.
    This supporting fact reuses the composition
    theorem of 3.1.11, pp. 221–222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothPrecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothPrecompositionExistence.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variables (A:X->Prop) (B:Y->Prop).
Variables E F:lmodType R.
Variables (ev:E->Y->Z) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNY hNZ B ev.
Hypothesis hF:is_smooth_function_space hNX hNZ A fv.
Variable f:X->Y.
Hypothesis hImage:forall x,A x->B (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY A f.

(** Source for [smooth_precomposition_member_exists]:
    each original smooth function composed
    with f has an actual smooth
    representative, supporting Federer 4.1.7,
    p. 359. *)
Lemma smooth_precomposition_member_exists h:
  exists g:F,forall x,A x->fv g x=ev h (f x).
Proof.
apply:(smooth_function_evaluation_surjective hF)=>k.
exact:(@norm_class_compose_on R X Y Z NX NY NZ hNX hNY hNZ
  A B f (ev h) k hImage (hf k) (smooth_function_evaluation_smooth hE h k)).
Qed.

(** Source for [smooth_precomposition_member]: the
    private choice of a proved actual
    smooth representative, hidden by the
    operator seal for Federer 4.1.7,
    p. 359. *)
Definition smooth_precomposition_member h:F:=projT1 (cid (smooth_precomposition_member_exists h)).

(** Source for [smooth_precomposition_member_value]:
    exact original values of the private
    representative, supporting Federer 4.1.7,
    p. 359. *)
Lemma smooth_precomposition_member_value h x:A x->
  fv (smooth_precomposition_member h) x=ev h (f x).
Proof. exact:(projT2 (cid (smooth_precomposition_member_exists h)) x). Qed.

(** Source for [smooth_precomposition_member_linear]:
    fixed smooth precomposition is linear
    in the original function, supporting
    Federer 4.1.7, p. 359. *)
Lemma smooth_precomposition_member_linear:linear smooth_precomposition_member.
Proof.
move=>c h g;apply:(smooth_function_extensional hF)=>x hx.
rewrite (smooth_precomposition_member_value (c*:h+g) hx)
  (smooth_function_add_value hE) (smooth_function_scale_value hE)
  (smooth_function_add_value hF) (smooth_function_scale_value hF)
  (smooth_precomposition_member_value h hx) (smooth_precomposition_member_value g hx).
by [].
Qed.

(** Source for [smooth_precomposition_exists]: an
    actual linear map satisfies the independent
    original precomposition law, supporting Federer
    4.1.7, p. 359. *)
Theorem smooth_precomposition_exists:
  exists P:Hom E F,is_smooth_precomposition A ev fv f P.
Proof.
exists (@HomMap R E F smooth_precomposition_member
  (introT (asboolP _) smooth_precomposition_member_linear)).
exact:smooth_precomposition_member_value.
Qed.
End SmoothPrecompositionExistence.
