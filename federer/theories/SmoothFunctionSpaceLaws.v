(** Federer (1969), 4.1.1, pp. 343–344: pointwise vector-space
    and extensionality laws for the abstract smooth-function space.
    These proofs use only its public evaluation specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity SmoothFunctionSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothSpaceLaws.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.

(** Source for [smooth_function_values_linear]: evaluations form
    a linear map into the ordinary function module, supporting
    E(U,Y) in Federer 4.1.1, p. 343. *)
Lemma smooth_function_values_linear : linear ev.
Proof.
move=>c f g; apply:funext=>x.
change (ev (c*:f+g) x=c*:ev f x+ev g x).
exact:(@smooth_function_evaluation_linear R X Y NX NY hNX hNY U E ev hE c f g x).
Qed.

(** Source for [smooth_function_values_hom]: evaluation as the
    linear map into the ordinary function space, supporting
    E(U,Y), Federer 4.1.1, p. 343. *)
Definition smooth_function_values_hom :
    Hom E (GRing.Lmodule.clone R (X->Y) _) :=
  @HomMap R E (GRing.Lmodule.clone R (X->Y) _) ev
    (introT (asboolP _) smooth_function_values_linear).

(** Source for [smooth_function_zero_value]: the zero smooth
    function vanishes at every point, Federer 4.1.1, p. 343. *)
Lemma smooth_function_zero_value x : ev 0 x=0.
Proof.
change (smooth_function_values_hom 0 x=0).
by rewrite linear0.
Qed.

(** Source for [smooth_function_add_value]: pointwise addition
    in E(U,Y), Federer 4.1.1, p. 343. *)
Lemma smooth_function_add_value f g x : ev (f+g) x=ev f x+ev g x.
Proof.
change (smooth_function_values_hom (f+g) x=
  smooth_function_values_hom f x+smooth_function_values_hom g x).
by rewrite linearD.
Qed.

(** Source for [smooth_function_scale_value]: pointwise scalar
    multiplication in E(U,Y), Federer 4.1.1, p. 343. *)
Lemma smooth_function_scale_value c f x : ev (c*:f) x=c*:ev f x.
Proof.
change (smooth_function_values_hom (c*:f) x=c*:smooth_function_values_hom f x).
by rewrite linearZ.
Qed.

(** Source for [smooth_function_extensional]: equality is
    determined by values on the actual open domain U, Federer
    4.1.1, p. 343. The normalization convention contributes no
    additional mathematical values outside U. *)
Lemma smooth_function_extensional f g :
  (forall x,U x -> ev f x=ev g x) -> f=g.
Proof.
move=>he; apply:(smooth_function_evaluation_injective hE).
apply:funext=>x; case:(pselect (U x))=>[hx|hx]; first exact:he.
by rewrite !(smooth_function_evaluation_outside hE _ hx).
Qed.
End SmoothSpaceLaws.
