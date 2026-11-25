(** Federer (1969), 1.7.3, p. 30, paragraph beginning with a linear map to
    another inner-product space: an orthonormal source basis can be chosen
    with mutually orthogonal images. Supporting Federer 1.7.4, but the
    target passage is in Federer 1. The target need not be
    finite-dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP TensorUP Bilinear LinearBasis
  PrincipalAxes PrincipalAxesUP PrincipalAxesDiagonal OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ImageBasis.
Variable R : realType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable f : {linear V -> U}.

(** Source for [image_bilinear_form]: Federer 1.7.3, p. 30,
    the displayed symmetric bilinear form S(x,y)=f(x).f(y). *)
Definition image_bilinear_form x y := C (f x) (f y).

(** Source for [image_bilinear_formP]: Federer 1.7.3, p. 30,
    supporting bilinearity of S(x,y)=f(x).f(y), without injectivity. *)
Lemma image_bilinear_formP : @bilinear R V V R^o image_bilinear_form.
Proof.
split=> y a x z; rewrite /image_bilinear_form linearP.
- by rewrite (bilDl (inner_bilinear hC)) (bilZl (inner_bilinear hC)).
- by rewrite (bilDr (inner_bilinear hC)) (bilZr (inner_bilinear hC)).
Qed.

(** Source for [image_bilinear_form_symmetric]: Federer
    1.7.3, p. 30, symmetry of the displayed form S. *)
Lemma image_bilinear_form_symmetric x y :
  image_bilinear_form x y = image_bilinear_form y x.
Proof. exact (@inner_symmetric R U C hC (f x) (f y)). Qed.

(** Source for [orthonormal_orthogonal_image_basis]: Federer
    1.7.3, p. 30, existence of an orthonormal basis of the
    finite-dimensional source with pairwise orthogonal images,
    obtained by principal axes for S(x,y)=f(x).f(y). *)
Theorem orthonormal_orthogonal_image_basis n (b : 'I_n -> V) (hb : is_basis b) :
  exists e : 'I_n -> V, is_basis e /\ orthonormal_family B e /\
    (forall i j, i != j -> C (f (e i)) (f (e j)) = 0).
Proof.
have [e he] := @principal_axes_exists R V B image_bilinear_form hB
  image_bilinear_formP image_bilinear_form_symmetric n b hb.
exists e; split; first exact: principal_axes_basis he.
split; first exact: principal_axes_orthonormal he.
move=> i j hij.
exact (@principal_axes_distinct R V B image_bilinear_form
  image_bilinear_form_symmetric n e he i j hij).
Qed.
End ImageBasis.
