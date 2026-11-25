(** Federer (1969), 4.1.7, p. 359:
    pull back an arbitrary original form
    field at every point of U.
    This alias uses the sealed partial
    pullback of 4.1.6, p. 354,
    and its sealed graph-preserving extension.
    Smoothness of f supplies all required
    differentiability points; the form may be Baire. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingDual DifferentialFormPullbackUP
  DifferentialFormPullbackSealed PartialFunctionExtensionSealed CurrentDomain CurrentSpaces CurrentConstantFields
  CurrentMapDifferential SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFormPullbackOnDomain.
Variable R:realType.
Variables v n k:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop) (f:X->Y).
Local Notation UT := (current_domain R v U).

(** Source for [current_form_pullback_on_domain]:
    the actual original partial pullback viewed
    on the original source domain, supporting
    Federer 4.1.7, p. 359. Its
    value is inherited from already sealed
    operations rather than a new chosen derivative. *)
Definition current_form_pullback_on_domain (psi:Y->A_m Y R^o k):UT->A_m X R^o k:=
  fun x=>@PartialFunctionExtension.value X (A_m X R^o k)
    (@DifferentialFormPullback.value R X Y R^o NX NY hNX hNY U V f k psi) 0 (set_val x).

(** Source for [current_form_pullback_on_domain_actual]:
    the original f#psi is exactly A^k
    Df(x)(psi(f(x))) at every point of U,
    supporting Federer 4.1.7, p. 359.
    The field psi requires no smoothness. *)
Theorem current_form_pullback_on_domain_actual (psi:Y->A_m Y R^o k):
  (forall x,U x->V (f x))->norm_class_all_orders hNX hNY U f->forall x:UT,
  current_form_pullback_on_domain psi x=
    A_m_dual (hom_as_linear (@current_map_differential R v n U f (set_val x)))
      (psi (f (set_val x))).
Proof.
move=>hImage hf x.
apply:(@PartialFunctionExtension.laws X (A_m X R^o k)
  (@DifferentialFormPullback.value R X Y R^o NX NY hNX hNY U V f k psi) 0).
apply:(@DifferentialFormPullback.laws R X Y R^o NX NY hNX hNY U V f k psi _ _).2.
split;first exact:(@hImage (set_val x) (set_valP x)).
exists (@current_map_differential R v n U f (set_val x));split;last by [].
exact:(@current_map_differential_actual R v n U f hf (set_val x) (set_valP x)).
Qed.

(** Source for [current_form_pullback_on_domain_constant]:
    each original constant target covector pulls
    back to the corresponding actual smooth
    source field, supporting finite-coordinate Baire
    pullbacks in Federer 4.1.7, p. 359. *)
Theorem current_form_pullback_on_domain_constant (h2:(1+1:R)!=0)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (hV:forall y,V y->norm_domain_interior NY V y)
    (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders hNX hNY U f) (a:A_m Y R^o k) (x:UT):
  current_form_pullback_on_domain (fun _=>a) x=
    @current_smooth_value R h2 v U hU k
      (@SmoothFormPullback.operator R h2 v n k U V hU hV f hImage hf
        (@current_constant_form R h2 n V hV k a)) (set_val x).
Proof.
rewrite (current_form_pullback_on_domain_actual (fun _=>a) hImage hf x).
rewrite (@smooth_form_pullback_values R v n k U V
  (@current_smooth_space R h2 n V hV k) (@current_smooth_space R h2 v U hU k)
  (@current_smooth_value R h2 n V hV k) (@current_smooth_value R h2 v U hU k) f
  (@SmoothFormPullback.operator R h2 v n k U V hU hV f hImage hf)
  (@SmoothFormPullback.laws R h2 v n k U V hU hV f hImage hf)
  (@current_constant_form R h2 n V hV k a) (set_val x)
  (@current_map_differential R v n U f (set_val x)) (set_valP x)
  (@current_map_differential_actual R v n U f hf (set_val x) (set_valP x))).
by rewrite (@current_constant_form_values R h2 n V hV k a (f (set_val x))
  (@hImage (set_val x) (set_valP x))).
Qed.
End CurrentFormPullbackOnDomain.
