(** Federer (1969), 4.1.7, p. 359:
    the actual exterior image pairs with
    psi wedge phi by pairing the
    original density with their actual pullbacks.
    This is the original characteristic law
    of 1.4.1, pp. 17–18,
    and product law of 4.1.6, p. 354. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom TensorUP ScalarCoefficients RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorMaps
  AlternatingForms AlternatingDual AlternatingPairing AlternatingProduct FormPullbackProduct
  CurrentDomain CurrentSpaces CurrentMapDifferential CurrentImageDensityPairing CurrentFormPullbackOnDomain
  SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentBaireProjectionPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n k p:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation UT := (current_domain R v U).
Local Notation E := (@current_smooth_space R h2 n V hV p).
Local Notation F := (@current_smooth_space R h2 v U hU p).
Local Notation ev := (@current_smooth_value R h2 n V hV p).
Local Notation fv := (@current_smooth_value R h2 v U hU p).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (@SmoothFormPullback.operator R h2 v n p U V hU hV f hImage hf).

(** Source for [current_baire_projection_pairing]:
    the original pointwise product pairing
    in the projection formula, Federer
    4.1.7, p. 359. The field
    psi is arbitrary; its Baire regularity
    enters only the subsequent integral argument. *)
Theorem current_baire_projection_pairing (xi:UT->exterior_power X (k+p))
    (psi:Y->A_m Y R^o k) (phi:E) (x:UT):
  pairing (@current_image_density R v n (k+p) U f xi x)
    (form_wedge h2 (scalar_bilinear R) (psi (f (set_val x))) (ev phi (f (set_val x))))=
  pairing (xi x) (form_wedge h2 (scalar_bilinear R)
    (@current_form_pullback_on_domain R v n k U V f psi x) (fv (pull phi) (set_val x))).
Proof.
pose D:=@current_map_differential R v n U f (set_val x).
rewrite (@current_form_pullback_on_domain_actual R v n k U V f psi hImage hf x).
rewrite (@smooth_form_pullback_values R v n p U V E F ev fv f pull
  (@SmoothFormPullback.laws R h2 v n p U V hU hV f hImage hf)
  phi (set_val x) D (set_valP x)
  (@current_map_differential_actual R v n U f hf (set_val x) (set_valP x))).
rewrite -(@form_pullback_product R h2 X Y R^o (hom_as_linear D)
  (fun a b=>a*b) (scalar_bilinear R) k p (psi (f (set_val x))) (ev phi (f (set_val x))))
  A_m_dual_pairing;by [].
Qed.
End CurrentBaireProjectionPairing.
