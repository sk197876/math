(** Federer (1969), 4.1.7, p. 359:
    the exact exterior differential image used
    in the weighted variation inequality. The
    pairing identity is the original 1.4.1,
    pp. 17–18, applied to actual smooth
    pullbacks and the actual Df. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals functions topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorMaps AlternatingForms
  AlternatingPairing AlternatingDual CurrentDomain CurrentSpaces CurrentConstantFields
  CurrentMapDifferential SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentImageDensityPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
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
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation UT := (current_domain R v U).
Local Notation E := (@current_smooth_space R h2 n V hV m).
Local Notation F := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).

(** Source for [current_image_density]: the literal
    exterior differential image Lambda_m Df(x)(xi(x)),
    supporting the original weighted inequality in
    Federer 4.1.7, p. 359. It is
    not normalized, and its mass is retained. *)
Definition current_image_density (xi:UT->exterior_power X m) (x:UT):exterior_power Y m:=
  exterior_power_map (hom_as_linear (@current_map_differential R v n U f (set_val x))) m (xi x).

(** Source for [current_image_density_pairing]: exact
    pairing of the pushed exterior density equals
    pairing of the original density with the
    actual smooth pullback, supporting Federer
    4.1.7, p. 359. All degrees, including
    zero, follow from the same original law. *)
Theorem current_image_density_pairing (xi:UT->exterior_power X m) (phi:E) (x:UT):
  pairing (current_image_density xi x) (ev phi (f (set_val x)))=
    pairing (xi x) (fv (pull phi) (set_val x)).
Proof.
rewrite (@smooth_form_pullback_values R v n m U V E F ev fv f pull
  (@SmoothFormPullback.laws R h2 v n m U V hU hV f hImage hf)
  phi (set_val x) (@current_map_differential R v n U f (set_val x)) (set_valP x)
  (@current_map_differential_actual R v n U f hf (set_val x) (set_valP x)))
  A_m_dual_pairing;by [].
Qed.

(** Source for [current_image_density_constant_pairing]:
    every fixed target covector coordinate of
    the exact image density is paired with
    a genuine original smooth source field,
    supporting measurability and compact bounds
    in Federer 4.1.7, p. 359. *)
Lemma current_image_density_constant_pairing (xi:UT->exterior_power X m)
    (a:A_m Y R^o m) (x:UT):
  pairing (current_image_density xi x) a=
    pairing (xi x) (fv (pull (@current_constant_form R h2 n V hV m a)) (set_val x)).
Proof.
have h:=current_image_density_pairing xi (@current_constant_form R h2 n V hV m a) x.
by rewrite (@current_constant_form_values R h2 n V hV m a (f (set_val x))
  (hImage (set_val x) (set_valP x))) in h.
Qed.
End CurrentImageDensityPairing.
