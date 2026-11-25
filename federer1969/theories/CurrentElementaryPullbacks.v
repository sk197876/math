(** Federer (1969), 4.1.10, p. 364: identity pullback is the
    identity and constant-map pullback vanishes in positive degree.
    The last paragraph permits any original open U. Reuse the
    actual differential, sealed smooth pullback and exterior map laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers
  ExteriorMapScaling AlternatingForms AlternatingDual AlternatingPairing
  CurrentSpaces SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_positive_zero_dual]: a zero linear map
    induces the zero map on positive covector degrees, by Federer
    1.3.1 and 1.4.1, pp. 14 and 17, supporting 4.1.10, p. 364. *)
Lemma current_positive_zero_dual (R : fieldType) (X Y : lmodType R) j
    (a : A_m Y R^o j.+1) :
  A_m_dual (hom_as_linear (0 : Hom X Y)) a=0.
Proof.
apply: pairing_ext => eta.
rewrite A_m_dual_pairing.
have hZero : forall v : X,
    hom_as_linear (0 : Hom X Y) v=(0:R)*:hom_as_linear (0 : Hom X Y) v.
  move=> v; change ((0:Y)=(0:R)*:(0:Y)); by rewrite scaler0.
have hScale := @exterior_power_map_scale R X Y
  (hom_as_linear (0 : Hom X Y)) (hom_as_linear (0 : Hom X Y)) 0
  hZero j.+1 eta.
rewrite exprS mul0r scale0r in hScale.
rewrite hScale.
by rewrite (lin0 ((@pairing_bilinear R Y R^o j.+1).1 a))
  (lin0 ((@pairing_bilinear R X R^o j.+1).2 eta)).
Qed.

Section CurrentElementaryPullbacks.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.

(** Source for [current_identity_pullback_values]: the identity
    map leaves every original form value unchanged, Federer
    4.1.10, p. 364. The source may be an open subset of the target. *)
Theorem current_identity_pullback_values j (V : set X)
    (hV : forall x, V x -> norm_domain_interior NX V x)
    (hImage : forall x, U x -> V x)
    (hId : norm_class_all_orders hNX hNX U (fun x:X => x))
    (psi : @current_smooth_space R h2 n V hV j) x : U x ->
  @current_smooth_value R h2 n U hU j
    (@SmoothFormPullback.operator R h2 n n j U V hU hV
      (fun x:X => x) hImage hId psi) x=
  @current_smooth_value R h2 n V hV j psi x.
Proof.
move=> hx.
pose I : Hom X X := hom_of_linear (linear_id X).
have hBound : norm_bounded_linear NX NX I.
  exists 1; split; first exact: ler01.
  by move=> z; change (NX z<=1*NX z); rewrite mul1r.
have hD := @norm_differential_linear R X X NX NX hNX hNX
  U x I (@hU x hx) hBound.
rewrite (@smooth_form_pullback_values R n n j U V
  (@current_smooth_space R h2 n V hV j) (@current_smooth_space R h2 n U hU j)
  (@current_smooth_value R h2 n V hV j) (@current_smooth_value R h2 n U hU j)
  (fun x:X => x) _ (@SmoothFormPullback.laws R h2 n n j U V hU hV
    (fun x:X => x) hImage hId) psi x I hx hD).
apply: pairing_ext => eta; rewrite A_m_dual_pairing.
have hIdMap := @exterior_power_map_ext R X X (hom_as_linear I)
  (linear_id X) (fun z => erefl z) j eta.
by rewrite hIdMap exterior_power_map_identity.
Qed.

(** Source for [current_identity_pullback]: g#psi=psi for
    the identity g, Federer 4.1.10, p. 364. This includes the
    original compact tests through their actual smooth inclusion. *)
Theorem current_identity_pullback j
    (hImage : forall x, U x -> U x)
    (hId : norm_class_all_orders hNX hNX U (fun x:X => x))
    (psi : @current_smooth_space R h2 n U hU j) :
  @SmoothFormPullback.operator R h2 n n j U U hU hU
    (fun x:X => x) hImage hId psi=psi.
Proof.
apply: (smooth_function_extensional (@current_smooth_space_laws R h2 n U hU j)).
exact: current_identity_pullback_values.
Qed.

(** Source for [current_constant_positive_pullback]: f#psi=0
    for a constant f in every positive degree, Federer 4.1.10,
    p. 364. No compactness or closedness is needed for this law. *)
Theorem current_constant_positive_pullback j (V : set X)
    (hV : forall x, V x -> norm_domain_interior NX V x) (u : X)
    (hImage : forall x, U x -> V u)
    (hConst : norm_class_all_orders hNX hNX U (fun _:X => u))
    (psi : @current_smooth_space R h2 n V hV j.+1) :
  @SmoothFormPullback.operator R h2 n n j.+1 U V hU hV
    (fun _:X => u) hImage hConst psi=0.
Proof.
apply: (smooth_function_extensional (@current_smooth_space_laws R h2 n U hU j.+1)) => x hx.
have hD := @norm_differential_constant R X X NX NX hNX hNX U x u (@hU x hx).
rewrite (@smooth_form_pullback_values R n n j.+1 U V
  (@current_smooth_space R h2 n V hV j.+1) (@current_smooth_space R h2 n U hU j.+1)
  (@current_smooth_value R h2 n V hV j.+1) (@current_smooth_value R h2 n U hU j.+1)
  (fun _:X => u) _ (@SmoothFormPullback.laws R h2 n n j.+1 U V hU hV
    (fun _:X => u) hImage hConst) psi x (0:Hom X X) hx hD).
rewrite current_positive_zero_dual.
change (0=smooth_function_values_hom (@current_smooth_space_laws R h2 n U hU j.+1) 0 x).
by rewrite linear0.
Qed.
End CurrentElementaryPullbacks.
