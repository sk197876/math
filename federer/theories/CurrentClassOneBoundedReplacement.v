(** Federer (1969), 4.1.19, p. 377: localize
    a class-one form and its actual derivative near
    the compact carrier of a coefficient probe. Reuse
    the original class-one compact replacement of 4.1.7,
    p. 358, and its continuous compact bounds. *)
From mathcomp Require Import functions all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorDerivativeUP CurrentDomain CurrentCoefficientNorms
  SmoothCompactSet CurrentClassOneCutoff FlatCochainRepresentationUP
  CompactContinuousCurrentFormBounded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_class_one_bounded_replacement]:
    the original class-one weak derivative comparison
    in Federer 4.1.19, p. 377,
    may use bounded representatives internally near
    any prescribed compact K. The original phi
    and derivative remain unchanged on that K;
    their own global bounds are not assumed. *)
Theorem current_class_one_bounded_replacement
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (phi : R_n R n -> A_m (R_n R n) R^o m)
    (beta : R_n R n -> A_m (R_n R n) R^o m.+1) :
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@current_form_comass_real_norm R h2 n m) U phi 1%N ->
  (forall x, U x -> has_exterior_derivative
    (inner_norm (@euclidean_inner_productP R n))
    (@current_form_comass R h2 n m) U phi x (beta x)) ->
  exists chi : R_n R n -> A_m (R_n R n) R^o m,
  exists b : R_n R n -> A_m (R_n R n) R^o m.+1,
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
      (@current_form_comass_real_norm R h2 n m) U chi 1%N /\
    (forall x, U x -> has_exterior_derivative
      (inner_norm (@euclidean_inner_productP R n))
      (@current_form_comass R h2 n m) U chi x (b x)) /\
    @is_bounded_measurable_current_form R h2 n U m
      (fun x : current_domain R n U => chi (set_val x)) /\
    @is_bounded_measurable_current_form R h2 n U m.+1
      (fun x : current_domain R n U => b (set_val x)) /\
    forall x, smooth_compact_carrier K x -> chi x=phi x /\ b x=beta x.
Proof.
move=> hClass hActual.
pose X := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose Y := A_m X R^o m.
pose Z := A_m X R^o m.+1.
pose NY := @current_form_comass R h2 n m.
pose hNY := @current_form_comass_real_norm R h2 n m.
pose NZ := @current_form_comass R h2 n m.+1.
pose hNZ := @current_form_comass_real_norm R h2 n m.+1.
have [C [chi [b [hChi [hB [hExterior [hOff
    [W [hW [hKW [hWU hAgreement]]]]]]]]]]] :=
  @current_class_one_compact_replacement R h2 n m U hU K phi beta hClass hActual.
have hChiU := @norm_class_open_restriction R X Y NX NY hNX hNY
  setT U chi 1%N (fun _ _ => Logic.I) hU hChi.
have hBU := @norm_class_open_restriction R X Z NX NZ hNX hNZ setT U b 0%N
  (fun _ _ => Logic.I) hU ((@norm_class_zeroP R X Z NX NZ hNX hNZ setT b).2 hB).
have hExteriorU (x : X) (hx : U x) : has_exterior_derivative NX NY U chi x (b x).
  have [L [hL hValue]] := hExterior x.
  exists L; split; last exact: hValue.
  exact: (@norm_differential_restrict R X Y NX NY setT U chi x L
    (fun _ _ => Logic.I) (@hU x hx) hL).
exists chi,b; split; first exact: hChiU.
split; first exact: hExteriorU.
split.
- exact: (@compact_continuous_current_form_bounded R h2 n m U hU C chi
    (norm_class_continuous hChiU) (fun x _ hx => (hOff x hx).1)).
split.
- exact: (@compact_continuous_current_form_bounded R h2 n m.+1 U hU C b
    (norm_class_continuous hBU) (fun x _ hx => (hOff x hx).2)).
- move=> x hx; exact: (@hAgreement x (@hKW x hx)).
Qed.
