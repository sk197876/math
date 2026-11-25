(** Federer (1969), 1.8.2, p. 40: Wirtinger's upper bound
    for a simple unit 2m-vector, and the necessity of the printed
    complex paired representation in the equality case. The proof
    restricts to the finite-dimensional associated space and follows
    the book's alternating two-form normal-form computation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors SimpleUnitAssociatedLift
  SubspaceCarrier InnerProductRestriction OrthogonalMaps ScalarRestriction
  ComplexScalarSealed ComplexPairedVectors HermitianUP HermitianRealImaginary
  HermitianRotation HermitianNormalCoefficients TwoFormPowers TwoFormPowerNaturality
  TwoFormVectorNormalForm TwoFormNormalPowers PairedOrthonormalDimension
  NormalPowerUnitBound PairedRealVectors PairedVectorNaturality ExteriorNorm
  InnerPolarity SkewNormalFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [wirtinger_unit_bound_and_equality_forward]: Federer
    1.8.2, p. 40, the unit-vector normal-form proof: the pairing is
    at most m!, and equality forces the vector to be a product of
    m complex real-imaginary pairs. No finite ambient dimension is assumed. *)
Theorem wirtinger_unit_bound_and_equality_forward (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType (ComplexScalars.C R))
    (H : V -> V -> ComplexScalars.C R) (hH : is_hermitian_product H)
    m (x : exterior_power (restricted_space (ComplexScalars.embed R) V) (m+m))
    (hs : simple x) (hx : exterior_norm h2 (hermitian_real_inner_product hH) x = 1) :
  pairing x (two_form_power h2 (hermitian_two_form hH) m) <= m`!%:R /\
  (pairing x (two_form_power h2 (hermitian_two_form hH) m) = m`!%:R ->
    exists v : 'I_m -> V, x = paired_complex_vector v).
Proof.
pose VR := restricted_space (ComplexScalars.embed R) V.
pose U := GRing.Lmodule.clone R (subspace_space (FedererSimple.T x)) _.
pose D := @restricted_inner_product R VR (hermitian_real_part H) (FedererSimple.T x).
pose hD := restricted_inner_productP (hermitian_real_inner_product hH) (FedererSimple.T x).
pose f : {linear U -> VR} := GRing.Linear.clone _ _ _ _
  (@subspace_val R VR (FedererSimple.T x)) _.
have hf : is_orthogonal_map D (hermitian_real_part H) f by move=> u v.
have [e [he [hy hyx]]] := @simple_unit_associated_lift R h2 VR
  (hermitian_real_part H) (hermitian_real_inner_product hH) (m+m) x hs hx.
pose y := e_lambda e (ord_tuple (m+m)).
pose phi := A_m_dual f (hermitian_two_form hH).
have [k [a [b [lambda [ho [h0 hn]]]]]] :=
  @alternating_two_form_vector_normal_form R h2 U D hD (m+m) e he phi.
have hk : (k <= m)%N := @orthonormal_pairs_dimension_bound R U D hD m e he k a b ho.
have hp : pairing x (two_form_power h2 (hermitian_two_form hH) m) =
    pairing y (two_form_power h2 phi m).
  rewrite /phi -two_form_power_natural A_m_dual_pairing.
  by rewrite /y hyx.
rewrite hp.
case hkm : (k == m).
- move/eqP: hkm=> hkm; subst k.
  have h1 i : lambda i <= 1 := @hermitian_normal_coefficient_bound R h2 V H hH
    U D hD f hf m a b lambda ho hn i.
  split.
  + rewrite hn; exact: (@normal_two_form_unit_bound R h2 U D hD m a b lambda ho h0 h1 y hy).
  + move=> hequal; rewrite hn in hequal.
    have [hyab hl] := proj1 (@normal_two_form_unit_equality R h2 U D hD m a b lambda
      ho h0 h1 y hy) hequal.
    have hb i : f (b i) = hermitian_rotation (f (a i)).
      exact: (proj1 (@hermitian_normal_coefficient_equality R h2 V H hH
        U D hD f hf m a b lambda ho hn i) (hl i)).
    exists (fun i => f (a i)).
    rewrite -hyx -/y hyab paired_real_vector_natural.
    have hbf : (fun i => f (b i)) = (fun i => ComplexScalars.ii R *: f (a i)).
      apply: funext => i; exact: hb.
    by rewrite hbf paired_real_complex_identification.
- have hlt : (k < m)%N by rewrite ltn_neqAle hkm hk.
  rewrite hn (@normal_two_form_power_above_blocks R h2 U k
      (fun i => inner_polarity hD (a i)) (fun i => inner_polarity hD (b i)) lambda m hlt)
    (bil0r (@pairing_bilinear R U R^o (m+m))).
  split; first exact: ler0n.
  move=> hzero.
  have hfac : (m`!%:R : R) != 0 by rewrite pnatr_eq0 -lt0n fact_gt0.
  by move: hfac; rewrite -hzero eqxx.
Qed.
