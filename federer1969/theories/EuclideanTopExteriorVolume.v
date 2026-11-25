(** Federer (1969), 3.2.20, p. 257: supporting top-degree
    volume scaling for the displayed Jacobian composition identity.
    It is the homogeneous form of 1.7.6, p. 34, where the
    exterior degree equals the source dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerNormalization InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorGrading
  ExteriorMaps TopExteriorNorm EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_exterior_volume_scale]: the homogeneous
    form of the top-degree statement in Federer 1.7.6, p. 34,
    used for the Jacobian product in 3.2.20, p. 257. Every
    top vector has image norm J_m(L) times its source norm. Zero
    vectors and zero-dimensional source are retained. *)
Theorem euclidean_top_exterior_volume_scale (R : realType) m n
    (L : Hom (R_n R m) (R_n R n)) (xi : exterior_power (R_n R m) m) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (exterior_power_map (hom_as_linear L) m xi)=
  euclidean_linear_jacobian m L*
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) xi.
Proof.
pose h2 := euclidean_two_nonzero R.
pose hB := @euclidean_inner_productP R m.
pose hC := @euclidean_inner_productP R n.
pose hE := @exterior_inner_productP R h2 (R_n R m) (@euclidean_inner_product R m) hB m.
case: (eqVneq xi 0)=> [->|hXi].
- by rewrite linear0 !exterior_norm_zero mulr0.
pose u := inner_normalize hE xi.
have hUnit : exterior_norm h2 hB u= 1.
  exact: (inner_normalize_norm hE hXi).
have hValue := @top_exterior_operator_unit_value R h2 (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n) hB hC
  m (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear L) u hUnit.
have hK := inner_normalizeK hE hXi.
have hImage := congr1 (exterior_power_map (hom_as_linear L) m) hK.
rewrite linearZ in hImage.
rewrite -hImage exterior_norm_scale.
have hNonnegative : 0<=exterior_norm h2 hB xi := exterior_norm_nonnegative h2 hB xi.
rewrite (ger0_norm hNonnegative) -hValue mulrC; reflexivity.
Qed.
