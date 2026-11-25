(** Federer (1969), 1.8.4, p. 40: the orthonormal
    covectors omega_1,...,omega_p pair with xi to its mass and
    annihilate T. The choice is made for nonzero xi; for a zero
    exterior space a p-frame need not exist. The main mass product
    theorem handles zero xi separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SubspaceCarrier InnerProductUP InnerProductRestriction
  InnerPolarity InnerDual InnerExterior InnerExteriorProducts ExteriorNorm ExteriorNormNaturality
  ExteriorMaps CovectorProductNaturality ExteriorGrading AlternatingCoordinates CovectorProducts
  OrthonormalFamilies OrthogonalMaps ComassUP ComassSimpleEquality ExteriorCovectorInner
  MassUP MassEquality LinearBasis PositiveSimpleOrthonormalFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simple_orthogonal_calibration]: Federer 1.8.4,
    p. 40, the orthonormal annihilating-covector choice used in
    the proof, together with the unit comass of their product.
    Nonvanishing is required for this auxiliary frame choice;
    it is not a restriction on the main product theorem. *)
Theorem simple_orthogonal_calibration (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (S T : subspace V)
    (hST : forall u v, S u -> T v -> B u v = 0)
    p (hp : (0 < p)%N) (kp : A_m V R^o p -> R)
    (hkp : forall phi, is_comass h2 hB phi (kp phi))
    (x0 : exterior_power (subspace_space S) p) a
    (hx : simple (exterior_power_map (subspace_inclusion S) p x0))
    (hxn : exterior_power_map (subspace_inclusion S) p x0 != 0)
    (ha : is_mass kp (exterior_power_map (subspace_inclusion S) p x0) a) :
  exists w : 'I_p -> A_m V R^o 1,
    orthonormal_family (inner_dual_product hB hb) w /\
    (forall i z, T z -> w i [tuple z] = 0) /\
    pairing (exterior_power_map (subspace_inclusion S) p x0)
      (one_forms_wedge h2 (scalar_bilinear R) (1 : R^o) w) = a /\
    kp (one_forms_wedge h2 (scalar_bilinear R) (1 : R^o) w) = 1.
Proof.
pose U := GRing.Lmodule.clone R (subspace_space S) _.
pose C := @restricted_inner_product R V B S.
pose hC := restricted_inner_productP hB S.
pose x := exterior_power_map (subspace_inclusion S) p x0.
have hx0 : x0 != 0.
  apply/eqP=> hz; move: hxn; by rewrite hz linear0 eqxx.
have hs0 : simple x0.
  have hh := exterior_power_map_simple (subspace_retraction S) hx.
  rewrite (@exterior_power_mapK R (GRing.Lmodule.clone R (subspace_space S) _) V
      (subspace_inclusion S) (subspace_retraction S) (@subspace_retractionK R V S) p) in hh.
    exact hh.
have [u [hu hxu]] := @simple_positive_orthonormal_factor R h2 U C hC p hp x0 hx0 hs0.
pose e := fun i => subspace_inclusion S (u i).
have he : orthonormal_family B e by move=> i j; exact: hu.
have hi : OrthogonalMaps.is_orthogonal_map C B (subspace_inclusion S) by move=> v w.
have hN : exterior_norm h2 hB x = exterior_norm h2 hC x0.
  exact (@exterior_norm_orthogonal_natural R h2 U V C B hC hB
    (subspace_inclusion S) hi p x0).
have hxe : x = exterior_norm h2 hB x *: e_lambda e (ord_tuple p).
  have hh := congr1 (exterior_power_map (subspace_inclusion S) p) hxu.
  by rewrite linearZ exterior_basis_product_natural -hN in hh.
pose w := fun i => inner_polarity hB (e i).
have hw : one_forms_wedge h2 (scalar_bilinear R) (1 : R^o) w =
    inner_exterior_form h2 hB (e_lambda e (ord_tuple p)).
  by rewrite inner_exterior_product_covectors.
exists w; split.
- move=> i j; by rewrite /w inner_dual_polarityE he.
- split.
  + move=> i z hz; rewrite /w inner_polarityE (inner_symmetric hB).
    apply: hST hz; exact: subspace_valP.
  + rewrite hw; split.
    * have haN := @simple_mass_euclidean R h2 V B hB n b hb p hp kp hkp x a hx ha.
      rewrite -/x {1}hxe (bilZl (@pairing_bilinear R V R^o p)).
      change (exterior_norm h2 hB x * exterior_inner_form h2 hB
        (e_lambda e (ord_tuple p)) (e_lambda e (ord_tuple p)) = a).
      by rewrite -exterior_norm_square (orthonormal_product_unit_norm h2 hB he) expr1n mulr1 -haN.
    * have hs := inner_exterior_simple h2 hB (product_simple e).
      have hh := @simple_comass_euclidean R h2 V B hB n b hb p hp _ _ hs (hkp _).
      by rewrite inner_exterior_form_norm (orthonormal_product_unit_norm h2 hB he) in hh.
Qed.
