(** Federer (1969), 4.1.25, p. 383: the compact
    summable field in the first displayed pushforward formula
    gives an actual finite-mass flat current. These facts
    follow from the preceding 4.1.18, p. 375; normality
    is not assumed or needed. The generic source degree
    also supplies the original zero-dimensional endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentMassSealed FlatCurrentsUP
  FlatCurrentFinite CurrentLipschitzCompactImage SmoothCompactSet
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorLinear CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairGlobalFlat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LebesgueActionDensity.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation W k := (@compact_summable_multivector_space R h2 n k U hU).
Local Notation D k := (@compact_summable_multivector_current R h2 n k U hU).
Local Notation H k := (@compact_summable_multivector_current_hom R h2 n k U hU).
Local Notation bd := (@current_boundary R h2 n d U hU).

(** Source for [current_lipschitz_lebesgue_action_density_flat]:
    the actual Lebesgue density current is flat by applying
    4.1.18, p. 375, to the pair (xi,0). This derives
    the input requirement of 4.1.14 before the Lipschitz
    pushforward in 4.1.25, p. 383, is used. *)
Theorem current_lipschitz_lebesgue_action_density_flat (xi : W d) :
  @is_flat_current R h2 n d U hU (D d xi).
Proof.
pose v : @current_lone_pair_space R h2 n d U hU := (xi,0).
have hFlat := @current_lone_pair_is_flat R h2 n d U hU v.
have hValue := @CurrentLonePair.laws R h2 n d U hU v.
change (@CurrentLonePair.map R h2 n d U hU v = D d xi+bd (H d.+1 0)) in hValue.
rewrite (Bilinear.lin0 (hom_linear (H d.+1)))
  (Bilinear.lin0 (hom_linear bd)) addr0 in hValue.
by rewrite hValue in hFlat.
Qed.

(** Source for [current_lipschitz_lebesgue_action_density_finite_mass]:
    the original summability hypothesis gives finite mass,
    with its exact preceding L1 value, supporting the
    dominated-convergence proof in 4.1.25, p. 383. *)
Theorem current_lipschitz_lebesgue_action_density_finite_mass (xi : W d) :
  (@CurrentMass.value R h2 n d U hU (D d xi) < +oo)%E.
Proof.
rewrite (@compact_summable_multivector_current_mass R h2 n d U hU xi).
exact: ltry.
Qed.

(** Source for [current_lipschitz_lebesgue_action_density_compact]:
    the original density current has compact actual support,
    supplying its smooth-image approximants in the first
    formula of 4.1.25, p. 383. A compact flat index
    is derived internally rather than required from a caller. *)
Theorem current_lipschitz_lebesgue_action_density_compact (xi : W d) :
  @compact (real_norm_metric_space hNX)
    (@current_support R h2 n U hU d (D d xi)).
Proof.
have [K hK] := @current_lipschitz_lebesgue_action_density_flat xi.
exact: (@flat_supported_current_compact R h2 n d U hU K (D d xi) hK).
Qed.
End LebesgueActionDensity.
