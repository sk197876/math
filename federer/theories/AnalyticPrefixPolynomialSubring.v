(** Federer (1969), 3.4.8(1),(8), pp. 326,
    329–330: original prefix rings are nested,
    and original polynomials in the next
    coordinate belong to the next prefix
    ring. Apply the existing pointed prefix
    composition and polynomial-image theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanScalarCoordinateMaps
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticCoordinateGermsSealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixNestedComposition
  AnalyticPrefixCoordinateGerm AnalyticPrefixGermSubring AnalyticPrefixGermSubringLaws
  CommutativeSubringUP CommutativePolynomialUP CommutativePolynomialEvaluationUP PolynomialEvaluationImage
  WeierstrassFunctionalPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixPolynomials.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Variable j:'I_n.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation Y:=(R_n R (j:nat).+1).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (j:nat).+1)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (j:nat).+1)).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R (j:nat))
  (inner_norm (@euclidean_inner_productP R (j:nat)))
  (inner_norm_real_norm (@euclidean_inner_productP R (j:nat))) 0)].
Local Notation A1:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation E0:=(@analytic_prefix_germ_map R X NX hNX n e he omega (j:nat) hJN).
Local Notation E1:=(@analytic_prefix_germ_map R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)).
Local Notation Q1:=(@analytic_prefix_germ_subring R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)).
Local Notation Gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).

(** Source for [analytic_adjacent_prefix_factorisation]:
    original prefix germ pullbacks factor
    through the next prefix, 3.4.8(1),(8),
    pp. 326, 329. Apply the existing
    exact adjacent composition theorem. *)
Theorem analytic_adjacent_prefix_factorisation:
  exists F:{rmorphism A->A1},forall a:A,E0 a = E1 (F a).
Proof.
pose covector:=fun i:'I_(j:nat).+1=>@euclidean_scalar_coordinate_map R (j:nat).+1 i.
pose P:=@AnalyticPrefixCoordinates.projection R Y (j:nat).+1 covector (j:nat) (leqnSn (j:nat)).
pose F:=@analytic_prefix_germ_map R Y NY hNY (j:nat).+1
  (@coordinate_basis R (j:nat).+1) (@coordinate_basisP R (j:nat).+1) covector (j:nat) (leqnSn (j:nat)).
have hP:=@AnalyticPrefixCoordinates.projection_laws R Y (j:nat).+1 covector (j:nat) (leqnSn (j:nat)).
have hF:=@analytic_prefix_germ_map_specification R Y NY hNY (j:nat).+1
  (@coordinate_basis R (j:nat).+1) (@coordinate_basisP R (j:nat).+1) covector (j:nat) (leqnSn (j:nat)).
exists F.
exact:(@analytic_adjacent_prefix_germ_composition R X NX hNX n omega (j:nat) hJN (ltn_ord j)
  (@AnalyticPrefixCoordinates.projection R X n omega (j:nat) hJN)
  (@AnalyticPrefixCoordinates.projection R X n omega (j:nat).+1 (ltn_ord j)) P E0 E1 F
  (@AnalyticPrefixCoordinates.projection_laws R X n omega (j:nat) hJN)
  (@AnalyticPrefixCoordinates.projection_laws R X n omega (j:nat).+1 (ltn_ord j)) hP
  (@analytic_prefix_germ_map_specification R X NX hNX n e he omega (j:nat) hJN)
  (@analytic_prefix_germ_map_specification R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)) hF).
Qed.

(** Source for [analytic_next_prefix_coordinate_member]:
    the next original coordinate germ belongs
    to its original prefix ring, 3.4.8(1),
    p. 326. An actual coordinate representative
    and the checked prefix-coordinate identity
    prove membership. *)
Theorem analytic_next_prefix_coordinate_member:Q1 Gamma.
Proof.
pose xi:=@euclidean_scalar_coordinate_map R (j:nat).+1 ord_max.
have hBound:=@euclidean_scalar_coordinate_bounded R (j:nat).+1 ord_max.
have [f [hF _]]:=@weierstrass_functional_power_representative R Y NY hNY xi 1 hBound.
have hValues y:analytic_representative_value f y = y ord_max by rewrite hF expr1.
apply/analytic_prefix_germ_subring_membership;exists (analytic_germ f).
exact:(@analytic_prefix_last_coordinate_germ R X NX hNX n e he omega j f hValues).
Qed.

(** Source for [analytic_prefix_polynomial_member]: every
    original polynomial in gamma_j with
    coefficients in Q_j belongs to Q_(j+1),
    as used for the original numerator
    in 3.4.8(8), p. 330. Apply the
    existing least polynomial-image subring law. *)
Theorem analytic_prefix_polynomial_member (P:comNzRingType)
  (embed:{rmorphism A->P}) (variable:P) (coefficient:P->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism P->G}):
  is_commutative_polynomial_evaluation embed variable E0 Gamma J ->forall H:P,Q1 (J H).
Proof.
move=>hJ.
have hImage:=@polynomial_evaluation_image_generated A P G embed variable coefficient hP E0 Gamma J hJ.
have hRing:=@analytic_prefix_germ_subring_laws R X NX hNX n e he omega (j:nat).+1 (ltn_ord j).
have [F hF]:=analytic_adjacent_prefix_factorisation.
have hGenerators:(fun a:G=>a = Gamma \/exists b:A,a = E0 b) `<=` Q1.
  move=>a [->|[b ->]];first exact:analytic_next_prefix_coordinate_member.
  apply/analytic_prefix_germ_subring_membership;exists (F b);exact:esym (hF b).
have hAll:=generated_commutative_subring_minimal hImage hRing hGenerators.
move=>H;apply:hAll;by exists H.
Qed.
End PrefixPolynomials.
