(** Federer (1969), 3.4.8(1), p. 326:
    the original prefix germ map retains every actual
    representative equation and every scalar constant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing PointedAnalyticPullbackUP PointedAnalyticPullbackSealed
  PointedAnalyticPullbackRing AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section MapLaws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Variable j:nat.
Hypothesis hjn:(j<=n)%N.
Local Notation Y:=(R_n R j).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R j)).
Local Notation p:=(@AnalyticPrefixCoordinates.projection R X n omega j hjn).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega j hjn).

(** Source for [analytic_prefix_germ_map_specification]: every
    original germ is pulled back by actual composition
    with p_j, 3.4.8(1), p. 326. *)
Lemma analytic_prefix_germ_map_specification:is_pointed_analytic_germ_pullback p E.
Proof.
exact:(@PointedAnalyticPullback.laws R X Y NX NY hNX hNY _ p 0 0
  (@analytic_prefix_projection_at_origin R X NX hNX n e he omega j hjn)
  (@analytic_prefix_projection_zero R X n omega j hjn)).
Qed.

(** Source for [analytic_prefix_germ_map_constant]: scalar
    constants are unchanged by the original coordinate
    pullback, supporting Q_0=R in 3.4.8(1), p. 326. *)
Lemma analytic_prefix_germ_map_constant (c:R):
  E (analytic_germ (@analytic_constant_representative R Y NY hNY 0 c))=
    analytic_germ (@analytic_constant_representative R X NX hNX 0 c).
Proof.
exact:(@pointed_analytic_pullback_constant R X Y NX NY hNX hNY 0 0 p E
  analytic_prefix_germ_map_specification c).
Qed.
End MapLaws.
