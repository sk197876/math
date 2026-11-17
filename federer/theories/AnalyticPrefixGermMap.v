(** Federer (1969), 3.4.8(1), p. 326:
    the original prefix projection induces a homomorphism
    of the actual analytic germ rings at zero.
    The maps remain behind the coordinate and pointed
    pullback seals; this module supplies their proved types. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormAnalyticUP
  AnalyticGermUP AnalyticGermRing PointedAnalyticPullbackSealed
  PointedAnalyticPullbackRingMorphism AnalyticPrefixCoordinatesSealed AnalyticPrefixMapRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixGerms.
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

(** Source for [analytic_prefix_projection_at_origin]: the
    original p_j is analytic at zero, supporting
    3.4.8(1), p. 326. *)
Lemma analytic_prefix_projection_at_origin:
  @norm_analytic_at R X Y NX NY hNX hNY setT p 0.
Proof. exact:((@analytic_prefix_projection_analytic R X NX hNX n e j p he) 0 Logic.I). Qed.

(** Source for [analytic_prefix_projection_zero]: the original
    linear p_j preserves the original centre, supporting
    3.4.8(1), p. 326. *)
Lemma analytic_prefix_projection_zero:p 0=0.
Proof. exact:linear0 p. Qed.

(** Source for [analytic_prefix_germ_map]: the original
    homomorphism O_0(p_j), 3.4.8(1), p. 326.
    Its values are the sealed pointed pullback; the
    proved arithmetic supplies the ring hierarchy. *)
Definition analytic_prefix_germ_map:
    {rmorphism [the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)]->
      [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]}:=
  @pointed_analytic_germ_ring_pullback R X Y NX NY hNX hNY p 0 0
    (@PointedAnalyticPullback.map R X Y NX NY hNX hNY setT p 0 0
      analytic_prefix_projection_at_origin analytic_prefix_projection_zero)
    (@PointedAnalyticPullback.laws R X Y NX NY hNX hNY setT p 0 0
      analytic_prefix_projection_at_origin analytic_prefix_projection_zero).
End PrefixGerms.
