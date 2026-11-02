(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureAlmostBasic MeasureDerivationContext
  FivefoldBallGrowth GrowthCenteredVitali NullBallLocus CenteredRatioInfinity
  CenteredBallRelations CenteredBallVitali CoveringRelationUP DirectionalLimitationUP
  DerivationExceptionalSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_centered_density_geometry]: direct two
    alternative hypotheses of Federer 2.9.15, p. 160.
    The first is the finite upper fivefold ball-ratio limit
    everywhere. The second is separability and an exact
    countable cover by directionally limited targets, with
    the parameters allowed to depend on the target. *)
Definition is_centered_density_geometry (R : realType) (X : metricType R)
    (phi : set X -> \bar R) : Prop :=
  (forall x, fivefold_ball_ratio_upper_limit phi x< +oo) \/
  ((exists D : set X, countable D /\ dense D) /\
    exists K : set (set X), countable K /\ (\bigcup_(A in K) A)=setT /\
      forall A, K A -> exists (xi : \bar R) (eta : R) (zeta : nat),
        is_directionally_limited_at A xi eta zeta).

(** Source for [geometric_centered_balls_vitali]: direct
    centered-ball Vitali assertion in the first proof paragraph
    of Federer 2.9.15, p. 160. Apply the local-growth
    adequacy argument in the first alternative and the exact
    countable directional-cover theorem 2.8.18 in the second. *)
Theorem geometric_centered_balls_vitali (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V0 : X -> set X -> Prop) :
  is_measure_derivation_context phi V0 -> is_centered_density_geometry phi ->
  is_vitali_relation phi (@centered_closed_ball_relation R X).
Proof.
move=> hc; case=> hgrowth; first exact: fivefold_growth_centered_balls_vitali hc hgrowth.
have [hsep [K [hK [hcover hdir]]]] := hgrowth.
have hphi := derivation_context_measure hc.
have hctx := @centered_subrelation_covering_context R X phi
  (@centered_closed_ball_relation R X) setT hphi (fun x S h => h).
exact: (@federer_2_8_18 R X phi K hctx hsep hK hcover hdir).
Qed.

(** Source for [measure_infinite_centered_density_points_null]:
    direct nullity of W in the first proof paragraph of
    Federer 2.9.15, p. 160, by 2.9.5, pp. 154–155.
    The geometric hypotheses give the new centered Vitali
    relation; an infinite radial limit lies in its infinite
    upper-derivate exceptional set. *)
Lemma measure_infinite_centered_density_points_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V0 : X -> set X -> Prop) :
  is_measure_derivation_context phi V0 -> is_derivation_measure psi ->
  is_centered_density_geometry phi -> phi (measure_infinite_centered_density_points psi phi)=0.
Proof.
move=> hc hpsi hgeo; have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hv := @geometric_centered_balls_vitali R X phi V0 hc hgeo.
have hctx : is_measure_derivation_context phi (@centered_closed_ball_relation R X) by constructor.
have hnull := @derivation_infinite_upper_points_null R X phi psi
  (@centered_closed_ball_relation R X) hctx hpsi.
apply: (@measure_null_subset R X phi hm _
  (derivation_infinite_upper_points psi phi (@centered_closed_ball_relation R X)) _ hnull).
move=> x hx; have hd := (@infinite_centered_density_derivate R X phi psi x hphi).1 hx.
exact: hd.2.1.
Qed.

(** Source for [centered_density_exceptional_union_null]: direct
    nullity of W union P used in Federer 2.9.15,
    p. 160. Both exceptional sets retain their exact
    printed definitions and the original standing context. *)
Lemma centered_density_exceptional_union_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V0 : X -> set X -> Prop) :
  is_measure_derivation_context phi V0 -> is_derivation_measure psi ->
  is_centered_density_geometry phi ->
  phi (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi)=0.
Proof.
move=> hc hpsi hgeo.
exact: (@measure_null_union R X phi (derivation_measure_law (derivation_context_measure hc)) _ _
  (@measure_infinite_centered_density_points_null R X phi psi V0 hc hpsi hgeo)
  (@measure_null_ball_points_null R X phi V0 hc)).
Qed.
