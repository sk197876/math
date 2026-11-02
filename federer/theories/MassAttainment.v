(** Federer (1969), 1.8.4, pp. 40-41: choosing a covector which attains the
    mass. Supporting compactness of the comass unit ball follows from the
    norm comparison of 1.8.1, p. 38, and bounded compactness of 1.7.1, p.
    28. Attainment in the closed unit ball includes zero exterior dimension;
    unit-norm attainment will require a nonzero mass. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  OrthonormalFamilies InnerBoundedness InnerFiniteCompactness InnerCoordinateContinuity
  InnerExterior InnerExteriorPositivity InnerExteriorIsomorphism
  ExteriorCovectorInner ExteriorGrading ExteriorIndices FiniteExteriorPowers
  AlternatingCoordinates AlternatingPairing SimpleUnitBall
  ComassUP ComassComparison MassUP CompactMaximum LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Attainment.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).
Local Notation hE := (@exterior_inner_productP R h2 V B hB m).
Local Notation E := (inner_metric_space hE).
Local Notation gamma := (@inner_exterior_form R h2 V B hB m).

(** Source for [polar_comass_unit_ball]: Federer 1.8.4,
    p. 41, supporting model of the comass unit ball under the
    polarity isomorphism of 1.7.5. Its elements are multivectors
    whose corresponding covectors have comass at most one. *)
Definition polar_comass_unit_ball : set E := fun z => kappa (gamma z) <= 1.

(** Source for [polar_comass_ball_halfspaces]: Federer 1.8.4,
    p. 41, supporting closed-half-space description of the dual
    unit ball, directly from the supremum definition in 1.8.1. *)
Lemma polar_comass_ball_halfspaces : polar_comass_unit_ball =
  \bigcap_(x in @simple_unit_ball R h2 V B hB m)
    ((fun z : E => inner_coordinate hE x z) @^-1` [set r : R^o | r <= 1]).
Proof.
apply/seteqP; split=> z hz.
- move=> x hx; change (is_true (inner_coordinate hE x z <= 1)).
  rewrite inner_coordinateE (inner_symmetric hE).
  exact: le_trans (comass_upper_law (hk (gamma z)) hx) hz.
- apply: (@comass_least_upper_bound R h2 V B hB m (gamma z)
    (kappa (gamma z)) (hk (gamma z)) 1) => x hx.
  have hh := hz x hx.
  change (is_true (inner_coordinate hE x z <= 1)) in hh.
  rewrite inner_coordinateE (inner_symmetric hE) in hh.
  exact hh.
Qed.

(** Source for [polar_comass_unit_ball_closed]: Federer 1.8.4,
    p. 41, supporting closedness of the set on which the
    mass-defining evaluation is maximised. *)
Lemma polar_comass_unit_ball_closed : closed polar_comass_unit_ball.
Proof.
rewrite polar_comass_ball_halfspaces; apply: closed_bigI => x hx.
apply: preimage_closed; last exact: closed_le.
move=> z _; exact: inner_coordinate_continuous.
Qed.

(** Source for [polar_comass_unit_ball_bounded]: Federer 1.8.4,
    p. 41, supporting boundedness from |phi|<=sqrt(C(n,m))||phi||,
    valid even when the exterior dimension is zero. *)
Lemma polar_comass_unit_ball_bounded : @inner_bounded R (exterior_power V m)
  (@exterior_inner_form R h2 V B hB m) hE polar_comass_unit_ball.
Proof.
exists (Num.sqrt (('C(n,m))%:R : R)) => z hz.
have hb := @euclidean_le_comass R h2 V B hB n e he m hm
  (gamma z) (kappa (gamma z)) (hk (gamma z)).
rewrite inner_exterior_form_norm in hb.
apply: (le_trans hb); apply: ler_piMr; first exact: sqrtr_ge0.
exact hz.
Qed.

(** Source for [polar_comass_unit_ball_compact]: Federer 1.8.4,
    p. 41, supporting compactness of the dual unit ball,
    obtained from a finite basis and closed boundedness. *)
Theorem polar_comass_unit_ball_compact : compact polar_comass_unit_ball.
Proof.
pose I := Finite.clone (Lambda n m) _.
pose b := fun i : I => e_lambda e (val i).
have hb : is_basis b := finite_e_lambda_basis he h2 m.
have hb' := @basis_reindex R (Choice.clone I _) (Choice.clone 'I_(#|I|) _)
  (exterior_power V m) b hb enum_rank enum_val (@enum_rankK I) (@enum_valK I).
exact: (@inner_finite_basis_boundedly_compact R (exterior_power V m)
  (@exterior_inner_form R h2 V B hB m) hE #|I| _ hb'
  polar_comass_unit_ball polar_comass_unit_ball_closed polar_comass_unit_ball_bounded).
Qed.

(** Source for [mass_attained]: Federer 1.8.4, p. 41,
    the mass can be attained by a covector of comass at most one.
    This form of the assertion includes the zero-dimensional
    exterior space, where a unit covector does not exist. *)
Theorem mass_attained (x : exterior_power V m) d (hd : is_mass kappa x d) :
  exists phi, kappa phi <= 1 /\ pairing x phi = d.
Proof.
have hn : polar_comass_unit_ball !=set0.
  exists 0; apply: (@comass_least_upper_bound R h2 V B hB m (gamma 0)
    (kappa (gamma 0)) (hk (gamma 0)) 1) => y hy.
  by rewrite linear0 (bil0r (@pairing_bilinear R V R^o m)); exact: ler01.
have [z [hz hmax]] := @continuous_compact_maximum R (Topological.clone E _)
  polar_comass_unit_ball (fun z => inner_coordinate hE x z)
  hn polar_comass_unit_ball_compact (@inner_coordinate_continuous R (exterior_power V m)
    (@exterior_inner_form R h2 V B hB m) hE x).
exists (gamma z); split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@mass_upper_law R V m kappa x d hd (gamma z) hz).
- apply: (@mass_least_upper_bound R V m kappa x d hd (pairing x (gamma z))) => phi hp.
  have [g [hfg hgf]] := @inner_exterior_inverse_exists R h2 V B hB n e he m.
  have hgp : polar_comass_unit_ball (g phi) by rewrite /polar_comass_unit_ball hgf.
  have hh := hmax (g phi) hgp.
  rewrite !inner_coordinateE (inner_symmetric hE (g phi) x) (inner_symmetric hE z x) /exterior_inner_form hgf in hh.
  exact hh.
Qed.
End Attainment.
