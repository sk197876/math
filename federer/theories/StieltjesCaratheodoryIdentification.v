(** Federer (1969), 2.10.7, pp. 174–175: the interval construction with cost
    g(b)-g(a) is the positive measure induced by the nondecreasing function
    g. Its open-interval value equals that increment at continuity
    endpoints. At the identity integrator it is Lebesgue measure and hence
    Hausdorff length on R. The two constructions are independent; Borel
    regularity and the continuity-endpoint characterisation prove their
    equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP StieltjesCaratheodory
  StieltjesCaratheodoryConsequences StieltjesInducedOpenIntervals StieltjesIntervalUniqueness
  StieltjesImageMeasures StieltjesInducedPairLaws StieltjesMonotone StieltjesLebesgueInduced
  RealHausdorffLebesgue HausdorffMeasure LebesgueScalarMeasure MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [stieltjes_caratheodory_induced_measure]:
    direct identification of the independent
    interval construction with the positive
    induced measure in Federer 2.10.7, p. 174.
    Equality is of set functions on all targets,
    not just on Borel sets or intervals. *)
Theorem stieltjes_caratheodory_induced_measure (R : realType) (g : R -> R)
    (mu nu : set R -> \bar R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> is_induced_measure_pair g mu nu ->
  stieltjes_caratheodory_measure g=mu.
Proof.
move=> hg hp.
have hfin := @monotone_locally_finite_variation R g hg.
have [hm [_ [_ [_ [hr [_ [_ [_ [_ [_ [hpoint _]]]]]]]]]]] :=
  @induced_measure_pair_laws R g hfin mu nu hp.
have hc := stieltjes_caratheodory_is_measure hg.
have hcr := stieltjes_caratheodory_borel_regular hg.
have hcostC a b : (a<b)%R -> stieltjes_caratheodory_measure g `]a,b[<=(g b-g a)%:E.
  exact: stieltjes_caratheodory_interval_bound hg.
have hcostM a b : (a<b)%R -> mu `]a,b[<=(g b-g a)%:E.
  exact: monotone_induced_open_interval_bound hg hp.
have hpointM x : g @ x --> g x -> mu [set x]=0.
  move=> hx; exact: (hpoint x hx).1.
have hpointC x : g @ x --> g x -> stieltjes_caratheodory_measure g [set x]=0.
  exact: stieltjes_caratheodory_continuity_point_null hg.
have heqI a b : (a<b)%R -> g @ a --> g a -> g @ b --> g b ->
    stieltjes_caratheodory_measure g `]a,b[=mu `]a,b[.
  move=> hab hca hcb.
  have hlower := @induced_stieltjes_below_caratheodory R g mu nu hg hp `]a,b[.
  apply/eqP; rewrite eq_le hlower andbT.
  rewrite (@monotone_induced_open_interval_increment R g mu nu a b hg hp hab hca hcb).
  exact: hcostC a b hab.
apply: funext=> A.
exact: (@stieltjes_continuity_interval_measure_unique R g (stieltjes_caratheodory_measure g) mu
  hc hm hg hcr hr hcostC hcostM hpointC hpointM heqI A).
Qed.

(** Source for [stieltjes_caratheodory_induced_pair]:
    direct actual induced-measure conclusion of
    Federer 2.10.7, p. 174. Existence of
    an induced pair is already proved from
    nondecreasing g; the negative part is zero.
    No induced pair remains an existence premise. *)
Corollary stieltjes_caratheodory_induced_pair (R : realType) (g : R -> R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) ->
  is_induced_measure_pair g (stieltjes_caratheodory_measure g) (fun _ => 0).
Proof.
move=> hg; have hfin := @monotone_locally_finite_variation R g hg.
have [mu [nu hp]] := induced_measure_pair_exists hfin.
have hzero := (@induced_measure_pair_monotone R g hfin hg mu nu hp).1.
by rewrite (@stieltjes_caratheodory_induced_measure R g mu nu hg hp) -hzero.
Qed.

(** Source for [stieltjes_caratheodory_open_interval]:
    direct printed open-interval identity in
    Federer 2.10.7, p. 174. Both endpoint
    continuity hypotheses are retained; the
    raw generator cost need not equal interval
    measure at discontinuity endpoints. *)
Theorem stieltjes_caratheodory_open_interval (R : realType) (g : R -> R) (a b : R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> (a<b)%R ->
  g @ a --> g a -> g @ b --> g b ->
  stieltjes_caratheodory_measure g `]a,b[=(g b-g a)%:E.
Proof.
move=> hg hab hca hcb.
exact: (@monotone_induced_open_interval_increment R g (stieltjes_caratheodory_measure g)
  (fun _ => 0) a b hg (stieltjes_caratheodory_induced_pair hg) hab hca hcb).
Qed.

(** Source for [identity_caratheodory_lebesgue]: direct
    identity-integrator special case of Federer
    2.10.7, p. 175, identified with the
    existing sealed Lebesgue line measure. *)
Theorem identity_caratheodory_lebesgue (R : realType) :
  stieltjes_caratheodory_measure (fun x : R => x)=@lebesgue_scalar_measure R.
Proof.
exact: (@stieltjes_caratheodory_induced_measure R (fun x => x) (@lebesgue_scalar_measure R)
  (fun _ => 0) (@identity_nondecreasing R) (@lebesgue_identity_induced R)).
Qed.

(** Source for [identity_caratheodory_hausdorff_length]:
    direct final link in Federer 2.10.7,
    p. 175: the identity-integrator interval
    construction equals one-dimensional Hausdorff
    measure on R. The equality with Lebesgue
    measure was proved independently above. *)
Corollary identity_caratheodory_hausdorff_length (R : realType) (A : set (real_line_metric R)) :
  stieltjes_caratheodory_measure (fun x : R => x) A=
    @hausdorff_measure R [the metricType R of real_line_metric R] 1 A.
Proof. by rewrite identity_caratheodory_lebesgue real_hausdorff_measure_one_lebesgue. Qed.
