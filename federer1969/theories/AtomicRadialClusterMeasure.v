(** Federer (1969), 3.3.18, p. 301: actual finite
    countably supported measures for the false-converse assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric GeometricErrorBudget GeometricDoubleBudget
  PointMassMeasure PointMassRegularity MeasureUP MeasureBasic MeasureSum MeasureBinaryAddition
  MeasureScaleIntegral NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [atomic_radial_cluster_measure_exists]: actual
    supporting measure for the countable-support examples mentioned
    in Federer 3.3.18, p. 301. Put a positive atom at zero and
    summably weighted atoms on fast radial clusters of every
    original sequence direction. Existing point masses, measure
    sums and numerical-sum laws prove existence, finite total mass,
    all-set measurability and the actual atomic lower bounds.
    All construction choices stay inside this opaque existence
    proof; no density or counterexample conclusion is supplied. *)
Theorem atomic_radial_cluster_measure_exists (R:realType) n
    (v:nat->inner_metric_space (@euclidean_inner_productP R n)):
  exists (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))),
    is_measure mu /\(forall A,measure_measurable mu A) /\mu setT< +oo /\
    countable E /\E 0%R /\mu (~` E)= 0 /\1<=mu [set 0%R] /\
    (forall j k,(j<=k)%N ->(geometric_error_budget (1:R) j*geometric_error_budget (1:R) k)%R%:E<=
      mu [set (geometric_error_budget (1:R) k)^+2 *:v j]) /\
    E=([set 0%R] `|` ((fun p:nat*nat=>(geometric_error_budget (1:R) p.2)^+2 *:v p.1) @`
      [set p:nat*nat|(p.1<=p.2)%N])).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose b:=geometric_error_budget (1:R).
pose w (p:nat*nat):=(b p.1*b p.2)%R.
pose z (p:nat*nat):X:=(b p.2)^+2 *:v p.1.
pose D:set (nat*nat):=[set p|(p.1<=p.2)%N].
pose component (p:nat*nat):=measure_scale (w p) (point_mass R (z p)).
have hb i:(0<b i)%R:=geometric_error_budget_positive i (@ltr01 R).
have hw p:(0<w p)%R:=mulr_gt0 (hb p.1) (hb p.2).
have hComponent p:is_measure (component p).
  exact:(@measure_scale_is_measure R [the choiceType of X] (point_mass R (z p)) (w p)
    (point_mass_is_measure R (z p)) (hw p)).
have [rho hSum]:=@measure_sum_exists R [the choiceType of X]
  [the choiceType of ((nat*nat)%type:Type)] D component.
have hRho:is_measure rho:=measure_sum_is_measure (fun p _=>hComponent p) hSum.
have hRhoMeas A:measure_measurable rho A.
  apply:(@measure_sum_measurable R [the choiceType of X]
    [the choiceType of ((nat*nat)%type:Type)] D component rho A
    (fun p _=>hComponent p) hSum)=>p _.
  exact:(@measure_scale_measurable R [the choiceType of X] (point_mass R (z p))
    (point_mass_is_measure R (z p)) (w p) A (point_mass_every_set_measurable R (z p) A)).
have hRhoTotal:rho setT<= 1.
  rewrite hSum.
  have hTerms:(fun p=>component p setT)=(fun p=>(w p)%:E).
    apply:funext=>p; rewrite /component /measure_scale (point_mass_in R Logic.I) mule1.
    by [].
  rewrite hTerms.
  apply:le_trans (@nonnegative_sum_subset R _ D setT (fun p=>(w p)%:E) (subsetT D)) _.
  exact:geometric_double_budget_bound.
pose zero:X:=0%R.
pose mu (A:set X):=point_mass R zero A+rho A.
have hMu:is_measure mu:=measure_binary_addition_is_measure (point_mass_is_measure R zero) hRho.
pose E:set X:=[set 0%R] `|` (z @` D).
have hCountable:countable E.
  pose cover (p:option (nat*nat)):X:=if p is Some jk then z jk else zero.
  have hSub:E `<=` cover @` setT.
    move=>x [hx|[jk hjk <-]].
    - exists None; first exact:Logic.I.
      exact:esym hx.
    - by exists (Some jk).
  apply:sub_countable (subset_card_le hSub) _.
  exact:sub_countable (card_image_le _ _) (countableP setT).
have hZero:E zero by left.
have hRhoOutside:rho (~` E)= 0.
  rewrite hSum; apply:nonnegative_sum_zero=>p hp.
  rewrite /component /measure_scale point_mass_out ?mule0 //.
  move=>hNot; apply:hNot; right; by exists p.
have hPointOutside:point_mass R zero (~` E)= 0.
  apply:point_mass_out=>hn; exact:hn hZero.
have hOutside:mu (~` E)= 0 by rewrite /mu hPointOutside hRhoOutside add0e.
have hMuTotal:mu setT< +oo.
  have hBound:mu setT<= 2.
    rewrite /mu (point_mass_in R Logic.I).
    have h:=leeD (lexx (1 : \bar R)) hRhoTotal.
    by rewrite -EFinD in h.
  exact:le_lt_trans hBound (ltry _).
have hBase:1<=mu [set zero].
  rewrite /mu (@point_mass_in R [the choiceType of X] zero [set zero] (erefl zero)).
  have h:=leeD (lexx (1 : \bar R)) (measure_nonnegative hRho [set zero]).
  by rewrite adde0 in h.
have hAtomic j k:(j<=k)%N ->(w (j,k))%:E<=mu [set z (j,k)].
  move=>hjk.
  have hTerm:=@measure_sum_component_bound R [the choiceType of X]
    [the choiceType of ((nat*nat)%type:Type)] D component rho (j,k) [set z (j,k)] hSum hjk.
  rewrite /component /measure_scale (@point_mass_in R [the choiceType of X] (z (j,k)) [set z (j,k)] (erefl (z (j,k)))) mule1 in hTerm.
  apply:le_trans hTerm _.
  have h:=leeD (measure_nonnegative (point_mass_is_measure R zero) [set z (j,k)])
    (lexx (rho [set z (j,k)])).
  by rewrite add0e in h.
exists mu,E; split; first exact:hMu.
split; first by move=>A; exact:measure_binary_addition_measurable
  (point_mass_every_set_measurable R zero A) (hRhoMeas A).
split; first exact:hMuTotal.
split; first exact:hCountable.
split; first exact:hZero.
split; first exact:hOutside.
split; first exact:hBase.
split; first exact:hAtomic.
by [].
Qed.
