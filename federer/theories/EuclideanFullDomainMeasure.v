(** Federer (1969), 4.1.7, pp. 357–358:
    Lebesgue measure on the original full
    current domain is the already defined
    open-subspace measure. The canonical inclusion
    and its inverse preserve the original
    topology, integrals and positive finite balls.
    No new measure normalization is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentDomainGeometry MetricSubsetBackground
  IsotropyGroupTopology SubtypeCompactHausdorff MetricClosedBalls ProperMapUP RadonProperPushforward
  EuclideanDistributionMeasureContext EuclideanLebesgueDimensions EuclideanLebesgueCompactInner
  EuclideanNormClosedBalls EuclideanClosedBallGrowth OpenSubspaceMeasure MeasureUP MeasurePushforward
  RadonMeasureUP MeasureIntegralUP SummableRealFunctionUP RadonWeightedPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanFullDomainMeasure.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation IT := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation FT := (current_domain R n (fun _=>True)).
Local Notation FM := (metric_subset ((fun _:X=>True):set NT)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).

(** Source for [euclidean_full_domain_point]: the
    same original Euclidean point viewed in
    the full current domain, supporting Federer
    4.1.7, pp. 357–358. *)
Definition euclidean_full_domain_point:X->FT:=fun x=>exist _ x (mem_set Logic.I).

(** Source for [euclidean_full_domain_measure]: the
    original Lebesgue measure over the full
    current domain, supporting Federer 4.1.7,
    pp. 357–358, through the existing open-subspace
    measure of 2.7.16, pp. 136–137. *)
Definition euclidean_full_domain_measure:set FT->\bar R:=
  @open_subspace_measure R X (fun _=>True) Leb.

(** Source for [euclidean_full_domain_measure_image]:
    the canonical copy of Lebesgue measure
    equals the original open-subspace measure,
    supporting Federer 4.1.7, pp. 357–358. *)
Lemma euclidean_full_domain_measure_image:
  euclidean_full_domain_measure=measure_pushforward euclidean_full_domain_point Leb.
Proof.
apply:funext=>A;rewrite /euclidean_full_domain_measure /open_subspace_measure /measure_pushforward.
congr Leb;apply/seteqP;split.
- move=>x [y hy hyx].
  have hSame:euclidean_full_domain_point x=y by apply:val_inj;exact:esym hyx.
  exact (eq_ind y A hy _ (esym hSame)).
- move=>x hx;exists (euclidean_full_domain_point x);by [].
Qed.

(** Source for [euclidean_full_domain_measure_laws]:
    the original full-domain Lebesgue measure
    is a Radon measure, supporting Federer
    4.1.7, pp. 357–358. The proof
    transports the existing Radon measure along
    the actual inverse inclusion maps. *)
Theorem euclidean_full_domain_measure_laws:
  is_measure euclidean_full_domain_measure /\is_radon_measure euclidean_full_domain_measure.
Proof.
rewrite euclidean_full_domain_measure_image.
have hForward:continuous (fun x:IT=>euclidean_full_domain_point x).
  apply:(@set_type_continuous_into NT (fun _=>True) IT euclidean_full_domain_point).
  exact:(@euclidean_distribution_inner_to_norm R n).
have hInverse:continuous (fun x:FT=>(set_val x:IT)).
  move=>x;exact:(continuous_comp (@set_type_val_continuous NT (fun _=>True) x)
    (@euclidean_distribution_norm_to_inner R n (set_val x))).
have hProper:@is_proper_map IT FT euclidean_full_domain_point.
  move=>K hK.
  have hCompact:compact ((fun x:FT=>(set_val x:IT)) @` K).
    apply:continuous_compact hK;exact:continuous_subspaceT hInverse.
  have hEqual:((fun x:FT=>(set_val x:IT)) @` K)=euclidean_full_domain_point @^-1` K.
    apply/seteqP;split.
    - move=>x [y hy hyx].
      have hSame:euclidean_full_domain_point x=y by apply:val_inj;exact:esym hyx.
      exact (eq_ind y K hy _ (esym hSame)).
    - move=>x hx;exists (euclidean_full_domain_point x);by [].
  by rewrite -hEqual.
have hHausdorff:hausdorff_space FT.
  exact:(@set_type_hausdorff NT (fun _=>True) (@metric_hausdorff R NT)).
split;first exact:measure_pushforward_is_measure (euclidean_lebesgue_is_measure R n).
exact:(@proper_continuous_radon_pushforward R IT FT Leb (euclidean_lebesgue_is_measure R n)
  (euclidean_lebesgue_radon R n) euclidean_full_domain_point hHausdorff
  (@current_domain_locally_compact R n (fun _=>True) hFull) hForward hProper).
Qed.

(** Source for [euclidean_full_domain_measure_ambient]:
    inclusion of the actual full-domain measure
    gives precisely original Lebesgue measure on
    R^n, supporting Federer 4.1.7, p. 358. *)
Theorem euclidean_full_domain_measure_ambient:
  measure_pushforward (set_val:FT->X) euclidean_full_domain_measure=Leb.
Proof.
rewrite euclidean_full_domain_measure_image.
apply:funext=>A;rewrite /measure_pushforward.
congr Leb;apply/seteqP;split=>x hx;exact:hx.
Qed.

(** Source for [euclidean_full_domain_real_integral]:
    the original Euclidean scalar integral agrees
    with its full-domain copy, supporting the
    current E^n in Federer 4.1.7,
    pp. 357–358. Only the existing image
    integral law of 2.4.18 is used. *)
Theorem euclidean_full_domain_real_integral (g:X->R) a:
  is_measure_integral Leb (real_total_integrand g) a->
  is_measure_integral euclidean_full_domain_measure
    (real_total_integrand (fun x:FT=>g (set_val x))) a.
Proof.
move=>hI;rewrite euclidean_full_domain_measure_image.
exact:((@real_total_pushforward_integral_iff R X FT Leb (euclidean_lebesgue_is_measure R n)
  euclidean_full_domain_point (fun x:FT=>g (set_val x)) hI.1 a).1 hI).
Qed.

(** Source for [euclidean_full_domain_ball_mass]:
    every original positive-radius ball has its
    exact Lebesgue mass in the full current
    domain, supporting the everywhere orientation of
    E^n in Federer 4.1.7, p. 358.
    Dimension zero is retained. *)
Theorem euclidean_full_domain_ball_mass (x:FM) r:0<r->
  euclidean_full_domain_measure (metric_closed_ball x r)=((@euclidean_closed_unit_volume R n)*r^+n)%:E.
Proof.
move=>hr;rewrite euclidean_full_domain_measure_image /measure_pushforward.
have hBall:euclidean_full_domain_point @^-1` (metric_closed_ball x r)=metric_closed_ball (set_val x:NT) r.
  apply/seteqP;split.
  { move=>z hz;exact:hz. }
  { move=>z hz;exact:hz. }
rewrite hBall;exact:(@euclidean_norm_closed_ball_measure R n (set_val x) r hr).
Qed.

(** Source for [euclidean_full_domain_ball_positive_finite]:
    each original ball has a positive finite
    denominator in the orienting formula for E^n,
    Federer 4.1.7, p. 358. No point
    or positive radius is excluded. *)
Theorem euclidean_full_domain_ball_positive_finite (x:FM) r:0<r->exists b:R,
  euclidean_full_domain_measure (metric_closed_ball x r)=b%:E /\0<b.
Proof.
move=>hr;exists ((@euclidean_closed_unit_volume R n)*r^+n);split.
- exact:(@euclidean_full_domain_ball_mass x r hr).
- exact:(mulr_gt0 (@euclidean_closed_unit_volume_laws R n).2 (exprn_gt0 n hr)).
Qed.
End EuclideanFullDomainMeasure.
