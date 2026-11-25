(** Federer (1969), 2.10.5(2), p. 173, continuity paragraph, paraphrased:
    f_S is continuous on O*(n,m) for bounded open convex S. The book cites
    3.2.36, p. 272, which proves a stronger joint compact-convex volume
    continuity using Steiner's formula. Here prove the needed assertion
    directly: closing S preserves every projected volume and gives a compact
    source; compact upper continuity combines with the open-incidence lower
    bound. This proof route does not assume the forward theorem or claim all
    of 3.2.36. The actual Lebesgue regularity and projection arguments
    remain internal to this development. Source context:
    ProjectedVolumeLowerContinuity.v and ProjectedVolumePointwiseClosure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities
  InnerMetric InnerConvex EuclideanBoundedClosure MetricDiameterUP MetricDiameter
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability ProjectedVolumeBounds
  ProjectedVolumePointwiseClosure CompactProjectedVolumeUpperContinuity ProjectedVolumeLowerContinuity
  RealMetricBackground ExtendedRealOrderTopology MeasurableRealEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_norm_bounded_closure_compact]:
    supporting compactification of the bounded
    source in Federer 2.10.5(2), p. 173,
    from finite-dimensional bounded compactness,
    1.7.1, p. 28. An explicit norm bound
    gives diameter at most twice that bound;
    the empty source is handled separately. *)
Lemma euclidean_norm_bounded_closure_compact (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) -> compact (closure S).
Proof.
move=> hb; case: (pselect (S !=set0))=> [[a ha]|hno].
- have hc : (0<=c)%R := le_trans (inner_norm_nonnegative (@euclidean_inner_productP R n) a) (hb a ha).
  have hd : extended_metric_diameter S<=(c+c)%R%:E.
    apply: (metric_diameter_least (extended_metric_diameter_specification S)).
    - by rewrite lee_fin addr_ge0.
    - move=> x y hx hy; rewrite lee_fin inner_metric_distanceE.
      have h := @inner_norm_triangle R (R_n R n) (@euclidean_inner_product R n)
        (@euclidean_inner_productP R n) x (-y)%R.
      rewrite inner_normN in h; exact: le_trans h (lerD (hb x hx) (hb y hy)).
  exact: (@euclidean_bounded_set_closure_compact R n S (c+c)%R (ex_intro _ a ha) hd).
- have he : S=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hno; by exists x.
  rewrite he closure0; exact: compact0.
Qed.

(** Source for [open_convex_projected_volume_upper_neighbourhood]:
    supporting upper continuity for Federer
    2.10.5(2), p. 173. Use compactness of
    Closure S and unchanged individual projected
    volumes; no general dense-set closure identity
    is asserted. *)
Lemma open_convex_projected_volume_upper_neighbourhood (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (p : euclidean_projection_space R n m) (b : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  open S -> @is_inner_convex R (R_n R n) S -> projected_volume_function S p<b%:E ->
  exists V : set (euclidean_projection_space R n m), open V /\ V p /\
    forall q, V q -> projected_volume_function S q<b%:E.
Proof.
move=> hb hS hc hp.
have hK := @euclidean_norm_bounded_closure_compact R n S c hb.
have hpK : projected_volume_function (closure S) p<b%:E.
  by rewrite (@projected_volume_function_open_convex_closure R n m S p hS hc).
have [V [hV [hVp hbound]]] := @compact_projected_volume_upper_neighbourhood R n m
  (closure S) p b hK hpK.
have hVo : @open (euclidean_projection_space R n m) V.
  exact: (orthogonal_projection_metric_openE V).1 hV.
exists V; split=> //; split=> // q hq.
have hh := hbound q hq.
by rewrite (@projected_volume_function_open_convex_closure R n m S q hS hc) in hh.
Qed.

(** Source for [open_convex_projected_volume_scalar_continuous]:
    supporting finite-scalar form of the continuity
    assertion in Federer 2.10.5(2), p. 173.
    Boundedness is used to prove finiteness before
    taking the scalar part of each projected volume. *)
Theorem open_convex_projected_volume_scalar_continuous (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  open S -> @is_inner_convex R (R_n R n) S ->
  continuous (fun p : euclidean_projection_space R n m =>
    (fine (projected_volume_function S p) : real_line_metric R)).
Proof.
move=> hb hS hc.
pose P := euclidean_projection_space R n m.
pose f (p : P) : real_line_metric R := fine (projected_volume_function S p).
have hfin p := @projected_volume_function_finite R n m S c hb p.
move=> p A hA.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (f p) A) hA.
have hlo : (f p-e)%R%:E<projected_volume_function S p.
  rewrite -(fineK (hfin p)) lte_fin; change (is_true (f p-e<f p)%R).
  have he0 : (0<e)%R := he; lra.
have hhi : projected_volume_function S p<(f p+e)%R%:E.
  rewrite -(fineK (hfin p)) lte_fin; change (is_true (f p<f p+e)%R).
  have he0 : (0<e)%R := he; lra.
have [V [hV [hpV hVl]]] := @projected_volume_lower_neighbourhood R n m S p (f p-e)%R hS hlo.
have [W [hW [hpW hWh]]] := @open_convex_projected_volume_upper_neighbourhood R n m S c p (f p+e)%R hb hS hc hhi.
have hnV : nbhs p V by rewrite openE in hV; exact: hV p hpV.
have hnW : nbhs p W by rewrite openE in hW; exact: hW p hpW.
apply: (@filterS _ (nbhs p) _ (V `&` W) _ _ (@filterI _ (nbhs p) _ V W hnV hnW))=> q [hqV hqW].
have hl : (f p-e<f q)%R.
  have h := hVl q hqV; by rewrite -(fineK (hfin q)) lte_fin in h.
have hu : (f q<f p+e)%R.
  have h := hWh q hqW; by rewrite -(fineK (hfin q)) lte_fin in h.
apply: hball; change (is_true (mdist (f p) (f q)<e)%R).
rewrite real_line_metric_distanceE ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [open_convex_projected_volume_continuous]:
    direct continuity assertion for bounded open
    convex S in Federer 2.10.5(2), p. 173.
    The target retains its extended-real order
    topology; the already proved finite scalar
    continuity is embedded without changing values. *)
Theorem open_convex_projected_volume_continuous (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  open S -> @is_inner_convex R (R_n R n) S ->
  continuous (projected_volume_function (m:=m) S : euclidean_projection_space R n m -> extended_real_line R).
Proof.
move=> hb hS hc.
have hf := @open_convex_projected_volume_scalar_continuous R n m S c hb hS hc.
have he : (fun p : euclidean_projection_space R n m => (fine (projected_volume_function S p))%:E)=
    projected_volume_function (m:=m) S.
  apply: funext=> p; exact: fineK (@projected_volume_function_finite R n m S c hb p).
rewrite -he; move=> p.
exact: continuous_comp (hf p) (@real_extended_embedding_continuous R (fine (projected_volume_function S p))).
Qed.
