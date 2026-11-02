(** Federer (1969), 2.10.36, printed p. 198: for a convex S in R^m and
    endpoints a_i,b_i in S, the norm of the exterior product of their
    differences is at most m! times L^m(S). Follow the printed induction and
    Steiner double-cone argument. First reduce arbitrary S to a compact
    convex hull of its finitely many endpoints so the already proved compact
    Steiner volume theorem applies. The principal statement has positive
    degree, as printed; an auxiliary degree-zero version explicitly requires
    S nonempty. The working Federer erratum has no correction on p. 198. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm InnerNormalization InnerMetric InnerConvex InnerCompactConvexHull
  OrthonormalFamilies OrthogonalMaps TensorUP EuclideanNormalChartUP EuclideanNormalChart
  NormalHeadChartGeometry SteinerChordVolumeBound EuclideanHeadExteriorBound
  ExteriorGrading FiniteExteriorPowers ExteriorNorm ExteriorMaps ExteriorMapScaling
  ExteriorOperatorEstimate ExteriorNormNaturality ExteriorProductFactors MeasureUP MeasureBasic PointMassMeasure
  EuclideanLebesgueDimensions EuclideanCoordinateTopology ScalarConvexLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_endpoint_volume_bound]: supporting
    compact-convex form of 2.10.36, p. 198.
    The induction uses the first chord as normal
    direction, projects the other chords, and applies
    the double-cone lower volume bound. A nonempty
    source is required in degree zero. *)
Theorem compact_convex_endpoint_volume_bound (R : realType) :
  forall (n : nat) (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : 'I_n -> inner_metric_space (@euclidean_inner_productP R n)),
  compact S -> is_inner_convex S -> S !=set0 ->
  (forall i, S (a i)) -> (forall i, S (b i)) ->
  ((exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda (fun i => a i-b i) (ord_tuple n)))%:E <=
    (n`!)%:R%:E*euclidean_lebesgue_measure n S)%E.
Proof.
elim=> [S a b hS hconv [x hx] ha hb|n IH S a b hS hconv hne ha hb].
- have h0 : S 0 by move: hx; rewrite (coordinate_zero x).
  have hnorm : exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R 0)
      (e_lambda (fun i => a i-b i) (ord_tuple 0))= 1.
    apply: orthonormal_product_unit_norm=> i j.
    have hi := ltn_ord i; by rewrite ltn0 in hi.
  by rewrite hnorm /euclidean_lebesgue_measure (point_mass_in R h0) mul1e.
pose hB := @euclidean_inner_productP R n.+1.
pose v := a ord0-b ord0.
case: (eqVneq v 0)=> [hv|hv0].
- have hz : e_lambda (fun i => a i-b i) (ord_tuple n.+1)=0.
    apply: (@exterior_product_zero_entry R [the choiceType of 'I_n.+1] (R_n R n.+1)
      (fun i => a i-b i) n.+1 (ord_tuple n.+1) ord0); first exact: mem_enum.
    exact hv.
  rewrite hz exterior_norm_zero.
  have hfac : (0<=(n.+1`!)%:R%:E :> \bar R)%E by rewrite lee_fin; exact: ler0n.
  exact (mule_ge0 hfac (measure_nonnegative (euclidean_lebesgue_is_measure R n.+1) S)).
- pose h := inner_norm hB v.
  have hh : 0<h by rewrite /h inner_norm_gt0.
  pose u := inner_normalize hB v.
  have hu : euclidean_inner_product u u= 1 := inner_normalize_square hB hv0.
  pose D := euclidean_normal_chart ord0 hu.
  have hD := euclidean_normal_chart_specification ord0 hu.
  pose f := normal_chart_forward_map D.
  pose g := normal_chart_backward_map D.
  have hgu : g u=@coordinate_basis R n.+1 ord0.
    by rewrite -(normal_chart_axis_law hD) (normal_chart_forward_inverse_law hD).
  have hchord : g v=@coordinate_head_inclusion R n h.
    rewrite -(inner_normalizeK hB hv0) linearZ hgu coordinate_head_inclusion_axis; reflexivity.
  pose p := linear_comp (GRing.Linear.clone _ _ _ _ (@coordinate_tail R n) _) g.
  pose K : set (inner_metric_space (@euclidean_inner_productP R n)) := p @` S.
  have hKc : compact K.
    apply: (continuous_compact _ hS); apply: continuous_subspaceT.
    move=> x; apply: (@continuous_comp (Topological.clone (inner_metric_space hB) _)
      (Topological.clone (inner_metric_space hB) _)
      (Topological.clone (inner_metric_space (@euclidean_inner_productP R n)) _)
      g (@coordinate_tail R n) x).
    - exact: euclidean_linear_continuous.
    - exact: coordinate_tail_continuous.
  have hKv : is_inner_convex K := linear_image_inner_convex hconv.
  have hKne : K !=set0.
    have [x hx] := hne; exists (p x); by exists x.
  pose a' (i : 'I_n) := p (a (lift ord0 i)).
  pose b' (i : 'I_n) := p (b (lift ord0 i)).
  have ha' i : K (a' i) by exists (a (lift ord0 i)); first exact: ha.
  have hb' i : K (b' i) by exists (b (lift ord0 i)); first exact: hb.
  have hIH := IH K a' b' hKc hKv hKne ha' hb'.
  have hg : is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) g.
    move=> x y.
    by rewrite -(normal_chart_orthogonal_law hD (g x) (g y))
      !(normal_chart_backward_inverse_law hD).
  have hprod := @euclidean_head_exterior_product_bound R n
    (fun i => g (a i-b i)) h hchord.
  rewrite -exterior_map_indexed_product
    (@exterior_norm_orthogonal_natural R (euclidean_two_nonzero R)
      (R_n R n.+1) (R_n R n.+1) _ _ hB hB g hg) (ger0_norm (ltW hh)) in hprod.
  have hproj : (fun i : 'I_n => coordinate_tail (g (a (lift ord0 i)-b (lift ord0 i))))=
      (fun i => a' i-b' i).
    apply: funext=> i; by rewrite /a' /b' /p /= !linearB.
  rewrite hproj in hprod.
  have hvol := @steiner_chord_projection_volume_bound R n u D S (a ord0) (b ord0)
    h hD hS hconv (ha ord0) (hb ord0) hh hchord.
  have hhE : (0<=h%:E)%E by rewrite lee_fin; exact: ltW hh.
  have hleft := lee_wpmul2l hhE hIH.
  have hfac : (0<=(n.+1`!)%:R%:E :> \bar R)%E by rewrite lee_fin; exact: ler0n.
  have hright := lee_wpmul2l hfac hvol.
  have hn : n.+1%:R != (0 : R) by rewrite pnatr_eq0.
  have he : (n.+1`!)%:R*(h/n.+1%:R)=h*(n`!)%:R.
    by rewrite factS natrM mulrAC mulrCA mulfV // mulr1.
  rewrite !muleA -EFinM he in hright.
  rewrite !muleA -EFinM in hleft.
  apply: le_trans _ (le_trans hleft hright).
  by rewrite lee_fin.
Qed.

(** Source for [convex_endpoint_volume_bound]: direct
    inequality in 2.10.36, p. 198, with
    a nonempty-source hypothesis only to include the
    auxiliary degree-zero case. No closedness, boundedness,
    measurability or finite-volume hypothesis is imposed. *)
Theorem convex_endpoint_volume_bound (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : 'I_n -> inner_metric_space (@euclidean_inner_productP R n)) :
  is_inner_convex S -> S !=set0 -> (forall i, S (a i)) -> (forall i, S (b i)) ->
  ((exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda (fun i => a i-b i) (ord_tuple n)))%:E <=
    (n`!)%:R%:E*euclidean_lebesgue_measure n S)%E.
Proof.
move=> hS hne ha hb.
have [K [hKc [hKv [hKS [hKa [hKb hKne]]]]]] :=
  @compact_convex_finite_endpoint_subset R (R_n R n) _ (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) [the finType of 'I_n] S a b (@coordinate_basisP R n) hS hne ha hb.
apply: le_trans (@compact_convex_endpoint_volume_bound R n K a b hKc hKv hKne hKa hKb) _.
apply: lee_wpmul2l; first by rewrite lee_fin; exact: ler0n.
exact (@measure_mono R (inner_metric_space (@euclidean_inner_productP R n))
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) K S hKS).
Qed.

(** Source for [federer_2_10_36]: direct positive-dimensional
    theorem in 2.10.36, printed p. 198:
    in words, the norm of the product of m
    endpoint differences in a convex subset of R^m
    is at most m! times its Lebesgue outer
    measure. A positive dimension makes the source
    nonempty automatically from the supplied endpoints. *)
Theorem federer_2_10_36 (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : 'I_n -> inner_metric_space (@euclidean_inner_productP R n)) :
  (0<n)%N -> is_inner_convex S -> (forall i, S (a i)) -> (forall i, S (b i)) ->
  ((exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda (fun i => a i-b i) (ord_tuple n)))%:E <=
    (n`!)%:R%:E*euclidean_lebesgue_measure n S)%E.
Proof.
move=> hn hS ha hb.
have hne : S !=set0 by exists (a (Ordinal hn)); exact: ha.
exact (@convex_endpoint_volume_bound R n S a b hS hne ha hb).
Qed.
