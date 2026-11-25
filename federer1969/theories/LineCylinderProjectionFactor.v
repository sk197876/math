(** Supporting Federer (1969), 2.10.46, p. 204: remove the coordinate
    choices from the projection-wise formula of Freilich (1950), Theorem
    4.5, Part 5, p. 247. The common-factor theorem of 1.7.4, p. 31, supplies
    a transverse projection, and the opaque adapted chart supplies its
    normal coordinates. The resulting scalar factor is intrinsically the
    norm of the projected cylinder axis. The transverse projection is an
    existential proof witness; no chosen implementation is used downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinear RealMetricBackground
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProductProjectionFactor
  OrthogonalProjectionChart OrthogonalProjectionChartUP LineCylinderProjectionCoordinates
  ProjectionMultiplicityIntegral LineCylinderProjectionIntegral TopologicalBorel LebesgueScalarMeasure
  MeasureAlmostUP MeasureAlmostBasic OrthogonalProjectionProbability ProjectionKernelProbability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [line_cylinder_projection_transverse_factor]: supporting
    intrinsic version of Freilich (1950), Theorem 4.5,
    Part 5, p. 247, for 2.10.46, p. 204.
    The transverse projection depends only on F. For all Borel
    cylinder factors with finite scalar length and finite transverse
    multiplicity integral, the projection integral is their product
    times the norm of F applied to the first unit vector. *)
Theorem line_cylinder_projection_transverse_factor (R : realType) n k
    (F : orthogonal_projection_metric_space R (1+n) (1+k)) :
  euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0))!=0 ->
  exists Q : orthogonal_projection_metric_space R n k,
    forall (T : set (real_line_metric R))
      (V : set (inner_metric_space (@euclidean_inner_productP R n))) (ell r : R),
    borel_set T -> borel_set V -> lebesgue_scalar_measure T=ell%:E ->
    projection_multiplicity_integral V Q=r%:E ->
    projection_multiplicity_integral
      ((fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @` (T `*` V)) F=
      (inner_norm (@euclidean_inner_productP R (1+k))
        (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0)))*ell*r)%:E.
Proof.
move=> haxis.
have [p [q [hp [hq hfactor]]]] := @euclidean_product_projection_factor R 1 n k
  (euclidean_projection_linear F) (euclidean_projection_linear_member F).
have [Q hQ] := euclidean_projection_linear_complete hq.
pose C := @orthogonal_projection_chart R 1 k p hp.
have hc : is_orthogonal_projection_chart p C.1 C.2 := orthogonal_projection_chart_specification hp.
have hfac u y : p (euclidean_projection_linear F (@euclidean_block_join R 1 n (u,y)))=
    euclidean_projection_linear Q y by rewrite hQ; exact: hfactor.
have he : @coordinate_basis R (1+n) (lshift n ord0)=
    @euclidean_block_join R 1 n (euclidean_one_embed 1,0).
  apply: euclidean_block_vectors_ext.
  - move=> i; rewrite (ord1 i) euclidean_block_join_left /coordinate_basis /euclidean_one_embed !ffunE eqxx; by [].
  - move=> i; by rewrite euclidean_block_join_right /coordinate_basis !ffunE eq_rlshift.
have hz : p (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0)))=0.
  by rewrite he hfactor linear0.
have hnorm := projection_chart_line_kernel_norm hc hz.
have ha : C.1 (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0))) (lshift k ord0)!=0.
  rewrite -normr_eq0 hnorm inner_norm_eq0; exact haxis.
exists Q=> T V ell r hT hV hell hr.
rewrite -hnorm.
exact: (@line_cylinder_projection_integral_value R n k F Q p C.1 C.2 T V ell r
  hc hfac ha hT hV hell hr).
Qed.


(** Source for [line_cylinder_almost_transverse_factor]: supporting
    almost-every-projection cylinder formula for 2.10.46, p. 204;
    Freilich (1950), Lemma 4.4 and Theorem 4.5,
    Parts 1–5, pp. 240–247. The exceptional axis-zero
    set is proved null. Each remaining projection has a single
    transverse factor valid for every Borel cylinder satisfying
    the finite-integral premises; no measurable selection is asserted. *)
Theorem line_cylinder_almost_transverse_factor (R : realType) n k
    (hkn : (1+k<=1+n)%N) :
  measure_almost_everywhere (@orthogonal_projection_probability R (1+n) (1+k) hkn)
    [set F | exists Q : orthogonal_projection_metric_space R n k,
      forall (T : set (real_line_metric R))
        (V : set (inner_metric_space (@euclidean_inner_productP R n))) (ell r : R),
      borel_set T -> borel_set V -> lebesgue_scalar_measure T=ell%:E ->
      projection_multiplicity_integral V Q=r%:E ->
      projection_multiplicity_integral
        ((fun z=>@euclidean_block_join R 1 n (euclidean_one_embed z.1,z.2)) @` (T `*` V)) F=
        (inner_norm (@euclidean_inner_productP R (1+k))
          (euclidean_projection_linear F (@coordinate_basis R (1+n) (lshift n ord0)))*ell*r)%:E].
Proof.
pose e := @coordinate_basis R (1+n) (lshift n ord0).
have he : e!=0.
  apply/eqP=> hh; have hcoord := congr1 (fun z : R_n R (1+n)=>z (lshift n ord0)) hh.
  have hbad : (1 : R)==0 by apply/eqP; move: hcoord; by rewrite /e /coordinate_basis !ffunE eqxx.
  by rewrite oner_eq0 in hbad.
have hz := @nonzero_vector_projection_kernel_probability_null R n k hkn e he.
have hae : measure_almost_everywhere (@orthogonal_projection_probability R (1+n) (1+k) hkn)
    (~` [set F | euclidean_projection_linear F e=0]).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_almost_everywhere_mono R (orthogonal_projection_metric_space R (1+n) (1+k))
  (@orthogonal_projection_probability R (1+n) (1+k) hkn) (@theta_star_is_measure R (1+n) (1+k) hkn)
  _ _ _ hae)=> F hF.
apply: line_cylinder_projection_transverse_factor; exact/eqP.
Qed.
