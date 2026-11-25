(** Federer (1969), 3.3.8, p. 295: positive normalization and
    original-source monotonicity in the conical mass bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureConeDensityUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_cost_subset]: the original E subset B
    estimate in Federer 3.3.8, p. 295. Positive inverse-radius and
    inverse-aperture factors preserve the original outer-measure order. *)
Lemma structure_cone_cost_subset (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) x (r s:R):
  is_measure phi ->E `<=` B ->0<r ->0<s ->
  (structure_cone_cost hmn phi E (x,p) r s<=
    structure_cone_cost hmn phi B (x,p) r s)%E.
Proof.
move=>hPhi hEB hr hs; rewrite /structure_cone_cost.
apply:lee_wpmul2r; first by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
apply:lee_wpmul2r; first by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
apply:(@measure_mono R _ phi hPhi)=>y [hy hCone]; by split; first exact:hEB y hy.
Qed.

(** Source for [structure_cone_cost_mass_bound]: the equivalence of
    normalized and unnormalized estimates used for C_j in Federer
    3.3.8, p. 295. All denominators are strictly positive finite
    reals; infinite original outer values are retained. *)
Lemma structure_cone_cost_mass_bound (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) x (r s b:R):
  0<r ->0<s ->
  ((structure_cone_cost hmn phi E (x,p) r s<=b%:E)%E <->
   (phi (E `&` structure_cone (structure_projection_kernel hmn p) x r%:E s)
      <=(b*r^+m*s^+m)%:E)%E).
Proof.
move=>hr hs.
have hrm:0<r^+m:=exprn_gt0 m hr.
have hsm:0<s^+m:=exprn_gt0 m hs.
have hDen:0<r^+m*s^+m by rewrite mulr_gt0.
rewrite /structure_cone_cost !exprVn -muleA -EFinM -invfM.
rewrite (lee_pdivrMr _ _ hDen).
by rewrite -EFinM mulrA.
Qed.
