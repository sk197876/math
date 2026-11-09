(** Federer (1969), 3.4.2(6), p. 312: comparison of the two
    oscillations at scaled positive cutoffs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormClassOneUP EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalCompactTube CriticalRetractedIncrement
  CriticalOscillation CriticalOscillationScalarBound RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_eta_zeta_comparison]: the last
    estimate in the proof of 3.4.2(6), p. 312. One compact tube
    gives η(delta)<=M^lambda ζ(M delta) for every sufficiently
    small positive delta. Extended supremum values are retained. *)
Theorem critical_chart_eta_zeta_comparison (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C T:set (R_n R m))
    (p:euclidean_projection_space R m mu) (g:R_n R mu->R_n R m)
    (f:R_n R m->Y) e M lambda delta:
  is_critical_manifold_chart k Z S p g ->
  is_critical_source_tube C e T ->C `<=` S ->
  T `<=` (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x)) ->
  1<=M ->
  (forall a b,T a ->T b ->
    inner_norm (@euclidean_inner_productP R m)
      (g (euclidean_projection_linear p a)-g (euclidean_projection_linear p b))<=
    M*inner_norm (@euclidean_inner_productP R m) (a-b)) ->
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) ->
  norm_class_one (inner_norm (@euclidean_inner_productP R m)) NY
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>f (g (euclidean_projection_linear p x))) ->
  1<=lambda ->0<delta<e ->
  (critical_eta NY Z S C f lambda delta<=
    (real_power M lambda)%:E*critical_zeta hNY Z S C f (lambda-1) (M*delta))%E.
Proof.
move=>hChart hTube hCS hTU hM hLip hR hF hLambda hDelta.
have hPositive:0<real_power M lambda.
  exact:(real_power_strictly_positive lambda (lt_le_trans ltr01 hM)).
have hNonnegative:=critical_zeta_nonnegative hNY Z S C f (lambda-1) (M*delta).
case hValue:(critical_zeta hNY Z S C f (lambda-1) (M*delta))=>[b| |].
- have hb:0<=b by move:hNonnegative;rewrite hValue lee_fin.
  rewrite -EFinM.
  apply:(critical_eta_finite_upper_bound (mulr_ge0 (ltW hPositive) hb)).
  move=>x c hx hc hZ hDist.
  exact:(@critical_retracted_increment_bound R m mu k Y NY hNY Z S C T p g hChart
    f e M lambda delta b x c hTube hCS hTU hM hLip hR hF hLambda hb hValue
    hx hc hZ hDist (andP hDelta).2).
- by rewrite gt0_muley ?lte_fin // leey.
- by move:hNonnegative;rewrite hValue.
Qed.
