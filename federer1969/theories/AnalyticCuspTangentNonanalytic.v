(** Federer (1969), 3.4.11, p. 338:
    the actual tangent of the original analytic cusp
    is not analytic. Its exact positive half-axis
    and the already proved analytic half-line obstruction
    give a nonanalytic germ at the origin. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  TangentConeUP SetGermUP AnalyticVarietyGermUP AnalyticCuspUP AnalyticCuspSealed
  AnalyticCuspTangent AnalyticHalfLineObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cusp_tangent_germ_not_analytic]:
    the original counterexample following the finite
    homogeneous polynomial assertion of 3.4.11, p. 338.
    The actual tangent has no finite local analytic
    equations at zero, although the source cusp does. *)
Theorem analytic_cusp_tangent_germ_not_analytic (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  ~@is_analytic_variety_germ R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0
      (norm_tangent_cone NX (@AnalyticCusp.set R) 0)).
Proof.
move=>X NX hNX.
pose e:=@coordinate_basis R 2 ord0.
have hLinear:linear (fun t:R^o=>t*:e).
  by move=>c x y;rewrite scalerDl scalerA.
pose L:Hom R^o X:=@HomMap R R^o X (fun t=>t*:e) (introT (asboolP _) hLinear).
have hValues t:L t=t*:e by [].
have hBound:norm_bounded_linear (fun t:R^o=>`|t|) NX L.
  exists (NX e);split;first exact:real_seminorm_nonnegative hNX.1 e.
  move=>t;change (is_true (NX (t*:e)<=NX e*`|t|)).
  have hNorm:NX (t*:e)=`|t|*NX e:=real_seminorm_scale hNX.1 t e.
  by rewrite hNorm mulrC.
apply:(@analytic_half_line_obstruction R X NX hNX
  (norm_tangent_cone NX (@AnalyticCusp.set R) 0) L hBound).
- move=>t ht;apply/(analytic_cusp_tangent_equation (L t)).
  rewrite hValues /e /coordinate_basis !ffunE /=.
  change (is_true (0<=t*1) /\t*0=0).
  by rewrite mulr1 mulr0;split;first exact:ltW ht.
- move=>t ht /analytic_cusp_tangent_equation [hFirst _].
  rewrite hValues /e /coordinate_basis !ffunE /= in hFirst.
  change (is_true (0<=t*1)) in hFirst;rewrite mulr1 in hFirst.
  have hFalse:=le_lt_trans hFirst ht;by rewrite ltxx in hFalse.
Qed.
