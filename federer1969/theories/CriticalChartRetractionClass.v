(** Federer (1969), 3.4.2(6), p. 312: the original projection
    retraction r=(p|S)^(-1) composed with p has class k. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormDifferentialUP
  NormClassOneUP NormRegularity NormRegularityOperations NormOpenDomainLaws
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalRelativeComposition
  RelativeClassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_projection_bounded_linear]: supporting the
    projection in r of 3.4.2(6), p. 312. The original orthogonal
    projection has bound one by the contraction law of 1.7.7, p. 34. *)
Lemma critical_projection_bounded_linear (R:realType) m mu
    (p:euclidean_projection_space R m mu):
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R mu))
    (hom_of_linear (euclidean_projection_linear p)).
Proof.
exists 1;split;first exact:ler01.
move=>x;rewrite hom_of_linearE mul1r.
have h:=euclidean_projection_nonexpanding p
  (x:inner_metric_space (@euclidean_inner_productP R m)) 0.
by rewrite !inner_metric_distanceE linear0 !subr0 in h.
Qed.

(** Source for [critical_chart_retraction_class]: r has class k on
    U=p^(-1)(p(S)), the first sentence of the proof of 3.4.2(6),
    p. 312. The original inverse chart and projection supply the
    composition; no retraction or extension is an extra hypothesis. *)
Theorem critical_chart_retraction_class (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g:
  is_critical_manifold_chart k Z S p g ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) k.
Proof.
move=>hChart.
pose X:=R_n R m;pose V:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NV:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose P:=hom_of_linear (euclidean_projection_linear p).
pose U:=fun x=>(euclidean_projection_linear p @` S) (P x).
have hBound:norm_bounded_linear NX NV P:=critical_projection_bounded_linear p.
have hFull a (ha:setT a):norm_domain_interior NX setT a:=norm_full_domain_interior NX a.
have hP0:=@norm_class_linear R X V NX NV hNX hNV setT P 0 hFull hBound.
have hG:=critical_chart_inverse_class hChart.
have hU a (ha:U a):norm_domain_interior NX U a.
  exact:(@norm_class_zero_preimage_interior R X V X NX NV NX
    (euclidean_projection_linear p @` S) P g
    (norm_class_continuous hP0) (norm_class_continuous hG) a ha).
have hPU:=@norm_class_linear R X V NX NV hNX hNV U P k hU hBound.
have hMap x (hx:U x):(euclidean_projection_linear p @` S) (P x):=hx.
exact:(norm_class_compose_on hMap hPU hG).
Qed.

(** Source for [critical_chart_relative_composition_class]: the map
    f composed with r has class k on the same original U, supporting
    the derivative functions in 3.4.2(7), p. 313. Relative class on S
    suffices; the target remains an arbitrary normed space. *)
Theorem critical_chart_relative_composition_class (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) Z S
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y):
  is_critical_manifold_chart k Z S p g ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>f (g (euclidean_projection_linear p x))) k.
Proof.
move=>hChart hf.
apply:(critical_relative_class_composition (critical_chart_retraction_class hChart) _ hf).
move=>x hx;exact:(critical_chart_right_inverse hChart hx).1.
Qed.
