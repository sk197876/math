(** Federer (1969), 4.1.24, p. 380: pull an
    original Lipschitz source map back by a linear
    coordinate projection. Its inverse-image source is
    open and the composite has a global Lipschitz
    bound there. Reuse finite linear bounds and the
    original relative composition theorem. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP LipschitzBasic
  MetricLipschitzComposition MetricLocalLipschitzContinuity EuclideanAffineSourceLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_linear_source_pullback]: the open
    projected source and its globally Lipschitz composite,
    used to combine the original defining image witnesses
    in 4.1.24, p. 380. Empty sources require
    no chosen point. *)
Theorem euclidean_linear_source_pullback (R:realType) d e n
    (Z:set (R_n R e))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R e)) Z x)
    (P:Hom (R_n R d) (R_n R e)) (f:R_n R e->R_n R n):
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R e)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f->
  (forall x,Z (P x)->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R d)) (fun y=>Z (P y)) x) /\
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (fun x=>Z (P x)) (fun x=>f (P x)).
Proof.
move=>hF.
pose X:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)).
pose Y:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R e)).
pose V:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
have hPLip:=@euclidean_linear_source_lipschitz R d e P.
have hPContinuous:continuous (P:X->Y).
  apply:metric_local_lipschitz_continuous_whole.
  exact:metric_lipschitz_is_local hPLip.
have hZOpen:@open Y Z.
  rewrite openE=>y hy;exact:(@norm_domain_interior_neighbourhood R (R_n R e)
    (inner_norm (@euclidean_inner_productP R e))
    (inner_norm_real_norm (@euclidean_inner_productP R e)) Z y).1 (hZ y hy).
have hOpen:@open X (fun x=>Z (P x)).
  exact:(@open_comp X Y P Z (fun x _=>hPContinuous x) hZOpen).
split.
- move=>x hx;apply:(@norm_domain_interior_neighbourhood R (R_n R d)
    (inner_norm (@euclidean_inner_productP R d))
    (inner_norm_real_norm (@euclidean_inner_productP R d)) (fun y=>Z (P y)) x).2.
  exact:open_nbhs_nbhs (conj hOpen hx).
- have[L [hL hPBound]]:=hPLip;have[M [hM hFBound]]:=hF.
  exists (M*L);split;first exact:mulr_gt0 hM hL.
  apply:(@metric_lipschitz_composition_bound R X Y V (fun x=>Z (P x)) Z
    P f L M (fun x hx=>hx) _ hFBound).
  exact:(@metric_lipschitz_bound_restrict R X Y setT (fun x=>Z (P x)) P L
    (fun _ _=>Logic.I) hPBound).
Qed.
