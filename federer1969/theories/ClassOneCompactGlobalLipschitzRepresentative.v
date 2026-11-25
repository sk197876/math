(** Federer (1969), 4.1.27, p. 384:
    the polynomial cube parametrisation is used only
    over a compact cube. To apply the preceding
    global Lipschitz density formula, replace a
    class-one map near the compact carrier by
    the earlier compact plateau representative.
    The original map and its differential agree
    on the resulting open neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP InnerNorm InnerMetric
  GrassmannAbbreviations EuclideanInnerProduct HilbertFormCompactness
  SmoothCompactSet CurrentMapDifferential CurrentClassOneCompactPlateau
  NormLocalLipschitzScalarProduct EuclideanLocalLipschitzCompactSupport
  LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [class_one_compact_global_lipschitz_representative]:
    the compactly supported replacement needed for
    the application of 4.1.25 to the
    cube map in 4.1.27, p. 384.
    Reuse the established plateau from 4.1.14,
    p. 372, and its compact-support global
    Lipschitz estimate. No global Lipschitz assertion
    about the original polynomial is introduced. *)
Theorem class_one_compact_global_lipschitz_representative
    (R:realType) n nu (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (f:R_n R n->R_n R nu):
  norm_class_one (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu)) U f->
  exists F:R_n R n->R_n R nu,exists W:set (R_n R n),
    @open (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) W /\
    smooth_compact_carrier K `<=` W /\W `<=` U /\
    @is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R n))
      (inner_metric_space (@euclidean_inner_productP R nu)) setT F /\
    norm_class_one (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R nu)) setT F /\
    (forall x,W x->F x=f x) /\
    forall x,W x->@current_map_differential R n nu setT F x=
      @current_map_differential R n nu U f x.
Proof.
move=>hClass.
have[F [W [C [hW [hKW [hWU [hValues
    [hC [hCU [hOff [hF hDifferentials]]]]]]]]]]]:=
  @current_class_one_compact_plateau_exists R n nu U hU K f hClass.
have hLocal:=@norm_class_one_locally_metric_lipschitz R
  (R_n R n) (R_n R nu)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) setT F hF.
have[L [hL hBound]]:=@euclidean_local_lipschitz_compact_support_global R n
  (R_n R nu) (inner_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) F C hC hOff hLocal.
have hLip:@is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R nu)) setT F.
  exists L;split;first exact:hL.
  split;first exact:ltW hL.
  move=>x y _ _.
  change (is_true (inner_norm (@euclidean_inner_productP R nu) (F x-F y)<=
    L*inner_norm (@euclidean_inner_productP R n) (x-y))).
  exact:hBound x y.
exists F,W;split;first exact:hW.
split;first exact:hKW.
split;first exact:hWU.
split;first exact:hLip.
split;first exact:hF.
split;[exact:hValues|exact:hDifferentials].
Qed.
