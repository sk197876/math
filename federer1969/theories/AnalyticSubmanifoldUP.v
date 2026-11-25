(** Federer (1969), 3.1.24, p. 240: analytic submanifolds
    are defined by the analytic replacement of 3.1.19(1), p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormAnalyticUP EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_submanifold_straightening]: condition
    (1) of 3.1.19 with analytic coordinate changes, as asserted
    in 3.1.24, p. 240. The existing class-one laws retain
    exact image and inverse identities; analyticity is required
    for both actual maps, not inferred from smoothness. *)
Definition is_analytic_submanifold_straightening (R:realType) n mu (B:set (R_n R n)) b
    (T C:set (R_n R n)) (s t:R_n R n->R_n R n) (Z:G (R_n R n) mu) :=
  @is_submanifold_straightening R n mu 1%N B b T C s t Z /\
  @norm_analytic R (R_n R n) (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n)) T s /\
  @norm_analytic R (R_n R n) (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n)) C t.

(** Source for [is_euclidean_analytic_submanifold]: analytic local
    straightening at every point, Federer 3.1.24, p. 240,
    referring to 3.1.19(1), p. 231. No chart existence or
    extra project axiom is postulated. Empty sets are allowed. *)
Definition is_euclidean_analytic_submanifold (R:realType) n mu (B:set (R_n R n)) :=
  forall b,B b -> exists T C s t Z,
    @is_analytic_submanifold_straightening R n mu B b T C s t Z.

(** Source for [analytic_submanifold_class_one]: the analytic
    straightening is in particular a class-one straightening,
    supporting 3.1.24, p. 240. *)
Lemma analytic_submanifold_class_one (R:realType) n mu (B:set (R_n R n)) :
  @is_euclidean_analytic_submanifold R n mu B -> @is_euclidean_submanifold R n mu 1%N B.
Proof.
move=>h b hb; have [T [C [s [t [Z [hZ _]]]]]]:=h b hb.
by exists T,C,s,t,Z.
Qed.
