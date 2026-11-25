(** Federer (1969), 3.1.1, p. 210: class zero means
    continuity on the actual open domain. Supporting the
    closed agreement sets used in 3.2.31, pp. 268–269. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormClassOneUP NormClassZeroTopology FiniteNormEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_class_zero_continuous]: a supporting
    whole-domain instance of the class-zero convention in Federer
    3.1.1, p. 210. Transfer the existing norm-topology theorem
    to the identical Euclidean inner-product neighborhoods.
    All natural source and target dimensions are retained. *)
Lemma euclidean_class_zero_continuous (R:realType) m n (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  continuous (fun x:inner_metric_space (@euclidean_inner_productP R m)=>
    (f x:inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=>hf a W hW.
have hWn:=(@inner_real_norm_same_nbhs R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (f a) W).1 hW.
have hPre:=@norm_class_zero_continuous_at R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f a hf Logic.I W hWn.
exact ((@inner_real_norm_same_nbhs R (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) a (f @^-1` W)).2 hPre).
Qed.
