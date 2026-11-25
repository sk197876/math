(** Private existence witnesses for the two Jacobian graphs,
    Federer (1969), 3.2.1, p. 241. Postcompose the existing
    opaque differential graphs with the abstract exterior norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  PartialFunctionUP PartialFunctionPostcomposition NormDifferential ApproximateDifferential
  EuclideanLinearJacobian JacobianUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_jacobian_graph_exists]: supporting existence
    of the partial J_k f in Federer 3.2.1, p. 241. Ordinary
    postcomposition preserves exactly the differential's actual domain. *)
Theorem euclidean_jacobian_graph_exists (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) :
  exists J:partial_function (R_n R m) R,is_euclidean_jacobian_graph k A f J.
Proof.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
exists (partial_function_postcompose (norm_differential hNX hNY A f) (euclidean_linear_jacobian k)).
move=>a j; split=>[[L [hL he]]|[L [hL he]]]; exists L; split=>//.
- exact ((norm_differential_graph hNX hNY A f a L).1 hL).
- exact ((norm_differential_graph hNX hNY A f a L).2 hL).
Qed.

(** Source for [approximate_jacobian_graph_exists]: supporting existence
    of ap J_k f in Federer 3.2.1, p. 241. The actual approximate
    differential graph is already single valued; no choice of an
    approximate differential at an undefined point is made. *)
Theorem approximate_jacobian_graph_exists (R:realType) m n k
    (A:R_n R m->Prop) (f:R_n R m->R_n R n) :
  exists J:partial_function (R_n R m) R,is_approximate_jacobian_graph k A f J.
Proof.
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
exists (partial_function_postcompose (approximate_differential hNY A f) (euclidean_linear_jacobian k)).
move=>a j; split=>[[L [hL he]]|[L [hL he]]]; exists L; split=>//.
- exact ((approximate_differential_graph hNY A f a L).1 hL).
- exact ((approximate_differential_graph hNY A f a L).2 hL).
Qed.
