(** Federer (1969), 4.1.26, p. 383: existence
    of the original partial determinant sign on A.
    The earlier opaque differential, ordinary graph
    postcomposition and sealed zero extension realize
    the independent specification; no new derivative
    construction is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialSealed
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  PartialFunctionUP PartialFunctionPostcomposition PartialZeroExtension LipschitzDegreeSummandUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [lipschitz_degree_summand_exists]: the original
    source summand in 4.1.26, p. 383,
    exists for every map and source set.
    Almost-everywhere differentiability and the later
    fibre-sum domain are separate analytic assertions. *)
Theorem lipschitz_degree_summand_exists (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m)):
  exists u:partial_function (R_n R m) R,is_lipschitz_degree_summand f A u.
Proof.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose D:=@NormDifferential.value R X X N N hN hN (fun _=>True) f.
pose hD:=@NormDifferential.laws R X X N N hN hN (fun _=>True) f.
pose v:=partial_function_postcompose D
  (fun L:Hom X X=>Num.sg (@euclidean_det R m (hom_as_linear L))).
exists (partial_function_zero_extension 0 A v)=>x a.
rewrite partial_function_zero_extension_graph;split.
- move=>[[hx [L [hL hValue]]]|[hx hValue]].
  + right;split;first exact:hx.
    exists L;split;[exact:(hD x L).1 hL|exact:hValue].
  + left;by split.
- move=>[[hx hValue]|[hx [L [hL hValue]]]].
  + right;by split.
  + left;split;first exact:hx.
    exists L;split;[exact:(hD x L).2 hL|exact:hValue].
Qed.
