(** Federer (1969), 3.4.2(7), p. 313: the common critical set
    is already one admissible flat piece in the class-one case. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric RealNormUP
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalFlatPiecesUP
  CriticalCommonZeroClosed CriticalTangentZeroOscillation CriticalOscillationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_class_one_common_flat_piece]: the choice
    U_j=S and H_j=B in the class-one subcase of 3.4.2(7), p. 313.
    The same pair controls every function in Φ(S,C,1). Compactness
    of B and its derivative oscillation are proved before applying
    (6); no flatness conclusion is supplied as a hypothesis. *)
Theorem critical_class_one_common_flat_piece (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)) (p:euclidean_projection_space R m mu) g:
  critical_manifold_family Z mu 1 S ->
  is_critical_manifold_chart 1 (grassmann_val Z) S p g ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  is_critical_flat_piece hNY Z mu S C 1 S
    (critical_common_tangent_zero_set hNY (grassmann_val Z) S C 1).
Proof.
move=>hFamily hChart hCS hC.
pose B:=critical_common_tangent_zero_set hNY (grassmann_val Z) S C 1.
have hB:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) B.
  exact:(@critical_common_zero_chart_compact R m mu 1 Y NY hNY (grassmann_val Z)
    S C p g (leqnn 1) hChart hCS hC).
split;first by exists mu;split;first exact:leqnn.
split;first by move=>x.
split;first exact:hB.
split.
- move=>x hx;split;[exact:(hCS x hx.1)|exact:hx.1].
- move=>f hf.
  have hBZero:B `<=` critical_tangent_zero_locus hNY (grassmann_val Z) S f.
    move=>x hx;exact:(hx.2 f hf).
  have hBS:B `<=` S by move=>x hx;exact:hCS x hx.1.
  have hZeta:=@critical_tangent_zero_zeta_limit R m mu Y NY hNY (grassmann_val Z)
    S B p g f hChart hBZero hB hf.1.
  have hLimit:=@critical_chart_oscillation_zero_limit R m mu Y NY hNY
    (grassmann_val Z) S B p g f 1 hChart hBS hB hf.1 (lexx 1).
  rewrite subrr in hLimit.
  exact:(hLimit hZeta).
Qed.
