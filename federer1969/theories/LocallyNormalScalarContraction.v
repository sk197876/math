(** Federer (1969), 4.1.7, p. 358: local
    normality is preserved by smooth scalar
    multiplication, and a compact test multiplier
    gives a normal current. Reuse the
    original boundary identity, finite-gauge criterion
    and compact support law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentContraction CurrentDegreeTransport
  CurrentIntegrationCriterion CurrentRepresentableLinear CurrentRepresentableDegreeTransport
  CurrentRepresentableSmoothProducts CurrentScalarBoundaryContraction CurrentContractionCompactSupport
  SmoothTestSpaces NormalCurrentsUP SmoothCurrentExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section LocallyNormalScalarContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation P := (fun k p=>@current_contraction R h2 n k p U hU).
Local Notation bd := (fun m=>@current_boundary R h2 n m U hU).
Local Notation d := (@smooth_current_exterior_derivative R h2 n 0 U hU).

(** Source for [locally_normal_scalar_contraction]: smooth
    scalar multiplication preserves the original local
    normality, supporting Federer 4.1.7, p. 358.
    The zero-degree boundary exception is retained. *)
Theorem locally_normal_scalar_contraction m (gamma:E 0) (T:C m):
  @is_locally_normal_current R h2 n U hU m T->
    @is_locally_normal_current R h2 n U hU m (P 0 m gamma T).
Proof.
case:m T=>[|q] T [hT hBT].
- split;last by [].
  exact:(@current_contraction_represented R h2 n 0 0 U hU gamma T hT).
- split;first exact:(@current_contraction_represented R h2 n 0 q.+1 U hU gamma T hT).
  change (@is_integration_representable_current R h2 n q U hU (bd q (P 0 q.+1 gamma T))).
  rewrite current_scalar_boundary_contraction.
  apply:(@represented_current_difference R h2 n q U hU).
  + exact:(@current_contraction_represented R h2 n 0 q U hU gamma (bd q T) hBT).
  + apply:(@current_contraction_represented R h2 n 1 q U hU (d gamma)).
    exact:(@represented_current_degree_transport R h2 n U hU (0+q).+1 (1+q)
      (esym (addSn 0 q)) T hT).
Qed.

(** Source for [locally_normal_compact_scalar_contraction]:
    if T is locally normal then T
    contracted gamma is normal for every
    gamma in D^0(U), Federer 4.1.7,
    p. 358, first local normality equivalence,
    forward implication. *)
Theorem locally_normal_compact_scalar_contraction m
    (gamma:@current_test_space R h2 n U hU 0) (T:C m):
  @is_locally_normal_current R h2 n U hU m T->
    @is_normal_current R h2 n U hU m (P 0 m (smooth_test_inclusion (hE 0) gamma) T).
Proof.
move=>hT;split.
- exact:(@locally_normal_scalar_contraction m (smooth_test_inclusion (hE 0) gamma) T hT).
- exact:(@current_contraction_by_test_compact R h2 n 0 m U hU gamma T).
Qed.
End LocallyNormalScalarContraction.
