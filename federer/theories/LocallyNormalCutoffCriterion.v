(** Federer (1969), 4.1.7, p. 358: T is
    locally normal exactly when every compact
    scalar localization is normal. The converse
    uses the existing finite-gauge criterion and
    the original scalar boundary product identity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentContraction
  CurrentDegreeTransport CurrentIntegrationCriterion CurrentLocalRepresentation CurrentRepresentableLinear
  CurrentRepresentableDegreeTransport CurrentRepresentableSmoothProducts CurrentScalarBoundaryContraction
  SmoothCurrentExteriorDerivative SmoothTestSpaces NormalCurrentsUP LocallyNormalScalarContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section LocallyNormalCutoffCriterion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation DT0 := (@current_test_space R h2 n U hU 0%N).
Local Notation inc := (smooth_test_inclusion (hE 0)).
Local Notation CP := (fun k p=>@current_contraction R h2 n k p U hU).
Local Notation bd := (fun m=>@current_boundary R h2 n m U hU).
Local Notation d := (@smooth_current_exterior_derivative R h2 n 0%N U hU).
Local Notation represented := (fun m=>@is_integration_representable_current R h2 n m U hU).
Local Notation LN := (fun m=>@is_locally_normal_current R h2 n U hU m).
Local Notation N := (fun m=>@is_normal_current R h2 n U hU m).

(** Source for [locally_normal_compact_cutoff_criterion]:
    the first original local-normality equivalence,
    Federer 4.1.7, p. 358. Both
    implications use actual compact scalar tests,
    and degree zero retains its boundary exception. *)
Theorem locally_normal_compact_cutoff_criterion m (T:C m):
  LN m T <->forall gamma:DT0,N m (CP 0 m (inc gamma) T).
Proof.
split;first by move=>hT gamma;exact:locally_normal_compact_scalar_contraction hT.
move=>hCutoffs.
have hT:represented m T.
  apply:(@current_compact_scalar_representation R h2 n m U hU T)=>gamma.
  exact:(hCutoffs gamma).1.1.
split=>//.
case:m T hT hCutoffs=>[|p] T hT hCutoffs;first by [].
apply:(@current_compact_scalar_representation R h2 n p U hU (bd p T))=>gamma.
pose a:=inc gamma.
pose B:=CP 1 p (d a)
  (@current_degree_transport R h2 n U hU (0+p).+1 (1+p) (esym (addSn 0 p)) T).
have hB:represented p B.
  apply:(@current_contraction_represented R h2 n 1 p U hU (d a)).
  exact:(@represented_current_degree_transport R h2 n U hU (0+p).+1 (1+p)
    (esym (addSn 0 p)) T hT).
have hBoundary:represented p (bd p (CP 0 p.+1 a T)):=(hCutoffs gamma).1.2.
have hSum:=@represented_current_linear R h2 n p U hU 1
  (bd p (CP 0 p.+1 a T)) B hBoundary hB.
rewrite scale1r current_scalar_boundary_contraction in hSum.
change (represented p ((CP 0 p a (bd p T)-B)+B)) in hSum.
by rewrite subrK in hSum.
Qed.
End LocallyNormalCutoffCriterion.
