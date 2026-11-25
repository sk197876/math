(** Federer (1969), 4.1.7, pp. 355–356: actual
    currents are determined by their original test
    evaluations. This supporting equality rule uses
    the opaque continuous-dual image laws of 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothTestTopology
  ContinuousRealDual LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentEvaluation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation O := (@current_test_opens R h2 n U hU m).
Local Notation hO := (smooth_test_final_topology_laws hE hD).1.

(** Source for [current_values_extensional]: equality
    on every original test implies equality of
    currents, supporting the identities in Federer
    4.1.7, p. 356. *)
Theorem current_values_extensional (T S:@current_space R h2 n U hU m):
  (forall phi,@current_value R h2 n U hU m T phi=
    @current_value R h2 n U hU m S phi)->T=S.
Proof.
move=>he.
apply:(subspace_representation_injective (@continuous_real_dual_model_laws R DT O hO)).
apply:hom_ext=>phi; exact:he.
Qed.
End CurrentEvaluation.
