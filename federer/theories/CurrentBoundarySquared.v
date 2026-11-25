(** Federer (1969), 4.1.7, p. 356: the
    first displayed current identity, boundary squared
    zero in every dimension at least two. The proof
    transposes square zero on the actual test forms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation CurrentBoundary
  CurrentTestExteriorDerivative CurrentExteriorDerivativeSquared.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_boundary_squared]: the original
    boundary satisfies boundary(boundary T)=0 for
    dimension at least two, Federer 4.1.7, p. 356. *)
Theorem current_boundary_squared (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m.+2):
  @current_boundary R h2 n m U hU
    (@current_boundary R h2 n m.+1 U hU T)=0.
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>phi.
by rewrite !current_boundary_evaluation current_test_exterior_derivative_squared !linear0.
Qed.
