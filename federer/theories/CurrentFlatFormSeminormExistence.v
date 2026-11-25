(** Federer (1969), 4.1.12, p. 367: existence
    of the original compact flat-form seminorm. The
    displayed maximum supplies an existence witness;
    downstream users use its independently stated law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothCurrentExteriorDerivative CurrentFlatFormSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_flat_form_seminorm_exists]: the
    original F_K exists on the actual smooth forms,
    Federer 4.1.12, p. 367. Its compact set and
    exterior derivative are the original ones. *)
Theorem current_flat_form_seminorm_exists (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
  exists p:@current_smooth_space R h2 n U hU m->R,
    @is_current_flat_form_seminorm R h2 n m U hU K p.
Proof.
exists (fun phi=>Num.max
  (smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 n U hU m) K 0%N phi)
  (smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 n U hU m.+1) K 0%N
    (@smooth_current_exterior_derivative R h2 n m U hU phi))).
by [].
Qed.
