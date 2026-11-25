(** Federer (1969), 3.1.1(2–3), p. 210:
    actual differentials transform by the chain rule under
    fixed invertible source and target linear coordinates.
    This is the original differential calculation used in
    3.2.46, p. 282, without a derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness OperatorNorm NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal NormDifferentialEnlarge NormDifferentialFiniteCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_frozen_differential]:
    D(M F L^{-1})(L(a))=M DF(a) L^{-1},
    supporting 3.2.46, p. 282, from the exact
    chain rule of 3.1.1(2), p. 210. The
    original actual differential is the only differential
    premise; all singular maps and natural dimensions remain. *)
Lemma euclidean_frozen_differential (R : realType) m n
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n})
    (F : R_n R m -> R_n R n) a (D : Hom (R_n R m) (R_n R n)) :
  cancel L I ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT F a D ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT (fun z=>M (F (I z))) (L a)
    (hom_comp (hom_of_linear M) (hom_comp D (hom_of_linear I))).
Proof.
move=> hLI hD.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
have hIBounded : norm_bounded_linear NX NX (hom_of_linear I).
  exists (linear_operator_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R m) (@coordinate_basisP R m) I); split.
  - exact:linear_operator_norm_nonnegative.
  - move=> v; exact (linear_operator_norm_bound (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R m) (@coordinate_basisP R m) I v).
have hMBounded : norm_bounded_linear NY NY (hom_of_linear M).
  exists (linear_operator_norm (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) M); split.
  - exact:linear_operator_norm_nonnegative.
  - move=> v; exact (linear_operator_norm_bound (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n) M v).
have hWhole : norm_domain_interior NX setT (L a).
  exists 1; split; first exact:ltr01; by move=> v hv.
have hDI := @norm_differential_linear R (R_n R m) (R_n R m) NX NX hNX hNX
  setT (L a) (hom_of_linear I) hWhole hIBounded.
have hDAt : has_norm_differential NX NY setT F (I (L a)) D by rewrite hLI.
have hComp := @norm_differential_chain R (R_n R m) (R_n R m) (R_n R n)
  NX NX NY hNX hNX hNY setT setT I F (L a) (hom_of_linear I) D hDI hDAt.
have hPre : has_norm_differential NX NY setT (fun z=>F (I z)) (L a)
    (hom_comp D (hom_of_linear I)).
  exact (@norm_differential_enlarge R (R_n R m) (R_n R n) NX NY
    (fun x=>setT x /\ setT (I x)) setT (fun z=>F (I z)) (L a)
    (hom_comp D (hom_of_linear I)) (fun x _=>Logic.I) hComp).
exact (@norm_differential_postcompose R (R_n R m) (R_n R n) (R_n R n)
  NX NY NY hNX setT (fun z=>F (I z)) (L a) (hom_comp D (hom_of_linear I))
  (hom_of_linear M) hPre hMBounded).
Qed.
