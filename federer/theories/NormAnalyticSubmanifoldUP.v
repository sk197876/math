(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.1.19(1), p. 231, and
    3.1.24, p. 240: analytic straightening in an
    arbitrary finite-dimensional normed ambient space. This is
    the same original plane-section definition as the existing
    Euclidean predicate; no chart existence is postulated. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ModuleQuotient RealNormUP NormDifferentialUP NormDiffeomorphismUP NormAnalyticUP
  GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanSubmanifoldUP AnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_norm_analytic_submanifold]: the original
    analytic version of 3.1.19(1), p. 231,
    used for the underlying real ambient space in
    3.4.12, p. 339. Actual class-one
    inverse maps and their analytic laws are explicit. *)
Definition is_norm_analytic_submanifold (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) m (S:set X):=
  forall b,S b ->exists (T C:set X) (s t:X->X) (Z:G X m),
    norm_domain_interior NX T b /\
    is_norm_diffeomorphism hNX hNX T C s t 1%N /\
    @norm_analytic R X X NX NX hNX hNX T s /\
    @norm_analytic R X X NX NX hNX hNX C t /\
    s @` (S `&` T)=[set x|grassmann_val Z x /\C x].

(** Source for [norm_analytic_euclidean_submanifold]: the normed
    straightening predicate is exactly the existing Euclidean
    analytic submanifold definition in Euclidean coordinates,
    3.1.24, p. 240. *)
Theorem norm_analytic_euclidean_submanifold (R:realType) n m (S:set (R_n R n)):
  is_norm_analytic_submanifold (inner_norm_real_norm (@euclidean_inner_productP R n)) m S <->
  @is_euclidean_analytic_submanifold R n m S.
Proof.
split=>h b hb;have [T [C [s [t [Z hZ]]]]]:=h b hb;exists T,C,s,t,Z.
- have [hT [hD [hS [hI hImage]]]]:=hZ.
  split;last by split.
  by constructor.
- have [[hT hD hImage] [hS hI]]:=hZ.
  by split=>//;split=>//;split=>//;split.
Qed.
