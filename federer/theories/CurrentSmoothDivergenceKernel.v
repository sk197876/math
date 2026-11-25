(** Federer (1969), 4.1.18, p. 377: the original
    smooth graph pairs (div eta,eta) have zero image
    under the sum of the Lebesgue-density and boundary
    maps. This whole-space law supports the original
    open-domain kernel-closure assertion. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentVectorSpaces CurrentBoundary CurrentSmoothLebesgue
  SmoothCurrentDivergence CurrentSmoothLebesgueBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentSmoothDivergenceKernel.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX :=
  (inner_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _:X => True).
Local Notation hFull :=
  (fun (x:X) (_:True) => @norm_full_domain_interior R X NX x).
Local Notation V d :=
  (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation L d := (@current_smooth_lebesgue_map R h2 n d).
Local Notation div :=
  (@smooth_current_divergence R h2 n m Full hFull).

(** Source for [current_smooth_divergence_pair_kernel]:
    the graph pair (div eta,eta) maps to zero, supporting
    the right-hand set in Federer 4.1.18, p. 377. The
    sign is positive in the pair because the preceding
    boundary formula is boundary(L eta)=-L(div eta).
    Compactly supported eta is a permitted special case. *)
Theorem current_smooth_divergence_pair_kernel (eta : V m.+1) :
  L m (div eta)+@current_boundary R h2 n m Full hFull
    (L m.+1 eta)=0.
Proof. by rewrite current_smooth_lebesgue_boundary addrN. Qed.
End CurrentSmoothDivergenceKernel.
