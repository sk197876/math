(** Federer (1969), 4.1.18, p. 375: independently
    specify the corresponding compact-test form
    homotopy by its inclusion into the already
    specified smooth-form homotopy. No carrier
    construction or existence is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothTestSpaces LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingTestHomotopyUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation E:=(fun d=>@current_smooth_space R h2 n Full hFull d).
Local Notation D:=(fun d=>@current_test_space R h2 n Full hFull d).
Local Notation Inc:=(fun d=>smooth_test_inclusion (@current_smooth_space_laws R h2 n Full hFull d)).
Variable K:Hom (E (1+m)%N) (E m).

(** Source for [is_current_smoothing_test_homotopy]: the
    actual compact-test operator has exactly the
    original smooth homotopy value, supporting
    the form identities of 4.1.18, p. 375. *)
Definition is_current_smoothing_test_homotopy
    (H:Hom (D (1+m)%N) (D m)):Prop:=
  forall omega,Inc m (H omega)= K (Inc (1+m)%N omega).

(** Source for [current_smoothing_test_homotopy_unique]:
    the original compact-test inclusion is injective,
    so the corresponding homotopy is unique,
    supporting 4.1.18, p. 375. *)
Theorem current_smoothing_test_homotopy_unique (H G:Hom (D (1+m)%N) (D m)):
  is_current_smoothing_test_homotopy H->is_current_smoothing_test_homotopy G->H= G.
Proof.
move=>hH hG;apply:hom_ext=>omega.
apply:(subspace_representation_injective
  (smooth_test_space_laws (@current_smooth_space_laws R h2 n Full hFull m))).
by rewrite (@hH omega) (@hG omega).
Qed.
End CurrentSmoothingTestHomotopyUP.
