(** Federer (1969), 4.1.7, p. 359:
    the bare equation boundary S=delta_b
    does not determine a unique whole-line
    current. The two actual integral
    primitives differ by E^1, whose
    nonzero value follows from 4.1.4. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentBoundary
  CurrentDiracDensity EuclideanFundamentalCurrent EuclideanFundamentalCurrentNonzero
  HalflineCurrents HalflinePrimitiveBoundary HalflineSecondPrimitive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [halfline_primitive_nonuniqueness]:
    two distinct actual whole-line currents
    have boundary delta_b, correcting the
    unqualified uniqueness phrase in Federer
    4.1.7, p. 359. *)
Theorem halfline_primitive_nonuniqueness (R:realType) (h2:(1+1:R)!=0) b:
  @current_boundary R h2 1 0%N (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1)) x)
    (@halfline_left_primitive_candidate R h2 b)=@full_dirac_current R h2 1 (euclidean_one_embed b) /\
  @current_boundary R h2 1 0%N (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1)) x)
    (@halfline_right_primitive_candidate R h2 b)=@full_dirac_current R h2 1 (euclidean_one_embed b) /\
  @halfline_left_primitive_candidate R h2 b<>@halfline_right_primitive_candidate R h2 b.
Proof.
split;first exact:halfline_left_primitive_boundary.
split;first exact:halfline_right_primitive_boundary.
move=>hEqual;apply:(@euclidean_fundamental_current_nonzero R h2 1).
have hDifference:@halfline_left_primitive_candidate R h2 b-
    @halfline_right_primitive_candidate R h2 b=@euclidean_fundamental_current R h2 1.
  by rewrite /halfline_right_primitive_candidate opprB addrCA subrr addr0.
by rewrite -hDifference -hEqual subrr.
Qed.
