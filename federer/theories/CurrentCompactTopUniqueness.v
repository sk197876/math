(** Federer (1969), 4.1.11, p. 365: identify the original
    reversed time-segment image by its boundary. The supporting
    uniqueness is an immediate use of the preceding compact
    closed top-degree vanishing theorem, 4.1.10, p. 364. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentCompactSmoothAlgebra CurrentConeCurrentFormulas.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_compact_top_boundary_unique]: two
    compact currents of the same positive top degree and with
    the same boundary coincide. This supporting consequence of
    Federer 4.1.10, p. 364, is used in the reversing identity
    of 4.1.11, p. 365. No degree-zero uniqueness is asserted. *)
Theorem current_compact_top_boundary_unique (R:realType) (h2:(1+1:R)!=0)
    n k (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (S T:@current_space R h2 n U hU k.+1)
    (hS:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU k.+1 S))
    (hT:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU k.+1 T)):
  n=k.+1->@current_boundary R h2 n k U hU S=@current_boundary R h2 n k U hU T->S=T.
Proof.
move=>hDegree hBoundary.
have hDifference:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n U hU k.+1 (S-T)).
  have h:=@current_compact_linear_support R h2 n k.+1 U hU (-1:R) T S hT hS.
  by rewrite scaleN1r addrC in h.
have hClosed:@current_boundary R h2 n k U hU (S-T)=0.
  by rewrite linearB /= hBoundary subrr.
pose hDerived:=@CurrentHomotopyUP.current_homotopy_source_open R n n
  (fun _:R=>True) U (fun _:R_n R n=>True)
  (fun _:R_n R n=>0) (fun x:R_n R n=>x)
  (@CurrentConeHomotopySealed.CurrentConeHomotopy.value R n 0)
  (@CurrentConeHomotopyClass.current_cone_ambient_homotopy R n 0 U hU).1.
have hOpen:hDerived=hU:=Prop_irrelevance _ _.
have hTop:=@current_compact_closed_top R h2 n U hU (0:R_n R n) k.
fold hDerived in hTop;rewrite hOpen in hTop.
have hZero:=hTop (S-T) hDifference hDegree hClosed.
apply/eqP;have hEq:S-T==0:=introT eqP hZero.
by rewrite subr_eq0 in hEq.
Qed.
