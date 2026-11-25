(** Federer (1969), 4.1.7, pp. 356–358:
    specialise the original boundary–contraction
    identity to a smooth scalar multiplier.
    The degree-zero sign is one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentContraction
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentBoundaryContraction SmoothCurrentExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentScalarBoundaryContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun d=>@current_space R h2 n U hU d).
Local Notation P := (fun k p=>@current_contraction R h2 n k p U hU).
Local Notation bd := (@current_boundary R h2 n m U hU).
Local Notation d := (@smooth_current_exterior_derivative R h2 n 0 U hU).

(** Source for [current_scalar_boundary_contraction]:
    the boundary of T contracted gamma
    equals (boundary T) contracted gamma
    minus T contracted d gamma, supporting
    the local normality assertions of Federer
    4.1.7, p. 358, from the
    second displayed identity on p. 356. *)
Theorem current_scalar_boundary_contraction (T:C m.+1)
    (gamma:@current_smooth_space R h2 n U hU 0):
  bd (P 0 m.+1 gamma T)= P 0 m gamma (bd T)-
    P 1 m (d gamma)
      (@current_degree_transport R h2 n U hU (0+m).+1 (1+m) (esym (addSn 0 m)) T).
Proof.
have hGeneral:=@current_boundary_contraction R h2 n 0 m U hU T gamma.
have hTransport:@current_degree_transport R h2 n U hU (0+m).+1 (0+m.+1)
    (esym (addnS 0 m)) T=T.
  exact:current_degree_transport_identity.
rewrite hTransport expr0 scale1r in hGeneral.
pose Q:=P 1 m (d gamma)
  (@current_degree_transport R h2 n U hU (0+m).+1 (1+m) (esym (addSn 0 m)) T).
pose A0:=bd (P 0 m.+1 gamma T).
have hSum:P 0 m gamma (bd T)=Q+A0:=hGeneral.
have hSubtract:=congr1 (fun z:C m=>z-Q) hSum.
have hCancel:(Q+A0)-Q=A0 by rewrite (addrC Q A0) addrK.
exact (esym (eq_trans hSubtract hCancel)).
Qed.
End CurrentScalarBoundaryContraction.
