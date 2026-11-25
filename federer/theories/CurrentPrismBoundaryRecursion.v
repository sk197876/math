(** Federer (1969), 4.1.11, p. 366: apply
    the original point-join boundary to the literal
    signed prism sum. These are the algebraic steps
    before the inductive boundary comparison with the
    Cartesian prism and compact top-degree uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Biorthogonal
  CurrentSpaces CurrentDirac CurrentDiracSmooth CurrentBoundary CurrentCompactBoundarySmooth
  CurrentCompactElementaryPushforwards CurrentDegreeTransportIdentity CurrentJoinSealed CurrentJoinBoundaryDegree CurrentJoinBoundaryFirstZero
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentBoundaryRecursion CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPrismBoundaryRecursion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Local Notation F := (fun (m:nat) (v:'I_(m.+1)->Y)=>@OrientedSimplexCurrent.value R h2 p m v).
Local Notation C := (fun m=>@current_space R h2 p Full hFull m).
Local Notation Boundary := (fun m=>@current_boundary R h2 p m Full hFull).
Local Notation Compact := (fun m (T:C m)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
  (@current_support R h2 p Full hFull m T)).
Variables A B:X->Y.
Local Notation PSum := (fun (m:nat) (v:'I_(m.+1)->X)=>
  @current_simplex_prism_sum R h2 n p A B m v).
Local Notation hPSum := (fun (m:nat) (v:'I_(m.+1)->X)=>
  @current_simplex_prism_sum_compact R h2 n p A B m v).

(** Source for [current_prism_sum_boundary_point]: the
    original zero-dimensional prism sum has boundary its
    upper endpoint minus its lower endpoint, supporting
    the induction in Federer 4.1.11, p. 366. *)
Theorem current_prism_sum_boundary_point (v:'I_1->X):
  Boundary 0%N (PSum 0%N v)=
    @dirac_current R h2 p Full hFull (B (v ord0))-
    @dirac_current R h2 p Full hFull (A (v ord0)).
Proof.
cbn beta.
rewrite (@current_simplex_prism_sum_point R h2 n p A B v).
rewrite oriented_simplex_current_boundary_segment oriented_simplex_current_point.
by rewrite /current_simplex_tail /current_simplex_face ordinal_consS ordinal_cons0.
Qed.

(** Source for [current_prism_sum_boundary_recursion]:
    applying the original join boundary to the two
    terms of the prism recursion, with the original
    point current of total one, supporting Federer
    4.1.11, p. 366. No boundary of a degree-zero
    current or join associativity is used. *)
Theorem current_prism_sum_boundary_recursion m (v:'I_(m.+2)->X):
  Boundary m.+1 (PSum m.+1 v)=
    F m.+1 (fun r=>B (v r))-PSum m (current_simplex_tail v)-
    @CurrentJoin.value R h2 p 0%N m
      (@dirac_current R h2 p Full hFull (A (v ord0)))
      (Boundary m (F m.+1 (fun r=>B (v r))))
      (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
      (@current_compact_boundary_compact R h2 p m Full hFull
        (F m.+1 (fun r=>B (v r)))
        (@oriented_simplex_current_compact R h2 p m.+1 (fun r=>B (v r))))+
    @CurrentJoin.value R h2 p 0%N m
      (@dirac_current R h2 p Full hFull (A (v ord0)))
      (Boundary m (PSum m (current_simplex_tail v)))
      (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
      (@current_compact_boundary_compact R h2 p m Full hFull
        (PSum m (current_simplex_tail v)) (hPSum m (current_simplex_tail v))).
Proof.
cbn beta.
pose P:=@dirac_current R h2 p Full hFull (A (v ord0)).
pose hP:=@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I.
pose T:=F m.+1 (fun r=>B (v r)).
pose hT:=@oriented_simplex_current_compact R h2 p m.+1 (fun r=>B (v r)).
pose U:=PSum m (current_simplex_tail v).
pose hU:=hPSum m (current_simplex_tail v).
have hRec:=@current_simplex_prism_sum_recursion R h2 n p A B m v.
rewrite hRec (linB (hom_linear (@current_boundary R h2 p m.+1 Full hFull))).
have hFirst:=@current_join_boundary_first_zero R h2 p m P T hP hT.
have hSecond:=@current_join_boundary_first_zero R h2 p m P U hP hU.
have hTotal:=@dirac_current_total R h2 p Full hFull (A (v ord0)) Logic.I hP.
rewrite /current_join_boundary /current_join_successor current_degree_transport_identity hTotal scale1r in hFirst.
rewrite /current_join_boundary /current_join_successor current_degree_transport_identity hTotal scale1r in hSecond.
rewrite hFirst hSecond.
rewrite opprB !addrA [LHS]addrAC;congr (_+_);exact:addrAC.
Qed.
End CurrentPrismBoundaryRecursion.
