(** Federer (1969), 4.1.18, p. 377: the original
    density-and-boundary map has a kernel closed for the
    pair L1 cost. This supporting current statement reuses
    mass-to-weak convergence and boundary continuity from
    4.1.12, pp. 368–369. Approximating pairs may have
    different supports; no common compact index is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentPointEvaluation CurrentBoundary
  CurrentMassSealed CurrentMassBasic CurrentMassWeakConvergence
  CurrentWeakSequenceLimit CurrentWeakLimitOperations CurrentWeakSequenceLinear
  GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPairMassKernelClosed.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation action:=(@current_value R h2 n U hU m).

(** Source for [current_pair_mass_kernel_closed]: arbitrarily
    accurate original mass-pair approximation by pairs with
    A+boundary S=0 forces the same identity for the original
    pair. This supplies closure into the kernel in Federer
    4.1.18, p. 377, after the existing density L1 bounds.
    Neither input needs finite mass, compact support or flatness. *)
Theorem current_pair_mass_kernel_closed (A:C) (S:Next):
  (forall epsilon:R,0<epsilon->exists B:C,exists Q:Next,
    B+bd Q=0 /\(M (A-B)+NextM (S-Q)<epsilon%:E)%E)->
  A+bd S=0.
Proof.
move=>hApprox.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
have hChoice k:exists p:(C*Next)%type,
    p.1+bd p.2=0 /\(M (A-p.1)+NextM (S-p.2)<(q^+k)%:E)%E.
  have[B [Q [hZero hCost]]]:=hApprox (q^+k) (exprn_gt0 k (andP hq).1).
  exists (B,Q);by split.
have[v hv]:=choice hChoice.
have hFirst:@is_current_weak_sequence_limit R h2 n m U hU
    (fun i=>(v i).1) A.
  apply:(@current_mass_convergence_is_weak R h2 n m U hU
    (fun i=>(v i).1) A)=>epsilon hEpsilon.
  have[k hk]:=@geometric_uniform_tail R q 1 epsilon hq (@ler01 R) hEpsilon.
  exists k=>L hKL.
  apply:(le_lt_trans (leeDl (M (A-(v L).1))
    (@current_mass_nonnegative R h2 n m.+1 U hU (S-(v L).2)))).
  apply:(lt_trans (@hv L).2);rewrite lte_fin.
  have h:=hk L hKL;by rewrite mulr1 in h.
have hSecond:@is_current_weak_sequence_limit R h2 n m.+1 U hU
    (fun i=>(v i).2) S.
  apply:(@current_mass_convergence_is_weak R h2 n m.+1 U hU
    (fun i=>(v i).2) S)=>epsilon hEpsilon.
  have[k hk]:=@geometric_uniform_tail R q 1 epsilon hq (@ler01 R) hEpsilon.
  exists k=>L hKL.
  apply:(le_lt_trans (leeDr (NextM (S-(v L).2))
    (@current_mass_nonnegative R h2 n m U hU (A-(v L).1)))).
  apply:(lt_trans (@hv L).2);rewrite lte_fin.
  have h:=hk L hKL;by rewrite mulr1 in h.
have hBoundary:=@current_weak_limit_boundary R h2 n m U hU
  (fun i=>(v i).2) S hSecond.
have hWeak:=@current_weak_sequence_limit_linear R h2 n m U hU
  (fun i=>(v i).1) (fun i=>bd (v i).2) A (bd S) 1 hFirst hBoundary.
have hSequence:(fun i=>1*:(v i).1+bd (v i).2)=
    (fun i=>(v i).1+bd (v i).2).
  by apply:funext=>i;rewrite scale1r.
rewrite hSequence scale1r in hWeak.
apply:(@current_values_extensional R h2 n m U hU)=>phi.
pose E:=@current_point_evaluation R h2 n m U hU phi.
change (E (A+bd S)=E 0).
rewrite (lin0 (hom_linear E)).
apply:(@current_weak_limit_eventual_value R h2 n m U hU
  (fun i=>(v i).1+bd (v i).2) (A+bd S) phi 0 0%N hWeak)=>i _.
rewrite (@hv i).1.
change (E 0=0);exact:(lin0 (hom_linear E)).
Qed.
End CurrentPairMassKernelClosed.
