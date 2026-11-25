(** Federer (1969), 4.1.15, p. 373: a fixed original
    test detects an alternating sequence of nonzero currents.
    This elementary weak-topology consequence supports both
    the degree-one example and its correctly typed boundary
    counterpart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CurrentSpaces CurrentEvaluation CurrentPointEvaluation CurrentWeakSequenceLimit
  NonzeroAlternatingRealSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentAlternatingSequenceDivergence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation DT:=(@current_test_space R h2 n U hU m).
Local Notation action:=(@current_value R h2 n U hU m).

(** Source for [current_alternating_sequence_diverges]: the weak
    nonconvergence in 4.1.15, p. 373, follows from a
    single test with nonzero action when the image currents
    are exactly (-1)^i times one nonzero current. *)
Theorem current_alternating_sequence_diverges (T:C):T<>0->
  ~exists Q:C,@is_current_weak_sequence_limit R h2 n m U hU
    (fun i=>(-1:R)^+i*:T) Q.
Proof.
move=>hNonzero [Q hWeak].
have [phi hPhi]:exists phi:DT,action T phi<>0.
  apply:contrapT=>hNone;apply:hNonzero.
  apply:(@current_values_extensional R h2 n m U hU)=>phi.
  rewrite (linear0 action) hom_zeroE.
  apply:contrapT=>hNot;apply:hNone;by exists phi.
pose b:R:=action T phi.
pose c:R:=action Q phi.
apply:(@nonzero_alternating_real_sequence_diverges R b hPhi).
exists c=>eps hEps;have [N hN]:=hWeak phi eps hEps.
exists N=>i hi.
have hValue:=hN i hi.
by rewrite current_value_scale in hValue.
Qed.
End CurrentAlternatingSequenceDivergence.
