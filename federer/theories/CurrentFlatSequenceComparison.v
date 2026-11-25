(** Federer (1969), 4.1.14, pp. 370–371: finite prefixes
    do not affect the original flat convergence, and two
    asymptotically equal smooth image sequences have the same
    limit. All values are the original extended flat seminorms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm CurrentFlatSequenceLimitUP
  CurrentFlatFiniteArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatSequenceComparison.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation Limit:=(@is_current_flat_sequence_limit R h2 n m U hU K).

(** Source for [current_flat_sequence_limit_tail]: passing to
    sufficiently large indices preserves the displayed limit,
    as used in Federer 4.1.14, p. 370. *)
Lemma current_flat_sequence_limit_tail (u:nat->C) T k:
  Limit u T->Limit (fun i=>u (k+i)%N) T.
Proof.
move=>hLimit epsilon hEpsilon;have[N hN]:=hLimit epsilon hEpsilon.
exists N=>i hNi;exact:hN _ (leq_trans hNi (leq_addl k i)).
Qed.

(** Source for [current_flat_sequence_limit_of_tail]: the
    original full sequence has the same limit as a sufficiently
    late tail, supporting the construction in Federer 4.1.14,
    p. 370. No condition is imposed on the finite prefix. *)
Lemma current_flat_sequence_limit_of_tail (u:nat->C) T k:
  Limit (fun i=>u (k+i)%N) T->Limit u T.
Proof.
move=>hLimit epsilon hEpsilon;have[N hN]:=hLimit epsilon hEpsilon.
exists (k+N)%N=>i hNi.
have hKi:(k<=i)%N:=leq_trans (leq_addr N k) hNi.
have hNRest:(N<=i-k)%N by rewrite leq_subRL // addnC.
have h:=hN (i-k)%N hNRest.
by rewrite (subnKC hKi) in h.
Qed.

(** Source for [current_flat_sequence_limit_compare]: comparing
    two smooth image sequences on the common source gives the
    same original F_E limit, Federer 4.1.14, p. 370. The
    finite triangle law is applied only after both actual errors
    have become finite; no flat-membership premise is added. *)
Theorem current_flat_sequence_limit_compare (u v:nat->C) T:
  Limit u T->
  (forall epsilon:R,0<epsilon->exists N:nat,forall i:nat,(N<=i)%N->
    (F ((u i-v i)%R)<epsilon%:E)%E)->Limit v T.
Proof.
move=>hLimit hClose epsilon hEpsilon.
have hThird:0<epsilon/3 by rewrite divr_gt0 // ltr0n.
have[k hk]:=hLimit (epsilon/3) hThird.
have[l hl]:=hClose (epsilon/3) hThird.
exists (maxn k l)=>i hNi.
have hA:=hk i (leq_trans (leq_maxl _ _) hNi).
have hB:=hl i (leq_trans (leq_maxr _ _) hNi).
have hAFinite:(F ((T-u i)%R)< +oo)%E:=lt_trans hA (ltry _).
have hBFinite:(F ((u i-v i)%R)< +oo)%E:=lt_trans hB (ltry _).
have hTriangle:=@current_flat_finite_triangle R h2 n m U hU K
  (T-u i) (u i-v i) hAFinite hBFinite.
rewrite addrA subrK in hTriangle.
have hCaps:=leeD (ltW hA) (ltW hB).
rewrite -EFinD in hCaps.
apply:(le_lt_trans (le_trans hTriangle hCaps)).
rewrite lte_fin;lra.
Qed.
End CurrentFlatSequenceComparison.
