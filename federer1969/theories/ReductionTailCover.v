(** Federer (1969), 3.4.8(13), p. 335:
    outside the exceptional differences in (7) and (9),
    one original E_m contains each rotation. The
    existing finite-minimum theorem selects the least complete
    B-tail at that particular rotation; no monotonicity
    or additional generic-coordinate assertion is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import AnalyticReductionDepthUP AnalyticReductionDepthExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [reduction_tail_cover]: the finite union
    of original E_m covers all nonexceptional rotations,
    3.4.8(13), p. 335. The hypotheses are
    precisely the membership equations and the complements
    of the differences already proved null in (7),(9). *)
Theorem reduction_tail_cover n (O:Type)
    (A E:'I_n.+1->set O) (B C:'I_n->set O) (g:O):
  ~A ord0 g ->
  (forall m:'I_n,E (widen_ord (leqnSn n) m) g <->
    C m g /\(forall j:'I_n,(m<=j)%N ->B j g) /\~A (widen_ord (leqnSn n) m) g) ->
  (E ord_max g <->~A ord_max g) ->
  (forall j:'I_n,A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g ->B j g) ->
  (forall m:'I_n,(forall j:'I_n,(m<=j)%N ->B j g) ->C m g) ->
  exists m:'I_n.+1,E m g.
Proof.
move=>hA0 hE hLast hAB hBC.
have [d hD]:=@analytic_reduction_depth_exists n unit tt (fun j _=>B j g).
have hDN:=analytic_reduction_depth_bound hD.
have [_ hTail]:=analytic_reduction_depth_attained hD.
pose di:'I_n.+1:=Ordinal (leq_ltn_trans hDN (ltnSn n)).
have hNotA:~A di g.
  case:(posnP d)=>[hZero|hPositive].
  - have hIndex:di=ord0 by apply:val_inj;exact:hZero.
    by rewrite hIndex.
  - have hPred:(d.-1<n)%N.
      have hBound:=hDN;by rewrite -(prednK hPositive) in hBound.
    pose j:'I_n:=Ordinal hPred.
    have hIndex:(@Ordinal n.+1 (j:nat).+1 (ltn_ord j))=di.
      apply:val_inj;exact:prednK hPositive.
    move=>hA.
    have hB:B j g by apply:hAB;rewrite hIndex.
    have hLower:has_analytic_reduction_tail (fun k (_:unit)=>B k g) d.-1.
      exists tt=>k hJK.
      case:(leqP d k)=>hDK;first exact:hTail k hDK.
      have hKJ:(k:nat)=d.-1.
        apply/eqP;rewrite eqn_leq hJK andbT -ltnS (prednK hPositive);exact:hDK.
      have hEqual:k=j by apply:val_inj;exact:hKJ.
      by rewrite hEqual.
    have hImpossible:=analytic_reduction_depth_minimal hD hLower.
    have hStrict:(d.-1<d)%N by rewrite -(prednK hPositive) ltnSn.
    by move:hImpossible;rewrite leqNgt hStrict.
case:(ltnP d n)=>hLess.
- pose m:'I_n:=Ordinal hLess.
  have hIndex:widen_ord (leqnSn n) m=di by apply:val_inj.
  exists di;rewrite -hIndex;apply:(hE m).2.
  split;first exact:hBC m hTail.
  split;first exact:hTail.
  by rewrite hIndex.
- have hEqual:d=n by apply/eqP;rewrite eqn_leq hDN hLess.
  have hIndex:di=ord_max by apply:val_inj;exact:hEqual.
  exists di;rewrite hIndex;apply:hLast.2.
  by rewrite -hIndex.
Qed.
