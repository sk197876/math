(** Federer (1969), 3.4.8(11), p. 335:
    the original nested strict prefix neighbourhood
    is closed relative to T. Every weak
    prefix inequality on the closure becomes strict
    by the monic root bounds and the
    adjacent-prefix norm estimate proved earlier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealMetricBackground FiniteContinuousStrictBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nested_prefix_box_relatively_closed]:
    S=T intersect V is closed relative
    to T in the original construction,
    3.4.8(11), p. 335. The scalar
    root and prefix-step estimates are the
    preceding proved inputs; this theorem supplies
    the full closure argument. *)
Theorem nested_prefix_box_relatively_closed (R:realType) (X:topologicalType)
    n m (hMN:(m<=n)%N) (D:set X) (q a:nat->X->R) (epsilon:nat->R):
  (forall j,continuous (fun x:X=>(q j x:real_line_metric R))) ->
  (forall j,(m<=j<n)%N ->epsilon j<epsilon j.+1/2) ->
  (forall j,(m<=j<n)%N ->forall x,D x ->q j.+1 x<=q j x+a j x) ->
  (forall j,(m<=j<n)%N ->forall x,D x ->
    (forall l:'I_n.+1,(m<=l)%N ->q l x<=epsilon l) ->
    q j x<=epsilon j ->a j x<epsilon j.+1/2) ->
  let V:set X:=[set x|forall j:'I_n.+1,(m<=j)%N ->q j x<epsilon j] in
  let S:set X:=D `&` V in
  let T:set X:=D `&` [set x|q m x<epsilon m] in
  T `&` closure S `<=` S.
Proof.
move=>hQ hShrink hStep hRoot V S T x [[hDx hBase] hClosure].
split;first exact:hDx.
have hSV:S `<=` V by move=>y [_ hy];exact:hy.
have hClosureV:closure V x:=closureS hSV hClosure.
have hWeak:=@continuous_strict_box_closure_bound R X 'I_n.+1
  [set j:'I_n.+1|(m<=j)%N] (fun j=>q j) (fun j=>epsilon j)
  (fun j=>hQ j) x hClosureV.
move=>j hMJ.
case:(eqVneq (j:nat) m)=>hEqual.
- by rewrite hEqual.
- have hMJLt:(m<j)%N by rewrite ltn_neqAle eq_sym hEqual hMJ.
  have hJPositive:(0<j)%N:=leq_ltn_trans (leq0n m) hMJLt.
  have hPred:(j.-1).+1 = (j:nat):=prednK hJPositive.
  have hMPrev:(m<=j.-1)%N by move:hMJLt;rewrite -hPred ltnS.
  have hPrevN:(j.-1<n)%N.
    have hBound:(j<=n)%N:=ltn_ord j.
    by rewrite -hPred in hBound.
  have hPrevBounds:(m<=j.-1<n)%N by apply/andP;split.
  have hPrevOrd:(j.-1<n.+1)%N:=ltn_trans hPrevN (ltnSn n).
  have hPrevious:q j.-1 x<=epsilon j.-1:=hWeak (Ordinal hPrevOrd) hMPrev.
  have hLast:=hRoot j.-1 hPrevBounds x hDx hWeak hPrevious.
  have hIncrement:=hStep j.-1 hPrevBounds x hDx.
  have hRadius:=hShrink j.-1 hPrevBounds.
  rewrite hPred in hLast hIncrement hRadius.
  lra.
Qed.
