(** Federer (1969), 3.4.8(11), pp. 334–335:
    assemble the original backwards radius selection,
    open prefix neighbourhood, closure control and
    finite component count. Analytic monic-root control
    and base component finiteness are the preceding
    algebraic and induction inputs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import RealMetricBackground FiniteBackwardPositiveRadii FiniteContinuousStrictBox
  NestedPrefixBoxClosed RelativeClopenComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nested_prefix_finite_neighbourhood]:
    the complete original nested neighbourhood construction,
    3.4.8(11), pp. 334–335. Its inputs
    are the previously proved prefix and root
    estimates and the lower-dimensional base component
    count; no clopen conclusion is assumed. *)
Theorem nested_prefix_finite_neighbourhood (R:realType) (X:topologicalType)
    n m (hMN:(m<=n)%N) (x0:X) (D:set X) (q a:nat->X->R) r:
  0<r ->
  (forall j,continuous (fun x:X=>(q j x:real_line_metric R))) ->
  (forall j,(j<=n)%N ->q j x0 = 0) ->
  (forall j,(m<=j<n)%N ->forall x,D x ->q j.+1 x<=q j x+a j x) ->
  (forall j,(m<=j<n)%N ->forall t:R,0<t ->exists s:R,0<s /\ s<t/2 /\
    forall x,D x ->q n x<=r ->q j x<=s ->a j x<t/2) ->
  (forall s:R,0<s ->s<=r ->finite_set (connected_component (D `&` [set x|q m x<s]) @`
    (D `&` [set x|q m x<s]))) ->
  exists epsilon:nat->R,epsilon n = r /\
    (forall j,(j<=n)%N ->0<epsilon j) /\
    let V:set X:=[set x|forall j:'I_n.+1,(m<=j)%N ->q j x<epsilon j] in
    open V /\ V x0 /\
    closure V `<=` [set x|q n x<=r] /\
    finite_set (connected_component (D `&` V) @` (D `&` V)).
Proof.
move=>hr hQ hZero hStep hControl hBaseFinite.
pose step:=fun j (t s:R)=>s<t/2 /\ ((m<=j<n)%N ->
  forall x,D x ->q n x<=r ->q j x<=s ->a j x<t/2).
have hChoose j t (ht:0<t):exists s:R,0<s /\ step j t s.
  case hActive:(m<=j<n)%N.
  - have [s [hs [hSmall hRoot]]]:=hControl j hActive t ht.
    exists s;split;first exact:hs.
    split;first exact:hSmall.
    by move=>_.
  - exists (t/4);split;first by rewrite divr_gt0 // ltr0n.
    split;first by lra.
    move=>hImpossible;by rewrite hActive in hImpossible.
have [epsilon [hLast [hPositive hSteps]]]:=@finite_backward_positive_radii R step hChoose n r hr.
have hChain:forall j k,(j<=k)%N ->(k<=n)%N ->epsilon j<=epsilon k.
  move=>j;elim=>[|k IH] hJK hKN.
  - move:hJK;rewrite leqn0=>/eqP ->;exact:lexx.
  - case:(eqVneq j k.+1)=>hEqual;first by rewrite hEqual.
    have hJK':(j<=k)%N by rewrite -ltnS ltn_neqAle hEqual hJK.
    have hKN':(k<=n)%N:=leq_trans (leqnSn k) hKN.
    have hEarlier:=IH hJK' hKN'.
    have hSmall:epsilon k<epsilon k.+1/2:=(hSteps k hKN).1.
    have hNextPositive:=hPositive k.+1 hKN.
    lra.
have hBaseBound:epsilon m<=r.
  rewrite -hLast;exact:hChain m n hMN (leqnn n).
exists epsilon;split;first exact:hLast.
split;first exact:hPositive.
pose V:set X:=[set x|forall j:'I_n.+1,(m<=j)%N ->q j x<epsilon j].
have hV:open V:=@finite_continuous_strict_box_open R X (Finite.clone 'I_n.+1 _)
  [set j:'I_n.+1|(m<=j)%N] (fun j=>q j) (fun j=>epsilon j) (fun j=>hQ j).
split;first exact:hV.
split.
- move=>j hMJ;rewrite hZero;[exact:hPositive j (ltn_ord j)|exact:ltn_ord j].
- split.
  + move=>x hx.
    have hWeak:=@continuous_strict_box_closure_bound R X 'I_n.+1
      [set j:'I_n.+1|(m<=j)%N] (fun j=>q j) (fun j=>epsilon j) (fun j=>hQ j) x hx.
    have hBound:=hWeak (ord_max:'I_n.+1) hMN.
    by rewrite hLast in hBound.
  + pose S:set X:=D `&` V.
    pose T:set X:=D `&` [set x|q m x<epsilon m].
    have hShrink j (hj:(m<=j<n)%N):epsilon j<epsilon j.+1/2.
      exact:(hSteps j (andP hj).2).1.
    have hRoot j (hj:(m<=j<n)%N) x (hx:D x)
        (hWeak:forall l:'I_n.+1,(m<=l)%N ->q l x<=epsilon l)
        (hPx:q j x<=epsilon j):a j x<epsilon j.+1/2.
      have hWhole:q n x<=r.
        have hBound:=hWeak (ord_max:'I_n.+1) hMN;by rewrite hLast in hBound.
      exact:(hSteps j (andP hj).2).2 hj x hx hWhole hPx.
    have hClosed:T `&` closure S `<=` S:=@nested_prefix_box_relatively_closed R X n m hMN
      D q a epsilon hQ hShrink hStep hRoot.
    have hST:S = T `&` V.
      apply/seteqP;split.
      - move=>x [hx hVx];split;last exact:hVx.
        split;first exact:hx.
        have hAt:=hVx (@Ordinal n.+1 m hMN) (leqnn m).
        exact:hAt.
      - by move=>x [[hx hBase] hVx];split.
    exact:(@relative_clopen_finite_components X S T V hV hST hClosed
      (hBaseFinite (epsilon m) (hPositive m hMN) hBaseBound)).
Qed.
