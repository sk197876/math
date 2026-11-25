(** Federer (1969), 3.3.18, p. 301: summable positive
    atomic budgets for a countably supported converse counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GeometricErrorBudget NonnegativeSum NonnegativeSumScale
  NonnegativeSumSupport NonnegativeSumProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [geometric_double_budget_bound]: supporting the
    countable-support counterexample assertion in Federer 3.3.18,
    p. 301. Products of the actual positive geometric error budgets
    have finite total sum, by 2.1.1(6),(10). The bound follows
    from their proved one-dimensional sum bounds, without an
    external infinite-series theorem. *)
Lemma geometric_double_budget_bound (R:realType):
  nonnegative_sum [set: (nat*nat)%type] (fun p=>
    (geometric_error_budget (1:R) p.1*geometric_error_budget (1:R) p.2)%:E)<= 1.
Proof.
pose b:=geometric_error_budget (1:R).
have hb i:(0<b i)%R:=geometric_error_budget_positive i (@ltr01 R).
have hbe i:(0<=(b i)%:E)%E by rewrite lee_fin; exact:ltW (hb i).
have hHalf:(0<=(1/2:R))%R by lra.
have hHalfE:(0<=(1/2:R)%R%:E)%E by rewrite lee_fin.
have hAll:[set:(nat*nat)%type]=[set:nat] `*` [set:nat].
  by apply/seteqP; split=>p _; split.
rewrite hAll.
have hWeight p:([set:nat] `*` [set:nat]) p ->0<=(b p.1*b p.2)%R%:E.
  move=>_; rewrite lee_fin; exact:mulr_ge0 (ltW (hb _)) (ltW (hb _)).
rewrite (nonnegative_sum_product_first hWeight).
have hOne:=@geometric_error_sum_bound R 1%R (@ltr01 R).
have hOuter:nonnegative_sum setT (fun j=>
    nonnegative_sum setT (fun k=>(b j*b k)%R%:E))<=
  nonnegative_sum setT (fun j=>(1/2:R)%R%:E*(b j)%:E).
  apply:nonnegative_sum_mono=>j _.
  have hTerms:(fun k=>(b j*b k)%R%:E)=(fun k=>(b j)%:E*(b k)%:E).
    by apply:funext=>k; rewrite EFinM.
  rewrite hTerms (@nonnegative_sum_scale R [the choiceType of (nat:Type)] setT
    (fun k=>(b k)%:E) (b j) (ltW (hb j)) (fun k _=>hbe k)).
  have hFinal:=lee_wpmul2l (hbe j) hOne.
  rewrite [((b j)%:E*(1/2)%R%:E)%E]muleC in hFinal.
  exact:hFinal.
apply:le_trans hOuter _.
rewrite (@nonnegative_sum_scale R [the choiceType of (nat:Type)] setT
  (fun j=>(b j)%:E) (1/2)%R hHalf (fun j _=>hbe j)).
apply:le_trans (lee_wpmul2l hHalfE hOne) _.
rewrite -EFinM lee_fin; lra.
Qed.
