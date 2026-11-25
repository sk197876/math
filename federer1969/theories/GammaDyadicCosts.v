(** Federer (1969), 3.2.13, p. 250: actual
    summable costs of the two Gamma interval covers.
    The positive near-zero exponent p need not be integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GammaDyadicMass GammaDyadicIntervals NonnegativeGeometricBound
  NonnegativeSum NonnegativeSumSupport NonnegativeSumProduct NonnegativeSumBoolean LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gamma_dyadic_origin_cost]: the
    exact constant-majorant cost on each origin interval,
    supporting Gamma finiteness in Federer 3.2.13, p. 250. *)
Lemma gamma_dyadic_origin_cost (R:realType) (C q:R) n:
  ((C*q^+n/(1/2)^+n)%R%:E)*lebesgue_scalar_measure (@gamma_origin_interval R n)=
    (C*q^+n/2)%R%:E.
Proof.
rewrite gamma_origin_interval_mass -EFinM; congr (_%:E).
have hr:(0<(1/2:R)^+n)%R by apply:exprn_gt0; apply:divr_gt0; lra.
have hEq:(C*q^+n/(1/2)^+n*((1/2)^+n/2)=
    (C*q^+n/(1/2)^+n)*(1/2)^+n/2)%R by ring.
by rewrite hEq divfK ?gt_eqF.
Qed.

(** Source for [gamma_dyadic_tail_cost]: the
    exact cost of the inverse-square tail bound,
    supporting the finite Gamma integral in Federer
    3.2.13, p. 250. *)
Lemma gamma_dyadic_tail_cost (R:realType) (C:R) n:
  (C*((2^+n)^-1)^+2)%R%:E*lebesgue_scalar_measure (@gamma_tail_interval R n)=
    (C*(1/2)^+n)%R%:E.
Proof.
rewrite gamma_tail_interval_mass -EFinM; congr (_%:E).
have hTwo:(0<(2:R))%R by lra.
have hr:(0<(2:R)^+n)%R:=exprn_gt0 n hTwo.
have hEq:(C*((2^+n)^-1)^+2*2^+n=C*(2^+n)^-1*((2^+n)^-1*2^+n))%R by rewrite expr2; ring.
rewrite hEq mulVf ?(gt_eqF hr) // mulr1.
by rewrite div1r exprVn.
Qed.

(** Source for [gamma_dyadic_total_cost_finite]:
    the summable dyadic majorants proving the defining
    Gamma integral finite, Federer 3.2.13, p. 250.
    The index bool times nat keeps both interval
    families and their costs separate without assuming disjointness. *)
Lemma gamma_dyadic_total_cost_finite (R:realType) (C D q:R):
  (0<=C)%R ->(0<=D)%R ->(0<=q)%R ->(q<1)%R ->
  nonnegative_sum setT (fun j:bool*nat=>
    (if j.1 then C*q^+j.2/(1/2)^+j.2 else D*((2^+j.2)^-1)^+2)%R%:E*
    lebesgue_scalar_measure (if j.1 then gamma_origin_interval j.2 else gamma_tail_interval j.2))< +oo.
Proof.
move=>hC hD hq hq1.
pose a (j:bool*nat):=(if j.1 then C*q^+j.2/2 else D*(1/2)^+j.2)%R%:E.
have hTerms (j:bool*nat):
    (if j.1 then C*q^+j.2/(1/2)^+j.2 else D*((2^+j.2)^-1)^+2)%R%:E*
      lebesgue_scalar_measure (if j.1 then gamma_origin_interval j.2 else gamma_tail_interval j.2)=a j.
  case:j=>[b n]; case:b; [exact:gamma_dyadic_origin_cost|exact:gamma_dyadic_tail_cost].
have hSum:nonnegative_sum setT (fun j:bool*nat=>
    (if j.1 then C*q^+j.2/(1/2)^+j.2 else D*((2^+j.2)^-1)^+2)%R%:E*
    lebesgue_scalar_measure (if j.1 then gamma_origin_interval j.2 else gamma_tail_interval j.2))=
      nonnegative_sum setT a.
  apply:nonnegative_sum_ext=>j _; exact:hTerms.
rewrite hSum.
have hHalf:(0<=(1/2:R))%R by lra.
have hHalf1:((1/2:R)<1)%R by lra.
have ha j:0<=a j.
  case:j=>[b n]; case:b; rewrite /a /= lee_fin.
  - apply:divr_ge0; [exact:mulr_ge0 hC (exprn_ge0 n hq)|lra].
  - exact:mulr_ge0 hD (exprn_ge0 n hHalf).
have hProd:((@setT (bool*nat))=(@setT bool) `*` (@setT nat)).
  by apply/seteqP; split=>j _; split.
rewrite hProd nonnegative_sum_product_first; last by move=>j _; exact:ha.
rewrite nonnegative_sum_bool; last by move=>b; exact:nonnegative_sum_nonnegative.
have hOrigin:nonnegative_sum setT (fun n=>a (true,n))<=(C/(1-q))%R%:E.
  have hMono:nonnegative_sum setT (fun n=>a (true,n))<=
      nonnegative_sum setT (fun n=>(C*q^+n)%R%:E).
    apply:nonnegative_sum_mono=>n _; rewrite /a /= lee_fin.
    have hTerm:(0<=C*q^+n)%R:=mulr_ge0 hC (exprn_ge0 n hq); nra.
  exact:le_trans hMono (nonnegative_geometric_bound hC hq hq1).
have hTail:nonnegative_sum setT (fun n=>a (false,n))<=(D/(1-1/2))%R%:E.
  exact:nonnegative_geometric_bound hD hHalf hHalf1.
have hBound:=leeD hOrigin hTail.
apply:le_lt_trans hBound _.
rewrite -EFinD; exact:ltry.
Qed.
