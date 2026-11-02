(** Federer (1969), 3.2.35, p. 272:
    actual nonnegative finite sums and weights
    on the positive radius integration interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP
  MeasureSubsetIntegral SubsetIntegralTotalAgreement TotalFiniteNonnegativeIntegral
  TotalNonnegativeExtendedScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_finite_nonnegative_integral]:
    supporting finite radius integral interchange
    in Federer 3.2.35, p. 272. Only
    values on the original integration set A
    need be nonnegative. Local total completions
    agree exactly with the sealed zero extensions;
    the proved finite integral law then applies.
    Empty index types and infinite values remain. *)
Lemma subset_finite_nonnegative_integral (R:realType) (X:choiceType) (I:finType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X)
    (u:I->X->extended_real_line R) (a:I->\bar R):
  (forall i x,A x ->0<=u i x) ->
  (forall i,is_measure_subset_integral mu A (partial_function_total (u i)) (a i)) ->
  is_measure_subset_integral mu A
    (partial_function_total (fun x=>(\sum_i u i x:extended_real_line R))) (\sum_i a i).
Proof.
move=>hu hi.
pose v i (x:X):extended_real_line R:=if pselect (A x) then u i x else 0.
have hOn i x:A x ->v i x=u i x.
  move=>hx; rewrite /v; case:(pselect (A x))=>// hn; exfalso; exact:hn hx.
have hOff i x:~A x ->v i x=0.
  move=>hx; rewrite /v; case:(pselect (A x))=>// hy; exfalso; exact:hx hy.
have hPositive i x:0<=v i x.
  case:(pselect (A x))=>hx.
  - rewrite (hOn i x hx); exact:hu.
  - by rewrite (hOff i x hx).
have hIntegrals i:is_measure_integral mu (partial_function_total (v i)) (a i).
  apply:(@subset_integral_total_supported R X mu A (v i) (a i) (hOff i)).1.
  apply:(@subset_integral_total_agreement R X mu A (u i) (v i) (a i) _).1 (hi i).
  move=>x hx; exact:Logic.eq_sym (hOn i x hx).
have hSum:=@total_finite_nonnegative_integral R X I mu hm v a hPositive hIntegrals.
have hSumOff x:~A x ->(\sum_i v i x)=0.
  move=>hx; apply:big1=>i _; exact:hOff i x hx.
have hSubset:=(@subset_integral_total_supported R X mu A (fun x=>(\sum_i v i x:extended_real_line R))
  (\sum_i a i) hSumOff).2 hSum.
apply:(@subset_integral_total_agreement R X mu A
  (fun x=>(\sum_i v i x:extended_real_line R)) (fun x=>(\sum_i u i x:extended_real_line R))
  (\sum_i a i) _).1 hSubset.
move=>x hx; apply:eq_bigr=>i _; exact:hOn i x hx.
Qed.

(** Source for [subset_nonnegative_extended_scale_integral]:
    supporting the actual intrinsic-volume weights
    in the last integral of Federer 3.2.35,
    p. 272. Nonnegativity is needed only
    on A. Exact support laws transport the
    existing extended constant scaling theorem,
    retaining its zero-times-infinity convention. *)
Lemma subset_nonnegative_extended_scale_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X)
    (u:X->extended_real_line R) a c:
  (forall x,A x ->0<=u x) ->0<=c ->
  is_measure_subset_integral mu A (partial_function_total u) a ->
  is_measure_subset_integral mu A (partial_function_total (fun x=>(c*u x:extended_real_line R))) (c*a).
Proof.
move=>hu hc hi.
pose v (x:X):extended_real_line R:=if pselect (A x) then u x else 0.
have hOn x:A x ->v x=u x.
  move=>hx; rewrite /v; case:(pselect (A x))=>// hn; exfalso; exact:hn hx.
have hOff x:~A x ->v x=0.
  move=>hx; rewrite /v; case:(pselect (A x))=>// hy; exfalso; exact:hx hy.
have hPositive x:0<=v x.
  case:(pselect (A x))=>hx; first by rewrite (hOn x hx); exact:hu.
  by rewrite (hOff x hx).
have hIntegrals:is_measure_integral mu (partial_function_total v) a.
  apply:(@subset_integral_total_supported R X mu A v a hOff).1.
  apply:(@subset_integral_total_agreement R X mu A u v a _).1 hi.
  move=>x hx; exact:Logic.eq_sym (hOn x hx).
have hScale:=@total_nonnegative_extended_scale_integral R X mu hm v a c hPositive hIntegrals hc.
have hScaleOff x:~A x ->c*v x=0 by move=>hx; rewrite (hOff x hx) mule0.
have hSubset:=(@subset_integral_total_supported R X mu A (fun x=>(c*v x:extended_real_line R))
  (c*a) hScaleOff).2 hScale.
apply:(@subset_integral_total_agreement R X mu A (fun x=>(c*v x:extended_real_line R))
  (fun x=>(c*u x:extended_real_line R)) (c*a) _).1 hSubset.
by move=>x hx; rewrite (hOn x hx).
Qed.
