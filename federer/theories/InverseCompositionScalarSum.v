(** Federer (1969), 3.1.24, pp. 239–240: isolate
    the outer-linear term from the scalar inverse composition
    formula, leaving the printed inverse-majorant remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices
  CompositionLinearIndex CompositionLinearMonomial CompositionRemainderFilter
  ScalarForwardMajorantDifferentials InverseMajorantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_composition_scalar_sum]: the normalized
    scalar composition sum for the forward majorant's derivative
    coefficients in Federer 3.1.24, pp. 239–240. The
    supplied lambda contains normalized inner coefficients. *)
Definition inverse_composition_scalar_sum (R:realType) (b g:R) (lambda:nat->R) p:R :=
  \sum_(a:composition_indices p p)
    (symmetric_multi_factorial (composition_indices_unbound a))%:R^-1*
    symmetric_scalar_monomial (fun i:'I_p=>lambda (val i).+1) (composition_indices_unbound a)*
    scalar_forward_majorant_coefficient b g (symmetric_multi_degree (composition_indices_unbound a)).

(** Source for [scalar_forward_majorant_coefficient_higher]:
    the scalar forward majorant has derivative -gamma^m m!
    in every order m>=2, Federer 3.1.24, p. 240.
    This is the evaluation of the already proved coefficient definition. *)
Lemma scalar_forward_majorant_coefficient_higher (R:realType) (b g:R) m :
  (2<=m)%N -> scalar_forward_majorant_coefficient b g m= -(g^+m*(m`!)%:R).
Proof. by case:m=>[|[|m]]. Qed.

(** Source for [inverse_composition_scalar_sum_split]: the
    scalar specialization of the isolated inverse derivative
    in Federer 3.1.24, pp. 239–240. The unique
    outer-linear term is beta*gamma*lambda_p; the sum of
    all remaining terms is minus the inverse-majorant remainder. *)
Theorem inverse_composition_scalar_sum_split (R:realType) (b g:R) (lambda:nat->R) p :
  (1<=p)%N -> inverse_composition_scalar_sum b g lambda p=
    (b*g)*lambda p-inverse_majorant_remainder g lambda p.
Proof.
move=>hp.
have [z hz]:=composition_degree_one_exists hp.
pose term (a:composition_indices p p):R:=
    (symmetric_multi_factorial (composition_indices_unbound a))%:R^-1*
    symmetric_scalar_monomial (fun i:'I_p=>lambda (val i).+1) (composition_indices_unbound a)*
    scalar_forward_majorant_coefficient b g (symmetric_multi_degree (composition_indices_unbound a)).
have hLin:term z=(b*g)*lambda p.
  rewrite /term (composition_degree_one_factorial hz)
    (composition_degree_one_scalar_monomial lambda hz) hz invr1 mul1r
    /scalar_forward_majorant_coefficient.
  exact:mulrC.
have hRest:(\sum_(a:composition_indices p p | a!=z) term a)= -inverse_majorant_remainder g lambda p.
  transitivity (\sum_(a:composition_indices p p |
    (1<symmetric_multi_degree (composition_indices_unbound a))%N) term a).
  - apply:eq_bigl=>a; exact (composition_remainder_filter a hp hz).
  - rewrite /inverse_majorant_remainder -sumrN.
    apply:eq_bigr=>a ha.
    rewrite /term (scalar_forward_majorant_coefficient_higher b g ha) /symmetric_scalar_monomial.
    pose d:=symmetric_multi_degree (composition_indices_unbound a).
    pose A:R:=(symmetric_multi_factorial (composition_indices_unbound a))%:R^-1.
    pose B:R:=\prod_(i<p) lambda (val i).+1^+(composition_indices_unbound a i).
    change ((A*B)*(-(g^+d*(d`!)%:R))= -((g^+d*(d`!)%:R*A)*B)); ring.
change ((\sum_(a:composition_indices p p) term a)=(b*g)*lambda p-inverse_majorant_remainder g lambda p).
rewrite (bigD1 z) // hLin hRest.
reflexivity.
Qed.

(** Source for [inverse_majorant_remainder_one]: the inverse
    remainder vanishes in order one, supporting the initial
    derivative coefficient in Federer 3.1.24, p. 240.
    A composition of weight one cannot have outer degree two. *)
Lemma inverse_majorant_remainder_one (R:realType) (g:R) (lambda:nat->R) :
  inverse_majorant_remainder g lambda 1=0.
Proof.
rewrite /inverse_majorant_remainder; apply:big1=>a ha.
have hh:=composition_indices_outer_degree a.
have hbad:(2<=1)%N:=leq_trans ha hh.
by [].
Qed.
