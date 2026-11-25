(** Federer (1969), 3.4.8(8), p. 329:
    the finite polynomial remainders generate a finite
    module over the original coefficient ring. Reuse
    the proved bounded-image submodule and exact
    finite-evaluation equations from 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP RingFiniteSynthesis
  CommutativePolynomialUP CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws
  PolynomialBoundedEvaluationModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Generation.
Variables A B C:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable phi:{rmorphism A->C}.
Variable t:C.
Variable E:{rmorphism B->C}.
Hypothesis hE:is_commutative_polynomial_evaluation embed variable phi t E.
Variable k:nat.
Local Notation V:=[the lmodType A of (ring_restricted_space phi C^o)].
Local Notation M:=(fun x:V=>exists P:B,(forall i,(k<=i)%N ->coefficient P i = 0) /\x = E P).

(** Source for [bounded_polynomial_image_generated]: the
    original bounded polynomial image is generated
    by 1,t,...,t^(k-1), supporting the finite
    extension in 3.4.8(8), p. 329. *)
Theorem bounded_polynomial_image_generated:
  is_generated_ring_submodule
    [set x:V|x \in map (fun i:'I_k=>(t^+(i:nat):V)) (enum 'I_k)] M.
Proof.
constructor.
- exact:(@bounded_polynomial_image_submodule A B C embed variable coefficient hP phi t E hE k).
- move=>x /mapP [i _ ->].
  exact:(@bounded_polynomial_image_contains_power A B C embed variable coefficient hP phi t E hE k i (ltn_ord i)).
- move=>N hN hPowers x [P [hSupport ->]].
  rewrite (@polynomial_evaluation_finite_expression A B C embed variable coefficient hP phi t E hE P k hSupport).
  have hGenerators (i:'I_k):N (t^+(i:nat)).
    apply:hPowers;apply/mapP;exists i;last by [].
    exact:mem_enum.
  have hSum:=@ring_submodule_finite_sum A V N hN k
    (fun i:'I_k=>(t^+(i:nat):V)) [ffun i:'I_k=>coefficient P i] hGenerators.
  change (N (\sum_(i<k) phi ([ffun j:'I_k=>coefficient P j] i)*t^+(i:nat))) in hSum.
  have hEqual:(\sum_(i<k) phi ([ffun j:'I_k=>coefficient P j] i)*t^+(i:nat)) =
      \sum_(i<k) phi (coefficient P i)*t^+(i:nat).
    apply:eq_bigr=>i _;by rewrite ffunE.
  by rewrite -hEqual.
Qed.

(** Source for [bounded_polynomial_image_finite]: the
    original remainder module has finitely many
    generators, supporting 3.4.8(8), p. 329. *)
Theorem bounded_polynomial_image_finite:is_finitely_generated_ring_submodule M.
Proof. exists (map (fun i:'I_k=>(t^+(i:nat):V)) (enum 'I_k));exact:bounded_polynomial_image_generated. Qed.
End Generation.
