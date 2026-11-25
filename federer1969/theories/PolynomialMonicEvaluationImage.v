(** Federer (1969), 3.4.8(8), p. 329:
    a monic annihilating polynomial makes the original
    simple algebra a finite coefficient module. Apply
    the existing monic-division theorem and the proved
    finite generation of bounded polynomial images. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP CommutativePolynomialUP
  CommutativePolynomialBasicLaws CommutativePolynomialDegreeUP CommutativePolynomialEvaluationUP
  PolynomialMonicDivision PolynomialBoundedImageGeneration RingScalarRestriction RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Image.
Variables A B C:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Hypothesis hDomain:is_commutative_integral_domain A.
Variable phi:{rmorphism A->C}.
Variable t:C.
Variable E:{rmorphism B->C}.
Hypothesis hE:is_commutative_polynomial_evaluation embed variable phi t E.
Variables (H:B) (k:nat).
Hypothesis hDegree:is_polynomial_degree coefficient H k.
Hypothesis hMonic:coefficient H k = 1.
Hypothesis hZero:E H = 0.
Local Notation V:=[the lmodType A of (ring_restricted_space phi C^o)].

(** Source for [monic_polynomial_evaluation_bounded_image]:
    reduce each original polynomial modulo the monic
    annihilator, retaining its exact quotient value;
    this is the finite-extension step in 3.4.8(8),
    p. 329. Reuse monic division from 3.4.7. *)
Theorem monic_polynomial_evaluation_bounded_image (x:C):
  (exists P:B,x = E P) <->exists r:B,
    (forall i,(k<=i)%N ->coefficient r i = 0) /\x = E r.
Proof.
split.
- move=>[P ->].
  have [q [r [hDivision hRemainder]]]:=@polynomial_monic_division A B embed variable coefficient
    hP hDomain H k hDegree hMonic P.
  exists r;split.
  + case:hRemainder=>[->|[d [hDK hDR]]].
    * move=>i _;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP i).
    * move=>i hi;exact:hDR.2 i (leq_trans hDK hi).
  + by rewrite hDivision rmorphD rmorphM hZero mulr0 add0r.
- move=>[r [_ hR]];by exists r.
Qed.

(** Source for [monic_polynomial_evaluation_finite_module]:
    the original simple extension has a finite
    coefficient module, 3.4.8(8), p. 329. The
    existing bounded-image theorem supplies its generators. *)
Theorem monic_polynomial_evaluation_finite_module:
  is_finitely_generated_ring_submodule (fun x:V=>exists P:B,x = E P).
Proof.
have hSets:(fun x:V=>exists P:B,x = E P) =
    (fun x:V=>exists r:B,(forall i,(k<=i)%N ->coefficient r i = 0) /\x = E r).
  apply:funext=>x;apply:propext;exact:monic_polynomial_evaluation_bounded_image.
rewrite hSets.
exact:(@bounded_polynomial_image_finite A B C embed variable coefficient hP phi t E hE k).
Qed.
End Image.
