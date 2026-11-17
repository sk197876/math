(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the degree-bounded part of a polynomial
    ideal is a finite module over the coefficient ring.
    This expands the coefficient proof of Hilbert's theorem;
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 2, no. 10, Corollary 1, p. 184. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP
  CommutativePolynomialFiniteSums PolynomialCoefficientDivision
  RingScalarRestriction RingSubmoduleUP RingIdealModules RingFiniteSynthesis
  NoetherianModuleUP NoetherianFiniteFreeModule NoetherianLinearCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BoundedIdeal.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable I:set B.
Hypothesis hI:is_commutative_ideal I.
Variable N:nat.
Local Notation V:=[the lmodType A of (ring_restricted_space embed B^o)].
Local Notation M:=([set P:V|I P /\forall i,(N<=i)%N ->coefficient P i = 0]).

(** Source for [bounded_polynomial_ideal_submodule]: bounded
    polynomials in the original ideal form a coefficient
    submodule, supporting Hilbert's theorem; Bourbaki (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184,
    for the expanded algebra of 3.4.8(5), p. 328. *)
Lemma bounded_polynomial_ideal_submodule:is_ring_submodule M.
Proof.
constructor.
- split;first exact:commutative_ideal_zero hI.
  by move=>i _;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP i).
- move=>P Q [hIP hPHigh] [hIQ hQHigh];split.
  + exact:(@commutative_ideal_add B I hI P Q hIP hIQ).
  + move=>i hi;by rewrite (@polynomial_coefficient_add A B embed variable coefficient hP)
      hPHigh // hQHigh // addr0.
- move=>P [hIP hPHigh];split.
  + exact:(@commutative_ideal_opp B I hI P hIP).
  + move=>i hi;by rewrite (@polynomial_coefficient_opp A B embed variable coefficient hP) hPHigh // oppr0.
- move=>a P [hIP hPHigh];change (I (embed a*P) /\forall i,(N<=i)%N ->coefficient (embed a*P) i = 0).
  split.
  + exact:(@commutative_ideal_mul B I hI (embed a) P hIP).
  + move=>i hi;by rewrite (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP)
      hPHigh // mulr0.
Qed.

(** Source for [bounded_polynomial_ideal_finitely_generated]:
    the actual degree-bounded ideal part has finite coefficient
    generators, supporting Hilbert's theorem; Bourbaki (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184,
    for the expanded algebra of 3.4.8(5), p. 328. *)
Theorem bounded_polynomial_ideal_finitely_generated:
  is_noetherian_commutative_ring A ->is_finitely_generated_ring_submodule M.
Proof.
move=>hNoetherian.
pose e (i:'I_N):V:=variable^+i.
pose synthesis:=GRing.Linear.clone _ _ _ _ (@ring_finite_synthesis A V N e) _.
apply:(@noetherian_module_linear_cover A [the lmodType A of {ffun 'I_N->A^o}] V
  synthesis M (@noetherian_finite_free_module A hNoetherian N) bounded_polynomial_ideal_submodule).
move=>P [hIP hPHigh];exists [ffun i:'I_N=>coefficient P i].
change ((\sum_(i<N) embed ([ffun j:'I_N=>coefficient P j] i)*variable^+i) = P).
under eq_bigr do rewrite ffunE.
exact:esym (@polynomial_finite_expression A B embed variable coefficient hP P N hPHigh).
Qed.
End BoundedIdeal.
