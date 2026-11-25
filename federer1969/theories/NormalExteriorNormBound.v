(** Norm comparison of the three products in Federer (1969), 2.10.32, p.
    197. Apply the proved algebraic double-difference identity and the real
    seminorm triangle law to the actual induced exterior norm. The common
    original-product bound is left explicit; Federer's erratum p. 4, book p.
    197 line 4, corrects its value to mu alpha(m)^(-1) 2^m when the
    normalised exterior diameter is at most mu. This algebraic helper does
    not silently identify that norm bound with the normalised cost. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerExteriorPositivity
  OrthonormalFamilies LinearBasis ExteriorGrading FiniteExteriorPowers ExteriorNorm ExteriorDiameterUP
  RealNormUP DoubleDifferenceSeminorm NormalExteriorDoubleDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normal_exterior_parallel_shift_norm_bound]: direct
    norm estimate after the half-difference identity
    in 2.10.32, p. 197. Its bound M
    is the unnormalised endpoint-product bound;
    conversion from the cost uses the corrected
    factor in the cited erratum entry. *)
Theorem normal_exterior_parallel_shift_norm_bound (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (n : nat) (e v : 'I_n -> V) (a g : 'I_n -> R) (u : V) (M : R) :
  let N := @exterior_norm R (real_exterior_two_nonzero R) V B hB n in
  is_basis e -> B u u= 1 -> (forall i, inner_coordinate hB u (v i)=0) ->
  N (e_lambda (fun i=>v i+(g i+2*a i)*:u) (ord_tuple n))<=M ->
  N (e_lambda (fun i=>v i+g i*:u) (ord_tuple n))<=M ->
  N (e_lambda (fun i=>v i+a i*:u) (ord_tuple n))<=M.
Proof.
move=> N he hu hv hfirst hsecond.
have hN : is_real_seminorm N.
  split.
  - exact: exterior_norm_nonnegative.
  - by move=> c x; exact: exterior_norm_scale.
  - move=> x y.
    exact (@inner_norm_triangle R _ _
      (@exterior_inner_productP R (real_exterior_two_nonzero R) V B hB n) x y).
have hd := @normal_exterior_double_difference R V B hB n e v a g u he hu hv.
exact (double_difference_seminorm_bound hN (esym hd) hfirst hsecond).
Qed.
