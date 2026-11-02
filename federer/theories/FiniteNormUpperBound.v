(** Federer (1969), 1.10.5, p. 48: supporting finite-dimensional norm
    comparison for positivity and attainment of the mass infimum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom LinearBasis FiniteDualDimension Annihilator
  OrthonormalFamilies OrthonormalParseval InnerProductUP InnerNorm InnerNormInequalities
  RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section UpperBound.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.

(** Source for [finite_seminorm_inner_upper_bound]: Federer 1.10.5,
    p. 48, supporting finite-dimensional comparison. A seminorm
    is bounded by the inner-product norm times the sum of its values
    on an orthonormal basis. The zero-dimensional case is included. *)
Theorem finite_seminorm_inner_upper_bound x :
  N x <= (\sum_i N (e i)) * inner_norm hB x.
Proof.
have hx := @basis_vector_expansion R V n e he x.
have hh := @real_seminorm_sum R V N hN (Finite.clone 'I_n _)
  (fun i => dual_basis he i x *: e i).
rewrite -hx in hh; apply: le_trans hh _.
rewrite mulr_suml; apply: ler_sum=> i _.
rewrite (real_seminorm_scale hN) (@orthonormal_basis_inner_coordinate R V B hB _ e ho he).
have hn : inner_norm hB (e i) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite expr1n ho eqxx.
have hc := inner_cauchy hB x (e i); rewrite hn mulr1 in hc.
rewrite [X in _ <= X]mulrC.
exact (ler_wpM2r (real_seminorm_nonnegative hN (e i)) hc).
Qed.
End UpperBound.
