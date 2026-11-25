(** Federer (1969), 4.1.12, pp. 367–369: the
    original mass bounds real linear combinations. This
    quantitative form of the earlier finite-mass closure
    follows from the same actual unit-comass test
    supremum and absolute-action estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed CurrentMassUP
  CurrentMassFiniteAlgebra ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFiniteMassLinearBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:(R_n R n)->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_finite_mass_linear_bound]:
    M(c S+T)<=|c| a+b when M(S)<=a and M(T)<=b,
    supporting the mass-minimum and product estimates
    of Federer 4.1.12, pp. 367–369. The
    upper bounds may be zero. *)
Theorem current_finite_mass_linear_bound c (S T:C) a b:
  (M S<=a%:E)%E->(M T<=b%:E)%E->
    (M ((c*:S+T)%R)<=(`|c| * a+b)%:E)%E.
Proof.
move=>hS hT.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n m U hU (c*:S+T)))=>z [phi [hPhi <-]].
have hSB:=le_trans (@current_mass_unit_absolute R h2 n m U hU S phi hPhi) hS.
have hTB:=le_trans (@current_mass_unit_absolute R h2 n m U hU T phi hPhi) hT.
rewrite lee_fin in hSB hTB.
rewrite (linearP action) hom_addE hom_scaleE lee_fin.
apply:(le_trans (lerD (ler_norm (c * action S phi)) (ler_norm (action T phi)))).
rewrite normrM;exact:lerD (ler_wpM2l (normr_ge0 c) hSB) hTB.
Qed.

(** Source for [current_finite_mass_scale_bound]:
    M(c S)<=|c| a for M(S)<=a, supporting
    signed fillings in Federer 4.1.12, p. 369.
    This is the preceding bound with zero second term. *)
Corollary current_finite_mass_scale_bound c (S:C) a:
  (M S<=a%:E)%E->(M ((c*:S)%R)<=(`|c| * a)%:E)%E.
Proof.
move=>hS.
have hZero:(M (0:C)<=(0:R)%:E)%E by rewrite current_mass_zero.
have h:=current_finite_mass_linear_bound c hS hZero.
by rewrite addr0 addr0 in h.
Qed.
End CurrentFiniteMassLinearBound.
