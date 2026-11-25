(** Federer (1969), 4.1.24, p. 382: the
    original mass triangle bound on finite-mass terms,
    as used to add integral-flat decomposition costs.
    This is the real-value form of the already
    proved finite mass linear bound. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentMassBasic CurrentFiniteMassLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_finite_mass_triangle]: the original
    mass of a sum is bounded by the sum
    of masses, supporting the integral-flat subadditivity
    in 4.1.24, p. 382. No density or
    representation is required from the caller. *)
Theorem current_finite_mass_triangle (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T S:@current_space R h2 n U hU m):
  (@CurrentMass.value R h2 n m U hU T< +oo)%E->
  (@CurrentMass.value R h2 n m U hU S< +oo)%E->
  (@CurrentMass.value R h2 n m U hU (T+S)<=
    @CurrentMass.value R h2 n m U hU T+
    @CurrentMass.value R h2 n m U hU S)%E.
Proof.
move=>hT hS.
have[a [ha hA]]:=@current_finite_mass_value R h2 n m U hU T hT.
have[b [hb hB]]:=@current_finite_mass_value R h2 n m U hU S hS.
have hTA:(@CurrentMass.value R h2 n m U hU T<=a%:E)%E by rewrite hA.
have hSB:(@CurrentMass.value R h2 n m U hU S<=b%:E)%E by rewrite hB.
have hBound:=@current_finite_mass_linear_bound R h2 n m U hU 1 T S a b hTA hSB.
rewrite scale1r normr1 mul1r in hBound.
by rewrite hA hB -EFinD.
Qed.
