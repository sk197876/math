(** Federer (1969), 3.4.5, p. 321: the
    finite convolution with the three actual surface-equation
    coefficients, supporting the real remainder argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import FlatExponentialSealed CartanEquationMixedCoefficients FiniteRectangularDeltaSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [cartan_sparse_coefficient_convolution]: multiplication
    by the actual original equation has precisely the two
    quadratic shifts and the cubic shift of the original
    divided coefficient array, supporting 3.4.5, p. 321.
    Every finite order, including zero, is retained. *)
Theorem cartan_sparse_coefficient_convolution (R:realType) (a:nat->nat->R) i j (z:R):
  (\sum_(r<i.+1) \sum_(s<j.+1) a (i-r)%N (j-s)%N*cartan_surface_mixed_coefficient r s z)=
    z*(if (2<=i)%N then a (i-2)%N j else 0)+
    z*(if (2<=j)%N then a i (j-2)%N else 0)-
    FlatExponential.value (1-z)*(if (3<=i)%N then a (i-3)%N j else 0).
Proof.
have hSelect (u v:nat) (b:R):
    (\sum_(r<i.+1) \sum_(s<j.+1) a (i-r)%N (j-s)%N*
      (if (((r:nat)==u)&&((s:nat)==v))%N then b else 0))=
    if ((u<=i)&&(v<=j))%N then a (i-u)%N (j-v)%N*b else 0.
  have hRewrite:(\sum_(r<i.+1) \sum_(s<j.+1) a (i-r)%N (j-s)%N*
      (if (((r:nat)==u)&&((s:nat)==v))%N then b else 0))=
      \sum_(r<i.+1) \sum_(s<j.+1) if (((r:nat)==u)&&((s:nat)==v))%N
        then a (i-r)%N (j-s)%N*b else 0.
    apply:eq_bigr=>r _;apply:eq_bigr=>s _.
    by case:((((r:nat)==u)&&((s:nat)==v))%N);rewrite ?mulr0.
  rewrite hRewrite (@finite_rectangular_delta_sum R^o i.+1 j.+1 u v
    (fun r s=>a (i-r)%N (j-s)%N*b)) !ltnS.
  by [].
have hPoint (r:'I_i.+1):
    (\sum_(s<j.+1) a (i-r)%N (j-s)%N*cartan_surface_mixed_coefficient r s z)=
    (\sum_(s<j.+1) a (i-r)%N (j-s)%N*(if (((r:nat)==2)&&((s:nat)==0))%N then z else 0))+
    (\sum_(s<j.+1) a (i-r)%N (j-s)%N*(if (((r:nat)==0)&&((s:nat)==2))%N then z else 0))-
    (\sum_(s<j.+1) a (i-r)%N (j-s)%N*(if (((r:nat)==3)&&((s:nat)==0))%N then FlatExponential.value (1-z) else 0)).
  under eq_bigr do rewrite /cartan_surface_mixed_coefficient mulrBr mulrDr.
  by rewrite sumrB big_split.
under eq_bigr do rewrite hPoint.
rewrite sumrB big_split (hSelect 2%N 0%N z) (hSelect 0%N 2%N z)
  (hSelect 3%N 0%N (FlatExponential.value (1-z))) !leq0n ?andbT ?andTb !subn0.
change ((if (2<=i)%N then a (i-2)%N j*z else 0)+
  (if (2<=j)%N then a i (j-2)%N*z else 0)-
  (if (3<=i)%N then a (i-3)%N j*FlatExponential.value (1-z) else 0)=
  z*(if (2<=i)%N then a (i-2)%N j else 0)+
  z*(if (2<=j)%N then a i (j-2)%N else 0)-
  FlatExponential.value (1-z)*(if (3<=i)%N then a (i-3)%N j else 0)).
by case:(2<=i)%N;case:(2<=j)%N;case:(3<=i)%N;ring.
Qed.
