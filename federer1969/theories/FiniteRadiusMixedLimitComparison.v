(** Federer (1969), 3.2.39, p. 276: one upper
    radius limit and the remaining lower radius limits compare
    with the finite sum of component upper limits. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal ring.
From Federer Require Import PositiveRadiusLimits PositiveRadiusLimitBounds PositiveRadiusFiniteApproximation
  FinitePositiveRadiusCutoff ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_radius_mixed_limit_comparison]: the
    display obtained after integration and radius division in
    Federer 3.2.39, p. 276. Actual full positive-real-radius
    limits and finite scalar upper/lower bounds suffice. Every
    cancellation is by a finite scalar. The distinguished
    function need not be known finite in advance, and either
    auxiliary finite index type may be empty. *)
Lemma finite_radius_mixed_limit_comparison (R:realType) (I J:finType)
    (f:R->\bar R) (g:I->R->\bar R) (h:J->R->\bar R) (a:J->R) (b:I->R):
  (forall j,(positive_radius_upper_limit (h j)<=(a j)%:E)%E) ->
  (forall i,((b i)%:E<=positive_radius_lower_limit (g i))%E) ->
  (forall r:R,0<r ->(f r+(\sum_i g i r)<=(\sum_j h j r))%E) ->
  (positive_radius_upper_limit f<=((\sum_j a j)-(\sum_i b i))%R%:E)%E.
Proof.
move=>hUpper hLower hPoint.
pose p:=(\sum_j a j)-(\sum_i b i).
pose K:R:=(#|I|+#|J|)%:R.
have hK:0<=K by rewrite /K ler0n.
apply:(@extended_upper_bound_from_scaled_errors R _ p K hK)=>e he.
have [dH [hdH hH]]:=@finite_common_positive_radius_bound R J
  (fun j r=>(h j r<=(a j+e)%R%:E)%E)
  (fun j=>@positive_radius_upper_finite_approximation R (h j) (a j) e (hUpper j) he).
have [dG [hdG hG]]:=@finite_common_positive_radius_bound R I
  (fun i r=>((b i-e)%R%:E<=g i r)%E)
  (fun i=>@positive_radius_lower_finite_approximation R (g i) (b i) e (hLower i) he).
have hCutoff:0<Num.min dH dG by rewrite lt_min hdH hdG.
apply:(@positive_radius_upper_eventual_bound R f (p+K*e)%R%:E (Num.min dH dG) hCutoff).
move=>r /andP[hr hSmall].
have hrH:0<r<dH.
  apply/andP; split=>//; apply:lt_le_trans hSmall _; by rewrite ge_min lexx.
have hrG:0<r<dG.
  apply/andP; split=>//; apply:lt_le_trans hSmall _; by rewrite ge_min lexx orbT.
have hSumH:(\sum_j h j r<=\sum_j (a j+e)%R%:E)%E.
  apply:lee_sum=>j _; exact:hH r hrH j.
have hSumG:(\sum_i (b i-e)%R%:E<=\sum_i g i r)%E.
  apply:lee_sum=>i _; exact:hG r hrG i.
have hRaw:=le_trans (leeD (lexx (f r)) hSumG) (le_trans (hPoint r hr) hSumH).
rewrite !sumEFin in hRaw.
have hDifference:(f r<=((\sum_j (a j+e))-(\sum_i (b i-e)))%R%:E)%E.
  rewrite EFinB leeBrDr; first exact hRaw.
  by rewrite fin_numE.
have hConstI:(\sum_(i:I) e)=(#|I|)%:R*e.
  rewrite sumr_const cardT; exact:esym (mulr_natl e _).
have hConstJ:(\sum_(j:J) e)=(#|J|)%:R*e.
  rewrite sumr_const cardT; exact:esym (mulr_natl e _).
have hAlgebra:(\sum_j (a j+e))-(\sum_i (b i-e))=p+K*e.
  rewrite big_split sumrB hConstI hConstJ /p /K natrD.
  change (((\sum_j a j)+(#|J|)%:R*e)-((\sum_i b i)-(#|I|)%:R*e)=
    (\sum_j a j)-(\sum_i b i)+((#|I|)%:R+(#|J|)%:R)*e).
  ring.
by rewrite hAlgebra in hDifference.
Qed.
