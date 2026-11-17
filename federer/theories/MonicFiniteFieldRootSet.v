(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    an original monic degree-k polynomial
    has at most k distinct roots over the original field.
    Apply the project's synthetic-division root
    count from 1.10.4, p. 46,
    and its finite-root-set connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals.
From Federer Require Import PolynomialCoefficientUniqueness PolynomialFiniteRoots.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [monic_finite_field_root_set]:
    the root bound giving the fibre
    numbers nu=0,...,k in 3.4.8(10),
    p. 332. The leading coefficient
    is the actual one; no root-counting
    conclusion is supplied as a premise. *)
Theorem monic_finite_field_root_set (R:fieldType) k (b:'I_k.+1->R):
  b ord_max = 1 ->
  finite_set [set t:R|\sum_(i<k.+1) b i*t^+(i:nat) = 0] /\
  forall roots:seq R,uniq roots ->
    (forall t,t \in roots ->\sum_(i<k.+1) b i*t^+(i:nat) = 0) ->
    (size roots<=k)%N.
Proof.
move=>hLeading.
pose s:=map b (enum 'I_k.+1).
have hValue t:@coefficient_polynomial_value R R^o s t = \sum_(i<k.+1) b i*t^+(i:nat).
  rewrite coefficient_polynomial_sum /s size_map size_enum_ord.
  apply:eq_bigr=>i _.
  rewrite (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
  exact:mulrC.
have hNonzero:~~all (pred1 (0:R)) s.
  apply/negP=>/allP hAll.
  have hMember:b ord_max \in s.
    apply/mapP;exists (@ord_max k);first by rewrite mem_enum.
    by [].
  have hZero:b ord_max = 0:=eqP (hAll _ hMember).
  have hOneZero:(1:R) = 0 by rewrite -hLeading.
  have hNot:(1:R)!=0 by rewrite oner_eq0.
  by rewrite hOneZero eqxx in hNot.
split.
- have hSet:[set t:R|\sum_(i<k.+1) b i*t^+(i:nat) = 0] =
      [set t:R|@coefficient_polynomial_value R R^o s t = 0].
    apply/seteqP;split=>t ht.
    - change (@coefficient_polynomial_value R R^o s t = 0);by rewrite hValue.
    - change (\sum_(i<k.+1) b i*t^+(i:nat) = 0);by rewrite -hValue.
  rewrite hSet;exact:(@coefficient_polynomial_finitely_many_roots R R^o s hNonzero).
- move=>roots hUniq hRoots;rewrite leqNgt;apply/negP=>hSize.
  have hCoefficients:(size s<=size roots)%N by rewrite /s size_map size_enum_ord.
  have hZero:=@coefficient_polynomial_roots R R^o (size roots) s roots hCoefficients
    (erefl _) hUniq (fun t ht=>ltac:(by rewrite hValue;exact:hRoots t ht)).
  by move:hNonzero;rewrite hZero.
Qed.
