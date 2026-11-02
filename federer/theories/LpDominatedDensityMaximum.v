(** Federer (1969), 2.5.7, p. 98: U is closed under pointwise maxima, by
    splitting f with the characteristic function of {u>=v}. The
    characteristic map is obtained only through its sealed laws, and all
    four products have actual summable integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  CharacteristicFunctionUP CharacteristicFunctionSealed SummableRealFunctionUP SummableRealArithmetic
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpCharacteristic TotalScalarComparison
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair LpDominatedDensityFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_lp_max_pairing_decomposition]: the displayed
    characteristic-function decomposition in Federer 2.5.7, p. 98 The
    resulting g,h belong to L+ and add to f, without requiring integrable
    constants. *)
Lemma positive_lp_max_pairing_decomposition (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (f u v : X -> R) :
  is_lp_conjugate_pair p q -> positive_function_lattice (total_scalar_lp mu p) f ->
  total_scalar_lp mu q u -> total_scalar_lp mu q v ->
  exists g h, positive_function_lattice (total_scalar_lp mu p) g /\
    positive_function_lattice (total_scalar_lp mu p) h /\
    (fun x => (g x+h x)%R)=f /\
    total_scalar_pairing mu f (fun x => Order.max (u x) (v x))=
      (total_scalar_pairing mu g u+total_scalar_pairing mu h v)%R.
Proof.
move=> hpq hf hu hv.
pose E := [set x | (v x <= u x)%R].
pose s := @CharacteristicFunction.value R X E.
have hs : is_characteristic_function E s := @CharacteristicFunction.laws R X E.
have hE := @total_scalar_measurable_comparison R X mu hm v u hv.2.1 hu.2.1.
pose g x := (f x*s x)%R.
pose h x := (f x-f x*s x)%R.
have [hg hh] := @positive_lp_characteristic_pieces R X mu hm p E s f hs hE hf.
exists g,h; split; first exact: hg.
split; first exact: hh.
split.
- by apply: funext=> x; rewrite /g /h addrCA subrr addr0.
- apply: total_scalar_pairing_value_of_integral.
  have hgi := (@total_lp_pairing_specification_and_bound R X mu hm p q g u hpq hg.1 hu).1.
  have hhi := (@total_lp_pairing_specification_and_bound R X mu hm p q h v hpq hh.1 hv).1.
  have hi := @real_total_integral_add R X mu hm _ _ _ _ hgi hhi.
  have he : (fun x => (g x*u x+h x*v x)%R)=(fun x => (f x*Order.max (u x) (v x))%R).
    apply: funext=> x; case: (pselect (E x))=> hx.
    + have hle : (v x <= u x)%R := hx.
      by rewrite /g /h (characteristic_on_set hs hx) mulr1 subrr mul0r addr0 max_l.
    + have hlt : (u x < v x)%R.
        rewrite ltNge; apply/negP=> hle; exact: hx hle.
      by rewrite /g /h (characteristic_off_set hs hx) mulr0 subr0 mul0r add0r max_r ?ltW.
  by rewrite he in hi.
Qed.

(** Source for [lp_dominated_density_maximum]: complete maximum closure of U
    in Federer 2.5.7, p. 98 Only the abstract positive functional laws and
    the proved conjugate-space pairings are used. *)
Theorem lp_dominated_density_maximum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R) (u v : X -> R) :
  is_lp_conjugate_pair p q -> is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  lp_dominated_density_family mu p q P u -> lp_dominated_density_family mu p q P v ->
  lp_dominated_density_family mu p q P (fun x => Order.max (u x) (v x)).
Proof.
move=> hpq hP hu hv; split.
- exact: (@function_lattice_maximum R X (total_scalar_lp mu q)
    (@total_scalar_lp_vector_lattice R X mu hm q (lp_conjugate_pair_admissible hpq).2).1 u v hu.1 hv.1).
- split.
  + move=> x; rewrite le_max; apply/orP; left; exact: hu.2.1 x.
  + move=> f hf.
    have [g [h [hg [hh [he hpair]]]]] := @positive_lp_max_pairing_decomposition R X mu hm p q f u v hpq hf hu.1 hv.1.
    rewrite hpair.
    have hsum := @monotone_daniell_integral_add R X (positive_function_lattice (total_scalar_lp mu p)) P hP g h hg hh.
    rewrite he in hsum; rewrite hsum.
    exact: lerD (hu.2.2 g hg) (hv.2.2 h hh).
Qed.
