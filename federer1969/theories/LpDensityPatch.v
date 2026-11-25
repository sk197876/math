(** Federer (1969), 2.5.7, p. 99: improve the candidate density k by adding
    r on the measurable separating set S. These supporting statements use
    characteristic laws and actual conjugate-space products. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP MonotoneDaniellIntegralUP CharacteristicFunctionUP
  SummableRealArithmetic TotalScalarLpUP TotalScalarLpClosure TotalScalarLpCharacteristic
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair LpDominatedDensityFamily LpDensityResidual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_density_patch_pairing]: the decomposition of integral
    f(k+r*s) in Federer 2.5.7, p. 99 Both localized tests remain in L+,
    although the characteristic function itself need not. *)
Lemma lp_density_patch_pairing (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q
    (S : set X) (s f k r : X -> R) :
  is_lp_conjugate_pair p q -> is_characteristic_function S s -> measure_measurable mu S ->
  positive_function_lattice (total_scalar_lp mu p) f ->
  total_scalar_lp mu q k -> total_scalar_lp mu q r ->
  total_scalar_pairing mu f (fun x => (k x+r x*s x)%R)=
    (total_scalar_pairing mu (fun x => (f x*s x)%R) (fun x => (k x+r x)%R)+
      total_scalar_pairing mu (fun x => (f x-f x*s x)%R) k)%R.
Proof.
move=> hpq hs hS hf hk hr.
have [hfs hrest] := @positive_lp_characteristic_pieces R X mu hm p S s f hs hS hf.
have hkr := @total_scalar_lp_add R X mu hm q k r hk hr.
have hi1 := (@total_lp_pairing_specification_and_bound R X mu hm p q _ _ hpq hfs.1 hkr).1.
have hi2 := (@total_lp_pairing_specification_and_bound R X mu hm p q _ k hpq hrest.1 hk).1.
have hi := @real_total_integral_add R X mu hm _ _ _ _ hi1 hi2.
have he : (fun x => ((f x*s x)*(k x+r x)+(f x-f x*s x)*k x)%R)=
    (fun x => (f x*(k x+r x*s x))%R).
  apply: funext=> x.
  rewrite !mulrDr mulrBl.
  rewrite [(_ + _ + (_ - _))%R]addrC addrACA.
  by rewrite addrA addrK mulrAC -mulrA.
rewrite he in hi; exact: (@total_scalar_pairing_value_of_integral R X mu _ _ _ hi).
Qed.

(** Source for [lp_density_patch_admissible]: the improved density k+r*s
    belongs to U in Federer 2.5.7, p. 99 The residual nonnegativity premise
    is precisely the consequence of the separating negative measure, proved
    in SeparatedDaniellValues.v. *)
Theorem lp_density_patch_admissible (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R)
    (S : set X) (s k r : X -> R) :
  is_lp_conjugate_pair p q ->
  is_monotone_daniell_integral (positive_function_lattice (total_scalar_lp mu p)) P ->
  is_characteristic_function S s -> measure_measurable mu S ->
  lp_dominated_density_family mu p q P k -> total_scalar_lp mu q r -> (forall x, (0 <= r x)%R) ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (0 <= lp_density_residual mu P (fun x => (k x+r x)%R) (fun x => (f x*s x)%R))%R) ->
  lp_dominated_density_family mu p q P (fun x => (k x+r x*s x)%R).
Proof.
move=> hpq hP hs hS hk hr hr0 hres.
have hrs := @total_scalar_lp_characteristic_piece R X mu hm q S s r hs hS hr.
split; first exact: (@total_scalar_lp_add R X mu hm q k _ hk.1 hrs).
split.
- move=> x; apply: addr_ge0 (hk.2.1 x) _.
  case: (pselect (S x))=> hx.
  + by rewrite (characteristic_on_set hs hx) mulr1.
  + by rewrite (characteristic_off_set hs hx) mulr0.
- move=> f hf.
  have [hfs hrest] := @positive_lp_characteristic_pieces R X mu hm p S s f hs hS hf.
  have hb1 : (total_scalar_pairing mu (fun x => (f x*s x)%R) (fun x => (k x+r x)%R)
      <= P (fun x => (f x*s x)%R))%R.
    have hh := hres f hf; by rewrite /lp_density_residual subr_ge0 in hh.
  have hb2 := hk.2.2 _ hrest.
  rewrite (@lp_density_patch_pairing R X mu hm p q S s f k r hpq hs hS hf hk.1 hr).
  have hsum := @monotone_daniell_integral_add R X _ P hP _ _ hfs hrest.
  have he : (fun x => (f x*s x+(f x-f x*s x))%R)=f.
    by apply: funext=> x; rewrite addrCA subrr addr0.
  rewrite he in hsum; rewrite hsum; exact: lerD hb1 hb2.
Qed.
