(** Federer (1969), 2.5.7, p. 99: subtract the two nonnegative densities and
    extend the representation from L+ to L. The product integrals below are
    summable by the already proved conjugate-space estimates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP SummableRealFunctionUP FunctionLatticeSeminormUP VectorFunctionLattice
  TotalScalarLpUP TotalScalarLpLattice TotalScalarPairingValue TotalLpPairingBound LpConjugatePair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_lp_pairing_linear]: linearity of the represented
    functional in Federer 2.5.7, p. 99 *)
Theorem total_lp_pairing_linear (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (k : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu q k ->
  is_linear_functional_on_functions (total_scalar_lp mu p) (fun f => total_scalar_pairing mu f k).
Proof.
move=> hpq hk.
have hs f : total_scalar_lp mu p f -> summable_real_functions mu (fun x => (f x*k x)%R).
  move=> hf; exists (total_scalar_pairing mu f k).
  exact: (@total_lp_pairing_specification_and_bound R X mu hm p q f k hpq hf hk).1.
split.
- move=> f g hf hg; exact: (@total_scalar_pairing_add_left R X mu hm f g k (hs f hf) (hs g hg)).
- move=> c f hf; exact: (@total_scalar_pairing_scale_left R X mu hm f k c (hs f hf)).
Qed.

(** Source for [total_lp_pairing_subtract_test]: subtracting positive and
    negative parts in Federer 2.5.7, p. 99 This is the full difference
    identity on the total Lp space. *)
Lemma total_lp_pairing_subtract_test (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (f g k : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p f -> total_scalar_lp mu p g -> total_scalar_lp mu q k ->
  total_scalar_pairing mu (fun x => (f x-g x)%R) k=
    (total_scalar_pairing mu f k-total_scalar_pairing mu g k)%R.
Proof.
move=> hpq hf hg hk.
exact: (@vector_lattice_additive_difference R X (total_scalar_lp mu p)
  (fun f => total_scalar_pairing mu f k)
  (@total_scalar_lp_vector_lattice R X mu hm p (lp_conjugate_pair_admissible hpq).1)
  (@total_lp_pairing_linear R X mu hm p q k hpq hk).1 f g hf hg).
Qed.

(** Source for [total_lp_pairing_subtract_density]: k=k+-k- in Federer
    2.5.7, p. 99 Both density factors belong to the conjugate space. *)
Lemma total_lp_pairing_subtract_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (f k l : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p f -> total_scalar_lp mu q k -> total_scalar_lp mu q l ->
  total_scalar_pairing mu f (fun x => (k x-l x)%R)=
    (total_scalar_pairing mu f k-total_scalar_pairing mu f l)%R.
Proof.
move=> hpq hf hk hl.
rewrite [total_scalar_pairing mu f _]total_scalar_pairing_commute
  (@total_lp_pairing_subtract_test R X mu hm q p k l f (lp_conjugate_pair_symmetric hpq) hk hl hf).
by rewrite [total_scalar_pairing mu k f]total_scalar_pairing_commute
  [total_scalar_pairing mu l f]total_scalar_pairing_commute.
Qed.
