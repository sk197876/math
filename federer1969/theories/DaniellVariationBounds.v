(** Consequences of the abstract variation specifications in Federer (1969),
    2.5.5, pp. 96–97 These proofs use only least-upper-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP
  DaniellIntegralAlgebra DaniellVariationUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_positive_variation_upper]: every mu(k) with 0 <= k
    <= f is below mu+(f), Federer 2.5.5, p. 96 *)
Lemma daniell_positive_variation_upper (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f k : X -> R) :
  positive_function_lattice L f -> lattice_positive_order_interval L f k -> A k <= P f.
Proof.
move=> hf hk; have hh : ((A k)%:E <= (P f)%:E)%E.
  apply: (@extended_real_supremum_upper R _ _ (hP f hf)).
  by exists k.
by move: hh; rewrite lee_fin.
Qed.

(** Source for [daniell_positive_variation_least]: least-upper-bound
    consequence of the first formula in Federer 2.5.5, p. 96 *)
Lemma daniell_positive_variation_least (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) (b : R) :
  positive_function_lattice L f ->
  (forall k, lattice_positive_order_interval L f k -> A k <= b) -> P f <= b.
Proof.
move=> hf hb; have hh : ((P f)%:E <= b%:E)%E.
  apply: (@extended_real_supremum_least R _ _ (hP f hf)).
  move=> v [k [hk ->]]; rewrite lee_fin; exact: hb k hk.
by move: hh; rewrite lee_fin.
Qed.

(** Source for [daniell_positive_variation_nonnegative]: positivity of mu+
    in Federer 2.5.5, p. 97 *)
Lemma daniell_positive_variation_nonnegative (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) :
  positive_function_lattice L f -> 0 <= P f.
Proof.
move=> hf.
rewrite -(@daniell_integral_zero R X L A hA f hf.1).
apply: (@daniell_positive_variation_upper R X L A P hP f (fun _ => 0) hf).
split; first exact: (@function_lattice_zero R X L hL f hf.1).
split; [by move=> x; exact: lexx|exact: hf.2].
Qed.

(** Source for [daniell_positive_variation_dominates]: mu(f) is one of the
    values defining mu+(f), Federer 2.5.5, p. 96 *)
Lemma daniell_positive_variation_dominates (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f : X -> R) :
  positive_function_lattice L f -> A f <= P f.
Proof.
move=> hf; apply: (@daniell_positive_variation_upper R X L A P hP f f hf).
split; first exact: hf.1.
split; first exact: hf.2.
by move=> x; exact: lexx.
Qed.

(** Source for [daniell_positive_variation_monotone]: order preservation of
    mu+ in Federer 2.5.5, p. 97 Inclusion of the admissible intervals is
    sufficient; mu need not preserve order. *)
Lemma daniell_positive_variation_monotone (R : realType) (X : Type)
    (L : set (X -> R)) (A P : (X -> R) -> R)
    (hP : is_daniell_positive_variation L A P) (f g : X -> R) :
  positive_function_lattice L f -> positive_function_lattice L g ->
  function_le f g -> P f <= P g.
Proof.
move=> hf hg hfg; apply: (@daniell_positive_variation_least R X L A P hP f (P g) hf).
move=> k [hk [hk0 hkf]]; apply: (@daniell_positive_variation_upper R X L A P hP g k hg).
split; first exact: hk.
split; first exact: hk0.
move=> x; exact: le_trans (hkf x) (hfg x).
Qed.

(** Source for [daniell_positive_negative_identity]: exact identity
    mu(f)=mu+(f)-mu-(f) for positive f in Federer 2.5.5, p. 96, final proof
    display Only the ordered-difference lattice law is needed. *)
Theorem daniell_positive_negative_identity (R : realType) (X : Type)
    (L : set (X -> R)) (A P Q : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P)
    (hQ : is_daniell_negative_variation L A Q) (f : X -> R) :
  positive_function_lattice L f -> A f= P f-Q f.
Proof.
move=> hf.
have hQb : Q f <= P f-A f.
  apply: (@daniell_positive_variation_least R X L (fun k => - A k) Q hQ f _ hf).
  exact: (@daniell_integral_negative_order_bound R X L A hL hA f (P f) hf.1
    (fun k hk => @daniell_positive_variation_upper R X L A P hP f k hf hk)).
have hPb : P f <= A f+Q f.
  apply: (@daniell_positive_variation_least R X L A P hP f _ hf)=> k hk.
  have hd := @lattice_positive_order_interval_complement R X L hL f k hf.1 hk.
  have hb := @daniell_positive_variation_upper R X L (fun k => - A k) Q hQ f _ hf hd.
  rewrite (@daniell_integral_ordered_difference R X L A hL hA f k hf.1 hk.1 hk.2.2) opprB in hb.
  by rewrite lerBlDr addrC in hb.
apply/eqP; rewrite eq_le; apply/andP; split.
- by rewrite lerBrDr addrC -lerBrDr.
- by rewrite lerBlDr.
Qed.
