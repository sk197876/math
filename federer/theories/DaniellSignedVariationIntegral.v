(** Federer (1969), 2.5.5, p. 96: the signed representation formula is
    asserted for every f in L, not only for positive f. All component
    integrals are finite, so no infinite difference is formed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellIntegralAlgebra
  DaniellVariationUP DaniellVariationBounds RealIntegralFunctionalUP SummableRealFunctionUP SummableRealArithmetic
  MeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_lattice_representation_signed_integral]: supporting
    extension from positive parts for the all-L formula in Federer 2.5.5, p.
    96; compare 2.5.2, p. 93. *)
Lemma positive_lattice_representation_signed_integral (R : realType) (X : choiceType)
    (L : set (X -> R)) (P : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hP : is_real_integral_functional mu (positive_function_lattice L) P) (f : X -> R) :
  L f ->
  is_measure_integral mu (real_total_integrand f)
    (P (fun x => Order.max (f x) 0%R)-P (fun x => (Order.max (f x) 0%R-f x)%R))%R%:E.
Proof.
move=> hf; pose p x := Order.max (f x) 0%R; pose q x := (p x-f x)%R.
have hpL : L p := function_lattice_positive_part hL hf.
have hp0 : function_nonnegative p by move=> x; rewrite /p le_max lexx orbT.
have hfp : function_le f p by move=> x; rewrite /p le_max lexx.
have hqL : L q := function_lattice_ordered_difference hL hf hpL hfp.
have hq0 : function_nonnegative q by move=> x; rewrite /q subr_ge0; exact: hfp.
have hi := @real_total_integral_subtract R X mu hm p q (P p) (P q)
  (hP p (conj hpL hp0)) (hP q (conj hqL hq0)).
have he : (fun x => (p x-q x)%R)=f by apply: funext=> x; rewrite /q opprB addrCA subrr addr0.
by rewrite he in hi.
Qed.

(** Source for [daniell_signed_variation_integral]: exact all-L signed
    representation formula in Federer 2.5.5, p. 96. this lemma proves the
    stated additional scope in Federer using ordered subtraction, without
    assuming L is a vector space. *)
Theorem daniell_signed_variation_integral (R : realType) (X : choiceType)
    (L : set (X -> R)) (A P Q : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (hQ : is_daniell_negative_variation L A Q)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hmu : is_real_integral_functional mu (positive_function_lattice L) P)
    (hnu : is_real_integral_functional nu (positive_function_lattice L) Q) (f : X -> R) :
  L f -> exists a b : R,
    is_measure_integral mu (real_total_integrand f) a%:E /\
    is_measure_integral nu (real_total_integrand f) b%:E /\ A f=(a-b)%R.
Proof.
move=> hf; pose p x := Order.max (f x) 0%R; pose q x := (p x-f x)%R.
have hpL : L p := function_lattice_positive_part hL hf.
have hp0 : function_nonnegative p by move=> x; rewrite /p le_max lexx orbT.
have hfp : function_le f p by move=> x; rewrite /p le_max lexx.
have hqL : L q := function_lattice_ordered_difference hL hf hpL hfp.
have hq0 : function_nonnegative q by move=> x; rewrite /q subr_ge0; exact: hfp.
exists (P p-P q)%R,(Q p-Q q)%R; split.
- exact: (@positive_lattice_representation_signed_integral R X L P hL mu hm hmu f hf).
- split; first exact: (@positive_lattice_representation_signed_integral R X L Q hL nu hn hnu f hf).
  have he : (fun x => (f x+q x)%R)=p by apply: funext=> x; rewrite /q addrCA subrr addr0.
  have ha := @daniell_integral_add R X L A hA f q hf hqL.
  rewrite he in ha.
  have hav : A f=(A p-A q)%R by rewrite ha addrK.
  rewrite hav (@daniell_positive_negative_identity R X L A P Q hL hA hP hQ p (conj hpL hp0))
    (@daniell_positive_negative_identity R X L A P Q hL hA hP hQ q (conj hqL hq0)).
  by rewrite !opprB (addrACA (P p) (- Q p)%R (Q q) (- P q)%R)
    (addrACA (P p) (- P q)%R (Q q) (- Q p)%R) [(- Q p + - P q)%R]addrC.
Qed.
