(** Federer (1969), 2.10.28(4), pp. 192–193: supporting ordinal enumeration
    of the specified family Phi(J,n). Derive its bijection from the abstract
    interval description and strict spacing, without importing or unfolding
    the finite-image existence construction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP EqualSpacingIntervalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_ordinal_enumeration]: supporting
    exact n-interval description of Phi(J,n)
    in 2.10.28(4), p. 192. Strict
    separation proves injectivity, and the
    family specification proves surjectivity.
    This is a consequence of the laws,
    not exposure of a hidden implementation. *)
Theorem equal_cost_interval_ordinal_enumeration (R : realType) (h : R -> R)
    (J : compact_real_intervals R) n F :
  is_equal_cost_interval_family h J n F ->
  (2<=n)%N /\ exists (a b s t : R) (f : 'I_n -> compact_real_intervals R),
    val J=(`[a,b] : set (real_line_metric R)) /\ 0<b-a /\
    is_cantor_split_radius h (b-a) n s /\ t=cantor_split_spacing (b-a) n s /\
    (forall i, val (f i)=(`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R))) /\
    injective f /\ F=[fset f i | i in enum 'I_n].
Proof.
move=> [hn [a [b [s [t [hJ [hd [hs [ht hchar]]]]]]]]]; split=> //.
have hspos := (cantor_split_radius_bounds hs).1.
have hst : s<t by rewrite ht; exact: cantor_split_spacing_strict hn hs.
have hchild (i : 'I_n) : is_compact_real_interval
    (`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)).
  exists (a+i%:R*t),(a+i%:R*t+s); split=> //; lra.
pose f (i : 'I_n) : compact_real_intervals R :=
  Sub (`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)) (mem_set (hchild i)).
have hvalue i : val (f i)=(`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)) by [].
have hf : injective f.
  move=> i j hij; case: (eqVneq i j)=> [heq|hne]; first exact heq.
  have hdis := @equal_spacing_ordinal_children_disjoint R n a s t i j hspos hst hne.
  have [x hx] := compact_real_interval_nonempty (set_valP (f i)).
  have hxj : val (f j) x by rewrite -hij.
  have hmem : (val (f i) `&` val (f j)) x by split.
  by rewrite !hvalue hdis in hmem.
have hF : F=[fset f i | i in enum 'I_n].
  apply/fsetP=> S; apply/idP/idP.
  - move=> hS; have [i [hi hSi]] := (hchar S).1 hS.
    pose o : 'I_n := Ordinal hi.
    apply/imfsetP; exists o; first exact: mem_enum.
    apply: val_inj; rewrite hvalue; exact hSi.
  - move=> /imfsetP[i hi ->]; apply/(hchar (f i)); exists (val i); split; first exact: ltn_ord.
    exact: hvalue.
exists a,b,s,t,f; split=> //; split=> //; split=> //; split=> //; split=> //; by split.
Qed.
