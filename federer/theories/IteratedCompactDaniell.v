(** Federer (1969), 2.6.4, p. 119, final proposition: the iterated
    functional is a Daniell integral. We prove its order bounds and
    increasing-sequence continuity from fixed compact rectangles, using the
    compactness argument of 2.5.13, pp. 106–107. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP FunctionLatticeSeminormUP
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit RealErrorOrderLimit IncreasingScalarErrors
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactProductSections CompactSupportUniformBound
  CompactIncreasingUniformApproximation IteratedCompactFunctionalAlgebra IteratedCompactFunctionalBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Product.
Variable R : realType.
Variables X Y : topologicalType.
Variables (A : (X -> R) -> R) (B : (Y -> R) -> R).
Hypotheses (hX : hausdorff_space X) (hlX : locally_compact (@setT X)).
Hypotheses (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y)).
Hypothesis hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A.
Hypothesis hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B.
Local Notation C := (fun h => B (fun y => A (fun x => h (x,y)))).
Local Notation KXY := (@compactly_supported_continuous_functions R (X*Y)%type).

(** Source for [iterated_compact_functional_order_bounded]: the
    finite upper bound on positive order intervals required for the
    product Daniell functional in Federer 2.6.4, p. 119. *)
Lemma iterated_compact_functional_order_bounded u : KXY u ->
  exists b : R, forall f, lattice_positive_order_interval KXY u f -> C f<=b.
Proof.
move=> hu.
pose K := fst @` real_function_support u.
pose L := snd @` real_function_support u.
have hK : compact K := compact_product_first_projection hu.2.
have hL : compact L := compact_product_second_projection hu.2.
have [M [hM hbound]] := compact_support_uniform_bound hu.
have [c [hc hb]] := @iterated_compact_functional_fixed_support_bound R X Y A B K L
  hX hlX hY hlY hK hL hA hB.
exists ((M+1)*c)=> f [hf [hf0 hfu]].
have hz x y : ~(K x /\ L y) -> f (x,y)=0.
  move=> hn.
  have hu0 : u (x,y)=0.
    apply: real_function_zero_off_support=> hs; apply: hn; split; by exists (x,y).
  apply/eqP; rewrite eq_le hf0 andbT; have hh := hfu (x,y); by rewrite hu0 in hh.
have hep : 0<M+1.
  have hh : M<M+1 by rewrite ltrDl ltr01.
    exact: le_lt_trans hM hh.
have hfe x y : `|f (x,y)|<=M+1.
  rewrite ger0_norm; last exact: hf0.
  apply: le_trans (hfu (x,y)) _; apply: le_trans (ler_norm _) _.
  apply: le_trans (hbound (x,y)) _; by rewrite lerDl ler01.
exact: le_trans (ler_norm _) (@hb f hf hz (M+1) hep hfe).
Qed.

(** Source for [iterated_compact_functional_increasing_continuity]:
    increasing-sequence continuity for the product functional in
    Federer 2.6.4, p. 119, proved by the compact
    uniform-error argument of 2.5.13, pp. 106–107. *)
Lemma iterated_compact_functional_increasing_continuity f g :
  (forall n, KXY (f n)) -> KXY g -> real_functions_increase_to f g ->
  extended_order_limit (fun n => (C (f n))%:E) (C g)%:E.
Proof.
move=> hf hg hi.
have hlat := @compactly_supported_continuous_functions_lattice R (X*Y)%type.
have hlin := @iterated_compact_functional_linear R X Y A B hX hlX hY hA hB.
have hdiff n p := @increasing_scalar_error_bounds R (X*Y)%type f g hi n p.
have hfg n : function_le (f n) g.
  move=> p; have hh := (andP (hdiff n p)).1; by rewrite subr_ge0 in hh.
pose d n p := g p-f n p.
have hd n : KXY (d n) := @function_lattice_ordered_difference R (X*Y)%type KXY hlat
  (f n) g (hf n) hg (hfg n).
pose H := d 0%N.
pose S := real_function_support H.
pose K := fst @` S.
pose L := snd @` S.
have hS : compact S := (hd 0%N).2.
have hK : compact K := compact_product_first_projection hS.
have hL : compact L := compact_product_second_projection hS.
have [c [hc hb]] := @iterated_compact_functional_fixed_support_bound R X Y A B K L
  hX hlX hY hlY hK hL hA hB.
have hdz n p : ~S p -> d n p=0.
  move=> hs; have hH : H p=0 := real_function_zero_off_support hs.
  have hh := (andP (hdiff n p)).2; have h0 := (andP (hdiff n p)).1.
  change (is_true (d n p<=H p)) in hh.
  apply/eqP; rewrite eq_le h0 andbT; by rewrite hH in hh.
have hrect n x y : ~(K x /\ L y) -> d n (x,y)=0.
  move=> hn; apply: hdz=> hs; apply: hn; split; by exists (x,y).
have hval n : C (d n)=C g-C (f n).
  have hadd := hlin.1 (f n) (d n) (hf n) (hd n).
  have heq : (fun p => f n p+d n p)=g by apply: funext=> p; rewrite /d addrCA subrr addr0.
  have heval : C (fun p => f n p+d n p)=C g := congr1 C heq.
  have hsum : C g=C (f n)+C (d n) := eq_trans (esym heval) hadd.
  by rewrite hsum addrAC subrr add0r.
apply: real_error_extended_order_limit=> e he.
have hcp : c<c+1 by rewrite ltrDl ltr01.
have hden : 0<c+1 := le_lt_trans hc hcp.
pose delta := e/(c+1).
have hdelta : 0<delta by rewrite /delta divr_gt0.
have [N hN] := @compact_increasing_uniform_approximation R (X*Y)%type S f g delta hS
  (fun n => (hf n).1) hg.1 hi hdelta.
exists N=> n hn.
have hde x y : `|d n (x,y)|<=delta.
  case: (pselect (S (x,y)))=> hs.
  - rewrite ger0_norm; last exact: (andP (hdiff n (x,y))).1.
    exact: ltW (hN n hn (x,y) hs).
  - rewrite (hdz n (x,y) hs) normr0; exact: ltW hdelta.
have hbd := @hb (d n) (hd n) (hrect n) delta hdelta hde.
rewrite hval distrC in hbd; apply: le_lt_trans hbd _.
have hm : delta*c<delta*(c+1) by rewrite ltr_pM2l.
by rewrite /delta divfK ?gt_eqF // in hm.
Qed.

(** Source for [iterated_compact_functional_daniell]: existence
    candidate satisfies all four Daniell laws in the final
    proposition of Federer 2.6.4, p. 119. *)
Theorem iterated_compact_functional_daniell : is_daniell_integral KXY C.
Proof.
have hlin := @iterated_compact_functional_linear R X Y A B hX hlX hY hA hB.
constructor.
- exact hlin.1.
- move=> c f hc hf; exact: hlin.2 c f hf.
- exact: iterated_compact_functional_order_bounded.
- exact: iterated_compact_functional_increasing_continuity.
Qed.
End Product.
