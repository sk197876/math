(** Federer (1969), 4.1.7, p. 358: the
    weighted Radon measure uses the Borel approximation
    of 2.2.3, pp. 61–62. This supporting lemma
    applies that approximation on the finite pieces
    of 2.3.4, p. 76, without requiring finiteness
    on every bounded set of an open subspace. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureSplit MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  CountablyMeasurableUP CountableDefaultEnumeration TopologicalBorel BorelRegularMeasureUP
  BorelRegularSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_finite_measurable_borel_cover]:
    the Borel superset with null excess from
    Federer 2.2.3, pp. 61–62, applied on each
    finite measurable piece. This supports the exact
    variation assertion of 4.1.7, p. 358. The
    target set and the whole measure may be infinite. *)
Theorem countably_finite_measurable_borel_cover (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_borel_regular_measure mu):
  measure_countably_measurable mu setT ->forall A,
  measure_measurable mu A ->exists B,
    borel_set B /\ A `<=` B /\ mu (B `\` A)=0.
Proof.
move=>[D [hD [hCover hFinite]]] A hA.
have [P [hP hEnum]]:=countable_default_enumeration set0 hD.
have hPf n:measure_measurable mu (P n) /\ mu (P n)< +oo.
  case:(hP n)=>[hd|->]; first exact:hFinite _ hd.
  split; first exact:measure_measurable_empty hm.
  by rewrite (measure_empty hm) lt0y.
have hAll:setT `<=` \bigcup_n P n.
  move=>x hx.
  have hUnion:(\bigcup_(C in D) C) x by rewrite -hCover.
  have [C hc hCx]:=hUnion.
  have [n hn]:=hEnum C hc.
  exists n=>//; by rewrite hn.
pose E n:=A `&` P n.
have hEach n:exists B,borel_set B /\ E n `<=` B /\ mu (B `\` E n)=0.
  have hEm:=measure_measurable_intersection hm hA (hPf n).1.
  have hEf:mu (E n)< +oo.
    exact:(le_lt_trans (@measure_mono R X mu hm (E n) (P n) (fun x hx=>hx.2)) (hPf n).2).
  have [C [B [hC [hB [hCE [hEB hZero]]]]]]:=
    @borel_regular_finite_sandwich R X mu hm hr (E n) hEm hEf.
  exists B; split=>//; split=>//.
  apply:(@measure_null_subset R X mu hm _ (B `\` C)) hZero.
  move=>x [hBx hnE]; split=>// hCx; exact:hnE (hCE x hCx).
pose B n:=projT1 (cid (hEach n)).
have hB n:=projT2 (cid (hEach n)).
exists (\bigcup_n B n); split.
- apply:borel_set_countable_union; first exact:countableP.
  by move=>n _; exact:(hB n).1.
- split.
  + move=>x hx; have [n _ hn]:=hAll x Logic.I.
    exists n=>//; apply:(hB n).2.1; by split.
  + have hZero:mu (\bigcup_n (B n `\` E n))=0.
      apply:(@measure_null_countable_union R X _ mu hm setT
        (fun n=>B n `\` E n) (countableP _)).
      by move=>n _; exact:(hB n).2.2.
    apply:(@measure_null_subset R X mu hm _ (\bigcup_n (B n `\` E n))) hZero.
    move=>x [[n _ hx] hnA]; exists n=>//; split=>//.
    by move=>[hAx _]; exact:hnA hAx.
Qed.
