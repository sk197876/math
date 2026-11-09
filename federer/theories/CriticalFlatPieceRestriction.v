(** Federer (1969), 3.4.2(7), pp. 312–314: restrictions in the
    compact reduction and the simultaneous induction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations RealNormUP
  RelativeClassUP CriticalManifoldFamilyUP CriticalFlatPiecesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_flat_function_larger_zero_set]: supporting
    the compact reduction of 3.4.2(7), p. 312. A function vanishing
    on a larger set also vanishes on every original subset. *)
Lemma critical_flat_function_larger_zero_set (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) S C D (f:R_n R m->Y) k:
  C `<=` D ->critical_flat_function_class hNY S D f k ->
  critical_flat_function_class hNY S C f k.
Proof. move=>hCD [hf hz];split;first exact:hf. move=>x hx;exact:hz x (hCD x hx). Qed.

(** Source for [critical_flat_piece_larger_zero_set]: supporting
    the compact reduction of 3.4.2(7), p. 312. A compact piece that
    controls all functions vanishing on C controls those vanishing on
    a larger original set D; its compact subset remains in D. *)
Lemma critical_flat_piece_larger_zero_set (R:realType) m d (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:G (R_n R m) d) mu S C D k T G:
  C `<=` D ->is_critical_flat_piece hNY Z mu S C k T G ->
  is_critical_flat_piece hNY Z mu S D k T G.
Proof.
move=>hCD [hFamily [hTS [hCompact [hGC hLimit]]]].
split;first exact:hFamily.
split;first exact:hTS.
split;first exact:hCompact.
split.
- move=>x hx;split;[exact:(hGC x hx).1|exact:hCD x (hGC x hx).2].
- move=>f hf;apply:hLimit.
  exact:(critical_flat_function_larger_zero_set hCD hf).
Qed.

(** Source for [critical_flat_function_source_restriction]: the
    restriction from S to a cutting manifold V in the last paragraph
    of the proof of 3.4.2(7), p. 314. The same local ambient extensions
    prove class k on V, and the zero set becomes V intersect C. *)
Lemma critical_flat_function_source_restriction (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) S V C (f:R_n R m->Y) k:
  V `<=` S ->critical_flat_function_class hNY S C f k ->
  critical_flat_function_class hNY V (V `&` C) f k.
Proof.
move=>hVS [hf hz];split.
- move=>a ha.
  have [U [g [haU [hg hAgree]]]]:=hf a (hVS a ha).
  exists U,g;split;first exact:haU.
  split;first exact:hg.
  move=>x hx hxU;split;first exact:hx.
  exact:(hAgree x (hVS x hx) hxU).2.
- move=>x [_ hx];exact:hz x hx.
Qed.

(** Source for [critical_flat_piece_larger_source]: the passage
    from Ψ(V,V intersect C,k) to Ψ(S,C,k) in 3.4.2(7), p. 314.
    The original compact piece is retained, and its dimension bound
    follows through the smaller cutting manifold. *)
Lemma critical_flat_piece_larger_source (R:realType) m d (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:G (R_n R m) d) mu v S V C k T G:
  (v<=mu)%N ->V `<=` S ->
  is_critical_flat_piece hNY Z v V (V `&` C) k T G ->
  is_critical_flat_piece hNY Z mu S C k T G.
Proof.
move=>hv hVS [[gamma [hGamma hFamily]] [hTV [hCompact [hGC hLimit]]]].
split.
- exists gamma;split;[exact:leq_trans hGamma hv|exact:hFamily].
split;first by move=>x hx;exact:hVS x (hTV x hx).
split;first exact:hCompact.
split.
- move=>x hx;split;[exact:(hGC x hx).1|exact:(hGC x hx).2.2].
- move=>f hf;apply:hLimit.
  exact:(critical_flat_function_source_restriction hVS hf).
Qed.
