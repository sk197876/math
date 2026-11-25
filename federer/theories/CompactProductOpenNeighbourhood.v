(** General topology supporting Federer (1969), 4.1.13,
    pp. 369–370: a compact product contained in an open set
    has a product of open neighbourhoods still contained there.
    This expands the printed instruction to replace U by a
    suitable neighbourhood of spt T, using the finite-cover
    principle of 2.2.5, p. 63. Empty compact factors are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals topology.
From Federer Require Import CompactFiniteCover ProductCoordinateNeighborhoods
  CompactProductTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_product_open_neighbourhood]: the
    support-neighbourhood step of Federer 4.1.13,
    pp. 369–370. Two finite-cover applications enlarge both
    compact factors, without a convexity assumption on the target. *)
Theorem compact_product_open_neighbourhood (P X:topologicalType)
    (K:set P) (L:set X) (O:set (P*X)):
  compact K->compact L->open O->K `*` L `<=` O->
  exists V W,open V /\open W /\K `<=` V /\L `<=` W /\V `*` W `<=` O.
Proof.
move=>hK hL hO hKLO.
pose J:=[the choiceType of (set P*set X)%type].
pose D:set J:=[set z|open z.1 /\open z.2 /\L `<=` z.2 /\z.1 `*` z.2 `<=` O].
have hCover:K `<=` \bigcup_(z in D) z.1.
  move=>p hp.
  have [V [W [hV [hpV [hW [hLW hVWO]]]]]]:=
    @compact_product_open_tube P X p L O hL hO
      (fun x hx=>hKLO (p,x) (conj hp hx)).
  exists (V,W);last exact:hpV.
  by split=>//;split=>//;split.
have [F hF hCoverF]:=@compact_open_finite_cover P J D (fun z=>z.1) K hK
  (fun z hz=>hz.1) hCover.
pose V:set P:=\bigcup_(z in [set` F]) z.1.
pose W:set X:=\bigcap_(z in [set` F]) z.2.
have hV:open V.
  apply:bigcup_open=>z hz.
  have hd:D z:=set_mem (hF z hz);exact:hd.1.
have hW:open W.
  apply:fset_bigcap_open=>z hz.
  have hd:D z:=set_mem (hF z hz);exact:hd.2.1.
have hLW:L `<=` W.
  move=>x hx z hz.
  have hd:D z:=set_mem (hF z hz);exact:hd.2.2.1 x hx.
exists V,W;split=>//;split=>//;split;first exact:hCoverF.
split;first exact:hLW.
move=>[p x] [[z hz hp] hx].
have hd:D z:=set_mem (hF z hz).
exact:hd.2.2.2 (conj hp (hx z hz)).
Qed.
